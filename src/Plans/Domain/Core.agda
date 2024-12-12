open import Data.Product
open import Data.List
open import Data.Nat using (ℕ)

module Plans.Domain.Core (Type : Set) (Action : Set) (Predicate : Set) where

infix 20 polvar_

data Polarity : Set where
  + - : Polarity
  polvar_ : ℕ → Polarity

neg : Polarity → Polarity
neg + = -
neg - = +
neg (polvar x) = polvar x

-- A pair containing a predicate and polarity
PredMap : Set
PredMap = Polarity × Predicate

-- A list containing pairs of polarities and predicates
State : Set
State = List PredMap

Preconditions : Set
Preconditions = State

Effects : Set
Effects = State

GoalState : Set
GoalState = State 

record ActionDescription : Set where
  field
    preconditions : Preconditions
    effects       : Effects

Context : Set
Context = Action → ActionDescription
