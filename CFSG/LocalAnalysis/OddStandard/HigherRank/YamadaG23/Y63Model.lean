module

public import Certificates.Data.Y63.Spec

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Y63Chk

structure Y63Model (D : Data) (k : ℕ) {G : Type} [Group G] (P Q : Subgroup G) (Θ : ℕ → G) :
    Prop where
  mem : ∀ i < 1024, Θ i ∈ Q
  inj : ∀ i < 1024, ∀ j < 1024, Θ i = Θ j → i = j
  surj : ∀ g ∈ Q, ∃ i < 1024, Θ i = g
  one : Θ 0 = 1
  memP : ∀ i < 512, Θ i ∈ P
  surjP : ∀ g ∈ P, ∃ i < 512, Θ i = g
  mq_lt : ∀ i < 1024, ∀ j < 1024, D.mq k i j < 1024
  mul : ∀ i < 1024, ∀ j < 1024, Θ (D.mq k i j) = Θ i * Θ j

end CFSG.OddStandard.HigherRank.YamadaG23
