module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Set

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

@[expose] def y7aU16 {G : Type} [Group G] (A C0 V : Subgroup G) : Set G :=
  {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V}

@[expose] def y7aS {G : Type} [Group G] (A V : Subgroup G) (t : G) : Set G :=
  {w : G | w ∈ y6Up A V t ∧ t⁻¹ * w ∉ V}

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

structure Y7APsi (c : Ctx7 G L) (ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)) (lab : G → Fin 16) :
    Prop where
  ker : ψ.ker = (C1 c.e).subgroupOf (y7aX c)
  lab_iff : ∀ u ∈ y7aU16 c.s.fr.A (C0 c.e) (V1 c.e), ∀ u' ∈ y7aU16 c.s.fr.A (C0 c.e) (V1 c.e),
    lab u = lab u' ↔ u⁻¹ * u' ∈ V1 c.e
  lab_surj : ∀ i : Fin 16, ∃ u ∈ y7aU16 c.s.fr.A (C0 c.e) (V1 c.e), lab u = i
  act : ∀ x : ↥(y7aX c), ∀ u ∈ y7aU16 c.s.fr.A (C0 c.e) (V1 c.e),
    ψ x (lab u) = lab ((x : G) * u * (x : G)⁻¹)
  lab_t : lab c.s.t = 0
  stab : ∀ x : ↥(y7aX c), ψ x 0 = 0 ↔ (x : G) ∈ y7aY c
  trans : ∀ i j : Fin 16, ∃ q ∈ ψ.range, q i = j
  card : Nat.card ψ.range = 288 ∨ Nat.card ψ.range = 576

structure Y7AReg (c : Ctx7 G L) (ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)) (lab : G → Fin 16)
    (P : Subgroup (Equiv.Perm (Fin 16))) : Prop extends Y7APsi c ψ lab where
  P_le : P ≤ ψ.range
  P_normal : ∀ q ∈ ψ.range, ∀ m ∈ P, q * m * q⁻¹ ∈ P
  P_two : IsPGroup 2 P
  P_card : Nat.card P = 16
  P_trans : ∀ i j : Fin 16, ∃ p ∈ P, p i = j
  P_max : ∀ N : Subgroup (Equiv.Perm (Fin 16)), N ≤ ψ.range →
    (∀ q ∈ ψ.range, ∀ m ∈ N, q * m * q⁻¹ ∈ N) → IsPGroup 2 N → N ≤ P

end CFSG.OddStandard.HigherRank.YamadaG23
