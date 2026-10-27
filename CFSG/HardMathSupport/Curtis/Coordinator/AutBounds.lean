module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {Y : Type*} [Group Y]

theorem le_sup_centralizer_of_isPGroup_of_not_dvd {L U : Subgroup Y} {p : ℕ} (hp : p.Prime)
    (hU : U ≤ Subgroup.normalizer (L : Set Y)) (hUp : IsPGroup p U)
    (hOut : ¬ p ∣ Nat.card (Outer ↥L)) : U ≤ L ⊔ Subgroup.centralizer (L : Set Y) := by
  intro u hu
  obtain ⟨k, hk⟩ := hUp ⟨u, hu⟩
  exact CFSG.AGLEmbedding.mem_sup_centralizer_of_not_dvd_card_outer hp hOut (hU hu)
    (by simpa using congrArg Subtype.val hk)

theorem inf_centralizer_subgroupOf_eq_center (L : Subgroup Y) :
    (L ⊓ Subgroup.centralizer (L : Set Y)).subgroupOf L = Subgroup.center ↥L := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, hx⟩ g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) g g.2)
  · intro hx
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (hx ⟨g, hg⟩)

theorem relIndex_centralizer_dvd_card_center_quotient {L U : Subgroup Y}
    (hU : U ≤ Subgroup.normalizer (L : Set Y)) (hUL : U ≤ L ⊔ Subgroup.centralizer (L : Set Y)) :
    (U ⊓ Subgroup.centralizer (L : Set Y)).relIndex U ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
  set N := Subgroup.normalizer (L : Set Y)
  set C := Subgroup.centralizer (L : Set Y)
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hLN : L ≤ N := Subgroup.le_normalizer
  have : (C.subgroupOf N).Normal := Subgroup.normal_subgroupOf_centralizer_normalizer _
  have hUs : (U ⊓ C).relIndex U = (C.subgroupOf N).relIndex (U.subgroupOf N ⊔ C.subgroupOf N) := by
    rw [Subgroup.relIndex_sup_right, Subgroup.relIndex_subgroupOf hU, Subgroup.inf_relIndex_left]
  have hLs : (L ⊓ C).relIndex L = (C.subgroupOf N).relIndex (L.subgroupOf N ⊔ C.subgroupOf N) := by
    rw [Subgroup.relIndex_sup_right, Subgroup.relIndex_subgroupOf hLN, Subgroup.inf_relIndex_left]
  have hle : U.subgroupOf N ⊔ C.subgroupOf N ≤ L.subgroupOf N ⊔ C.subgroupOf N := by
    refine sup_le ?_ le_sup_right
    rw [← Subgroup.subgroupOf_sup hLN hCN]
    exact Subgroup.subgroupOf_mono _ hUL
  have hdvd : (U ⊓ C).relIndex U ∣ (L ⊓ C).relIndex L := by
    rw [hUs, hLs]
    exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hle)
  refine hdvd.trans (dvd_of_eq ?_)
  rw [Subgroup.relIndex, inf_centralizer_subgroupOf_eq_center, Subgroup.index]

theorem relIndex_centralizer_le_of_le_sup [Finite Y] {L U : Subgroup Y} {p k : ℕ} (hp : p.Prime)
    (hU : U ≤ Subgroup.normalizer (L : Set Y)) (hUL : U ≤ L ⊔ Subgroup.centralizer (L : Set Y))
    (hUp : IsPGroup p U) (hk : ¬ p ^ (k + 1) ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) :
    (U ⊓ Subgroup.centralizer (L : Set Y)).relIndex U ≤ p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd := relIndex_centralizer_dvd_card_center_quotient hU hUL
  obtain ⟨m, hm⟩ := hUp.exists_card_eq
  have hdU : (U ⊓ Subgroup.centralizer (L : Set Y)).relIndex U ∣ p ^ m := by
    rw [← hm]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdU
  rw [hj] at hdvd ⊢
  refine Nat.pow_le_pow_right hp.pos ?_
  by_contra hjk
  exact hk ((pow_dvd_pow p (by omega)).trans hdvd)

end CFSG.HardMathSupport.Curtis.Coordinator
