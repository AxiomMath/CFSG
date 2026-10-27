module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10L104_pocket_eq [Finite G] (hP5 : Asc82FactPockets5) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2)
    {D : Subgroup G} (hD : Sl23PocketIn L z D) : D = K1 ∨ D = K2 := by
  obtain ⟨K1', K2', -, -, _, huniq, -, -, -, -⟩ := hP5 G L hpsp z hctx.toSec10Z.pocket
  have hcase : (K1 = K1' ∧ K2 = K2') ∨ (K1 = K2' ∧ K2 = K1') := by
    rcases huniq K1 hctx.pocket1 with h1 | h1 <;> rcases huniq K2 hctx.pocket2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hctx.ne
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hctx.ne
  rcases huniq D hD with h | h
  · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (h.trans h1.symm)
    · exact Or.inr (h.trans h2.symm)
  · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (h.trans h2.symm)
    · exact Or.inl (h.trans h1.symm)

theorem sec10L104_K_normal [Finite G] (hP5 : Asc82FactPockets5) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L) (hctx : Sec10Ctx G t L S z K1 K2) :
    ((K1 ⊔ K2).subgroupOf (L ⊓ centralizer ({z} : Set G))).Normal := by
  obtain ⟨K1', K2', _, _, _, _, _, hsup', hrel, _⟩ := hP5 G L hpsp z hctx.toSec10Z.pocket
  have hsup : K1 ⊔ K2 = oTwoRes (L ⊓ centralizer ({z} : Set G)) :=
    sec10K0_pockets_sup hP5 hpsp hctx
  have hidx : ((K1 ⊔ K2).subgroupOf (L ⊓ centralizer ({z} : Set G))).index = 2 := by
    rw [hsup, hsup']
    exact hrel
  exact Subgroup.normal_of_index_eq_two hidx

theorem sec10L104_pocket_of_normal [Finite G] (hP5 : Asc82FactPockets5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) {D : Subgroup G} (hzD : z ∈ D) (hDK : D ≤ K1 ⊔ K2)
    (hnorm : ∀ k ∈ K1 ⊔ K2, ∀ d ∈ D, k * d * k⁻¹ ∈ D) (hiso : Nonempty (↥K1 ≃* ↥D)) :
    Sl23PocketIn L z D := by
  obtain ⟨e⟩ := hiso
  have hKY : K1 ⊔ K2 ≤ L ⊓ centralizer ({z} : Set G) :=
    sup_le hctx.pocket1.2.1 hctx.pocket2.2.1
  have hDY : D ≤ L ⊓ centralizer ({z} : Set G) := hDK.trans hKY
  refine ⟨hzD, hDY, ?_, isSL23Mod_of_mulEquiv e hctx.pocket1.2.2.2⟩
  have hKnormalY := sec10L104_K_normal hP5 hpsp hctx
  have hDnK : K1 ⊔ K2 ≤ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer_iff.mpr hnorm
  have hDnormal : ((D.subgroupOf (L ⊓ centralizer ({z} : Set G))).subgroupOf
      ((K1 ⊔ K2).subgroupOf (L ⊓ centralizer ({z} : Set G)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.subgroupOf_mono (L ⊓ centralizer ({z} : Set G)) hDK)]
    rw [Subgroup.le_normalizer_iff]
    intro x hx a ha
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.le_normalizer_iff.mp hDnK (x : G) (Subgroup.mem_subgroupOf.mp hx)
        (a : G) (Subgroup.mem_subgroupOf.mp ha))
  exact Subgroup.IsSubnormal.step (D.subgroupOf (L ⊓ centralizer ({z} : Set G)))
    ((K1 ⊔ K2).subgroupOf (L ⊓ centralizer ({z} : Set G)))
    (Subgroup.subgroupOf_mono _ hDK) hKnormalY.isSubnormal hDnormal

end CFSG.OddStandard.SmallF3.Omega
