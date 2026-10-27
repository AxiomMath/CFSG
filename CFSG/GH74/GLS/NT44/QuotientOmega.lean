module

public import CFSG.Goldschmidt.Basic
import CFSG.LocalAnalysis.ComponentClassification.AS81QbarComp

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

theorem omega1_centerQuotient_eq_map_of_inducesOmega1
    {G : Type} [Group G] {A L T : Subgroup G}
    (hAL : A ≤ L) (hind : CFSG.Goldschmidt.InducesOmega1 A L T) :
    CFSG.Goldschmidt.Omega1
      ((T.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L))) =
    (A.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L)) := by
  let π : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  let Abar : Subgroup (L ⧸ Subgroup.center L) := (A.subgroupOf L).map π
  let Tbar : Subgroup (L ⧸ Subgroup.center L) := (T.subgroupOf L).map π
  change CFSG.Goldschmidt.Omega1 Tbar = Abar
  have hiff : ∀ q : L ⧸ Subgroup.center L,
      q ∈ Abar ↔ q ∈ Tbar ∧ q ^ 2 = 1 := by
    intro q
    constructor
    · intro hq
      change q ∈ (A.subgroupOf L).map π at hq
      rcases (Subgroup.mem_map.mp hq) with ⟨a0, ha0, rfl⟩
      have ha : (a0 : G) ∈ A := Subgroup.mem_subgroupOf.mp ha0
      rcases hind.1 (a0 : G) ha with ⟨t, ht, htsq, hact⟩
      let t0 : L := ⟨t, ht.2⟩
      have hsame : ∀ x ∈ L, ((a0 : L) : G)⁻¹ * x * (a0 : L) =
          ((t0 : L) : G)⁻¹ * x * (t0 : L) := by
        intro x hx
        simpa [t0] using hact x hx
      have hpi : π a0 = π t0 := by
        simpa only [π, QuotientGroup.mk'_apply] using
          (CFSG.ComponentClassification.AS81.Qbar.mk_eq_of_sameOn hsame)
      have hcenter : t0 ^ 2 ∈ Subgroup.center L := by
        rw [Subgroup.mem_center_iff]
        intro l
        apply Subtype.ext
        simpa [t0] using (Subgroup.mem_centralizer_iff.mp htsq) (l : G) l.2
      have hpow : (π t0) ^ 2 = 1 := by
        change (QuotientGroup.mk t0 : L ⧸ Subgroup.center L) ^ 2 = 1
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact hcenter
      have hqpow : (π a0) ^ 2 = 1 := by
        rw [hpi]
        exact hpow
      refine ⟨?_, hqpow⟩
      change π a0 ∈ (T.subgroupOf L).map π
      exact Subgroup.mem_map.mpr
        ⟨t0, Subgroup.mem_subgroupOf.mpr ht.1, hpi.symm⟩
    · rintro ⟨hqT, hq2⟩
      change q ∈ (T.subgroupOf L).map π at hqT
      rcases (Subgroup.mem_map.mp hqT) with ⟨t0, ht0, rfl⟩
      have ht0T : (t0 : G) ∈ T := Subgroup.mem_subgroupOf.mp ht0
      have hcenter : t0 ^ 2 ∈ Subgroup.center L := by
        change (QuotientGroup.mk t0 : L ⧸ Subgroup.center L) ^ 2 = 1 at hq2
        rw [← QuotientGroup.mk_pow] at hq2
        exact (QuotientGroup.eq_one_iff (t0 ^ 2)).mp hq2
      have hcent : ((t0 : L) : G) ^ 2 ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        simpa using congrArg Subtype.val
          ((Subgroup.mem_center_iff.mp hcenter) ⟨x, hx⟩)
      rcases hind.2 (t0 : G) ⟨ht0T, t0.2⟩ hcent with ⟨a, ha, hact⟩
      let a0 : L := ⟨a, hAL ha⟩
      have hsame : ∀ x ∈ L, ((a0 : L) : G)⁻¹ * x * (a0 : L) =
          ((t0 : L) : G)⁻¹ * x * (t0 : L) := by
        intro x hx
        simpa [a0] using hact x hx
      have heq : QuotientGroup.mk a0 = QuotientGroup.mk t0 :=
        CFSG.ComponentClassification.AS81.Qbar.mk_eq_of_sameOn hsame
      change π t0 ∈ (A.subgroupOf L).map π
      refine Subgroup.mem_map.mpr
        ⟨a0, Subgroup.mem_subgroupOf.mpr ha, ?_⟩
      simpa only [π, QuotientGroup.mk'_apply] using heq
  apply le_antisymm
  · intro q hq
    change q ∈ Subgroup.closure {t | t ∈ Tbar ∧ t ^ 2 = 1} at hq
    exact (Subgroup.mem_closure.mp hq) Abar (fun x hx => (hiff x).mpr hx)
  · intro q hq
    change q ∈ Subgroup.closure {t | t ∈ Tbar ∧ t ^ 2 = 1}
    exact Subgroup.subset_closure ((hiff q).mp hq)

end CFSG.GH74.GLS.NT44

end
