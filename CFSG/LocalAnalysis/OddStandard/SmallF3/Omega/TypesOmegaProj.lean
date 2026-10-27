module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaInvol
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def omegaProj (hQ : Q.Nondegenerate) : Subgroup (ProjOrth Q) :=
  (omegaGroup hQ).map (toProj Q)

instance omegaProj_normal (hQ : Q.Nondegenerate) : (omegaProj hQ).Normal :=
  (omegaGroup_normal hQ).map (toProj Q) (QuotientGroup.mk'_surjective (piGroup Q))

theorem mem_omegaProj_iff (hQ : Q.Nondegenerate) {x : ProjOrth Q} :
    x ∈ omegaProj hQ ↔ ∃ g ∈ omegaGroup hQ, toProj Q g = x := by
  rw [omegaProj]
  exact Subgroup.mem_map

open Classical in
theorem index_omegaProj (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    (omegaProj hQ).index = if piOrth Q ∈ omegaGroup hQ then 4 else 2 := by
  have hmap : (omegaProj hQ).index = (omegaGroup hQ ⊔ piGroup Q).index := by
    rw [omegaProj, Subgroup.index_map (f := toProj Q),
      (toProj Q).range_eq_top_of_surjective (QuotientGroup.mk'_surjective (piGroup Q)),
      Subgroup.index_top, mul_one, QuotientGroup.ker_mk']
  rw [hmap]
  by_cases hmem : piOrth Q ∈ omegaGroup hQ
  · rw [if_pos hmem]
    have hle : piGroup Q ≤ omegaGroup hQ := by
      intro g hg
      rcases mem_piGroup_iff.mp hg with rfl | rfl
      · exact one_mem _
      · exact hmem
    rw [sup_eq_left.mpr hle]
    exact index_omegaGroup hQ h2
  · rw [if_neg hmem]
    have hrel : (omegaGroup hQ).relIndex (omegaGroup hQ ⊔ piGroup Q) = 2 := by
      rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
      refine ⟨piOrth Q, Subgroup.mem_sup_right (mem_piGroup_iff.mpr (Or.inr rfl)), hmem, ?_⟩
      intro b hb
      obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
      rcases mem_piGroup_iff.mp hz with rfl | rfl
      · exact Or.inr (by simpa using hy)
      · refine Or.inl ?_
        rw [mul_assoc, piOrth_mul_self, mul_one]
        exact hy
    have hmul := Subgroup.relIndex_mul_index (H := omegaGroup hQ)
      (K := omegaGroup hQ ⊔ piGroup Q) le_sup_left
    rw [hrel, index_omegaGroup hQ h2] at hmul
    omega

theorem index_omegaProj_of_odd (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (hn : Odd (Module.finrank (ZMod 3) V)) : (omegaProj hQ).index = 2 := by
  rw [index_omegaProj hQ h2,
    if_neg (fun hmem => (Nat.not_even_iff_odd.mpr hn)
      ((piOrth_mem_omegaGroup_iff hQ).mp hmem).1)]

open Classical in
theorem card_omegaProj_mul (hQ : Q.Nondegenerate) (h0 : 0 < Module.finrank (ZMod 3) V) :
    Nat.card (omegaProj hQ) * (if piOrth Q ∈ omegaGroup hQ then 2 else 1) =
      Nat.card (omegaGroup hQ) := by
  have hcard : Nat.card (piGroup Q ⊓ omegaGroup hQ : Subgroup (OGroup Q)) =
      if piOrth Q ∈ omegaGroup hQ then 2 else 1 := by
    by_cases hmem : piOrth Q ∈ omegaGroup hQ
    · rw [if_pos hmem]
      have hle : piGroup Q ≤ omegaGroup hQ := by
        intro g hg
        rcases mem_piGroup_iff.mp hg with rfl | rfl
        · exact one_mem _
        · exact hmem
      rw [le_antisymm inf_le_left (le_inf le_rfl hle)]
      exact card_piGroup (Q := Q) h0
    · rw [if_neg hmem]
      have hbot : piGroup Q ⊓ omegaGroup hQ = ⊥ := by
        apply le_antisymm
        · intro g hg
          obtain ⟨hgp, hgh⟩ := hg
          rcases mem_piGroup_iff.mp hgp with h1 | hp
          · rw [h1]; exact Subgroup.mem_bot.mpr rfl
          · rw [hp] at hgh; exact absurd hgh hmem
        · exact bot_le
      rw [hbot]
      exact Subgroup.card_bot
  have key : Nat.card (omegaProj hQ) *
      Nat.card (piGroup Q ⊓ omegaGroup hQ : Subgroup (OGroup Q)) =
      Nat.card (omegaGroup hQ) := by
    have h := Subgroup.relIndex_mul_card (H := (toProj Q).ker) (K := omegaGroup hQ)
    rw [Subgroup.relIndex_ker (f := toProj Q)] at h
    simpa [omegaProj, QuotientGroup.ker_mk'] using h
  rw [hcard] at key
  exact key

end CFSG.OddStandard.SmallF3.Omega
