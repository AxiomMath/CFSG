module

public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.RankThreeCoreUniqueness.Helpers

local notation "pRes" => CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual

theorem exists_perfect_three_dvd_of_surjective_perm {Q : Type*} [Group Q] [Finite Q]
    {P : Subgroup Q} {n : ℕ} (hn : 5 ≤ n) (f : ↥P →* Equiv.Perm (Fin n))
    (hf : Function.Surjective f) :
    ∃ Y : Subgroup Q, Y ≤ P ∧ ⁅Y, Y⁆ = Y ∧ 3 ∣ Nat.card Y := by
  set B : Subgroup ↥P := (alternatingGroup (Fin n)).comap f with hB
  set g : ↥B →* Equiv.Perm (Fin n) := f.comp B.subtype with hg
  have hrange : g.range = alternatingGroup (Fin n) := by
    ext σ
    simp only [MonoidHom.mem_range, hg, MonoidHom.comp_apply, Subgroup.coe_subtype]
    constructor
    · rintro ⟨b, rfl⟩
      exact b.2
    · intro hσ
      obtain ⟨p, hp⟩ := hf σ
      exact ⟨⟨p, by simpa [hB, hp] using hσ⟩, hp⟩
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hAperf : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by simpa using hn)⟩
  have hRperf : Group.IsPerfect ↥g.range := by rw [hrange]; exact hAperf
  have hres : (pRes ↥B).map g = alternatingGroup (Fin n) := by
    have h1 := finite_perfectResidual_map_eq g.rangeRestrict g.rangeRestrict_surjective
    have h2 : pRes ↥g.range = ⊤ :=
      top_le_iff.mp (perfect_subgroup_le_perfectResidual ⊤ inferInstance)
    rw [h2] at h1
    have h3 := congrArg (Subgroup.map g.range.subtype) h1
    rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict, Subgroup.map_top,
      Subgroup.range_subtype, hrange] at h3
    exact h3
  set R : Subgroup ↥P := (pRes ↥B).map B.subtype with hR
  have hRf : R.map f = alternatingGroup (Fin n) := by
    rw [hR, Subgroup.map_map]; exact hres
  have hRperf : ⁅R, R⁆ = R := by
    rw [hR, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp
      (finite_perfectResidual_isPerfect (G := ↥B))]
  refine ⟨R.map P.subtype, Subgroup.map_subtype_le R, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hRperf]
  · have h3 : 3 ∣ Nat.card (alternatingGroup (Fin n)) := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      have h6 : 3 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      obtain ⟨k, hk⟩ := h2
      rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [hk] at h6
      exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h6)
    have h4 : Nat.card (alternatingGroup (Fin n)) ∣ Nat.card R := by
      rw [← hRf]; exact Subgroup.card_map_dvd R f
    have h5 : Nat.card (R.map P.subtype) = Nat.card R :=
      Subgroup.card_map_of_injective P.subtype_injective
    rw [h5]
    exact h3.trans h4

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
