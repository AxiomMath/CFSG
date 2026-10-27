module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLTwoRoots
public import CFSG.Timmesfeld.ARS.FrameSL3Steinberg
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Open.StatedAPI CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.Timmesfeld.ARS.FrameSL3
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem excTL_two_sl3 {τ : Tag} (hτ : τ ≠ .G2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {γ δ : Fin τ.rank → ℤ} {h : ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (nγ : iform γ γ = 2 * h) (nδ : iform δ δ = 2 * h) (hab : iform γ δ = -h) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin 3) K →* (Module.End K (RootModule τ K))ˣ,
      ∀ α ∈ excTLHex γ δ, ∀ c : K, pinnedX τ K α c ∈ ρ.range := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
    (by rw [← one_add_one_eq_two]; exact (excTL_two_facts K hK).2.1)
  have hδγ : iform δ γ = -h := by rw [iform_comm]; exact hab
  have hh := excTL_h_cases hτ hγ nγ
  have hs : IsRoot τ (γ + δ) := (excTL_a2_of_iform hτ hγ hδ nγ nδ hab).1
  have hγ' := IsRoot.neg hγ
  have hδ' := IsRoot.neg hδ
  have hs' := IsRoot.neg hs
  have ns : iform (γ + δ) (γ + δ) = 2 * h := by
    simp only [iform_add_left, iform_add_right, nγ, nδ, hab, hδγ]
    omega
  have nγ' : iform (-γ) (-γ) = 2 * h := by rw [excTL_iform_neg_neg, nγ]
  have nδ' : iform (-δ) (-δ) = 2 * h := by rw [excTL_iform_neg_neg, nδ]
  have ns' : iform (-(γ + δ)) (-(γ + δ)) = 2 * h := by rw [excTL_iform_neg_neg, ns]
  have ha := pinnedX_add τ K γ
  have hb := pinnedX_add τ K δ
  have hc := pinnedX_add τ K (γ + δ)
  have ha' := pinnedX_add τ K (-γ)
  have hb' := pinnedX_add τ K (-δ)
  have hc' := pinnedX_add τ K (-(γ + δ))
  have hfam := fam_comm (F := K) (a := pinnedX τ K γ) (b := pinnedX τ K δ)
    (c := pinnedX τ K (γ + δ)) (a' := pinnedX τ K (-γ)) (b' := pinnedX τ K (-δ))
    (c' := pinnedX τ K (-(γ + δ))) ha hb hc ha' hb' hc'
    (fun s t => excTL_commute_pinnedX_pos hτ hγ hs nγ ns
      (by simp only [iform_add_right, nγ, hab]; omega) s t)
    (fun s t => excTL_commute_pinnedX_pos hτ hγ hδ' nγ nδ'
      (by simp only [excTL_iform_neg_right, hab]; omega) s t)
    (fun s t => excTL_commute_pinnedX_pos hτ hδ hs nδ ns
      (by simp only [iform_add_right, nδ, hδγ]; omega) s t)
    (fun s t => excTL_commute_pinnedX_pos hτ hδ hγ' nδ nγ'
      (by simp only [excTL_iform_neg_right, hδγ]; omega) s t)
    (fun s t => excTL_commute_pinnedX_pos hτ hγ' hs' nγ' ns'
      (by simp only [excTL_iform_neg_left, excTL_iform_neg_right, iform_add_right, nγ, hab]; omega)
      s t)
    (fun s t => excTL_commute_pinnedX_pos hτ hδ' hs' nδ' ns'
      (by simp only [excTL_iform_neg_left, excTL_iform_neg_right, iform_add_right, nδ, hδγ]; omega)
      s t)
    (fun s t => excTL_two_comm_pinnedX hτ hK hγ hδ nγ nδ hab rfl s t)
    (fun s t => excTL_two_comm_pinnedX hτ hK hγ' hs nγ' ns
      (by simp only [excTL_iform_neg_left, iform_add_right, nγ, hab]; omega) (by abel) s t)
    (fun s t => excTL_two_comm_pinnedX hτ hK hγ hs' nγ ns'
      (by simp only [excTL_iform_neg_right, iform_add_right, nγ, hab]; omega) (by abel) s t)
    (fun s t => excTL_two_comm_pinnedX hτ hK hγ' hδ' nγ' nδ'
      (by simp only [excTL_iform_neg_left, excTL_iform_neg_right, hab]; omega) (by abel) s t)
    (fun s t => excTL_two_comm_pinnedX hτ hK hδ' hs nδ' ns
      (by simp only [excTL_iform_neg_left, iform_add_right, nδ, hδγ]; omega) (by abel) s t)
    (fun s t => excTL_two_comm_pinnedX hτ hK hδ hs' nδ ns'
      (by simp only [excTL_iform_neg_right, iform_add_right, nδ, hδγ]; omega) (by abel) s t)
  obtain ⟨ρ, hρ⟩ := exists_hom_of_steinberg (fam_add ha hb hc ha' hb' hc') hfam
  refine ⟨ρ, fun α hα c => ?_⟩
  simp only [excTLHex, Set.mem_insert_iff, Set.mem_singleton_iff] at hα
  rcases hα with e | e | e | e | e | e <;> rw [e]
  · exact ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c, hρ 0 1 _ c⟩
  · exact ⟨Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c, hρ 1 2 _ c⟩
  · exact ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c, hρ 0 2 _ c⟩
  · exact ⟨Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c, hρ 1 0 _ c⟩
  · exact ⟨Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c, hρ 2 1 _ c⟩
  · exact ⟨Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c, hρ 2 0 _ c⟩

theorem excTL_two_card_le {τ : Tag} (hτ : τ ≠ .G2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {γ δ : Fin τ.rank → ℤ} {h : ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (nγ : iform γ γ = 2 * h) (nδ : iform δ δ = 2 * h) (hab : iform γ δ = -h)
    {S : Set (Fin τ.rank → ℤ)} (hS : S ⊆ excTLHex γ δ) :
    Finite ↥(rootSpan τ K S) ∧ Nat.card ↥(rootSpan τ K S) ≤ 168 := by
  obtain ⟨ρ, hρ⟩ := excTL_two_sl3 hτ hK hγ hδ nγ nδ hab
  have hle : rootSpan τ K S ≤ ρ.range := iSup₂_le fun α hα =>
    (Subgroup.closure_le _).2 (by rintro _ ⟨c, rfl⟩; exact hρ α (hS hα) c)
  have hfin : Finite (Matrix.SpecialLinearGroup (Fin 3) K) := inferInstance
  have : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  have h1 : Nat.card ↥(rootSpan τ K S) ≤ Nat.card ρ.range := Subgroup.card_le_of_le hle
  have h2 : Nat.card ρ.range ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) :=
    Nat.card_le_card_of_surjective _ ρ.rangeRestrict_surjective
  have h3 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) = 168 := by
    rw [← card_statedSL, card_statedSL_three, hK]
    norm_num
  exact ⟨Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle),
    by omega⟩

end CFSG.HardMathSupport.Dickson.Sec6.I1431
