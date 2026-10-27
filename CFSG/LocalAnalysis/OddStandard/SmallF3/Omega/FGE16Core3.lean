module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Core2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Cnt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Ker

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

variable (B : Subgroup (OGroup Q)) [Fintype ↥B] [DecidableEq ↥B]

theorem fg_finrank_wt_le_three (hB : IsElemAb2 B 4) (hdim : Module.finrank (ZMod 3) V = 6)
    (χ : ↥B → ZMod 3) : Module.finrank (ZMod 3) (fgWt (fgT B) χ) ≤ 3 := by
  have hsum := fgWt_finrank_sum (fgT B) (fgT_sq B hB) (fgT_comm B hB)
  rw [hdim] at hsum
  set W := Finset.univ.filter (fun χ : ↥B → ZMod 3 => fgWt (fgT B) χ ≠ ⊥) with hW
  have h4 : 4 ≤ W.card := fg_four_le_card_weights B hB
  by_cases hχ : fgWt (fgT B) χ = ⊥
  · rw [hχ]
    simp
  · have hχW : χ ∈ W := by simp [hW, hχ]
    have h1 : ∑ χ' ∈ W, Module.finrank (ZMod 3) (fgWt (fgT B) χ') ≤ 6 := by
      rw [← hsum]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ W)
    rw [← Finset.add_sum_erase W _ hχW] at h1
    have h2 : (W.erase χ).card • 1 ≤
        ∑ χ' ∈ W.erase χ, Module.finrank (ZMod 3) (fgWt (fgT B) χ') := by
      apply Finset.card_nsmul_le_sum
      intro χ' hχ'
      have hne : fgWt (fgT B) χ' ≠ ⊥ := by
        have := Finset.mem_of_mem_erase hχ'
        simpa [hW] using this
      exact Submodule.one_le_finrank_iff.mpr hne
    rw [Finset.card_erase_of_mem hχW, smul_eq_mul, mul_one] at h2
    omega

theorem fg_not_centralizes (hB : IsElemAb2 B 4) (hdim : Module.finrank (ZMod 3) V = 6)
    (f : OGroup Q) (hf : ∀ g, g ∈ B ↔ f * g * f⁻¹ ∈ B) (hf5 : f ^ 5 = 1) (hf1 : f ≠ 1) :
    ¬ ∀ g ∈ B, f * g = g * f := by
  intro hcomm
  have hσ : ∀ χ : ↥B → ZMod 3, fgPerm B (ZMod 3) (fgCj B f hf) χ = χ := by
    intro χ
    funext g
    show χ ((fgCj B f hf).symm g) = χ g
    congr 1
    apply Subtype.ext
    show f⁻¹ * (g : OGroup Q) * f = g
    rw [mul_assoc, ← hcomm g g.2, inv_mul_cancel_left]
  have hmem : ∀ (χ : ↥B → ZMod 3), ∀ v ∈ fgWt (fgT B) χ,
      ((f : OGroup Q) : V ≃ₗ[ZMod 3] V) v ∈ fgWt (fgT B) χ := by
    intro χ v hv
    have h1 : ((f : OGroup Q) : V ≃ₗ[ZMod 3] V) v ∈
        (fgWt (fgT B) χ).map (((f : OGroup Q) : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) := ⟨v, hv, rfl⟩
    rwa [fgWt_map_f B f hf χ, hσ χ] at h1
  have hf5' : ((f : OGroup Q) : V ≃ₗ[ZMod 3] V) ^ 5 = 1 := by
    have := congrArg (fun x : OGroup Q => (x : V ≃ₗ[ZMod 3] V)) hf5
    simpa using this
  have hle : ⨆ χ, fgWt (fgT B) χ ≤ LinearMap.eqLocus
      (((f : OGroup Q) : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) LinearMap.id := by
    apply iSup_le
    intro χ v hv
    exact fg_fix_of_finrank_le_three (fgWt (fgT B) χ) _ hf5' (hmem χ)
      (fg_finrank_wt_le_three B hB hdim χ) v hv
  have hfix : ∀ v : V, ((f : OGroup Q) : V ≃ₗ[ZMod 3] V) v = v := by
    intro v
    have hv : v ∈ (⊤ : Submodule (ZMod 3) V) := trivial
    rw [← fgWt_iSup_eq_top (fgT B) (fgT_sq B hB) (fgT_comm B hB)] at hv
    exact hle hv
  exact hf1 (Subtype.ext (LinearEquiv.ext hfix))

theorem fg_centralizer_bot (hB : IsElemAb2 B 4) (hdim : Module.finrank (ZMod 3) V = 6)
    (f : OGroup Q) (hf : ∀ g, g ∈ B ↔ f * g * f⁻¹ ∈ B) (hf5 : f ^ 5 = 1) (hf1 : f ≠ 1) :
    B ⊓ Subgroup.centralizer {f} = ⊥ := by
  have hB16 : Nat.card ↥B = 16 := by
    rw [hB.2]
    norm_num
  rcases fg_card_centralizer_sixteen hf5 B hB16 hf with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · exfalso
    haveI : Finite ↥B := Nat.finite_of_card_ne_zero (by omega)
    have heq : B ⊓ Subgroup.centralizer {f} = B :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hB16])
    have hBc : B ≤ Subgroup.centralizer {f} := by
      rw [← heq]
      exact inf_le_right
    refine fg_not_centralizes B hB hdim f hf hf5 hf1 fun g hg => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hBc hg)) f rfl

theorem fg_perm_ne_self (hB : IsElemAb2 B 4) (hdim : Module.finrank (ZMod 3) V = 6)
    (f : OGroup Q) (hf : ∀ g, g ∈ B ↔ f * g * f⁻¹ ∈ B) (hf5 : f ^ 5 = 1) (hf1 : f ≠ 1)
    {χ : ↥B → ZMod 3} (hχ : fgWt (fgT B) χ ≠ ⊥) (hχ1 : χ ≠ fun _ => 1) :
    fgPerm B (ZMod 3) (fgCj B f hf) χ ≠ χ := by
  intro hfix
  have hB16 : Nat.card ↥B = 16 := by
    rw [hB.2]
    norm_num
  have hmul : ∀ g h : ↥B, χ (g * h) = χ g * χ h := fun g h =>
    fgWt_mul (fgT B) hχ (fgT_mul B g h)
  have hone : χ 1 = 1 := fgWt_one (fgT B) hχ (fgT_one B)
  have hsq : ∀ g, χ g * χ g = 1 := fgWt_sq (fgT B) (fgT_sq B hB) hχ
  have hnt : ∃ g, χ g ≠ 1 := by
    by_contra h
    push_neg at h
    exact hχ1 (funext h)
  obtain ⟨H, hHB, hH8, hHmem⟩ := fg_exists_kernel B hB16 χ hone hmul hsq hnt
  have hcj : ∀ g : ↥B, χ (fgCj B f hf g) = χ g := by
    intro g
    have h1 := congrFun hfix (fgCj B f hf g)
    rw [fgPerm_apply] at h1
    simpa using h1.symm
  have hHinv : ∀ h, h ∈ H ↔ f * h * f⁻¹ ∈ H := by
    intro h
    by_cases hh : h ∈ B
    · have hfh : f * h * f⁻¹ ∈ B := (hf h).1 hh
      rw [hHmem h hh, hHmem _ hfh]
      exact (hcj ⟨h, hh⟩).symm ▸ Iff.rfl
    · have hfh : f * h * f⁻¹ ∉ B := fun h' => hh ((hf h).2 h')
      exact iff_of_false (fun h' => hh (hHB h')) (fun h' => hfh (hHB h'))
  have := fg_card_invariant_subgroup hf5 B H hB16 hHB
    (fg_centralizer_bot B hB hdim f hf hf5 hf1) hHinv
  omega

end CFSG.OddStandard.SmallF3.Omega
