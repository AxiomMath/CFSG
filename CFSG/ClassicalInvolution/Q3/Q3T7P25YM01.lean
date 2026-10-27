module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25W01
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YMH01
public import CFSG.ClassicalInvolution.Asc77.AscCX4L3
public import CFSG.ClassicalInvolution.Asc77.AscCX1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU (eq_of_central_ratio)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
namespace Asc77.C25W.Sp
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C25W
open CFSG.ClassicalInvolution.Asc77.C25W.Sp
variable {F : Type} [Field F]

theorem fix_of_trivial [Finite F] (h4 : Nat.card F = 3) (M : gsp 2 F) (ρ : F ≃+* F)
    (h : conjAut 2 F M * fieldAut 2 F ρ = 1) :
    ∀ g : StatedSp 2 F, conjSp 2 F M (fieldSp 2 F ρ g) = g := by
  set α : MulAut (StatedSp 2 F) := conjSp 2 F M * fieldSp 2 F ρ with hα
  have hαproj : ∀ g, proj 2 F (α g) = proj 2 F g := by
    intro g
    have h1 := congrArg (fun γ : MulAut (StatedProj (StatedSp 2 F)) => γ (proj 2 F g)) h
    have e : α g = conjSp 2 F M (fieldSp 2 F ρ g) := rfl
    rw [e]
    simpa [MulAut.mul_apply, fieldAut_proj, conjAut_proj] using h1
  have hperf : Group.IsPerfect (StatedSp 2 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple (n := 2) (F := F) (by norm_num)
      (Or.inr (Or.inl ⟨h4, le_rfl⟩))).1
  have : Group.IsPerfect (MonoidHom.id (StatedSp 2 F)).range := Group.IsPerfect.range _
  have key := ModelFacts.Orth15.ChainU.eq_of_central_ratio (MonoidHom.id (StatedSp 2 F)).range
      α.toMonoidHom (fun r _ => by
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F]
    change α r * r⁻¹ ∈ spScalars 2 F
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hαproj, mul_inv_cancel])
  intro g
  exact key g ⟨g, rfl⟩

theorem shape_of_trivial [Finite F] (h4 : Nat.card F = 3) (M : gsp 2 F) (ρ : F ≃+* F)
    (h : conjAut 2 F M * fieldAut 2 F ρ = 1) :
    ρ = 1 ∧ ∃ a : F, a ≠ 0 ∧
      ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = a • 1 := by
  have hfix := fix_of_trivial h4 M ρ h
  have hu : ∀ (k : Fin 2) (t : F),
      ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inl k) (Sum.inr k) (ρ t) =
        Matrix.transvection (Sum.inl k) (Sum.inr k) t *
          ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro k t
    have := rel_of_fixed M ρ _ (hfix (longBlock F 2 k (sl2Upper t)))
    rwa [longBlock_sl2Upper, mat_elt_positiveLong, map_transvection] at this
  have hl : ∀ (k : Fin 2) (t : F),
      ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inr k) (Sum.inl k) (ρ t) =
        Matrix.transvection (Sum.inr k) (Sum.inl k) t *
          ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro k t
    have := rel_of_fixed M ρ _ (hfix (longBlock F 2 k (sl2Lower t)))
    rwa [longBlock_sl2Lower, mat_elt_negativeLong, map_transvection] at this
  have hdet : ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (M : GL (Fin 2 ⊕ Fin 2) F).isUnit).ne_zero
  obtain ⟨hσ, a, b, ha, hb, hMab⟩ := sp4_shape ρ _ hdet hu hl
  refine ⟨hσ, a, ha, ?_⟩
  have hij : (0 : Fin 2) ≠ 1 := by decide
  set g : StatedSp 2 F :=
    CFSG.LieType.Universal.Symplectic.equivStatedSp 2 F
      (TauCeti.GLSymplecticFin.leviHom (TauCeti.transvectionUnit hij (1 : F))) with hg
  have hrel := rel_of_fixed M ρ g (hfix g)
  have hmat : mat 2 F g = Matrix.fromBlocks (Matrix.transvection (0 : Fin 2) 1 (1 : F)) 0 0
      (((TauCeti.transvectionUnit hij (1 : F))⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ := by
    rw [hg, CFSG.LieType.Universal.Symplectic.SpExtras.mat_equiv_leviHom,
      TauCeti.coe_transvectionUnit]
  subst hσ
  rw [hMab, hmat] at hrel
  have e := congrFun (congrFun hrel (Sum.inl 0)) (Sum.inl 1)
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transvection] at e
  subst e
  rw [hMab, Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

theorem normal_form_sq [Finite F] (h2 : (2 : F) ≠ 0) (h4 : Nat.card F = 3)
    (β : MulAut (StatedProj (StatedSp 2 F))) (hβ : β * β * (β * β) = 1) :
    ∃ (Nl : gsp 2 F) (τ : F ≃+* F) (l c' : F) (N₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F),
      (∀ x, τ (τ x) = x) ∧ l ≠ 0 ∧
      ((Nl : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = l • N₁ ∧
      N₁ᵀ * gram F 2 * N₁ = gram F 2 ∧ c' * c' = 1 ∧ N₁ * N₁.map τ = c' • 1 ∧
      β * β = conjAut 2 F Nl * fieldAut 2 F τ := by
  obtain ⟨A, σ, hAσ⟩ := exists_conjAut_fieldAut_sp4 h2 β
  have hsq : β * β = conjAut 2 F (A * gspFieldMap σ A) * fieldAut 2 F (σ.trans σ) := by
    rw [hAσ]; exact sq_formula A σ
  set N : gsp 2 F := A * gspFieldMap σ A with hN
  set τ : F ≃+* F := σ.trans σ with hτ
  have h4' : (conjAut 2 F N * fieldAut 2 F τ) * (conjAut 2 F N * fieldAut 2 F τ) = _ := rfl
  have hone : conjAut 2 F (N * gspFieldMap τ N) * fieldAut 2 F (τ.trans τ) = 1 := by
    rw [← sq_formula N τ, ← hsq]; exact hβ
  obtain ⟨hττ, a, ha, hMa⟩ := shape_of_trivial h4 (N * gspFieldMap τ N) (τ.trans τ) hone
  have hττ' : ∀ x, τ (τ x) = x := fun x => by
    have := RingEquiv.congr_fun hττ x
    simpa using this
  have hmul : ((multiplier 2 F N : Fˣ) : F) =
      ((multiplier 2 F A : Fˣ) : F) * σ ((multiplier 2 F A : Fˣ) : F) := by
    rw [hN, map_mul, Units.val_mul, multiplier_gspFieldMap]
  obtain ⟨l, hl⟩ := isSquare_mul_map h2 σ ((multiplier 2 F A : Fˣ) : F) (Units.ne_zero _)
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact Units.ne_zero (multiplier 2 F N) (by rw [hmul, hl]; ring)
  set Nm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((N : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hNm
  have hNspec : Nmᵀ * gram F 2 * Nm = (l * l) • gram F 2 := by
    have := multiplier_spec N
    rw [hmul, hl] at this
    exact this
  set N₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := l⁻¹ • Nm with hN₁
  have hN₁iso : N₁ᵀ * gram F 2 * N₁ = gram F 2 := by
    rw [hN₁]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hNspec, smul_smul]
    have : l⁻¹ * l⁻¹ * (l * l) = 1 := by field_simp
    rw [this, one_smul]
  have hMm : Nm * Nm.map τ = a • 1 := by
    have := hMa
    rw [Subgroup.coe_mul, Units.val_mul] at this
    exact this
  have hmapN₁ : N₁.map τ = τ l⁻¹ • Nm.map τ := by
    ext i j; simp [hN₁, Matrix.map_apply]
  have hNN : N₁ * N₁.map τ = (l⁻¹ * τ l⁻¹ * a) • 1 := by
    rw [hmapN₁, hN₁, Matrix.smul_mul, Matrix.mul_smul, hMm, smul_smul, smul_smul]
  have hc'1 : (l⁻¹ * τ l⁻¹ * a) * (l⁻¹ * τ l⁻¹ * a) = 1 := by
    have hiso' := map_isometry τ N₁ hN₁iso
    have h1 : (N₁ * N₁.map τ)ᵀ * gram F 2 * (N₁ * N₁.map τ) = gram F 2 := by
      calc (N₁ * N₁.map τ)ᵀ * gram F 2 * (N₁ * N₁.map τ) =
          (N₁.map τ)ᵀ * (N₁ᵀ * gram F 2 * N₁) * N₁.map τ := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = gram F 2 := by rw [hN₁iso]; exact hiso'
    rw [hNN] at h1
    have e := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inr 0)
    simp [Matrix.transpose_smul, gram, Matrix.fromBlocks] at e
    simpa using e
  refine ⟨N, τ, l, l⁻¹ * τ l⁻¹ * a, N₁, hττ', hl0, ?_, hN₁iso, hc'1, hNN, hsq⟩
  rw [hN₁, smul_inv_smul₀ hl0]
end Asc77.C25W.Sp

end

section

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
namespace Asc77.C25W.Sp
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C25W
open CFSG.ClassicalInvolution.Asc77.C25W.Sp
variable {F : Type} [Field F]

theorem psp4_sq_fixed [Finite F] (h2 : (2 : F) ≠ 0) (h4 : Nat.card F = 3)
    (β : MulAut (StatedProj (StatedSp 2 F))) (hβ : β * β * (β * β) = 1) :
    ∃ (u w : Fin 2 ⊕ Fin 2 → F) (s : StatedSp 2 F), form u w = 1 ∧
      s ∈ planeGroup (Submodule.span F {u, w}) ∧ orderOf (proj 2 F s) = 4 ∧
      β (β (proj 2 F s)) = proj 2 F s := by
  obtain ⟨Nl, τ, l, c', N₁, hττ, hl, hNl, hN₁, hc'1, hN₁τ, hsq⟩ := normal_form_sq h2 h4 β hβ
  obtain ⟨u, w, s, huw, hs, hs4, hsc, hcomm⟩ :=
    exists_stable_rotation (m := 0) τ N₁ hττ h2 hN₁ c' hc'1 hN₁τ
  refine ⟨u, w, s, huw, hs, orderOf_proj_eq_four hs4 hsc, ?_⟩
  have e1 : β (β (proj 2 F s)) = (β * β) (proj 2 F s) := rfl
  rw [e1, hsq, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_conjSp, mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_fieldSp, hNl]
  have e := hcomm
  rw [mat_apply] at e
  rw [Matrix.smul_mul, e, Matrix.mul_smul]
end Asc77.C25W.Sp

end

section

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.Generic
namespace Asc77.C25W.Sp
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C25W
open CFSG.ClassicalInvolution.Asc77.C25W.Sp
variable {F : Type} [Field F]

theorem psp4_model_sq [Finite F] (h2 : (2 : F) ≠ 0) (h4 : Nat.card F = 3) {Y : Type} [Group Y]
    (ψ : StatedSp 2 F →* Y) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hsurj : Function.Surjective ψ) {R R' : Subgroup (StatedSp 2 F)} {i i' : StatedSp 2 F}
    (hR : IsLongRootSp2 R i) (hR' : IsLongRootSp2 R' i') (hne : R.map ψ ≠ R'.map ψ) {z' : Y}
    (hz : IsUniqueInvolution (R.map ψ) z') (hz' : IsUniqueInvolution (R'.map ψ) z')
    (β : MulAut Y) (hβ : ∀ x : Y, β (β (β (β x))) = x) :
    ∃ (u w : Fin 2 ⊕ Fin 2 → F) (s : StatedSp 2 F), form u w = 1 ∧
      s ∈ planeGroup (Submodule.span F {u, w}) ∧ orderOf (ψ s) = 4 ∧ β (β (ψ s)) = ψ s := by
  have hk := ker_eq_spScalars h2 ψ hker hR hR' hne hz hz'
  set e := projEquiv ψ hsurj hk with he
  let β' : MulAut (StatedProj (StatedSp 2 F)) := e.trans (β.trans e.symm)
  have hβ'1 : ∀ x, e (β' x) = β (e x) := fun x => by simp [β']
  have hβ'4 : β' * β' * (β' * β') = 1 := by
    ext x
    apply e.injective
    show e (β' (β' (β' (β' x)))) = e x
    rw [hβ'1, hβ'1, hβ'1, hβ'1, hβ]
  obtain ⟨u, w, s, huw, hs, hord, hfix⟩ := psp4_sq_fixed h2 h4 β' hβ'4
  refine ⟨u, w, s, huw, hs, ?_, ?_⟩
  · rw [← projEquiv_proj ψ hsurj hk s, ← he, MulEquiv.orderOf_eq]
    exact hord
  · have h1 := congrArg e hfix
    have e1 : e (β' (β' (proj 2 F s))) = β (β (e (proj 2 F s))) := by rw [hβ'1, hβ'1]
    rw [e1] at h1
    exact h1
end Asc77.C25W.Sp

end

section

set_option linter.unusedSectionVars false
namespace Asc77.C25W
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C25W
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Models.SymplecticPairs

theorem layer5Sq_of_hom {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type} [Group Y] (t :
    StatedLieTag) (k e : ℕ)
    (hadm : StatedLieAdmissible t k p e) (ψ : (modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (ht : t = .PSp) (hk : k = 2) (h3 : p ^ e = 3)
    {R R' : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') (β : MulAut Y)
    (hβ : ∀ x : Y, β (β (β (β x))) = x) :
    ∃ R₀ ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D, ∃ s ∈ R₀,
      orderOf (ψ s) = 4 ∧ β (β (ψ s)) = ψ s := by
  subst ht hk
  have he : e ≠ 0 := by
    rintro rfl
    simp at h3
  have h2 := two_ne_zero_gf (p := p) e hp2
  have h4 : Nat.card (GaloisField p e) = 3 := by
    rw [GaloisField.card p e he]
    exact h3
  obtain ⟨P, hP, hRP⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
  obtain ⟨P', hP', hRP'⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'
  obtain ⟨i, hi⟩ := (exists_isLongRootSp2_iff h2 R).mpr ⟨P, hP, hRP⟩
  obtain ⟨i', hi'⟩ := (exists_isLongRootSp2_iff h2 R').mpr ⟨P', hP', hRP'⟩
  obtain ⟨u, w, s, huw, hs, hord, hfix⟩ :=
    Sp.psp4_model_sq h2 h4 ψ hker hsurj hi hi' hne hz hz' β hβ
  refine ⟨planeGroup (Submodule.span (GaloisField p e) {u, w}), ?_, s, hs, hord, hfix⟩
  exact (mem_fundamentalSubgroups_PSp_iff hadm _).mpr ⟨_, ⟨u, w, huw, rfl⟩, rfl⟩

theorem layer5Sq_proved : Layer5Sq := by
  intro Y _ _ Φ D A A' z' a₀ b₀ hD1 hi htw hconj β hββ
  obtain ⟨i, hi⟩ := hi
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : ∀ j : Fin D.card, Function.Surjective (D.hom j) := by
    intro j
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom j).range := by
      intro l
      rw [Subsingleton.elim l j]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hcase : ∀ j : Fin D.card, D.tag j = .PSp ∧ D.rank j = 2 := by
    intro j
    rw [Subsingleton.elim j i]
    simp only [IsOrthTag] at hi
    rcases hi with ⟨-, ht, hn⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · exact ⟨ht, hn⟩
    all_goals omega
  have hexp : ∀ j : Fin D.card, D.exp j = 1 := by
    intro j
    rcases D.exp_eq j with h | ⟨hT, -⟩
    · exact h
    · rw [(hcase j).1] at hT
      exact absurd hT (by decide)
  have hβ : ∀ x : Y, β (β (β (β x))) = x := hββ
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₂₁ : i₂ = i₁ := Subsingleton.elim _ _
  subst h₂₁
  have hq' : 3 ^ D.exp i₂ = 3 := by rw [hexp i₂]; norm_num
  have hz : IsUniqueInvolution (R.map (D.hom i₂)) z' := by
    rw [← hAR]
    exact htw.hzA
  have hz' : IsUniqueInvolution (R'.map (D.hom i₂)) z' := by
    rw [← hAR']
    exact htw.hzA'
  have hne : R.map (D.hom i₂) ≠ R'.map (D.hom i₂) := by
    rw [← hAR, ← hAR']
    exact htw.ne
  obtain ⟨R₀, hR₀, s, hs, hord, hfix⟩ :=
    layer5Sq_of_hom (by norm_num : (3 : ℕ) ≠ 2) (D.tag i₂) (D.rank i₂) (D.exp i₂) (D.admissible i₂)
        (D.hom i₂)
      (D.ker_le_center i₂) (hsurj i₂) (hcase i₂).1 (hcase i₂).2 hq' hR hR' hne hz hz' β hβ
  have hfund : D.tag i₂ ≠ .G2 ∧ D.tag i₂ ≠ .trialityD4 := by
    rw [(hcase i₂).1]
    exact ⟨by decide, by decide⟩
  have hsingle := CFSG.ClassicalInvolution.RouteD.Gaps.fundamentalSingleClass_of_ne D i₂
    hfund.1 hfund.2
  have hJ : R₀.map (D.hom i₂) ∈ Φ :=
    D.map_mem_of_single_class (fun g L hL => hconj L hL g) i₂ hsingle hR₀
  refine ⟨R₀.map (D.hom i₂), hJ, D.hom i₂ s, Subgroup.mem_map_of_mem _ hs, ?_, ?_, hfix⟩
  · have h4 : D.hom i₂ s ^ 4 = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    simpa [pow_succ, mul_assoc] using h4
  · intro h
    have h2 : orderOf (D.hom i₂ s) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hord] at h2
    omega
end Asc77.C25W

end

section

open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU (eq_of_central_ratio)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.ClassicalInvolution.Generic
namespace Asc77.C25W.Sp
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C25W
open CFSG.ClassicalInvolution.Asc77.C25W.Sp
variable {F : Type} [Field F]

theorem sp4_blocks_shape [Finite F] (h2 : (2 : F) ≠ 0) (h4 : Nat.card F = 3)
    (β : MulAut (StatedProj (StatedSp 2 F)))
    (hfix : ∀ k : Fin 2, ∀ r ∈ (longBlock F 2 k).range, β (proj 2 F r) = proj 2 F r) :
    ∃ (A : gsp 2 F) (a b : F), a ≠ 0 ∧ b ≠ 0 ∧ a * a = b * b ∧
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        Matrix.diagonal (Sum.elim ![a, b] ![a, b]) ∧ β = conjAut 2 F A := by
  obtain ⟨A, σ, hβ⟩ := exists_conjAut_fieldAut_sp4 h2 β
  set α : MulAut (StatedSp 2 F) := conjSp 2 F A * fieldSp 2 F σ with hα
  have hαproj : ∀ g, proj 2 F (α g) = β (proj 2 F g) := fun g => by rw [hβ]; rfl
  have hfixα : ∀ k : Fin 2, ∀ r ∈ (longBlock F 2 k).range, α r = r := by
    intro k
    obtain ⟨eB⟩ := (isClassicalSL2_longRootSp2 h2 k).nonempty_mulEquiv
    refine Q3T7P25.eq_of_central_ratio3_card (longRootSp2 F 2 k) h4 eB (fun z hz => ?_)
      α.toMonoidHom (fun r hr => ?_)
    · rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F] at hz
      exact Q3T7P25.mul_self_of_mem_spScalars hz
    have h : α r * r⁻¹ ∈ spScalars 2 F := by
      rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hαproj, hfix k r hr, mul_inv_cancel]
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F]
    exact h
  have hu : ∀ (k : Fin 2) (t : F),
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inl k) (Sum.inr k) (σ t) =
        Matrix.transvection (Sum.inl k) (Sum.inr k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro k t
    have hg := hfixα k (longBlock F 2 k (sl2Upper t)) ⟨_, rfl⟩
    have := rel_of_fixed A σ _ hg
    rwa [longBlock_sl2Upper, mat_elt_positiveLong, map_transvection] at this
  have hl : ∀ (k : Fin 2) (t : F),
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inr k) (Sum.inl k) (σ t) =
        Matrix.transvection (Sum.inr k) (Sum.inl k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro k t
    have hg := hfixα k (longBlock F 2 k (sl2Lower t)) ⟨_, rfl⟩
    have := rel_of_fixed A σ _ hg
    rwa [longBlock_sl2Lower, mat_elt_negativeLong, map_transvection] at this
  have hdet : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (A : GL (Fin 2 ⊕ Fin 2) F).isUnit).ne_zero
  obtain ⟨hσ, a, b, ha, hb, hAab⟩ := sp4_shape σ _ hdet hu hl
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  rw [hAab] at hμ
  have hAA : a * a = b * b := sp4_sq a b μ hμ
  subst hσ
  rw [show fieldAut 2 F (RingEquiv.refl F) = 1 from map_one _, mul_one] at hβ
  exact ⟨A, a, b, ha, hb, hAA, hAab, hβ⟩

theorem sp4_aut_blocks_fine [Finite F] (h2 : (2 : F) ≠ 0) (h4 : Nat.card F = 3)
    (β : MulAut (StatedProj (StatedSp 2 F)))
    (hfix : ∀ k : Fin 2, ∀ r ∈ (longBlock F 2 k).range, β (proj 2 F r) = proj 2 F r) :
    β = 1 ∨ β = MulAut.conj (proj 2 F (longInv F 2 1)) := by
  obtain ⟨A, a, b, ha, hb, hab, hAab, hβ⟩ := sp4_blocks_shape h2 h4 β hfix
  rcases mul_self_eq_mul_self_iff.mp hab with h | h
  ·
    left
    subst h
    have hcen : (A : GL (Fin 2 ⊕ Fin 2) F) ∈ Subgroup.center (GL (Fin 2 ⊕ Fin 2) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      refine ⟨Units.mk0 a ha, ?_⟩
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, hAab, Matrix.scalar_apply]
      congr 1
      funext i
      rcases i with i | i <;> fin_cases i <;> rfl
    have hconj : conjAut 2 F A = 1 := by
      ext p
      obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) p
      show proj 2 F (conjSp 2 F A g) = proj 2 F g
      congr 1
      apply Subtype.ext
      rw [coe_conjSp, ← Subgroup.mem_center_iff.mp hcen (g : GL (Fin 2 ⊕ Fin 2) F),
        mul_inv_cancel_right]
    rw [hβ, hconj]
  ·
    right
    rw [hβ]
    apply conjAut_eq_conj_longInv A a ha 1
    rw [hAab, mat_longInv, ← Matrix.diagonal_smul]
    congr 1
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [h, mem_coords]

theorem psp4_cent [Finite F] (h2 : (2 : F) ≠ 0) (h4 : Nat.card F = 3)
    {R R' : Subgroup (StatedSp 2 F)} (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i)
    (hne : R ≠ R') {x x' : StatedSp 2 F} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F)) (β : MulAut (StatedProj (StatedSp 2 F)))
    (hβ : ∀ r ∈ R, β (proj 2 F r) = proj 2 F r) (hβ' : ∀ r ∈ R', β (proj 2 F r) = proj 2 F r) :
    β = 1 ∨ β = MulAut.conj (proj 2 F x) := by
  obtain ⟨g, k, hRg, hR'g⟩ := twin_std_sp h2 hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  set c : MulAut (StatedProj (StatedSp 2 F)) := MulAut.conj (proj 2 F g) with hcdef
  have hcp : ∀ s, c (proj 2 F s) = proj 2 F (g * s * g⁻¹) := fun s => by
    rw [hcdef, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set β' : MulAut (StatedProj (StatedSp 2 F)) := c⁻¹ * β * c with hβ'def
  have hβ'p : ∀ s, β' (proj 2 F s) = (c⁻¹) (β (c (proj 2 F s))) := fun s => rfl
  have hfixβ' : ∀ (S T : Subgroup (StatedSp 2 F)), T = S.map (MulAut.conj g).toMonoidHom →
      (∀ r ∈ T, β (proj 2 F r) = proj 2 F r) → ∀ r ∈ S, β' (proj 2 F r) = proj 2 F r := by
    intro S T hT hfix r hr
    have hmem : g * r * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := ⟨r, hr, rfl⟩
    rw [← hT] at hmem
    rw [hβ'p, hcp, hfix _ hmem, ← hcp]
    simp
  have hk : ∀ k k₀ : Fin 2, k₀ = k ∨ k₀ = Fin.rev k := by decide
  have hfix : ∀ k₀ : Fin 2, ∀ r ∈ (longBlock F 2 k₀).range, β' (proj 2 F r) = proj 2 F r := by
    intro k₀
    rcases hk k k₀ with rfl | rfl
    · exact hfixβ' _ R hRg hβ
    · exact hfixβ' _ R' hR'g hβ'
  have hβc : β = c * β' * c⁻¹ := by rw [hβ'def]; group
  have hxg : x = g * longInv F 2 k * g⁻¹ := by
    have hxL : x ∈ (longBlock F 2 k).range.map (MulAut.conj g).toMonoidHom := by
      rw [← hRg]; exact hxR
    obtain ⟨y, hy, hyx⟩ := hxL
    have hyx' : g * y * g⁻¹ = x := hyx
    have hy2 : y * y = 1 := by
      have : g * (y * y) * g⁻¹ = 1 := by
        calc g * (y * y) * g⁻¹ = (g * y * g⁻¹) * (g * y * g⁻¹) := by group
          _ = x * x := by rw [hyx']
          _ = 1 := hx2
      have h1 : y * y = g⁻¹ * (g * (y * y) * g⁻¹) * g := by group
      rw [h1, this]; group
    have hy1 : y ≠ 1 := by
      intro h
      apply hx1
      rw [← hyx', h]; group
    have hyL : y = longInv F 2 k := by
      have hstd := isLongRootSp2_standard (K := F) (n := 2) k
      refine hstd.eq_of_orderOf_eq_two h2 ?_ (orderOf_eq_prime (by rwa [pow_two]) hy1)
      rw [longRootSp2]
      exact hy
    rw [← hyx', hyL]
  rcases sp4_aut_blocks_fine h2 h4 β' hfix with h | h
  · left
    rw [hβc, h]
    group
  · right
    have hL1 : proj 2 F (longInv F 2 1) = proj 2 F (longInv F 2 k) := by
      rcases hk k 1 with rfl | hk1
      · rfl
      · rw [hk1]
        exact proj_longInv_rev k
    have hcL : c (proj 2 F (longInv F 2 k)) = proj 2 F x := by rw [hcp, hxg]
    rw [hβc, h, hL1]
    ext p
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hcL,
      MulAut.apply_inv_self]
end Asc77.C25W.Sp

end

section

set_option linter.unusedSectionVars false
namespace Asc77.C25W
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C25W
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
namespace Sp
open CFSG.ClassicalInvolution.Asc77.C25W.Sp
variable {F : Type} [Field F]

theorem psp4_model_cent [Finite F] (h2 : (2 : F) ≠ 0) (h4 : Nat.card F = 3) {Y : Type} [Group Y]
    (ψ : StatedSp 2 F →* Y) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hsurj : Function.Surjective ψ) {R R' : Subgroup (StatedSp 2 F)} {i i' : StatedSp 2 F}
    (hR : IsLongRootSp2 R i) (hR' : IsLongRootSp2 R' i') (hne : R.map ψ ≠ R'.map ψ) {z' : Y}
    (hz : IsUniqueInvolution (R.map ψ) z') (hz' : IsUniqueInvolution (R'.map ψ) z')
    (β : MulAut Y) (hβ : ∀ y ∈ R.map ψ, β y = y) (hβ' : ∀ y ∈ R'.map ψ, β y = y) :
    β = 1 ∨ ∀ y, β y = z' * y * z'⁻¹ := by
  have hk := ker_eq_spScalars h2 ψ hker hR hR' hne hz hz'
  have hψi := psp4_map_inv_eq h2 ψ hker hR hz
  have hψi' := psp4_map_inv_eq h2 ψ hker hR' hz'
  have hcen : Subgroup.center (StatedSp 2 F) = spScalars 2 F :=
    CFSG.LieType.Universal.Symplectic.center_eq 2 F
  set e := projEquiv ψ hsurj hk with he
  let β' : MulAut (StatedProj (StatedSp 2 F)) := e.trans (β.trans e.symm)
  have hβ'e : ∀ y, e (β' (e.symm y)) = β y := fun y => by simp [β']
  have he_proj : ∀ x, e (proj 2 F x) = ψ x := fun x => projEquiv_proj ψ hsurj hk x
  have hiR : i ∈ R := (hR.isClassicalSL2 h2).mem
  have hi'R' : i' ∈ R' := (hR'.isClassicalSL2 h2).mem
  have hi2 : i * i = 1 := by
    have := pow_orderOf_eq_one i
    rwa [(hR.isClassicalSL2 h2).orderOf_eq_two, pow_two] at this
  have hi'2 : i' * i' = 1 := by
    have := pow_orderOf_eq_one i'
    rwa [(hR'.isClassicalSL2 h2).orderOf_eq_two, pow_two] at this
  have hi1 : i ≠ 1 := by
    intro h
    have := (hR.isClassicalSL2 h2).orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hi'1 : i' ≠ 1 := by
    intro h
    have := (hR'.isClassicalSL2 h2).orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hc : i' * i⁻¹ ∈ Subgroup.center (StatedSp 2 F) := by
    rw [hcen, ← hk]
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψi, hψi', mul_inv_cancel]
  have hRne : R ≠ R' := fun h => hne (by rw [h])
  have hβR : ∀ r ∈ R, β' (proj 2 F r) = proj 2 F r := by
    intro r hr
    have h1 : β (ψ r) = ψ r := hβ _ (Subgroup.mem_map_of_mem ψ hr)
    have h2' : β' (proj 2 F r) = e.symm (β (e (proj 2 F r))) := rfl
    rw [h2', he_proj, h1]
    exact e.symm_apply_eq.mpr (he_proj r).symm
  have hβR' : ∀ r ∈ R', β' (proj 2 F r) = proj 2 F r := by
    intro r hr
    have h1 : β (ψ r) = ψ r := hβ' _ (Subgroup.mem_map_of_mem ψ hr)
    have h2' : β' (proj 2 F r) = e.symm (β (e (proj 2 F r))) := rfl
    rw [h2', he_proj, h1]
    exact e.symm_apply_eq.mpr (he_proj r).symm
  rcases psp4_cent h2 h4 ⟨i, hR⟩ ⟨i', hR'⟩ hRne hiR hi2 hi1 hi'R' hi'2 hi'1 hc β' hβR hβR' with
    h | h
  · left
    ext y
    rw [← hβ'e y, h]
    simp
  · right
    intro y
    have hconj : e (proj 2 F i * e.symm y * (proj 2 F i)⁻¹) = z' * y * z'⁻¹ := by
      rw [map_mul, map_mul, map_inv, he_proj, MulEquiv.apply_symm_apply, hψi]
    rw [← hβ'e y, h, MulAut.conj_apply]
    exact hconj
end Sp
section ModelFact

@[expose] def Cent5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (D : LieSystemData 3 1 Y Φ)
    (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    D.card = 1 → (∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i)) →
    TwinSect0 Φ A A' z' a₀ b₀ →
    ∀ β : Y ≃* Y, (∀ x ∈ A, β x = x) → (∀ x ∈ A', β x = x) →
      β = 1 ∨ ∀ y : Y, β y = z' * y * z'⁻¹
end ModelFact

theorem cent5_of_hom {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type} [Group Y] (t : StatedLieTag)
    (k e : ℕ)
    (hadm : StatedLieAdmissible t k p e) (ψ : (modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (ht : t = .PSp) (hk : k = 2) (h3 : p ^ e = 3)
    {R R' : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') (β : MulAut Y)
    (hβ : ∀ y ∈ R.map ψ, β y = y) (hβ' : ∀ y ∈ R'.map ψ, β y = y) :
    β = 1 ∨ ∀ y, β y = z' * y * z'⁻¹ := by
  subst ht hk
  have he : e ≠ 0 := by
    rintro rfl
    simp at h3
  have h2 := two_ne_zero_gf (p := p) e hp2
  have h4 : Nat.card (GaloisField p e) = 3 := by
    rw [GaloisField.card p e he]
    exact h3
  obtain ⟨P, hP, hRP⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
  obtain ⟨P', hP', hRP'⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'
  obtain ⟨i, hi⟩ := (exists_isLongRootSp2_iff h2 R).mpr ⟨P, hP, hRP⟩
  obtain ⟨i', hi'⟩ := (exists_isLongRootSp2_iff h2 R').mpr ⟨P', hP', hRP'⟩
  exact Sp.psp4_model_cent h2 h4 ψ hker hsurj hi hi' hne hz hz' β hβ hβ'

theorem cent5_proved : Cent5 := by
  intro Y _ _ Φ D A A' z' a₀ b₀ hD1 hi htw β hA hA'
  obtain ⟨i, hi⟩ := hi
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : ∀ j : Fin D.card, Function.Surjective (D.hom j) := by
    intro j
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom j).range := by
      intro l
      rw [Subsingleton.elim l j]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hcase : ∀ j : Fin D.card, D.tag j = .PSp ∧ D.rank j = 2 := by
    intro j
    rw [Subsingleton.elim j i]
    simp only [IsOrthTag] at hi
    rcases hi with ⟨-, ht, hn⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · exact ⟨ht, hn⟩
    all_goals omega
  have hexp : ∀ j : Fin D.card, D.exp j = 1 := by
    intro j
    rcases D.exp_eq j with h | ⟨hT, -⟩
    · exact h
    · rw [(hcase j).1] at hT
      exact absurd hT (by decide)
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₂₁ : i₂ = i₁ := Subsingleton.elim _ _
  subst h₂₁
  have hq' : 3 ^ D.exp i₂ = 3 := by rw [hexp i₂]; norm_num
  have hz : IsUniqueInvolution (R.map (D.hom i₂)) z' := by
    rw [← hAR]
    exact htw.hzA
  have hz' : IsUniqueInvolution (R'.map (D.hom i₂)) z' := by
    rw [← hAR']
    exact htw.hzA'
  have hne : R.map (D.hom i₂) ≠ R'.map (D.hom i₂) := by
    rw [← hAR, ← hAR']
    exact htw.ne
  exact cent5_of_hom (by norm_num : (3 : ℕ) ≠ 2) (D.tag i₂) (D.rank i₂) (D.exp i₂) (D.admissible
      i₂) (D.hom i₂)
    (D.ker_le_center i₂) (hsurj i₂) (hcase i₂).1 (hcase i₂).2 hq' hR hR' hne hz hz' β
    (by rw [← hAR]; exact hA) (by rw [← hAR']; exact hA')
end Asc77.C25W

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX.Sp
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.ClassicalInvolution.Asc77.CX.Sp
open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
    CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 CFSG.ClassicalInvolution.Generic
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups
variable {F : Type} [Field F]

theorem oddCoreOf_map_longRoot_eq_bot [Finite F] (h2 : (2 : F) ≠ 0)
    {Y : Type} [Group Y] (ψ : StatedSp 2 F →* Y)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) {R : Subgroup (StatedSp 2 F)}
    {i : StatedSp 2 F} (hR : IsLongRootSp2 R i) :
    Asc77.oddCoreOf (R.map ψ) = ⊥ := by
  have hinj : Function.Injective (ψ.comp R.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxk : (x : StatedSp 2 F) ∈ ψ.ker := hx
    have hxc := hker hxk
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F] at hxc
    exact Subgroup.mem_bot.mpr (Subtype.ext (eq_one_of_mem_longRoot_of_mem_spScalars hR x.2 hxc))
  have hrange : (ψ.comp R.subtype).range = R.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨e⟩ := (hR.isClassicalSL2 h2).nonempty_mulEquiv
  let e₁ : ↥(R.map ψ) ≃* SL(2, F) :=
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans e
  have hO : classicalInvolutionOddCore ↥(R.map ψ) = ⊥ := by
    have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant e₁
    have h3 : classicalInvolutionOddCore SL(2, F) = ⊥ :=
      CFSG.ClassicalInvolution.Asc77.CX.CX4.L4.oddCore_sl2_eq_bot_odd h2
    have h4' : (classicalInvolutionOddCore ↥(R.map ψ)).map e₁.toMonoidHom = ⊥ := by
      rw [← h3]
      exact h1
    rwa [Subgroup.map_eq_bot_iff_of_injective _ e₁.injective] at h4'
  unfold Asc77.oddCoreOf
  rw [hO, Subgroup.map_bot]

theorem center_eq_bot_of_twin [Finite F] (h2 : (2 : F) ≠ 0) (h4 : Nat.card F = 3) {Y : Type}
    [Group Y] (ψ : StatedSp 2 F →* Y) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hsurj : Function.Surjective ψ) {R R' : Subgroup (StatedSp 2 F)} {i i' : StatedSp 2 F}
    (hR : IsLongRootSp2 R i) (hR' : IsLongRootSp2 R' i') (hne : R.map ψ ≠ R'.map ψ) {z' : Y}
    (hz : IsUniqueInvolution (R.map ψ) z') (hz' : IsUniqueInvolution (R'.map ψ) z') :
    Subgroup.center Y = ⊥ := by
  have hk := C25W.Sp.ker_eq_spScalars h2 ψ hker hR hR' hne hz hz'
  set e := C25W.Sp.projEquiv ψ hsurj hk with he
  have hsimp : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inr (Or.inl ⟨h4, le_rfl⟩))
  have hperf : Group.IsPerfect (StatedSp 2 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple (n := 2) (F := F) (by norm_num)
      (Or.inr (Or.inl ⟨h4, le_rfl⟩))).1
  have hperfP : Group.IsPerfect (StatedProj (StatedSp 2 F)) :=
    Group.IsPerfect.ofSurjective (f := proj 2 F) proj_surjective
  have hcP : Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedProj (StatedSp 2 F)))
      with h | h
    · exact h
    · exfalso
      have hcomm : ∀ a b : StatedProj (StatedSp 2 F), a * b = b * a := fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
      have hbot : ⁅(⊤ : Subgroup (StatedProj (StatedSp 2 F))),
          (⊤ : Subgroup (StatedProj (StatedSp 2 F)))⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        exact Subgroup.mem_centralizer_iff.mpr fun y _ => (hcomm y x)
      have htop : ⁅(⊤ : Subgroup (StatedProj (StatedSp 2 F))),
          (⊤ : Subgroup (StatedProj (StatedSp 2 F)))⁆ = ⊤ := hperfP.commutator_eq_top
      have : (⊤ : Subgroup (StatedProj (StatedSp 2 F))) = ⊥ := htop.symm.trans hbot
      exact (IsSimpleGroup.toNontrivial).exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
        hab (by
          have ha' : a ∈ (⊥ : Subgroup _) := this ▸ Subgroup.mem_top a
          have hb' : b ∈ (⊥ : Subgroup _) := this ▸ Subgroup.mem_top b
          rw [Subgroup.mem_bot] at ha' hb'
          rw [ha', hb'])
  rw [eq_bot_iff]
  intro x hx
  have hx' : e.symm x ∈ Subgroup.center (StatedProj (StatedSp 2 F)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hx (e g)
  rw [hcP, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot, ← e.apply_symm_apply x, hx', map_one]
end Asc77.CX.Sp
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Models.SymplecticPairs

theorem layer5_facts_of_hom {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type} [Group Y] (t :
    StatedLieTag) (k e : ℕ)
    (hadm : StatedLieAdmissible t k p e) (ψ : (modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (ht : t = .PSp) (hk : k = 2) (h3 : p ^ e = 3)
    {R R' : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') :
    Subgroup.center Y = ⊥ ∧ oddCoreOf (R.map ψ) = ⊥ ∧ oddCoreOf (R'.map ψ) = ⊥ := by
  subst ht hk
  have he : e ≠ 0 := by
    rintro rfl
    simp at h3
  have h2 := C25W.two_ne_zero_gf (p := p) e hp2
  have h4 : Nat.card (GaloisField p e) = 3 := by
    rw [GaloisField.card p e he]
    exact h3
  obtain ⟨P, hP, hRP⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
  obtain ⟨P', hP', hRP'⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'
  obtain ⟨i, hi⟩ := (exists_isLongRootSp2_iff h2 R).mpr ⟨P, hP, hRP⟩
  obtain ⟨i', hi'⟩ := (exists_isLongRootSp2_iff h2 R').mpr ⟨P', hP', hRP'⟩
  exact ⟨Sp.center_eq_bot_of_twin h2 h4 ψ hker hsurj hi hi' hne hz hz',
    Sp.oddCoreOf_map_longRoot_eq_bot h2 ψ hker hi,
    Sp.oddCoreOf_map_longRoot_eq_bot h2 ψ hker hi'⟩

theorem layer5_facts {Y : Type} [Group Y]
    {Φ : Set (Subgroup Y)} (D : LieSystemData 3 1 Y Φ) {A A' : Subgroup Y} {z' a₀ b₀ : Y}
    (hD1 : D.card = 1) (hi : ∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i))
    (htw : TwinSect0 Φ A A' z' a₀ b₀) :
    Subgroup.center Y = ⊥ ∧ oddCoreOf A = ⊥ ∧ oddCoreOf A' = ⊥ := by
  obtain ⟨i, hi⟩ := hi
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : ∀ j : Fin D.card, Function.Surjective (D.hom j) := by
    intro j
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom j).range := by
      intro l
      rw [Subsingleton.elim l j]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hcase : ∀ j : Fin D.card, D.tag j = .PSp ∧ D.rank j = 2 := by
    intro j
    rw [Subsingleton.elim j i]
    simp only [IsOrthTag] at hi
    rcases hi with ⟨-, ht, hn⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · exact ⟨ht, hn⟩
    all_goals omega
  have hexp : ∀ j : Fin D.card, D.exp j = 1 := by
    intro j
    rcases D.exp_eq j with h | ⟨hT, -⟩
    · exact h
    · rw [(hcase j).1] at hT
      exact absurd hT (by decide)
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₂₁ : i₂ = i₁ := Subsingleton.elim _ _
  subst h₂₁
  have hq' : 3 ^ D.exp i₂ = 3 := by rw [hexp i₂]; norm_num
  have hz : IsUniqueInvolution (R.map (D.hom i₂)) z' := by
    rw [← hAR]
    exact htw.hzA
  have hz' : IsUniqueInvolution (R'.map (D.hom i₂)) z' := by
    rw [← hAR']
    exact htw.hzA'
  have hne : R.map (D.hom i₂) ≠ R'.map (D.hom i₂) := by
    rw [← hAR, ← hAR']
    exact htw.ne
  rw [hAR, hAR']
  exact layer5_facts_of_hom (by norm_num : (3 : ℕ) ≠ 2) (D.tag i₂) (D.rank i₂) (D.exp i₂)
      (D.admissible i₂) (D.hom i₂)
    (D.ker_le_center i₂) (hsurj i₂) (hcase i₂).1 (hcase i₂).2 hq' hR hR' hne hz hz'
end Asc77.CX

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
section Facts

theorem layerTwinFacts_five_proved {Y : Type} [Group Y] [Finite Y]
    {Φ : Set (Subgroup Y)} (D : LieSystemData 3 1 Y Φ) {A A' : Subgroup Y} {z' a₀ b₀ : Y}
    (hD1 : D.card = 1) (hi : ∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i))
    (htw : TwinSect0 Φ A A' z' a₀ b₀) : LayerTwinFacts A A' z' := by
  classical
  obtain ⟨hcen, hO, hO'⟩ := layer5_facts D hD1 hi htw
  have hcent := C25W.cent5_proved Y Φ D A A' z' a₀ b₀ hD1 hi htw
  have hz2 : z' * z' = 1 := htw.hzA.sq
  have hcc : MulAut.conj z' * MulAut.conj z' = 1 := by
    rw [← map_mul, hz2, map_one]
  have hmem : ∀ β : MulAut Y, (∀ y ∈ A, β y = y) → (∀ y ∈ A', β y = y) →
      β = 1 ∨ β = MulAut.conj z' := by
    intro β hβ hβ'
    rcases hcent β hβ hβ' with h | h
    · exact Or.inl h
    · right
      ext y
      exact h y
  refine ⟨hcen, hO, hO', fun P _ hP => ?_, fun β hβ hβ' _ h1 hc => ?_⟩
  · refine ⟨fun β hβP => ?_, ?_⟩
    · rcases hmem β (hP β hβP).1 (hP β hβP).2 with rfl | rfl
      · exact mul_one 1
      · exact hcc
    · have hinj : Function.Injective
          (fun β : P => if (β : MulAut Y) = 1 then (0 : Fin 2) else 1) := by
        intro β₁ β₂ h
        apply Subtype.ext
        by_cases h₁ : (β₁ : MulAut Y) = 1 <;> by_cases h₂ : (β₂ : MulAut Y) = 1 <;>
          simp only [h₁, h₂, ↓reduceIte] at h
        · rw [h₁, h₂]
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · rw [(hmem β₁ (hP β₁ β₁.2).1 (hP β₁ β₁.2).2).resolve_left h₁,
            (hmem β₂ (hP β₂ β₂.2).1 (hP β₂ β₂.2).2).resolve_left h₂]
      have h2 : Nat.card P ≤ Nat.card (Fin 2) := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_fin] at h2
      omega
  · rcases hmem β hβ hβ' with h | h
    · exact absurd h h1
    · exact absurd h hc
end Facts
end Asc77.CX

end

end CFSG.ClassicalInvolution.Q3.Q3T8
