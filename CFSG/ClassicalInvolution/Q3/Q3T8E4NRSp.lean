module

public import CFSG.ClassicalInvolution.Q3.Q3T8E4NR
public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen
public import CFSG.ClassicalInvolution.Q3.Q3T8E4NRDef

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.E4NR3

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.ClassicalInvolution.Asc77.T8W (sp4_shape_one sp4_entries diagonal_commute_blockMat
  swapMat swapMat_symp comm_of_conj_conj)
open CFSG.ClassicalInvolution.RouteD (ker_proj_eq_center)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation)
open CFSG.ClassicalInvolution.Q3.Q3Z (isPerfect_sp4_three)
open CFSG.ClassicalInvolution.Q3.Q3TPS (ringChar_galoisField_three_ne_two)
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

section Lift

theorem exists_semilinear_lift3' {X : Type} [Group X] (ψ : StatedSp 2 𝔽₃ →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 𝔽₃)) (τ : X ≃* X) :
    ∃ (A : gsp 2 𝔽₃) (σ : 𝔽₃ ≃+* 𝔽₃),
      ∀ x : StatedSp 2 𝔽₃, τ (ψ x) = ψ (conjSp 2 𝔽₃ A (fieldSp 2 𝔽₃ σ x)) := by
  classical
  have hperf : Group.IsPerfect (StatedSp 2 𝔽₃) := isPerfect_sp4_three
  obtain ⟨β, hβ, -⟩ := exists_mulEquiv_of_central_cover (π := proj 2 𝔽₃) proj_surjective
    (ker_proj_eq_center 2) (θ := ψ) hψ hker τ
  obtain ⟨hall, -, -⟩ := odd_symplectic_automorphism_semilinear_representation (r := 2)
    ringChar_galoisField_three_ne_two le_rfl
  obtain ⟨A, σ, hAσ⟩ := hall β
  refine ⟨A, σ, ?_⟩
  let α : StatedSp 2 𝔽₃ →* StatedSp 2 𝔽₃ :=
    (conjSp 2 𝔽₃ A).toMonoidHom.comp (fieldSp 2 𝔽₃ σ).toMonoidHom
  have hα : ∀ x, proj 2 𝔽₃ (α x) = β (proj 2 𝔽₃ x) := fun x => by
    rw [hAσ, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
    rfl
  intro x
  exact (hβ α hα x).symm

end Lift


section Square

theorem ker_pow_three_eq_one {X : Type} [Group X] (ψ : StatedSp 2 𝔽₃ →* X)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 𝔽₃)) :
    ∀ z ∈ ψ.ker, z ^ 3 = 1 → z = 1 := by
  intro z hz hz3
  have hz2 : z * z = 1 := mul_self_eq_one_of_mem_center (by norm_num) (hker hz)
  calc z = z ^ 3 * (z * z)⁻¹ := by group
    _ = 1 := by rw [hz3, hz2]; group

theorem fin2_rev_cases (k j : Fin 2) : j = k ∨ j = Fin.rev k := by
  revert k j
  decide

theorem sq_eq_one_of_ne_zero_gf3 {a : 𝔽₃} (ha : a ≠ 0) : a * a = 1 := by
  have : Fintype 𝔽₃ := Fintype.ofFinite _
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  have hc : Fintype.card 𝔽₃ = 3 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num)]
    norm_num
  rw [hc] at h
  simpa [pow_two] using h

theorem sp4_sq_one3 {Y : Type} [Group Y] (ψ : StatedSp 2 𝔽₃ →* Y) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 𝔽₃)) (k : Fin 2) (σ : MulAut Y)
    (h0 : ∀ r ∈ (longBlock 𝔽₃ 2 k).range, σ (ψ r) = ψ r)
    (h1 : ∀ r ∈ (longBlock 𝔽₃ 2 (Fin.rev k)).range, σ (ψ r) = ψ r) : σ * σ = 1 := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  obtain ⟨A, τ, hAτ⟩ := exists_semilinear_lift3' ψ hψ hker σ
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (StatedSp 2 𝔽₃),
      ∀ g, α g = conjSp 2 𝔽₃ A (fieldSp 2 𝔽₃ τ g) :=
    ⟨conjSp 2 𝔽₃ A * fieldSp 2 𝔽₃ τ, fun g => rfl⟩
  have hlift : ∀ x, ψ (α x) = σ (ψ x) := fun x => by rw [hαdef]; exact (hAτ x).symm
  have hk3 := ker_pow_three_eq_one ψ hker
  have hfixj : ∀ j : Fin 2, (∀ r ∈ (longBlock 𝔽₃ 2 j).range, σ (ψ r) = ψ r) →
      ∀ r ∈ (longBlock 𝔽₃ 2 j).range, α r = r := by
    intro j hj
    refine E4G3.fix_of_gen3 ψ hker hk3 α.toMonoidHom ?_ (fun r hr => by
      show ψ (α r) = ψ r
      rw [hlift, hj r hr])
    have := (ModelFacts.gen3_top_sl2 (F := 𝔽₃)).map (longBlock 𝔽₃ 2 j)
    rwa [← MonoidHom.range_eq_map] at this
  set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔽₃ :=
    ((A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔽₃) with hAm
  have hdet : Am.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (A : GL (Fin 2 ⊕ Fin 2) 𝔽₃).isUnit).ne_zero
  have hrel : ∀ j : Fin 2, (∀ r ∈ (longBlock 𝔽₃ 2 j).range, α r = r) →
      (∀ t : 𝔽₃, Am * Matrix.transvection (Sum.inl j) (Sum.inr j) (τ t) =
        Matrix.transvection (Sum.inl j) (Sum.inr j) t * Am) ∧
      (∀ t : 𝔽₃, Am * Matrix.transvection (Sum.inr j) (Sum.inl j) (τ t) =
        Matrix.transvection (Sum.inr j) (Sum.inl j) t * Am) := by
    intro j hfix
    refine ⟨fun t => ?_, fun t => ?_⟩
    · have hg := hfix (longBlock 𝔽₃ 2 j (sl2Upper t)) ⟨_, rfl⟩
      have := rel_of_fixed A τ _ ((hαdef _).symm.trans hg)
      rwa [longBlock_sl2Upper, mat_elt_positiveLong, map_transvection] at this
    · have hg := hfix (longBlock 𝔽₃ 2 j (sl2Lower t)) ⟨_, rfl⟩
      have := rel_of_fixed A τ _ ((hαdef _).symm.trans hg)
      rwa [longBlock_sl2Lower, mat_elt_negativeLong, map_transvection] at this
  obtain ⟨hu0, hl0⟩ := hrel k (hfixj k h0)
  obtain ⟨hu1, hl1⟩ := hrel (Fin.rev k) (hfixj (Fin.rev k) h1)
  obtain ⟨hτ1, a, ha, r1, r2, c1, c2, d1, d2⟩ := sp4_shape_one τ Am hdet k hu0 hl0
  obtain ⟨-, b, hb, r1', r2', c1', c2', d1', d2'⟩ := sp4_shape_one τ Am hdet (Fin.rev k) hu1 hl1
  subst hτ1
  have hrk : Fin.rev k ≠ k := by fin_cases k <;> decide
  have hoff : ∀ c e, c ≠ e → Am c e = 0 := by
    intro c e hce
    rcases c with i | i
    · rcases fin2_rev_cases k i with rfl | rfl
      · exact r1 e hce.symm
      · rcases e with j | j
        · rcases fin2_rev_cases k j with rfl | rfl
          · exact c1 _ (fun h => hrk (Sum.inl.inj h))
          · exact r1' _ hce.symm
        · rcases fin2_rev_cases k j with rfl | rfl
          · exact c2 _ (by simp)
          · exact r1' _ hce.symm
    · rcases fin2_rev_cases k i with rfl | rfl
      · exact r2 e hce.symm
      · rcases e with j | j
        · rcases fin2_rev_cases k j with rfl | rfl
          · exact c1 _ (by simp)
          · exact r2' _ hce.symm
        · rcases fin2_rev_cases k j with rfl | rfl
          · exact c2 _ (fun h => hrk (Sum.inr.inj h))
          · exact r2' _ hce.symm
  have hdiag : Am = Matrix.diagonal (fun c => Am c c) := by
    ext c e
    by_cases hce : c = e
    · subst hce
      simp
    · rw [Matrix.diagonal_apply_ne _ hce]
      exact hoff c e hce
  have haa : a * a = 1 := sq_eq_one_of_ne_zero_gf3 ha
  have hbb : b * b = 1 := sq_eq_one_of_ne_zero_gf3 hb
  have hentry : ∀ c, Am c c * Am c c = 1 := by
    intro c
    rcases c with i | i
    · rcases fin2_rev_cases k i with rfl | rfl
      · rw [d1]
        exact haa
      · rw [d1']
        exact hbb
    · rcases fin2_rev_cases k i with rfl | rfl
      · rw [d2]
        exact haa
      · rw [d2']
        exact hbb
  have hAA : Am * Am = 1 := by
    rw [hdiag, Matrix.diagonal_mul_diagonal]
    ext c e
    by_cases hce : c = e
    · subst hce
      simp [hentry c]
    · simp [Matrix.diagonal_apply_ne _ hce, Matrix.one_apply_ne hce]
  have hAAu : (A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) * (A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_one]
    exact hAA
  have hαrefl : ∀ g, α g = conjSp 2 𝔽₃ A g := fun g => by
    rw [hαdef, show fieldSp 2 𝔽₃ (RingEquiv.refl 𝔽₃) = 1 from map_one _]
    rfl
  have hα2 : ∀ g, α (α g) = g := by
    intro g
    apply Subtype.ext
    rw [hαrefl, hαrefl, coe_conjSp, coe_conjSp, inv_eq_of_mul_eq_one_right hAAu]
    calc (A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) * ((A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) * (g : GL (Fin 2 ⊕ Fin 2) 𝔽₃) *
        (A : GL (Fin 2 ⊕ Fin 2) 𝔽₃)) * (A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) =
        ((A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) * (A : GL (Fin 2 ⊕ Fin 2) 𝔽₃)) * (g : GL (Fin 2 ⊕ Fin 2) 𝔽₃) *
          ((A : GL (Fin 2 ⊕ Fin 2) 𝔽₃) * (A : GL (Fin 2 ⊕ Fin 2) 𝔽₃)) := by group
      _ = g := by rw [hAAu]; group
  ext y
  obtain ⟨x, rfl⟩ := hψ y
  show σ (σ (ψ x)) = ψ x
  rw [← hlift, ← hlift, hα2]

end Square


section Inner

theorem e4_sp_inner3 {X : Type} [Group X]
    (ψ : StatedSp 2 𝔽₃ →* X) {R R' : Subgroup (StatedSp 2 𝔽₃)} {y y' : StatedSp 2 𝔽₃}
    (hP : E4Pair3N ψ R R' y y') (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i) :
    ∀ s : StatedSp 2 𝔽₃, (∀ r ∈ R, s * r = r * s) → (∀ r ∈ R', s * r = r * s) →
      ∀ k ∈ ψ.ker, s * s ≠ y * y' * k := by
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  intro s hs hs' k hk hsk
  have hc : y' * y⁻¹ ∈ Subgroup.center (StatedSp 2 𝔽₃) := by
    have := hP.cen
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
    rw [hyi, ← hP.comm y hP.hy y' hP.hy']
    exact this
  obtain ⟨g, k₀, hRg, hR'g⟩ := twin_std_sp h2 hR hR' hP.ne hP.hy
    hP.hy2 hP.hy1 hP.hy' hP.hy'2 hP.hy'1 hc
  have hcomm : ∀ (L S₁ : Subgroup (StatedSp 2 𝔽₃)),
      S₁ = L.map (MulAut.conj g).toMonoidHom → (∀ r ∈ S₁, s * r = r * s) →
      ∀ r ∈ L, (g⁻¹ * s * g) * r = r * (g⁻¹ * s * g) := by
    intro L S₁ hS₁ hS r hr
    have hmem : g * r * g⁻¹ ∈ S₁ := by
      rw [hS₁]
      exact ⟨r, hr, rfl⟩
    have h := hS _ hmem
    calc (g⁻¹ * s * g) * r = g⁻¹ * (s * (g * r * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * r * g⁻¹) * s) * g := by rw [h]
      _ = r * (g⁻¹ * s * g) := by group
  have hcommj : ∀ j : Fin 2, ∀ r ∈ (longBlock 𝔽₃ 2 j).range,
      (g⁻¹ * s * g) * r = r * (g⁻¹ * s * g) := by
    intro j
    rcases fin2_rev_cases k₀ j with rfl | rfl
    · exact hcomm _ R hRg hs
    · exact hcomm _ R' hR'g hs'
  generalize hs₀ : g⁻¹ * s * g = s₀ at hcommj
  have hu : ∀ (j : Fin 2) (t : 𝔽₃),
      mat 2 𝔽₃ s₀ * Matrix.transvection (Sum.inl j) (Sum.inr j) t =
        Matrix.transvection (Sum.inl j) (Sum.inr j) t * mat 2 𝔽₃ s₀ := by
    intro j t
    have hg := hcommj j (longBlock 𝔽₃ 2 j (sl2Upper t)) ⟨_, rfl⟩
    have := congrArg (mat 2 𝔽₃) hg
    rwa [map_mul, map_mul, longBlock_sl2Upper, mat_elt_positiveLong] at this
  have hl : ∀ (j : Fin 2) (t : 𝔽₃),
      mat 2 𝔽₃ s₀ * Matrix.transvection (Sum.inr j) (Sum.inl j) t =
        Matrix.transvection (Sum.inr j) (Sum.inl j) t * mat 2 𝔽₃ s₀ := by
    intro j t
    have hg := hcommj j (longBlock 𝔽₃ 2 j (sl2Lower t)) ⟨_, rfl⟩
    have := congrArg (mat 2 𝔽₃) hg
    rwa [map_mul, map_mul, longBlock_sl2Lower, mat_elt_negativeLong] at this
  have hdet : (mat 2 𝔽₃ s₀).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (s₀ : GL (Fin 2 ⊕ Fin 2) 𝔽₃).isUnit).ne_zero
  obtain ⟨-, a, b, ha, hb, hab⟩ := sp4_shape (RingEquiv.refl 𝔽₃)
    (mat 2 𝔽₃ s₀) hdet (fun j t => by simpa using hu j t) (fun j t => by simpa using hl j t)
  have hsymp := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp s₀.2
  have hsymp' : (mat 2 𝔽₃ s₀)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * mat 2 𝔽₃ s₀ =
      Matrix.fromBlocks 0 1 (-1) 0 := hsymp
  rw [hab, Matrix.diagonal_transpose] at hsymp'
  have e0 := congrFun (congrFun hsymp' (Sum.inl 0)) (Sum.inr 0)
  have e1 := congrFun (congrFun hsymp' (Sum.inl 1)) (Sum.inr 1)
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul] at e0 e1
  have hss : s₀ * s₀ = 1 := by
    apply mat_injective
    rw [map_mul, map_one, hab, diag_sq a b (by rw [e0, e1]), e0, one_smul]
  have hs : s = g * s₀ * g⁻¹ := by rw [← hs₀]; group
  have hsq : s * s = 1 := by
    calc s * s = (g * s₀ * g⁻¹) * (g * s₀ * g⁻¹) := by rw [← hs]
      _ = g * (s₀ * s₀) * g⁻¹ := by group
      _ = 1 := by rw [hss]; group
  rw [hsq] at hsk
  exact hP.nontwin (by rw [eq_inv_of_mul_eq_one_left hsk.symm]; exact ψ.ker.inv_mem hk)

end Inner

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.E4NR3
