module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Klein
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Spin

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped commutatorElement

section Sq

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem sq_mem_elementaryGroup (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)
    {w : V ≃ₗ[F] V} (hw : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    w * w ∈ elementaryGroup Q := by
  have hcomm := commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero h2 hQ h₁₂ h₁₃ h₂₃
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  let M : Subgroup (V ≃ₗ[F] V) :=
    { carrier := {w | w ∈ O ∧ w * w ∈ elementaryGroup Q}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro w₁ w₂ ⟨hw₁, hw₁'⟩ ⟨hw₂, hw₂'⟩
        refine ⟨mul_mem hw₁ hw₂, ?_⟩
        have hc : ⁅w₁⁻¹, w₂⁆ ∈ elementaryGroup Q := by
          rw [← hcomm]
          exact Subgroup.commutator_mem_commutator (inv_mem hw₁) hw₂
        have e : w₁ * w₂ * (w₁ * w₂) = (w₁ * w₁) * ⁅w₁⁻¹, w₂⁆ * (w₂ * w₂) := by
          simp only [commutatorElement_def, inv_inv]
          group
        rw [e]
        exact mul_mem (mul_mem hw₁' hc) hw₂'
      inv_mem' := by
        rintro w ⟨hw, hw'⟩
        refine ⟨inv_mem hw, ?_⟩
        have e : w⁻¹ * w⁻¹ = (w * w)⁻¹ := by group
        rw [e]
        exact inv_mem hw' }
  have hrefl : Subgroup.closure (Set.range (reflect Q)) ≤ M := by
    rw [Subgroup.closure_le]
    rintro _ ⟨v, rfl⟩
    exact ⟨reflect_mem_orthogonalGroup Q v, by
      rw [reflect_mul_self]
      exact one_mem _⟩
  exact (hrefl (orthogonalGroup_le_closure_reflect h2 hQ hw)).2

end Sq

section Mat

variable {F : Type} [Field F]

theorem exists_scalar_of_commute_E (T : Matrix (Fin 2) (Fin 2) F →ₗ[F] Matrix (Fin 2) (Fin 2) F)
    (hL₁ : ∀ X, T (!![0, 1; 0, 0] * X) = !![0, 1; 0, 0] * T X)
    (hL₂ : ∀ X, T (!![0, 0; 1, 0] * X) = !![0, 0; 1, 0] * T X)
    (hR₁ : ∀ X, T (X * !![0, 1; 0, 0]) = T X * !![0, 1; 0, 0])
    (hR₂ : ∀ X, T (X * !![0, 0; 1, 0]) = T X * !![0, 0; 1, 0]) :
    ∃ c : F, ∀ X, T X = c • X := by
  set C := T 1 with hC
  have h12 : !![0, 1; 0, 0] * C = C * !![0, 1; 0, 0] := by
    have a := hL₁ 1
    have b := hR₁ 1
    rw [mul_one] at a
    rw [one_mul] at b
    rw [← a, ← b]
  have h21 : !![0, 0; 1, 0] * C = C * !![0, 0; 1, 0] := by
    have a := hL₂ 1
    have b := hR₂ 1
    rw [mul_one] at a
    rw [one_mul] at b
    rw [← a, ← b]
  have e1 := congrFun (congrFun h12 0) 0
  have e2 := congrFun (congrFun h12 0) 1
  have e3 := congrFun (congrFun h21 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have hCs : C = C 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e1, e2, e3]
  have hdec : ∀ X : Matrix (Fin 2) (Fin 2) F, X = X 0 0 • !![1, 0; 0, 0] + X 0 1 • !![0, 1; 0, 0] +
      X 1 0 • !![0, 0; 1, 0] + X 1 1 • !![0, 0; 0, 1] := by
    intro X
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have t12 : T !![0, 1; 0, 0] = !![0, 1; 0, 0] * C := by
    have := hL₁ 1
    rwa [mul_one] at this
  have t21 : T !![0, 0; 1, 0] = !![0, 0; 1, 0] * C := by
    have := hL₂ 1
    rwa [mul_one] at this
  have t11 : T !![1, 0; 0, 0] = !![1, 0; 0, 0] * C := by
    have e : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 0, 0] * !![0, 0; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [e, hL₁, t21, ← mul_assoc]
  have t22 : T !![0, 0; 0, 1] = !![0, 0; 0, 1] * C := by
    have e : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) = !![0, 0; 1, 0] * !![0, 1; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [e, hL₂, t12, ← mul_assoc]
  obtain ⟨c, hc⟩ : ∃ c : F, C = c • (1 : Matrix (Fin 2) (Fin 2) F) := ⟨C 0 0, hCs⟩
  refine ⟨c, fun X => ?_⟩
  have hTX : T X = X * C := by
    conv_lhs => rw [hdec X]
    simp only [map_add, map_smul, t11, t12, t21, t22]
    conv_rhs => rw [hdec X]
    simp only [add_mul, smul_mul_assoc]
  rw [hTX, hc, mul_smul_comm, mul_one]

end Mat

section Centralizer

open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem swap_La_incl (fr : Frame Q) (B : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F) :
    fr.swap.La B (fr.incl X) =
      fr.incl (X * sigmaLin (B : Matrix (Fin 2) (Fin 2) F)) := by
  have h := twinInv_incl fr (1 : SL(2, F)) B X
  have e : twinInv fr (1 : SL(2, F)) B = fr.swap.La B := by
    unfold twinInv
    rw [map_one, one_mul]
  rw [e] at h
  rw [h]
  simp

theorem scalar_on_span_of_commute (h2 : (2 : F) ≠ 0) (fr : Frame Q) {a : V ≃ₗ[F] V}
    (hLa : ∀ A : SL(2, F), a * fr.La A = fr.La A * a)
    (hsw : ∀ B : SL(2, F), a * fr.swap.La B = fr.swap.La B * a) :
    (∃ c : F, ∀ x ∈ fr.span, a x = c • x) ∧ ∀ x ∈ fr.perp, a x ∈ fr.perp := by
  have hz : ∀ x, a (fr.La (-1) x) = fr.La (-1) (a x) := fun x => by
    have := congrArg (fun g : V ≃ₗ[F] V => g x) (hLa (-1))
    simpa using this
  have hspan : ∀ x ∈ fr.span, a x ∈ fr.span := by
    intro x hx
    obtain ⟨hdec, hr⟩ := decomp_span_perp fr (a x)
    set s := fr.incl (fr.coords (a x)) with hs
    set r := a x - s with hr'
    have h1 : fr.La (-1) (a x) = -(a x) := by
      rw [← hz, La_neg_one_of_mem_span fr hx, map_neg]
    have h2' : fr.La (-1) (a x) = -s + r := by
      conv_lhs => rw [hdec]
      rw [map_add, La_neg_one_of_mem_span fr ⟨_, rfl⟩, La_neg_one_of_mem_perp fr hr]
    have h3 : r = 0 := by
      have : r + r = 0 := by
        have e : -(a x) = -s + r := h1.symm.trans h2'
        have e2 : a x = s + r := by rw [hr']; abel
        rw [e2] at e
        have e3 : -(s + r) = -s - r := by abel
        rw [e3] at e
        have : r + r = (-s + r) - (-s - r) := by abel
        rw [this, e]; abel
      have h4 : (2 : F) • r = 0 := by rw [two_smul]; exact this
      exact (smul_eq_zero.mp h4).resolve_left h2
    rw [hdec, h3, add_zero]
    exact ⟨_, rfl⟩
  have hperp : ∀ x ∈ fr.perp, a x ∈ fr.perp := by
    intro x hx
    obtain ⟨hdec, hr⟩ := decomp_span_perp fr (a x)
    set s := fr.incl (fr.coords (a x)) with hs
    set r := a x - s with hr'
    have h1 : fr.La (-1) (a x) = a x := by
      rw [← hz, La_neg_one_of_mem_perp fr hx]
    have h2' : fr.La (-1) (a x) = -s + r := by
      conv_lhs => rw [hdec]
      rw [map_add, La_neg_one_of_mem_span fr ⟨_, rfl⟩, La_neg_one_of_mem_perp fr hr]
    have e2 : a x = s + r := by rw [hr']; abel
    have h3 : s = 0 := by
      have e : s + r = -s + r := by rw [← e2, ← h1, h2'] 
      have : s + s = 0 := by
        have : s + s = (s + r) - (-s + r) := by abel
        rw [this, e]; abel
      have h4 : (2 : F) • s = 0 := by rw [two_smul]; exact this
      exact (smul_eq_zero.mp h4).resolve_left h2
    have : r ∈ fr.perp := hr
    rw [e2, h3, zero_add]
    exact this
  refine ⟨?_, hperp⟩
  let T : Matrix (Fin 2) (Fin 2) F →ₗ[F] Matrix (Fin 2) (Fin 2) F :=
    fr.coords ∘ₗ (a : V →ₗ[F] V) ∘ₗ fr.incl
  have hT : ∀ X, a (fr.incl X) = fr.incl (T X) := by
    intro X
    exact (Frame.mem_span_iff fr).mp (hspan _ ⟨X, rfl⟩)
  have hinj : ∀ X Y, fr.incl X = fr.incl Y → X = Y := fun X Y h => by
    have := congrArg fr.coords h
    rwa [Frame.coords_incl, Frame.coords_incl] at this
  have hL : ∀ (A : SL(2, F)) X, T ((A : Matrix (Fin 2) (Fin 2) F) * X) =
      (A : Matrix (Fin 2) (Fin 2) F) * T X := by
    intro A X
    apply hinj
    have h := congrArg (fun g : V ≃ₗ[F] V => g (fr.incl X)) (hLa A)
    simp only [LinearEquiv.mul_apply] at h
    rw [Frame.La_apply_incl, hT, hT, Frame.La_apply_incl] at h
    exact h
  have hR : ∀ (B : SL(2, F)) X, T (X * sigmaLin (B : Matrix (Fin 2) (Fin 2) F)) =
      T X * sigmaLin (B : Matrix (Fin 2) (Fin 2) F) := by
    intro B X
    apply hinj
    have h := congrArg (fun g : V ≃ₗ[F] V => g (fr.incl X)) (hsw B)
    simp only [LinearEquiv.mul_apply] at h
    rw [swap_La_incl, hT, hT, swap_La_incl] at h
    exact h
  have e12 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) = 1 + !![0, 1; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have e21 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) = 1 + !![0, 0; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hL₁ : ∀ X, T (!![0, 1; 0, 0] * X) = !![0, 1; 0, 0] * T X := by
    intro X
    have h := hL (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1) X
    rw [Frame.coe_transvection_zero_one, e12, add_mul, add_mul, one_mul, one_mul, map_add] at h
    exact add_left_cancel h
  have hL₂ : ∀ X, T (!![0, 0; 1, 0] * X) = !![0, 0; 1, 0] * T X := by
    intro X
    have h := hL (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1) X
    rw [Frame.coe_transvection_one_zero, e21, add_mul, add_mul, one_mul, one_mul, map_add] at h
    exact add_left_cancel h
  have hR₂ : ∀ X, T (X * !![0, 0; 1, 0]) = T X * !![0, 0; 1, 0] := by
    intro X
    have h := hR (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1) X
    have hσ : sigmaLin (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) = 1 - !![0, 0; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply]
    rw [Frame.coe_transvection_zero_one, hσ, mul_sub, mul_sub, mul_one, mul_one, map_sub] at h
    exact sub_right_inj.mp h
  have hR₁ : ∀ X, T (X * !![0, 1; 0, 0]) = T X * !![0, 1; 0, 0] := by
    intro X
    have h := hR (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1) X
    have hσ : sigmaLin (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) = 1 - !![0, 1; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply]
    rw [Frame.coe_transvection_one_zero, hσ, mul_sub, mul_sub, mul_one, mul_one, map_sub] at h
    exact sub_right_inj.mp h
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_E T hL₁ hL₂ hR₁ hR₂
  refine ⟨c, fun x hx => ?_⟩
  obtain ⟨X, rfl⟩ := hx
  rw [hT, hc, map_smul]

end Centralizer

section GLLin

open CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBHigherLinearField Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

noncomputable def glLin : GL ι F →* ((ι → F) ≃ₗ[F] (ι → F)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F)).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

theorem glLin_apply (g : GL ι F) (v : ι → F) : glLin g v = (g : Matrix ι ι F) *ᵥ v := by
  simp [glLin]

theorem glLin_spinMatrix (Q : QuadraticForm F (ι → F)) (x : spinGroup Q) :
    glLin (spinMatrix Q x) = spinAction Q x := by
  refine LinearEquiv.ext fun v => ?_
  rw [glLin_apply, spinMatrix_mulVec]

theorem glFieldEquiv_refl (g : GL ι F) : glFieldEquiv ι (RingEquiv.refl F) g = g := by
  apply Units.ext
  ext i j
  exact glFieldEquiv_entry ι (RingEquiv.refl F) g i j

end GLLin

section Abstract

variable {G : Type*} [Group G]

theorem commutatorElement_mul_central_left {c : G} (hc : c ∈ Subgroup.center G) (g h : G) :
    ⁅g * c, h⁆ = ⁅g, h⁆ := by
  have e : c * h * c⁻¹ = h := by
    rw [← Subgroup.mem_center_iff.mp hc h, mul_inv_cancel_right]
  simp only [commutatorElement_def, mul_inv_rev]
  calc g * c * h * (c⁻¹ * g⁻¹) * h⁻¹ = g * (c * h * c⁻¹) * g⁻¹ * h⁻¹ := by group
    _ = g * h * g⁻¹ * h⁻¹ := by rw [e]

theorem commutatorElement_mul_central {c₁ c₂ : G} (h₁ : c₁ ∈ Subgroup.center G)
    (h₂ : c₂ ∈ Subgroup.center G) (g₁ g₂ : G) : ⁅g₁ * c₁, g₂ * c₂⁆ = ⁅g₁, g₂⁆ := by
  rw [commutatorElement_mul_central_left h₁, ← commutatorElement_inv,
    commutatorElement_mul_central_left h₂, commutatorElement_inv]

theorem alpha_fixes_commutators (α : G ≃* G) {S : Subgroup G}
    (h : ∀ s ∈ S, s⁻¹ * α s ∈ Subgroup.center G) : ∀ g ∈ ⁅S, S⁆, α g = g := by
  have hle : ⁅S, S⁆ ≤ MonoidHom.eqLocus (α : G →* G) (MonoidHom.id G) := by
    rw [Subgroup.commutator_le]
    intro s hs t ht
    show α ⁅s, t⁆ = ⁅s, t⁆
    rw [map_commutatorElement]
    obtain ⟨cs, hcs, hαs⟩ : ∃ cs ∈ Subgroup.center G, α s = s * cs := ⟨s⁻¹ * α s, h s hs, by group⟩
    obtain ⟨ct, hct, hαt⟩ : ∃ ct ∈ Subgroup.center G, α t = t * ct := ⟨t⁻¹ * α t, h t ht, by group⟩
    rw [hαs, hαt, commutatorElement_mul_central hcs hct]
  exact fun g hg => hle hg

theorem exists_lift_commutator {K : Type*} [Group K] (θ : K →* G) {P : Subgroup G}
    (hP : P ≤ θ.range) (hperf : ⁅P, P⁆ = P) :
    ∀ g ∈ P, ∃ s ∈ ⁅P.comap θ, P.comap θ⁆, θ s = g := by
  intro g hg
  have h1 : (P.comap θ).map θ = P := Subgroup.map_comap_eq_self hP
  have h2 : (⁅P.comap θ, P.comap θ⁆).map θ = P := by
    rw [Subgroup.map_commutator, h1, hperf]
  have : g ∈ (⁅P.comap θ, P.comap θ⁆).map θ := by
    rw [h2]
    exact hg
  obtain ⟨s, hs, rfl⟩ := this
  exact ⟨s, hs, rfl⟩

end Abstract

section FieldAut

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem ringEquiv_eq_refl_of_commute (N : Matrix ι ι F) (hN : N ≠ 0) (A : GL ι F) (φ : F ≃+* F)
    (h : ∀ c : F, (A : Matrix ι ι F) * ((1 + c • N).map φ) = (1 + c • N) * (A : Matrix ι ι F)) :
    φ = RingEquiv.refl F := by
  have hmap : ∀ c : F, ((1 : Matrix ι ι F) + c • N).map φ = 1 + φ c • N.map φ := by
    intro c
    rw [Matrix.map_add φ (fun a b => map_add φ a b), Matrix.map_one φ (map_zero φ) (map_one φ),
      Matrix.map_smul' φ c N (fun a b => map_mul φ a b)]
  have h2 : ∀ c : F, φ c • ((A : Matrix ι ι F) * N.map φ) = c • (N * (A : Matrix ι ι F)) := by
    intro c
    have := h c
    rw [hmap, mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc] at this
    exact add_left_cancel this
  have h1 : (A : Matrix ι ι F) * N.map φ = N * (A : Matrix ι ι F) := by
    have := h2 1
    rwa [map_one, one_smul, one_smul] at this
  have hNA : N * (A : Matrix ι ι F) ≠ 0 := by
    intro h0
    apply hN
    have : N * (A : Matrix ι ι F) * ((A⁻¹ : GL ι F) : Matrix ι ι F) = 0 := by rw [h0, zero_mul]
    rwa [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] at this
  ext c
  have := h2 c
  rw [h1] at this
  have h3 : (φ c - c) • (N * (A : Matrix ι ι F)) = 0 := by
    rw [sub_smul, this, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp h4
  · exact absurd h4 hNA

end FieldAut

section Nu

open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

noncomputable def nuLin (fr : Frame Q) : V →ₗ[F] V :=
  fr.incl ∘ₗ (LinearMap.mulLeft F (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F)) ∘ₗ fr.coords

theorem La_transvection_eq (fr : Frame Q) (c : F) :
    (fr.La (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c) :
      V →ₗ[F] V) = 1 + c • nuLin fr := by
  refine LinearMap.ext fun x => ?_
  have e : ∀ Y : Matrix (Fin 2) (Fin 2) F, (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) F) * Y - Y =
      c • ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) * Y) := by
    intro Y
    rw [Matrix.eta_fin_two Y]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  simp only [LinearEquiv.coe_coe, LinearMap.add_apply, Module.End.one_apply,
    LinearMap.smul_apply]
  rw [Frame.La_apply, Frame.coe_transvection_zero_one, e, map_smul]
  rfl

theorem nuLin_ne_zero (fr : Frame Q) : nuLin fr ≠ 0 := by
  intro h
  have h1 := LinearMap.congr_fun h (fr.incl !![0, 0; 1, 0])
  simp only [nuLin, LinearMap.comp_apply, Frame.coords_incl, LinearMap.mulLeft_apply,
    LinearMap.zero_apply] at h1
  have e : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 0; 1, 0] = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e] at h1
  have := congrArg fr.coords h1
  rw [Frame.coords_incl, map_zero] at this
  have h2 := congrFun (congrFun this 0) 0
  simp at h2

end Nu

section Core

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBHigherLinearField Matrix
open scoped MatrixGroups

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

@[expose] def LiftSim (Q : QuadraticForm F (ι → F)) {H : Type} [Group H]
    (ψ : spinGroup Q →* H) : Prop :=
  ∀ σ : ↥ψ.range ≃* ↥ψ.range, ∃ α : spinGroup Q ≃* spinGroup Q,
    (∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x)) ∧
      ∃ (A : GL ι F) (φ : F ≃+* F) (μ : Fˣ),
        (∀ v : ι → F, Q (A.val *ᵥ (fun i => φ (v i))) = μ * φ (Q v)) ∧
          ∀ x, spinMatrix Q (α x) = A * glFieldEquiv ι φ (spinMatrix Q x) * A⁻¹

theorem exists_aut_of_centralizing (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    [Group.IsPerfect (spinGroup Q)] (hrange : (spinAction Q).range = elementaryGroup Q)
    (fr : Frame Q) {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (hlift : LiftSim Q ψ) (σ : ↥ψ.range ≃* ↥ψ.range)
    (hσ : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, σ (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σ ℓ * (ψ.rangeRestrict s)⁻¹) :
    ∃ (α : spinGroup Q ≃* spinGroup Q) (a : (ι → F) ≃ₗ[F] (ι → F)) (c : F),
      (∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x)) ∧
      (∀ x, spinAction Q (α x) = a * spinAction Q x * a⁻¹) ∧
      (∀ x ∈ fr.span, a x = c • x) ∧ (∃ μ : Fˣ, (μ : F) = c ^ 2 ∧
        ∀ v, Q (a v) = μ * Q v) := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  set θ := spinAction Q with hθ
  obtain ⟨α, hαψ, A, φ, μ, hsim, hmat⟩ := hlift σ
  set P : Subgroup ((ι → F) ≃ₗ[F] (ι → F)) := fr.La.range ⊔ fr.swap.La.range with hP
  have hPE : P ≤ θ.range := by
    rw [hrange]
    exact sup_le (fun g ⟨A, hA⟩ => hA ▸ fr.La_mem_elementaryGroup A)
      (fun g ⟨A, hA⟩ => hA ▸ fr.swap.La_mem_elementaryGroup A)
  have hcentral : ∀ s ∈ P.comap θ, s⁻¹ * α s ∈ Subgroup.center (spinGroup Q) := by
    intro s hs
    have hℓ := hσ s (Subgroup.mem_comap.mp hs)
    set x := ψ.rangeRestrict s with hx
    have hζ : ∀ m : ↥ψ.range, (x⁻¹ * σ x) * m = m * (x⁻¹ * σ x) := by
      intro m
      obtain ⟨ℓ, rfl⟩ := σ.surjective m
      have h1 := hℓ ℓ
      rw [map_mul, map_mul, map_inv] at h1
      calc x⁻¹ * σ x * σ ℓ = x⁻¹ * (σ x * σ ℓ * (σ x)⁻¹) * σ x := by group
        _ = x⁻¹ * (x * σ ℓ * x⁻¹) * σ x := by rw [h1]
        _ = σ ℓ * (x⁻¹ * σ x) := by group
    refine mem_center_of_commutators_central fun t => hψ ?_
    rw [← MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, map_commutatorElement, map_mul,
      map_inv, hαψ s]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hζ _)
  have hfix := alpha_fixes_commutators α hcentral
  have hF4 : ∃ s : Finset F, s.card = 4 := by
    have := Fintype.ofFinite F
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨t, ht⟩
  have hSL : Group.IsPerfect SL(2, F) := CFSG.LinearGroups.special_linear_dimension_two_perfect hF4
  have hL₁ : ⁅fr.La.range, fr.La.range⁆ = fr.La.range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range fr.La)
  have hL₂ : ⁅fr.swap.La.range, fr.swap.La.range⁆ = fr.swap.La.range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range fr.swap.La)
  have hPperf : ⁅P, P⁆ = P := by
    refine le_antisymm (Subgroup.commutator_le.mpr fun x hx y hy => ?_) (sup_le ?_ ?_)
    · simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    · calc fr.La.range = ⁅fr.La.range, fr.La.range⁆ := hL₁.symm
        _ ≤ ⁅P, P⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc fr.swap.La.range = ⁅fr.swap.La.range, fr.swap.La.range⁆ := hL₂.symm
        _ ≤ ⁅P, P⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
  have hlift2 := exists_lift_commutator θ hPE hPperf
  have hN : (LinearMap.toMatrix' (nuLin fr)) ≠ 0 := by
    intro h0
    exact nuLin_ne_zero fr ((LinearMap.toMatrix').injective (by rw [h0, map_zero]))
  have hφ : φ = RingEquiv.refl F := by
    refine ringEquiv_eq_refl_of_commute (LinearMap.toMatrix' (nuLin fr)) hN A φ fun c => ?_
    set g := fr.La (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c)
      with hg
    have hgP : g ∈ P := Subgroup.mem_sup_left (⟨_, rfl⟩ : g ∈ fr.La.range)
    obtain ⟨s, hs, hsg⟩ := hlift2 g hgP
    have hαs : α s = s := hfix s hs
    have hm := hmat s
    rw [hαs] at hm
    have hM : ((spinMatrix Q s : GL ι F) : Matrix ι ι F) =
        1 + c • LinearMap.toMatrix' (nuLin fr) := by
      rw [coe_spinMatrix, hsg, hg]
      have := La_transvection_eq fr c
      rw [show ((g : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) →ₗ[F] (ι → F)) = 1 + c • nuLin fr from this,
        map_add, map_smul, LinearMap.toMatrix'_one]
    have hMA : ((spinMatrix Q s : GL ι F) : Matrix ι ι F) * (A : Matrix ι ι F) =
        (A : Matrix ι ι F) * (((spinMatrix Q s : GL ι F) : Matrix ι ι F).map φ) := by
      set G := glFieldEquiv ι φ (spinMatrix Q s) with hG
      have h1 : spinMatrix Q s * A = A * G := by
        calc spinMatrix Q s * A = (A * G * A⁻¹) * A := by rw [← hm]
          _ = A * G := by group
      have h2' := congrArg (fun g : GL ι F => (g : Matrix ι ι F)) h1
      simp only [Units.val_mul] at h2'
      have hGm : (G : Matrix ι ι F) = ((spinMatrix Q s : GL ι F) : Matrix ι ι F).map φ := by
        ext i j
        exact glFieldEquiv_entry ι φ _ i j
      rw [hGm] at h2'
      exact h2'
    rw [hM] at hMA
    exact hMA.symm
  subst hφ
  have hmat' : ∀ x, spinMatrix Q (α x) = A * spinMatrix Q x * A⁻¹ := by
    intro x
    rw [hmat x, glFieldEquiv_refl]
  set a : (ι → F) ≃ₗ[F] (ι → F) := glLin A with ha
  have hθα : ∀ x, θ (α x) = a * θ x * a⁻¹ := by
    intro x
    rw [← glLin_spinMatrix, hmat', map_mul, map_mul, map_inv, glLin_spinMatrix]
  have hcomm : ∀ g ∈ P, a * g = g * a := by
    intro g hg
    obtain ⟨s, hs, rfl⟩ := hlift2 g hg
    have h1 := hθα s
    rw [hfix s hs] at h1
    calc a * θ s = (a * θ s * a⁻¹) * a := by group
      _ = θ s * a := by rw [← h1]
  obtain ⟨⟨c, hc⟩, -⟩ := scalar_on_span_of_commute h2 fr
    (fun A₀ => hcomm _ (Subgroup.mem_sup_left (⟨A₀, rfl⟩ : fr.La A₀ ∈ fr.La.range)))
    (fun B₀ => hcomm _ (Subgroup.mem_sup_right (⟨B₀, rfl⟩ : fr.swap.La B₀ ∈ fr.swap.La.range)))
  have hsim' : ∀ v, Q (a v) = μ * Q v := by
    intro v
    have := hsim v
    simpa [ha, glLin_apply] using this
  refine ⟨α, a, c, hαψ, hθα, hc, μ, ?_, hsim'⟩
  have hv := hsim' (fr.incl 1)
  rw [hc _ ⟨1, rfl⟩, QuadraticMap.map_smul, Frame.Q_incl, Matrix.det_one] at hv
  rw [pow_two]
  simpa using hv.symm

end Core

section Final

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Asc77 Matrix
open scoped MatrixGroups

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

theorem hom_eq_of_central_diff {K : Type*} [Group K] [Group.IsPerfect K] (α β : K →* K)
    (h : ∀ x, (β x)⁻¹ * α x ∈ Subgroup.center K) : α = β := by
  have hle : ⁅(⊤ : Subgroup K), ⊤⁆ ≤ MonoidHom.eqLocus α β := by
    rw [Subgroup.commutator_le]
    intro s _ t _
    show α ⁅s, t⁆ = β ⁅s, t⁆
    rw [map_commutatorElement, map_commutatorElement]
    obtain ⟨cs, hcs, hαs⟩ : ∃ cs ∈ Subgroup.center K, α s = β s * cs :=
      ⟨(β s)⁻¹ * α s, h s, by group⟩
    obtain ⟨ct, hct, hαt⟩ : ∃ ct ∈ Subgroup.center K, α t = β t * ct :=
      ⟨(β t)⁻¹ * α t, h t, by group⟩
    rw [hαs, hαt, commutatorElement_mul_central hcs hct]
  have htop : ⁅(⊤ : Subgroup K), ⊤⁆ = ⊤ := Group.isPerfect_def.mp inferInstance
  ext x
  have hx : x ∈ ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ := by
    rw [htop]
    exact Subgroup.mem_top x
  exact hle hx

theorem toInducedAutOn_apply_coe {L : Subgroup H} (m : ↥(Subgroup.normalizer (L : Set H)))
    (ℓ : ↥L) : (((toInducedAutOn L m : ↥(inducedAutOn L)) : MulAut ↥L) ℓ : H) =
      (m : H) * (ℓ : H) * (m : H)⁻¹ := rfl

theorem exists_isometry_of_centralizing (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    [Group.IsPerfect (spinGroup Q)] (hrange : (spinAction Q).range = elementaryGroup Q)
    (fr : Frame Q) {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (hlift : LiftSim Q ψ) (σ : ↥ψ.range ≃* ↥ψ.range)
    (hσ : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, σ (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σ ℓ * (ψ.rangeRestrict s)⁻¹) :
    ∃ (α : spinGroup Q ≃* spinGroup Q) (w : (ι → F) ≃ₗ[F] (ι → F)),
      (∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x)) ∧
      w ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ (∀ x ∈ fr.span, w x = x) ∧
      ∀ x, spinAction Q (α x) = w * spinAction Q x * w⁻¹ := by
  classical
  set θ := spinAction Q with hθ
  obtain ⟨α, a, c, hαψ, hθα, hc, μ, hμc, hsim⟩ :=
    exists_aut_of_centralizing hodd h5 hrange fr hψ hlift σ hσ
  have hc0 : c ≠ 0 := by
    intro h0
    apply μ.ne_zero
    rw [hμc, h0]
    ring
  set sm : (ι → F) ≃ₗ[F] (ι → F) := LinearEquiv.smulOfNeZero F (ι → F) c hc0 with hsm_def
  set sm' : (ι → F) ≃ₗ[F] (ι → F) :=
    LinearEquiv.smulOfNeZero F (ι → F) c⁻¹ (inv_ne_zero hc0) with hsm'_def
  have hsm_comm : ∀ g : (ι → F) ≃ₗ[F] (ι → F), sm * g = g * sm := fun g => by
    ext x
    simp [sm]
  have hsm_inv : sm * sm' = 1 := by
    ext x
    simp [sm, sm', hc0]
  set w : (ι → F) ≃ₗ[F] (ι → F) := sm' * a with hw
  have ha : a = sm * w := by rw [hw, ← mul_assoc, hsm_inv, one_mul]
  have hwspan : ∀ x ∈ fr.span, w x = x := by
    intro x hx
    rw [hw, LinearEquiv.mul_apply, hc x hx]
    simp [sm', hc0]
  have hwiso : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    have h1 : w x = c⁻¹ • a x := by
      rw [hw, LinearEquiv.mul_apply]
      simp [sm']
    rw [h1, QuadraticMap.map_smul, hsim, hμc]
    simp only [smul_eq_mul]
    field_simp
  have hθw : ∀ x, θ (α x) = w * θ x * w⁻¹ := by
    intro x
    rw [hθα, ha, _root_.mul_inv_rev]
    calc sm * w * θ x * (w⁻¹ * sm⁻¹) = sm * (w * θ x * w⁻¹) * sm⁻¹ := by group
      _ = (w * θ x * w⁻¹) * sm * sm⁻¹ := by rw [hsm_comm]
      _ = w * θ x * w⁻¹ := by group
  exact ⟨α, w, hαψ, hwiso, hwspan, hθw⟩

omit [DecidableEq ι] in
theorem sq_mem_of_frame (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (fr : Frame Q) (hV : 7 ≤ Module.finrank F (ι → F)) {w : (ι → F) ≃ₗ[F] (ι → F)}
    (hwiso : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : w * w ∈ elementaryGroup Q := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hperp3 : 3 ≤ Module.finrank F fr.perp := by
    have := finrank_perp_add_four fr
    omega
  obtain ⟨P₃, he₃, hf₃⟩ := exists_hypPair_le hodd (polarNondegOn_perp hQ fr) hperp3
  have h₁₃ : fr.P.Orth P₃ :=
    ⟨polar_perp_of_mem_span fr fr.e₁_mem_span he₃, polar_perp_of_mem_span fr fr.e₁_mem_span hf₃,
      polar_perp_of_mem_span fr fr.f₁_mem_span he₃, polar_perp_of_mem_span fr fr.f₁_mem_span hf₃⟩
  have h₂₃ : fr.P'.Orth P₃ :=
    ⟨polar_perp_of_mem_span fr fr.e₂_mem_span he₃, polar_perp_of_mem_span fr fr.e₂_mem_span hf₃,
      polar_perp_of_mem_span fr fr.f₂_mem_span he₃, polar_perp_of_mem_span fr fr.f₂_mem_span hf₃⟩
  exact sq_mem_elementaryGroup h2 hQ fr.orth h₁₃ h₂₃ hwiso

omit [Fintype ι] [DecidableEq ι] [Finite F] in
theorem exists_sq_lift [Group.IsPerfect (spinGroup Q)]
    (hrange : (spinAction Q).range = elementaryGroup Q) (α : spinGroup Q ≃* spinGroup Q)
    {w : (ι → F) ≃ₗ[F] (ι → F)} (hy_mem : w * w ∈ elementaryGroup Q)
    (hθw : ∀ x, spinAction Q (α x) = w * spinAction Q x * w⁻¹) :
    ∃ ŷ : spinGroup Q, spinAction Q ŷ = w * w ∧ ∀ x, α (α x) = ŷ * x * ŷ⁻¹ := by
  obtain ⟨ŷ, hŷ⟩ : ∃ ŷ : spinGroup Q, spinAction Q ŷ = w * w := by
    have h := hy_mem
    rw [← hrange] at h
    exact h
  refine ⟨ŷ, hŷ, ?_⟩
  have hh : ((α : spinGroup Q →* spinGroup Q).comp (α : spinGroup Q →* spinGroup Q)) =
      (MulAut.conj ŷ).toMonoidHom := by
    refine hom_eq_of_central_diff _ _ fun x => ?_
    apply ker_spinAction_le_center Q
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    show (spinAction Q (ŷ * x * ŷ⁻¹))⁻¹ * spinAction Q (α (α x)) = 1
    rw [hθw, hθw, map_mul, map_mul, map_inv, hŷ]
    group
  intro x
  exact DFunLike.congr_fun hh x

omit [Fintype ι] [DecidableEq ι] [Finite F] in
theorem e_sq_eq {ψ : spinGroup Q →* H}
    (e : ↥(elementaryGroup Q) →* ↥(inducedAutOn ψ.range))
    (he : ∀ (s : spinGroup Q) (hs : spinAction Q s ∈ elementaryGroup Q),
      e ⟨spinAction Q s, hs⟩ = toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩)
    (v : ↥(inducedAutOn ψ.range)) (α : spinGroup Q ≃* spinGroup Q)
    (hαψ : ∀ x, ψ.rangeRestrict (α x) = (v : MulAut ↥ψ.range) (ψ.rangeRestrict x))
    {y : (ι → F) ≃ₗ[F] (ι → F)} (hy_mem : y ∈ elementaryGroup Q) {ŷ : spinGroup Q}
    (hŷ : spinAction Q ŷ = y) (hαα : ∀ x, α (α x) = ŷ * x * ŷ⁻¹) :
    e ⟨y, hy_mem⟩ = v * v := by
  have h1 : e ⟨y, hy_mem⟩ = toInducedAutOn ψ.range ⟨ψ ŷ, mem_normalizer_range ψ ŷ⟩ := by
    have := he ŷ (by rw [hŷ]; exact hy_mem)
    rw [← this]
    congr 1
    exact Subtype.ext hŷ.symm
  rw [h1]
  apply Subtype.ext
  apply MulEquiv.ext
  intro ℓ
  obtain ⟨x, rfl⟩ := ψ.rangeRestrict_surjective ℓ
  have h2' : (((v * v : ↥(inducedAutOn ψ.range)) : MulAut ↥ψ.range) (ψ.rangeRestrict x)) =
      ψ.rangeRestrict (α (α x)) := by
    show (v : MulAut ↥ψ.range) ((v : MulAut ↥ψ.range) (ψ.rangeRestrict x)) = _
    rw [← hαψ, ← hαψ]
  rw [h2', hαα]
  apply Subtype.ext
  show (ψ ŷ * ψ x * (ψ ŷ)⁻¹ : H) = _
  simp

omit [Fintype ι] [DecidableEq ι] [Finite F] in
theorem sq_eq_one_of_e {X : Type} [Group X] (e : ↥(elementaryGroup Q) →* X) (hker : KerScalar Q e)
    (fr : Frame Q) {y : (ι → F) ≃ₗ[F] (ι → F)} (hy : y ∈ elementaryGroup Q)
    (hspan : ∀ x ∈ fr.span, y x = x) (hyy : e ⟨y, hy⟩ * e ⟨y, hy⟩ = 1) : y * y = 1 := by
  have h1 : e (⟨y, hy⟩ * ⟨y, hy⟩) = 1 := by rw [map_mul]; exact hyy
  obtain ⟨c', hc'⟩ := mem_scalars.mp (hker _ h1)
  have hne : fr.incl 1 ≠ 0 := by
    intro h0
    have := congrArg fr.coords h0
    rw [Frame.coords_incl, map_zero] at this
    exact one_ne_zero (congrFun (congrFun this 0) 0)
  have hspan1 : fr.incl 1 ∈ fr.span := ⟨1, rfl⟩
  have h4 : (y * y) (fr.incl 1) = fr.incl 1 := by
    rw [LinearEquiv.mul_apply, hspan _ hspan1, hspan _ hspan1]
  have h5' : (y * y) (fr.incl 1) = c' • fr.incl 1 := hc' (fr.incl 1)
  have hc1 : c' = 1 := by
    rw [h4] at h5'
    have : (c' - 1) • fr.incl 1 = 0 := by rw [sub_smul, ← h5', one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hne)
  ext x
  rw [show (y * y : (ι → F) ≃ₗ[F] (ι → F)) x = c' • x from hc' x, hc1, one_smul]
  rfl

omit [Fintype ι] [DecidableEq ι] [Finite F] in
theorem eq_one_of_minusSp_eq_bot (h2 : (2 : F) ≠ 0) {y : (ι → F) ≃ₗ[F] (ι → F)}
    (hyy : y * y = 1) (hbot : minusSp y = ⊥) : y = 1 := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_eq h2 hyy x
  have hr0 : r = 0 := by
    have : r ∈ (⊥ : Submodule F (ι → F)) := hbot ▸ hr
    exact (Submodule.mem_bot _).mp this
  rw [hr0, add_zero]
  exact mem_plusSp.mp hu

omit [Fintype ι] [DecidableEq ι] [Finite F] in
theorem mul_La_neg_one_eq_neg (h2 : (2 : F) ≠ 0) (fr : Frame Q) {y : (ι → F) ≃ₗ[F] (ι → F)}
    (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hyy : y * y = 1)
    (hspan : ∀ x ∈ fr.span, y x = x) (hbot : plusSp y ⊓ fr.perp = ⊥) :
    y * fr.La (-1) = LinearEquiv.neg F := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨hdec, hr⟩ := decomp_span_perp fr x
  obtain ⟨u, hu, r, hr', hpur⟩ := exists_add_eq_perp fr h2 hyy hyO hspan hr
  have hu0 : u = 0 := by
    have : u ∈ (⊥ : Submodule F (ι → F)) := hbot ▸ hu
    exact (Submodule.mem_bot _).mp this
  have hpr : x - fr.incl (fr.coords x) = r := by rw [hpur, hu0, zero_add]
  have hyr : y r = -r := mem_minusSp.mp hr'
  have hs_span : fr.incl (fr.coords x) ∈ fr.span := ⟨_, rfl⟩
  show y (fr.La (-1) x) = -x
  conv_lhs => rw [hdec]
  rw [map_add, La_neg_one_of_mem_span fr hs_span, La_neg_one_of_mem_perp fr hr, map_add,
    map_neg, hspan _ hs_span, hpr, hyr]
  conv_rhs => rw [hdec, hpr]
  abel

theorem alphaOf_spin_frame_centralizer_eq_bot (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (fr : Frame Q) (hV : 7 ≤ Module.finrank F (ι → F))
    {ψ : spinGroup Q →* H} [Finite H] (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (hlift : LiftSim Q ψ) {s₂ : spinGroup Q} (hs₂ : spinAction Q s₂ = fr.La (-1))
    (v : ↥(inducedAutOn ψ.range))
    (hv : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      v * toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩ =
        toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩ * v)
    (hy2 : v * v * (v * v) = 1) (hy1 : v * v ≠ 1)
    (hyz : v * v ≠ toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩, v * v} :
      Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h3 : 3 ≤ Module.finrank F (ι → F) := by omega
  obtain ⟨e, he, hker, hnorm, hcent⟩ := exists_hom_spin hodd hQ h3 hrange ψ hψ
  have : Finite ↥(inducedAutOn ψ.range) := inferInstance
  have := hnorm
  have hσ : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, (v : MulAut ↥ψ.range) (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * (v : MulAut ↥ψ.range) ℓ * (ψ.rangeRestrict s)⁻¹ := by
    intro s hs ℓ
    have h := congrArg (fun g : ↥(inducedAutOn ψ.range) => ((g : MulAut ↥ψ.range) ℓ : ↥ψ.range))
      (hv s hs)
    exact Subtype.ext (congrArg Subtype.val h)
  obtain ⟨α, w, hαψ, hwiso, hwspan, hθw⟩ :=
    exists_isometry_of_centralizing hodd h5 hrange fr hψ hlift (v : MulAut ↥ψ.range) hσ
  have hy_mem : w * w ∈ elementaryGroup Q := sq_mem_of_frame hodd hQ fr hV hwiso
  have hspan_y : ∀ x ∈ fr.span, (w * w) x = x := fun x hx => by
    rw [LinearEquiv.mul_apply, hwspan x hx, hwspan x hx]
  obtain ⟨ŷ, hŷ, hαα⟩ := exists_sq_lift hrange α hy_mem hθw
  have hey : e ⟨w * w, hy_mem⟩ = v * v := e_sq_eq e he v α hαψ hy_mem hŷ hαα
  have hyy : w * w * (w * w) = 1 :=
    sq_eq_one_of_e e hker fr hy_mem hspan_y (by rw [hey]; exact hy2)
  have hyO : w * w ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q hy_mem
  have hzmem : fr.La (-1) ∈ elementaryGroup Q := fr.La_mem_elementaryGroup (-1)
  have hez : e ⟨fr.La (-1), hzmem⟩ =
      toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩ := by
    have := he s₂ (by rw [hs₂]; exact hzmem)
    rw [← this]
    congr 1
    exact Subtype.ext hs₂.symm
  have hR : minusSp (w * w) ≠ ⊥ := by
    intro hbot
    apply hy1
    have h1 : w * w = 1 := eq_one_of_minusSp_eq_bot h2 hyy hbot
    have : (⟨w * w, hy_mem⟩ : ↥(elementaryGroup Q)) = 1 := Subtype.ext h1
    rw [this, map_one] at hey
    exact hey.symm
  have hW : plusSp (w * w) ⊓ fr.perp ≠ ⊥ := by
    intro hbot
    have hneg := mul_La_neg_one_eq_neg h2 fr hyO hyy hspan_y hbot
    have hnegmem : (LinearEquiv.neg F : (ι → F) ≃ₗ[F] (ι → F)) ∈ elementaryGroup Q := by
      rw [← hneg]
      exact mul_mem hy_mem hzmem
    have hecent : e ⟨LinearEquiv.neg F, hnegmem⟩ = 1 := by
      apply hcent
      rintro _ ⟨g, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext (LinearEquiv.ext fun x => ?_)
      simp
    have h1 : e ⟨(w * w) * fr.La (-1), mul_mem hy_mem hzmem⟩ =
        e ⟨w * w, hy_mem⟩ * e ⟨fr.La (-1), hzmem⟩ := by
      rw [← map_mul]
      rfl
    have h2' : e ⟨(w * w) * fr.La (-1), mul_mem hy_mem hzmem⟩ = 1 := by
      have : (⟨(w * w) * fr.La (-1), mul_mem hy_mem hzmem⟩ : ↥(elementaryGroup Q)) =
          ⟨LinearEquiv.neg F, hnegmem⟩ := Subtype.ext hneg
      rw [this, hecent]
    rw [h1, hey, hez] at h2'
    have hz2 : toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩ *
        toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩ = 1 := by
      rw [← hez, ← map_mul]
      have : (⟨fr.La (-1), hzmem⟩ * ⟨fr.La (-1), hzmem⟩ : ↥(elementaryGroup Q)) = 1 :=
        Subtype.ext fr.La_neg_one_mul_self
      rw [this, map_one]
    apply hyz
    exact (mul_eq_one_iff_eq_inv.mp h2').trans (inv_eq_of_mul_eq_one_left hz2)
  have key := alphaOf_frame_klein_eq_bot hodd h5 hQ fr hy_mem hyy hspan_y hV hR hW e hker hcent
  rw [hez, hey] at key
  exact key

end Final

end CFSG.ClassicalInvolution.ModelFacts.Orth15
