module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Twin

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalGroups.Orthogonal.Small CFSG.ClassicalInvolution.Asc77 QuadraticMap Matrix
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

@[expose] def eigIn (u : V ≃ₗ[F] V) (c : F) (S : Submodule F V) : Submodule F V where
  carrier := {x | x ∈ S ∧ u x = c • x}
  add_mem' := fun ⟨hxS, hx⟩ ⟨hyS, hy⟩ =>
    ⟨S.add_mem hxS hyS, by rw [map_add, hx, hy, smul_add]⟩
  zero_mem' := ⟨S.zero_mem, by simp⟩
  smul_mem' := fun r x ⟨hxS, hx⟩ => ⟨S.smul_mem r hxS, by rw [map_smul, hx, smul_comm]⟩

theorem mem_eigIn_iff {u : V ≃ₗ[F] V} {c : F} {S : Submodule F V} {x : V} :
    x ∈ eigIn u c S ↔ x ∈ S ∧ u x = c • x := Iff.rfl

section Action

variable (fr : Frame Q) (A A' : SL(2, F))

@[expose] noncomputable def twinInv : V ≃ₗ[F] V := fr.La A * fr.swap.La A'

theorem twinInv_incl (X : Matrix (Fin 2) (Fin 2) F) :
    twinInv fr A A' (fr.incl X) =
      fr.incl ((A : Matrix (Fin 2) (Fin 2) F) * X * sigmaLin (A' : Matrix (Fin 2) (Fin 2) F)) := by
  unfold twinInv
  rw [LinearEquiv.mul_apply, Frame.La_swap_apply, Frame.embLin_apply, Frame.coords_incl,
    ← map_add, Frame.La_apply_incl]
  congr 1
  simp only [LinearMap.mulRight_apply]
  rw [add_sub_cancel]
  exact (Matrix.mul_assoc _ _ _).symm

theorem twinInv_perp {x : V} (hx : x ∈ fr.perp) : twinInv fr A A' x = x := by
  unfold twinInv
  rw [LinearEquiv.mul_apply, Frame.La_swap_apply, Frame.embLin_apply, (Frame.mem_perp_iff fr).mp hx]
  simp only [map_zero, sub_self, add_zero]
  exact Frame.La_apply_of_coords_eq_zero fr A ((Frame.mem_perp_iff fr).mp hx)

theorem twinInv_mem_orthogonalGroup :
    twinInv fr A A' ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  mul_mem (fr.La_mem_orthogonalGroup A) (fr.swap.La_mem_orthogonalGroup A')

theorem twinInv_mem_elementaryGroup : twinInv fr A A' ∈ elementaryGroup Q :=
  mul_mem (fr.La_mem_elementaryGroup A) (fr.swap.La_mem_elementaryGroup A')

end Action

section Eigen

theorem not_forall_mul_mul_eq_neg (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 2) (Fin 2) F}
    (hd : A.det = 1) : ¬ ∀ X : Matrix (Fin 2) (Fin 2) F, A * X * A = -X := by
  intro h
  have hA' := Matrix.eta_fin_two A
  set a := A 0 0
  set b := A 0 1
  set c := A 1 0
  set d := A 1 1
  have h00 := h !![1, 0; 0, 0]
  have h01 := h !![0, 1; 0, 0]
  rw [hA'] at h00 h01
  simp only [Matrix.mul_fin_two] at h00 h01
  have e1 := congrFun (congrFun h00 0) 0
  have e2 := congrFun (congrFun h00 0) 1
  have e3 := congrFun (congrFun h00 1) 0
  have e4 := congrFun (congrFun h01 0) 0
  have e5 := congrFun (congrFun h01 0) 1
  simp at e1 e2 e3 e4 e5
  rw [Matrix.det_fin_two] at hd
  have hd' : a * d - b * c = 1 := hd
  have ha : a ≠ 0 := by
    intro h0
    rw [h0] at e1
    simp at e1
  have hb : b = 0 := e2.resolve_left ha
  have hc : c = 0 := e3.resolve_right ha
  rw [hb, hc] at hd'
  have h3 : a * d = 1 := by simpa using hd'
  exact h2 (by linear_combination e5 - h3)

variable (fr : Frame Q) {A A' : SL(2, F)}

theorem sigmaLin_neg_one : sigmaLin (-1 : Matrix (Fin 2) (Fin 2) F) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply]

theorem sigmaLin_sq (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1) :
    sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) * sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) = -1 := by
  rw [← sigmaLin_mul, hA', sigmaLin_neg_one]

theorem decomp_span_perp (x : V) :
    x = fr.incl (fr.coords x) + (x - fr.incl (fr.coords x)) ∧
      (x - fr.incl (fr.coords x)) ∈ fr.perp := by
  refine ⟨by abel, ?_⟩
  rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]

theorem twinInv_twinInv (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1) (x : V) :
    twinInv fr A A' (twinInv fr A A' x) = x := by
  obtain ⟨hx, hr⟩ := decomp_span_perp fr x
  set X := fr.coords x
  set r := x - fr.incl X
  have h1 : twinInv fr A A' x = fr.incl ((A : Matrix (Fin 2) (Fin 2) F) * X *
      sigmaLin (A' : Matrix (Fin 2) (Fin 2) F)) + r := by
    conv_lhs => rw [hx]
    rw [map_add, twinInv_incl, twinInv_perp fr A A' hr]
  rw [h1, map_add, twinInv_incl, twinInv_perp fr A A' hr]
  have h2 : (A : Matrix (Fin 2) (Fin 2) F) * ((A : Matrix (Fin 2) (Fin 2) F) * X *
      sigmaLin (A' : Matrix (Fin 2) (Fin 2) F)) * sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) = X := by
    calc _ = ((A : Matrix (Fin 2) (Fin 2) F) * A) * X *
          (sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) *
            sigmaLin (A' : Matrix (Fin 2) (Fin 2) F)) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [hA, sigmaLin_sq hA']; simp
  rw [h2]
  exact hx.symm

theorem twinInv_mem_span {x : V} (hx : x ∈ fr.span) : twinInv fr A A' x ∈ fr.span := by
  obtain ⟨X, rfl⟩ := hx
  rw [twinInv_incl]
  exact ⟨_, rfl⟩

section TwinFrame

theorem eig_decomp (h2 : (2 : F) ≠ 0) (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1) {x : V} (hx : x ∈ fr.span) :
    ∃ x₁ ∈ eigIn (twinInv fr A A') (-1) fr.span, ∃ x₂ ∈ eigIn (twinInv fr A A') 1 fr.span,
      x = x₁ + x₂ := by
  set u := twinInv fr A A' with hu
  refine ⟨(2⁻¹ : F) • (x - u x), ⟨?_, ?_⟩, (2⁻¹ : F) • (x + u x), ⟨?_, ?_⟩, ?_⟩
  · exact fr.span.smul_mem _ (fr.span.sub_mem hx (twinInv_mem_span fr hx))
  · rw [map_smul, map_sub, hu, twinInv_twinInv fr hA hA' x, neg_one_smul, ← smul_neg, neg_sub]
  · exact fr.span.smul_mem _ (fr.span.add_mem hx (twinInv_mem_span fr hx))
  · rw [map_smul, map_add, hu, twinInv_twinInv fr hA hA' x, one_smul, add_comm]
  · rw [← smul_add, show x - u x + (x + u x) = (2 : F) • x by module, smul_smul,
      inv_mul_cancel₀ h2, one_smul]

theorem polar_eig (h2 : (2 : F) ≠ 0) {x y : V} (hx : x ∈ eigIn (twinInv fr A A') (-1) fr.span)
    (hy : y ∈ eigIn (twinInv fr A A') 1 fr.span) : polar Q x y = 0 := by
  have hO := twinInv_mem_orthogonalGroup fr A A'
  have h1 := polar_map_of_mem hO x y
  rw [(mem_eigIn_iff.mp hx).2, (mem_eigIn_iff.mp hy).2, neg_one_smul, one_smul,
    polar_neg_left] at h1
  have h3 : (2 : F) * polar Q x y = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp h3).resolve_left h2

theorem eig_ne_bot_neg (h2 : (2 : F) ≠ 0) (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1) :
    eigIn (twinInv fr A A') (-1) fr.span ≠ ⊥ := by
  intro hbot
  set S : Matrix (Fin 2) (Fin 2) F := sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) with hS
  have hfix : ∀ X : Matrix (Fin 2) (Fin 2) F, (A : Matrix (Fin 2) (Fin 2) F) * X * S = X := by
    intro X
    obtain ⟨x₁, hx₁, x₂, hx₂, hsum⟩ := eig_decomp fr h2 hA hA' (x := fr.incl X) ⟨X, rfl⟩
    rw [hbot, Submodule.mem_bot] at hx₁
    rw [hx₁, zero_add] at hsum
    have h1 := (mem_eigIn_iff.mp hx₂).2
    rw [← hsum, one_smul, twinInv_incl] at h1
    have := congrArg fr.coords h1
    rw [Frame.coords_incl, Frame.coords_incl] at this
    exact this
  have hSA : S = -(A : Matrix (Fin 2) (Fin 2) F) := by
    have h1 := hfix 1
    rw [Matrix.mul_one] at h1
    calc S = (-(A : Matrix (Fin 2) (Fin 2) F)) * ((A : Matrix (Fin 2) (Fin 2) F) * S) := by
          rw [← Matrix.mul_assoc, Matrix.neg_mul, hA]; simp
      _ = -(A : Matrix (Fin 2) (Fin 2) F) := by rw [h1]; simp
  refine not_forall_mul_mul_eq_neg h2 (A := (A : Matrix (Fin 2) (Fin 2) F)) A.det_coe fun X => ?_
  have h1 := hfix X
  rw [hSA, Matrix.mul_neg] at h1
  exact neg_eq_iff_eq_neg.mp h1

theorem eig_ne_bot_pos (h2 : (2 : F) ≠ 0) (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1) :
    eigIn (twinInv fr A A') 1 fr.span ≠ ⊥ := by
  intro hbot
  set S : Matrix (Fin 2) (Fin 2) F := sigmaLin (A' : Matrix (Fin 2) (Fin 2) F) with hS
  have hfix : ∀ X : Matrix (Fin 2) (Fin 2) F, (A : Matrix (Fin 2) (Fin 2) F) * X * S = -X := by
    intro X
    obtain ⟨x₁, hx₁, x₂, hx₂, hsum⟩ := eig_decomp fr h2 hA hA' (x := fr.incl X) ⟨X, rfl⟩
    rw [hbot, Submodule.mem_bot] at hx₂
    rw [hx₂, add_zero] at hsum
    have h1 := (mem_eigIn_iff.mp hx₁).2
    rw [← hsum, neg_one_smul, twinInv_incl, ← map_neg] at h1
    have := congrArg fr.coords h1
    rw [Frame.coords_incl, Frame.coords_incl] at this
    exact this
  have hSA : S = (A : Matrix (Fin 2) (Fin 2) F) := by
    have h1 := hfix 1
    rw [Matrix.mul_one] at h1
    calc S = (-(A : Matrix (Fin 2) (Fin 2) F)) * ((A : Matrix (Fin 2) (Fin 2) F) * S) := by
          rw [← Matrix.mul_assoc, Matrix.neg_mul, hA]; simp
      _ = (A : Matrix (Fin 2) (Fin 2) F) := by rw [h1]; simp
  refine not_forall_mul_mul_eq_neg h2 (A := (A : Matrix (Fin 2) (Fin 2) F)) A.det_coe fun X => ?_
  have h1 := hfix X
  rw [hSA] at h1
  exact h1

theorem eig_sup_eq_span (h2 : (2 : F) ≠ 0) (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1) :
    eigIn (twinInv fr A A') (-1) fr.span ⊔ eigIn (twinInv fr A A') 1 fr.span = fr.span := by
  refine le_antisymm (sup_le (fun x hx => (mem_eigIn_iff.mp hx).1)
    (fun x hx => (mem_eigIn_iff.mp hx).1)) fun x hx => ?_
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := eig_decomp fr h2 hA hA' hx
  exact Submodule.add_mem_sup hx₁ hx₂

theorem polar_perp_of_mem_span {x y : V} (hx : x ∈ fr.span) (hy : y ∈ fr.perp) :
    polar Q x y = 0 := by
  rw [polar_comm]
  have h := (Frame.mem_perp_iff_forall_incl fr).mp hy
  have : x = fr.incl (fr.coords x) := (Frame.mem_span_iff fr).mp hx
  rw [this]
  exact h _

theorem finrank_span_eq_four : Module.finrank F fr.span = 4 := by
  have hinj : Function.Injective fr.incl := fun X Y h => by
    have := congrArg fr.coords h
    rwa [Frame.coords_incl, Frame.coords_incl] at this
  have h := LinearMap.finrank_range_of_inj hinj
  show Module.finrank F (LinearMap.range fr.incl) = 4
  rw [h]
  simp [Module.finrank_matrix]

theorem La_neg_one_of_mem_span {x : V} (hx : x ∈ fr.span) : fr.La (-1) x = -x := by
  rw [Frame.La_neg_one_apply, ← (Frame.mem_span_iff fr).mp hx, two_smul]
  abel

theorem La_neg_one_of_mem_perp {x : V} (hx : x ∈ fr.perp) : fr.La (-1) x = x :=
  Frame.La_apply_of_coords_eq_zero fr (-1) ((Frame.mem_perp_iff fr).mp hx)

theorem twinDatum_of_frame [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1) (hV : 7 ≤ Module.finrank F V) :
    TwinDatum Q (eigIn (twinInv fr A A') (-1) fr.span) (eigIn (twinInv fr A A') 1 fr.span)
      fr.perp (twinInv fr A A') (twinInv fr A A' * fr.La (-1)) where
  nd₁ := polarNondegOn_of_orth (F := fr) (eig_sup_eq_span fr h2 hA hA').symm
    (fun x hx y hy => polar_eig fr h2 hx hy)
  nd₂ := polarNondegOn_of_orth (F := fr)
    (by rw [sup_comm]; exact (eig_sup_eq_span fr h2 hA hA').symm)
    (fun x hx y hy => by rw [polar_comm]; exact polar_eig fr h2 hy hx)
  ndW := CFSG.ClassicalInvolution.ModelFacts.polarNondegOn_perp hQ fr
  o₁₂ := fun x hx y hy => polar_eig fr h2 hx hy
  o₁W := fun x hx y hy => polar_perp_of_mem_span fr (mem_eigIn_iff.mp hx).1 hy
  o₂W := fun x hx y hy => polar_perp_of_mem_span fr (mem_eigIn_iff.mp hx).1 hy
  top := by
    rw [eig_sup_eq_span fr h2 hA hA']
    exact (Frame.isCompl_span_perp fr).sup_eq_top
  ne₁ := eig_ne_bot_neg fr h2 hA hA'
  ne₂ := eig_ne_bot_pos fr h2 hA hA'
  d₁₂ := by
    rw [eig_sup_eq_span fr h2 hA hA', finrank_span_eq_four]
    omega
  dW := by
    have h := Submodule.finrank_add_eq_of_isCompl (Frame.isCompl_span_perp fr)
    rw [finrank_span_eq_four] at h
    omega
  neg₁ := fun x hx => by rw [(mem_eigIn_iff.mp hx).2, neg_one_smul]
  fix₁ := fun x hx => by
    obtain ⟨y₂, hy₂, y₃, hy₃, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, (mem_eigIn_iff.mp hy₂).2, one_smul, twinInv_perp fr A A' hy₃]
  neg₂ := fun x hx => by
    rw [LinearEquiv.mul_apply, La_neg_one_of_mem_span fr (mem_eigIn_iff.mp hx).1, map_neg,
      (mem_eigIn_iff.mp hx).2, one_smul]
  fix₂ := fun x hx => by
    obtain ⟨y₁, hy₁, y₃, hy₃, rfl⟩ := Submodule.mem_sup.mp hx
    rw [LinearEquiv.mul_apply, map_add, map_add, La_neg_one_of_mem_span fr (mem_eigIn_iff.mp hy₁).1,
      La_neg_one_of_mem_perp fr hy₃, map_neg, (mem_eigIn_iff.mp hy₁).2, twinInv_perp fr A A' hy₃,
      neg_one_smul, neg_neg]
  mem₁ := twinInv_mem_elementaryGroup fr A A'
  mem₂ := mul_mem (twinInv_mem_elementaryGroup fr A A') (fr.La_mem_elementaryGroup (-1))

theorem alphaOf_frame_twin_eq_bot [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hQ : (polarBilin Q).Nondegenerate)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1) (hV : 7 ≤ Module.finrank F V)
    {X : Type} [Group X] [Finite X] (e : ↥(elementaryGroup Q) →* X) (hker : KerScalar Q e)
    [e.range.Normal] (hcent : ∀ x : X, (∀ y ∈ e.range, x * y = y * x) → x = 1) :
    alphaOf (Subgroup.closure ({e ⟨twinInv fr A A', twinInv_mem_elementaryGroup fr A A'⟩,
      e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩} : Set X)) = ⊥ := by
  have h2 := two_ne_zero_of_odd_card hodd
  have T := twinDatum_of_frame fr h2 hQ hA hA' hV
  have key := alphaOf_twin_eq_bot hodd h5 hQ T e hker hcent
  set a₁ : ↥(elementaryGroup Q) := ⟨twinInv fr A A', twinInv_mem_elementaryGroup fr A A'⟩
  set z : ↥(elementaryGroup Q) := ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩
  have h12 : (⟨twinInv fr A A' * fr.La (-1), T.mem₂⟩ : ↥(elementaryGroup Q)) = a₁ * z := rfl
  have hmul : e (a₁ * z) = e a₁ * e z := map_mul e a₁ z
  have hcl : Subgroup.closure ({e a₁, e ⟨twinInv fr A A' * fr.La (-1), T.mem₂⟩} : Set X) =
      Subgroup.closure ({e a₁, e z} : Set X) := by
    rw [h12, hmul]
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
    · rintro _ (rfl | rfl)
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    · rintro _ (rfl | rfl)
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · have h1 : e z = (e a₁)⁻¹ * (e a₁ * e z) := by group
        have h3 : (e a₁)⁻¹ * (e a₁ * e z) ∈ Subgroup.closure ({e a₁, e a₁ * e z} : Set X) :=
          mul_mem (inv_mem (Subgroup.subset_closure (Set.mem_insert _ _)))
            (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
        rwa [← h1] at h3
  rw [hcl] at key
  exact key

end TwinFrame

end Eigen

end CFSG.ClassicalInvolution.ModelFacts.Orth15
