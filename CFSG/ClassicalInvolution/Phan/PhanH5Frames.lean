module

public import CFSG.ClassicalInvolution.Phan.PhanH4Theta
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge

public section

namespace CFSG.ClassicalInvolution.PhanB3.H

open CliffordAlgebra QuadraticMap CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalInvolution.WeakCT
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

variable {F : Type} [Field F]



@[expose] def mk7 (x0 x1 x2 y0 y1 y2 z : F) : Fin 3 ⊕ Fin 3 ⊕ Unit → F :=
  Sum.elim ![x0, x1, x2] (Sum.elim ![y0, y1, y2] fun _ => z)

omit [Field F] in
@[simp] theorem mk7_x0 (x0 x1 x2 y0 y1 y2 z : F) : mk7 x0 x1 x2 y0 y1 y2 z (.inl 0) = x0 := rfl
omit [Field F] in
@[simp] theorem mk7_x1 (x0 x1 x2 y0 y1 y2 z : F) : mk7 x0 x1 x2 y0 y1 y2 z (.inl 1) = x1 := rfl
omit [Field F] in
@[simp] theorem mk7_x2 (x0 x1 x2 y0 y1 y2 z : F) : mk7 x0 x1 x2 y0 y1 y2 z (.inl 2) = x2 := rfl
omit [Field F] in
@[simp] theorem mk7_y0 (x0 x1 x2 y0 y1 y2 z : F) :
    mk7 x0 x1 x2 y0 y1 y2 z (.inr (.inl 0)) = y0 := rfl
omit [Field F] in
@[simp] theorem mk7_y1 (x0 x1 x2 y0 y1 y2 z : F) :
    mk7 x0 x1 x2 y0 y1 y2 z (.inr (.inl 1)) = y1 := rfl
omit [Field F] in
@[simp] theorem mk7_y2 (x0 x1 x2 y0 y1 y2 z : F) :
    mk7 x0 x1 x2 y0 y1 y2 z (.inr (.inl 2)) = y2 := rfl
omit [Field F] in
@[simp] theorem mk7_z (x0 x1 x2 y0 y1 y2 z : F) (u : Unit) :
    mk7 x0 x1 x2 y0 y1 y2 z (.inr (.inr u)) = z := rfl

theorem quad_mk7 (x0 x1 x2 y0 y1 y2 z : F) :
    quadOdd 3 F (mk7 x0 x1 x2 y0 y1 y2 z) = x0 * y0 + x1 * y1 + x2 * y2 + z ^ 2 := by
  simp [quadOdd_apply, mk7, Fin.sum_univ_three]

theorem polar_mk7 (x0 x1 x2 y0 y1 y2 z x0' x1' x2' y0' y1' y2' z' : F) :
    polar (quadOdd 3 F) (mk7 x0 x1 x2 y0 y1 y2 z) (mk7 x0' x1' x2' y0' y1' y2' z') =
      x0 * y0' + x0' * y0 + (x1 * y1' + x1' * y1) + (x2 * y2' + x2' * y2) + 2 * (z * z') := by
  simp [polar_quadOdd, mk7, Fin.sum_univ_three]

omit [Field F] in
theorem mk7_eta (v : Fin 3 ⊕ Fin 3 ⊕ Unit → F) :
    v = mk7 (v (.inl 0)) (v (.inl 1)) (v (.inl 2)) (v (.inr (.inl 0))) (v (.inr (.inl 1)))
      (v (.inr (.inl 2))) (v (.inr (.inr ()))) := by
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i <;> simp [mk7]
  · fin_cases i <;> simp [mk7]
  · simp [mk7]

theorem neg_mk7 (x0 x1 x2 y0 y1 y2 z : F) :
    -mk7 x0 x1 x2 y0 y1 y2 z = mk7 (-x0) (-x1) (-x2) (-y0) (-y1) (-y2) (-z) := by
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i <;> simp [mk7]
  · fin_cases i <;> simp [mk7]
  · simp [mk7]

theorem kappa_eq_mk7 (v : Fin 2 ⊕ Fin 2 ⊕ Unit → F) :
    kappa v = mk7 (v (.inr (.inr ()))) (2 * v (.inl 0)) (v (.inl 1)) (-v (.inr (.inr ())))
      (-(1 / 2) * v (.inr (.inl 0))) (-v (.inr (.inl 1))) 0 := by
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i <;> simp [kappa_apply, mk7]
  · fin_cases i <;> simp [kappa_apply, mk7]
  · simp [kappa_apply, mk7]


noncomputable def hyp1 (h2 : (2 : F) ≠ 0) : HypFrame (quadOdd 3 F) 2 where
  vec i s := cond s (![mk7 0 2 0 0 0 0 0, mk7 0 0 1 0 0 0 0] i)
    (![mk7 0 0 0 0 (1 / 2) 0 0, mk7 0 0 0 0 0 1 0] i)
  map_vec i s := by
    fin_cases i <;> cases s <;> simp [quad_mk7]
  polar_vec_of_ne i j hij s t := by
    fin_cases i <;> fin_cases j <;> simp at hij <;> cases s <;> cases t <;> simp [polar_mk7]
  polar_vec_not i s := by
    have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    fin_cases i <;> cases s <;> simp [polar_mk7, h]
  exists_aux i j := ⟨mk7 0 0 0 0 0 0 1, by simp [quad_mk7], fun s => by
    fin_cases i <;> fin_cases j <;> cases s <;> simp [polar_mk7]⟩

noncomputable def hyp0 (h2 : (2 : F) ≠ 0) : HypFrame (quadOdd 3 F) 2 where
  vec i s := cond s
    (![mk7 (1 / 2) (1 / 2) 0 (1 / 2) (-(1 / 2)) 0 0, mk7 0 0 (1 / 2) 0 0 (-(1 / 2)) (1 / 2)] i)
    (![mk7 (1 / 2) (-(1 / 2)) 0 (1 / 2) (1 / 2) 0 0, mk7 0 0 (-(1 / 2)) 0 0 (1 / 2) (1 / 2)] i)
  map_vec i s := by
    have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    fin_cases i <;> cases s <;> simp [quad_mk7] <;> field_simp <;> ring
  polar_vec_of_ne i j hij s t := by
    fin_cases i <;> fin_cases j <;> simp at hij <;> cases s <;> cases t <;> simp [polar_mk7]
  polar_vec_not i s := by
    have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    fin_cases i <;> cases s <;> simp [polar_mk7] <;> field_simp <;> ring
  exists_aux i j := ⟨mk7 0 1 0 0 1 0 0, by simp [quad_mk7], fun s => by
    fin_cases i <;> fin_cases j <;> cases s <;> simp [polar_mk7]⟩


section Link
open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalInvolution.WeakCT
open CFSG.Assembly.LowTwoRank (StatedSp)

theorem kappa_vec_00 (h2 : (2 : F) ≠ 0) :
    kappa ((oddFrame 2 F).vec 0 true) = (hyp1 h2).vec 0 true := by
  simp [kappa_eq_mk7, hyp1, oddVec]

theorem kappa_vec_01 (h2 : (2 : F) ≠ 0) :
    kappa ((oddFrame 2 F).vec 0 false) = -(hyp1 h2).vec 0 false := by
  simp [kappa_eq_mk7, hyp1, oddVec, neg_mk7]

theorem kappa_vec_10 (h2 : (2 : F) ≠ 0) :
    kappa ((oddFrame 2 F).vec 1 true) = (hyp1 h2).vec 1 true := by
  simp [kappa_eq_mk7, hyp1, oddVec]

theorem kappa_vec_11 (h2 : (2 : F) ≠ 0) :
    kappa ((oddFrame 2 F).vec 1 false) = -(hyp1 h2).vec 1 false := by
  simp [kappa_eq_mk7, hyp1, oddVec, neg_mk7]


variable {φ : StatedSp 2 F →* spinGroup (quadOdd 2 F)} {θ : StatedSp 2 F →* spinGroup (quadOdd 3 F)}

theorem theta_Lu (h2 : (2 : F) ≠ 0) (hφ : IsLevi φ)
    (hcoe : ∀ g, (θ g : CliffordAlgebra (quadOdd 3 F)) =
      negSpinHom (quadOdd 2 F) (quadOdd 3 F) kappa (quad_kappa h2) (φ g)) (c : F) :
    θ (spBlock F 1 (tv 0 1 c)) =
      (hyp1 h2).longRoot (i := 0) (j := 1) (by decide) true false (.ofAdd c) := by
  apply Subtype.ext
  have hx : (φ (spBlock F 1 (tv 0 1 c)) : CliffordAlgebra (quadOdd 2 F)) = 1 + c •
      (ι (quadOdd 2 F) ((oddFrame 2 F).vec 0 true) *
        ι (quadOdd 2 F) ((oddFrame 2 F).vec 1 false)) := by
    rw [phi_Lu hφ, HypFrame.coe_longRoot]
  rw [hcoe, negSpinHom_root _ _ _ _ _ hx, HypFrame.coe_longRoot, kappa_vec_00 h2, kappa_vec_11 h2,
    map_neg, mul_neg, smul_neg, neg_smul, neg_neg]

theorem theta_Ll (h2 : (2 : F) ≠ 0) (hφ : IsLevi φ)
    (hcoe : ∀ g, (θ g : CliffordAlgebra (quadOdd 3 F)) =
      negSpinHom (quadOdd 2 F) (quadOdd 3 F) kappa (quad_kappa h2) (φ g)) (c : F) :
    θ (spBlock F 1 (tv 1 0 c)) =
      (hyp1 h2).longRoot (i := 1) (j := 0) (by decide) true false (.ofAdd c) := by
  apply Subtype.ext
  have hx : (φ (spBlock F 1 (tv 1 0 c)) : CliffordAlgebra (quadOdd 2 F)) = 1 + c •
      (ι (quadOdd 2 F) ((oddFrame 2 F).vec 1 true) *
        ι (quadOdd 2 F) ((oddFrame 2 F).vec 0 false)) := by
    rw [phi_Ll hφ, HypFrame.coe_longRoot]
  rw [hcoe, negSpinHom_root _ _ _ _ _ hx, HypFrame.coe_longRoot, kappa_vec_10 h2, kappa_vec_01 h2,
    map_neg, mul_neg, smul_neg, neg_smul, neg_neg]

theorem theta_comp_spBlock_one (h2 : (2 : F) ≠ 0) (hφ : IsLevi φ)
    (hcoe : ∀ g, (θ g : CliffordAlgebra (quadOdd 3 F)) =
      negSpinHom (quadOdd 2 F) (quadOdd 3 F) kappa (quad_kappa h2) (φ g)) :
    θ.comp (spBlock F 1) = (hyp1 h2).longSL2 (i := 0) (j := 1) (by decide) true false := by
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · rw [MonoidHom.comp_apply, theta_Lu h2 hφ hcoe, tv01_eq_sl2Upper]
    exact (HypFrame.longSL2_upperSL2 (hyp1 h2) _ true false c).symm
  · rw [MonoidHom.comp_apply, theta_Ll h2 hφ hcoe, tv10_eq_sl2Lower]
    exact (HypFrame.longSL2_lowerSL2 (hyp1 h2) _ true false c).symm


theorem La1_neg_one_mk7 (h2 : (2 : F) ≠ 0) (x0 x1 x2 y0 y1 y2 z : F) :
    ((hyp1 h2).toFrame (i := 0) (j := 1) (by decide) true false).La (-1)
      (mk7 x0 x1 x2 y0 y1 y2 z) = mk7 x0 (-x1) (-x2) y0 (-y1) (-y2) z := by
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  rw [Frame.La_neg_one_apply]
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i <;>
    simp [Frame.incl_apply, Frame.coords_apply, HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂,
      Frame.f₂, hyp1, polar_mk7] <;> field_simp <;> ring
  · fin_cases i <;>
    simp [Frame.incl_apply, Frame.coords_apply, HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂,
      Frame.f₂, hyp1, polar_mk7] <;> field_simp <;> ring
  · simp [Frame.incl_apply, Frame.coords_apply, HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂,
      Frame.f₂, hyp1, polar_mk7]


theorem La0_neg_one_mk7 (h2 : (2 : F) ≠ 0) (x0 x1 x2 y0 y1 y2 z : F) :
    ((hyp0 h2).toFrame (i := 0) (j := 1) (by decide) true false).La (-1)
      (mk7 x0 x1 x2 y0 y1 y2 z) = mk7 (-y0) y1 y2 (-x0) x1 x2 (-z) := by
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  rw [Frame.La_neg_one_apply]
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i <;>
    simp [Frame.incl_apply, Frame.coords_apply, HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂,
      Frame.f₂, hyp0, polar_mk7] <;> field_simp <;> ring
  · fin_cases i <;>
    simp [Frame.incl_apply, Frame.coords_apply, HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂,
      Frame.f₂, hyp0, polar_mk7] <;> field_simp <;> ring
  · simp [Frame.incl_apply, Frame.coords_apply, HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂,
      Frame.f₂, hyp0, polar_mk7]
    field_simp
    ring


noncomputable abbrev fr1 (h2 : (2 : F) ≠ 0) : Frame (quadOdd 3 F) :=
  (hyp1 h2).toFrame (i := 0) (j := 1) (by decide) true false

noncomputable abbrev fr0 (h2 : (2 : F) ≠ 0) : Frame (quadOdd 3 F) :=
  (hyp0 h2).toFrame (i := 0) (j := 1) (by decide) true false

theorem fr0_e₁_eq (h2 : (2 : F) ≠ 0) :
    (fr0 h2).e₁ = mk7 (1 / 2) (1 / 2) 0 (1 / 2) (-(1 / 2)) 0 0 := by
  simp [fr0, hyp0, HypFrame.toFrame, Frame.e₁]

theorem fr0_e₂_eq (h2 : (2 : F) ≠ 0) :
    (fr0 h2).e₂ = mk7 0 0 (-(1 / 2)) 0 0 (1 / 2) (1 / 2) := by
  simp [fr0, hyp0, HypFrame.toFrame, Frame.e₂]

theorem La1_neg_one (h2 : (2 : F) ≠ 0) (x : Fin 3 ⊕ Fin 3 ⊕ Unit → F) :
    (fr1 h2).La (-1) x = mk7 (x (.inl 0)) (-x (.inl 1)) (-x (.inl 2)) (x (.inr (.inl 0)))
      (-x (.inr (.inl 1))) (-x (.inr (.inl 2))) (x (.inr (.inr ()))) := by
  conv_lhs => rw [mk7_eta x]
  exact La1_neg_one_mk7 h2 _ _ _ _ _ _ _

theorem La0_neg_one (h2 : (2 : F) ≠ 0) (x : Fin 3 ⊕ Fin 3 ⊕ Unit → F) :
    (fr0 h2).La (-1) x = mk7 (-x (.inr (.inl 0))) (x (.inr (.inl 1))) (x (.inr (.inl 2)))
      (-x (.inl 0)) (x (.inl 1)) (x (.inl 2)) (-x (.inr (.inr ()))) := by
  conv_lhs => rw [mk7_eta x]
  exact La0_neg_one_mk7 h2 _ _ _ _ _ _ _

theorem fr1_comm_fr0 (h2 : (2 : F) ≠ 0) :
    (fr0 h2).La (-1) * (fr1 h2).La (-1) = (fr1 h2).La (-1) * (fr0 h2).La (-1) := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, La1_neg_one, La0_neg_one, La0_neg_one,
    La1_neg_one]
  simp

theorem mem_inf_fr (h2 : (2 : F) ≠ 0) (x : Fin 3 ⊕ Fin 3 ⊕ Unit → F) :
    x ∈ (fr0 h2).span ⊓ (fr1 h2).span ↔
      ∃ a b : F, x = mk7 0 a b 0 (-a) (-b) 0 := by
  rw [Submodule.mem_inf, Frame.mem_span_iff_inv _ h2, Frame.mem_span_iff_inv _ h2,
    La0_neg_one, La1_neg_one]
  have hx : ∀ t : F, t = -t → t = 0 := fun t ht => by
    have : (2 : F) * t = 0 := by linear_combination ht
    exact (mul_eq_zero.mp this).resolve_left h2
  constructor
  · rintro ⟨h0, h1⟩
    have a1 := congrFun h1 (.inl 0)
    have a2 := congrFun h1 (.inr (.inl 0))
    have a3 := congrFun h1 (.inr (.inr ()))
    have b1 := congrFun h0 (.inl 1)
    have b2 := congrFun h0 (.inl 2)
    simp at a1 a2 a3 b1 b2
    have x0 := hx _ a1
    have y0 := hx _ a2
    have z0 := hx _ a3
    refine ⟨x (.inl 1), x (.inl 2), ?_⟩
    rw [mk7_eta x]
    have : x (.inr (.inl 1)) = -x (.inl 1) := by linear_combination b1
    have : x (.inr (.inl 2)) = -x (.inl 2) := by linear_combination b2
    simp [x0, y0, z0, *]
  · rintro ⟨a, b, rfl⟩
    simp [neg_mk7]

noncomputable def mapPp : (F × F) →ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Unit → F) where
  toFun p := mk7 0 p.1 p.2 0 (-p.1) (-p.2) 0
  map_add' p q := by
    funext s
    rcases s with i | i | u
    · fin_cases i <;> simp
    · fin_cases i <;> simp <;> ring
    · simp
  map_smul' c p := by
    funext s
    rcases s with i | i | u
    · fin_cases i <;> simp
    · fin_cases i <;> simp
    · simp

theorem mapPp_injective : Function.Injective (mapPp (F := F)) := by
  intro p q h
  have h1 := congrFun h (.inl 1)
  have h2 := congrFun h (.inl 2)
  simp [mapPp] at h1 h2
  exact Prod.ext h1 h2

theorem inf_fr_eq_range (h2 : (2 : F) ≠ 0) :
    (fr0 h2).span ⊓ (fr1 h2).span = LinearMap.range mapPp := by
  ext x
  rw [mem_inf_fr h2, LinearMap.mem_range]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨(a, b), rfl⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨a, b, rfl⟩

theorem finrank_inf_fr (h2 : (2 : F) ≠ 0) :
    Module.finrank F ↥((fr0 h2).span ⊓ (fr1 h2).span) = 2 := by
  rw [inf_fr_eq_range h2, LinearMap.finrank_range_of_inj mapPp_injective]
  simp

theorem not_hasSingularVector_inf_fr (h2 : (2 : F) ≠ 0) (hn1 : ¬ IsSquare (-1 : F)) :
    ¬ HasSingularVector (quadOdd 3 F) ((fr0 h2).span ⊓ (fr1 h2).span) := by
  rintro ⟨v, hv, hv0, hQ⟩
  obtain ⟨a, b, rfl⟩ := (mem_inf_fr h2 v).mp hv
  rw [quad_mk7] at hQ
  simp at hQ
  have hb : b = 0 := by
    by_contra hb
    exact hn1 ⟨a / b, by field_simp; linear_combination hQ⟩
  subst hb
  have ha : a = 0 := by simpa using hQ
  subst ha
  refine hv0 ?_
  funext s
  rcases s with i | i | u
  · fin_cases i <;> simp
  · fin_cases i <;> simp
  · simp

end Link

end CFSG.ClassicalInvolution.PhanB3.H
