module

public import CFSG.CGT.Timmesfeld75.SLTransvection

public section

namespace CFSG.CGT.T75K

open Module LinearMap CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

section Basic

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def sv (g : SL(n, F)) (x : Fin n → F) : Fin n → F :=
  (g : Matrix (Fin n) (Fin n) F) *ᵥ x

theorem sv_mul (g h : SL(n, F)) (x : Fin n → F) : sv (g * h) x = sv g (sv h x) := by
  simp [sv, Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem sv_one (x : Fin n → F) : sv (1 : SL(n, F)) x = x := by
  simp [sv]

theorem sv_inv_sv (g : SL(n, F)) (x : Fin n → F) : sv g (sv g⁻¹ x) = x := by
  rw [← sv_mul, mul_inv_cancel, sv_one]

theorem sv_sv_inv (g : SL(n, F)) (x : Fin n → F) : sv g⁻¹ (sv g x) = x := by
  rw [← sv_mul, inv_mul_cancel, sv_one]

theorem sv_add (g : SL(n, F)) (x y : Fin n → F) : sv g (x + y) = sv g x + sv g y :=
  Matrix.mulVec_add _ _ _

theorem sv_sub (g : SL(n, F)) (x y : Fin n → F) : sv g (x - y) = sv g x - sv g y :=
  Matrix.mulVec_sub _ _ _

theorem sv_smul (g : SL(n, F)) (a : F) (x : Fin n → F) : sv g (a • x) = a • sv g x :=
  Matrix.mulVec_smul _ _ _

theorem sv_neg (g : SL(n, F)) (x : Fin n → F) : sv g (-x) = - sv g x :=
  Matrix.mulVec_neg _ _

theorem sv_ext {g h : SL(n, F)} (e : ∀ x, sv g x = sv h x) : g = h :=
  Subtype.ext (Matrix.ext_iff_mulVec.2 e)

theorem add_self_of_char_two [CharP F 2] (v : Fin n → F) : v + v = 0 := by
  have h20 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  rw [← two_smul F v, h20, zero_smul]

theorem ncard_range_smul_le [Finite F] (p : Fin n → F) :
    (Set.range (fun a : F => a • p)).ncard ≤ Nat.card F := by
  rw [← Set.image_univ, ← Set.ncard_univ F]
  exact Set.ncard_image_le (Set.toFinite _)

end Basic

section Unip

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def Unip (f : Dual F (Fin n → F)) : Set SL(n, F) :=
  {g | (∀ x, f x = 0 → sv g x = x) ∧ ∀ x, f (sv g x - x) = 0}

@[expose] def lab (e₁ : Fin n → F) (g : SL(n, F)) : Fin n → F := sv g e₁ - e₁

variable {f : Dual F (Fin n → F)} {e₁ : Fin n → F}

theorem unip_apply (he : f e₁ = 1) {g : SL(n, F)} (hg : g ∈ Unip f) (x : Fin n → F) :
    sv g x = x + f x • lab e₁ g := by
  have h1 : f (x - f x • e₁) = 0 := by
    rw [map_sub, map_smul, he, smul_eq_mul, mul_one, sub_self]
  have h2 := hg.1 _ h1
  rw [sv_sub, sv_smul] at h2
  unfold lab
  have h3 : sv g x = (x - f x • e₁) + f x • sv g e₁ := by
    rw [← h2]; abel
  rw [h3]
  module

theorem unip_lab_mem {g : SL(n, F)} (hg : g ∈ Unip f) : f (lab e₁ g) = 0 :=
  hg.2 e₁

theorem unip_ext (he : f e₁ = 1) {g g' : SL(n, F)} (hg : g ∈ Unip f) (hg' : g' ∈ Unip f)
    (h : lab e₁ g = lab e₁ g') : g = g' :=
  sv_ext fun x => by rw [unip_apply he hg, unip_apply he hg', h]

theorem unip_one : (1 : SL(n, F)) ∈ Unip f :=
  ⟨fun x _ => sv_one x, fun x => by rw [sv_one, sub_self, map_zero]⟩

theorem unip_inv {g : SL(n, F)} (hg : g ∈ Unip f) : g⁻¹ ∈ Unip f := by
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · have := hg.1 x hx
    calc sv g⁻¹ x = sv g⁻¹ (sv g x) := by rw [this]
      _ = x := sv_sv_inv g x
  · have h := hg.2 (sv g⁻¹ x)
    rw [sv_inv_sv] at h
    have e : sv g⁻¹ x - x = -(x - sv g⁻¹ x) := by abel
    rw [e, map_neg, neg_eq_zero]
    exact h

theorem unip_lab_mul {g g' : SL(n, F)} (hg : g ∈ Unip f) (hg' : g' ∈ Unip f) :
    lab e₁ (g * g') = lab e₁ g + lab e₁ g' := by
  have h1 : sv g' e₁ = e₁ + lab e₁ g' := by unfold lab; abel
  have h2 : sv g (lab e₁ g') = lab e₁ g' := hg.1 _ (unip_lab_mem hg')
  unfold lab at *
  rw [sv_mul, h1, sv_add, h2]
  abel

theorem unip_lab_one : lab e₁ (1 : SL(n, F)) = 0 := by
  unfold lab; rw [sv_one, sub_self]

theorem unip_lab_inv {g : SL(n, F)} (hg : g ∈ Unip f) :
    lab e₁ g⁻¹ = - lab e₁ g := by
  have := unip_lab_mul (e₁ := e₁) (unip_inv hg) hg
  rw [inv_mul_cancel, unip_lab_one] at this
  exact eq_neg_of_add_eq_zero_left this.symm

theorem unip_conj (he : f e₁ = 1) {τ g : SL(n, F)} (hτ : ∀ x, f (sv τ x) = f x)
    (hg : g ∈ Unip f) : τ * g * τ⁻¹ ∈ Unip f ∧ lab e₁ (τ * g * τ⁻¹) = sv τ (lab e₁ g) := by
  have hτ' : ∀ x, f (sv τ⁻¹ x) = f x := fun x => by
    have := hτ (sv τ⁻¹ x)
    rw [sv_inv_sv] at this
    exact this.symm
  have hmem : τ * g * τ⁻¹ ∈ Unip f := by
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · have h0 : f (sv τ⁻¹ x) = 0 := by rw [hτ', hx]
      rw [sv_mul, sv_mul, hg.1 _ h0, sv_inv_sv]
    · have h2 := hg.2 (sv τ⁻¹ x)
      rw [sv_mul, sv_mul]
      have e : sv τ (sv g (sv τ⁻¹ x)) - x =
          sv τ (sv g (sv τ⁻¹ x) - sv τ⁻¹ x) := by
        rw [sv_sub, sv_inv_sv]
      rw [e, hτ, h2]
  refine ⟨hmem, ?_⟩
  have ha : f (sv τ⁻¹ e₁) = 1 := by rw [hτ', he]
  have h1 : sv g (sv τ⁻¹ e₁) = sv τ⁻¹ e₁ + lab e₁ g := by
    rw [unip_apply he hg, ha, one_smul]
  have h3 : sv (τ * g * τ⁻¹) e₁ = e₁ + sv τ (lab e₁ g) := by
    rw [sv_mul, sv_mul, h1, sv_add, sv_inv_sv]
  show sv (τ * g * τ⁻¹) e₁ - e₁ = _
  rw [h3]
  abel

end Unip

section Invol

variable {F : Type*} [Field F] {n : ℕ} {f : Dual F (Fin n → F)}

theorem unip_of_invol [CharP F 2] {g : SL(n, F)} (hg2 : g * g = 1)
    (hfix : ∀ x, sv g x = x ↔ f x = 0) : g ∈ Unip f := by
  refine ⟨fun x hx => (hfix x).2 hx, fun x => ?_⟩
  rw [← hfix]
  have h2 : sv g (sv g x) = x := by rw [← sv_mul, hg2, sv_one]
  have h20 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  rw [sv_sub, h2]
  have h3 : (2 : F) • (sv g x - x) = 0 := by rw [h20, zero_smul]
  rw [two_smul] at h3
  have h4 : x - sv g x = -(sv g x - x) := by abel
  rw [h4, ← eq_neg_of_add_eq_zero_left h3]

end Invol

section Transv

variable {F : Type*} [Field F] {n : ℕ}

theorem exists_transv {f' : Dual F (Fin n → F)} {p : Fin n → F} (h : f' p = 0) :
    ∃ τ : SL(n, F), (∀ x, sv τ x = x + f' x • p) ∧
      Matrix.SpecialLinearGroup.toLin' τ = LinearEquiv.transvection h := by
  have hdet : (LinearEquiv.transvection h).det = 1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    have e : ((LinearEquiv.transvection h : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
        (Fin n → F) →ₗ[F] (Fin n → F)) = LinearMap.transvection f' p := by
      ext x : 1
      simp
    rw [e, LinearMap.transvection.det, h]
    simp
  refine ⟨(Matrix.SpecialLinearGroup.toLin'_equiv).symm ⟨LinearEquiv.transvection h, hdet⟩, ?_⟩
  have h1 := (Matrix.SpecialLinearGroup.toLin'_equiv (R := F) (n := Fin n)).apply_symm_apply
    ⟨LinearEquiv.transvection h, hdet⟩
  have h2 : Matrix.SpecialLinearGroup.toLin'
      ((Matrix.SpecialLinearGroup.toLin'_equiv).symm ⟨LinearEquiv.transvection h, hdet⟩) =
      LinearEquiv.transvection h := congrArg Subtype.val h1
  refine ⟨fun x => ?_, h2⟩
  have h3 := congrArg (fun e : (Fin n → F) ≃ₗ[F] (Fin n → F) => e x) h2
  simp only [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
    LinearEquiv.transvection.apply] at h3
  exact h3

theorem exists_isTransvection {f' : Dual F (Fin n → F)} {p : Fin n → F} (h : f' p = 0)
    (hf : f' ≠ 0) (hp : p ≠ 0) :
    ∃ τ : SL(n, F), (∀ x, sv τ x = x + f' x • p) ∧ IsTransvection τ := by
  obtain ⟨τ, hτ, hτ'⟩ := exists_transv h
  refine ⟨τ, hτ, ?_, f', p, h, hτ'⟩
  intro h1
  obtain ⟨w, hw⟩ : ∃ w, f' w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf (LinearMap.ext hcon)
  have h2 := hτ w
  rw [h1, sv_one] at h2
  have h3 : f' w • p = 0 := by
    have := h2
    rw [eq_comm, add_eq_left] at this
    exact this
  rcases smul_eq_zero.1 h3 with h4 | h4
  · exact hw h4
  · exact hp h4

theorem exists_data_of_isTransvection {u : SL(n, F)} (hu : IsTransvection u) :
    ∃ (f₀ : Dual F (Fin n → F)) (p : Fin n → F), f₀ p = 0 ∧ f₀ ≠ 0 ∧ p ≠ 0 ∧
      ∀ y, sv u y = y + f₀ y • p := by
  obtain ⟨hu1, f₀, p, hfv, he⟩ := hu
  have hne : LinearEquiv.transvection hfv ≠ 1 := by
    rw [← he]
    intro h
    apply hu1
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [h, map_one]
  obtain ⟨hf, hp⟩ := ne_zero_of_transvection_ne_one hfv hne
  refine ⟨f₀, p, hfv, hf, hp, fun y => ?_⟩
  have h3 := congrArg (fun e : (Fin n → F) ≃ₗ[F] (Fin n → F) => e y) he
  simp only [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
    LinearEquiv.transvection.apply] at h3
  exact h3

theorem exists_dual_of_notMem_span {p v : Fin n → F} (hv : v ∉ Submodule.span F {p}) :
    ∃ f' : Dual F (Fin n → F), f' p = 0 ∧ f' v = 1 := by
  obtain ⟨f, hfv, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hp0 : f p = 0 := by
    have : f p ∈ Submodule.map f (Submodule.span F {p}) :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self p)
    rw [hfp] at this
    exact Submodule.mem_bot F |>.1 this
  refine ⟨(f v)⁻¹ • f, ?_, ?_⟩
  · simp [hp0]
  · simp [inv_mul_cancel₀ hfv]

end Transv

end CFSG.CGT.T75K
