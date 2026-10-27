module

public import CFSG.LieType.Chevalley.RootWeightFiltrationShifts
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Polynomial.Basic

public noncomputable section

namespace CFSG.LieType.Chevalley.RootWeight

open scoped RealInnerProductSpace Pointwise

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

open _root_.Classical in
@[expose] def conjFamily (A : Finset (Module.End K V)) (g : (Module.End K V)ˣ) :
    Finset (Module.End K V) :=
  A.image fun a => (↑g⁻¹ : Module.End K V) * a * g

theorem conjFamily_nonempty {A : Finset (Module.End K V)} (hA : A.Nonempty)
    (g : (Module.End K V)ˣ) : (conjFamily A g).Nonempty := by
  classical
  exact hA.image _

theorem zero_notMem_conjFamily {A : Finset (Module.End K V)}
    (hA0 : (0 : Module.End K V) ∉ A) (g : (Module.End K V)ˣ) :
    (0 : Module.End K V) ∉ conjFamily A g := fun h0 => by
  classical
  obtain ⟨a, ha, h⟩ := Finset.mem_image.1 h0
  have : a = (g : Module.End K V) * ((↑g⁻¹ : Module.End K V) * a * g) * ↑g⁻¹ := by
    simp only [← mul_assoc, Units.mul_inv, one_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  rw [h, mul_zero, zero_mul] at this
  exact hA0 (this ▸ ha)

theorem conjFamily_mul (A : Finset (Module.End K V)) (g k : (Module.End K V)ˣ) :
    conjFamily A (g * k) = conjFamily (conjFamily A g) k := by
  classical
  rw [conjFamily, conjFamily, conjFamily, Finset.image_image]
  refine Finset.image_congr fun a _ => ?_
  simp only [Function.comp_apply, mul_inv_rev, Units.val_mul, mul_assoc]

open _root_.Classical in
theorem conjFamily_eq_of_image_eq {A : Finset (Module.End K V)} {h : (Module.End K V)ˣ}
    (hh : (A.image fun a => (h : Module.End K V) * a * ↑h⁻¹) = A) : conjFamily A h = A := by
  conv_lhs => rw [← hh]
  rw [conjFamily, Finset.image_image]
  convert Finset.image_id (s := A) using 2
  funext a
  simp only [Function.comp_apply, id, ← mul_assoc, Units.inv_mul, one_mul]
  rw [mul_assoc, Units.inv_mul, mul_one]

section Semilinear

variable {σ σ' : K →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

@[expose] def semilinearConjUnit (s : V ≃ₛₗ[σ] V) (g : (Module.End K V)ˣ) : (Module.End K V)ˣ where
  val := semilinearConj s g
  inv := semilinearConj s ↑g⁻¹
  val_inv := LinearMap.ext fun x => by
    simp only [Module.End.mul_apply, semilinearConj_apply, LinearEquiv.symm_apply_apply,
      Module.End.one_apply]
    rw [← Module.End.mul_apply (g : Module.End K V), Units.mul_inv, Module.End.one_apply,
      LinearEquiv.apply_symm_apply]
  inv_val := LinearMap.ext fun x => by
    simp only [Module.End.mul_apply, semilinearConj_apply, LinearEquiv.symm_apply_apply,
      Module.End.one_apply]
    rw [← Module.End.mul_apply (↑g⁻¹ : Module.End K V), Units.inv_mul, Module.End.one_apply,
      LinearEquiv.apply_symm_apply]

theorem coe_semilinearConjUnit (s : V ≃ₛₗ[σ] V) (g : (Module.End K V)ˣ) :
    (semilinearConjUnit s g : Module.End K V) = semilinearConj s g :=
  rfl

theorem coe_semilinearConjUnit_inv (s : V ≃ₛₗ[σ] V) (g : (Module.End K V)ˣ) :
    (↑(semilinearConjUnit s g)⁻¹ : Module.End K V) = semilinearConj s ↑g⁻¹ :=
  rfl

theorem semilinearConjUnit_symm_semilinearConjUnit (s : V ≃ₛₗ[σ] V) (g : (Module.End K V)ˣ) :
    semilinearConjUnit s (semilinearConjUnit s.symm g) = g :=
  Units.ext (LinearMap.ext fun x => by
    rw [coe_semilinearConjUnit, semilinearConj_apply, coe_semilinearConjUnit, semilinearConj_apply,
      LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])

open _root_.Classical in
theorem conjFamily_semilinearConj (s : V ≃ₛₗ[σ] V) (A : Finset (Module.End K V))
    (g : (Module.End K V)ˣ) :
    conjFamily (A.image (semilinearConj s)) (semilinearConjUnit s g) =
      (conjFamily A g).image (semilinearConj s) := by
  rw [conjFamily, conjFamily, Finset.image_image, Finset.image_image]
  refine Finset.image_congr fun a _ => LinearMap.ext fun x => ?_
  simp only [Function.comp_apply, Module.End.mul_apply, coe_semilinearConjUnit_inv,
    coe_semilinearConjUnit, semilinearConj_apply, LinearEquiv.symm_apply_apply]

end Semilinear

variable {E : Type*} [DecidableEq E] {Ω : Finset E} {Vχ : E → Submodule K V}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[expose] def frameShift (hV : DirectSum.IsInternal fun χ : Ω => Vχ χ)
    (A : Finset (Module.End K V)) (g : (Module.End K V)ˣ) (l : E) : ℝ :=
  minWeightShift hV (conjFamily A g) l

variable [FiniteDimensional ℝ E] [FiniteDimensional K V]
  (hV : DirectSum.IsInternal fun χ : Ω => Vχ χ) {A : Finset (Module.End K V)}

theorem continuous_frameShift (hA : A.Nonempty) (hA0 : (0 : Module.End K V) ∉ A)
    (g : (Module.End K V)ˣ) : Continuous (frameShift hV A g) :=
  (weight_filtration_endomorphism_shifts hV _ (conjFamily_nonempty hA g)
    (zero_notMem_conjFamily hA0 g)).2.2.2.1

theorem frameShift_smul (hA : A.Nonempty) (hA0 : (0 : Module.End K V) ∉ A)
    (g : (Module.End K V)ˣ) {t : ℝ} (ht : 0 ≤ t) (l : E) :
    frameShift hV A g (t • l) = t * frameShift hV A g l :=
  (weight_filtration_endomorphism_shifts hV _ (conjFamily_nonempty hA g)
    (zero_notMem_conjFamily hA0 g)).2.2.2.2.1 t ht l

theorem frameShift_add_le (hA : A.Nonempty) (hA0 : (0 : Module.End K V) ∉ A)
    (g : (Module.End K V)ˣ) (l m : E) :
    frameShift hV A g l + frameShift hV A g m ≤ frameShift hV A g (l + m) :=
  (weight_filtration_endomorphism_shifts hV _ (conjFamily_nonempty hA g)
    (zero_notMem_conjFamily hA0 g)).2.2.2.2.2.1 l m

theorem frameShift_zero (hA : A.Nonempty) (hA0 : (0 : Module.End K V) ∉ A)
    (g : (Module.End K V)ˣ) : frameShift hV A g 0 = 0 := by
  have h := frameShift_smul hV hA hA0 g le_rfl (0 : E)
  rwa [zero_smul, zero_mul] at h

theorem frameShift_mul_of_preserve (hA : A.Nonempty) (hA0 : (0 : Module.End K V) ∉ A)
    (g b : (Module.End K V)ˣ) {l : E}
    (hb : ∀ c : ℝ, (weightFiltration Ω Vχ l c).map (b : Module.End K V) =
      weightFiltration Ω Vχ l c) :
    frameShift hV A (g * b) l = frameShift hV A g l := by
  rw [frameShift, frameShift, conjFamily_mul]
  exact (weight_filtration_endomorphism_shifts hV _ (conjFamily_nonempty hA g)
    (zero_notMem_conjFamily hA0 g)).2.2.1 l b hb

theorem frameShift_mul_rep (hA : A.Nonempty) (hA0 : (0 : Module.End K V) ∉ A)
    (g n : (Module.End K V)ˣ) {u : E ≃ₗᵢ[ℝ] E} (hu : Ω.image u = Ω)
    (hn : ∀ χ ∈ Ω, (Vχ χ).map (n : Module.End K V) = Vχ (u χ)) (l : E) :
    frameShift hV A (g * n) l = frameShift hV A g (u l) := by
  rw [frameShift, frameShift, conjFamily_mul]
  exact ((weight_filtration_endomorphism_shifts hV _ (conjFamily_nonempty hA g)
    (zero_notMem_conjFamily hA0 g)).2.2.2.2.2.2.1 u hu n hn).2 l

open _root_.Classical in
theorem frameShift_semilinearConj (hA : A.Nonempty) (hA0 : (0 : Module.End K V) ∉ A)
    {σ σ' : K →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (s : V ≃ₛₗ[σ] V)
    {u : E ≃ₗᵢ[ℝ] E} (hu : Ω.image u = Ω)
    (hs : ∀ χ ∈ Ω, (Vχ χ).map s.toLinearMap = Vχ (u χ)) (g : (Module.End K V)ˣ) (l : E) :
    frameShift hV (A.image (semilinearConj s)) (semilinearConjUnit s g) (u l) =
      frameShift hV A g l := by
  rw [frameShift, frameShift, conjFamily_semilinearConj]
  exact ((weight_filtration_endomorphism_shifts hV _ (conjFamily_nonempty hA g)
    (zero_notMem_conjFamily hA0 g)).2.2.2.2.2.2.2 u hu σ σ' s hs).2 l

theorem exists_frameShift_max (hA : A.Nonempty) (hA0 : (0 : Module.End K V) ∉ A)
    (G : Subgroup (Module.End K V)ˣ) [Finite G] {S : Set E} (hS : IsCompact S)
    (hSne : S.Nonempty) :
    ∃ g ∈ G, ∃ l ∈ S, ∀ g' ∈ G, ∀ l' ∈ S, frameShift hV A g' l' ≤ frameShift hV A g l := by
  have hmax : ∀ g : (Module.End K V)ˣ, ∃ l ∈ S, ∀ l' ∈ S,
      frameShift hV A g l' ≤ frameShift hV A g l := fun g => by
    obtain ⟨l, hl, hmax⟩ := hS.exists_isMaxOn hSne (continuous_frameShift hV hA hA0 g).continuousOn
    exact ⟨l, hl, fun l' hl' => hmax hl'⟩
  choose L hLS hL using hmax
  obtain ⟨g, hg⟩ := Finite.exists_max fun g : G => frameShift hV A g (L g)
  exact ⟨g, g.2, L g, hLS g, fun g' hg' l' hl' =>
    (hL g' l' hl').trans (hg ⟨g', hg'⟩)⟩

theorem map_weightFiltration_eq_of_dominant (hA : A.Nonempty) (hA0 : (0 : Module.End K V) ∉ A)
    {G B : Subgroup (Module.End K V)ˣ} (hBG : B ≤ G) {W : Subgroup (E ≃ₗᵢ[ℝ] E)}
    (hWΩ : ∀ w ∈ W, Ω.image w = Ω) {n : (E ≃ₗᵢ[ℝ] E) → (Module.End K V)ˣ}
    (hn : ∀ w ∈ W, ∀ χ ∈ Ω, (Vχ χ).map (n w : Module.End K V) = Vχ (w χ)) {Dom : Set E}
    (hB : ∀ b ∈ B, ∀ l ∈ Dom, ∀ c : ℝ,
      (weightFiltration Ω Vχ l c).map (b : Module.End K V) = weightFiltration Ω Vχ l c)
    (hG : (G : Set (Module.End K V)ˣ) =
      ⋃ w ∈ W, (B : Set (Module.End K V)ˣ) * {n w} * (B : Set (Module.End K V)ˣ))
    {M : ℝ} (hMpos : 0 < M) (hM : ∀ g ∈ G, ∀ l : E, ‖l‖ = 1 → frameShift hV A g l ≤ M)
    {g₁ g₂ : (Module.End K V)ˣ} (hg₁ : g₁ ∈ G) (hg₂ : g₂ ∈ G) {l m : E} (hl : l ∈ Dom)
    (hm : m ∈ Dom) (hl1 : ‖l‖ = 1) (hm1 : ‖m‖ = 1) (h₁ : frameShift hV A g₁ l = M)
    (h₂ : frameShift hV A g₂ m = M) (c : ℝ) :
    (weightFiltration Ω Vχ l c).map (g₁ : Module.End K V) =
      (weightFiltration Ω Vχ m c).map (g₂ : Module.End K V) := by
  have hmem : g₁⁻¹ * g₂ ∈ (G : Set (Module.End K V)ˣ) := mul_mem (inv_mem hg₁) hg₂
  rw [hG] at hmem
  simp only [Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨w, hw, hbw⟩ := hmem
  obtain ⟨_, ⟨b₁, hb₁, _, rfl, rfl⟩, b₂, hb₂, hb⟩ := hbw
  beta_reduce at hb
  set k := g₁ * b₁ with hk
  have hkG : k ∈ G := mul_mem hg₁ (hBG hb₁)
  have hkn : k * n w = g₂ * b₂⁻¹ := by
    rw [hk]
    calc g₁ * b₁ * n w = g₁ * (b₁ * n w * b₂) * b₂⁻¹ := by group
      _ = g₂ * b₂⁻¹ := by rw [hb]; group
  have hkl : frameShift hV A k l = M := by
    rw [hk, frameShift_mul_of_preserve hV hA hA0 g₁ b₁ (hB b₁ hb₁ l hl), h₁]
  have hkm : frameShift hV A k (w m) = M := by
    rw [← frameShift_mul_rep hV hA hA0 k (n w) (hWΩ w hw) (hn w hw), hkn,
      frameShift_mul_of_preserve hV hA hA0 g₂ b₂⁻¹ (hB b₂⁻¹ (inv_mem hb₂) m hm), h₂]
  have hwm1 : ‖w m‖ = 1 := by rw [LinearIsometryEquiv.norm_map, hm1]
  have hlm : l = w m := by
    by_contra hne
    set z : E := (1 / 2 : ℝ) • (l + w m) with hz
    have hzM : M ≤ frameShift hV A k z := by
      rw [hz, frameShift_smul hV hA hA0 k (by norm_num)]
      have := frameShift_add_le hV hA hA0 k l (w m)
      rw [hkl, hkm] at this
      linarith
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, frameShift_zero hV hA hA0] at hzM
      linarith
    have hzn : ‖z‖ < 1 := by
      have hsub : 0 < ‖l - w m‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      have e1 := norm_add_sq_real l (w m)
      have e2 := norm_sub_sq_real l (w m)
      have hsq : ‖z‖ ^ 2 < 1 := by
        rw [hz, norm_smul, mul_pow, e1, hl1, hwm1]
        rw [hl1, hwm1] at e2
        have : ‖(1 / 2 : ℝ)‖ ^ 2 = 1 / 4 := by norm_num
        rw [this]
        nlinarith
      nlinarith [norm_nonneg z]
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have hunit : ‖‖z‖⁻¹ • z‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hzpos.ne']
    have hbig := hM k hkG _ hunit
    rw [frameShift_smul hV hA hA0 k (inv_nonneg.2 hzpos.le)] at hbig
    have : M < ‖z‖⁻¹ * frameShift hV A k z := by
      have h1 : 1 < ‖z‖⁻¹ := one_lt_inv_iff₀.2 ⟨hzpos, hzn⟩
      nlinarith
    linarith
  have e₁ : (weightFiltration Ω Vχ l c).map (g₁ : Module.End K V) =
      (weightFiltration Ω Vχ l c).map (k : Module.End K V) := by
    rw [hk, Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, hB b₁ hb₁ l hl c]
  have e₂ : (weightFiltration Ω Vχ (w m) c) =
      (weightFiltration Ω Vχ m c).map (n w : Module.End K V) :=
    (map_weightFiltration (n w : Module.End K V) w (hWΩ w hw) (hn w hw) m c).symm
  rw [e₁, hlm, e₂, ← Submodule.map_comp, ← Module.End.mul_eq_comp, ← Units.val_mul, hkn,
    Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp,
    hB b₂⁻¹ (inv_mem hb₂) m hm c]

theorem map_weightFiltration_eq_of_frameShift_eq_max (hA : A.Nonempty)
    (hA0 : (0 : Module.End K V) ∉ A) {G B : Subgroup (Module.End K V)ˣ} (hBG : B ≤ G)
    {W : Subgroup (E ≃ₗᵢ[ℝ] E)} (hWΩ : ∀ w ∈ W, Ω.image w = Ω)
    {n : (E ≃ₗᵢ[ℝ] E) → (Module.End K V)ˣ} (hnG : ∀ w ∈ W, n w ∈ G)
    (hn : ∀ w ∈ W, ∀ χ ∈ Ω, (Vχ χ).map (n w : Module.End K V) = Vχ (w χ)) {Dom : Set E}
    (hDom : ∀ x : E, ∃ w ∈ W, ∃ μ ∈ Dom, w μ = x)
    (hB : ∀ b ∈ B, ∀ l ∈ Dom, ∀ c : ℝ,
      (weightFiltration Ω Vχ l c).map (b : Module.End K V) = weightFiltration Ω Vχ l c)
    (hG : (G : Set (Module.End K V)ˣ) =
      ⋃ w ∈ W, (B : Set (Module.End K V)ˣ) * {n w} * (B : Set (Module.End K V)ˣ))
    {M : ℝ} (hMpos : 0 < M) (hM : ∀ g ∈ G, ∀ l : E, ‖l‖ = 1 → frameShift hV A g l ≤ M)
    {g₁ g₂ : (Module.End K V)ˣ} (hg₁ : g₁ ∈ G) (hg₂ : g₂ ∈ G) {l₁ l₂ : E} (hl₁ : ‖l₁‖ = 1)
    (hl₂ : ‖l₂‖ = 1) (h₁ : frameShift hV A g₁ l₁ = M) (h₂ : frameShift hV A g₂ l₂ = M)
    (c : ℝ) :
    (weightFiltration Ω Vχ l₁ c).map (g₁ : Module.End K V) =
      (weightFiltration Ω Vχ l₂ c).map (g₂ : Module.End K V) := by
  have hdom : ∀ {g : (Module.End K V)ˣ} {l : E}, g ∈ G → ‖l‖ = 1 → frameShift hV A g l = M →
      ∃ g' ∈ G, ∃ μ ∈ Dom, ‖μ‖ = 1 ∧ frameShift hV A g' μ = M ∧
        (weightFiltration Ω Vχ l c).map (g : Module.End K V) =
          (weightFiltration Ω Vχ μ c).map (g' : Module.End K V) := by
    intro g l hg hl hgl
    obtain ⟨w, hw, μ, hμ, rfl⟩ := hDom l
    refine ⟨g * n w, mul_mem hg (hnG w hw), μ, hμ, by rwa [LinearIsometryEquiv.norm_map] at hl,
      by rw [frameShift_mul_rep hV hA hA0 g (n w) (hWΩ w hw) (hn w hw), hgl], ?_⟩
    rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp,
      map_weightFiltration (n w : Module.End K V) w (hWΩ w hw) (hn w hw) μ c]
  obtain ⟨g₁', hg₁', μ₁, hμ₁, hμ₁1, h₁', e₁⟩ := hdom hg₁ hl₁ h₁
  obtain ⟨g₂', hg₂', μ₂, hμ₂, hμ₂1, h₂', e₂⟩ := hdom hg₂ hl₂ h₂
  rw [e₁, e₂]
  exact map_weightFiltration_eq_of_dominant hV hA hA0 hBG hWΩ hn hB hG hMpos hM hg₁' hg₂'
    hμ₁ hμ₂ hμ₁1 hμ₂1 h₁' h₂' c

open _root_.Classical in
theorem finite_Bruhat_optimal_weight_filtration (A : Finset (Module.End K V)) (hA : A.Nonempty)
    (hA0 : (0 : Module.End K V) ∉ A) (G : Subgroup (Module.End K V)ˣ) [Finite G]
    (B : Subgroup (Module.End K V)ˣ) (hBG : B ≤ G) (W : Subgroup (E ≃ₗᵢ[ℝ] E))
    (hWΩ : ∀ w ∈ W, Ω.image w = Ω) (n : (E ≃ₗᵢ[ℝ] E) → (Module.End K V)ˣ)
    (hnG : ∀ w ∈ W, n w ∈ G)
    (hn : ∀ w ∈ W, ∀ χ ∈ Ω, (Vχ χ).map (n w : Module.End K V) = Vχ (w χ)) (Dom : Set E)
    (hDom : ∀ x : E, ∃ w ∈ W, ∃ μ ∈ Dom, w μ = x)
    (hB : ∀ b ∈ B, ∀ l ∈ Dom, ∀ c : ℝ,
      (weightFiltration Ω Vχ l c).map (b : Module.End K V) = weightFiltration Ω Vχ l c)
    (hG : (G : Set (Module.End K V)ˣ) =
      ⋃ w ∈ W, (B : Set (Module.End K V)ˣ) * {n w} * (B : Set (Module.End K V)ˣ))
    (h₀ : ∃ g₀ ∈ G, ∃ l₀ : E, l₀ ≠ 0 ∧ 0 < frameShift hV A g₀ l₀) :
    ∃ M : ℝ, 0 < M ∧
      (∃ g ∈ G, ∃ l : E, ‖l‖ = 1 ∧ frameShift hV A g l = M) ∧
      (∀ g ∈ G, ∀ l : E, ‖l‖ = 1 → frameShift hV A g l ≤ M) ∧
      ∃ F : ℝ → Submodule K V,
        (∀ g ∈ G, ∀ l : E, ‖l‖ = 1 → frameShift hV A g l = M → ∀ c : ℝ,
          (weightFiltration Ω Vχ l c).map (g : Module.End K V) = F c) ∧
        (∀ h ∈ G, (A.image fun a => (h : Module.End K V) * a * ↑h⁻¹) = A →
          ∀ c : ℝ, (F c).map (h : Module.End K V) = F c) ∧
        ∀ (σ σ' : K →+* K) [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (s : V ≃ₛₗ[σ] V),
          (∀ g : (Module.End K V)ˣ, semilinearConjUnit s g ∈ G ↔ g ∈ G) →
          ∀ u : E ≃ₗᵢ[ℝ] E, Ω.image u = Ω →
          (∀ χ ∈ Ω, (Vχ χ).map s.toLinearMap = Vχ (u χ)) →
          (A.image (semilinearConj s)).Nonempty ∧
          (0 : Module.End K V) ∉ A.image (semilinearConj s) ∧
          (∃ g ∈ G, ∃ l : E, ‖l‖ = 1 ∧ frameShift hV (A.image (semilinearConj s)) g l = M) ∧
          (∀ g ∈ G, ∀ l : E, ‖l‖ = 1 → frameShift hV (A.image (semilinearConj s)) g l ≤ M) ∧
          ∀ g ∈ G, ∀ l : E, ‖l‖ = 1 → frameShift hV (A.image (semilinearConj s)) g l = M →
            ∀ c : ℝ, (weightFiltration Ω Vχ l c).map (g : Module.End K V) =
              (F c).map s.toLinearMap := by
  obtain ⟨g₀, hg₀, l₀, hl₀, hpos⟩ := h₀
  have hl₀n : 0 < ‖l₀‖ := norm_pos_iff.2 hl₀
  have hS : (Metric.sphere (0 : E) 1).Nonempty :=
    ⟨‖l₀‖⁻¹ • l₀, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hl₀n.ne']⟩
  obtain ⟨g₁, hg₁, l₁, hl₁, hmax⟩ :=
    exists_frameShift_max hV hA hA0 G (isCompact_sphere (0 : E) 1) hS
  rw [mem_sphere_zero_iff_norm] at hl₁
  set M := frameShift hV A g₁ l₁ with hMdef
  have hM : ∀ g ∈ G, ∀ l : E, ‖l‖ = 1 → frameShift hV A g l ≤ M := fun g hg l hl =>
    hmax g hg l (mem_sphere_zero_iff_norm.2 hl)
  have hMpos : 0 < M := by
    have h1 := hM g₀ hg₀ (‖l₀‖⁻¹ • l₀) (by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hl₀n.ne'])
    rw [frameShift_smul hV hA hA0 g₀ (inv_nonneg.2 hl₀n.le)] at h1
    have h2 : 0 < ‖l₀‖⁻¹ * frameShift hV A g₀ l₀ := mul_pos (inv_pos.2 hl₀n) hpos
    linarith
  set F : ℝ → Submodule K V := fun c => (weightFiltration Ω Vχ l₁ c).map (g₁ : Module.End K V)
    with hF
  have huniq : ∀ g ∈ G, ∀ l : E, ‖l‖ = 1 → frameShift hV A g l = M → ∀ c : ℝ,
      (weightFiltration Ω Vχ l c).map (g : Module.End K V) = F c := fun g hg l hl hgl c =>
    map_weightFiltration_eq_of_frameShift_eq_max hV hA hA0 hBG hWΩ hnG hn hDom hB hG hMpos hM hg
      hg₁ hl hl₁ hgl rfl c
  refine ⟨M, hMpos, ⟨g₁, hg₁, l₁, hl₁, rfl⟩, hM, F, huniq, fun h hh hhA c => ?_,
    fun σ σ' _ _ s hsG u hu hs => ?_⟩
  ·
    have hhg : frameShift hV A (h * g₁) l₁ = M := by
      rw [frameShift, conjFamily_mul, conjFamily_eq_of_image_eq hhA]
      exact hMdef.symm
    have := huniq (h * g₁) (mul_mem hh hg₁) l₁ hl₁ hhg c
    rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp] at this
    exact this
  ·
    set A' := A.image (semilinearConj s) with hA'
    have hA'ne : A'.Nonempty := hA.image _
    have hA'0 : (0 : Module.End K V) ∉ A' := fun h0 => by
      obtain ⟨a, ha, h⟩ := Finset.mem_image.1 h0
      have : a = 0 := LinearMap.ext fun x => by
        have hx := LinearMap.congr_fun h (s x)
        rw [semilinearConj_apply, LinearEquiv.symm_apply_apply, LinearMap.zero_apply] at hx
        rw [LinearMap.zero_apply]
        exact s.map_eq_zero_iff.1 hx
      exact hA0 (this ▸ ha)
    have hpre : ∀ g : (Module.End K V)ˣ, ∀ l : E,
        frameShift hV A' g l = frameShift hV A (semilinearConjUnit s.symm g) (u.symm l) := by
      intro g l
      have := frameShift_semilinearConj hV hA hA0 s hu hs (semilinearConjUnit s.symm g) (u.symm l)
      rwa [semilinearConjUnit_symm_semilinearConjUnit, LinearIsometryEquiv.apply_symm_apply]
        at this
    have hmemG : ∀ g ∈ G, semilinearConjUnit s.symm g ∈ G := fun g hg => by
      rw [← hsG, semilinearConjUnit_symm_semilinearConjUnit]
      exact hg
    have hnorm : ∀ l : E, ‖u.symm l‖ = ‖l‖ := fun l => LinearIsometryEquiv.norm_map _ l
    refine ⟨hA'ne, hA'0, ⟨semilinearConjUnit s g₁, (hsG g₁).2 hg₁, u l₁,
      by rw [LinearIsometryEquiv.norm_map, hl₁],
      frameShift_semilinearConj hV hA hA0 s hu hs g₁ l₁⟩,
      fun g hg l hl => ?_, fun g hg l hl hgl c => ?_⟩
    · rw [hpre]
      exact hM _ (hmemG g hg) _ (by rw [hnorm, hl])
    · rw [hpre] at hgl
      have h1 := huniq _ (hmemG g hg) _ (by rw [hnorm, hl]) hgl c
      have hinv : (weightFiltration Ω Vχ l c).map s.symm.toLinearMap =
          weightFiltration Ω Vχ (u.symm l) c := by
        conv_lhs => rw [← LinearIsometryEquiv.apply_symm_apply u l,
          ← map_weightFiltration s.toLinearMap u hu hs (u.symm l) c]
        rw [← Submodule.map_comp]
        simp only [LinearEquiv.symm_comp, Submodule.map_id]
      calc (weightFiltration Ω Vχ l c).map (g : Module.End K V) =
            (weightFiltration Ω Vχ l c).map
              (semilinearConjUnit s (semilinearConjUnit s.symm g) : Module.End K V) := by
            rw [semilinearConjUnit_symm_semilinearConjUnit]
        _ = (((weightFiltration Ω Vχ l c).map s.symm.toLinearMap).map
              (semilinearConjUnit s.symm g : Module.End K V)).map s.toLinearMap := by
            rw [coe_semilinearConjUnit, semilinearConj, Submodule.map_comp, Submodule.map_comp]
        _ = (F c).map s.toLinearMap := by rw [hinv, h1]

end CFSG.LieType.Chevalley.RootWeight
