module

public import CFSG.LieType.SeitzGeneration.OmegaF2.Sigma
public import CFSG.LieType.SeitzGeneration.OmegaF2.TransitB

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.LieType.SeitzGeneration.RootPairOrth

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {k : Subfield K}
  {Q₀ : QuadraticForm k (Fin d → k)} (S : HypCoord Q)

private theorem cb_eq_zero_of_polar_single (hnd : (polarBilin Q).Nondegenerate) {w : Fin d → K}
    (h : ∀ j : Fin d, polar Q w (Pi.single j 1) = 0) : w = 0 :=
  hnd.1 w fun n => by
    show polar Q w n = 0
    rw [polar_expand_right]
    exact Finset.sum_eq_zero fun c _ => by rw [h c, mul_zero]

private theorem cb_polar_sub_smul_left (u p z : Fin d → K) (α : K) :
    polar Q (u - α • p) z = polar Q u z - α * polar Q p z := by
  rw [sub_eq_add_neg, polar_add_left, polar_neg_left, polar_smul_left_eq, sub_eq_add_neg]

private theorem cb_isRat_smul {α : K} {p : Fin d → K} (hα : α ∈ k) (hp : IsRat k p) :
    IsRat k (α • p) := by
  intro i
  rw [Pi.smul_apply, smul_eq_mul]
  exact k.mul_mem hα (hp i)

private theorem cb_isRat_add {p q : Fin d → K} (hp : IsRat k p) (hq : IsRat k q) :
    IsRat k (p + q) := by
  intro i
  rw [Pi.add_apply]
  exact k.add_mem (hp i) (hq i)

private theorem cb_exists_minor_ne (hnd : (polarBilin Q).Nondegenerate) {x y : Fin d → K}
    (hind : LinearIndependent K ![x, y]) :
    ∃ i j : Fin d, polar Q x (Pi.single i 1) * polar Q y (Pi.single j 1) -
      polar Q x (Pi.single j 1) * polar Q y (Pi.single i 1) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hx0 : x ≠ 0 := hind.ne_zero 0
  obtain ⟨i, hi⟩ : ∃ i : Fin d, polar Q x (Pi.single i 1) ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (cb_eq_zero_of_polar_single hnd h)
  obtain ⟨c, hc⟩ : ∃ c : K, c * polar Q x (Pi.single i 1) = polar Q y (Pi.single i 1) :=
    ⟨polar Q y (Pi.single i 1) / polar Q x (Pi.single i 1), div_mul_cancel₀ _ hi⟩
  have hy : y - c • x = 0 := by
    refine cb_eq_zero_of_polar_single hnd fun j => ?_
    rw [cb_polar_sub_smul_left]
    have h2 : polar Q x (Pi.single i 1) *
        (polar Q y (Pi.single j 1) - c * polar Q x (Pi.single j 1)) = 0 := by
      linear_combination hcon i j - polar Q x (Pi.single j 1) * hc
    exact (mul_eq_zero.mp h2).resolve_left hi
  have hsum := (LinearIndependent.pair_iff.mp hind) c (-1) (by
    have e : c • x + (-1 : K) • y = -(y - c • x) := by module
    rw [e, hy, neg_zero])
  exact one_ne_zero (neg_eq_zero.mp hsum.2)

private theorem cb_exists_coeffs_two {a₁ a₂ b₁ b₂ : K} (ha₁ : a₁ ∈ k) (ha₂ : a₂ ∈ k)
    (hb₁ : b₁ ∈ k) (hb₂ : b₂ ∈ k) (hD : a₁ * b₂ - a₂ * b₁ ≠ 0) :
    ∃ α β γ δ : K, α ∈ k ∧ β ∈ k ∧ γ ∈ k ∧ δ ∈ k ∧ α * a₁ + β * a₂ = 1 ∧
      α * b₁ + β * b₂ = 0 ∧ γ * a₁ + δ * a₂ = 0 ∧ γ * b₁ + δ * b₂ = 1 := by
  have hDk : a₁ * b₂ - a₂ * b₁ ∈ k := k.sub_mem (k.mul_mem ha₁ hb₂) (k.mul_mem ha₂ hb₁)
  have hinv : (a₁ * b₂ - a₂ * b₁)⁻¹ ∈ k := k.inv_mem hDk
  have hm : (a₁ * b₂ - a₂ * b₁) * (a₁ * b₂ - a₂ * b₁)⁻¹ = 1 := mul_inv_cancel₀ hD
  refine ⟨b₂ * (a₁ * b₂ - a₂ * b₁)⁻¹, -(b₁ * (a₁ * b₂ - a₂ * b₁)⁻¹),
    -(a₂ * (a₁ * b₂ - a₂ * b₁)⁻¹), a₁ * (a₁ * b₂ - a₂ * b₁)⁻¹,
    k.mul_mem hb₂ hinv, k.neg_mem (k.mul_mem hb₁ hinv), k.neg_mem (k.mul_mem ha₂ hinv),
    k.mul_mem ha₁ hinv, ?_, ?_, ?_, ?_⟩
  · linear_combination hm
  · ring
  · ring
  · linear_combination hm

private theorem cb_exists_dual_pair (hext : IsExtension k Q₀ Q)
    (hnd : (polarBilin Q).Nondegenerate) {x y : Fin d → K} (hx : IsRat k x) (hy : IsRat k y)
    (hind : LinearIndependent K ![x, y]) :
    ∃ x' y' : Fin d → K, IsRat k x' ∧ IsRat k y' ∧ polar Q x x' = 1 ∧ polar Q y x' = 0 ∧
      polar Q x y' = 0 ∧ polar Q y y' = 1 := by
  obtain ⟨i, j, hD⟩ := cb_exists_minor_ne hnd hind
  have ha : ∀ l : Fin d, polar Q x (Pi.single l 1) ∈ k := fun l =>
    polar_isRat_mem hext hx (isRat_single k l)
  have hb : ∀ l : Fin d, polar Q y (Pi.single l 1) ∈ k := fun l =>
    polar_isRat_mem hext hy (isRat_single k l)
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, e1, e2, e3, e4⟩ :=
    cb_exists_coeffs_two (ha i) (ha j) (hb i) (hb j) hD
  refine ⟨α • Pi.single i 1 + β • Pi.single j 1, γ • Pi.single i 1 + δ • Pi.single j 1,
    (cb_isRat_smul hα (isRat_single k i)).add (cb_isRat_smul hβ (isRat_single k j)),
    (cb_isRat_smul hγ (isRat_single k i)).add (cb_isRat_smul hδ (isRat_single k j)),
    ?_, ?_, ?_, ?_⟩
  · rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq]; exact e1
  · rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq]; exact e2
  · rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq]; exact e3
  · rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq]; exact e4

theorem perp_mem_span_rational (hext : IsExtension k Q₀ Q) (hnd : (polarBilin Q).Nondegenerate)
    {x y : Fin d → K} (hx : IsRat k x) (hy : IsRat k y) (hind : LinearIndependent K ![x, y])
    {v : Fin d → K} (hvx : polar Q v x = 0) (hvy : polar Q v y = 0) :
    v ∈ Submodule.span K {z : Fin d → K | IsRat k z ∧ polar Q z x = 0 ∧ polar Q z y = 0} := by
  obtain ⟨x', y', hx', hy', h1, h2, h3, h4⟩ := cb_exists_dual_pair hext hnd hx hy hind
  have h1' : polar Q x' x = 1 := by rw [polar_comm]; exact h1
  have h2' : polar Q x' y = 0 := by rw [polar_comm]; exact h2
  have h3' : polar Q y' x = 0 := by rw [polar_comm]; exact h3
  have h4' : polar Q y' y = 1 := by rw [polar_comm]; exact h4
  have hfZ : ∀ c : Fin d, (Pi.single c 1 - polar Q (Pi.single c 1) x • x' -
      polar Q (Pi.single c 1) y • y' : Fin d → K) ∈
      {z : Fin d → K | IsRat k z ∧ polar Q z x = 0 ∧ polar Q z y = 0} := by
    intro c
    refine ⟨((isRat_single k c).sub
      (cb_isRat_smul (polar_isRat_mem hext (isRat_single k c) hx) hx')).sub
      (cb_isRat_smul (polar_isRat_mem hext (isRat_single k c) hy) hy'), ?_, ?_⟩
    · rw [cb_polar_sub_smul_left, cb_polar_sub_smul_left, h1', h3']; ring
    · rw [cb_polar_sub_smul_left, cb_polar_sub_smul_left, h2', h4']; ring
  have hsumA : ∑ c, v c * polar Q (Pi.single c 1) x = 0 :=
    (polar_expand_left v x).symm.trans hvx
  have hsumB : ∑ c, v c * polar Q (Pi.single c 1) y = 0 :=
    (polar_expand_left v y).symm.trans hvy
  have hvdec : v = ∑ c, v c • (Pi.single c 1 : Fin d → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hsum : v = ∑ c, v c • (Pi.single c 1 - polar Q (Pi.single c 1) x • x' -
      polar Q (Pi.single c 1) y • y') := by
    have key : ∑ c, v c • (Pi.single c 1 - polar Q (Pi.single c 1) x • x' -
        polar Q (Pi.single c 1) y • y') = (∑ c, v c • (Pi.single c 1 : Fin d → K)) -
        (∑ c, v c * polar Q (Pi.single c 1) x) • x' -
        (∑ c, v c * polar Q (Pi.single c 1) y) • y' := by
      simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.sum_smul]
    rw [key, ← hvdec, hsumA, hsumB, zero_smul, zero_smul, sub_zero, sub_zero]
  rw [hsum]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span (hfZ c))

private theorem cb_adjust_of_singular {c₁ c₂ : Fin d → K} (hbad : BadPlane Q k c₁ c₂)
    {x y z : Fin d → K} (hx : IsRat k x) (hy : IsRat k y) (hzR : IsRat k z) (hQx : Q x = 0)
    (hQy : Q y = 0) (hQz : Q z = 0) (hxy : polar Q x y = 0) (hzx : polar Q z x = 0)
    (hzy : polar Q z y = 0) (hΔ : pairDet Q c₁ c₂ x y ≠ 0) :
    ∃ a b : K, a ∈ k ∧ b ∈ k ∧ polar Q (z + a • x + b • y) c₁ = 0 ∧
      polar Q (z + a • x + b • y) c₂ = 0 := by
  obtain ⟨ha, hb⟩ := hbad x y z hx hy hzR hQx hQy hQz hxy (by rw [polar_comm]; exact hzx)
    (by rw [polar_comm]; exact hzy) hΔ
  obtain ⟨h1, h2⟩ := polar_radical_vector (x := x) (y := y) (z := z) (c₁ := c₁) (c₂ := c₂) hΔ
  exact ⟨_, _, ha, hb, h1, h2⟩

theorem exists_adjust (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q) (htail : TailAnisotropic S)
    {c₁ c₂ : Fin d → K} (hbad : BadPlane Q k c₁ c₂) {x y : Fin d → K} (hx : IsRat k x)
    (hy : IsRat k y) (hQx : Q x = 0) (hQy : Q y = 0) (hxy : polar Q x y = 0)
    (hΔ : pairDet Q c₁ c₂ x y ≠ 0) {v : Fin d → K} (hv : IsRat k v) (hvx : polar Q v x = 0)
    (hvy : polar Q v y = 0) :
    ∃ a b : K, a ∈ k ∧ b ∈ k ∧ polar Q (v + a • x + b • y) c₁ = 0 ∧
      polar Q (v + a • x + b • y) c₂ = 0 := by
  obtain ⟨hind, -⟩ := linearIndependent_of_pairDet_ne hΔ
  have hcl := rational_perp_mem_closure S hk hext htail hx hy hQx hQy hxy hind hv hvx hvy
  clear hv hvx hvy
  induction hcl using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨hzR, hQz, hzx, hzy⟩ := hz
    exact cb_adjust_of_singular hbad hx hy hzR hQx hQy hQz hxy hzx hzy hΔ
  | zero =>
    refine ⟨0, 0, k.zero_mem, k.zero_mem, ?_, ?_⟩ <;>
      simp only [zero_smul, add_zero] <;> exact polar_zero_left _ _
  | add u w hu hw ihu ihw =>
    obtain ⟨a, b, ha, hb, h1, h2⟩ := ihu
    obtain ⟨a', b', ha', hb', h1', h2'⟩ := ihw
    refine ⟨a + a', b + b', k.add_mem ha ha', k.add_mem hb hb', ?_, ?_⟩
    · have e : u + w + (a + a') • x + (b + b') • y =
          (u + a • x + b • y) + (w + a' • x + b' • y) := by module
      rw [e, polar_add_left, h1, h1', add_zero]
    · have e : u + w + (a + a') • x + (b + b') • y =
          (u + a • x + b • y) + (w + a' • x + b' • y) := by module
      rw [e, polar_add_left, h2, h2', add_zero]
  | neg u hu ihu =>
    obtain ⟨a, b, ha, hb, h1, h2⟩ := ihu
    refine ⟨-a, -b, k.neg_mem ha, k.neg_mem hb, ?_, ?_⟩
    · have e : -u + (-a) • x + (-b) • y = -(u + a • x + b • y) := by module
      rw [e, polar_neg_left, h1, neg_zero]
    · have e : -u + (-a) • x + (-b) • y = -(u + a • x + b • y) := by module
      rw [e, polar_neg_left, h2, neg_zero]

theorem mem_span_of_perp_perp (hnd : (polarBilin Q).Nondegenerate) {x y c₁ c₂ : Fin d → K}
    (hx : Q x = 0) (hy : Q y = 0) (hxy : polar Q x y = 0) (hc₁ : Q c₁ = 0) (hc₂ : Q c₂ = 0)
    (hc₁₂ : polar Q c₁ c₂ = 0) (hΔ : pairDet Q c₁ c₂ x y ≠ 0) {v : Fin d → K}
    (hv : ∀ w : Fin d → K, polar Q w x = 0 → polar Q w y = 0 → polar Q w c₁ = 0 →
      polar Q w c₂ = 0 → polar Q v w = 0) :
    v ∈ Submodule.span K {x, y, c₁, c₂} := by
  have hrefl : (polarBilin Q).IsRefl := fun a b h => by
    rw [polarBilin_apply_apply] at h ⊢
    rw [polar_comm]
    exact h
  have hgen : ∀ w : Fin d → K,
      w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q)
        (Submodule.span K ({x, y, c₁, c₂} : Set (Fin d → K))) →
      polar Q x w = 0 ∧ polar Q y w = 0 ∧ polar Q c₁ w = 0 ∧ polar Q c₂ w = 0 := by
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw
    exact ⟨hw x (Submodule.subset_span (by simp)), hw y (Submodule.subset_span (by simp)),
      hw c₁ (Submodule.subset_span (by simp)), hw c₂ (Submodule.subset_span (by simp))⟩
  have hdd : v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q)
      (LinearMap.BilinForm.orthogonal (polarBilin Q)
        (Submodule.span K ({x, y, c₁, c₂} : Set (Fin d → K)))) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hgen w hw
    rw [polarBilin_apply_apply, polar_comm]
    exact hv w (by rw [polar_comm]; exact h1) (by rw [polar_comm]; exact h2)
      (by rw [polar_comm]; exact h3) (by rw [polar_comm]; exact h4)
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl
    (Submodule.span K ({x, y, c₁, c₂} : Set (Fin d → K)))]
  exact hdd

theorem perp_mem_span_R (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q)
    (hnd : (polarBilin Q).Nondegenerate) (htail : TailAnisotropic S) {c₁ c₂ : Fin d → K}
    (hbad : BadPlane Q k c₁ c₂) {x y : Fin d → K} (hx : IsRat k x) (hy : IsRat k y)
    (hQx : Q x = 0) (hQy : Q y = 0) (hxy : polar Q x y = 0) (hΔ : pairDet Q c₁ c₂ x y ≠ 0)
    {v : Fin d → K} (hvx : polar Q v x = 0) (hvy : polar Q v y = 0) (hv₁ : polar Q v c₁ = 0)
    (hv₂ : polar Q v c₂ = 0) :
    v ∈ Submodule.span K {r : Fin d → K | IsRat k r ∧ polar Q r x = 0 ∧ polar Q r y = 0 ∧
      polar Q r c₁ = 0 ∧ polar Q r c₂ = 0} := by
  obtain ⟨hind, -⟩ := linearIndependent_of_pairDet_ne hΔ
  have hgen : ∀ u ∈ Submodule.span K {z : Fin d → K | IsRat k z ∧ polar Q z x = 0 ∧
      polar Q z y = 0},
      ∃ (r : Fin d → K) (A B : K), r ∈ Submodule.span K {r : Fin d → K | IsRat k r ∧
        polar Q r x = 0 ∧ polar Q r y = 0 ∧ polar Q r c₁ = 0 ∧ polar Q r c₂ = 0} ∧
        u = r + A • x + B • y ∧ polar Q r c₁ = 0 ∧ polar Q r c₂ = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨hur, hux, huy⟩ := hu
      obtain ⟨a, b, ha, hb, ha1, ha2⟩ :=
        exists_adjust S hk hext htail hbad hx hy hQx hQy hxy hΔ hur hux huy
      have hr : IsRat k (u + a • x + b • y) :=
        cb_isRat_add (cb_isRat_add hur (cb_isRat_smul ha hx)) (cb_isRat_smul hb hy)
      have hxx : polar Q x x = 0 := by rw [polar_self, hQx, smul_zero]
      have hyy : polar Q y y = 0 := by rw [polar_self, hQy, smul_zero]
      have hyx : polar Q y x = 0 := by rw [polar_comm]; exact hxy
      have hrx : polar Q (u + a • x + b • y) x = 0 := by
        simp only [polar_add_left, polar_smul_left_eq, hux, hxx, hyx, mul_zero, zero_add,
          add_zero]
      have hry : polar Q (u + a • x + b • y) y = 0 := by
        simp only [polar_add_left, polar_smul_left_eq, huy, hxy, hyy, mul_zero, zero_add,
          add_zero]
      exact ⟨u + a • x + b • y, -a, -b, Submodule.subset_span ⟨hr, hrx, hry, ha1, ha2⟩,
        by module, ha1, ha2⟩
    | zero =>
      exact ⟨0, 0, 0, Submodule.zero_mem _, by simp, polar_zero_left _ _, polar_zero_left _ _⟩
    | add u v _ _ hu hvv =>
      obtain ⟨r₁, A₁, B₁, hr₁, hu', hu1, hu2⟩ := hu
      obtain ⟨r₂, A₂, B₂, hr₂, hv', hv1, hv2⟩ := hvv
      refine ⟨r₁ + r₂, A₁ + A₂, B₁ + B₂, Submodule.add_mem _ hr₁ hr₂, ?_, ?_, ?_⟩
      · rw [hu', hv']
        module
      · rw [polar_add_left, hu1, hv1, add_zero]
      · rw [polar_add_left, hu2, hv2, add_zero]
    | smul a u _ hu =>
      obtain ⟨r, A, B, hr, hu', hc1, hc2⟩ := hu
      refine ⟨a • r, a * A, a * B, Submodule.smul_mem _ _ hr, ?_, ?_, ?_⟩
      · rw [hu']
        module
      · rw [polar_smul_left_eq, hc1, mul_zero]
      · rw [polar_smul_left_eq, hc2, mul_zero]
  have hv' : v ∈ Submodule.span K {z : Fin d → K | IsRat k z ∧ polar Q z x = 0 ∧
      polar Q z y = 0} :=
    perp_mem_span_rational hext hnd hx hy hind hvx hvy
  obtain ⟨r, A, B, hr, hvrAB, hr1, hr2⟩ := hgen v hv'
  have e1 : A * polar Q x c₁ + B * polar Q y c₁ = 0 := by
    have h := hv₁
    rw [hvrAB, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hr1,
      zero_add] at h
    exact h
  have e2 : A * polar Q x c₂ + B * polar Q y c₂ = 0 := by
    have h := hv₂
    rw [hvrAB, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hr2,
      zero_add] at h
    exact h
  have hA : A * pairDet Q c₁ c₂ x y = 0 := by
    unfold pairDet
    linear_combination (polar Q y c₂) * e1 - (polar Q y c₁) * e2
  have hB : B * pairDet Q c₁ c₂ x y = 0 := by
    unfold pairDet
    linear_combination (polar Q x c₁) * e2 - (polar Q x c₂) * e1
  have hA0 : A = 0 := (mul_eq_zero.mp hA).resolve_right hΔ
  have hB0 : B = 0 := (mul_eq_zero.mp hB).resolve_right hΔ
  rw [hvrAB, hA0, hB0, zero_smul, zero_smul, add_zero, add_zero]
  exact hr

theorem sigmaVec_mem_span_of_bad (hk : Nat.card k = 2) (hext : IsExtension k Q₀ Q)
    (hnd : (polarBilin Q).Nondegenerate) (htail : TailAnisotropic S) {σ : K ≃+* K}
    (hσk : ∀ x, x ∈ k ↔ σ x = x) {c₁ c₂ : Fin d → K} (hc₁ : Q c₁ = 0) (hc₂ : Q c₂ = 0)
    (hc₁₂ : polar Q c₁ c₂ = 0) (hbad : BadPlane Q k c₁ c₂) {x y : Fin d → K} (hx : IsRat k x)
    (hy : IsRat k y) (hQx : Q x = 0) (hQy : Q y = 0) (hxy : polar Q x y = 0)
    (hΔ : pairDet Q c₁ c₂ x y ≠ 0) :
    sigmaVec σ c₁ ∈ Submodule.span K {x, y, c₁, c₂} ∧
      sigmaVec σ c₂ ∈ Submodule.span K {x, y, c₁, c₂} := by
  have hmain : ∀ c : Fin d → K, (∀ r : Fin d → K, IsRat k r → polar Q r x = 0 →
      polar Q r y = 0 → polar Q r c₁ = 0 → polar Q r c₂ = 0 → polar Q c r = 0) →
      sigmaVec σ c ∈ Submodule.span K {x, y, c₁, c₂} := by
    intro c hcr
    refine mem_span_of_perp_perp hnd hQx hQy hxy hc₁ hc₂ hc₁₂ hΔ ?_
    intro w hw1 hw2 hw3 hw4
    have hwR := perp_mem_span_R S hk hext hnd htail hbad hx hy hQx hQy hxy hΔ hw1 hw2 hw3 hw4
    clear hw1 hw2 hw3 hw4
    induction hwR using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨hrR, hrx, hry, hr1, hr2⟩ := hr
      have hs := polar_sigmaVec hext hσk c r
      rw [sigmaVec_isRat hσk hrR] at hs
      rw [hs, hcr r hrR hrx hry hr1 hr2, map_zero]
    | zero => exact polar_zero_right _ _
    | add a b _ _ ha hb => rw [polar_add_right, ha, hb, add_zero]
    | smul a r _ hr => rw [polar_smul_right_eq, hr, mul_zero]
  exact ⟨hmain c₁ fun r _ _ _ hr1 _ => by rw [polar_comm]; exact hr1,
    hmain c₂ fun r _ _ _ _ hr2 => by rw [polar_comm]; exact hr2⟩

end CFSG.LieType.SeitzGeneration.OmegaF2
