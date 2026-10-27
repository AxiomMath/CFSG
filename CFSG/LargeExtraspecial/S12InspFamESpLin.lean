module

public import CFSG.LargeExtraspecial.S12InspFamESpBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S12InspSp

open CFSG.Open LinearMap.BilinForm

section Proj

variable {ι : Type} {b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)}

variable (b) in
@[expose] def pr (v y x : ι → ZMod 2) : ι → ZMod 2 := x + b x y • v + b x v • y

variable {v y : ι → ZMod 2}

theorem pr_add (x z : ι → ZMod 2) : pr b v y (x + z) = pr b v y x + pr b v y z := by
  simp only [pr, add_left, add_smul]
  abel

theorem pr_smul (c : ZMod 2) (x : ι → ZMod 2) : pr b v y (c • x) = c • pr b v y x := by
  simp only [pr, smul_left, smul_add, smul_smul]

theorem pr_zero : pr b v y 0 = 0 := by
  simp [pr]

theorem pr_of_perp {x : ι → ZMod 2} (hxv : b x v = 0) (hxy : b x y = 0) : pr b v y x = x := by
  rw [pr, hxv, hxy, zero_smul, zero_smul, add_zero, add_zero]

theorem eq_pr_add {x : ι → ZMod 2} (hxv : b x v = 0) : x = pr b v y x + b x y • v := by
  rw [pr, hxv, zero_smul, add_zero, add_assoc, add_self_vec, add_zero]

theorem b_pr_right {w : ι → ZMod 2} (hwv : b w v = 0) (hwy : b w y = 0) (x : ι → ZMod 2) :
    b w (pr b v y x) = b w x := by
  rw [pr, add_right, add_right, smul_right, smul_right, hwv, hwy, mul_zero, mul_zero, add_zero,
    add_zero]

variable (halt : ∀ x, b x x = 0) (hyv : b y v = 1)
include halt hyv

theorem b_pr_v (x : ι → ZMod 2) : b (pr b v y x) v = 0 := by
  rw [pr, add_left, add_left, smul_left, smul_left, halt v, hyv, mul_zero, mul_one, add_zero,
    add_self_zmod2]

theorem b_pr_y (x : ι → ZMod 2) : b (pr b v y x) y = 0 := by
  rw [pr, add_left, add_left, smul_left, smul_left, b_symm halt v y, hyv, halt y, mul_one,
    mul_zero, add_zero, add_self_zmod2]

theorem pr_v : pr b v y v = 0 := by
  rw [pr, b_symm halt v y, hyv, halt v, one_smul, zero_smul, add_zero, add_self_vec]

end Proj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)}
  {v y : ι → ZMod 2}

theorem pr_act_add_smul (halt : ∀ x, b x x = 0) (hyv : b y v = 1) {c : SpG b}
    (hcv : act c v = v) (x : ι → ZMod 2) (s : ZMod 2) :
    pr b v y (act c (x + s • v)) = pr b v y (act c x) := by
  rw [act_add, act_smul, hcv, pr_add, pr_smul, pr_v halt hyv, smul_zero, add_zero]

variable (b) in
@[expose] noncomputable def res (v y : ι → ZMod 2) (c : SpG b) (w : ι → ZMod 2) :
    ι → ZMod 2 :=
  pr b v y (act c w)

theorem res_add (c : SpG b) (x z : ι → ZMod 2) :
    res b v y c (x + z) = res b v y c x + res b v y c z := by
  rw [res, res, res, act_add, pr_add]

theorem res_one {w : ι → ZMod 2} (hwv : b w v = 0) (hwy : b w y = 0) : res b v y 1 w = w := by
  rw [res, act_one, pr_of_perp hwv hwy]

theorem b_res_v (halt : ∀ x, b x x = 0) (hyv : b y v = 1) (c : SpG b) (w : ι → ZMod 2) :
    b (res b v y c w) v = 0 :=
  b_pr_v halt hyv _

theorem b_res_y (halt : ∀ x, b x x = 0) (hyv : b y v = 1) (c : SpG b) (w : ι → ZMod 2) :
    b (res b v y c w) y = 0 :=
  b_pr_y halt hyv _

theorem res_mul (halt : ∀ x, b x x = 0) (hyv : b y v = 1) {c d : SpG b} (hcv : act c v = v)
    (hdv : act d v = v) {w : ι → ZMod 2} (hwv : b w v = 0) :
    res b v y (c * d) w = res b v y c (res b v y d w) := by
  have h1 : b (act d w) v = 0 := by rw [b_act_left hdv, hwv]
  have h2 := pr_act_add_smul halt hyv hcv (pr b v y (act d w)) (b (act d w) y)
  rw [← eq_pr_add h1] at h2
  rw [res, res, res, act_mul]
  exact h2

theorem mem_rad_of_res (halt : ∀ x, b x x = 0) (hyv : b y v = 1) {c : SpG b}
    (hcv : act c v = v) (hres : ∀ w, b w v = 0 → b w y = 0 → res b v y c w = w) :
    c ∈ rad b v := by
  refine mem_rad.2 ⟨hcv, fun x hx => ⟨b (act c (pr b v y x)) y, ?_⟩⟩
  have h1 : b (act c (pr b v y x)) v = 0 := by rw [b_act_left hcv, b_pr_v halt hyv]
  have h2 := eq_pr_add (y := y) h1
  have h3 : pr b v y (act c (pr b v y x)) = pr b v y x :=
    hres _ (b_pr_v halt hyv x) (b_pr_y halt hyv x)
  rw [h3] at h2
  have hx' := eq_pr_add (y := y) hx
  have hpx : pr b v y x = x + b x y • v := by
    rw [pr, hx, zero_smul, add_zero]
  calc act c x = act c (pr b v y x + b x y • v) := by rw [← hx']
    _ = act c (pr b v y x) + b x y • v := by rw [act_add, act_smul, hcv]
    _ = pr b v y x + b (act c (pr b v y x)) y • v + b x y • v := by rw [← h2]
    _ = x + b (act c (pr b v y x)) y • v + (b x y • v + b x y • v) := by rw [hpx]; abel
    _ = x + b (act c (pr b v y x)) y • v := by rw [add_self_vec, add_zero]

variable (b) in
@[expose] noncomputable def uvec (y : ι → ZMod 2) (k : SpG b) : ι → ZMod 2 := act k y + y

theorem act_y_eq (k : SpG b) : act k y = y + uvec b y k := by
  rw [uvec, add_comm, add_assoc, add_self_vec, add_zero]

theorem b_uvec_v {k : SpG b} (hkv : act k v = v) : b (uvec b y k) v = 0 := by
  rw [uvec, add_left, b_act_left hkv, add_self_zmod2]

theorem act_eq_of_mem_rad (halt : ∀ x, b x x = 0) (hyv : b y v = 1) {k : SpG b}
    (hk : k ∈ rad b v) {x : ι → ZMod 2} (hx : b x v = 0) :
    act k x = x + b x (uvec b y k) • v := by
  obtain ⟨c, hc⟩ := (mem_rad.1 hk).2 x hx
  have e := b_act_act k x y
  have hvu : b v (uvec b y k) = 0 := by rw [b_symm halt, b_uvec_v (mem_rad.1 hk).1]
  rw [hc, act_y_eq] at e
  simp only [add_left, add_right, smul_left] at e
  rw [b_symm halt v y, hyv, hvu] at e
  have e' : b x (uvec b y k) + c = 0 := by linear_combination e
  rw [hc, ← eq_of_add_eq_zero_zmod2 e']

variable (b) in
@[expose] noncomputable def piv (v y : ι → ZMod 2) (k : SpG b) : ι → ZMod 2 :=
  pr b v y (uvec b y k)

theorem b_piv_v (halt : ∀ x, b x x = 0) (hyv : b y v = 1) (k : SpG b) :
    b (piv b v y k) v = 0 :=
  b_pr_v halt hyv _

theorem b_piv_y (halt : ∀ x, b x x = 0) (hyv : b y v = 1) (k : SpG b) :
    b (piv b v y k) y = 0 :=
  b_pr_y halt hyv _

theorem piv_one : piv b v y 1 = 0 := by
  rw [piv, uvec, act_one, add_self_vec, pr_zero]

theorem piv_mul (halt : ∀ x, b x x = 0) (hyv : b y v = 1) {k k' : SpG b} (hk : k ∈ rad b v)
    (hk' : k' ∈ rad b v) : piv b v y (k * k') = piv b v y k + piv b v y k' := by
  have hu' : b (uvec b y k') v = 0 := b_uvec_v (mem_rad.1 hk').1
  have e : uvec b y (k * k') =
      uvec b y k + uvec b y k' + b (uvec b y k') (uvec b y k) • v := by
    rw [uvec, act_mul, act_y_eq (k := k'), act_add, act_eq_of_mem_rad halt hyv hk hu',
      act_y_eq (k := k)]
    calc y + uvec b y k + (uvec b y k' + b (uvec b y k') (uvec b y k) • v) + y =
        (y + y) + (uvec b y k + uvec b y k' + b (uvec b y k') (uvec b y k) • v) := by abel
      _ = _ := by rw [add_self_vec, zero_add]
  rw [piv, e, pr_add, pr_add, pr_smul, pr_v halt hyv, smul_zero, add_zero]
  rfl

theorem eq_one_or_eq_of_piv (halt : ∀ x, b x x = 0) (hyv : b y v = 1) {T : SpG b}
    (hT : ∀ x, act T x = x + b x v • v) {k : SpG b} (hk : k ∈ rad b v)
    (h0 : piv b v y k = 0) : k = 1 ∨ k = T := by
  have hu : b (uvec b y k) v = 0 := b_uvec_v (mem_rad.1 hk).1
  have hu' : uvec b y k = b (uvec b y k) y • v := by
    have := eq_pr_add (y := y) hu
    rwa [show pr b v y (uvec b y k) = 0 from h0, zero_add] at this
  have key : ∀ x, act k x = x + (b (uvec b y k) y * b x v) • v := by
    intro x
    have hx' : b (x + b x v • y) v = 0 := by
      rw [add_left, smul_left, hyv, mul_one, add_self_zmod2]
    have hxx : x = (x + b x v • y) + b x v • y := by
      rw [add_assoc, add_self_vec, add_zero]
    have e1 : b (x + b x v • y) (uvec b y k) = 0 := by
      rw [hu', smul_right, hx', mul_zero]
    conv_lhs => rw [hxx]
    rw [act_add, act_smul, act_eq_of_mem_rad halt hyv hk hx', e1, zero_smul, add_zero,
      act_y_eq, smul_add]
    conv_lhs => rw [hu']
    rw [smul_smul, mul_comm (b x v)]
    calc x + b x v • y + (b x v • y + (b (uvec b y k) y * b x v) • v) =
        x + (b (uvec b y k) y * b x v) • v + (b x v • y + b x v • y) := by abel
      _ = _ := by rw [add_self_vec, add_zero]
  rcases zmod_two_cases (b (uvec b y k) y) with h | h
  · left
    exact act_ext fun x => by rw [key, h, zero_mul, zero_smul, add_zero, act_one]
  · right
    exact act_ext fun x => by rw [key, h, one_mul, hT]

theorem piv_conj (halt : ∀ x, b x x = 0) (hyv : b y v = 1) {c k : SpG b} (hcv : act c v = v)
    (hk : k ∈ rad b v) : piv b v y (c * k * c⁻¹) = res b v y c (piv b v y k) := by
  have hcv' : act c⁻¹ v = v := act_inv_eq hcv
  have hz : b (act c⁻¹ y + y) v = 0 := by rw [add_left, b_act_left hcv', add_self_zmod2]
  have hy' : act c⁻¹ y = y + (act c⁻¹ y + y) := by
    rw [add_comm y, add_assoc, add_self_vec, add_zero]
  have hu : b (uvec b y k) v = 0 := b_uvec_v (mem_rad.1 hk).1
  set z := act c⁻¹ y + y with hzdef
  have e : uvec b y (c * k * c⁻¹) = act c (uvec b y k) + b z (uvec b y k) • v := by
    rw [uvec, act_mul, act_mul, hy', act_add, act_y_eq (k := k), act_eq_of_mem_rad halt hyv hk hz]
    rw [show y + uvec b y k + (z + b z (uvec b y k) • v) =
        (y + z) + uvec b y k + b z (uvec b y k) • v by abel, act_add, act_add, act_smul, hcv,
      ← hy', act_act_inv]
    calc y + act c (uvec b y k) + b z (uvec b y k) • v + y =
        (y + y) + (act c (uvec b y k) + b z (uvec b y k) • v) := by abel
      _ = _ := by rw [add_self_vec, zero_add]
  have hpu : pr b v y (uvec b y k) = uvec b y k + b (uvec b y k) y • v := by
    rw [pr, hu, zero_smul, add_zero]
  rw [piv, e, pr_add, pr_smul, pr_v halt hyv, smul_zero, add_zero, res, piv, hpu,
    pr_act_add_smul halt hyv hcv]

section Transvection

variable (halt : ∀ x, b x x = 0)
include halt

theorem tr_mul_self (a : ι → ZMod 2) : tr halt a * tr halt a = 1 := by
  refine act_ext fun x => ?_
  rw [act_mul, act_tr, act_tr, act_one, add_left, smul_left, halt a, mul_zero, add_zero,
    add_assoc, add_self_vec, add_zero]

theorem tr_comm {a z : ι → ZMod 2} (h : b a z = 0) :
    tr halt a * tr halt z = tr halt z * tr halt a := by
  have h' : b z a = 0 := by rw [b_symm halt, h]
  refine act_ext fun x => ?_
  rw [act_mul, act_mul, act_tr, act_tr, act_tr, act_tr, add_left, add_left, smul_left,
    smul_left, h, h', mul_zero, mul_zero, add_zero, add_zero]
  abel

theorem conj_tr (g : SpG b) (a : ι → ZMod 2) : g * tr halt a * g⁻¹ = tr halt (act g a) := by
  refine act_ext fun x => ?_
  rw [act_mul, act_mul, act_tr, act_tr, act_add, act_smul, act_act_inv]
  congr 2
  rw [← b_act_act g (act g⁻¹ x) a, act_act_inv]

theorem act_tr_mul_tr_self {a z : ι → ZMod 2} (h : b a z = 1) :
    act (tr halt a * tr halt z) a = z := by
  have h' : b z a = 1 := by rw [b_symm halt, h]
  rw [act_mul, act_tr, act_tr, h, one_smul, add_left, halt a, h', zero_add, one_smul,
    add_add_self_left]

theorem eq_tr {T : SpG b} (hT : ∀ x, act T x = x + b x v • v) : T = tr halt v :=
  act_ext fun x => by rw [hT, act_tr]

theorem tr_mem_centralizer {T : SpG b} (hT : ∀ x, act T x = x + b x v • v)
    {a : ι → ZMod 2} (ha : b a v = 0) : tr halt a ∈ Subgroup.centralizer {T} := by
  rw [Subgroup.mem_centralizer_singleton_iff, eq_tr halt hT]
  exact tr_comm halt ha

theorem act_tr_of_perp {a x : ι → ZMod 2} (h : b x a = 0) : act (tr halt a) x = x := by
  rw [act_tr, h, zero_smul, add_zero]

theorem act_tr_mul_tr_v {a z : ι → ZMod 2} (ha : b a v = 0) (hz : b z v = 0) :
    act (tr halt a * tr halt z) v = v := by
  have h1 : b v z = 0 := by rw [b_symm halt, hz]
  have h2 : b v a = 0 := by rw [b_symm halt, ha]
  rw [act_mul, act_tr_of_perp halt h1, act_tr_of_perp halt h2]

end Transvection

omit [DecidableEq ι] in
theorem exists_ne_zero_perp4 (h4 : 4 < Fintype.card ι) (w₁ w₂ w₃ w₄ : ι → ZMod 2) :
    ∃ c, c ≠ 0 ∧ b c w₁ = 0 ∧ b c w₂ = 0 ∧ b c w₃ = 0 ∧ b c w₄ = 0 := by
  let F : (ι → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    LinearMap.pi fun i => b.flip (![w₁, w₂, w₃, w₄] i)
  have h := LinearMap.ker_ne_bot_of_finrank_lt (f := F) (by simpa using h4)
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 h
  have hc' : ∀ i, b c (![w₁, w₂, w₃, w₄] i) = 0 := fun i => congrFun (LinearMap.mem_ker.1 hc) i
  exact ⟨c, hc0, hc' 0, hc' 1, hc' 2, hc' 3⟩

section Perp

variable (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
include halt hnd

omit [Fintype ι] [DecidableEq ι] in
theorem exists_perp_b_eq_one {a : ι → ZMod 2} (hv : v ≠ 0) (ha0 : a ≠ 0) (hav : a ≠ v) :
    ∃ c, b c v = 0 ∧ b a c = 1 := by
  obtain ⟨y', hy'⟩ := exists_b_eq_one halt hnd hv
  by_contra hcon
  push Not at hcon
  have key : ∀ x, b (a + b a y' • v) x = 0 := by
    intro x
    have hx : b (x + b x v • y') v = 0 := by
      rw [add_left, smul_left, hy', mul_one, add_self_zmod2]
    have h1 : b a (x + b x v • y') = 0 :=
      (zmod_two_cases _).resolve_right (hcon _ hx)
    rw [add_right, smul_right] at h1
    rw [add_left, smul_left, b_symm halt v x]
    linear_combination h1
  have h0 := hnd _ key
  rcases zmod_two_cases (b a y') with h | h
  · rw [h, zero_smul, add_zero] at h0
    exact ha0 h0
  · rw [h, one_smul] at h0
    exact hav (eq_of_add_eq_zero_vec h0)

omit [Fintype ι] [DecidableEq ι] in
theorem exists_perp_b_eq_one_two {a z : ι → ZMod 2} (hv : v ≠ 0) (ha0 : a ≠ 0) (hav : a ≠ v)
    (hz0 : z ≠ 0) (hzv : z ≠ v) : ∃ c, b c v = 0 ∧ b a c = 1 ∧ b z c = 1 := by
  obtain ⟨c₁, hc₁v, hc₁⟩ := exists_perp_b_eq_one halt hnd hv ha0 hav
  obtain ⟨c₂, hc₂v, hc₂⟩ := exists_perp_b_eq_one halt hnd hv hz0 hzv
  by_cases h1 : b z c₁ = 1
  · exact ⟨c₁, hc₁v, hc₁, h1⟩
  by_cases h2 : b a c₂ = 1
  · exact ⟨c₂, hc₂v, h2, hc₂⟩
  have h1' := (zmod_two_cases _).resolve_right h1
  have h2' := (zmod_two_cases _).resolve_right h2
  refine ⟨c₁ + c₂, by rw [add_left, hc₁v, hc₂v, add_zero], ?_, ?_⟩
  · rw [add_right, hc₁, h2', add_zero]
  · rw [add_right, h1', hc₂, zero_add]

end Perp

end CFSG.LargeExtraspecial.S12InspSp
