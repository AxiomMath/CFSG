module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRadical

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] {K : Type*} [Field K]

structure SzRootCoords (T₁ : Subgroup G) (a : ℕ) (d : G) (u v : G → K) (κ : K) : Prop where
  mul : ∀ x ∈ T₁, ∀ x' ∈ T₁, u (x * x') = u x + u x' ∧
    v (x * x') = v x + v x' + u x * u x' ^ 2 ^ (a + 1)
  inj : ∀ x ∈ T₁, ∀ x' ∈ T₁, u x = u x' → v x = v x' → x = x'
  surj : ∀ α β, ∃ x ∈ T₁, u x = α ∧ v x = β
  conj_mem : ∀ x ∈ T₁, d⁻¹ * x * d ∈ T₁
  conj_u : ∀ x ∈ T₁, u (d⁻¹ * x * d) = κ * u x
  conj_v : ∀ x ∈ T₁, u x = 0 → v (d⁻¹ * x * d) = κ ^ (2 ^ (a + 1) + 1) * v x

@[expose] def szA₁ (T₁ : Subgroup G) : Subgroup G := T₁ ⊓ centralizer (T₁ : Set G)

@[expose] def szR (T₁ R₂ : Subgroup G) (t : G) : Subgroup G := T₁ ⊔ R₂ ⊔ zpowers t

theorem mem_szA₁ {T₁ : Subgroup G} {x : G} :
    x ∈ szA₁ T₁ ↔ x ∈ T₁ ∧ x ∈ centralizer (T₁ : Set G) :=
  mem_inf

theorem szA₁_le (T₁ : Subgroup G) : szA₁ T₁ ≤ T₁ := inf_le_left

theorem le_szR_left (T₁ R₂ : Subgroup G) (t : G) : T₁ ≤ szR T₁ R₂ t :=
  le_sup_left.trans le_sup_left

theorem le_szR_mid (T₁ R₂ : Subgroup G) (t : G) : R₂ ≤ szR T₁ R₂ t :=
  le_sup_right.trans le_sup_left

theorem mem_szR_right (T₁ R₂ : Subgroup G) (t : G) : t ∈ szR T₁ R₂ t :=
  mem_sup_right (mem_zpowers t)

theorem sup_le_szR (T₁ R₂ : Subgroup G) (t : G) : T₁ ⊔ R₂ ≤ szR T₁ R₂ t := le_sup_left

structure SzR2 (T₁ R₂ : Subgroup G) (t d : G) : Prop where
  t_sq : t ^ 2 = 1
  t_comm : ∀ x ∈ T₁, x * t = t * x
  d_comm : d * t = t * d
  d_mem : d ∈ normalizer (R₂ : Set G)
  R₂_comm : ∀ r ∈ R₂, ∀ r' ∈ R₂, r * r' = r' * r
  le_R₂ : szA₁ T₁ ≤ R₂
  inf_le : T₁ ⊓ R₂ ≤ szA₁ T₁
  comm_mem : ∀ x ∈ T₁, ∀ r ∈ R₂, x * r * x⁻¹ * r⁻¹ ∈ szA₁ T₁
  rho_mem : ∀ r ∈ R₂, r * t * r⁻¹ * t⁻¹ ∈ szA₁ T₁
  rho_surj : ∀ b ∈ szA₁ T₁, ∃ r ∈ R₂, r * t * r⁻¹ * t⁻¹ = b
  rho_ker : ∀ r ∈ R₂, r * t * r⁻¹ * t⁻¹ = 1 → r ∈ szA₁ T₁

namespace SzRootCoords

variable {T₁ : Subgroup G} {a : ℕ} {d : G} {u v : G → K} {κ : K}

theorem u_one (h : SzRootCoords T₁ a d u v κ) : u 1 = 0 := by
  have h1 := (h.mul 1 (one_mem _) 1 (one_mem _)).1
  rw [mul_one] at h1
  exact add_eq_left.mp h1.symm

theorem v_one (h : SzRootCoords T₁ a d u v κ) : v 1 = 0 := by
  have h1 := (h.mul 1 (one_mem _) 1 (one_mem _)).2
  rw [mul_one, h.u_one, zero_mul, add_zero] at h1
  exact add_eq_left.mp h1.symm

variable [CharP K 2]

theorem inv (h : SzRootCoords T₁ a d u v κ) {x : G} (hx : x ∈ T₁) :
    u x⁻¹ = u x ∧ v x⁻¹ = v x + u x ^ (2 ^ (a + 1) + 1) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨h1, h3⟩ := h.mul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, h.u_one] at h1
  rw [mul_inv_cancel, h.v_one] at h3
  have hu : u x⁻¹ = u x := by linear_combination -h1 - u x * h2
  refine ⟨hu, ?_⟩
  rw [hu] at h3
  linear_combination -h3 - (v x + u x ^ (2 ^ (a + 1) + 1)) * h2

theorem sq (h : SzRootCoords T₁ a d u v κ) {x : G} (hx : x ∈ T₁) :
    u (x ^ 2) = 0 ∧ v (x ^ 2) = u x ^ (2 ^ (a + 1) + 1) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨h1, h3⟩ := h.mul x hx x hx
  rw [← _root_.sq] at h1 h3
  exact ⟨by linear_combination h1 + u x * h2, by linear_combination h3 + v x * h2⟩

theorem comm (h : SzRootCoords T₁ a d u v κ) {x x' : G} (hx : x ∈ T₁) (hx' : x' ∈ T₁) :
    u (x * x' * x⁻¹ * x'⁻¹) = 0 ∧
      v (x * x' * x⁻¹ * x'⁻¹) = u x * u x' ^ 2 ^ (a + 1) + u x' * u x ^ 2 ^ (a + 1) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨i1, i2⟩ := h.inv hx
  obtain ⟨i3, i4⟩ := h.inv hx'
  obtain ⟨a1, b1⟩ := h.mul _ hx _ hx'
  obtain ⟨a2, b2⟩ := h.mul _ (mul_mem hx hx') _ (inv_mem hx)
  obtain ⟨a3, b3⟩ := h.mul _ (mul_mem (mul_mem hx hx') (inv_mem hx)) _ (inv_mem hx')
  rw [i1, a1] at a2
  rw [i3, a2] at a3
  rw [i1, i2, a1, b1] at b2
  rw [i3, i4, a2, b2] at b3
  refine ⟨by linear_combination a3 + (u x + u x') * h2, ?_⟩
  rw [b3]
  linear_combination (v x + v x' + u x ^ (2 ^ (a + 1) + 1) + u x' ^ (2 ^ (a + 1) + 1) +
    u x * u x' ^ 2 ^ (a + 1)) * h2

omit [CharP K 2] in
theorem commute_of_u_eq_zero (h : SzRootCoords T₁ a d u v κ) {x : G} (hx : x ∈ T₁) (hu : u x = 0)
    {x' : G} (hx' : x' ∈ T₁) : x' * x = x * x' := by
  obtain ⟨a1, b1⟩ := h.mul _ hx' _ hx
  obtain ⟨a2, b2⟩ := h.mul _ hx _ hx'
  refine h.inj _ (mul_mem hx' hx) _ (mul_mem hx hx') (by rw [a1, a2]; exact add_comm _ _) ?_
  rw [b1, b2, hu, zero_mul, add_zero, zero_pow (pow_pos two_pos _).ne', mul_zero, add_zero]
  exact add_comm _ _

omit [CharP K 2] in
theorem mem_szA₁_iff [Fintype K] (h : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {x : G} (hx : x ∈ T₁) : x ∈ szA₁ T₁ ↔ u x = 0 := by
  classical
  refine ⟨fun hxc => ?_, fun hu =>
    mem_inf.mpr ⟨hx, mem_centralizer_iff.mpr fun x' hx' => h.commute_of_u_eq_zero hx hu hx'⟩⟩
  have hfix : ∀ x' ∈ T₁, u x * u x' ^ 2 ^ (a + 1) = u x' * u x ^ 2 ^ (a + 1) := by
    intro x' hx'
    have hc := mem_centralizer_iff.mp (mem_inf.mp hxc).2 x' hx'
    have e1 := (h.mul _ hx' _ hx).2
    have e2 := (h.mul _ hx _ hx').2
    rw [hc, e2] at e1
    linear_combination e1
  obtain ⟨x₁, hx₁, hu₁, -⟩ := h.surj 1 0
  have h1 := hfix x₁ hx₁
  rw [hu₁, one_pow, mul_one, one_mul] at h1
  rcases SzRadical.eq_zero_or_eq_one_of_pow_theta_eq hK h1.symm with h0 | h1'
  · exact h0
  · exfalso
    have hall : ∀ w : K, w = 0 ∨ w = 1 := by
      intro w
      obtain ⟨x', hx', hu', -⟩ := h.surj w 0
      have h3 := hfix x' hx'
      rw [h1', one_mul, one_pow, mul_one, hu'] at h3
      exact SzRadical.eq_zero_or_eq_one_of_pow_theta_eq hK h3
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun w _ => by
      rcases hall w with hw | hw <;> simp [hw]
    have h4 := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ, hK] at h4
    have h5 : 2 ^ 2 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (h5.trans h4) (by norm_num)

section A₁

variable [Fintype K] (h : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
  (hK : Fintype.card K = 2 ^ (2 * a + 1))
include h ha hK

omit [CharP K 2] in
theorem u_eq_zero_of_mem_szA₁ {b : G} (hb : b ∈ szA₁ T₁) : u b = 0 :=
  (h.mem_szA₁_iff ha hK (szA₁_le T₁ hb)).mp hb

omit [CharP K 2] in
theorem v_mul_szA₁ {b b' : G} (hb : b ∈ szA₁ T₁) (hb' : b' ∈ szA₁ T₁) :
    v (b * b') = v b + v b' := by
  rw [(h.mul b (szA₁_le T₁ hb) b' (szA₁_le T₁ hb')).2, h.u_eq_zero_of_mem_szA₁ ha hK hb,
    zero_mul, add_zero]

theorem v_inv_szA₁ {b : G} (hb : b ∈ szA₁ T₁) : v b⁻¹ = v b := by
  have h1 := h.v_mul_szA₁ ha hK hb (inv_mem hb)
  rw [mul_inv_cancel, h.v_one] at h1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination -h1 - v b * h2

omit [CharP K 2] in
theorem eq_one_of_v_eq_zero {b : G} (hb : b ∈ szA₁ T₁) (h0 : v b = 0) : b = 1 :=
  h.inj b (szA₁_le T₁ hb) 1 (one_mem _) (by rw [h.u_eq_zero_of_mem_szA₁ ha hK hb, h.u_one])
    (by rw [h0, h.v_one])

omit [CharP K 2] in
theorem exists_v_eq (w : K) : ∃ b ∈ szA₁ T₁, v b = w := by
  obtain ⟨b, hb, hu, hv⟩ := h.surj 0 w
  exact ⟨b, (h.mem_szA₁_iff ha hK hb).mpr hu, hv⟩

theorem sq_eq_one_of_mem_szA₁ {b : G} (hb : b ∈ szA₁ T₁) : b ^ 2 = 1 := by
  have hbT := szA₁_le T₁ hb
  obtain ⟨h1, h2⟩ := h.sq hbT
  refine h.inj _ (pow_mem hbT 2) 1 (one_mem _) (by rw [h1, h.u_one]) ?_
  rw [h2, h.u_eq_zero_of_mem_szA₁ ha hK hb, zero_pow (Nat.succ_ne_zero _), h.v_one]

theorem comm_mem_szA₁ {x x' : G} (hx : x ∈ T₁) (hx' : x' ∈ T₁) :
    x * x' * x⁻¹ * x'⁻¹ ∈ szA₁ T₁ :=
  (h.mem_szA₁_iff ha hK (mul_mem (mul_mem (mul_mem hx hx') (inv_mem hx)) (inv_mem hx'))).mpr
    (h.comm hx hx').1

theorem sq_mem_szA₁ {x : G} (hx : x ∈ T₁) : x ^ 2 ∈ szA₁ T₁ :=
  (h.mem_szA₁_iff ha hK (pow_mem hx 2)).mpr (h.sq hx).1

omit [CharP K 2] in
theorem conj_mem_szA₁ {b : G} (hb : b ∈ szA₁ T₁) : d⁻¹ * b * d ∈ szA₁ T₁ :=
  (h.mem_szA₁_iff ha hK (h.conj_mem b (szA₁_le T₁ hb))).mpr (by
    rw [h.conj_u b (szA₁_le T₁ hb), h.u_eq_zero_of_mem_szA₁ ha hK hb, mul_zero])

omit [CharP K 2] in
theorem v_conj_szA₁ {b : G} (hb : b ∈ szA₁ T₁) :
    v (d⁻¹ * b * d) = κ ^ (2 ^ (a + 1) + 1) * v b :=
  h.conj_v b (szA₁_le T₁ hb) (h.u_eq_zero_of_mem_szA₁ ha hK hb)

theorem inv_mul_mem_szA₁_of_u_eq {x x' : G} (hx : x ∈ T₁) (hx' : x' ∈ T₁) (hu : u x = u x') :
    x⁻¹ * x' ∈ szA₁ T₁ := by
  refine (h.mem_szA₁_iff ha hK (mul_mem (inv_mem hx) hx')).mpr ?_
  rw [(h.mul _ (inv_mem hx) _ hx').1, (h.inv hx).1, hu, CharTwo.add_self_eq_zero]

end A₁

end SzRootCoords

theorem comm_mem_of_generators {R A : Subgroup G} {P : G → Prop}
    (hgen : ∀ S : Subgroup G, (∀ g, P g → g ∈ S) → R ≤ S) (hPR : ∀ g, P g → g ∈ R)
    (hA : ∀ y ∈ R, ∀ b ∈ A, y * b = b * y)
    (hP : ∀ g, P g → ∀ g', P g' → g * g' * g⁻¹ * g'⁻¹ ∈ A) :
    ∀ x ∈ R, ∀ x' ∈ R, x * x' * x⁻¹ * x'⁻¹ ∈ A := by
  let S : G → Subgroup G := fun x =>
    { carrier := {z | z ∈ R ∧ x * z * x⁻¹ * z⁻¹ ∈ A}
      mul_mem' := by
        rintro z z' ⟨hz, hzA⟩ ⟨hz', hz'A⟩
        refine ⟨mul_mem hz hz', ?_⟩
        have e : x * (z * z') * x⁻¹ * (z * z')⁻¹ =
            x * z * x⁻¹ * z⁻¹ * (z * (x * z' * x⁻¹ * z'⁻¹) * z⁻¹) := by group
        rw [e, hA z hz _ hz'A, mul_assoc (x * z' * x⁻¹ * z'⁻¹), mul_inv_cancel, mul_one]
        exact mul_mem hzA hz'A
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro z ⟨hz, hzA⟩
        refine ⟨inv_mem hz, ?_⟩
        have e : x * z⁻¹ * x⁻¹ * z⁻¹⁻¹ = z⁻¹ * (x * z * x⁻¹ * z⁻¹)⁻¹ * z := by group
        rw [e, hA _ (inv_mem hz) _ (inv_mem hzA), mul_assoc, inv_mul_cancel, mul_one]
        exact inv_mem hzA }
  have hS : ∀ x, ∀ z ∈ S x, x * z * x⁻¹ * z⁻¹ ∈ A := fun x z hz => hz.2
  have hgen1 : ∀ g, P g → ∀ z ∈ R, g * z * g⁻¹ * z⁻¹ ∈ A := fun g hg z hz =>
    hS g z (hgen (S g) (fun g' hg' => ⟨hPR g' hg', hP g hg g' hg'⟩) hz)
  intro x hx x' hx'
  refine hS x x' (hgen (S x) (fun g hg => ⟨hPR g hg, ?_⟩) hx')
  have e : x * g * x⁻¹ * g⁻¹ = (g * x * g⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem (hgen1 g hg x hx)

namespace SzR2

variable {T₁ R₂ : Subgroup G} {t d : G}

theorem le_normalizer_R₂ (hS : SzR2 T₁ R₂ t d) : T₁ ≤ normalizer (R₂ : Set G) := by
  have key : ∀ y ∈ T₁, ∀ r ∈ R₂, y * r * y⁻¹ ∈ R₂ := fun y hy r hr => by
    have e : y * r * y⁻¹ = (y * r * y⁻¹ * r⁻¹) * r := by group
    rw [e]
    exact mul_mem (hS.le_R₂ (hS.comm_mem y hy r hr)) hr
  intro x hx
  refine mem_normalizer_iff.mpr fun r => ⟨fun hr => key x hx r hr, fun hr => ?_⟩
  have e : r = x⁻¹ * (x * r * x⁻¹) * x⁻¹⁻¹ := by group
  rw [e]
  exact key x⁻¹ (inv_mem hx) _ hr

theorem t_inv (hS : SzR2 T₁ R₂ t d) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hS.t_sq)

theorem conj_t_mem (hS : SzR2 T₁ R₂ t d) {r : G} (hr : r ∈ R₂) : t * r * t⁻¹ ∈ R₂ := by
  have h1 : t * r⁻¹ * t⁻¹ = r⁻¹ * (r * t * r⁻¹ * t⁻¹) := by group
  have h2 : t * r⁻¹ * t⁻¹ ∈ R₂ := h1 ▸ mul_mem (inv_mem hr) (hS.le_R₂ (hS.rho_mem r hr))
  have e : t * r * t⁻¹ = (t * r⁻¹ * t⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem h2

theorem t_mem_normalizer_R₂ (hS : SzR2 T₁ R₂ t d) : t ∈ normalizer (R₂ : Set G) := by
  refine mem_normalizer_iff.mpr fun r => ⟨hS.conj_t_mem, fun hr => ?_⟩
  have e : r = t * (t * r * t⁻¹) * t⁻¹ := by
    calc r = t⁻¹ * (t * r * t⁻¹) * t := by group
      _ = t * (t * r * t⁻¹) * t⁻¹ := by rw [hS.t_inv]
  rw [e]
  exact hS.conj_t_mem hr

theorem commute_szA₁ (hS : SzR2 T₁ R₂ t d) :
    ∀ x ∈ szR T₁ R₂ t, ∀ b ∈ szA₁ T₁, x * b = b * x := by
  have hle : szR T₁ R₂ t ≤ centralizer (szA₁ T₁ : Set G) := by
    refine sup_le (sup_le (fun x hx => mem_centralizer_iff.mpr fun b hb => ?_)
      (fun r hr => mem_centralizer_iff.mpr fun b hb => hS.R₂_comm b (hS.le_R₂ hb) r hr)
      ) (zpowers_le.mpr (mem_centralizer_iff.mpr fun b hb => hS.t_comm b (szA₁_le T₁ hb)))
    exact (mem_centralizer_iff.mp (mem_szA₁.mp hb).2 x hx).symm
  intro x hx b hb
  exact (mem_centralizer_iff.mp (hle hx) b hb).symm

theorem exists_decomp (hS : SzR2 T₁ R₂ t d) {x : G} (hx : x ∈ szR T₁ R₂ t) :
    ∃ y ∈ T₁, ∃ r ∈ R₂, x = y * r ∨ x = y * r * t := by
  have h1 : ((T₁ ⊔ R₂ : Subgroup G) : Set G) = (T₁ : Set G) * (R₂ : Set G) :=
    coe_mul_of_left_le_normalizer_right T₁ R₂ hS.le_normalizer_R₂
  have hconj : ∀ w ∈ T₁ ⊔ R₂, t * w * t⁻¹ ∈ T₁ ⊔ R₂ := by
    intro w hw
    rw [← SetLike.mem_coe, h1] at hw ⊢
    obtain ⟨y, hy, r, hr, rfl⟩ := hw
    refine ⟨y, hy, t * r * t⁻¹, hS.conj_t_mem hr, ?_⟩
    have e := hS.t_comm y hy
    calc y * (t * r * t⁻¹) = (y * t) * r * t⁻¹ := by group
      _ = t * (y * r) * t⁻¹ := by rw [e]; group
  have htN : zpowers t ≤ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) := by
    refine zpowers_le.mpr (mem_normalizer_iff.mpr fun w => ⟨hconj w, fun hw => ?_⟩)
    have e : w = t * (t * w * t⁻¹) * t⁻¹ := by
      calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
        _ = t * (t * w * t⁻¹) * t⁻¹ := by rw [hS.t_inv]
    rw [e]
    exact hconj _ hw
  have h2 : ((szR T₁ R₂ t : Subgroup G) : Set G) =
      ((T₁ ⊔ R₂ : Subgroup G) : Set G) * ((zpowers t : Subgroup G) : Set G) :=
    coe_mul_of_right_le_normalizer_left (T₁ ⊔ R₂) (zpowers t) htN
  rw [← SetLike.mem_coe, h2] at hx
  obtain ⟨w, hw, s, hs, rfl⟩ := hx
  rw [SetLike.mem_coe, ← SetLike.mem_coe, h1] at hw
  obtain ⟨y, hy, r, hr, rfl⟩ := hw
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
  refine ⟨y, hy, r, hr, ?_⟩
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, hS.t_sq]
  rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
  · left
    show y * r * t ^ (2 * j) = y * r
    rw [zpow_mul, ht2, one_zpow, mul_one]
  · right
    show y * r * t ^ (2 * j + 1) = y * r * t
    rw [zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

theorem rho_eq_one_of_mem_T₁ (hS : SzR2 T₁ R₂ t d) {y : G} (hy : y ∈ T₁) :
    y * t * y⁻¹ * t⁻¹ = 1 := by
  rw [hS.t_comm y hy]
  group

theorem conj_rho (hS : SzR2 T₁ R₂ t d) (x : G) :
    d⁻¹ * x * d * t * (d⁻¹ * x * d)⁻¹ * t⁻¹ = d⁻¹ * (x * t * x⁻¹ * t⁻¹) * d := by
  have h1 : d * t⁻¹ = t⁻¹ * d := by rw [hS.t_inv, hS.d_comm]
  calc d⁻¹ * x * d * t * (d⁻¹ * x * d)⁻¹ * t⁻¹ = d⁻¹ * x * (d * t) * d⁻¹ * x⁻¹ * d * t⁻¹ := by
        group
    _ = d⁻¹ * x * (t * d) * d⁻¹ * x⁻¹ * (d * t⁻¹) := by rw [hS.d_comm]; group
    _ = d⁻¹ * x * (t * d) * d⁻¹ * x⁻¹ * (t⁻¹ * d) := by rw [h1]
    _ = d⁻¹ * (x * t * x⁻¹ * t⁻¹) * d := by group

theorem conj_d_mem (hS : SzR2 T₁ R₂ t d) {r : G} (hr : r ∈ R₂) : d⁻¹ * r * d ∈ R₂ := by
  have := (mem_normalizer_iff.mp (inv_mem hS.d_mem) r).mp hr
  simpa using this

section Calculus

variable [Fintype K] [CharP K 2] {a : ℕ} {u v : G → K} {κ : K}
  (hS : SzR2 T₁ R₂ t d) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
  (hK : Fintype.card K = 2 ^ (2 * a + 1))
include hS hc ha hK

theorem comm_mem_szA₁ :
    ∀ x ∈ szR T₁ R₂ t, ∀ x' ∈ szR T₁ R₂ t, x * x' * x⁻¹ * x'⁻¹ ∈ szA₁ T₁ := by
  refine comm_mem_of_generators (P := fun g => g ∈ T₁ ∨ g ∈ R₂ ∨ g = t)
    (fun S hS' => sup_le (sup_le (fun x hx => hS' x (Or.inl hx))
      (fun x hx => hS' x (Or.inr (Or.inl hx)))) (zpowers_le.mpr (hS' t (Or.inr (Or.inr rfl)))))
    ?_ hS.commute_szA₁ ?_
  · rintro g (hg | hg | hg)
    · exact le_szR_left T₁ R₂ t hg
    · exact le_szR_mid T₁ R₂ t hg
    · rw [hg]; exact mem_szR_right T₁ R₂ t
  · have hinv : ∀ x z : G, x * z * x⁻¹ * z⁻¹ = (z * x * z⁻¹ * x⁻¹)⁻¹ := fun x z => by group
    rintro g (hg | hg | hg) g' (hg' | hg' | hg')
    · exact hc.comm_mem_szA₁ ha hK hg hg'
    · exact hS.comm_mem g hg g' hg'
    · rw [hg', hS.rho_eq_one_of_mem_T₁ hg]; exact one_mem _
    · rw [hinv]; exact inv_mem (hS.comm_mem g' hg' g hg)
    · rw [hS.R₂_comm g hg g' hg']; simp only [mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    · rw [hg']; exact hS.rho_mem g hg
    · rw [hg, hinv, hS.rho_eq_one_of_mem_T₁ hg', inv_one]; exact one_mem _
    · rw [hg, hinv]; exact inv_mem (hS.rho_mem g' hg')
    · rw [hg, hg']; simp only [mul_inv_cancel_right, mul_inv_cancel]; exact one_mem _

omit hc ha hK in
theorem commutator_mul_left' (hR : ∀ x ∈ szR T₁ R₂ t, ∀ x' ∈ szR T₁ R₂ t,
      x * x' * x⁻¹ * x'⁻¹ ∈ szA₁ T₁) {x x' z : G}
    (hx : x ∈ szR T₁ R₂ t) (hx' : x' ∈ szR T₁ R₂ t) (hz : z ∈ szR T₁ R₂ t) :
    x * x' * z * (x * x')⁻¹ * z⁻¹ = x * z * x⁻¹ * z⁻¹ * (x' * z * x'⁻¹ * z⁻¹) := by
  have hc' := hR x' hx' z hz
  have h1 := hS.commute_szA₁ x hx _ hc'
  have h2 := hS.commute_szA₁ _ (le_szR_left T₁ R₂ t (szA₁_le T₁ hc')) _ (hR x hx z hz)
  calc x * x' * z * (x * x')⁻¹ * z⁻¹ =
        x * (x' * z * x'⁻¹ * z⁻¹) * x⁻¹ * (x * z * x⁻¹ * z⁻¹) := by group
    _ = (x' * z * x'⁻¹ * z⁻¹) * (x * z * x⁻¹ * z⁻¹) := by rw [h1]; group
    _ = _ := h2

theorem commutator_mul_left {x x' z : G} (hx : x ∈ szR T₁ R₂ t) (hx' : x' ∈ szR T₁ R₂ t)
    (hz : z ∈ szR T₁ R₂ t) :
    x * x' * z * (x * x')⁻¹ * z⁻¹ = x * z * x⁻¹ * z⁻¹ * (x' * z * x'⁻¹ * z⁻¹) :=
  hS.commutator_mul_left' (hS.comm_mem_szA₁ hc ha hK) hx hx' hz

theorem commutator_mul_right {x z z' : G} (hx : x ∈ szR T₁ R₂ t) (hz : z ∈ szR T₁ R₂ t)
    (hz' : z' ∈ szR T₁ R₂ t) :
    x * (z * z') * x⁻¹ * (z * z')⁻¹ = x * z * x⁻¹ * z⁻¹ * (x * z' * x⁻¹ * z'⁻¹) := by
  have h1 := hS.commute_szA₁ z hz _ (hS.comm_mem_szA₁ hc ha hK x hx z' hz')
  calc x * (z * z') * x⁻¹ * (z * z')⁻¹ =
        (x * z * x⁻¹ * z⁻¹) * (z * (x * z' * x⁻¹ * z'⁻¹) * z⁻¹) := by group
    _ = _ := by rw [h1]; group

theorem sq_mem_szA₁_of_mem_R₂ {r : G} (hr : r ∈ R₂) : r ^ 2 ∈ szA₁ T₁ := by
  apply hS.rho_ker _ (pow_mem hr 2)
  have hb := hS.rho_mem r hr
  have hcomm := hS.commute_szA₁ r (le_szR_mid T₁ R₂ t hr) _ hb
  calc r ^ 2 * t * (r ^ 2)⁻¹ * t⁻¹ = r * (r * t * r⁻¹ * t⁻¹) * r⁻¹ * (r * t * r⁻¹ * t⁻¹) := by
        simp only [sq]; group
    _ = (r * t * r⁻¹ * t⁻¹) ^ 2 := by rw [hcomm]; simp only [sq]; group
    _ = 1 := hc.sq_eq_one_of_mem_szA₁ ha hK hb

omit hS hc ha hK in
theorem sq_mul_of_commute {x x' : G} (h : x' * x ^ 2 = x ^ 2 * x') :
    (x * x') ^ 2 = x * x' * x⁻¹ * x'⁻¹ * x ^ 2 * x' ^ 2 := by
  calc (x * x') ^ 2 = x * x' * x⁻¹ * x'⁻¹ * (x' * x ^ 2) * x' := by simp only [sq]; group
    _ = _ := by rw [h]; simp only [sq]; group

theorem sq_mem_szA₁ {x : G} (hx : x ∈ szR T₁ R₂ t) : x ^ 2 ∈ szA₁ T₁ := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ szR T₁ R₂ t ∧ x ^ 2 ∈ szA₁ T₁}
      mul_mem' := by
        rintro x x' ⟨hx, hx2⟩ ⟨hx', hx'2⟩
        refine ⟨mul_mem hx hx', ?_⟩
        rw [sq_mul_of_commute (hS.commute_szA₁ x' hx' _ hx2)]
        exact mul_mem (mul_mem (hS.comm_mem_szA₁ hc ha hK x hx x' hx') hx2) hx'2
      one_mem' := ⟨one_mem _, by rw [one_pow]; exact one_mem _⟩
      inv_mem' := by
        rintro x ⟨hx, hx2⟩
        exact ⟨inv_mem hx, by rw [inv_pow]; exact inv_mem hx2⟩ }
  have hle : szR T₁ R₂ t ≤ S := by
    refine sup_le (sup_le (fun y hy => ⟨le_szR_left T₁ R₂ t hy, hc.sq_mem_szA₁ ha hK hy⟩)
      (fun r hr => ⟨le_szR_mid T₁ R₂ t hr, hS.sq_mem_szA₁_of_mem_R₂ hc ha hK hr⟩))
      (zpowers_le.mpr ⟨mem_szR_right T₁ R₂ t, by rw [hS.t_sq]; exact one_mem _⟩)
  exact (hle hx).2

theorem sq_mul {x x' : G} (hx : x ∈ szR T₁ R₂ t) (hx' : x' ∈ szR T₁ R₂ t) :
    (x * x') ^ 2 = x * x' * x⁻¹ * x'⁻¹ * x ^ 2 * x' ^ 2 :=
  sq_mul_of_commute (hS.commute_szA₁ x' hx' _ (hS.sq_mem_szA₁ hc ha hK hx))

theorem rho_mul {x x' : G} (hx : x ∈ szR T₁ R₂ t) (hx' : x' ∈ szR T₁ R₂ t) :
    v (x * x' * t * (x * x')⁻¹ * t⁻¹) = v (x * t * x⁻¹ * t⁻¹) + v (x' * t * x'⁻¹ * t⁻¹) := by
  have ht := mem_szR_right T₁ R₂ t
  rw [hS.commutator_mul_left hc ha hK hx hx' ht, hc.v_mul_szA₁ ha hK
    (hS.comm_mem_szA₁ hc ha hK x hx t ht) (hS.comm_mem_szA₁ hc ha hK x' hx' t ht)]

omit [Fintype K] [CharP K 2] ha hK in
theorem rho_eq_zero_of_mem_T₁ {y : G} (hy : y ∈ T₁) : v (y * t * y⁻¹ * t⁻¹) = 0 := by
  rw [hS.rho_eq_one_of_mem_T₁ hy, hc.v_one]

omit [CharP K 2] in
theorem rho_eq_zero_iff {r : G} (hr : r ∈ R₂) : v (r * t * r⁻¹ * t⁻¹) = 0 ↔ r ∈ szA₁ T₁ :=
  ⟨fun h0 => hS.rho_ker r hr (hc.eq_one_of_v_eq_zero ha hK (hS.rho_mem r hr) h0),
    fun hA => hS.rho_eq_zero_of_mem_T₁ hc (szA₁_le T₁ hA)⟩

omit [CharP K 2] in
theorem exists_rho_eq (w : K) : ∃ r ∈ R₂, v (r * t * r⁻¹ * t⁻¹) = w := by
  obtain ⟨b, hb, hbw⟩ := hc.exists_v_eq ha hK w
  obtain ⟨r, hr, hrb⟩ := hS.rho_surj b hb
  exact ⟨r, hr, by rw [hrb, hbw]⟩

omit [CharP K 2] in
theorem rho_conj {r : G} (hr : r ∈ R₂) :
    v (d⁻¹ * r * d * t * (d⁻¹ * r * d)⁻¹ * t⁻¹) =
      κ ^ (2 ^ (a + 1) + 1) * v (r * t * r⁻¹ * t⁻¹) := by
  rw [hS.conj_rho, hc.v_conj_szA₁ ha hK (hS.rho_mem r hr)]

theorem inv_mul_mem_szA₁_of_rho_eq {r r' : G} (hr : r ∈ R₂) (hr' : r' ∈ R₂)
    (h : v (r * t * r⁻¹ * t⁻¹) = v (r' * t * r'⁻¹ * t⁻¹)) : r⁻¹ * r' ∈ szA₁ T₁ := by
  have hrR := le_szR_mid T₁ R₂ t hr
  have hr'R := le_szR_mid T₁ R₂ t hr'
  rw [← hS.rho_eq_zero_iff hc ha hK (mul_mem (inv_mem hr) hr'),
    hS.rho_mul hc ha hK (inv_mem hrR) hr'R]
  have h0 := hS.rho_mul hc ha hK (inv_mem hrR) hrR
  rw [show r⁻¹ * r * t * (r⁻¹ * r)⁻¹ * t⁻¹ = 1 by group, hc.v_one] at h0
  linear_combination -h0 - h

end Calculus

end SzR2

end CFSG.SeitzReduction.RankOne
