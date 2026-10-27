module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Level1
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1LevelBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3A₁Coords

variable {G : Type*} [Group G] {K : Type*} [Field K] {A₁ : Subgroup G} {d : G} {v : G → K}
  {μ : K}

theorem eq_one_of_v_eq_zero (hc : U3A₁Coords A₁ d v μ) {b : G} (hb : b ∈ A₁) (h0 : v b = 0) :
    b = 1 :=
  hc.inj b hb 1 (one_mem _) (by rw [h0, hc.v_one])

theorem sq_eq_one [CharP K 2] (hc : U3A₁Coords A₁ d v μ) {b : G} (hb : b ∈ A₁) : b ^ 2 = 1 := by
  refine hc.eq_one_of_v_eq_zero (pow_mem hb 2) ?_
  rw [sq, hc.mul b hb b hb, CharTwo.add_self_eq_zero]

theorem conj_pow (hc : U3A₁Coords A₁ d v μ) (n : ℕ) {b : G} (hb : b ∈ A₁) :
    (d ^ n)⁻¹ * b * d ^ n ∈ A₁ ∧ v ((d ^ n)⁻¹ * b * d ^ n) = μ ^ n * v b := by
  induction n with
  | zero => simpa using hb
  | succ n ih =>
    have e : (d ^ (n + 1))⁻¹ * b * d ^ (n + 1) = d⁻¹ * ((d ^ n)⁻¹ * b * d ^ n) * d := by
      rw [pow_succ]
      group
    rw [e]
    exact ⟨hc.conj_mem _ ih.1, by rw [hc.conj _ ih.1, ih.2, pow_succ]; ring⟩

theorem pow_eq_one_of_centralizes (hc : U3A₁Coords A₁ d v μ) {m : ℕ}
    (hm : ∀ b ∈ A₁, d ^ m * b * (d ^ m)⁻¹ = b) : μ ^ m = 1 := by
  obtain ⟨b, hb, hb1⟩ := hc.surj 1
  have e : (d ^ m)⁻¹ * b * d ^ m = b := by
    calc (d ^ m)⁻¹ * b * d ^ m = (d ^ m)⁻¹ * (d ^ m * b * (d ^ m)⁻¹) * d ^ m := by rw [hm b hb]
      _ = b := by group
  have h1 := (hc.conj_pow m hb).2
  rw [e, hb1, mul_one] at h1
  exact h1.symm

end U3A₁Coords

namespace U3C1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

section Basic

variable (h : U3C1Stage G L f t T d V U U₁ k)
include h

theorem t_sq : t ^ 2 = 1 := h.start.sq_eq_one

theorem t_mul_self : t * t = 1 := by rw [← sq]; exact h.t_sq

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_self

theorem t_comm {y : G} (hy : y ∈ szT₁ L T) : y * t = t * y :=
  mem_centralizer_iff.mp h.start.mem_centralizer_szT₁ y hy

theorem V_comm {r : G} (hr : r ∈ V) {y : G} (hy : y ∈ szT₁ L T) : y * r = r * y :=
  mem_centralizer_iff.mp (h.le_centralizer hr) y hy

theorem t_mul_of_mem {r : G} (hr : r ∈ V) : t * r = r⁻¹ * t := by
  calc t * r = (t * r * t⁻¹) * t := by group
    _ = r⁻¹ * t := by rw [h.inv r hr]

theorem sup_le_U₁ : szT₁ L T ⊔ V ≤ U₁ := h.inf_eq ▸ inf_le_left

theorem T₁_le_U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans h.sup_le_U₁

theorem V_le_U₁ : V ≤ U₁ := le_sup_right.trans h.sup_le_U₁

theorem t_mem_U : t ∈ U := by
  rw [← h.sup_eq]
  exact mem_sup_right (mem_zpowers t)

theorem conj_mem_U₁ {x : G} (hx : x ∈ U) {w : G} (hw : w ∈ U₁) : x * w * x⁻¹ ∈ U₁ :=
  (mem_normalizer_iff.mp (h.U₁_normal hx) w).mp hw

theorem t_mem_normalizer_U₁ : t ∈ normalizer (U₁ : Set G) := h.U₁_normal h.t_mem_U

theorem mem_or_mul_t_mem {x : G} (hx : x ∈ U) : x ∈ U₁ ∨ x * t ∈ U₁ :=
  CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers h.t_mul_self h.t_mem_normalizer_U₁
    (by rw [h.sup_eq]; exact hx)

theorem conj_V {x : G} (hx : x ∈ U₁) {r : G} (hr : r ∈ V) : x * r * x⁻¹ ∈ V := by
  have e : x * r * x⁻¹ = r * (r⁻¹ * (x * r * x⁻¹)) := by group
  rw [e]
  exact mul_mem hr (h.le (h.conj_V₁ x hx r hr))

theorem U_le_normalizer_V : U ≤ normalizer (V : Set G) := by
  rw [← h.sup_eq]
  refine sup_le (fun x hx => mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => ?_)
    (zpowers_le.mpr (mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => ?_))
  · simpa using h.conj_V (inv_mem hx) hr
  · rw [h.t_inv, show t * r * t = t * r * t⁻¹ by rw [h.t_inv], h.inv r hr]
    exact inv_mem hr

theorem conj_V_of_mem_U {x : G} (hx : x ∈ U) {r : G} (hr : r ∈ V) : x * r * x⁻¹ ∈ V :=
  (mem_normalizer_iff.mp (h.U_le_normalizer_V hx) r).mp hr

theorem T₁_le_normalizer_V : szT₁ L T ≤ normalizer (V : Set G) := fun y hy =>
  mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => by
    rw [h.V_comm hr (inv_mem hy), inv_mul_cancel_right]
    exact hr

theorem exists_mul_of_mem_sup {x : G} (hx : x ∈ szT₁ L T ⊔ V) :
    ∃ y ∈ szT₁ L T, ∃ r ∈ V, x = y * r := by
  have hx' : x ∈ ((szT₁ L T ⊔ V : Subgroup G) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right _ _ h.T₁_le_normalizer_V] at hx'
  obtain ⟨y, hy, r, hr, rfl⟩ := hx'
  exact ⟨y, hy, r, hr, rfl⟩

theorem sup_le_centralizer_V : szT₁ L T ⊔ V ≤ centralizer (V : Set G) :=
  sup_le (fun _ hy => mem_centralizer_iff.mpr fun _ hr => (h.V_comm hr hy).symm)
    (fun r hr => mem_centralizer_iff.mpr fun r' hr' => h.comm r' hr' r hr)

theorem t_mem_normalizer_sup : t ∈ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) := by
  refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_
  obtain ⟨y, hy, r, hr, rfl⟩ := h.exists_mul_of_mem_sup hx
  have e : t⁻¹ * (y * r) * t = y * (t * r * t⁻¹) := by
    calc t⁻¹ * (y * r) * t = (t * y) * r * t := by rw [h.t_inv]; group
      _ = y * t * r * t := by rw [← h.t_comm hy]
      _ = y * (t * r * t⁻¹) := by rw [h.t_inv]; group
  rw [e, h.inv r hr]
  exact mul_mem (mem_sup_left hy) (mem_sup_right (inv_mem hr))

theorem t_mem_normalizer_T₁ : t ∈ normalizer (szT₁ L T : Set G) :=
  mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => by
    rw [h.t_inv, ← h.t_comm hy, mul_assoc, h.t_mul_self, mul_one]
    exact hy

theorem sq_mul_mul_t {y r : G} (hy : y ∈ szT₁ L T) (hr : r ∈ V) : (y * r * t) ^ 2 = y ^ 2 := by
  have e1 : t * y = y * t := (h.t_comm hy).symm
  have e3 : r * y = y * r := (h.V_comm hr hy).symm
  calc (y * r * t) ^ 2 = y * r * (t * y) * r * t := by rw [sq]; group
    _ = y * (r * y) * (t * r) * t := by rw [e1]; group
    _ = y * (y * r) * (r⁻¹ * t) * t := by rw [e3, h.t_mul_of_mem hr]
    _ = y * y * (t * t) := by group
    _ = y ^ 2 := by rw [h.t_mul_self, mul_one, sq]

theorem inf_eq_szA₁ : szT₁ L T ⊓ V = szA₁ (szT₁ L T) :=
  le_antisymm (fun _ hx => mem_szA₁.mpr ⟨(mem_inf.mp hx).1, h.le_centralizer (mem_inf.mp hx).2⟩)
    (le_inf (szA₁_le _) h.le)

theorem pow_mem_szA₁ {r : G} (hr : r ∈ V) : r ^ 2 ^ k ∈ szA₁ (szT₁ L T) := by
  refine h.omega _ (pow_mem hr _) ?_
  rw [← pow_mul, ← pow_succ]
  exact h.pow r hr

theorem comm_t_of_mem_V {r : G} (hr : r ∈ V) : r * t * r⁻¹ * t⁻¹ = r ^ 2 :=
  SzC1.comm_eq_sq_of_inv (h.inv r hr)

theorem comm_t_of_mem_T₁ {y : G} (hy : y ∈ szT₁ L T) : y * t * y⁻¹ * t⁻¹ = 1 := by
  rw [h.t_comm hy]
  group

theorem mem_T₁_of_comm {z : G} (hz : z ∈ U₁) (hzt : z * t = t * z) : z ∈ szT₁ L T := by
  have hz' : z ∈ U ⊓ centralizer ({t} : Set G) :=
    mem_inf.mpr ⟨h.U₁_le hz, mem_centralizer_singleton_iff.mpr hzt⟩
  rw [h.inf_centralizer] at hz'
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers h.t_mul_self
    h.t_mem_normalizer_T₁ hz' with h1 | h1
  · exact h1
  · exact absurd (by simpa using mul_mem (inv_mem hz) (h.T₁_le_U₁ h1)) h.t_not_mem

theorem chi_mul_left {x x' : G} (hx : x ∈ U₁) (hx' : x' ∈ U₁) {r : G} (hr : r ∈ V) :
    r⁻¹ * (x * x' * r * (x * x')⁻¹) = r⁻¹ * (x * r * x⁻¹) * (r⁻¹ * (x' * r * x'⁻¹)) := by
  have h1 := h.conj_szA₁ x (h.U₁_le hx) _ (h.conj_V₁ x' hx' r hr)
  calc r⁻¹ * (x * x' * r * (x * x')⁻¹) =
        r⁻¹ * (x * r * x⁻¹) * (x * (r⁻¹ * (x' * r * x'⁻¹)) * x⁻¹) := by group
    _ = _ := by rw [h1]

theorem chi_mul_right {x : G} (hx : x ∈ U₁) {r r' : G} (hr : r ∈ V) (hr' : r' ∈ V) :
    (r * r')⁻¹ * (x * (r * r') * x⁻¹) = r⁻¹ * (x * r * x⁻¹) * (r'⁻¹ * (x * r' * x⁻¹)) := by
  have e1 : r'⁻¹ * (r⁻¹ * (x * r * x⁻¹)) = (r⁻¹ * (x * r * x⁻¹)) * r'⁻¹ :=
    h.comm _ (inv_mem hr') _ (h.le (h.conj_V₁ x hx r hr))
  calc (r * r')⁻¹ * (x * (r * r') * x⁻¹) = r'⁻¹ * (r⁻¹ * (x * r * x⁻¹)) * (x * r' * x⁻¹) := by
        group
    _ = (r⁻¹ * (x * r * x⁻¹)) * r'⁻¹ * (x * r' * x⁻¹) := by rw [e1]
    _ = _ := by group

theorem chi_eq_one_of_mem_sup {x : G} (hx : x ∈ szT₁ L T ⊔ V) {r : G} (hr : r ∈ V) :
    r⁻¹ * (x * r * x⁻¹) = 1 := by
  rw [← mem_centralizer_iff.mp (h.sup_le_centralizer_V hx) r hr]
  group

theorem conj_T₁_mem {x : G} (hx : x ∈ U) {y : G} (hy : y ∈ szT₁ L T) : x * y * x⁻¹ ∈ szT₁ L T := by
  have e : x * y * x⁻¹ = y * (y⁻¹ * (x * y * x⁻¹)) := by group
  rw [e]
  exact mul_mem hy (szA₁_le _ (h.conj_T₁ x hx y hy))

theorem delta_mul_left {x x' : G} (hx : x ∈ U) (hx' : x' ∈ U) {y : G} (hy : y ∈ szT₁ L T) :
    y⁻¹ * (x * x' * y * (x * x')⁻¹) = y⁻¹ * (x * y * x⁻¹) * (y⁻¹ * (x' * y * x'⁻¹)) := by
  have h1 := h.conj_szA₁ x hx _ (h.conj_T₁ x' hx' y hy)
  calc y⁻¹ * (x * x' * y * (x * x')⁻¹) =
        y⁻¹ * (x * y * x⁻¹) * (x * (y⁻¹ * (x' * y * x'⁻¹)) * x⁻¹) := by group
    _ = _ := by rw [h1]

theorem card_U₁ : Nat.card U₁ = (2 ^ f) ^ (k + 4) := by
  have h2 := RankOne.Endings.relIndex_sup_zpowers_eq_two h.t_not_mem h.t_mem_normalizer_U₁
    h.t_mul_self
  rw [h.sup_eq] at h2
  have h3 := relIndex_mul_card (H := U₁) (K := U)
  rw [h2, inf_of_le_left h.U₁_le, h.card_U] at h3
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3

theorem isPGroup_U : IsPGroup 2 U :=
  IsPGroup.of_card (n := 1 + f * (k + 4)) (by rw [h.card_U]; ring)

theorem comm_t_conj_d (y : G) :
    d⁻¹ * y * d * t * (d⁻¹ * y * d)⁻¹ * t⁻¹ = d⁻¹ * (y * t * y⁻¹ * t⁻¹) * d := by
  have hdt : d * t = t * d := (mem_centralizer_singleton_iff.mp h.d_norm.2)
  have e1 : d * t * d⁻¹ = t := by rw [hdt, mul_inv_cancel_right]
  have e2 : d * t⁻¹ * d⁻¹ = t⁻¹ := by rw [h.t_inv, e1]
  calc d⁻¹ * y * d * t * (d⁻¹ * y * d)⁻¹ * t⁻¹ =
        d⁻¹ * (y * (d * t * d⁻¹) * y⁻¹ * (d * t⁻¹ * d⁻¹)) * d := by group
    _ = _ := by rw [e1, e2]

theorem chi_eq_one_of_mem_szA₁ {x : G} (hx : x ∈ U₁) {b : G} (hb : b ∈ szA₁ (szT₁ L T)) :
    b⁻¹ * (x * b * x⁻¹) = 1 := by
  rw [h.conj_szA₁ x (h.U₁_le hx) b hb, inv_mul_cancel]

theorem szA₁_comm : ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), b * b' = b' * b :=
  fun b hb b' hb' => h.comm b (h.le hb) b' (h.le hb')

theorem conj_d_mem_U₁ {x : G} (hx : x ∈ U₁) : d⁻¹ * x * d ∈ U₁ := by
  simpa using (mem_normalizer_iff.mp (inv_mem h.d_mem_U₁) x).mp hx

theorem conj_d_mem_T₁ {y : G} (hy : y ∈ szT₁ L T) : d⁻¹ * y * d ∈ szT₁ L T := by
  simpa using (mem_normalizer_iff.mp (inv_mem h.d_norm.1.2) y).mp hy

theorem four_le_q : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.start.two_le

theorem one_lt_q : 1 < 2 ^ f := by have := h.four_le_q; omega

end Basic

section Facts

variable (h : U3C1Stage G L f t T d V U U₁ k)
include h

theorem card_T₁ : Nat.card (szT₁ L T) = (2 ^ f) ^ 3 :=
  (h.start.facts_of_card_sylow h.card_sylow).1

theorem card_szA₁ : Nat.card (szA₁ (szT₁ L T)) = 2 ^ f :=
  (h.start.facts_of_card_sylow h.card_sylow).2.1

theorem mem_szA₁_of_sq_eq_one {y : G} (hy : y ∈ szT₁ L T) (h2 : y ^ 2 = 1) :
    y ∈ szA₁ (szT₁ L T) :=
  (h.start.facts_of_card_sylow h.card_sylow).2.2.2.2.1 y hy h2

theorem sq_mem_szA₁ {y : G} (hy : y ∈ szT₁ L T) : y ^ 2 ∈ szA₁ (szT₁ L T) :=
  (h.start.facts_of_card_sylow h.card_sylow).2.2.2.1 y hy

theorem comm_T₁_mem {y y' : G} (hy : y ∈ szT₁ L T) (hy' : y' ∈ szT₁ L T) :
    y * y' * y⁻¹ * y'⁻¹ ∈ szA₁ (szT₁ L T) := by
  rw [(h.start.facts_of_card_sylow h.card_sylow).2.2.1]
  exact commutator_mem_commutator hy hy'

theorem relIndex_V_sup : V.relIndex (szT₁ L T ⊔ V) = (2 ^ f) ^ 2 := by
  rw [SzC1.relIndex_sup_eq_relIndex_inf h.T₁_le_normalizer_V, h.inf_eq_szA₁]
  have h1 := relIndex_mul_card (H := szA₁ (szT₁ L T)) (K := szT₁ L T)
  rw [inf_of_le_left (szA₁_le _), h.card_szA₁, h.card_T₁] at h1
  have h2 : (2 ^ f) ^ 3 = (2 ^ f) ^ 2 * 2 ^ f := by ring
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h1

theorem card_sup : Nat.card (szT₁ L T ⊔ V : Subgroup G) = (2 ^ f) ^ (k + 3) := by
  have h1 := relIndex_mul_card (H := V) (K := szT₁ L T ⊔ V)
  rw [inf_of_le_left le_sup_right, h.relIndex_V_sup, h.card] at h1
  rw [← h1]
  ring

theorem card_sup_lt : Nat.card (szT₁ L T ⊔ V : Subgroup G) < Nat.card U₁ := by
  rw [h.card_sup, h.card_U₁]
  exact Nat.pow_lt_pow_right h.one_lt_q (by omega)

theorem comm_t_mem {x : G} (hx : x ∈ U) : x * t * x⁻¹ * t⁻¹ ∈ V := by
  set z := x * t * x⁻¹ with hz
  have hzR : z ∈ szR (szT₁ L T) V t :=
    (mem_normalizer_iff.mp (h.U_le hx) t).mp (mem_szR_right _ V t)
  have hzU₁ : z ∉ U₁ := fun hz1 => h.t_not_mem (by
    have := h.conj_mem_U₁ (inv_mem hx) hz1
    rwa [hz, show x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t by group] at this)
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers h.t_mul_self
    h.t_mem_normalizer_sup hzR with h1 | h1
  · exact absurd (h.sup_le_U₁ h1) hzU₁
  · obtain ⟨y, hy, r, hr, hyr⟩ := h.exists_mul_of_mem_sup h1
    have hzt : z = y * r * t := by
      rw [← hyr, mul_assoc, h.t_mul_self, mul_one]
    have hsq : z ^ 2 = 1 := by
      rw [hz, sq, show x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ by group, h.t_mul_self,
        mul_one, mul_inv_cancel]
    rw [hzt, h.sq_mul_mul_t hy hr] at hsq
    have hyA := h.mem_szA₁_of_sq_eq_one hy hsq
    rw [h.t_inv, hyr]
    exact mul_mem (h.le hyA) hr

theorem comm_t_of_mem_sup {y r : G} (hy : y ∈ szT₁ L T) (hr : r ∈ V) :
    y * r * t * (y * r)⁻¹ * t⁻¹ = r ^ 2 := by
  rw [SzC1.comm_t_mul, h.comm_t_of_mem_V hr, h.comm_t_of_mem_T₁ hy, mul_one,
    mem_centralizer_iff.mp (h.le_centralizer (pow_mem hr 2)) y hy, mul_inv_cancel_right]

end Facts

section Coords

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {v : G → K}
  {μ : K} (h : U3C1Stage G L f t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : U3A₁Coords (szA₁ (szT₁ L T)) d v μ)
include h hK hc

theorem S_mul {x y : G} (hx : x ∈ U₁) (hy : y ∈ U₁) :
    v ((x * y * t * (x * y)⁻¹ * t⁻¹) ^ 2 ^ k) =
      v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) + v ((y * t * y⁻¹ * t⁻¹) ^ 2 ^ k) := by
  have hσy := h.comm_t_mem (h.U₁_le hy)
  have hσx := h.comm_t_mem (h.U₁_le hx)
  rw [SzC1.comm_t_mul, (Commute.mul_pow (h.comm _ (h.conj_V hx hσy) _ hσx) _), conj_pow,
    h.conj_szA₁ x (h.U₁_le hx) _ (h.pow_mem_szA₁ hσy),
    hc.mul _ (h.pow_mem_szA₁ hσy) _ (h.pow_mem_szA₁ hσx), add_comm]

theorem S_conj_d {x : G} (hx : x ∈ U₁) :
    v ((d⁻¹ * x * d * t * (d⁻¹ * x * d)⁻¹ * t⁻¹) ^ 2 ^ k) =
      μ * v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) := by
  have e : (d⁻¹ * (x * t * x⁻¹ * t⁻¹) * d) ^ 2 ^ k = d⁻¹ * (x * t * x⁻¹ * t⁻¹) ^ 2 ^ k * d := by
    simpa only [inv_inv] using conj_pow (a := d⁻¹) (b := x * t * x⁻¹ * t⁻¹) (i := 2 ^ k)
  rw [h.comm_t_conj_d x, e, hc.conj _ (h.pow_mem_szA₁ (h.comm_t_mem (h.U₁_le hx)))]

theorem S_eq_zero_of_mem_sup {x : G} (hx : x ∈ szT₁ L T ⊔ V) :
    v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) = 0 := by
  obtain ⟨y, hy, r, hr, rfl⟩ := h.exists_mul_of_mem_sup hx
  rw [h.comm_t_of_mem_sup hy hr, ← pow_mul, ← pow_succ', h.pow r hr, hc.v_one]

theorem mem_sup_of_S_eq_zero {x : G} (hx : x ∈ U₁) (h0 : v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) = 0) :
    x ∈ szT₁ L T ⊔ V := by
  have hσ := h.comm_t_mem (h.U₁_le hx)
  have h1 : (x * t * x⁻¹ * t⁻¹) ^ 2 ^ k = 1 := hc.eq_one_of_v_eq_zero (h.pow_mem_szA₁ hσ) h0
  obtain ⟨w, hw, hxw⟩ := SzC1.exists_sq_eq_of_pow_eq_one h.comm h.omega h.pow
    (by rw [h.card_szA₁, h.card]) hσ h1
  have hwx : w⁻¹ * x ∈ szT₁ L T := by
    refine h.mem_T₁_of_comm (mul_mem (inv_mem (h.V_le_U₁ hw)) hx) ?_
    have e1 : x * t * x⁻¹ = w * t * w⁻¹ := by
      rw [show x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t by group, hxw, ← h.comm_t_of_mem_V hw]
      group
    calc w⁻¹ * x * t = w⁻¹ * (x * t * x⁻¹) * x := by group
      _ = w⁻¹ * (w * t * w⁻¹) * x := by rw [e1]
      _ = t * (w⁻¹ * x) := by group
  have hmem : w * (w⁻¹ * x) ∈ szT₁ L T ⊔ V := mul_mem (mem_sup_right hw) (mem_sup_left hwx)
  rwa [mul_inv_cancel_left] at hmem

theorem exists_S_ne_zero : ∃ x ∈ U₁, v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) ≠ 0 := by
  by_contra hne
  push Not at hne
  have hle : U₁ ≤ szT₁ L T ⊔ V := fun x hx => h.mem_sup_of_S_eq_zero hK hc hx (hne x hx)
  exact absurd (Subgroup.card_le_of_le hle) (not_le.mpr h.card_sup_lt)

theorem S_surj (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) (s : K) :
    ∃ x ∈ U₁, v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) = s := by
  by_cases hs : s = 0
  · exact ⟨1, one_mem _, by simp [hs, hc.v_one]⟩
  obtain ⟨x₀, hx₀, hS₀⟩ := h.exists_S_ne_zero hK hc
  obtain ⟨m, hm⟩ := hμ (s / v ((x₀ * t * x₀⁻¹ * t⁻¹) ^ 2 ^ k)) (div_ne_zero hs hS₀)
  have key : ∀ n : ℕ, ∃ x ∈ U₁, v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) =
      μ ^ n * v ((x₀ * t * x₀⁻¹ * t⁻¹) ^ 2 ^ k) := by
    intro n
    induction n with
    | zero => exact ⟨x₀, hx₀, by rw [pow_zero, one_mul]⟩
    | succ n ih =>
      obtain ⟨x, hx, hxS⟩ := ih
      refine ⟨d⁻¹ * x * d, h.conj_d_mem_U₁ hx, ?_⟩
      rw [h.S_conj_d hK hc hx, hxS, pow_succ]
      ring
  obtain ⟨x, hx, hxS⟩ := key m
  exact ⟨x, hx, by rw [hxS, hm, div_mul_cancel₀ s hS₀]⟩

theorem exists_comm_t_eq (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) {r : G} (hr : r ∈ V) :
    ∃ y ∈ U₁, y * t * y⁻¹ * t⁻¹ = r := by
  obtain ⟨y₀, hy₀, hS⟩ := h.S_surj hK hc hμ (v (r ^ 2 ^ k))
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, σ₀ = y₀ * t * y₀⁻¹ * t⁻¹ := ⟨_, rfl⟩
  have hσ : σ₀ ∈ V := hσ₀ ▸ h.comm_t_mem (h.U₁_le hy₀)
  rw [← hσ₀] at hS
  have heq : σ₀ ^ 2 ^ k = r ^ 2 ^ k :=
    hc.inj _ (h.pow_mem_szA₁ hσ) _ (h.pow_mem_szA₁ hr) hS
  have h1 : (σ₀⁻¹ * r) ^ 2 ^ k = 1 := by
    rw [(Commute.mul_pow (h.comm _ (inv_mem hσ) _ hr) _), inv_pow, heq, inv_mul_cancel]
  obtain ⟨w, hw, hw2⟩ := SzC1.exists_sq_eq_of_pow_eq_one h.comm h.omega h.pow
    (by rw [h.card_szA₁, h.card]) (mul_mem (inv_mem hσ) hr) h1
  refine ⟨w * y₀, mul_mem (h.V_le_U₁ hw) hy₀, ?_⟩
  have hc1 : w * σ₀ * w⁻¹ = σ₀ := by rw [h.comm w hw σ₀ hσ, mul_inv_cancel_right]
  rw [SzC1.comm_t_mul, ← hσ₀, h.comm_t_of_mem_V hw, hc1, ← hw2]
  group

end Coords

end U3C1Stage

end CFSG.SeitzReduction.RankOne
