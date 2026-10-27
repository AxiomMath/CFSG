module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S4A

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem mem_normalizer_V₃ (h : d.Hyp) {g : G} (hgS : g ∈ normalizer (d.S₃ : Set G))
    (hgY : g ∈ normalizer (d.Y : Set G)) : g ∈ normalizer (d.V₃ : Set G) :=
  mem_normalizer_fintype fun x hx => by
    obtain ⟨hxS, hxc⟩ := (h.mem_V₃_iff).1 hx
    refine (h.mem_V₃_iff).2 ⟨(mem_normalizer_iff.1 hgS x).1 hxS, fun s hs => ?_⟩
    have hs' : g⁻¹ * s * g ∈ d.S₃ := by
      have := (mem_normalizer_iff.1 (inv_mem hgS) s).1 hs
      rwa [inv_inv] at this
    have := (mem_normalizer_iff.1 hgY _).1 (hxc _ hs')
    rwa [show g * (x * (g⁻¹ * s * g) * x⁻¹ * (g⁻¹ * s * g)⁻¹) * g⁻¹ =
      g * x * g⁻¹ * s * (g * x * g⁻¹)⁻¹ * s⁻¹ by group] at this

theorem NHS_le_normalizer_S₃ (h : d.Hyp) : normalizer (d.S : Set G) ⊓ d.H ≤
    normalizer (d.S₃ : Set G) := fun n hn => mem_normalizer_fintype fun x hx => by
  obtain ⟨hxR, hxc⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (h.NHS_le_normalizer_R₃ hn) x).1 hxR,
    mem_centralizer_iff.2 fun w hw => ?_⟩
  have hnW := h.NHS_le_normalizer_W hn
  have hw' : n⁻¹ * w * n ∈ d.W := by
    have := (mem_normalizer_iff.1 (inv_mem hnW) w).1 hw
    rwa [inv_inv] at this
  have e := mem_centralizer_iff.1 hxc _ hw'
  calc w * (n * x * n⁻¹) = n * ((n⁻¹ * w * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * w * n)) * n⁻¹ := by rw [e]
    _ = n * x * n⁻¹ * w := by group

theorem V₃_inf_H (h : d.Hyp) : d.V₃ ⊓ d.H = ⁅d.S, d.S⁆ := by
  refine le_antisymm (fun x hx => ?_) (le_inf ?_ ?_)
  · obtain ⟨hxV, hxH⟩ := Subgroup.mem_inf.1 hx
    have hxS : x ∈ d.S := by
      have : x ∈ d.S₃ ⊓ d.H := Subgroup.mem_inf.2 ⟨V₃_le_S₃ hxV, hxH⟩
      rwa [h.S₃_inf_H] at this
    have : x ∈ d.S ⊓ d.V₃ := Subgroup.mem_inf.2 ⟨hxS, hxV⟩
    rwa [h.S_inf_V₃] at this
  · intro x hx
    have : x ∈ d.S ⊓ d.V₃ := by
      rw [h.S_inf_V₃]
      exact hx
    exact this.2
  · intro x hx
    exact h.L_le_H (d.pull_le_L _ (d.A₂_le_S (commutator_S_le_A₂ hx)))

theorem commutator_S_le_V₃ (h : d.Hyp) : ⁅d.S, d.S⁆ ≤ d.V₃ := fun x hx => by
  have : x ∈ d.S ⊓ d.V₃ := by
    rw [h.S_inf_V₃]
    exact hx
  exact this.2

theorem V₃_le_centralizer_W : d.V₃ ≤ centralizer (d.W : Set G) := fun _ hx =>
  S₃_le_centralizer_W (V₃_le_S₃ hx)

theorem W_le_V₃ (h : d.Hyp) : d.W ≤ d.V₃ := fun w hw => h.Y_le_V₃ (d.W_le_Y hw)

theorem V₃_mul_self_mem_W (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    {x : G} (hx : x ∈ d.V₃) : x * x ∈ d.W := by
  have hV := h.V₃_eq hK
  have hTN : d.D₃ ⊓ d.D₂ ≤ normalizer (d.Y : Set G) := fun t ht =>
    mem_normalizer_of_forall_comm fun y hy => (D₂_comm_Y' (Subgroup.mem_inf.1 ht).2 hy).symm
  have hset := coe_mul_of_left_le_normalizer_right (d.D₃ ⊓ d.D₂) d.Y hTN
  obtain ⟨t, ht, y, hy, rfl⟩ : x ∈ ((d.D₃ ⊓ d.D₂ : Subgroup G) : Set G) * (d.Y : Set G) := by
    rw [← hset, ← hV]
    exact hx
  have hty : y * t = t * y := (D₂_comm_Y' (Subgroup.mem_inf.1 ht).2 hy).symm
  have e : t * y * (t * y) = (t * t) * (y * y) := by
    calc t * y * (t * y) = t * (y * t) * y := by group
      _ = t * (t * y) * y := by rw [hty]
      _ = (t * t) * (y * y) := by group
  rw [e, h.Y_sq hy, mul_one]
  exact h.D₁_mul_self_mem_W hK (D₃_le_D₁' (Subgroup.mem_inf.1 ht).1)

theorem t_mem_normalizer_V₃ (h : d.Hyp) : d.t ∈ normalizer (d.V₃ : Set G) := by
  refine h.mem_normalizer_V₃ ?_ ?_
  · rw [h.S₃_eq]
    exact h.t_mem_normalizer_SYD₃
  · exact mem_normalizer_fintype fun y hy => by
      rw [h.t_inv]
      exact h.t_conj_mem_Y hy

theorem exists_V₃_crossed (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    {k : G} (hk : k ∈ ⁅d.S, d.S⁆ ⊔ d.W) :
    ∃ v ∈ d.V₃, ∃ w ∈ d.W, v⁻¹ * d.t * v * d.t = k * w := by
  have hWc : ∀ w ∈ d.W, ∀ x ∈ d.S₃, w * x = x * w := fun w hw x hx =>
    mem_centralizer_iff.1 (S₃_le_centralizer_W hx) w hw
  have hKV : ⁅d.S, d.S⁆ ⊔ d.W ≤ d.V₃ := sup_le h.commutator_S_le_V₃ h.W_le_V₃
  let B₀ : Set G :=
    {k | k ∈ ⁅d.S, d.S⁆ ⊔ d.W ∧ ∃ v ∈ d.V₃, ∃ w ∈ d.W, v⁻¹ * d.t * v * d.t = k * w}
  have h1 : (1 : G) ∈ B₀ := ⟨one_mem _, 1, one_mem _, 1, one_mem _, by simp [h.t_mul_t]⟩
  have hmul : ∀ a ∈ B₀, ∀ b ∈ B₀, a * b ∈ B₀ := by
    rintro a ⟨haK, v₁, hv₁, w₁, hw₁, e₁⟩ b ⟨hbK, v₂, hv₂, w₂, hw₂, e₂⟩
    have hc₁ : v₁⁻¹ * d.t * v₁ * d.t ∈ d.V₃ := by
      rw [e₁]
      exact mul_mem (hKV haK) (h.W_le_V₃ hw₁)
    have hcomm : v₂⁻¹ * (v₁⁻¹ * d.t * v₁ * d.t) * v₂ * (v₁⁻¹ * d.t * v₁ * d.t)⁻¹ ∈ d.W := by
      have := h.V₃_commutator_mem_W hK (inv_mem hv₂) hc₁
      rwa [inv_inv] at this
    obtain ⟨c', hc', hc'e⟩ : ∃ c' ∈ d.W, v₂⁻¹ * (v₁⁻¹ * d.t * v₁ * d.t) * v₂ =
        c' * (v₁⁻¹ * d.t * v₁ * d.t) := ⟨_, hcomm, by group⟩
    have hprod : (v₁ * v₂)⁻¹ * d.t * (v₁ * v₂) * d.t =
        c' * (v₁⁻¹ * d.t * v₁ * d.t) * (v₂⁻¹ * d.t * v₂ * d.t) := by
      rw [← hc'e]
      calc (v₁ * v₂)⁻¹ * d.t * (v₁ * v₂) * d.t
          = v₂⁻¹ * v₁⁻¹ * d.t * v₁ * (d.t * d.t) * v₂ * d.t := by rw [h.t_mul_t]; group
        _ = v₂⁻¹ * (v₁⁻¹ * d.t * v₁ * d.t) * v₂ * (v₂⁻¹ * d.t * v₂ * d.t) := by group
    refine ⟨mul_mem haK hbK, v₁ * v₂, mul_mem hv₁ hv₂, c' * w₁ * w₂,
      mul_mem (mul_mem hc' hw₁) hw₂, ?_⟩
    rw [hprod, e₁, e₂]
    have haS₃ : a ∈ d.S₃ := V₃_le_S₃ (hKV haK)
    have hbS₃ : b ∈ d.S₃ := V₃_le_S₃ (hKV hbK)
    calc c' * (a * w₁) * (b * w₂) = (c' * a) * w₁ * b * w₂ := by group
      _ = (a * c') * w₁ * b * w₂ := by rw [hWc c' hc' a haS₃]
      _ = a * c' * (w₁ * b) * w₂ := by group
      _ = a * c' * (b * w₁) * w₂ := by rw [hWc w₁ hw₁ b hbS₃]
      _ = a * (c' * b) * w₁ * w₂ := by group
      _ = a * (b * c') * w₁ * w₂ := by rw [hWc c' hc' b hbS₃]
      _ = (a * b) * (c' * w₁ * w₂) := by group
  have hinvB : ∀ a ∈ B₀, a⁻¹ ∈ B₀ := fun a ha => by
    have hpow : ∀ n : ℕ, a ^ n ∈ B₀ := fun n => by
      induction n with
      | zero => simpa using h1
      | succ n ih => rw [pow_succ]; exact hmul _ ih _ ha
    have e : a⁻¹ = a ^ (orderOf a - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos a),
        pow_orderOf_eq_one]
    rw [e]
    exact hpow _
  let B : Subgroup G :=
    { carrier := B₀
      one_mem' := h1
      mul_mem' := fun {a b} ha hb => hmul a ha b hb
      inv_mem' := fun {a} ha => hinvB a ha }
  have hS'N : ∀ s ∈ d.S, ∀ k ∈ ⁅d.S, d.S⁆ ⊔ d.W, s * k * s⁻¹ ∈ ⁅d.S, d.S⁆ ⊔ d.W := fun s hs k hk =>
    (mem_normalizer_iff.1 (mem_normalizer_sup (le_normalizer_commutator_left' d.S d.S hs)
      (h.S_le_normalizer_W hs)) k).1 hk
  have hSinv : ∀ s ∈ d.S, ∀ k ∈ B₀, s * k * s⁻¹ ∈ B₀ := by
    rintro s hs k ⟨hkK, v, hv, w, hw, e⟩
    have hst : s * d.t = d.t * s := h.t_comm_of_mem_L (d.pull_le_L _ hs)
    refine ⟨hS'N s hs k hkK, s * v * s⁻¹, h.conj_mem_V₃ (h.S_le_S₃ hs) hv, s * w * s⁻¹,
      (mem_normalizer_iff.1 (h.S_le_normalizer_W hs) w).1 hw, ?_⟩
    rw [crossed_conj hst, e]
    group
  have hX₄ : d.X₄ ≤ B := fun a ha => by
    have haX : a ∈ d.X₃ ⊔ d.X₄ := mem_sup_right ha
    obtain ⟨u, hu, w, hw, e⟩ := h.exists_D₃_conj_t haX
    obtain ⟨x₂, hx₂, t₀, ht₀, rfl⟩ := h.exists_eq_mul_of_mem_D₃' hu
    have hx₂S : x₂ ∈ d.S := X₂_le_S' hx₂
    have hx₂R : x₂ ∈ d.R := mem_sup_left hx₂S
    have e1 := h.crossed_mul_of_mem_R hx₂R t₀
    rw [e1] at e
    have e2 : t₀ * d.t * t₀⁻¹ * d.t = (x₂⁻¹ * a * x₂) * (x₂⁻¹ * w * x₂) := by
      calc t₀ * d.t * t₀⁻¹ * d.t = x₂⁻¹ * (x₂ * (t₀ * d.t * t₀⁻¹ * d.t) * x₂⁻¹) * x₂ := by group
        _ = x₂⁻¹ * (a * w) * x₂ := by rw [e]
        _ = (x₂⁻¹ * a * x₂) * (x₂⁻¹ * w * x₂) := by group
    have ha' : x₂⁻¹ * a * x₂ ∈ B₀ := by
      refine ⟨?_, t₀⁻¹, inv_mem (D₃_inf_D₂_le_V₃ h hK ht₀), x₂⁻¹ * w * x₂, ?_, ?_⟩
      · have haS' : a ∈ ⁅d.S, d.S⁆ ⊔ d.W := by
          rw [commutator_S_eq]
          exact mem_sup_left (mem_sup_left ha)
        have := hS'N x₂⁻¹ (inv_mem hx₂S) a haS'
        rwa [inv_inv] at this
      · have := (mem_normalizer_iff.1 (inv_mem (h.S_le_normalizer_W hx₂S)) w).1 hw
        rwa [inv_inv] at this
      · rw [inv_inv, e2]
    have := hSinv x₂ hx₂S _ ha'
    rwa [show x₂ * (x₂⁻¹ * a * x₂) * x₂⁻¹ = a by group] at this
  have hF : d.F ≤ B := fun f hf => by
    obtain ⟨x, hx, e⟩ := h.exists_E₂_crossed_eq hf
    refine ⟨?_, x, h.Y_le_V₃ (h.Y_eq_E₂ ▸ hx), 1, one_mem _, by rw [mul_one]; exact e⟩
    rw [commutator_S_eq]
    exact mem_sup_left (mem_sup_right hf)
  have hW : d.W ≤ B := fun w hw => ⟨mem_sup_right hw, 1, one_mem _, w⁻¹, inv_mem hw, by
    rw [inv_one, one_mul, mul_one, h.t_mul_t, mul_inv_cancel]⟩
  have hall : ⁅d.S, d.S⁆ ⊔ d.W ≤ B := by
    rw [commutator_S_eq]
    exact sup_le (sup_le hX₄ hF) hW
  obtain ⟨-, v, hv, w, hw, e⟩ := hall hk
  exact ⟨v, hv, w, hw, e⟩

theorem commutator_S_le_H (h : d.Hyp) : ⁅d.S, d.S⁆ ≤ d.H := fun x hx =>
  h.L_le_H (d.pull_le_L _ (d.A₂_le_S (commutator_S_le_A₂ hx)))

theorem commutator_S_sup_W_le_V₃ (h : d.Hyp) : ⁅d.S, d.S⁆ ⊔ d.W ≤ d.V₃ :=
  sup_le h.commutator_S_le_V₃ h.W_le_V₃

theorem t_conj_mem_V₃ (h : d.Hyp) {k : G} (hk : k ∈ d.V₃) : d.t * k * d.t ∈ d.V₃ := by
  have := (mem_normalizer_iff.1 h.t_mem_normalizer_V₃ k).1 hk
  rwa [h.t_inv] at this

theorem V₃_le_normalizer_commutator_sup_W (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.V₃ ≤ normalizer ((⁅d.S, d.S⁆ ⊔ d.W : Subgroup G) : Set G) := fun v hv =>
  mem_normalizer_fintype fun k hk => by
    have hc := h.V₃_commutator_mem_W hK hv (h.commutator_S_sup_W_le_V₃ hk)
    rw [show v * k * v⁻¹ = (v * k * v⁻¹ * k⁻¹) * k by group]
    exact mul_mem (mem_sup_right hc) hk

theorem t_mem_normalizer_commutator_sup_W (h : d.Hyp) :
    d.t ∈ normalizer ((⁅d.S, d.S⁆ ⊔ d.W : Subgroup G) : Set G) :=
  mem_normalizer_sup (mem_normalizer_of_forall_comm fun s hs =>
      mem_centralizer_singleton_iff.1 (h.commutator_S_le_H hs))
    (mem_normalizer_fintype fun w hw => by
      rw [h.t_inv]
      exact h.t_conj_mem_W hw)

theorem commutator_S_sup_W_inf_H (h : d.Hyp) : (⁅d.S, d.S⁆ ⊔ d.W) ⊓ d.H = ⁅d.S, d.S⁆ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxK, hxH⟩ := Subgroup.mem_inf.1 hx
    have hN : ⁅d.S, d.S⁆ ≤ normalizer (d.W : Set G) := fun s hs =>
      h.S_le_normalizer_W (d.A₂_le_S (commutator_S_le_A₂ hs))
    have hset := coe_mul_of_left_le_normalizer_right ⁅d.S, d.S⁆ d.W hN
    obtain ⟨s, hs, w, hw, rfl⟩ : x ∈ ((⁅d.S, d.S⁆ : Subgroup G) : Set G) * (d.W : Set G) := by
      rw [← hset]
      exact hxK
    have hwH : w ∈ d.H := by
      have := mul_mem (inv_mem (h.commutator_S_le_H hs)) hxH
      rwa [inv_mul_cancel_left] at this
    have hwZ : w ∈ d.ZX₄ := by
      have : w ∈ d.W ⊓ d.H := Subgroup.mem_inf.2 ⟨hw, hwH⟩
      rwa [h.sec4_9_W.2.1] at this
    refine mul_mem hs ?_
    rw [commutator_S_eq]
    exact mem_sup_right (d.ZX₄_le_F hwZ)
  · exact le_inf le_sup_left h.commutator_S_le_H

theorem crossed_V₃_mem (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    {x : G} (hx : x ∈ d.V₃) : x * d.t * x⁻¹ * d.t ∈ ⁅d.S, d.S⁆ ⊔ d.W := by
  have hV := h.V₃_eq hK
  have hTN : d.D₃ ⊓ d.D₂ ≤ normalizer (d.Y : Set G) := fun t ht =>
    mem_normalizer_of_forall_comm fun y hy => (D₂_comm_Y' (Subgroup.mem_inf.1 ht).2 hy).symm
  have hset := coe_mul_of_left_le_normalizer_right (d.D₃ ⊓ d.D₂) d.Y hTN
  obtain ⟨u, hu, y, hy, rfl⟩ : x ∈ ((d.D₃ ⊓ d.D₂ : Subgroup G) : Set G) * (d.Y : Set G) := by
    rw [← hset, ← hV]
    exact hx
  obtain ⟨hu₃, hu₂⟩ := Subgroup.mem_inf.1 hu
  have hθy : y * d.t * y⁻¹ * d.t ∈ d.F := h.crossed_mem_F_of_mem_Y hy
  have hcomm : u * (y * d.t * y⁻¹ * d.t) * u⁻¹ = y * d.t * y⁻¹ * d.t := by
    rw [D₂_comm_Y' hu₂ (h.F_le_Y hθy), mul_inv_cancel_right]
  have hF : d.F ≤ ⁅d.S, d.S⁆ := by
    rw [commutator_S_eq]
    exact le_sup_right
  have hθu : u * d.t * u⁻¹ * d.t ∈ ⁅d.S, d.S⁆ ⊔ d.W := by
    obtain ⟨a, ha, w, hw, hθ⟩ := h.exists_eq_mul_of_mem_AW (h.theta_mem_AW (D₃_le_D₁' hu₃))
    have hD₀ : u * d.t * u⁻¹ * d.t ∈ d.D₀ := h.crossed_mem_D₀ (D₂_le_XC₀ hu₂)
    have haD₀ : a ∈ d.D₀ := by
      have : a = (u * d.t * u⁻¹ * d.t) * w⁻¹ := by rw [← hθ]; group
      rw [this]
      exact mul_mem hD₀ (inv_mem (Y_le_D₀ (d.W_le_Y hw)))
    have haS' : a ∈ ⁅d.S, d.S⁆ := by
      rw [commutator_S_eq]
      exact Data.Hyp.X₃₄_le_XF (h.A₁_inf_D₀_le ha haD₀)
    rw [← hθ]
    exact mul_mem (mem_sup_left haS') (mem_sup_right hw)
  rw [h.crossed_mul_eq u y, hcomm]
  exact mul_mem (mem_sup_left (hF hθy)) hθu

theorem commutator_withT_V₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    ⁅d.V₃ ⊔ zpowers d.t, d.V₃ ⊔ zpowers d.t⁆ = ⁅d.S, d.S⁆ ⊔ d.W := by
  have hWP : d.W ≤ ⁅d.V₃ ⊔ zpowers d.t, d.V₃ ⊔ zpowers d.t⁆ := by
    rw [← h.commutator_V₃_eq_W hK]
    exact Subgroup.commutator_mono le_sup_left le_sup_left
  apply le_antisymm
  · refine commutator_sup_le_of (h.V₃_le_normalizer_commutator_sup_W hK)
      (zpowers_le.2 h.t_mem_normalizer_commutator_sup_W) (fun a ha a' ha' => ?_)
      (fun b hb b' hb' => ?_) (fun a ha b hb => ?_)
    · rw [commutatorElement_def]
      exact mem_sup_right (h.V₃_commutator_mem_W hK ha ha')
    · have : ⁅b, b'⁆ = 1 := by
        rcases h.eq_one_or_eq_t hb with rfl | rfl <;>
          rcases h.eq_one_or_eq_t hb' with rfl | rfl <;> simp [commutatorElement_def]
      rw [this]
      exact one_mem _
    · rcases h.eq_one_or_eq_t hb with rfl | rfl
      · have : ⁅a, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
        rw [this]
        exact one_mem _
      · rw [commutatorElement_def, h.t_inv]
        exact h.crossed_V₃_mem hK ha
  · refine sup_le (fun k hk => ?_) hWP
    obtain ⟨v, hv, w, hw, e⟩ := h.exists_V₃_crossed hK (mem_sup_left hk)
    have h1 := commutator_mem_commutator
      (mem_sup_left (inv_mem hv) : v⁻¹ ∈ d.V₃ ⊔ zpowers d.t)
      (mem_sup_right (mem_zpowers d.t) : d.t ∈ d.V₃ ⊔ zpowers d.t)
    rw [commutatorElement_def, h.t_inv, inv_inv, e] at h1
    have := mul_mem h1 (inv_mem (hWP hw))
    rwa [mul_inv_cancel_right] at this

theorem withT_V₃_inf_centralizer_K (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    (d.V₃ ⊔ zpowers d.t) ⊓ centralizer ((⁅d.S, d.S⁆ ⊔ d.W : Subgroup G) : Set G) = d.Y := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxc⟩ := Subgroup.mem_inf.1 hx
    have hxV : x ∈ d.V₃ := by
      rcases (mem_sup_zpowers_iff h.t_mul_t fun k hk => h.t_conj_mem_V₃ hk).1 hxP with h1 | h1
      · exact h1
      · exfalso
        apply h.t_not_mem_centralizer_W
        have hxW : x ∈ centralizer (d.W : Set G) := mem_centralizer_iff.2 fun w hw =>
          mem_centralizer_iff.1 hxc w (show w ∈ ⁅d.S, d.S⁆ ⊔ d.W from mem_sup_right hw)
        have := mul_mem (inv_mem hxW) (V₃_le_centralizer_W h1)
        rwa [inv_mul_cancel_left] at this
    have hxS' : x ∈ centralizer ((⁅d.S, d.S⁆ : Subgroup G) : Set G) :=
      mem_centralizer_iff.2 fun k hk =>
        mem_centralizer_iff.1 hxc k (show k ∈ ⁅d.S, d.S⁆ ⊔ d.W from mem_sup_left hk)
    have : x ∈ d.S₃ ⊓ centralizer ((⁅d.S, d.S⁆ : Subgroup G) : Set G) :=
      Subgroup.mem_inf.2 ⟨V₃_le_S₃ hxV, hxS'⟩
    rwa [h.S₃_inf_centralizer_commutator_S] at this
  · intro y hy
    exact Subgroup.mem_inf.2 ⟨mem_sup_left (h.Y_le_V₃ hy), mem_centralizer_iff.2 fun k hk =>
      D₂_comm_Y' (h.V₃_le_D₂ hK (h.commutator_S_sup_W_le_V₃ hk)) hy⟩

theorem withT_V₃_inf_centralizer_Y (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    (d.V₃ ⊔ zpowers d.t) ⊓ centralizer (d.Y : Set G) = d.V₃ := by
  have hV₃C : d.V₃ ≤ centralizer (d.Y : Set G) := fun v hv =>
    mem_centralizer_iff.2 fun y hy => (D₂_comm_Y' (h.V₃_le_D₂ hK hv) hy).symm
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxc⟩ := Subgroup.mem_inf.1 hx
    rcases (mem_sup_zpowers_iff h.t_mul_t fun k hk => h.t_conj_mem_V₃ hk).1 hxP with h1 | h1
    · exact h1
    · exfalso
      apply h.t_not_mem_centralizer_Y
      have := mul_mem (inv_mem hxc) (hV₃C h1)
      rwa [inv_mul_cancel_left] at this
  · exact le_inf le_sup_left hV₃C

theorem normalizer_withT_V₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    normalizer ((d.V₃ ⊔ zpowers d.t : Subgroup G) : Set G) =
      (normalizer (d.S : Set G) ⊓ d.H) ⊔ d.V₃ := by
  have hKV := h.commutator_S_sup_W_le_V₃
  have hN9 := h.sec4_9.2.2.1
  have hNW : normalizer (d.A₁ : Set G) ⊓ d.H ≤ normalizer (d.W : Set G) := fun n hn =>
    (Subgroup.mem_inf.1 (h.NHA₁_le_XW hn)).2
  have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.A₁ : Set G) ⊓ d.H) d.W hNW
  apply le_antisymm
  · intro g hg
    have hPK := h.commutator_withT_V₃ hK
    have hgK : g ∈ normalizer ((⁅d.S, d.S⁆ ⊔ d.W : Subgroup G) : Set G) :=
      mem_normalizer_fintype fun x hx => by
        rw [← hPK] at hx ⊢
        exact conj_mem_commutator_of_mem_normalizer hg hx
    have hgY : g ∈ normalizer (d.Y : Set G) := by
      refine mem_normalizer_fintype fun y hy => ?_
      rw [← h.withT_V₃_inf_centralizer_K hK]
      refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 hg y).1 (mem_sup_left (h.Y_le_V₃ hy)),
        mem_centralizer_iff.2 fun k hk => ?_⟩
      have hk' : g⁻¹ * k * g ∈ ⁅d.S, d.S⁆ ⊔ d.W := by
        have := (mem_normalizer_iff.1 (inv_mem hgK) k).1 hk
        rwa [inv_inv] at this
      have e : (g⁻¹ * k * g) * y = y * (g⁻¹ * k * g) :=
        D₂_comm_Y' (h.V₃_le_D₂ hK (hKV hk')) hy
      calc k * (g * y * g⁻¹) = g * ((g⁻¹ * k * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * k * g)) * g⁻¹ := by rw [e]
        _ = (g * y * g⁻¹) * k := by group
    have hgV : g ∈ normalizer (d.V₃ : Set G) := by
      refine mem_normalizer_fintype fun v hv => ?_
      rw [← h.withT_V₃_inf_centralizer_Y hK]
      refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 hg v).1 (mem_sup_left hv),
        mem_centralizer_iff.2 fun y hy => ?_⟩
      have hy' : g⁻¹ * y * g ∈ d.Y := by
        have := (mem_normalizer_iff.1 (inv_mem hgY) y).1 hy
        rwa [inv_inv] at this
      have e : v * (g⁻¹ * y * g) = (g⁻¹ * y * g) * v := D₂_comm_Y' (h.V₃_le_D₂ hK hv) hy'
      calc y * (g * v * g⁻¹) = g * ((g⁻¹ * y * g) * v) * g⁻¹ := by group
        _ = g * (v * (g⁻¹ * y * g)) * g⁻¹ := by rw [e]
        _ = (g * v * g⁻¹) * y := by group
    have hgW : g ∈ normalizer (d.W : Set G) := mem_normalizer_fintype fun w hw => by
      rw [← h.commutator_V₃_eq_W hK] at hw ⊢
      exact conj_mem_commutator_of_mem_normalizer hgV hw
    rcases conj_t_cases h.t_mul_t (fun k hk => h.t_conj_mem_V₃ hk) hg with
      hD | ⟨e, he, heq, hinv⟩
    · exfalso
      apply h.t_not_mem_centralizer_W
      refine mem_centralizer_iff.2 fun w' hw' => ?_
      have hw : g * w' * g⁻¹ ∈ d.W := (mem_normalizer_iff.1 hgW w').1 hw'
      have h1 := mem_centralizer_iff.1 (V₃_le_centralizer_W hD) _ hw
      have e1 : g * (w' * d.t) * g⁻¹ = g * (d.t * w') * g⁻¹ := by
        calc g * (w' * d.t) * g⁻¹ = (g * w' * g⁻¹) * (g * d.t * g⁻¹) := by group
          _ = (g * d.t * g⁻¹) * (g * w' * g⁻¹) := h1
          _ = g * (d.t * w') * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e1)
    · have hθ : e * d.t * e⁻¹ * d.t = e * e := h.crossed_eq_mul_self hinv
      have hee : e * e ∈ d.W := h.V₃_mul_self_mem_W hK he
      have heC : e ∈ centralizer (d.W : Set G) := V₃_le_centralizer_W he
      have heN : e ∈ normalizer ((d.withT d.W : Subgroup G) : Set G) := by
        refine mem_normalizer_fintype fun x hx => ?_
        have hle : d.withT d.W ≤ (d.withT d.W).comap (MulAut.conj e).toMonoidHom := by
          refine sup_le (fun w hw => ?_) (zpowers_le.2 ?_)
          · change e * w * e⁻¹ ∈ d.withT d.W
            rw [← mem_centralizer_iff.1 heC w hw, mul_inv_cancel_right]
            exact mem_sup_left hw
          · change e * d.t * e⁻¹ ∈ d.withT d.W
            have : e * d.t * e⁻¹ = (e * e) * d.t := by
              calc e * d.t * e⁻¹ = (e * d.t * e⁻¹ * d.t) * d.t := by
                    rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
                _ = (e * e) * d.t := by rw [hθ]
            rw [this]
            exact mul_mem (mem_sup_left hee) (mem_sup_right (mem_zpowers _))
        exact hle hx
      rw [hN9] at heN
      obtain ⟨n, hn, w₀, hw₀, hnw⟩ : e ∈ ((normalizer (d.A₁ : Set G) ⊓ d.H : Subgroup G) :
          Set G) * (d.W : Set G) := by
        rw [← hset]
        exact heN
      have hnV : n ∈ d.V₃ := by
        have : n = e * w₀⁻¹ := by rw [← hnw]; group
        rw [this]
        exact mul_mem he (inv_mem (h.W_le_V₃ hw₀))
      have hnS' : n ∈ ⁅d.S, d.S⁆ := by
        have : n ∈ d.V₃ ⊓ d.H := Subgroup.mem_inf.2 ⟨hnV, hn.2⟩
        rwa [h.V₃_inf_H] at this
      have heK : e ∈ ⁅d.S, d.S⁆ ⊔ d.W := by
        rw [← hnw]
        exact mul_mem (mem_sup_left hnS') (mem_sup_right hw₀)
      obtain ⟨v, hv, w₁, hw₁, hvθ⟩ := h.exists_V₃_crossed hK (inv_mem heK)
      have hc : v⁻¹ * e * v⁻¹⁻¹ * e⁻¹ ∈ d.W := h.V₃_commutator_mem_W hK (inv_mem hv) he
      have hv1 : v⁻¹ * d.t * v = e⁻¹ * w₁ * d.t := by
        calc v⁻¹ * d.t * v = (v⁻¹ * d.t * v * d.t) * d.t := by
              rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
          _ = e⁻¹ * w₁ * d.t := by rw [hvθ]
      have hg₁t : (v⁻¹ * g) * d.t * (v⁻¹ * g)⁻¹ = ((v⁻¹ * e * v⁻¹⁻¹ * e⁻¹) * w₁) * d.t := by
        calc (v⁻¹ * g) * d.t * (v⁻¹ * g)⁻¹ = v⁻¹ * (g * d.t * g⁻¹) * v := by group
          _ = v⁻¹ * (e * d.t) * v := by rw [heq]
          _ = (v⁻¹ * e * v) * (v⁻¹ * d.t * v) := by group
          _ = (v⁻¹ * e * v) * (e⁻¹ * w₁ * d.t) := by rw [hv1]
          _ = ((v⁻¹ * e * v⁻¹⁻¹ * e⁻¹) * w₁) * d.t := by group
      have hv'W : v⁻¹ ∈ normalizer (d.W : Set G) := mem_normalizer_of_forall_comm fun w hw =>
        mem_centralizer_iff.1 (inv_mem (V₃_le_centralizer_W hv)) w hw
      have hg₁W : v⁻¹ * g ∈ normalizer (d.W : Set G) := mul_mem hv'W hgW
      have hg₁N : v⁻¹ * g ∈ normalizer ((d.withT d.W : Subgroup G) : Set G) := by
        refine mem_normalizer_fintype fun x hx => ?_
        have hle : d.withT d.W ≤ (d.withT d.W).comap (MulAut.conj (v⁻¹ * g)).toMonoidHom := by
          refine sup_le (fun w hw => ?_) (zpowers_le.2 ?_)
          · exact mem_sup_left ((mem_normalizer_iff.1 hg₁W w).1 hw)
          · change (v⁻¹ * g) * d.t * (v⁻¹ * g)⁻¹ ∈ d.withT d.W
            rw [hg₁t]
            exact mul_mem (mem_sup_left (mul_mem hc hw₁)) (mem_sup_right (mem_zpowers _))
        exact hle hx
      rw [hN9] at hg₁N
      obtain ⟨n₁, hn₁, w₂, hw₂, hnw₂⟩ : v⁻¹ * g ∈ ((normalizer (d.A₁ : Set G) ⊓ d.H :
          Subgroup G) : Set G) * (d.W : Set G) := by
        rw [← hset]
        exact hg₁N
      have hn₁K : n₁ ∈ normalizer ((⁅d.S, d.S⁆ ⊔ d.W : Subgroup G) : Set G) := by
        have : n₁ = v⁻¹ * g * w₂⁻¹ := by rw [← hnw₂]; group
        rw [this]
        exact mul_mem (mul_mem (h.V₃_le_normalizer_commutator_sup_W hK (inv_mem hv)) hgK)
          (h.V₃_le_normalizer_commutator_sup_W hK (inv_mem (h.W_le_V₃ hw₂)))
      have hn₁H : n₁ ∈ d.H := hn₁.2
      have hn₁XF : n₁ ∈ normalizer ((d.X₄ ⊔ d.F : Subgroup G) : Set G) := by
        refine mem_normalizer_fintype fun x hx => ?_
        rw [← commutator_S_eq] at hx ⊢
        have h1 := (mem_normalizer_iff.1 hn₁K x).1 (mem_sup_left hx)
        have h2 : n₁ * x * n₁⁻¹ ∈ d.H :=
          mul_mem (mul_mem hn₁H (h.commutator_S_le_H hx)) (inv_mem hn₁H)
        have := Subgroup.mem_inf.2 ⟨h1, h2⟩
        rwa [h.commutator_S_sup_W_inf_H] at this
      have hn₁S : n₁ ∈ normalizer (d.S : Set G) :=
        h.mem_normalizer_S_of_mem_normalizer_XF hn₁H hn₁XF
      have hnw₂' : n₁ * w₂ = v⁻¹ * g := hnw₂
      have hgeq : g = v * (n₁ * w₂) := by rw [hnw₂']; group
      rw [hgeq]
      exact mul_mem (mem_sup_right hv) (mul_mem (mem_sup_left (Subgroup.mem_inf.2 ⟨hn₁S, hn₁H⟩))
        (mem_sup_right (h.W_le_V₃ hw₂)))
  · refine sup_le (fun n hn => ?_) (fun v hv => ?_)
    · exact mem_normalizer_withT_of_comm (h.mem_normalizer_V₃ (h.NHS_le_normalizer_S₃ hn)
        (h.NHS_le_normalizer_Y hn)) (mem_centralizer_singleton_iff.1 hn.2)
    · exact (d.V₃ ⊔ zpowers d.t).le_normalizer (mem_sup_left hv)

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
