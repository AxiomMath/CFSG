module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S5D

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem commutator_R₃_le_V₃ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    ⁅d.R₃, d.R₃⁆ ≤ d.V₃ := by
  rw [h.R₃_eq_S₃_sup]
  refine commutator_sup_le_of h.S₃_le_normalizer_V₃ (zpowers_le.2 h.t_mem_normalizer_V₃)
    (fun a ha a' ha' => h.commutator_mem_V₃_of_mem_S₃ hK ha ha') (fun b hb b' hb' => ?_)
    (fun a ha b hb => ?_)
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
      exact h.theta_mem_V₃_of_mem_S₃ hK ha

theorem S'W_le_commutator_R₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    ⁅d.S, d.S⁆ ⊔ d.W ≤ ⁅d.R₃, d.R₃⁆ := by
  rw [← h.commutator_withT_V₃ hK]
  have : d.V₃ ⊔ zpowers d.t ≤ d.R₃ := sup_le (V₃_le_S₃.trans S₃_le_R₃)
    (zpowers_le.2 (h.R_le_R₃ (mem_sup_right (mem_zpowers _))))
  exact Subgroup.commutator_mono this this

theorem Y_le_centralizer_commutator_R₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.Y ≤ centralizer ((⁅d.R₃, d.R₃⁆ : Subgroup G) : Set G) := fun y hy =>
  mem_centralizer_iff.2 fun r hr =>
    D₂_comm_Y' (h.V₃_le_D₂ hK (h.commutator_R₃_le_V₃ hK hr)) hy

theorem centralizer_commutator_R₃_inf_R₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    centralizer ((⁅d.R₃, d.R₃⁆ : Subgroup G) : Set G) ⊓ d.R₃ = d.Y := by
  refine le_antisymm (fun x hx => ?_) (le_inf (h.Y_le_centralizer_commutator_R₃ hK) h.Y_le_R₃)
  obtain ⟨hxC, hxR⟩ := Subgroup.mem_inf.1 hx
  have hxR' : x ∈ d.S₃ ⊔ zpowers d.t := by rwa [h.R₃_eq_S₃_sup] at hxR
  have hsw := h.S'W_le_commutator_R₃ hK
  rcases (mem_sup_zpowers_iff h.t_mul_t fun k hk => h.t_conj_mem_S₃ hk).1 hxR' with h1 | h1
  · have : x ∈ d.S₃ ⊓ centralizer ((⁅d.S, d.S⁆ : Subgroup G) : Set G) :=
      Subgroup.mem_inf.2 ⟨h1, mem_centralizer_iff.2 fun k hk =>
        mem_centralizer_iff.1 hxC k (hsw (mem_sup_left hk))⟩
    rwa [h.S₃_inf_centralizer_commutator_S] at this
  · exfalso
    apply h.t_not_mem_centralizer_W
    have hxW : x ∈ centralizer (d.W : Set G) := mem_centralizer_iff.2 fun w hw =>
      mem_centralizer_iff.1 hxC w (hsw (mem_sup_right hw))
    have := mul_mem (inv_mem hxW) (S₃_le_centralizer_W h1)
    rwa [inv_mul_cancel_left] at this

theorem normalizer_R₃_le_normalizer_Y (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    normalizer (d.R₃ : Set G) ≤ normalizer (d.Y : Set G) := fun g hg => by
  refine mem_normalizer_fintype fun y hy => ?_
  rw [← h.centralizer_commutator_R₃_inf_R₃ hK]
  refine Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun r hr => ?_,
    (mem_normalizer_iff.1 hg y).1 (h.Y_le_R₃ hy)⟩
  have hr' : g⁻¹ * r * g ∈ ⁅d.R₃, d.R₃⁆ := by
    have := conj_mem_commutator_self_of_mem_normalizer (inv_mem hg) hr
    rwa [inv_inv] at this
  have hyc := mem_centralizer_iff.1 (h.Y_le_centralizer_commutator_R₃ hK hy) _ hr'
  calc r * (g * y * g⁻¹) = g * ((g⁻¹ * r * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * r * g)) * g⁻¹ := by rw [hyc]
    _ = (g * y * g⁻¹) * r := by group

theorem V₃_inf_A₂ (h : d.Hyp) : d.V₃ ⊓ d.A₂ = ⁅d.S, d.S⁆ := by
  refine le_antisymm (fun x hx => ?_) (le_inf h.commutator_S_le_V₃ commutator_S_le_A₂)
  obtain ⟨hxV, hxA⟩ := Subgroup.mem_inf.1 hx
  have : x ∈ d.S ⊓ d.V₃ := Subgroup.mem_inf.2 ⟨d.A₂_le_S hxA, hxV⟩
  rwa [h.S_inf_V₃] at this

theorem V₃_inf_A₁ (h : d.Hyp) : d.V₃ ⊓ d.A₁ = ⁅d.S, d.S⁆ ⊓ d.A₁ := by
  refine le_antisymm (fun x hx => ?_) (inf_le_inf_right _ h.commutator_S_le_V₃)
  obtain ⟨hxV, hxA⟩ := Subgroup.mem_inf.1 hx
  have : x ∈ d.S ⊓ d.V₃ := Subgroup.mem_inf.2 ⟨d.A₁_le_S hxA, hxV⟩
  rw [h.S_inf_V₃] at this
  exact Subgroup.mem_inf.2 ⟨this, hxA⟩

theorem card_commutator_S_inf_A₁ (h : d.Hyp) :
    Nat.card (⁅d.S, d.S⁆ ⊓ d.A₁ : Subgroup G) = 2 ^ 5 := by
  have hFN : d.A₁ ≤ normalizer (d.F : Set G) := fun g hg =>
    normalizer_S_le_normalizer_F (d.S.le_normalizer (d.A₁_le_S hg))
  have hSN : d.A₁ ≤ normalizer ((⁅d.S, d.S⁆ : Subgroup G) : Set G) := fun g hg =>
    le_normalizer_commutator_left' d.S d.S (d.A₁_le_S hg)
  have e1 := card_sup_mul_card_inf_of_le_normalizer d.F d.A₁ hFN
  have e2 := card_sup_mul_card_inf_of_le_normalizer ⁅d.S, d.S⁆ d.A₁ hSN
  have hFA : d.F ⊓ d.A₁ = d.Z₂ := (Z₂_eq (d := d)).symm
  have hsup : (⁅d.S, d.S⁆ ⊔ d.A₁ : Subgroup G) = d.F ⊔ d.A₁ := by
    rw [commutator_S_eq]
    refine le_antisymm (sup_le (sup_le ?_ ?_) le_sup_right) (sup_le_sup_right ?_ _)
    · exact (d.pull_mono X₄sub_le_A₁sub').trans le_sup_right
    · exact le_sup_left
    · exact le_sup_right
  rw [hFA, card_Z₂, d.card_F, d.card_A₁] at e1
  rw [hsup, card_commutator_S, d.card_A₁] at e2
  have hc : Nat.card (d.F ⊔ d.A₁ : Subgroup G) = 2 ^ 8 := by omega
  rw [hc] at e2
  omega

theorem card_V₃_sup_A₂ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    Nat.card (d.V₃ ⊔ d.A₂ : Subgroup G) = 2 ^ 14 := by
  have e := card_sup_mul_card_inf_of_le_normalizer d.V₃ d.A₂ fun g hg =>
    h.S_le_normalizer_V₃ (d.A₂_le_S hg)
  rw [h.V₃_inf_A₂, card_commutator_S, h.card_V₃ hK, d.card_A₂] at e
  omega

theorem card_V₃_sup_A₁ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    Nat.card (d.V₃ ⊔ d.A₁ : Subgroup G) = 2 ^ 14 := by
  have e := card_sup_mul_card_inf_of_le_normalizer d.V₃ d.A₁ fun g hg =>
    h.S_le_normalizer_V₃ (d.A₁_le_S hg)
  rw [h.V₃_inf_A₁, h.card_commutator_S_inf_A₁, h.card_V₃ hK, d.card_A₁] at e
  omega

theorem sup_V₃_comm_sq_mem_Y' (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {P' : Subgroup G} (hP'S : P' ≤ d.S₃)
    (hc : ∀ x ∈ P', ∀ y ∈ P', x * y * x⁻¹ * y⁻¹ ∈ d.Y) (hs : ∀ x ∈ P', x * x ∈ d.Y) :
    (∀ x ∈ P' ⊔ d.V₃, ∀ y ∈ P' ⊔ d.V₃, x * y * x⁻¹ * y⁻¹ ∈ d.Y) ∧
      ∀ x ∈ P' ⊔ d.V₃, x * x ∈ d.Y := by
  have hset := coe_mul_of_left_le_normalizer_right P' d.V₃ fun g hg =>
    mem_normalizer_fintype fun x hx => h.conj_mem_V₃ (hP'S hg) hx
  have hN : ∀ g ∈ d.S₃, ∀ y ∈ d.Y, g * y * g⁻¹ ∈ d.Y := fun g hg y hy =>
    (mem_normalizer_iff.1 (h.S₃_le_normalizer_Y hg) y).1 hy
  constructor
  · intro x hx y hy
    obtain ⟨s, hs, v, hv, rfl⟩ : x ∈ (P' : Set G) * (d.V₃ : Set G) := by
      rw [← hset]
      exact hx
    obtain ⟨s', hs', v', hv', rfl⟩ : y ∈ (P' : Set G) * (d.V₃ : Set G) := by
      rw [← hset]
      exact hy
    have hsS := hP'S hs
    have hs'S := hP'S hs'
    have hc₁ : v * s' * v⁻¹ * s'⁻¹ ∈ d.Y := (h.mem_V₃_iff.1 hv).2 s' hs'S
    have hc₂ : v * v' * v⁻¹ * v'⁻¹ ∈ d.Y := (h.mem_V₃_iff.1 hv).2 v' (V₃_le_S₃ hv')
    have hc₃ : v' * s⁻¹ * v'⁻¹ * s ∈ d.Y := by
      have := (h.mem_V₃_iff.1 hv').2 s⁻¹ (inv_mem hsS)
      rwa [inv_inv] at this
    have e : s * v * (s' * v') * (s * v)⁻¹ * (s' * v')⁻¹ =
        (s * (v * s' * v⁻¹ * s'⁻¹) * s⁻¹) *
          ((s * s') * ((v * v' * v⁻¹ * v'⁻¹) * (v' * s⁻¹ * v'⁻¹ * s)) * (s * s')⁻¹) *
          (s * s' * s⁻¹ * s'⁻¹) := by group
    rw [e]
    exact mul_mem (mul_mem (hN s hsS _ hc₁) (hN (s * s') (mul_mem hsS hs'S) _ (mul_mem hc₂ hc₃)))
      (hc s hs s' hs')
  · intro x hx
    obtain ⟨s, hs', v, hv, rfl⟩ : x ∈ (P' : Set G) * (d.V₃ : Set G) := by
      rw [← hset]
      exact hx
    have hsS := hP'S hs'
    have hc : v * s * v⁻¹ * s⁻¹ ∈ d.Y := (h.mem_V₃_iff.1 hv).2 s hsS
    have e : s * v * (s * v) = (s * (v * s * v⁻¹ * s⁻¹) * s⁻¹) * (s * s) * (v * v) := by group
    rw [e]
    exact mul_mem (mul_mem (hN s hsS _ hc) (hs s hs')) (h.D₂_mul_self_mem_Y hK
      (h.V₃_le_D₂ hK hv))

theorem R₃_le_normalizer_S₃ (h : d.Hyp) : d.R₃ ≤ normalizer (d.S₃ : Set G) := by
  rw [h.R₃_eq_S₃_sup]
  refine sup_le d.S₃.le_normalizer (zpowers_le.2 (mem_normalizer_fintype fun k hk => ?_))
  rw [h.t_inv]
  exact h.t_conj_mem_S₃ hk

theorem card_R₃ (h : d.Hyp) : Nat.card d.R₃ = 2 ^ 17 := h.sec4_13_3.2.2.2.2.2.1

theorem mem_commutator_S_sup_Y_of_theta_mem_Y (h : d.Hyp) {v : G} (hv : v ∈ d.V₃)
    (hθ : v * d.t * v⁻¹ * d.t ∈ d.Y) : v ∈ ⁅d.S, d.S⁆ ⊔ d.Y := by
  have hvX : v ∈ d.XC₀ := h.R₃_le_XC₀ (S₃_le_R₃ (V₃_le_S₃ hv))
  have hxNY := h.mem_NHA₂Y_of_crossed_mem hvX hθ
  have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.A₂ : Set G) ⊓ d.H) d.Y
    h.NHA₂_le_normalizer_Y
  obtain ⟨n, hn, y, hy, rfl⟩ : v ∈ ((normalizer (d.A₂ : Set G) ⊓ d.H : Subgroup G) : Set G) *
      (d.Y : Set G) := by
    rw [← hset]
    exact hxNY
  have hnV : n ∈ d.V₃ := by
    have := mul_mem hv (inv_mem (h.Y_le_V₃ hy))
    rwa [mul_inv_cancel_right] at this
  have hnS' : n ∈ ⁅d.S, d.S⁆ := by
    have : n ∈ d.V₃ ⊓ d.H := Subgroup.mem_inf.2 ⟨hnV, hn.2⟩
    rwa [h.V₃_inf_H] at this
  exact mul_mem (mem_sup_left hnS') (mem_sup_right hy)

theorem le_S₃_of_elemAb (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    {B : Subgroup G} (hBR : B ≤ d.R₃) (hc : ∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ d.Y)
    (hs : ∀ x ∈ B, x * x ∈ d.Y) (hcard : 2 ^ 14 ≤ Nat.card B) : B ≤ d.S₃ := by
  by_contra hBS
  obtain ⟨b, hbB, hbS⟩ := SetLike.not_le_iff_exists.1 hBS
  have hbR : b ∈ d.S₃ ⊔ zpowers d.t := by
    rw [← h.R₃_eq_S₃_sup]
    exact hBR hbB
  obtain ⟨s, hsS₃, hbs⟩ : ∃ s ∈ d.S₃, b = s * d.t := by
    rcases (mem_sup_zpowers_iff h.t_mul_t fun k hk => h.t_conj_mem_S₃ hk).1 hbR with h1 | h1
    · exact absurd h1 hbS
    · exact ⟨b * d.t, h1, by rw [mul_assoc, h.t_mul_t, mul_one]⟩
  have hBN : B ≤ normalizer (d.S₃ : Set G) := hBR.trans h.R₃_le_normalizer_S₃
  have e1 := card_sup_mul_card_inf_of_le_normalizer d.S₃ B hBN
  have hle1 : Nat.card (d.S₃ ⊔ B : Subgroup G) ≤ 2 ^ 17 := by
    have := Subgroup.card_le_of_le (sup_le S₃_le_R₃ hBR)
    rwa [h.card_R₃] at this
  rw [h.card_S₃] at e1
  have hB₀card : 2 ^ 13 ≤ Nat.card (d.S₃ ⊓ B : Subgroup G) := by
    have := Nat.mul_le_mul_right (Nat.card (d.S₃ ⊓ B : Subgroup G)) hle1
    omega
  have hB₀S : d.S₃ ⊓ B ≤ d.S₃ := inf_le_left
  have hB₀B : d.S₃ ⊓ B ≤ B := inf_le_right
  obtain ⟨hcE, hsE⟩ := h.sup_V₃_comm_sq_mem_Y' hK hB₀S
    (fun x hx y hy => hc x (hB₀B hx) y (hB₀B hy)) (fun x hx => hs x (hB₀B hx))
  have hE := h.le_A₁V₃_or_le_A₂V₃ hK (sup_le hB₀S V₃_le_S₃) le_sup_right hcE hsE
  have hA₁ : Nat.card (d.A₁ ⊔ d.V₃ : Subgroup G) = 2 ^ 14 := by
    rw [sup_comm]
    exact h.card_V₃_sup_A₁ hK
  have hA₂ : Nat.card (d.A₂ ⊔ d.V₃ : Subgroup G) = 2 ^ 14 := by
    rw [sup_comm]
    exact h.card_V₃_sup_A₂ hK
  have hEcard : Nat.card (d.V₃ ⊔ (d.S₃ ⊓ B) : Subgroup G) ≤ 2 ^ 14 := by
    rw [sup_comm]
    rcases hE with hE | hE
    · exact (Subgroup.card_le_of_le hE).trans hA₁.le
    · exact (Subgroup.card_le_of_le hE).trans hA₂.le
  have hinf : (d.V₃ ⊓ (d.S₃ ⊓ B) : Subgroup G) ≤ ⁅d.S, d.S⁆ ⊔ d.Y := by
    intro x hx
    obtain ⟨hxV, hxB₀⟩ := Subgroup.mem_inf.1 hx
    have hxB : x ∈ B := hB₀B hxB₀
    have hxb : x * b * x⁻¹ * b⁻¹ ∈ d.Y := hc x hxB b hbB
    have hxs : x * s * x⁻¹ * s⁻¹ ∈ d.Y := (h.mem_V₃_iff.1 hxV).2 s hsS₃
    have e : s * (x * d.t * x⁻¹ * d.t) * s⁻¹ =
        (x * s * x⁻¹ * s⁻¹)⁻¹ * (x * b * x⁻¹ * b⁻¹) := by
      have hti : (s * d.t)⁻¹ = d.t * s⁻¹ := by rw [mul_inv_rev, h.t_inv]
      rw [hbs, hti]
      group
    have h1 : s * (x * d.t * x⁻¹ * d.t) * s⁻¹ ∈ d.Y := by
      rw [e]
      exact mul_mem (inv_mem hxs) hxb
    have h2 := (mem_normalizer_iff.1 (h.S₃_le_normalizer_Y (inv_mem hsS₃)) _).1 h1
    rw [show s⁻¹ * (s * (x * d.t * x⁻¹ * d.t) * s⁻¹) * s⁻¹⁻¹ = x * d.t * x⁻¹ * d.t by group]
      at h2
    exact h.mem_commutator_S_sup_Y_of_theta_mem_Y hxV h2
  have hinfcard : Nat.card (d.V₃ ⊓ (d.S₃ ⊓ B) : Subgroup G) ≤ 2 ^ 10 := by
    have := Subgroup.card_le_of_le hinf
    rwa [h.card_S'Y] at this
  have e2 := card_sup_mul_card_inf_of_le_normalizer d.V₃ (d.S₃ ⊓ B) fun g hg =>
    h.S₃_le_normalizer_V₃ (hB₀S hg)
  rw [h.card_V₃ hK] at e2
  have := Nat.mul_le_mul hEcard hinfcard
  omega

theorem conj_mem_S₃_of_mem_normalizer_R₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {g : G}
    (hg : g ∈ normalizer (d.R₃ : Set G)) {E : Subgroup G} (hES : E ≤ d.S₃)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ d.Y) (hs : ∀ x ∈ E, x * x ∈ d.Y)
    (hcard : 2 ^ 14 ≤ Nat.card E) {x : G} (hx : x ∈ E) : g * x * g⁻¹ ∈ d.S₃ := by
  have hgY := h.normalizer_R₃_le_normalizer_Y hK hg
  have hN : ∀ y ∈ d.Y, g * y * g⁻¹ ∈ d.Y := fun y hy => (mem_normalizer_iff.1 hgY y).1 hy
  have hBR : E.map (MulAut.conj g).toMonoidHom ≤ d.R₃ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hg x).1 (S₃_le_R₃ (hES hx))
  have hBle := h.le_S₃_of_elemAb hK hBR (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have := hN _ (hc x hx y hy)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ by group] at this)
    (by
      rintro _ ⟨x, hx, rfl⟩
      have := hN _ (hs x hx)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show g * (x * x) * g⁻¹ = (g * x * g⁻¹) * (g * x * g⁻¹) by group] at this)
    (by
      rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
      exact hcard)
  exact hBle ⟨x, hx, rfl⟩

theorem S₃_eq_A₁V₃_sup_A₂V₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.S₃ = (d.A₁ ⊔ d.V₃) ⊔ (d.A₂ ⊔ d.V₃) := by
  refine le_antisymm ?_ (sup_le (sup_le (d.A₁_le_S.trans h.S_le_S₃) V₃_le_S₃)
    (sup_le (d.A₂_le_S.trans h.S_le_S₃) V₃_le_S₃))
  rw [h.S₃_eq_S_sup_V₃ hK, S_eq_A₁_sup_A₂]
  exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
    (le_sup_right.trans le_sup_left)

theorem normalizer_R₃_le_normalizer_S₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    normalizer (d.R₃ : Set G) ≤ normalizer (d.S₃ : Set G) := fun g hg => by
  refine mem_normalizer_fintype fun x hx => ?_
  have hle : d.S₃ ≤ d.S₃.comap (MulAut.conj g).toMonoidHom := by
    refine (h.S₃_eq_A₁V₃_sup_A₂V₃ hK).le.trans (sup_le (fun y hy => ?_) (fun y hy => ?_))
    · exact h.conj_mem_S₃_of_mem_normalizer_R₃ hK hg (sup_le (d.A₁_le_S.trans h.S_le_S₃) V₃_le_S₃)
        (h.A₁V₃_elemAb hK).1 (h.A₁V₃_elemAb hK).2 (by rw [← sup_comm, h.card_V₃_sup_A₁ hK]) hy
    · exact h.conj_mem_S₃_of_mem_normalizer_R₃ hK hg (sup_le (d.A₂_le_S.trans h.S_le_S₃) V₃_le_S₃)
        (h.A₂V₃_elemAb hK).1 (h.A₂V₃_elemAb hK).2 (by rw [← sup_comm, h.card_V₃_sup_A₂ hK]) hy
  exact hle hx

theorem exists_mem_P₀_theta_mul_mem_V₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) {g : G} (hg : g ∈ d.S₃) :
    ∃ p ∈ d.P₀, (p * d.t * p⁻¹ * d.t)⁻¹ * g ∈ d.V₃ := by
  haveI : (d.V₃.subgroupOf d.S₃).Normal :=
    (Subgroup.normal_subgroupOf_iff V₃_le_S₃).2 fun v g hv hg => h.conj_mem_V₃ hg hv
  let ψ : d.P₀ →* d.S₃ ⧸ d.V₃.subgroupOf d.S₃ :=
    MonoidHom.mk' (fun x => QuotientGroup.mk
      ⟨(x : G) * d.t * (x : G)⁻¹ * d.t, h.theta_mem_S₃ x.2⟩) (fun x y => by
      rw [← QuotientGroup.mk_mul]
      refine Eq.symm (QuotientGroup.eq.2 ?_)
      rw [Subgroup.mem_subgroupOf]
      exact h.theta_mul_mem_V₃ hK x.2 y.2)
  have hmk : ∀ (g g' : G) (hg : g ∈ d.S₃) (hg' : g' ∈ d.S₃), g⁻¹ * g' ∈ d.V₃ →
      (QuotientGroup.mk (⟨g, hg⟩ : ↥d.S₃) : d.S₃ ⧸ d.V₃.subgroupOf d.S₃) =
        QuotientGroup.mk ⟨g', hg'⟩ := fun g g' hg hg' hv =>
    QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hv)
  have hsurj : ∀ g : ↥d.S₃, ∃ π : d.P₀, ψ π = QuotientGroup.mk g := by
    rintro ⟨g, hg⟩
    have hset₁ := coe_mul_of_left_le_normalizer_right d.S d.V₃ fun g hg =>
      h.S_le_normalizer_V₃ hg
    have hA₁N : d.A₁ ≤ normalizer (d.A₂ : Set G) := fun a ha =>
      normalizer_S_le_normalizer_A₂ (d.S.le_normalizer (d.A₁_le_S ha))
    have hset₂ := coe_mul_of_left_le_normalizer_right d.A₁ d.A₂ hA₁N
    have hg' : g ∈ d.S ⊔ d.V₃ := by rwa [h.S₃_eq_S_sup_V₃ hK] at hg
    obtain ⟨s, hs, v, hv, hsv⟩ : g ∈ (d.S : Set G) * (d.V₃ : Set G) := by
      rw [← hset₁]
      exact hg'
    have hs' : s ∈ d.A₁ ⊔ d.A₂ := by rwa [S_eq_A₁_sup_A₂] at hs
    obtain ⟨a₁, ha₁, a₂, ha₂, ha₁₂⟩ : s ∈ (d.A₁ : Set G) * (d.A₂ : Set G) := by
      rw [← hset₂]
      exact hs'
    obtain ⟨u, hu, w, hw, huw⟩ := h.sec4_11_2.2.1 a₁ ha₁
    obtain ⟨u', hu', y, hy, hu'y⟩ := h.sec4_15_2.2.1 a₂ (h.A₂_le_D₀ ha₂)
    have h₁ : ψ ⟨u, h.D₁_le_P₀ hK hKY hu⟩ =
        QuotientGroup.mk ⟨a₁, h.S_le_S₃ (d.A₁_le_S ha₁)⟩ := by
      show QuotientGroup.mk _ = _
      refine hmk _ _ _ _ ?_
      rw [huw, mul_inv_rev, inv_mul_cancel_right]
      exact inv_mem (h.W_le_V₃ hw)
    have h₂ : ψ ⟨u', h.D₂_le_P₀ hK hu'⟩ =
        QuotientGroup.mk ⟨a₂, h.S_le_S₃ (d.A₂_le_S ha₂)⟩ := by
      show QuotientGroup.mk _ = _
      refine hmk _ _ _ _ ?_
      rw [hu'y, mul_inv_rev, inv_mul_cancel_right]
      exact inv_mem (h.Y_le_V₃ hy)
    refine ⟨⟨u, h.D₁_le_P₀ hK hKY hu⟩ * ⟨u', h.D₂_le_P₀ hK hu'⟩, ?_⟩
    rw [map_mul, h₁, h₂, ← QuotientGroup.mk_mul]
    refine hmk _ _ _ _ ?_
    change (a₁ * a₂)⁻¹ * g ∈ d.V₃
    have hsv' : s * v = g := hsv
    have ha₁₂' : a₁ * a₂ = s := ha₁₂
    rw [← hsv', ← ha₁₂', inv_mul_cancel_left]
    exact hv
  obtain ⟨π, hπ⟩ := hsurj ⟨g, hg⟩
  refine ⟨π, π.2, ?_⟩
  have hψπ : ψ π = QuotientGroup.mk ⟨(π : G) * d.t * (π : G)⁻¹ * d.t, h.theta_mem_S₃ π.2⟩ := rfl
  rw [hψπ] at hπ
  have := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hπ)
  exact this

theorem mem_normalizer_withT_V₃_of_theta_mem_V₃ (h : d.Hyp) {x : G}
    (hxN : x ∈ normalizer (d.V₃ : Set G)) (hθ : x * d.t * x⁻¹ * d.t ∈ d.V₃) :
    x ∈ normalizer ((d.V₃ ⊔ zpowers d.t : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun y hy => ?_
  have hle : d.V₃ ⊔ zpowers d.t ≤ (d.V₃ ⊔ zpowers d.t).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le (fun v hv => ?_) (zpowers_le.2 ?_)
    · exact mem_sup_left ((mem_normalizer_iff.1 hxN v).1 hv)
    · change x * d.t * x⁻¹ ∈ d.V₃ ⊔ zpowers d.t
      rw [show x * d.t * x⁻¹ = (x * d.t * x⁻¹ * d.t) * d.t by
        rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]]
      exact mul_mem (mem_sup_left hθ) (mem_sup_right (mem_zpowers _))
  exact hle hy

theorem normalizer_R₃_eq (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) :
    normalizer (d.R₃ : Set G) = (normalizer (d.S : Set G) ⊓ d.H) ⊔ d.P := by
  apply le_antisymm
  · intro g hg
    have hgY := h.normalizer_R₃_le_normalizer_Y hK hg
    have hgS₃ := h.normalizer_R₃_le_normalizer_S₃ hK hg
    have hgV₃ := h.mem_normalizer_V₃ hgS₃ hgY
    have htR : d.t ∈ d.R₃ := h.R_le_R₃ (mem_sup_right (mem_zpowers _))
    have hθS : g * d.t * g⁻¹ * d.t ∈ d.S₃ := by
      have hy : g * d.t * g⁻¹ ∈ d.R₃ := (mem_normalizer_iff.1 hg _).1 htR
      rw [h.R₃_eq_S₃_sup] at hy
      rcases (mem_sup_zpowers_iff h.t_mul_t fun k hk => h.t_conj_mem_S₃ hk).1 hy with h1 | h1
      · exfalso
        apply h.t_not_mem_S₃
        have := (mem_normalizer_iff.1 (inv_mem hgS₃) _).1 h1
        rwa [show g⁻¹ * (g * d.t * g⁻¹) * g⁻¹⁻¹ = d.t by group] at this
      · exact h1
    obtain ⟨p, hpP₀, hp⟩ := h.exists_mem_P₀_theta_mul_mem_V₃ hK hKY hθS
    have hpN : p ∈ normalizer (d.V₃ : Set G) := (Data.mem_P₀.1 hpP₀).2.2.1.1
    have hpP : p ∈ d.P := by
      rw [h.P_eq_P₀ hK hKY]
      exact hpP₀
    have hθ : (p⁻¹ * g) * d.t * (p⁻¹ * g)⁻¹ * d.t ∈ d.V₃ := by
      have hpθS : p * d.t * p⁻¹ * d.t ∈ d.S₃ := h.theta_mem_S₃ hpP₀
      have h1 : (g * d.t * g⁻¹ * d.t) * (p * d.t * p⁻¹ * d.t)⁻¹ ∈ d.V₃ := by
        have := h.conj_mem_V₃ hpθS hp
        rwa [show (p * d.t * p⁻¹ * d.t) * ((p * d.t * p⁻¹ * d.t)⁻¹ * (g * d.t * g⁻¹ * d.t)) *
          (p * d.t * p⁻¹ * d.t)⁻¹ = (g * d.t * g⁻¹ * d.t) * (p * d.t * p⁻¹ * d.t)⁻¹ by group]
          at this
      have h2 := (mem_normalizer_iff.1 (inv_mem hpN) _).1 h1
      have e : p⁻¹ * (g * d.t * g⁻¹ * d.t) * p⁻¹⁻¹ * (p⁻¹ * (p * d.t * p⁻¹ * d.t)⁻¹ * p) =
          p⁻¹ * ((g * d.t * g⁻¹ * d.t) * (p * d.t * p⁻¹ * d.t)⁻¹) * p⁻¹⁻¹ := by group
      rw [h.crossed_mul_eq p⁻¹ g, h.crossed_inv_eq p, e]
      exact h2
    have hxT : p⁻¹ * g ∈ normalizer ((d.V₃ ⊔ zpowers d.t : Subgroup G) : Set G) :=
      h.mem_normalizer_withT_V₃_of_theta_mem_V₃ (mul_mem (inv_mem hpN) hgV₃) hθ
    rw [h.normalizer_withT_V₃ hK] at hxT
    have hmem : p⁻¹ * g ∈ (normalizer (d.S : Set G) ⊓ d.H) ⊔ d.P :=
      sup_le_sup_left (h.V₃_le_P hK) _ hxT
    rw [show g = p * (p⁻¹ * g) by group]
    exact mul_mem (mem_sup_right hpP) hmem
  · exact sup_le h.NHS_le_normalizer_R₃ (h.P_le_normalizer_R₃ hK hKY)

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
