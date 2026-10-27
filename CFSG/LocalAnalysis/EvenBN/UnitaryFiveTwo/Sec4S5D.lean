module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S5C

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

@[expose] def Data.P {G : Type} [Group G] (d : Data G) : Subgroup G := d.D₁ ⊔ d.D₂

theorem eq_A₂sub_or_eq_Ssub_of_conj_e₁ {R : Subgroup SU52} (hAR : A₂sub ≤ R) (hR : R ≤ Ssub)
    (he : ∀ r ∈ R, e₁SU * r * e₁SU⁻¹ ∈ R) : R = A₂sub ∨ R = Ssub := by
  by_cases hRA : R ≤ A₂sub
  · exact Or.inl (le_antisymm hRA hAR)
  right
  obtain ⟨r, hrR, hrA⟩ := IsConcreteLE.not_le_iff_exists.1 hRA
  have hr10 : mat r 1 0 ≠ 0 := fun h0 => hrA (mem_A₂sub.2 ⟨hR hrR, h0⟩)
  refine le_antisymm hR fun y hy => le_of_coord_omega (B := (Ssub : Set SU52))
    (fun x => mat x 1 0) hAR hR (fun x hx z hz hxz => ?_) (fun z hz h0 => mem_A₂sub.2 ⟨hz, h0⟩)
    (fun r => e₁SU * r * e₁SU⁻¹) he (fun r _ => mat_conj_e₁_one_zero r) hrR hr10 hy
  refine mem_A₂sub.2 ⟨mul_mem (inv_mem hx) hz, ?_⟩
  have h1 := mat_mul_one_zero hx (inv_mem hx)
  rw [mul_inv_cancel, mat_one, Matrix.one_apply_ne (by decide)] at h1
  have h2 := mat_mul_one_zero (inv_mem hx) hz
  rw [h2]
  linear_combination (-1 : F4) * h1 - hxz

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem D₂_le_centralizer_Y : d.D₂ ≤ centralizer (d.Y : Set G) := fun u hu =>
  mem_centralizer_iff.2 fun y hy => (D₂_comm_Y' hu hy).symm

theorem S_inf_centralizer_Y (h : d.Hyp) : d.S ⊓ centralizer (d.Y : Set G) = d.A₂ := by
  have hA₂ : d.A₂ ≤ d.S ⊓ centralizer (d.Y : Set G) :=
    le_inf d.A₂_le_S fun a ha => D₂_le_centralizer_Y (h.A₂_le_D₂' ha)
  refine le_antisymm (fun x hx => ?_) hA₂
  let E : Subgroup SU52 := (d.S ⊓ centralizer (d.Y : Set G)).comap d.ι
  have hES : E ≤ Ssub := fun σ hσ => d.ι_mem_pull_iff.1 (Subgroup.mem_inf.1 hσ).1
  have hAE : A₂sub ≤ E := fun σ hσ => hA₂ ⟨σ, hσ, rfl⟩
  have he₁N : d.e₁ ∈ normalizer (d.S : Set G) := (Subgroup.mem_inf.1 h.e₁_mem_NHS).1
  have he₁Y : d.e₁ ∈ normalizer (d.Y : Set G) := h.NHS_le_normalizer_Y h.e₁_mem_NHS
  have heE : ∀ r ∈ E, e₁SU * r * e₁SU⁻¹ ∈ E := fun r hr => by
    obtain ⟨hrS, hrC⟩ := Subgroup.mem_inf.1 hr
    have e : d.ι (e₁SU * r * e₁SU⁻¹) = d.e₁ * d.ι r * d.e₁⁻¹ := by
      simp only [Data.e₁, map_mul, map_inv]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [e]
      exact (mem_normalizer_iff.1 he₁N _).1 hrS
    · rw [e]
      refine mem_centralizer_iff.2 fun y hy => ?_
      have hy' : d.e₁⁻¹ * y * d.e₁ ∈ d.Y := by
        have := (mem_normalizer_iff.1 (inv_mem he₁Y) y).1 hy
        rwa [inv_inv] at this
      have hc := mem_centralizer_iff.1 hrC _ hy'
      calc y * (d.e₁ * d.ι r * d.e₁⁻¹) = d.e₁ * ((d.e₁⁻¹ * y * d.e₁) * d.ι r) * d.e₁⁻¹ := by group
        _ = d.e₁ * (d.ι r * (d.e₁⁻¹ * y * d.e₁)) * d.e₁⁻¹ := by rw [hc]
        _ = d.e₁ * d.ι r * d.e₁⁻¹ * y := by group
  rcases eq_A₂sub_or_eq_Ssub_of_conj_e₁ hAE hES heE with hE | hE
  · obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨σ, hσ, rfl⟩ := hxS
    have : σ ∈ E := Subgroup.mem_inf.2 ⟨⟨σ, hσ, rfl⟩, hxC⟩
    rw [hE] at this
    exact ⟨σ, this, rfl⟩
  · exfalso
    have hYW : d.Y ≤ d.W := fun y hy => Subgroup.mem_inf.2 ⟨hy, mem_centralizer_iff.2
      fun s hs => by
        obtain ⟨σ, hσ, rfl⟩ := hs
        have : σ ∈ E := by rw [hE]; exact hσ
        exact (mem_centralizer_iff.1 (Subgroup.mem_inf.1 this).2 y hy).symm⟩
    have := Subgroup.card_le_of_le hYW
    rw [h.card_Y', h.sec4_9_W.1] at this
    omega

theorem X₂_inf_centralizer_Y (h : d.Hyp) : d.X₂ ⊓ centralizer (d.Y : Set G) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.1 hx
  have h1 : x ∈ d.S ⊓ centralizer (d.Y : Set G) := Subgroup.mem_inf.2 ⟨X₂_le_S' hxX, hxC⟩
  rw [h.S_inf_centralizer_Y] at h1
  have h2 : x ∈ d.X₂ ⊓ d.A₂ := Subgroup.mem_inf.2 ⟨hxX, h1⟩
  rwa [h.X₂_inf_A₂] at h2

theorem mem_D₂_of_mem_S₃_of_mem_centralizer_Y (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {s : G} (hs : s ∈ d.S₃)
    (hc : s ∈ centralizer (d.Y : Set G)) : s ∈ d.D₂ := by
  have hset₁ := coe_mul_of_left_le_normalizer_right d.S d.V₃ fun g hg => h.S_le_normalizer_V₃ hg
  have hset₂ := coe_mul_of_left_le_normalizer_right d.X₂ d.A₂ h.X₂_le_normalizer_A₂
  rw [h.S₃_eq_S_sup_V₃ hK] at hs
  obtain ⟨s₀, hs₀, v, hv, hsv⟩ : s ∈ (d.S : Set G) * (d.V₃ : Set G) := by
    rw [← hset₁]
    exact hs
  have hs₀' : s₀ ∈ d.X₂ ⊔ d.A₂ := by
    rw [sup_comm, ← d.S_eq_sup]
    exact hs₀
  obtain ⟨x₂, hx₂, a, ha, hxa⟩ : s₀ ∈ (d.X₂ : Set G) * (d.A₂ : Set G) := by
    rw [← hset₂]
    exact hs₀'
  have hav : a * v ∈ d.D₂ := mul_mem (h.A₂_le_D₂' ha) (h.V₃_le_D₂ hK hv)
  have hsv' : s₀ * v = s := hsv
  have hxa' : x₂ * a = s₀ := hxa
  have hs_eq : s = x₂ * (a * v) := by rw [← hsv', ← hxa', mul_assoc]
  have hx₂C : x₂ ∈ centralizer (d.Y : Set G) := by
    have : x₂ = s * (a * v)⁻¹ := by rw [hs_eq]; group
    rw [this]
    exact mul_mem hc (inv_mem (D₂_le_centralizer_Y hav))
  have hx₂1 : x₂ = 1 := by
    have : x₂ ∈ d.X₂ ⊓ centralizer (d.Y : Set G) := Subgroup.mem_inf.2 ⟨hx₂, hx₂C⟩
    rw [h.X₂_inf_centralizer_Y] at this
    exact Subgroup.mem_bot.1 this
  rw [hs_eq, hx₂1, one_mul]
  exact hav

theorem D₁_le_normalizer_D₂ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) : d.D₁ ≤ normalizer (d.D₂ : Set G) :=
  fun x hx => mem_normalizer_fintype fun u hu => by
    have hc := (h.P₀_eq_and_card hK hKY).2.2 x (h.D₁_le_P₀ hK hKY hx) u (h.D₂_le_P₀ hK hu)
    have hxY := h.D₁_le_normalizer_Y hKY hx
    have hxuC : x * u * x⁻¹ ∈ centralizer (d.Y : Set G) := by
      refine mem_centralizer_iff.2 fun y hy => ?_
      have hy' : x⁻¹ * y * x ∈ d.Y := by
        have := (mem_normalizer_iff.1 (inv_mem hxY) y).1 hy
        rwa [inv_inv] at this
      have e := D₂_comm_Y' hu hy'
      calc y * (x * u * x⁻¹) = x * ((x⁻¹ * y * x) * u) * x⁻¹ := by group
        _ = x * (u * (x⁻¹ * y * x)) * x⁻¹ := by rw [← e]
        _ = x * u * x⁻¹ * y := by group
    have hcC : x * u * x⁻¹ * u⁻¹ ∈ centralizer (d.Y : Set G) :=
      mul_mem hxuC (inv_mem (D₂_le_centralizer_Y hu))
    have hcD := h.mem_D₂_of_mem_S₃_of_mem_centralizer_Y hK hc hcC
    have := mul_mem hcD hu
    rwa [inv_mul_cancel_right] at this

theorem t_conj_mem_D₁ (h : d.Hyp) {k : G} (hk : k ∈ d.D₁) : d.t * k * d.t ∈ d.D₁ := by
  have htW : d.t ∈ normalizer (d.W : Set G) := mem_normalizer_fintype fun w hw => by
    rw [h.t_inv]
    exact h.t_conj_mem_W hw
  have htX : d.t ∈ d.XW :=
    Subgroup.mem_inf.2 ⟨d.AWT.le_normalizer (mem_sup_right (mem_zpowers _)), htW⟩
  have := h.conj_mem_D₁ htX hk
  rwa [h.t_inv] at this

theorem t_conj_mem_D₂ (h : d.Hyp) {k : G} (hk : k ∈ d.D₂) : d.t * k * d.t ∈ d.D₂ := by
  have htX : d.t ∈ d.XC₀ := d.C₀.le_normalizer h.t_mem_C₀
  have := h.conj_mem_D₂ htX hk
  rwa [h.t_inv] at this

theorem P_eq_P₀ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) : d.P = d.P₀ :=
  ((h.P₀_eq_and_card hK hKY).1).symm

theorem card_P (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) : Nat.card d.P = 2 ^ 20 := by
  rw [h.P_eq_P₀ hK hKY]
  exact (h.P₀_eq_and_card hK hKY).2.1

theorem D₁_le_P : d.D₁ ≤ d.P := le_sup_left

theorem D₂_le_P : d.D₂ ≤ d.P := le_sup_right

theorem S_le_P (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) : d.S ≤ d.P := by
  rw [h.P_eq_P₀ hK hKY]
  exact h.S_le_S₃.trans (h.S₃_le_P₀ hK)

theorem V₃_le_P (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.V₃ ≤ d.P := (h.V₃_le_D₂ hK).trans D₂_le_P

theorem W_le_P (h : d.Hyp) : d.W ≤ d.P := h.W_le_D₁.trans D₁_le_P

theorem P_le_centralizer_W (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) : d.P ≤ centralizer (d.W : Set G) :=
  fun x hx => (Data.mem_P₀.1 (by rwa [h.P_eq_P₀ hK hKY] at hx)).2.1

theorem P_le_normalizer_R₃ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) : d.P ≤ normalizer (d.R₃ : Set G) :=
  fun x hx => (Data.mem_P₀.1 (by rwa [h.P_eq_P₀ hK hKY] at hx)).1

theorem P_inf_H (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) : d.P ⊓ d.H = d.S := by
  refine le_antisymm (fun x hx => ?_) (le_inf (h.S_le_P hK hKY) fun s hs =>
    h.R_le_H (mem_sup_left hs))
  obtain ⟨hxP, hxH⟩ := Subgroup.mem_inf.1 hx
  have hxP₀ : x ∈ d.P₀ := by rwa [← h.P_eq_P₀ hK hKY]
  have hθ : x * d.t * x⁻¹ * d.t = 1 :=
    h.crossed_eq_one_of_comm (mem_centralizer_singleton_iff.1 hxH)
  have hx₃ : x ∈ d.S₃ := h.mem_S₃_of_theta_mem_V₃ hK hxP₀ (by rw [hθ]; exact one_mem _)
  have : x ∈ d.S₃ ⊓ d.H := Subgroup.mem_inf.2 ⟨hx₃, hxH⟩
  rwa [h.S₃_inf_H] at this

theorem t_not_mem_P (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) : d.t ∉ d.P := fun ht => by
  have : d.t ∈ d.P ⊓ d.H := Subgroup.mem_inf.2 ⟨ht, h.t_mem_H⟩
  rw [h.P_inf_H hK hKY] at this
  exact h.t_not_mem_L (d.pull_le_L _ this)

theorem t_mem_normalizer_P (h : d.Hyp) : d.t ∈ normalizer (d.P : Set G) :=
  mem_normalizer_sup (mem_normalizer_fintype fun k hk => by
      rw [h.t_inv]
      exact h.t_conj_mem_D₁ hk)
    (mem_normalizer_fintype fun k hk => by
      rw [h.t_inv]
      exact h.t_conj_mem_D₂ hk)

theorem t_conj_mem_P (h : d.Hyp) {k : G} (hk : k ∈ d.P) : d.t * k * d.t ∈ d.P := by
  have := (mem_normalizer_iff.1 h.t_mem_normalizer_P k).1 hk
  rwa [h.t_inv] at this

theorem NHS_le_normalizer_P (h : d.Hyp) :
    normalizer (d.S : Set G) ⊓ d.H ≤ normalizer (d.P : Set G) := fun n hn =>
  mem_normalizer_sup (mem_normalizer_fintype fun k hk => h.conj_mem_D₁ (h.NHS_le_XW hn) hk)
    (mem_normalizer_fintype fun k hk => h.conj_mem_D₂ (h.NHS_le_XC₀ hn) hk)

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
