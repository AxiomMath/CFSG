module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S3B

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem X₂_le_S' : d.X₂ ≤ d.S := d.pull_mono X₂sub_le_Ssub

theorem X₂_le_A₁ : d.X₂ ≤ d.A₁ := d.pull_mono X₂sub_le_A₁sub

theorem A₁_le_D₃ (h : d.Hyp) : d.A₁ ≤ d.D₃ := (le_sup_left : d.A₁ ≤ d.AW).trans h.AW_le_D₃

theorem X₂_le_normalizer_A₂ (h : d.Hyp) : d.X₂ ≤ normalizer (d.A₂ : Set G) := fun x hx =>
  (h.S_le_NHA₂ (X₂_le_S' hx)).1

theorem X₂_inf_A₂ (h : d.Hyp) : d.X₂ ⊓ d.A₂ = ⊥ := by
  have e := card_sup_mul_card_inf_of_le_normalizer d.A₂ d.X₂ (h.X₂_le_normalizer_A₂)
  rw [← d.S_eq_sup, d.card_S, d.card_A₂, card_X₂ (d := d)] at e
  have h1 : Nat.card (d.A₂ ⊓ d.X₂ : Subgroup G) = 1 := by omega
  rw [inf_comm]
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem X₂_inf_D₂ (h : d.Hyp) : d.X₂ ⊓ d.D₂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxX, hxD⟩ := Subgroup.mem_inf.1 hx
  have hxH : x ∈ d.H := h.L_le_H (d.pull_le_L _ (X₂_le_S' hxX))
  have hxA : x ∈ d.A₂ := by
    have : x ∈ d.D₂ ⊓ d.H := Subgroup.mem_inf.2 ⟨hxD, hxH⟩
    rwa [h.D₂_inf_H] at this
  have := Subgroup.mem_inf.2 ⟨hxX, hxA⟩
  rwa [h.X₂_inf_A₂] at this

theorem S₃_le_normalizer_Y (h : d.Hyp) : d.S₃ ≤ normalizer (d.Y : Set G) :=
  h.S₃_le_S_sup_D₂.trans (sup_le h.S_le_normalizer_Y fun e he =>
    mem_normalizer_of_forall_comm fun y hy => (D₂_comm_Y' he hy).symm)

theorem D₃_le_normalizer_D₂ (h : d.Hyp) : d.D₃ ≤ normalizer (d.D₂ : Set G) := fun u hu => by
  have := h.S₃_le_S_sup_D₂ (h.D₃_le_S₃' hu)
  exact (sup_le h.S_le_normalizer_D₂ (d.D₂).le_normalizer) this

theorem exists_eq_mul_of_mem_D₃' (h : d.Hyp) {x : G} (hx : x ∈ d.D₃) :
    ∃ x₂ ∈ d.X₂, ∃ u ∈ d.D₃ ⊓ d.D₂, x = x₂ * u := by
  obtain ⟨s, hs, e, he, rfl⟩ := h.exists_eq_mul_of_mem_D₃ hx
  have hset := coe_mul_of_left_le_normalizer_right d.X₂ d.A₂ h.X₂_le_normalizer_A₂
  obtain ⟨x₂, hx₂, a, ha, hsa⟩ : s ∈ (d.X₂ : Set G) * (d.A₂ : Set G) := by
    rw [← hset, sup_comm, ← d.S_eq_sup]
    exact hs
  refine ⟨x₂, hx₂, a * e, ⟨?_, mul_mem (h.A₂_le_D₂' ha) he⟩, ?_⟩
  · have h1 : x₂⁻¹ * (s * e) ∈ d.D₃ :=
      mul_mem (inv_mem (h.A₁_le_D₃ (X₂_le_A₁ hx₂))) hx
    rw [← hsa, show x₂⁻¹ * (x₂ * a * e) = a * e by group] at h1
    exact h1
  · rw [← hsa]
    group

theorem D₃_le_normalizer_D₃_inf_D₂ (h : d.Hyp) :
    d.D₃ ≤ normalizer ((d.D₃ ⊓ d.D₂ : Subgroup G) : Set G) := fun x hx =>
  mem_normalizer_fintype fun t ht => Subgroup.mem_inf.2
    ⟨mul_mem (mul_mem hx (Subgroup.mem_inf.1 ht).1) (inv_mem hx),
      (mem_normalizer_iff.1 (h.D₃_le_normalizer_D₂ hx) t).1 (Subgroup.mem_inf.1 ht).2⟩

theorem card_D₃_inf_D₂ (h : d.Hyp) : Nat.card (d.D₃ ⊓ d.D₂ : Subgroup G) = 2 ^ 10 := by
  set T : Subgroup G := d.D₃ ⊓ d.D₂ with hT
  have hX : d.X₂ ≤ normalizer (T : Set G) := fun x hx =>
    h.D₃_le_normalizer_D₃_inf_D₂ (h.A₁_le_D₃ (X₂_le_A₁ hx))
  have e := card_sup_mul_card_inf_of_le_normalizer T d.X₂ hX
  have hsup : T ⊔ d.X₂ = d.D₃ := by
    refine le_antisymm (sup_le inf_le_left (X₂_le_A₁.trans h.A₁_le_D₃)) fun x hx => ?_
    obtain ⟨x₂, hx₂, u, hu, rfl⟩ := h.exists_eq_mul_of_mem_D₃' hx
    exact mul_mem (mem_sup_right hx₂) (mem_sup_left hu)
  have hinf : T ⊓ d.X₂ = ⊥ := by
    rw [eq_bot_iff, ← h.X₂_inf_D₂]
    exact fun x hx => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2⟩
  rw [hsup, hinf, Subgroup.card_bot, h.card_D₃, card_X₂ (d := d)] at e
  omega

theorem D₃_inf_D₂_eq (h : d.Hyp) : d.D₃ ⊓ d.D₂ = d.D₁ ⊓ d.D₂ :=
  le_antisymm (inf_le_inf D₃_le_D₁' le_rfl) (le_inf h.D₁_inf_D₂_le_D₃ inf_le_right)

theorem card_Y' (h : d.Hyp) : Nat.card d.Y = 2 ^ 8 := h.sec4_6.2.2.2.2.1

theorem F_le_S : d.F ≤ d.S := d.F_le_A₂.trans d.A₂_le_S

theorem Y_le_S₃ (h : d.Hyp) : d.Y ≤ d.S₃ := by
  rw [h.S₃_eq]
  exact (le_sup_right : d.Y ≤ d.S ⊔ d.Y).trans le_sup_left

theorem mem_V₃_iff (h : d.Hyp) {x : G} :
    x ∈ d.V₃ ↔ x ∈ d.S₃ ∧ ∀ s ∈ d.S₃, x * s * x⁻¹ * s⁻¹ ∈ d.Y := by
  constructor
  · intro hx
    obtain ⟨hc, hxS⟩ := Subgroup.mem_inf.1 hx
    exact ⟨hxS, hc.2⟩
  · rintro ⟨hx, hc⟩
    exact Subgroup.mem_inf.2 ⟨⟨h.S₃_le_normalizer_Y hx, hc⟩, hx⟩

theorem V₃_le_S₃ : d.V₃ ≤ d.S₃ := inf_le_right

theorem conj_mem_V₃ (h : d.Hyp) {g x : G} (hg : g ∈ d.S₃) (hx : x ∈ d.V₃) :
    g * x * g⁻¹ ∈ d.V₃ := by
  obtain ⟨hxS, hxc⟩ := (h.mem_V₃_iff).1 hx
  refine (h.mem_V₃_iff).2 ⟨mul_mem (mul_mem hg hxS) (inv_mem hg), fun s hs => ?_⟩
  have := (mem_normalizer_iff.1 (h.S₃_le_normalizer_Y hg) _).1
    (hxc (g⁻¹ * s * g) (mul_mem (mul_mem (inv_mem hg) hs) hg))
  rwa [show g * (x * (g⁻¹ * s * g) * x⁻¹ * (g⁻¹ * s * g)⁻¹) * g⁻¹ =
    g * x * g⁻¹ * s * (g * x * g⁻¹)⁻¹ * s⁻¹ by group] at this

theorem Y_le_V₃ (h : d.Hyp) : d.Y ≤ d.V₃ := fun y hy => (h.mem_V₃_iff).2 ⟨h.Y_le_S₃ hy, fun s hs => by
  have := (mem_normalizer_iff.1 (h.S₃_le_normalizer_Y hs) y⁻¹).1 (inv_mem hy)
  rw [show y * s * y⁻¹ * s⁻¹ = y * (s * y⁻¹ * s⁻¹) by group]
  exact mul_mem hy this⟩

theorem S_inf_Y (h : d.Hyp) : d.S ⊓ d.Y = d.F := by
  refine le_antisymm (fun y hy => ?_) (le_inf F_le_S h.F_le_Y)
  obtain ⟨hyS, hyY⟩ := Subgroup.mem_inf.1 hy
  exact (h.mem_F_iff_Y y).2 ⟨hyY, mem_centralizer_singleton_iff.1
    (h.L_le_H (d.pull_le_L _ hyS))⟩

theorem commutator_S_le_A₂ : ⁅d.S, d.S⁆ ≤ d.A₂ := by
  rw [commutator_S_eq]
  exact sup_le (d.pull_mono X₄sub_le_A₂sub) d.F_le_A₂

theorem card_commutator_S : Nat.card (⁅d.S, d.S⁆ : Subgroup G) = 2 ^ 6 := by
  rw [commutator_S_eq, show d.X₄ ⊔ d.F = d.pull (X₄sub ⊔ Fsub) from (d.pull_sup _ _).symm,
    ← commutator_Ssub_eq_X₄sub_sup_Fsub, d.card_pull, card_commutator_Ssub]

theorem Y_le_normalizer_commutator_S (h : d.Hyp) :
    d.Y ≤ normalizer ((⁅d.S, d.S⁆ : Subgroup G) : Set G) := fun y hy =>
  mem_normalizer_of_forall_comm fun n hn =>
    Y_comm_D₀ hy (h.A₂_le_D₀ (commutator_S_le_A₂ hn)) |>.symm

theorem S'_inf_Y (h : d.Hyp) : ⁅d.S, d.S⁆ ⊓ d.Y = d.F := by
  refine le_antisymm (fun y hy => ?_) (le_inf ?_ h.F_le_Y)
  · obtain ⟨hyS, hyY⟩ := Subgroup.mem_inf.1 hy
    have : y ∈ d.S ⊓ d.Y := Subgroup.mem_inf.2 ⟨commutator_S_le_A₂.trans d.A₂_le_S hyS, hyY⟩
    rwa [h.S_inf_Y] at this
  · rw [commutator_S_eq]
    exact le_sup_right

theorem card_S'Y (h : d.Hyp) : Nat.card (⁅d.S, d.S⁆ ⊔ d.Y : Subgroup G) = 2 ^ 10 := by
  have e := card_sup_mul_card_inf_of_le_normalizer ⁅d.S, d.S⁆ d.Y h.Y_le_normalizer_commutator_S
  rw [h.S'_inf_Y, card_commutator_S, h.card_Y', d.card_F] at e
  omega

theorem card_SY (h : d.Hyp) : Nat.card (d.S ⊔ d.Y : Subgroup G) = 2 ^ 14 := by
  have e := card_sup_mul_card_inf_of_le_normalizer d.Y d.S h.S_le_normalizer_Y
  rw [inf_comm, h.S_inf_Y, sup_comm, h.card_Y', d.card_S, d.card_F] at e
  omega

theorem mem_commutator_S_of_comm_mem_F {s : G} (hs : s ∈ d.S)
    (hc : ∀ g ∈ d.S, g * s * g⁻¹ * s⁻¹ ∈ d.F) : s ∈ ⁅d.S, d.S⁆ := by
  rw [commutator_S_eq]
  obtain ⟨σ, hσ, rfl⟩ := hs
  have hσ' : σ ∈ X₄sub ⊔ Fsub := mem_X₄sub_sup_Fsub_iff.2 ⟨hσ, fun τ hτ => by
    have := hc (d.ι τ) ⟨τ, hτ, rfl⟩
    have e : d.ι τ * d.ι σ * (d.ι τ)⁻¹ * (d.ι σ)⁻¹ = d.ι (τ * σ * τ⁻¹ * σ⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e] at this
    exact d.ι_mem_pull_iff.1 this⟩
  have : d.ι σ ∈ d.pull (X₄sub ⊔ Fsub) := ⟨σ, hσ', rfl⟩
  rwa [d.pull_sup] at this

theorem comm_mem_F_of_mem_commutator_S {s g : G} (hs : s ∈ ⁅d.S, d.S⁆) (hg : g ∈ d.S) :
    g * s * g⁻¹ * s⁻¹ ∈ d.F := by
  rw [commutator_S_eq] at hs
  have hs' : s ∈ d.pull (X₄sub ⊔ Fsub) := by
    rw [d.pull_sup]
    exact hs
  obtain ⟨σ, hσ, rfl⟩ := hs'
  obtain ⟨τ, hτ, rfl⟩ := hg
  have e : d.ι τ * d.ι σ * (d.ι τ)⁻¹ * (d.ι σ)⁻¹ = d.ι (τ * σ * τ⁻¹ * σ⁻¹) := by
    simp only [map_mul, map_inv]
  rw [e]
  exact ⟨_, (mem_X₄sub_sup_Fsub_iff.1 hσ).2 τ hτ, rfl⟩

theorem mem_commutator_S_of_mul_mem_V₃ (h : d.Hyp) {s y : G} (hs : s ∈ d.S) (hy : y ∈ d.Y)
    (hx : s * y ∈ d.V₃) : s ∈ ⁅d.S, d.S⁆ := by
  obtain ⟨-, hxc⟩ := (h.mem_V₃_iff).1 hx
  refine mem_commutator_S_of_comm_mem_F hs fun g hg => ?_
  have hgS₃ : g ∈ d.S₃ := h.S_le_S₃ hg
  have h1 := hxc g hgS₃
  have hg_y : g * y⁻¹ * g⁻¹ ∈ d.Y :=
    (mem_normalizer_iff.1 (h.S₃_le_normalizer_Y hgS₃) _).1 (inv_mem hy)
  have hy1 : s * (y * g * y⁻¹ * g⁻¹) * s⁻¹ ∈ d.Y := by
    have : y * g * y⁻¹ * g⁻¹ ∈ d.Y := by
      rw [show y * g * y⁻¹ * g⁻¹ = y * (g * y⁻¹ * g⁻¹) by group]
      exact mul_mem hy hg_y
    exact (mem_normalizer_iff.1 (h.S_le_normalizer_Y hs) _).1 this
  have hsg : s * g * s⁻¹ * g⁻¹ ∈ d.Y := by
    have e : s * g * s⁻¹ * g⁻¹ =
        (s * (y * g * y⁻¹ * g⁻¹) * s⁻¹)⁻¹ * ((s * y) * g * (s * y)⁻¹ * g⁻¹) := by group
    rw [e]
    exact mul_mem (inv_mem hy1) h1
  have hsgS : s * g * s⁻¹ * g⁻¹ ∈ d.S := mul_mem (mul_mem (mul_mem hs hg) (inv_mem hs)) (inv_mem hg)
  have hF : s * g * s⁻¹ * g⁻¹ ∈ d.F := by
    have : s * g * s⁻¹ * g⁻¹ ∈ d.S ⊓ d.Y := Subgroup.mem_inf.2 ⟨hsgS, hsg⟩
    rwa [h.S_inf_Y] at this
  have := inv_mem hF
  rwa [show (s * g * s⁻¹ * g⁻¹)⁻¹ = g * s * g⁻¹ * s⁻¹ by group] at this

theorem V₃_inf_SY_le (h : d.Hyp) : d.V₃ ⊓ (d.S ⊔ d.Y) ≤ ⁅d.S, d.S⁆ ⊔ d.Y := by
  intro x hx
  obtain ⟨hxV, hxSY⟩ := Subgroup.mem_inf.1 hx
  have hset := coe_mul_of_left_le_normalizer_right d.S d.Y h.S_le_normalizer_Y
  obtain ⟨s, hs, y, hy, rfl⟩ : x ∈ (d.S : Set G) * (d.Y : Set G) := by
    rw [← hset]
    exact hxSY
  exact mul_mem (mem_sup_left (h.mem_commutator_S_of_mul_mem_V₃ hs hy hxV)) (mem_sup_right hy)

theorem card_V₃_le (h : d.Hyp) : Nat.card d.V₃ ≤ 2 ^ 12 := by
  set P : Subgroup G := d.S ⊔ d.Y with hP
  have hPS₃ : P ≤ d.S₃ := sup_le h.S_le_S₃ h.Y_le_S₃
  have h1 : P.relIndex d.V₃ * Nat.card (P ⊓ d.V₃ : Subgroup G) = Nat.card d.V₃ :=
    Subgroup.relIndex_mul_card P d.V₃
  have h3 : P.relIndex d.S₃ * Nat.card (P ⊓ d.S₃ : Subgroup G) = Nat.card d.S₃ :=
    Subgroup.relIndex_mul_card P d.S₃
  have hcardP : Nat.card P = 2 ^ 14 := h.card_SY
  rw [inf_eq_left.2 hPS₃, hcardP, h.card_S₃] at h3
  have hne : P.relIndex d.S₃ ≠ 0 := fun e => by
    rw [e, zero_mul] at h3
    norm_num at h3
  have h2 : P.relIndex d.V₃ ≤ P.relIndex d.S₃ :=
    Subgroup.relIndex_le_of_le_right V₃_le_S₃ hne
  have h4 : Nat.card (P ⊓ d.V₃ : Subgroup G) ≤ 2 ^ 10 := by
    have : P ⊓ d.V₃ ≤ ⁅d.S, d.S⁆ ⊔ d.Y := by
      rw [inf_comm]
      exact h.V₃_inf_SY_le
    have := Subgroup.card_le_of_le this
    rwa [h.card_S'Y] at this
  have h5 : P.relIndex d.S₃ = 4 := by omega
  calc Nat.card d.V₃ = P.relIndex d.V₃ * Nat.card (P ⊓ d.V₃ : Subgroup G) := h1.symm
    _ ≤ 4 * 2 ^ 10 := Nat.mul_le_mul (h5 ▸ h2) h4
    _ = 2 ^ 12 := by norm_num

theorem D₁_inf_Y (h : d.Hyp) : d.D₁ ⊓ d.Y = d.V₂ := by
  refine le_antisymm (fun x hx => ?_) (le_inf h.V₂_le_D₁ h.V₂_le_Y)
  obtain ⟨hxD, hxY⟩ := Subgroup.mem_inf.1 hx
  have h1 : x ∈ d.D₁ ⊓ ((normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y) :=
    Subgroup.mem_inf.2 ⟨hxD, mem_sup_right hxY⟩
  rw [h.sec4_11_4.1] at h1
  have hset := coe_mul_of_left_le_normalizer_right d.A₁ d.V₂ h.A₁_le_normalizer_V₂
  obtain ⟨a, ha, v, hv, rfl⟩ : x ∈ (d.A₁ : Set G) * (d.V₂ : Set G) := by
    rw [← hset]
    exact h1
  have haY : a ∈ d.Y := by
    have := mul_mem hxY (inv_mem (h.V₂_le_Y hv))
    rwa [mul_inv_cancel_right] at this
  have haH : a * d.t = d.t * a := h.t_comm_of_mem_L (d.pull_le_L _ ha)
  have haF : a ∈ d.F := (h.mem_F_iff_Y a).2 ⟨haY, haH⟩
  have haZ : a ∈ d.Z₂ := by
    rw [Z₂_eq]
    exact Subgroup.mem_inf.2 ⟨haF, ha⟩
  exact mul_mem (h.Z₂_le_V₂ haZ) hv

theorem D₃_inf_D₂_le_V₃ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.D₃ ⊓ d.D₂ ≤ d.V₃ := by
  intro x hx
  obtain ⟨hxD₃, hxD₂⟩ := Subgroup.mem_inf.1 hx
  refine (h.mem_V₃_iff).2 ⟨h.D₃_le_S₃' hxD₃, fun s hs => ?_⟩
  have hS₃ : d.S₃ ≤ d.D₀ ⊔ d.D₃ := by
    rw [h.S₃_eq]
    refine sup_le (sup_le ?_ (Y_le_D₀.trans le_sup_left)) le_sup_right
    rw [d.S_eq_sup]
    exact sup_le (h.A₂_le_D₀.trans le_sup_left)
      (X₂_le_A₁.trans (h.A₁_le_D₃.trans le_sup_right))
  have hle : d.D₀ ⊔ d.D₃ ≤ centModSub d.Y x := by
    refine sup_le (fun p hp => ?_) (fun u hu => ?_)
    · refine mem_centModSub.2 ⟨mem_normalizer_of_forall_comm fun n hn => Y_comm_D₀ hn hp, ?_⟩
      have := inv_mem ((h.D₂_le_cenMod_D₀ hxD₂).2 p hp)
      rwa [show (x * p * x⁻¹ * p⁻¹)⁻¹ = p * x * p⁻¹ * x⁻¹ by group] at this
    · refine mem_centModSub.2 ⟨h.S₃_le_normalizer_Y (h.D₃_le_S₃' hu), ?_⟩
      exact d.W_le_Y (h.D₁_commutator_mem_W hK (D₃_le_D₁' hu) (D₃_le_D₁' hxD₃))
  have h1 := (mem_centModSub.1 (hle (hS₃ hs))).2
  have h2 := inv_mem h1
  rwa [show (s * x * s⁻¹ * x⁻¹)⁻¹ = x * s * x⁻¹ * s⁻¹ by group] at h2

theorem card_D₃_inf_D₂_sup_Y (h : d.Hyp) :
    Nat.card (d.D₃ ⊓ d.D₂ ⊔ d.Y : Subgroup G) = 2 ^ 12 := by
  have hT : d.D₃ ⊓ d.D₂ ≤ normalizer (d.Y : Set G) := fun e he =>
    mem_normalizer_of_forall_comm fun y hy => (D₂_comm_Y' (Subgroup.mem_inf.1 he).2 hy).symm
  have e := card_sup_mul_card_inf_of_le_normalizer d.Y (d.D₃ ⊓ d.D₂) hT
  have hinf : d.Y ⊓ (d.D₃ ⊓ d.D₂) = d.V₂ := by
    refine le_antisymm (fun x hx => ?_) (le_inf h.V₂_le_Y (le_inf h.V₂_le_D₃
      (fun v hv => h.Y_le_D₂ (h.V₂_le_Y hv))))
    obtain ⟨hxY, hxT⟩ := Subgroup.mem_inf.1 hx
    have : x ∈ d.D₁ ⊓ d.Y := Subgroup.mem_inf.2 ⟨D₃_le_D₁' (Subgroup.mem_inf.1 hxT).1, hxY⟩
    rwa [h.D₁_inf_Y] at this
  rw [hinf, sup_comm, h.card_Y', h.card_D₃_inf_D₂, h.card_V₂] at e
  omega

theorem V₃_eq (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.V₃ = d.D₃ ⊓ d.D₂ ⊔ d.Y :=
  (Subgroup.eq_of_le_of_card_ge (sup_le (h.D₃_inf_D₂_le_V₃ hK) (h.Y_le_V₃))
    (by rw [h.card_D₃_inf_D₂_sup_Y]; exact h.card_V₃_le)).symm

theorem card_V₃ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    Nat.card d.V₃ = 2 ^ 12 := by
  rw [h.V₃_eq hK, h.card_D₃_inf_D₂_sup_Y]

theorem S_inf_V₃ (h : d.Hyp) : d.S ⊓ d.V₃ = ⁅d.S, d.S⁆ := by
  refine le_antisymm (fun x hx => ?_) (le_inf (commutator_S_le_A₂.trans d.A₂_le_S) fun x hx => ?_)
  · obtain ⟨hxS, hxV⟩ := Subgroup.mem_inf.1 hx
    exact h.mem_commutator_S_of_mul_mem_V₃ hxS (one_mem _) (by rwa [mul_one])
  · have hxS : x ∈ d.S := commutator_S_le_A₂.trans d.A₂_le_S hx
    refine (h.mem_V₃_iff).2 ⟨h.S_le_S₃ hxS, fun s hs => ?_⟩
    have hle : d.S ⊔ d.D₂ ≤ centModSub d.Y x := by
      refine sup_le (fun g hg => ?_) (fun e he => ?_)
      · exact mem_centModSub.2 ⟨h.S_le_normalizer_Y hg,
          h.F_le_Y (comm_mem_F_of_mem_commutator_S hx hg)⟩
      · exact mem_centModSub.2 ⟨mem_normalizer_of_forall_comm fun y hy =>
          (D₂_comm_Y' he hy).symm,
          (h.D₂_le_cenMod_D₀ he).2 x (h.A₂_le_D₀ (commutator_S_le_A₂ hx))⟩
    have h1 := (mem_centModSub.1 (hle (h.S₃_le_S_sup_D₂ hs))).2
    have h2 := inv_mem h1
    rwa [show (s * x * s⁻¹ * x⁻¹)⁻¹ = x * s * x⁻¹ * s⁻¹ by group] at h2

theorem S₃_eq_S_sup_V₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) : d.S₃ = d.S ⊔ d.V₃ := by
  have hN : d.S ≤ normalizer (d.V₃ : Set G) := fun g hg =>
    mem_normalizer_fintype fun x hx => h.conj_mem_V₃ (h.S_le_S₃ hg) hx
  have e := card_sup_mul_card_inf_of_le_normalizer d.V₃ d.S hN
  rw [inf_comm, h.S_inf_V₃, sup_comm, card_commutator_S, h.card_V₃ hK, d.card_S] at e
  refine (Subgroup.eq_of_le_of_card_ge (sup_le h.S_le_S₃ V₃_le_S₃) ?_).symm
  rw [h.card_S₃]
  omega

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
