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
theorem D₁_mul_self_mem_W (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {x : G} (hx : x ∈ d.D₁) :
    x * x ∈ d.W := by
  have hcen : ∀ w ∈ d.W, ∀ x ∈ d.D₁, w * x = x * w := fun w hw x hx =>
    mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 w hw
  let Ω : Subgroup G :=
    { carrier := {x | x ∈ d.D₁ ∧ x * x ∈ d.W}
      one_mem' := ⟨one_mem _, by rw [mul_one]; exact one_mem _⟩
      mul_mem' := by
        rintro x y ⟨hxD, hxx⟩ ⟨hyD, hyy⟩
        refine ⟨mul_mem hxD hyD, ?_⟩
        have hc : y * x * y⁻¹ * x⁻¹ ∈ d.W := h.D₁_commutator_mem_W hK hyD hxD
        have hxc : x * (y * x * y⁻¹ * x⁻¹) = (y * x * y⁻¹ * x⁻¹) * x := (hcen _ hc x hxD).symm
        have e : x * y * (x * y) = (y * x * y⁻¹ * x⁻¹) * (x * x) * (y * y) := by
          calc x * y * (x * y) = x * (y * x) * y := by group
            _ = x * ((y * x * y⁻¹ * x⁻¹) * x * y) * y := by group
            _ = (x * (y * x * y⁻¹ * x⁻¹)) * x * y * y := by group
            _ = ((y * x * y⁻¹ * x⁻¹) * x) * x * y * y := by rw [hxc]
            _ = (y * x * y⁻¹ * x⁻¹) * (x * x) * (y * y) := by group
        rw [e]
        exact mul_mem (mul_mem hc hxx) hyy
      inv_mem' := by
        rintro x ⟨hxD, hxx⟩
        refine ⟨inv_mem hxD, ?_⟩
        rw [show x⁻¹ * x⁻¹ = (x * x)⁻¹ by group]
        exact inv_mem hxx }
  have hZD : Ω ≤ d.D₁ := fun _ hx => hx.1
  have hAW : d.AW ≤ Ω := by
    refine sup_le (fun a ha => ⟨h.A₁_le_D₁ ha, h.ZX₄_le_W (mul_self_mem_ZX₄ ha)⟩)
      (fun w hw => ⟨h.W_le_D₁ hw, ?_⟩)
    rw [h.W_sq hw]
    exact one_mem _
  have hV : d.V₂ ≤ Ω := fun v hv => ⟨h.V₂_le_D₁ hv, by
    rw [h.Y_sq (h.V₂_le_Y hv)]
    exact one_mem _⟩
  have hinv : ∀ g ∈ normalizer (d.A₁ : Set G) ⊓ d.H, ∀ x ∈ Ω, g * x * g⁻¹ ∈ Ω := by
    intro g hg x hx
    have hgX := h.NHA₁_le_XW hg
    have hgW := (Subgroup.mem_inf.1 hgX).2
    refine ⟨h.conj_mem_D₁ hgX hx.1, ?_⟩
    have := (mem_normalizer_iff.1 hgW _).1 hx.2
    rwa [show g * (x * x) * g⁻¹ = g * x * g⁻¹ * (g * x * g⁻¹) by group] at this
  rcases h.eq_AW_or_eq_D₁ hZD hAW hinv with hΩ | hΩ
  · exfalso
    obtain ⟨v, hv, hvAW⟩ := h.exists_mem_V₂_not_mem_AW
    have hvΩ : v ∈ Ω := hV hv
    rw [hΩ] at hvΩ
    exact hvAW hvΩ
  · have hxΩ : x ∈ Ω := by
      rw [hΩ]
      exact hx
    exact hxΩ.2

theorem exists_mem_Z₂_not_mem_ZX₄' : ∃ g ∈ d.Z₂, g ∉ d.ZX₄ := by
  have hZ : Nat.card d.ZX₄ = 2 := by rw [Data.ZX₄, d.card_pull, card_ZX₄sub]
  by_contra hcon
  have hle : d.Z₂ ≤ d.ZX₄ := fun g hg => by
    by_contra hn
    exact hcon ⟨g, hg, hn⟩
  have := Subgroup.card_le_of_le hle
  rw [card_Z₂ (d := d), hZ] at this
  omega

theorem commutator_D₁_eq_W (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) : ⁅d.D₁, d.D₁⁆ = d.W := by
  have hCW : ⁅d.D₁, d.D₁⁆ ≤ d.W := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact h.D₁_commutator_mem_W hK hx hy
  refine le_antisymm hCW ?_
  set C : Subgroup G := ⁅d.D₁, d.D₁⁆ with hCdef
  have hz : d.z ∈ C := by
    have e : d.z = ⁅d.ι (x₂SU 1), d.ι (x₃SU F4.ω)⁆ := by
      rw [← map_commutatorElement, commutator_x₂_x₃_eq]
      rfl
    rw [e]
    exact commutator_mem_commutator
      (h.A₁_le_D₁ ⟨_, X₂sub_le_A₁sub (x₂SU_mem 1), rfl⟩)
      (h.A₁_le_D₁ ⟨_, X₃sub_le_A₁sub (x₃SU_mem _), rfl⟩)
  have hZC : d.ZX₄ ≤ C := fun a ha => by
    rcases eq_one_or_eq_z ha with rfl | rfl
    · exact one_mem _
    · exact hz
  obtain ⟨g', hg', hg'Z⟩ := exists_mem_Z₂_not_mem_ZX₄' (d := d)
  obtain ⟨v, hv, hvg⟩ := h.exists_V₂_crossed_eq hg'
  have hvY : v ∈ d.Y := h.V₂_le_Y hv
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (h.Y_sq hvY)
  have hg'Y : g' ∈ d.Y := h.F_le_Y (Z₂_le_F hg')
  have hex : ∃ a ∈ d.A₁, g' * a ≠ a * g' := by
    by_contra hcon
    refine hg'Z (mem_ZX₄_of_central (Z₂_le_A₁ hg') fun b hb => ?_)
    by_contra hne
    exact hcon ⟨b, hb, hne⟩
  obtain ⟨a, haA, hna⟩ := hex
  have hat : a * d.t = d.t * a := h.t_comm_of_mem_L (d.pull_le_L _ haA)
  have hE : a * g' * a⁻¹ ∈ d.Y := by
    have h1 := Z₂_comm_S hg' (d.A₁_le_S haA)
    have hZZ : d.ZX₄ ≤ d.Z₂ := by
      rw [Z₂_eq_sup]
      exact le_sup_right
    have h2 : a * g' * a⁻¹ ∈ d.Z₂ := by
      rw [show a * g' * a⁻¹ = (a * g' * a⁻¹ * g'⁻¹) * g' by group]
      exact mul_mem (hZZ h1) hg'
    exact h.F_le_Y (Z₂_le_F h2)
  have hvE : v * (a * g' * a⁻¹) = (a * g' * a⁻¹) * v := h.Y_comm hvY hE
  have hvD : v ∈ d.D₁ := h.V₂_le_D₁ hv
  have haD : a ∈ d.D₁ := h.A₁_le_D₁ haA
  have hcC : v * a * v⁻¹ * a⁻¹ ∈ C := by
    have := commutator_mem_commutator hvD haD
    rwa [commutatorElement_def] at this
  have hcW : v * a * v⁻¹ * a⁻¹ ∈ d.W := h.D₁_commutator_mem_W hK hvD haD
  have hcnZ : v * a * v⁻¹ * a⁻¹ ∉ d.ZX₄ := by
    intro hcZ
    have hct : (v * a * v⁻¹ * a⁻¹) * d.t = d.t * (v * a * v⁻¹ * a⁻¹) :=
      ((h.mem_ZX₄_iff_W _).1 hcZ).2
    have e1 : (v * a * v⁻¹ * a⁻¹) * d.t * (v * a * v⁻¹ * a⁻¹)⁻¹ = d.t := by
      rw [hct]
      group
    have hv_t : v⁻¹ * d.t * v = g' * d.t := by
      calc v⁻¹ * d.t * v = v⁻¹ * d.t * v * d.t * d.t := by
            rw [mul_assoc (v⁻¹ * d.t * v) d.t d.t, h.t_mul_t, mul_one]
        _ = g' * d.t := by rw [hvg]
    have hat' : a⁻¹ * d.t * a = d.t := by rw [mul_assoc, ← hat, inv_mul_cancel_left]
    have hat'' : a * d.t * a⁻¹ = d.t := by rw [hat, mul_inv_cancel_right]
    have e2 : (v * a * v⁻¹ * a⁻¹) * d.t * (v * a * v⁻¹ * a⁻¹)⁻¹ = (a * g' * a⁻¹) * g' * d.t := by
      calc (v * a * v⁻¹ * a⁻¹) * d.t * (v * a * v⁻¹ * a⁻¹)⁻¹
          = v * a * v⁻¹ * (a⁻¹ * d.t * a) * v * a⁻¹ * v⁻¹ := by group
        _ = v * a * (v⁻¹ * d.t * v) * a⁻¹ * v⁻¹ := by rw [hat']; group
        _ = v * a * (g' * d.t) * a⁻¹ * v⁻¹ := by rw [hv_t]
        _ = v * (a * g' * a⁻¹) * (a * d.t * a⁻¹) * v⁻¹ := by group
        _ = v * (a * g' * a⁻¹) * d.t * v⁻¹ := by rw [hat'']
        _ = (a * g' * a⁻¹) * (v * d.t * v⁻¹) := by rw [hvE]; group
        _ = (a * g' * a⁻¹) * (g' * d.t) := by
            rw [hvi]
            rw [hvi] at hv_t
            rw [hv_t]
        _ = (a * g' * a⁻¹) * g' * d.t := by group
    have e3 : (a * g' * a⁻¹) * g' = 1 := by
      have := e2.symm.trans e1
      exact mul_right_cancel (this.trans (one_mul _).symm)
    have e4 : a * g' * a⁻¹ = g' := mul_right_cancel (e3.trans (h.Y_sq hg'Y).symm)
    exact hna (mul_inv_eq_iff_eq_mul.1 e4).symm
  have hlt : d.ZX₄ < C := lt_of_le_of_ne hZC fun e => hcnZ (e ▸ hcC)
  have hZ : Nat.card d.ZX₄ = 2 := by rw [Data.ZX₄, d.card_pull, card_ZX₄sub]
  have hW4 : Nat.card d.W = 4 := h.sec4_9_W.1
  have hd1 : Nat.card C ∣ 4 := hW4 ▸ Subgroup.card_dvd_of_le hCW
  have hd2 : 2 ∣ Nat.card C := hZ ▸ Subgroup.card_dvd_of_le hZC
  have hne : Nat.card C ≠ 2 := fun e => hlt.ne (Subgroup.eq_of_le_of_card_ge hZC (by omega))
  have hle4 : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) hd1
  have hpos : 0 < Nat.card C := Nat.card_pos
  exact (Subgroup.eq_of_le_of_card_ge hCW (by omega)) ▸ le_rfl

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
