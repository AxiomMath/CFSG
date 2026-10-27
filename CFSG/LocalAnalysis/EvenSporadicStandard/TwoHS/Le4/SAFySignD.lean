module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFySignC
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyWrMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

abbrev K0 : Subgroup (Equiv.Perm (Fin 5)) := centralizer ({v0} : Set (Equiv.Perm (Fin 5)))

set_option maxRecDepth 100000 in
theorem card_K0 : Nat.card K0 = 8 := by
  have h1 : Nat.card K0 = Nat.card {σ : Equiv.Perm (Fin 5) // σ * v0 = v0 * σ} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun σ => mem_centralizer_singleton_iff)
  rw [h1, Nat.card_eq_fintype_card]
  decide

@[expose] def kap : ↥K0 := ⟨v0, mem_centralizer_singleton_iff.2 rfl⟩

theorem kap_ne_one : kap ≠ 1 := fun h => v0_ne_one (congrArg Subtype.val h)

theorem kap_comm (b : ↥K0) : b * kap = kap * b :=
  Subtype.ext (mem_centralizer_singleton_iff.1 b.2)

set_option maxRecDepth 100000 in
theorem perm5_k0_center : ∀ b : Equiv.Perm (Fin 5), b * v0 = v0 * b →
    (∀ c : Equiv.Perm (Fin 5), c * v0 = v0 * c → c * b = b * c) → b = 1 ∨ b = v0 := by decide

theorem kap_center : ∀ b : ↥K0, (∀ c : ↥K0, c * b = b * c) → b = 1 ∨ b = kap := by
  intro b hb
  have := perm5_k0_center b.1 (mem_centralizer_singleton_iff.1 b.2) fun c hc =>
    congrArg Subtype.val (hb ⟨c, mem_centralizer_singleton_iff.2 hc⟩)
  rcases this with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem d8_mul_r2 : ∀ d : DihedralGroup 4, d * DihedralGroup.r 2 = DihedralGroup.r 2 * d := by
  decide

@[expose] def embK : DihedralGroup 4 × ↥K0 →* HModel where
  toFun p := (p.1, 1, (p.2 : Equiv.Perm (Fin 5)))
  map_one' := rfl
  map_mul' a b := by ext <;> simp

variable {G : Type} [Group G] [Finite G] {t r : G} {Θ : HModel →* G}

theorem FyConf.center_eq_bot (h : FyConf t r Θ) : center (RedX r) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzc := Subgroup.mem_center_iff.1 hz
  obtain ⟨⟨d, c, σ⟩, rfl⟩ := h.exists_lift z (hzc h.tauX).symm
  have hcomm := fun m' : HModel => (h.Phi_comm_iff m' (d, c, σ)).1 (hzc (h.Phi m'))
  have hd : d = 1 ∨ d = DihedralGroup.r 2 := d8_center d fun d' => (hcomm (d', 1, 1)).1
  have hσ : σ = 1 := CFSG.perm_eq_one_of_forall_commute (by simp) fun τ =>
    ((hcomm (1, 1, τ)).2).symm
  subst hσ
  have hcz : h.Phi (1, c, 1) = 1 := (h.Phi_eq_one_iff _).2 ⟨rfl, rfl⟩
  have hsplit : h.Phi (d, c, 1) = h.Phi (d, 1, 1) := by
    have : ((d, c, 1) : HModel) = (d, 1, 1) * (1, c, 1) := by ext <;> simp
    rw [this, map_mul, hcz, mul_one]
  rcases hd with rfl | rfl
  · rw [hsplit]
    exact (h.Phi_eq_one_iff _).2 ⟨rfl, rfl⟩
  · exfalso
    obtain ⟨δ, hδ, ⟨x, hx⟩, -⟩ := h.exists_delta
    have hxz := hzc x
    rw [hsplit] at hxz
    have hcen : x * h.tauX * x⁻¹ = h.tauX := by
      have h1 : x * h.tauX = h.tauX * x := hxz
      calc x * h.tauX * x⁻¹ = h.tauX * x * x⁻¹ := by rw [h1]
        _ = h.tauX := by group
    have hw : h.Phi (δ, 1, v0) = h.tauX := hx.symm.trans hcen
    have h1 : h.Phi ((δ, 1, v0) * (DihedralGroup.r 2, 1, 1)) = 1 := by
      rw [map_mul, hw]
      exact h.tauX_sq
    have h2 := ((h.Phi_eq_one_iff _).1 h1).2
    exact v0_ne_one (by simpa using h2)

theorem FyConf.exists_sylow (h : FyConf t r Θ) :
    ∃ P : Sylow 2 (RedX r), Nonempty (↥P ≃* W8) := by
  obtain ⟨δ, hδ, ⟨x₀, hx₀⟩, hnc⟩ := h.exists_delta
  have hΨ : Function.Injective (h.Phi.comp embK) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨d, k⟩ hk
    have := (h.Phi_eq_one_iff (embK (d, k))).1 hk
    exact Prod.ext this.1 (Subtype.ext this.2)
  have hQ : ∀ y : RedX r, (y * h.tauX = h.tauX * y ∧
      y * h.Phi (δ, 1, v0) = h.Phi (δ, 1, v0) * y) ↔ y ∈ (h.Phi.comp embK).range := by
    intro y
    constructor
    · rintro ⟨hyt, hyv⟩
      obtain ⟨⟨d, c, σ⟩, rfl⟩ := h.exists_lift y hyt
      have h3 := ((h.Phi_comm_iff (d, c, σ) (δ, 1, v0)).1 hyv).2
      refine ⟨(d, ⟨σ, mem_centralizer_singleton_iff.2 h3⟩), ?_⟩
      have hcz : h.Phi (1, c, 1) = 1 := (h.Phi_eq_one_iff _).2 ⟨rfl, rfl⟩
      have : ((d, c, σ) : HModel) = (d, 1, σ) * (1, c, 1) := by ext <;> simp
      show h.Phi (d, 1, σ) = h.Phi (d, c, σ)
      rw [this, map_mul, hcz, mul_one]
    · rintro ⟨p, rfl⟩
      refine ⟨h.Phi_comm_tau (embK p), ?_⟩
      refine (h.Phi_comm_iff (embK p) (δ, 1, v0)).2 ⟨?_, ?_⟩
      · show p.1 * δ = δ * p.1
        rcases hδ with rfl | rfl
        · simp
        · exact d8_mul_r2 p.1
      · exact mem_centralizer_singleton_iff.1 p.2.2
  exact exists_sylow_wreath card_K0 (h.Phi.comp embK) hΨ kap kap_ne_one kap_comm kap_center
    δ hδ rfl rfl hQ h.card_cent hx₀ hnc

end CFSG.EvenSporadicStandard.TwoHS
