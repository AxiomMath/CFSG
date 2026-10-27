module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card

import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.GroupTheory

theorem four_dvd_card_sub_card_fixedBy {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]
    [Finite Ω] {t : G} (ht : t ^ 2 = 1) (htG : t ∈ _root_.commutator G) :
    4 ∣ Nat.card Ω - Nat.card (MulAction.fixedBy Ω t) := by
  classical
  haveI : Fintype Ω := Fintype.ofFinite Ω
  let π : G →* Equiv.Perm Ω := MulAction.toPermHom G Ω
  have hsign : Equiv.Perm.sign (π t) = 1 := by
    have h := Abelianization.commutator_subset_ker
      ((Equiv.Perm.sign : Equiv.Perm Ω →* ℤˣ).comp π) htG
    exact MonoidHom.mem_ker.mp h
  have hpow : π t ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hfix : Function.fixedPoints (π t) = MulAction.fixedBy Ω t := by
    ext x
    simp [π, Function.fixedPoints, Function.IsFixedPt, MulAction.mem_fixedBy]
  have h2 := Equiv.Perm.sign_of_pow_two_eq_one hpow
  rw [hsign] at h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hev : Even ((Fintype.card Ω - Fintype.card (Function.fixedPoints (π t))) / 2) :=
    (neg_one_pow_eq_one_iff_even (by decide)).mp h2.symm
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one (σ := π t) hpow
  have hsum : (π t).cycleType.sum = (π t).cycleType.card * 2 := by
    rw [hct]
    simp
  have hfc := Equiv.Perm.card_fixedPoints (π t)
  have hle := Equiv.Perm.sum_cycleType_le (π t)
  have hdiff : Fintype.card Ω - Fintype.card (Function.fixedPoints (π t)) =
      (π t).cycleType.card * 2 := by omega
  rw [hdiff, Nat.mul_div_cancel _ (by norm_num)] at hev
  obtain ⟨m, hm⟩ := hev
  rw [← hfix, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [hdiff, hm]
  exact ⟨m, by ring⟩

theorem card_fixedBy_quotient_mul_card {G : Type*} [Group G] [Finite G] (L : Subgroup G) (t : G) :
    Nat.card (MulAction.fixedBy (G ⧸ L) t) * Nat.card L =
      Nat.card (Subgroup.centralizer ({t} : Set G)) *
        Set.ncard {y : G | IsConj t y ∧ y ∈ L} := by
  classical
  let P : Set G := {g | g⁻¹ * t * g ∈ L}
  have hPpre : P = (QuotientGroup.mk : G → G ⧸ L) ⁻¹' (MulAction.fixedBy (G ⧸ L) t) := by
    ext g
    simp only [P, Set.mem_setOf_eq, Set.mem_preimage, MulAction.mem_fixedBy]
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
    have : (t * g)⁻¹ * g = (g⁻¹ * t * g)⁻¹ := by group
    rw [this, inv_mem_iff]
  have h1 : Nat.card ↥P = Nat.card L * Nat.card (MulAction.fixedBy (G ⧸ L) t) := by
    rw [hPpre, Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet L _), Nat.card_prod]
  let T : Set G := {y | IsConj t y ∧ y ∈ L}
  have hex : ∀ y : T, ∃ g : G, g⁻¹ * t * g = y := by
    intro y
    obtain ⟨c, hc⟩ := isConj_iff.mp y.2.1
    exact ⟨c⁻¹, by simpa using hc⟩
  choose gy hgy using hex
  have hcent : ∀ c g : G, c * t = t * c → (c * g)⁻¹ * t * (c * g) = g⁻¹ * t * g := by
    intro c g hc
    have h : c⁻¹ * t * c = t := by
      calc c⁻¹ * t * c = c⁻¹ * (t * c) := mul_assoc _ _ _
        _ = c⁻¹ * (c * t) := by rw [hc]
        _ = t := inv_mul_cancel_left c t
    calc (c * g)⁻¹ * t * (c * g) = g⁻¹ * (c⁻¹ * t * c) * g := by group
      _ = g⁻¹ * t * g := by rw [h]
  let Ψ : ↥(Subgroup.centralizer ({t} : Set G)) × ↥T → ↥P := fun p =>
    ⟨p.1.1 * gy p.2, by
      show (p.1.1 * gy p.2)⁻¹ * t * (p.1.1 * gy p.2) ∈ L
      rw [hcent _ _ (Subgroup.mem_centralizer_singleton_iff.mp p.1.2), hgy]
      exact p.2.2.2⟩
  have hΨ : ∀ p, (Ψ p : G) = p.1.1 * gy p.2 := fun p => rfl
  have hinj : Function.Injective Ψ := by
    intro p q hpq
    have h : p.1.1 * gy p.2 = q.1.1 * gy q.2 := congrArg Subtype.val hpq
    have hy : (p.2 : G) = q.2 := by
      have e1 := hcent _ (gy p.2) (Subgroup.mem_centralizer_singleton_iff.mp p.1.2)
      have e2 := hcent _ (gy q.2) (Subgroup.mem_centralizer_singleton_iff.mp q.1.2)
      rw [hgy] at e1 e2
      rw [← e1, ← e2, h]
    have hyy : p.2 = q.2 := Subtype.ext hy
    have hc : p.1.1 = q.1.1 := by
      rw [hyy] at h
      exact mul_right_cancel h
    exact Prod.ext (Subtype.ext hc) hyy
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨g, hg⟩
    have hgT : g⁻¹ * t * g ∈ T :=
      ⟨isConj_iff.mpr ⟨g⁻¹, by simp⟩, hg⟩
    set y : T := ⟨g⁻¹ * t * g, hgT⟩ with hy
    have hcent' : g * (gy y)⁻¹ * t = t * (g * (gy y)⁻¹) := by
      have h := hgy y
      have h' : g⁻¹ * t * g = (gy y)⁻¹ * t * gy y := h.symm
      calc g * (gy y)⁻¹ * t = g * (gy y)⁻¹ * t * (gy y * g⁻¹) * (g * (gy y)⁻¹) := by group
        _ = g * ((gy y)⁻¹ * t * gy y) * g⁻¹ * (g * (gy y)⁻¹) := by group
        _ = g * (g⁻¹ * t * g) * g⁻¹ * (g * (gy y)⁻¹) := by rw [← h']
        _ = t * (g * (gy y)⁻¹) := by group
    refine ⟨(⟨g * (gy y)⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr hcent'⟩, y), ?_⟩
    apply Subtype.ext
    simp [hΨ]
  have h2 : Nat.card ↥P =
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) * Set.ncard T := by
    rw [← Nat.card_coe_set_eq T, ← Nat.card_prod]
    exact (Nat.card_congr (Equiv.ofBijective Ψ ⟨hinj, hsurj⟩)).symm
  rw [mul_comm (Nat.card (MulAction.fixedBy (G ⧸ L) t)), ← h1, h2]

end CFSG.GroupTheory
