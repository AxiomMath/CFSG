module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
import all Mathlib.GroupTheory.Perm.Cycle.Factors

public section

namespace CFSG.ComponentClassification.HSFLit

open Equiv Equiv.Perm Subgroup
open scoped Pointwise

abbrev a0 : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3

abbrev b0 : Perm (Fin 7) := swap 0 2

abbrev c0 : Perm (Fin 7) := swap 4 5

abbrev rho0 : Perm (Fin 7) := a0 * c0

theorem rho0_cycleType : rho0.cycleType = {4, 2} := by decide

theorem card_centralizer_rho : Nat.card (centralizer ({rho0} : Set (Perm (Fin 7)))) = 8 := by
  rw [Equiv.Perm.nat_card_centralizer, rho0_cycleType]
  simp

theorem card_sup_eq_mul_of_le_normalizer {G : Type*} [Group G] {N H : Subgroup G}
    (hle : H ≤ normalizer (N : Set G)) (hdisj : N ⊓ H = ⊥) :
    Nat.card (N ⊔ H : Subgroup G) = Nat.card N * Nat.card H := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : N × H => (⟨p.1 * p.2, mul_mem_sup p.1.2 p.2.2⟩ : (N ⊔ H : Subgroup G))) ⟨?_, ?_⟩)
  · rintro ⟨n, k⟩ ⟨n', k'⟩ he
    have he' : (n : G) * k = n' * k' := congrArg Subtype.val he
    have hmem : (n' : G)⁻¹ * n ∈ N ⊓ H := by
      refine ⟨N.mul_mem (N.inv_mem n'.2) n.2, ?_⟩
      have heq : (n' : G)⁻¹ * n = k' * (k : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← he', mul_inv_cancel_right]
      rw [heq]
      exact H.mul_mem k'.2 (H.inv_mem k.2)
    rw [hdisj, mem_bot, inv_mul_eq_one] at hmem
    have hn : n' = n := Subtype.ext hmem
    subst hn
    rw [Subtype.ext (mul_left_cancel he')]
  · rintro ⟨g, hg⟩
    have hg' : g ∈ (N : Set G) * (H : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left N H hle]
      exact hg
    obtain ⟨n, hn, k, hk, rfl⟩ := hg'
    exact ⟨(⟨n, hn⟩, ⟨k, hk⟩), rfl⟩

theorem a0_c0_comm : a0 * c0 = c0 * a0 := by decide

theorem b0_c0_comm : b0 * c0 = c0 * b0 := by decide

theorem orderOf_a0 : orderOf a0 = 4 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · decide
  · decide

theorem orderOf_rho0 : orderOf rho0 = 4 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · decide
  · decide

theorem b0_rho0 : b0 * rho0 * b0⁻¹ = rho0⁻¹ := by decide

theorem b0_not_mem_centralizer : b0 ∉ centralizer ({rho0} : Set (Perm (Fin 7))) := by
  rw [mem_centralizer_singleton_iff]
  decide

theorem sign_b0 : Perm.sign b0 = -1 := Perm.sign_swap (by decide)

theorem sign_c0 : Perm.sign c0 = -1 := Perm.sign_swap (by decide)

theorem centralizer_rho0_eq :
    centralizer ({rho0} : Set (Perm (Fin 7))) = zpowers a0 ⊔ zpowers c0 := by
  have hle : zpowers a0 ⊔ zpowers c0 ≤ centralizer ({rho0} : Set (Perm (Fin 7))) := by
    rw [sup_le_iff, zpowers_le, zpowers_le, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff]
    constructor <;> decide
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_centralizer_rho]
  have hcN : zpowers c0 ≤ normalizer (zpowers a0 : Set (Perm (Fin 7))) := by
    rw [zpowers_le]
    exact centralizer_le_normalizer _ (by
      rw [mem_centralizer_iff]
      intro g hg
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      exact ((Commute.zpow_left a0_c0_comm k)).eq)
  have hfix : ∀ g ∈ zpowers a0, g 4 = 4 := by
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    have h4 : a0 4 = 4 := by decide
    exact zpow_apply_eq_self_of_apply_eq_self h4 k
  have hdisj : zpowers a0 ⊓ zpowers c0 = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hga, hgc⟩
    have hc2 : c0 * c0 = 1 := by decide
    have : g = 1 ∨ g = c0 := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hgc
      rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
      · left; rw [zpow_mul, show c0 ^ (2 : ℤ) = 1 by rw [zpow_two, hc2], one_zpow]
      · right; rw [zpow_add, zpow_mul, show c0 ^ (2 : ℤ) = 1 by rw [zpow_two, hc2], one_zpow,
          one_mul, zpow_one]
    rcases this with rfl | rfl
    · exact one_mem _
    · exfalso
      have := hfix c0 hga
      revert this
      decide
  rw [card_sup_eq_mul_of_le_normalizer hcN hdisj, Nat.card_zpowers, Nat.card_zpowers, orderOf_a0,
    orderOf_eq_prime (by decide : c0 ^ 2 = 1) (by decide : c0 ≠ 1)]

abbrev P0 : Subgroup (Perm (Fin 7)) := normalizer (zpowers rho0 : Set (Perm (Fin 7)))

abbrev R0 : Subgroup (Perm (Fin 7)) := P0 ⊓ alternatingGroup (Fin 7)

theorem eq_or_eq_inv_of_orderOf_eq_four {G : Type*} [Group G] {x u : G} (hx4 : orderOf x = 4)
    (hu : u ∈ zpowers x) (hu4 : orderOf u = 4) : u = x ∨ u = x⁻¹ := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
  rw [← zpow_mod_orderOf, hx4] at hu4 ⊢
  have h0 : 0 ≤ i % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h4 : i % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, i % ((4 : ℕ) : ℤ) = r := ⟨(i % ((4 : ℕ) : ℤ)).toNat, by omega⟩
  rw [hr] at hu4 ⊢
  have hr4 : r < 4 := by omega
  rw [zpow_natCast] at hu4 ⊢
  have hx4' : x ^ 4 = 1 := by rw [← hx4, pow_orderOf_eq_one]
  interval_cases r
  · rw [pow_zero, orderOf_one] at hu4; norm_num at hu4
  · exact Or.inl (pow_one x)
  · exfalso
    have h2 : (x ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hx4'
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hu4] at this
    norm_num at this
  · right
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx4']

theorem mem_normalizer_zpowers_of_conj_mem {G : Type*} [Group G] [Finite G] {g x : G}
    (h : g * x * g⁻¹ ∈ zpowers x) : g ∈ normalizer (zpowers x : Set G) := by
  have hle : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ zpowers x := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    exact h
  have heq : (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← heq]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← heq] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    have : w = y := by
      have := congrArg (fun z => g⁻¹ * z * g) hwy
      simpa [MulAut.conj_apply, mul_assoc] using this
    rw [← this]; exact hw

theorem centralizer_zpowers_eq_singleton {G : Type*} [Group G] (x : G) :
    centralizer (zpowers x : Set G) = centralizer ({x} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem b0_mem_P0 : b0 ∈ P0 :=
  mem_normalizer_zpowers_of_conj_mem (by rw [b0_rho0]; exact inv_mem (mem_zpowers _))

theorem mem_P0_iff (σ : Perm (Fin 7)) :
    σ ∈ P0 ↔ σ ∈ centralizer ({rho0} : Set (Perm (Fin 7))) ∨
      σ * b0 ∈ centralizer ({rho0} : Set (Perm (Fin 7))) := by
  constructor
  · intro hσ
    have h1 : σ * rho0 * σ⁻¹ ∈ zpowers rho0 := (mem_normalizer_iff.mp hσ rho0).mp (mem_zpowers _)
    have h2 : orderOf (σ * rho0 * σ⁻¹) = 4 := by
      rw [show σ * rho0 * σ⁻¹ = MulAut.conj σ rho0 from rfl, MulEquiv.orderOf_eq, orderOf_rho0]
    rcases eq_or_eq_inv_of_orderOf_eq_four orderOf_rho0 h1 h2 with h3 | h3
    · left
      rw [mem_centralizer_singleton_iff]
      calc σ * rho0 = σ * rho0 * σ⁻¹ * σ := by group
        _ = rho0 * σ := by rw [h3]
    · right
      rw [mem_centralizer_singleton_iff]
      have hb : b0 * rho0 = rho0⁻¹ * b0 := by
        rw [← b0_rho0]; group
      symm
      calc rho0 * (σ * b0) = (σ * rho0 * σ⁻¹)⁻¹ * σ * b0 := by rw [h3, inv_inv]; group
        _ = σ * rho0⁻¹ * b0 := by group
        _ = σ * (b0 * rho0) := by rw [hb]; group
        _ = σ * b0 * rho0 := by group
  · rintro (h1 | h1)
    · rw [← centralizer_zpowers_eq_singleton] at h1
      exact centralizer_le_normalizer _ h1
    · rw [← centralizer_zpowers_eq_singleton] at h1
      have h2 := centralizer_le_normalizer _ h1
      have := mul_mem h2 b0_mem_P0
      rwa [mul_assoc, ← sq, show b0 ^ 2 = 1 by decide, mul_one] at this

theorem card_P0 : Nat.card P0 = 16 := by
  have hC : centralizer ({rho0} : Set (Perm (Fin 7))) ≤ P0 := by
    rw [← centralizer_zpowers_eq_singleton]; exact centralizer_le_normalizer _
  have hidx : ((centralizer ({rho0} : Set (Perm (Fin 7)))).subgroupOf P0).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨b0, b0_mem_P0⟩, fun σ => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    rcases (mem_P0_iff σ).mp σ.2 with h1 | h1
    · refine Or.inr ⟨h1, fun h2 => b0_not_mem_centralizer ?_⟩
      have := mul_mem (inv_mem h1) h2
      simpa using this
    · refine Or.inl ⟨h1, fun h2 => b0_not_mem_centralizer ?_⟩
      have := mul_mem (inv_mem h2) h1
      simpa using this
  have h := Subgroup.card_mul_index ((centralizer ({rho0} : Set (Perm (Fin 7)))).subgroupOf P0)
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv, card_centralizer_rho] at h
  omega

theorem c0_mem_centralizer : c0 ∈ centralizer ({rho0} : Set (Perm (Fin 7))) := by
  rw [mem_centralizer_singleton_iff]; decide

theorem c0_mem_P0 : c0 ∈ P0 := by
  have h := c0_mem_centralizer
  rw [← centralizer_zpowers_eq_singleton] at h
  exact centralizer_le_normalizer _ h

theorem a0_mem_P0 : a0 ∈ P0 := by
  have h : a0 ∈ centralizer ({rho0} : Set (Perm (Fin 7))) := by
    rw [mem_centralizer_singleton_iff]; decide
  rw [← centralizer_zpowers_eq_singleton] at h
  exact centralizer_le_normalizer _ h

theorem c0_comm_of_mem_P0 {σ : Perm (Fin 7)} (hσ : σ ∈ P0) : σ * c0 = c0 * σ := by
  have hCc : ∀ τ ∈ centralizer ({rho0} : Set (Perm (Fin 7))), τ * c0 = c0 * τ := by
    intro τ hτ
    rw [centralizer_rho0_eq] at hτ
    have hle : zpowers a0 ⊔ zpowers c0 ≤ centralizer ({c0} : Set (Perm (Fin 7))) := by
      rw [sup_le_iff, zpowers_le, zpowers_le, mem_centralizer_singleton_iff,
        mem_centralizer_singleton_iff]
      exact ⟨a0_c0_comm, rfl⟩
    exact mem_centralizer_singleton_iff.mp (hle hτ)
  rcases (mem_P0_iff σ).mp hσ with h1 | h1
  · exact hCc σ h1
  · have h2 := hCc _ h1
    have hσ' : σ = σ * b0 * b0 := by rw [mul_assoc, show b0 * b0 = 1 by decide, mul_one]
    rw [hσ', mul_assoc, b0_c0_comm, ← mul_assoc, h2, mul_assoc]

theorem P0_le_closure : P0 ≤ closure ({a0, b0, c0} : Set (Perm (Fin 7))) := by
  intro σ hσ
  have hC : centralizer ({rho0} : Set (Perm (Fin 7))) ≤ closure ({a0, b0, c0} : Set _) := by
    rw [centralizer_rho0_eq, sup_le_iff, zpowers_le, zpowers_le]
    exact ⟨subset_closure (by simp), subset_closure (by simp)⟩
  rcases (mem_P0_iff σ).mp hσ with h1 | h1
  · exact hC h1
  · have := mul_mem (hC h1) (subset_closure (by simp) : b0 ∈ closure ({a0, b0, c0} : Set _))
    rwa [mul_assoc, show b0 * b0 = 1 by decide, mul_one] at this

theorem card_R0 : Nat.card R0 = 8 := by
  have hidx : (R0.subgroupOf P0).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨b0, b0_mem_P0⟩, fun σ => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    have h1 : ((σ * ⟨b0, b0_mem_P0⟩ : P0) : Perm (Fin 7)) ∈ R0 ↔
        Perm.sign (σ : Perm (Fin 7)) = -1 := by
      rw [Subgroup.coe_mul]
      constructor
      · rintro ⟨-, h⟩
        change _ ∈ alternatingGroup (Fin 7) at h
        rw [Perm.mem_alternatingGroup, Perm.sign_mul, sign_b0] at h
        rcases Int.units_eq_one_or (Perm.sign (σ : Perm (Fin 7))) with h' | h'
        · rw [h'] at h; exact absurd h (by decide)
        · exact h'
      · intro h
        refine ⟨mul_mem σ.2 b0_mem_P0, ?_⟩
        change _ ∈ alternatingGroup (Fin 7)
        rw [Perm.mem_alternatingGroup, Perm.sign_mul, sign_b0, h]
        rfl
    have h2 : (σ : Perm (Fin 7)) ∈ R0 ↔ Perm.sign (σ : Perm (Fin 7)) = 1 :=
      ⟨fun h => h.2, fun h => ⟨σ.2, h⟩⟩
    rw [h1, h2]
    rcases Int.units_eq_one_or (Perm.sign (σ : Perm (Fin 7))) with h | h <;> simp [h]
  have h := Subgroup.card_mul_index (R0.subgroupOf P0)
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : R0 ≤ P0)).toEquiv] at h
  have h16 := card_P0
  change Nat.card ↥(P0 ⊓ alternatingGroup (Fin 7)) = 8
  omega

theorem mem_R0_or_mul_c0_mem_R0 {σ : Perm (Fin 7)} (hσ : σ ∈ P0) : σ ∈ R0 ∨ σ * c0 ∈ R0 := by
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h
  · exact Or.inl ⟨hσ, h⟩
  · refine Or.inr ⟨mul_mem hσ c0_mem_P0, ?_⟩
    change _ ∈ alternatingGroup (Fin 7)
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, h, sign_c0]
    rfl

theorem c0_not_mem_alternating : c0 ∉ alternatingGroup (Fin 7) := by
  intro h
  have := Perm.mem_alternatingGroup.mp h
  rw [sign_c0] at this
  exact absurd this (by decide)

theorem factorization_card_perm_seven : (Nat.card (Perm (Fin 7))).factorization 2 = 4 := by
  rw [Nat.card_perm, Nat.card_fin, show Nat.factorial 7 = 2 ^ 4 * 315 by decide,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (315 : ℕ))]

noncomputable def sylowP0 : Sylow 2 (Perm (Fin 7)) :=
  Sylow.ofCard (p := 2) P0 (by rw [card_P0, factorization_card_perm_seven]; norm_num)

theorem coe_sylowP0 : (sylowP0 : Subgroup (Perm (Fin 7))) = P0 := Sylow.coe_ofCard _ _

end CFSG.ComponentClassification.HSFLit
