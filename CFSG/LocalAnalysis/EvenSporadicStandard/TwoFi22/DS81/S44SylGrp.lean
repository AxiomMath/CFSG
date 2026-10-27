module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44SylFix
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.Simproc.Divisors

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44.Syl

open Subgroup MulAction

section Group

variable {V : Type} [CommGroup V] [Finite V] {G : Type} [Group G] [Finite G]

theorem card_centralizer_dvd (hV : Nat.card V = 2 ^ 11) (ρ : G →* MulAut V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : TwoOrderGe11 p) {g : G} (hg : orderOf g = p) :
    Nat.card (centralizer (zpowers g : Set G)) ∣ Nat.card V - 1 := by
  have ha : ρ g ^ p = 1 := by rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
  have ha1 : ρ g ≠ 1 := by
    intro h
    have : g = 1 := hρ (h.trans (map_one ρ).symm)
    rw [this, orderOf_one] at hg
    exact hp.prime.one_lt.ne hg
  let _ : MulAction (centralizer (zpowers g : Set G)) V :=
    MulAction.compHom V (ρ.comp (centralizer (zpowers g : Set G)).subtype)
  refine card_dvd_of_free (V := V) (H := centralizer (zpowers g : Set G)) ?_ ?_
  · intro c
    exact map_one (ρ c.1)
  · intro c v hv hcv
    have hcomm : Commute (ρ c.1) (ρ g) := by
      have := (mem_centralizer_iff.1 c.2) g (mem_zpowers g)
      exact (Commute.map (show Commute g c.1 from this) ρ).symm
    have h1 : ρ c.1 = 1 := eq_one_of_commute hV hp ha ha1 hcomm hv hcv
    exact Subtype.ext (hρ (h1.trans (map_one ρ).symm))

theorem card_normalizer_dvd (hV : Nat.card V = 2 ^ 11) (ρ : G →* MulAut V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : TwoOrderGe11 p) {g : G} (hg : orderOf g = p) :
    Nat.card (normalizer (zpowers g : Set G)) ∣ (Nat.card V - 1) * (p - 1) := by
  classical
  have hHc : Nat.card (zpowers g) = p := by rw [Nat.card_zpowers, hg]
  have key : Nat.card (normalizer (zpowers g : Set G) ⧸ (zpowers g).normalizerMonoidHom.ker) ∣
      Nat.card (MulAut (zpowers g)) :=
    card_dvd_of_injective _ (QuotientGroup.kerLift_injective _)
  have hAut : Nat.card (MulAut (zpowers g)) = p - 1 := by
    rw [IsCyclic.card_mulAut, hHc, Nat.totient_prime hp.prime]
  have hker : (zpowers g).normalizerMonoidHom.ker =
      (centralizer (zpowers g : Set G)).subgroupOf (normalizer (zpowers g : Set G)) :=
    normalizerMonoidHom_ker _
  have hkc : Nat.card (zpowers g).normalizerMonoidHom.ker =
      Nat.card (centralizer (zpowers g : Set G)) := by
    rw [hker]
    exact Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer _)).toEquiv
  have := Subgroup.card_mul_index (zpowers g).normalizerMonoidHom.ker
  rw [← this, hkc, Subgroup.index_eq_card]
  exact mul_dvd_mul (card_centralizer_dvd hV ρ hρ hp hg) (hAut ▸ key)

end Group

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem card_sylow_eq_prime {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card G)
    (hp2 : ¬ p ^ 2 ∣ Nat.card G) (P : Sylow p G) : Nat.card P = p := by
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hpr : p.Prime := Fact.out
  have h1 : 1 ≤ (Nat.card G).factorization p := (hpr.dvd_iff_one_le_factorization hG0).1 hp
  have h2 : ¬ 2 ≤ (Nat.card G).factorization p := fun h =>
    hp2 ((hpr.pow_dvd_iff_le_factorization hG0).2 h)
  have hfac : (Nat.card G).factorization p = 1 := by omega
  rw [P.card_eq_multiplicity, hfac, pow_one]

theorem exists_gen_of_card_prime {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : Nat.card P = p) :
    ∃ g : G, orderOf g = p ∧ P = zpowers g := by
  have : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P)
  have hord : orderOf (g : G) = p := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hP]
  refine ⟨g, hord, (eq_of_le_of_card_ge ?_ ?_).symm⟩
  · exact zpowers_le.2 g.2
  · rw [Nat.card_zpowers, hord, hP]

end Sylow

theorem num89 (m i : ℕ) (hm : m ∣ 2047 * 88) (hi : i * m = 23 * 89 * 887040) (h89 : 89 ∣ m)
    (hmod : i ≡ 1 [MOD 89]) : False := by
  obtain ⟨e, rfl⟩ := h89
  have he : e ∣ 2024 := by
    have : 89 * e ∣ 89 * 2024 := by simpa using hm
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hmem : e ∈ Nat.divisors 2024 := Nat.mem_divisors.2 ⟨he, by norm_num⟩
  have hmod' : i % 89 = 1 := hmod
  simp only [Nat.divisors_ofNat, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> omega

theorem num23 (m i : ℕ) (hm : m ∣ 2047 * 22) (hi : i * m = 244823040) (h23 : 23 ∣ m)
    (hmod : i ≡ 1 [MOD 23]) : m = 253 := by
  have h506 : m ∣ 506 := by
    have h1 : m ∣ Nat.gcd (2047 * 22) 244823040 := Nat.dvd_gcd hm (Dvd.intro_left _ hi)
    have h2 : Nat.gcd (2047 * 22) 244823040 = 506 := by norm_num
    rwa [h2] at h1
  have hmem : m ∈ Nat.divisors 506 := Nat.mem_divisors.2 ⟨h506, by norm_num⟩
  have hmod' : i % 23 = 1 := hmod
  simp only [Nat.divisors_ofNat, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44.Syl
