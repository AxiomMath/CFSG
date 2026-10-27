module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.CardCommute
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open MulAction

theorem card_modEq_one_of_orbit_sizes {Γ X : Type*} [Group Γ] [Finite Γ] [MulAction Γ X] [Finite X]
    (x₀ : X) (hfix : ∀ g : Γ, g • x₀ = x₀) (m : ℕ)
    (h : ∀ x : X, x ≠ x₀ → m ∣ Nat.card Γ / Nat.card (stabilizer Γ x)) :
    Nat.card X ≡ 1 [MOD m] := by
  classical
  have := Fintype.ofFinite Γ
  have := Fintype.ofFinite X
  have : Fintype (orbitRel.Quotient Γ X) := Fintype.ofFinite _
  have : ∀ b : X, Fintype (stabilizer Γ b) := fun b => Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, card_eq_sum_card_group_div_card_stabilizer Γ X]
  set ω₀ : orbitRel.Quotient Γ X := Quotient.mk'' x₀ with hω₀
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ω₀)]
  have h1 : Nat.card Γ / Nat.card (stabilizer Γ ω₀.out) = 1 := by
    have hout : (ω₀.out : X) = x₀ := by
      have : orbitRel Γ X ω₀.out x₀ := Quotient.exact (Quotient.out_eq ω₀)
      obtain ⟨g, hg⟩ := this
      rw [← hg]; exact hfix g
    have : stabilizer Γ ω₀.out = ⊤ := by
      rw [hout]; ext g; simp [hfix g]
    rw [this, Nat.card_congr Subgroup.topEquiv.toEquiv]
    exact Nat.div_self Nat.card_pos
  have h2 : m ∣ ∑ ω ∈ Finset.univ.erase ω₀, Fintype.card Γ / Fintype.card (stabilizer Γ ω.out) := by
    refine Finset.dvd_sum fun ω hω => ?_
    have hne : (ω.out : X) ≠ x₀ := by
      intro hout
      apply (Finset.mem_erase.mp hω).1
      rw [← Quotient.out_eq ω, hout]
    have := h _ hne
    simpa [Nat.card_eq_fintype_card] using this
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h1
  rw [h1]
  exact (Nat.modEq_zero_iff_dvd.mpr h2).add_left 1

theorem sylowCount_eq_one (n : ℕ) (hn : n ≡ 1 [MOD 121])
    (hdvd : n * (11 ^ 3 * 24) ∣ 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43)
    (hpr : ∀ r : ℕ, r.Prime → r ∣ n → r = 2 ∨ r = 3 ∨ r = 11) : n = 1 := by
  have h1 : n ∣ 2 ^ 18 * 3 ^ 2 * (5 * 7 * 23 * 29 * 31 * 37 * 43) := by
    have : 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43
        = (11 ^ 3 * 24) * (2 ^ 18 * 3 ^ 2 * (5 * 7 * 23 * 29 * 31 * 37 * 43)) := by norm_num
    rw [this, mul_comm n] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hcop : Nat.Coprime n (5 * 7 * 23 * 29 * 31 * 37 * 43) := by
    refine Nat.coprime_of_dvd fun p hp hpn hpK => ?_
    have := hpr p hp hpn
    have hp' : p ∣ 5 ∨ p ∣ 7 ∨ p ∣ 23 ∨ p ∣ 29 ∨ p ∣ 31 ∨ p ∣ 37 ∨ p ∣ 43 := by
      simp only [Nat.Prime.dvd_mul hp] at hpK
      tauto
    rcases hp' with h | h | h | h | h | h | h <;>
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h
        omega
  have h2 : n ∣ 2 ^ 18 * 3 ^ 2 := hcop.dvd_of_dvd_mul_right h1
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp h2
  obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow (by norm_num)).mp hy
  obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow (by norm_num)).mp hz
  interval_cases a <;> interval_cases b <;> simp_all [Nat.ModEq]

theorem normalizer_subgroupOf_eq_inf {G : Type*} [Group G] (H Q : Subgroup G) (hQH : Q ≤ H) :
    Subgroup.normalizer (Q.subgroupOf H : Set H) =
      (Subgroup.normalizer (Q : Set G) ⊓ H).subgroupOf H := by
  ext g
  simp only [Subgroup.mem_normalizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.coe_mul, Subgroup.coe_inv]
  constructor
  · intro hg
    refine ⟨fun x => ?_, g.2⟩
    constructor
    · intro hx
      have := (hg ⟨x, hQH hx⟩).mp hx
      exact this
    · intro hx
      have hxH : x ∈ H := by
        have := H.mul_mem (H.inv_mem g.2) (H.mul_mem (hQH hx) g.2)
        simpa [mul_assoc] using this
      exact (hg ⟨x, hxH⟩).mpr hx
  · rintro ⟨hg, -⟩ h
    exact hg h

theorem centralizer_le_normalizer_of_count {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (z : G) (hz : orderOf z = 11) (hQ : Nat.card Q = 11 ^ 3)
    (_hzQ : z ∈ Q) (hzc : ∀ q ∈ Q, q * z = z * q)
    (hTI : ∀ Q' : Subgroup G, Nat.card Q' = 11 ^ 3 → Q' ≤ Subgroup.centralizer ({z} : Set G) →
        Q' ≠ Q → ∀ g ∈ Q, g ∈ Q' → g ∈ Subgroup.zpowers z)
    (hN : Nat.card ↥(Subgroup.normalizer (Q : Set G) ⊓ Subgroup.centralizer ({z} : Set G)) = 11 ^ 3 * 24)
    (hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set G)) → r = 2 ∨ r = 3 ∨ r = 11)
    (hG : Nat.card G = 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  have h11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set H := Subgroup.centralizer ({z} : Set G) with hH
  have hQH : Q ≤ H := fun q hq => by
    rw [hH, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (hzc q hq).symm
  set Q₀ : Subgroup H := Q.subgroupOf H with hQ₀
  have hQ₀card : Nat.card Q₀ = 11 ^ 3 := by
    rw [← hQ]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hHdvd : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
  have hHne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card H).factorization 11 = 3 := by
    have h3 : 11 ^ 3 ∣ Nat.card H := hQ₀card ▸ Subgroup.card_subgroup_dvd_card Q₀
    have h4 : ¬ 11 ^ 4 ∣ Nat.card H := by
      intro h
      have := h.trans hHdvd
      rw [hG] at this
      revert this; norm_num
    have a := (Nat.Prime.pow_dvd_iff_le_factorization h11.out hHne).mp h3
    have b : ¬ 4 ≤ (Nat.card H).factorization 11 := fun h =>
      h4 ((Nat.Prime.pow_dvd_iff_le_factorization h11.out hHne).mpr h)
    omega
  let P₀ : Sylow 11 H := Sylow.ofCard Q₀ (by rw [hQ₀card, hfac])
  have hP₀ : (P₀ : Subgroup H) = Q₀ := rfl
  have hmod : Nat.card (Sylow 11 H) ≡ 1 [MOD 121] := by
    refine card_modEq_one_of_orbit_sizes (Γ := Q₀) P₀ ?_ 121 ?_
    · intro g
      rw [Subgroup.smul_def, Sylow.smul_eq_iff_mem_normalizer]
      exact Subgroup.le_normalizer (show (g : H) ∈ Q₀ from g.2)
    · intro P' hne
      have hp : IsPGroup 11 Q₀ := IsPGroup.of_card hQ₀card
      let f : Q₀ →* G := H.subtype.comp Q₀.subtype
      have hf : Function.Injective f := H.subtype_injective.comp Q₀.subtype_injective
      have hSle : (stabilizer Q₀ P').map f ≤ Subgroup.zpowers z := by
        rintro _ ⟨g, hg, rfl⟩
        have hg' : g • P' = P' := hg
        have h1 : (g : H) ∈ Subgroup.normalizer (P' : Set H) :=
          Sylow.smul_eq_iff_mem_normalizer.mp hg'
        have h2 : (g : H) ∈ Q₀ ⊓ (P' : Subgroup H) := by
          rw [← hp.inf_normalizer_sylow]; exact ⟨g.2, h1⟩
        refine hTI (Subgroup.map H.subtype (P' : Subgroup H)) ?_ ?_ ?_ (f g) ?_ ?_
        · rw [Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity, hfac]
        · exact Subgroup.map_subtype_le _
        · intro heq
          apply hne
          apply Sylow.ext
          apply Subgroup.map_injective H.subtype_injective
          rw [heq, hP₀, hQ₀, Subgroup.map_subgroupOf_eq_of_le hQH]
        · exact (Subgroup.mem_subgroupOf.mp g.2)
        · exact ⟨g, h2.2, rfl⟩
      have hdvd : Nat.card (stabilizer Q₀ P') ∣ 11 := by
        have h11' : Nat.card (Subgroup.zpowers z) = 11 := by rw [Nat.card_zpowers, hz]
        have := Subgroup.card_dvd_of_le hSle
        rwa [Subgroup.card_map_of_injective hf, h11'] at this
      rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h <;> rw [h, hQ₀card] <;> norm_num
  have hindex : Nat.card (Sylow 11 H) * Nat.card (Subgroup.normalizer (Q₀ : Set H)) = Nat.card H := by
    rw [Sylow.card_eq_index_normalizer P₀, mul_comm]
    exact Subgroup.card_mul_index _
  have hnorm : Nat.card (Subgroup.normalizer (Q₀ : Set H)) = 11 ^ 3 * 24 := by
    rw [hQ₀, normalizer_subgroupOf_eq_inf H Q hQH]
    rw [← hN]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hone : Nat.card (Sylow 11 H) = 1 := by
    apply sylowCount_eq_one _ hmod
    · have := hindex
      rw [hnorm] at this
      rw [this, ← hG]
      exact hHdvd
    · intro r hr hrn
      exact hprime r hr (hindex ▸ Dvd.dvd.mul_right hrn _)
  have : Subsingleton (Sylow 11 H) := by
    have := (Nat.card_eq_one_iff_unique.mp hone).1
    exact this
  have hnormal := Sylow.normal_of_subsingleton P₀
  intro x hx
  have h1 : (⟨x, hx⟩ : H) ∈ Subgroup.normalizer (Q₀ : Set H) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (show Q₀.Normal from hnormal)]; trivial
  rw [hQ₀, normalizer_subgroupOf_eq_inf H Q hQH] at h1
  exact (Subgroup.mem_inf.mp h1).1

section Sylow
open scoped Pointwise

theorem exists_conj_of_card_pow {G : Type*} [Group G] [Finite G] (Q Q' : Subgroup G)
    (hQ : Nat.card Q = 11 ^ 3) (hQ' : Nat.card Q' = 11 ^ 3) (hG : ¬ 11 ^ 4 ∣ Nat.card G) :
    ∃ g : G, ∀ x, x ∈ Q' ↔ g⁻¹ * x * g ∈ Q := by
  have h11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card G).factorization 11 = 3 := by
    have h3 : 11 ^ 3 ∣ Nat.card G := hQ ▸ Subgroup.card_subgroup_dvd_card Q
    have a := (Nat.Prime.pow_dvd_iff_le_factorization h11.out hGne).mp h3
    have b : ¬ 4 ≤ (Nat.card G).factorization 11 := fun h =>
      hG ((Nat.Prime.pow_dvd_iff_le_factorization h11.out hGne).mpr h)
    omega
  let P : Sylow 11 G := Sylow.ofCard Q (by rw [hQ, hfac])
  let P' : Sylow 11 G := Sylow.ofCard Q' (by rw [hQ', hfac])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
  refine ⟨g, fun x => ?_⟩
  have : (P' : Subgroup G) = (g • P : Sylow 11 G) := by rw [hg]
  show x ∈ (P' : Subgroup G) ↔ _
  rw [this, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem exists_conj_mem_of_orderOf {G : Type*} [Group G] [Finite G] (Q : Subgroup G)
    (hQ : Nat.card Q = 11 ^ 3) (hG : ¬ 11 ^ 4 ∣ Nat.card G) {g : G} (hg : orderOf g = 11) :
    ∃ h : G, h⁻¹ * g * h ∈ Q := by
  have h11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card G).factorization 11 = 3 := by
    have h3 : 11 ^ 3 ∣ Nat.card G := hQ ▸ Subgroup.card_subgroup_dvd_card Q
    have a := (Nat.Prime.pow_dvd_iff_le_factorization h11.out hGne).mp h3
    have b : ¬ 4 ≤ (Nat.card G).factorization 11 := fun h =>
      hG ((Nat.Prime.pow_dvd_iff_le_factorization h11.out hGne).mpr h)
    omega
  let P₀ : Sylow 11 G := Sylow.ofCard Q (by rw [hQ, hfac])
  have hp : IsPGroup 11 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg]; norm_num)
  obtain ⟨P', hP'⟩ := hp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P₀ P'
  refine ⟨h, ?_⟩
  have hgP' : g ∈ (P' : Subgroup G) := hP' (Subgroup.mem_zpowers g)
  have : (P' : Subgroup G) = (h • P₀ : Sylow 11 G) := by rw [hh]
  rw [this, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hgP'
  exact hgP'

end Sylow

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
