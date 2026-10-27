module

public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.GH74.Uniqueness.SU.SU7Gen
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.GH74.Uniqueness.SU.SU7.Gen

open Subgroup

theorem card_map_mul_card_inf_ker {X H : Type*} [Group X] [Group H] (f : X →* H)
    (R : Subgroup X) : Nat.card (R.map f) * Nat.card ↥(R ⊓ f.ker) = Nat.card R := by
  let g : ↥R →* H := f.comp R.subtype
  have hr : g.range = R.map f := by
    ext y
    simp only [g, MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply,
      Subgroup.coe_subtype, Subtype.exists]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩
  have hk : g.ker = (R ⊓ f.ker).subgroupOf R := by
    ext ⟨r, hr⟩
    simp only [g, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨hr, h⟩, fun h => h.2⟩
  have h1 := Subgroup.card_mul_index g.ker
  have h2 : Nat.card g.ker = Nat.card ↥(R ⊓ f.ker) := by
    rw [hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2, Subgroup.index_ker, hr] at h1
  rw [mul_comm]
  exact h1

theorem normal_le_of_central_sylow {H : Type*} [Group H] [Finite H] {D A : Subgroup H}
    (hDn : ∀ h : H, ∀ d ∈ D, h * d * h⁻¹ ∈ D) (hAD : A ≤ D)
    (hAc : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a) (hAp : IsPGroup 2 A) (hAidx : ¬ 2 ∣ A.relIndex D)
    (hO : ∀ N : Subgroup H, N.Normal → Odd (Nat.card N) → N = ⊥) : D ≤ A := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup D := A.subgroupOf D with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    have hn' : (n : H) ∈ A := hn
    have : g * n * g⁻¹ = n := by
      apply Subtype.ext
      have := hAc (n : H) hn' (g : H) g.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (g : H) * (n : H) * (g : H)⁻¹ = (n : H) * (g : H) * (g : H)⁻¹ := by rw [← this]
        _ = (n : H) := by group
    rw [this]; exact hn⟩
  have hNcard : Nat.card N = Nat.card A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv
  have hNidx : N.index = A.relIndex D := rfl
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hNcard, hk, hNidx]
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hAidx
  obtain ⟨K', hK'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set K : Subgroup H := K'.map D.subtype with hK
  have hKD : K ≤ D := by rintro _ ⟨d, -, rfl⟩; exact d.2
  have hKodd : Odd (Nat.card K) := by
    have h1 := hK'.card_mul_card
    have h3 := Subgroup.card_mul_index N
    have hpos : 0 < Nat.card N := Nat.card_pos
    have : Nat.card K' = N.index := Nat.eq_of_mul_eq_mul_left hpos (h1.trans h3.symm)
    rw [hK, Subgroup.card_map_of_injective D.subtype_injective, this, hNidx]
    exact Nat.odd_iff.2 (by have := hAidx; omega)
  have hAK : A ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyA, hyK⟩
    obtain ⟨d, hd, rfl⟩ := hyK
    have h1 : (d : D) ∈ N := hyA
    have h2 : (d : D) ∈ K' := hd
    have := hK'.disjoint
    rw [Subgroup.disjoint_def] at this
    have h3 := this h1 h2
    rw [Subgroup.mem_bot]
    simpa using congrArg Subtype.val h3
  have hdecomp : ∀ d ∈ D, ∃ a ∈ A, ∃ k₀ ∈ K, d = a * k₀ := by
    intro d hd
    obtain ⟨⟨a', k''⟩, hak⟩ := hK'.2 ⟨d, hd⟩
    have hd' : ((a' : D) : H) * ((k'' : D) : H) = d := congrArg Subtype.val hak
    exact ⟨(a' : H), a'.2, ((k'' : D) : H), ⟨(k'' : D), k''.2, rfl⟩, hd'.symm⟩
  have hKchar : ∀ d ∈ D, Odd (orderOf d) → d ∈ K := by
    intro d hd hodd
    obtain ⟨a, haA, k₀, hk₀, rfl⟩ := hdecomp d hd
    have hk₀D : k₀ ∈ D := hKD hk₀
    have hcomm : Commute a k₀ := hAc a haA k₀ hk₀D
    set t := orderOf (a * k₀) with ht
    have h1 : (a * k₀) ^ t = 1 := pow_orderOf_eq_one _
    rw [hcomm.mul_pow] at h1
    have h2 : a ^ t = (k₀ ^ t)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : a ^ t ∈ A ⊓ K :=
      ⟨A.pow_mem haA t, by rw [h2]; exact K.inv_mem (K.pow_mem hk₀ t)⟩
    rw [hAK, Subgroup.mem_bot] at h3
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hAp ⟨a, haA⟩
    have hj' : orderOf a = 2 ^ j := by simpa using hj
    have hdvd : orderOf a ∣ t := orderOf_dvd_of_pow_eq_one h3
    have hodd' : Odd (orderOf a) := Odd.of_dvd_nat hodd hdvd
    have hj0 : j = 0 := by
      by_contra hne
      rw [hj'] at hodd'
      exact (Nat.not_even_iff_odd.2 hodd') (Nat.even_pow.2 ⟨even_two, hne⟩)
    rw [hj0, pow_zero] at hj'
    have : a = 1 := orderOf_eq_one_iff.1 hj'
    rw [this, one_mul]
    exact hk₀
  have hKn : K.Normal := ⟨fun k hk h => by
    apply hKchar
    · exact hDn h k (hKD hk)
    · rw [show h * k * h⁻¹ = (MulAut.conj h) k from rfl, MulEquiv.orderOf_eq]
      have := Subgroup.orderOf_dvd_natCard K hk
      exact Odd.of_dvd_nat hKodd this⟩
  have hK1 := hO K hKn hKodd
  have hKcard1 : Nat.card K = 1 := by rw [hK1]; simp
  have hDcard : Nat.card D = Nat.card A := by
    have h1 := hK'.card_mul_card
    rw [hNcard] at h1
    have hK'1 : Nat.card K' = 1 := by
      have := Subgroup.card_map_of_injective D.subtype_injective (K := K')
      rw [← hK, hKcard1] at this
      exact this.symm
    rw [hK'1, mul_one] at h1
    exact h1.symm
  exact (Subgroup.eq_of_le_of_card_ge hAD (by rw [hDcard])).symm ▸ le_rfl

theorem a5_three_elt : ∀ a b : Equiv.Perm (Fin 5), Equiv.Perm.sign a = 1 → Equiv.Perm.sign b = 1 →
    a ≠ 1 → b ≠ 1 → a ≠ b → a * a = 1 → b * b = 1 → a * b = b * a →
    ∃ c : Equiv.Perm (Fin 5), Equiv.Perm.sign c = 1 ∧ c ≠ 1 ∧ c * c * c = 1 ∧ c * a * c⁻¹ = b ∧
      c * b * c⁻¹ = a * b := by
  decide +kernel

theorem exists_two_ne_one_of_card_four {Y : Type*} [Group Y] {P : Subgroup Y}
    (hP4 : Nat.card P = 4) : ∃ t₁ ∈ P, t₁ ≠ 1 ∧ ∃ t₂ ∈ P, t₂ ≠ 1 ∧ t₂ ≠ t₁ := by
  classical
  have hP1 : ∃ t₁ ∈ P, t₁ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 hcon
    rw [this, Subgroup.card_bot] at hP4; omega
  obtain ⟨t₁, ht₁, ht₁1⟩ := hP1
  refine ⟨t₁, ht₁, ht₁1, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsub : (P : Set Y) ⊆ ({1, t₁} : Finset Y) := by
    intro g hg
    by_cases h1 : g = 1
    · simp [h1]
    · have := hcon g hg h1
      simp [this]
  have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at this
  have h3 : ({1, t₁} : Finset Y).card ≤ 2 := Finset.card_le_two
  have : Nat.card P ≤ 2 := by
    calc Nat.card P = Nat.card (P : Set Y) := rfl
      _ ≤ _ := this
      _ ≤ 2 := h3
  omega

theorem eq_bot_of_normal_isPGroup_alt5 {N : Subgroup (alternatingGroup (Fin 5))} (hN : N.Normal)
    (hp : IsPGroup 2 N) : N = ⊥ := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have := hs
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]; decide
    have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 5)) 3
      (by rw [hcard]; norm_num)
    have hcN : c ∈ N := by rw [h]; exact Subgroup.mem_top c
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hp ⟨c, hcN⟩
    have hk' : orderOf c = 2 ^ k := by simpa using hk
    rw [hc] at hk'
    have : 3 ∣ 2 ^ k := by rw [← hk']
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    omega

end CFSG.GH74.Uniqueness.SU.SU7.Gen
