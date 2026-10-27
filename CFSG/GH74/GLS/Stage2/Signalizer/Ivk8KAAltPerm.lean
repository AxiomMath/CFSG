module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87AltCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.KAAlt

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltPerm
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltCore

section Step1

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem odd_orderOf_of_mem_pGroup {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup p ↥P) {x : G} (hx : x ∈ P) : Odd (orderOf x) := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hd : orderOf (⟨x, hx⟩ : ↥P) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hd
  have h1 : orderOf x = p ^ j := by
    rw [← Subgroup.orderOf_coe (⟨x, hx⟩ : ↥P)] at hj
    exact hj
  rw [h1]
  exact (hp.odd_of_ne_two hp2).pow

omit [Fintype α] [DecidableEq α] in
theorem eq_of_pow_two_pow {x : Perm α} (hx : Odd (orderOf x)) {a : α} (i : ℕ)
    (h : (x ^ (2 ^ i)) a = a) : x a = a := by
  have hcop : (2 ^ i).Coprime (orderOf x) := Nat.Coprime.pow_left i (Nat.coprime_two_left.2 hx)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h m

theorem fix_support {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : Perm α} (hy : y * y = 1)
    {P : Subgroup (Perm α)} (hPp : IsPGroup p ↥P) (hcomm : ∀ e ∈ P, e * y = y * e)
    (hD : ∀ v : Perm α, Odd (orderOf v) → v * y = y * v →
      v ∈ normalizer (P : Set (Perm α))) :
    ∀ x ∈ P, ∀ a, y a ≠ a → x a = a := by
  intro x hx a ha
  by_contra hxa
  have hxodd : Odd (orderOf x) := odd_orderOf_of_mem_pGroup hp hp2 hPp hx
  have hyx : ∀ w, x (y w) = y (x w) := fun w => by
    have := congrArg (fun f : Perm α => f w) (hcomm x hx)
    simpa [Perm.mul_apply] using this
  have hxinj : ∀ u v, x u = x v → u = v := fun u v h => x.injective h
  obtain ⟨b, hb⟩ : ∃ b, b = x a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = x b := ⟨_, rfl⟩
  have hyb : y b ≠ b := by
    rw [hb, ← hyx]
    exact fun h => ha (hxinj _ _ h)
  have hyc : y c ≠ c := by
    rw [hc, ← hyx]
    exact fun h => hyb (hxinj _ _ h)
  have hba : b ≠ a := by rw [hb]; exact hxa
  have hx2a : ∀ i, (x ^ (2 ^ i)) a = a → False := fun i h => hxa (eq_of_pow_two_pow hxodd i h)
  have hyy : ∀ w, y (y w) = w := yy hy
  have hbya : b ≠ y a := by
    intro h
    apply hx2a 1
    have h1 : x (x a) = a := by
      rw [← hb, h, hyx, ← hb, h, hyy]
    simpa [pow_two] using h1
  have hca : c ≠ a := by
    intro h
    apply hx2a 1
    have h1 : x (x a) = a := by rw [← hb, ← hc, h]
    simpa [pow_two] using h1
  have hcya : c ≠ y a := by
    intro h
    apply hx2a 2
    have h1 : x (x a) = y a := by rw [← hb, ← hc, h]
    have h2 : x (x (y a)) = a := by
      rw [hyx, hyx, h1, hyy]
    have h3 : x (x (x (x a))) = a := by rw [h1, h2]
    simpa [pow_succ, pow_mul, Perm.mul_apply] using h3
  have hcb : c ≠ b := by
    intro h
    apply hxa
    have h1 : x b = b := by rw [← hc, h]
    have h2 : x b = x a := by rw [h1, hb]
    exact hb ▸ (hxinj _ _ h2) ▸ rfl
  have hcyb : c ≠ y b := by
    intro h
    apply hbya
    have h1 : x b = x (y a) := by rw [← hc, h, hb, hyx]
    exact hxinj _ _ h1
  have hT : Trip y a b c := ⟨ha, hyb, hyc, hba, hbya, hca, hcya, hcb, hcyb⟩
  have hU : U y a b ∈ normalizer (P : Set (Perm α)) := U_mem hy hD hT
  have hUx : U y a b * x * (U y a b)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hU x).1 hx
  have hW : U y a b * x * (U y a b)⁻¹ * x⁻¹ ∈ P := P.mul_mem hUx (P.inv_mem hx)
  have hUinv : (U y a b)⁻¹ = U y a b := inv_eq_of_mul_eq_one_right (U_mul_self hy hT)
  have hxU : x * U y a b * x⁻¹ = swap b (y b) * swap c (y c) := by
    have e1 := Equiv.swap_apply_apply x a (y a)
    have e2 := Equiv.swap_apply_apply x b (y b)
    rw [hyx, ← hb] at e1
    rw [hyx, ← hc] at e2
    calc x * U y a b * x⁻¹ = (x * swap a (y a) * x⁻¹) * (x * swap b (y b) * x⁻¹) := by
          unfold U; group
      _ = swap b (y b) * swap c (y c) := by rw [← e1, ← e2]
  have hWeq : U y a b * x * (U y a b)⁻¹ * x⁻¹ = U y a c := by
    rw [hUinv]
    calc U y a b * x * U y a b * x⁻¹ = U y a b * (x * U y a b * x⁻¹) := by group
      _ = swap a (y a) * swap b (y b) * (swap b (y b) * swap c (y c)) := by rw [hxU]; rfl
      _ = U y a c := by
        unfold U
        rw [mul_assoc, ← mul_assoc (swap b (y b)), Equiv.swap_mul_self, one_mul]
  rw [hWeq] at hW
  have hT' : Trip y a c b := hT.swap23 hy
  have hsq : U y a c * U y a c = 1 := U_mul_self hy hT'
  obtain ⟨k, hk⟩ := hPp ⟨U y a c, hW⟩
  have hk' : (U y a c) ^ (p ^ k) = 1 := congrArg Subtype.val hk
  have h2 : orderOf (U y a c) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have h3 : orderOf (U y a c) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime 2 (p ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h4 : orderOf (U y a c) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h3
  have h5 : U y a c = 1 := orderOf_eq_one_iff.1 h4
  have h6 := U_apply_left hy hT'
  rw [h5, Perm.one_apply] at h6
  exact ha h6.symm

end Step1

section Step2

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem sign_eq_one_of_odd' {β : Type*} [Fintype β] [DecidableEq β] {v : Perm β}
    (hv : Odd (orderOf v)) : Perm.sign v = 1 := by
  have h1 : Perm.sign v ^ orderOf v = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Perm.sign v) with h | h
  · exact h
  · rw [h, hv.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem cyclic_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : Perm α} (hy : y * y = 1)
    {P : Subgroup (Perm α)} (hPp : IsPGroup p ↥P) (hP1 : P ≠ ⊥)
    (hfix : ∀ x ∈ P, ∀ a, y a ≠ a → x a = a)
    (hcomm : ∀ e ∈ P, e * y = y * e)
    (hD : ∀ v : Perm α, Odd (orderOf v) → v * y = y * v →
      v ∈ normalizer (P : Set (Perm α))) : IsCyclic ↥P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hyy : ∀ w, y (y w) = w := yy hy
  let Φ := {a : α // y a = a}
  let ι : Perm Φ →* Perm α := Equiv.Perm.ofSubtype
  have hι : Function.Injective ι := Equiv.Perm.ofSubtype_injective
  have hPι : P ≤ ι.range := by
    intro x hx
    have hyx : ∀ w, x (y w) = y (x w) := fun w => by
      have := congrArg (fun f : Perm α => f w) (hcomm x hx)
      simpa [Perm.mul_apply] using this
    have h1 : ∀ w, y (x w) = x w ↔ y w = w := by
      intro w
      rw [← hyx]
      exact ⟨fun h => x.injective h, fun h => by rw [h]⟩
    refine ⟨x.subtypePerm h1, Equiv.Perm.ofSubtype_subtypePerm h1 fun w hw => ?_⟩
    by_contra hyw
    exact hw (hfix x hx w hyw)
  let P' : Subgroup (Perm Φ) := P.comap ι
  have hmap : P'.map ι = P := Subgroup.map_comap_eq_self hPι
  have hP'p : IsPGroup p ↥P' := hPp.comap_of_injective ι hι
  have hP'1 : P' ≠ ⊥ := by
    intro h
    apply hP1
    rw [← hmap, h, Subgroup.map_bot]
  have hcommι : ∀ v' : Perm Φ, ι v' * y = y * ι v' := by
    intro v'
    ext w
    simp only [Perm.mul_apply]
    by_cases hw : y w = w
    · have h1 : ι v' w = ↑(v' ⟨w, hw⟩) := Equiv.Perm.ofSubtype_apply_of_mem v' hw
      rw [hw, h1]
      exact (v' ⟨w, hw⟩).2.symm
    · have h1 : ι v' w = w := Equiv.Perm.ofSubtype_apply_of_not_mem v' hw
      have h2 : ι v' (y w) = y w := by
        refine Equiv.Perm.ofSubtype_apply_of_not_mem v' ?_
        intro h
        apply hw
        rw [hyy] at h
        exact h.symm
      rw [h1, h2]
  have hDι : ∀ v' : Perm Φ, Odd (orderOf v') → v' ∈ normalizer (P' : Set (Perm Φ)) := by
    intro v' hv'
    have hv := hD (ι v') (by rw [orderOf_injective ι hι]; exact hv') (hcommι v')
    rw [Subgroup.mem_normalizer_iff] at hv ⊢
    intro h
    show ι h ∈ P ↔ ι (v' * h * v'⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hv _
  have hoddP' : ∀ x ∈ P', Odd (orderOf x) := by
    intro x hx
    have := odd_orderOf_of_mem_pGroup hp hp2 hPp (show ι x ∈ P from hx)
    rwa [orderOf_injective ι hι] at this
  by_cases hm : 5 ≤ Nat.card Φ
  · exfalso
    have : Nontrivial Φ := by
      have : 1 < Nat.card Φ := by omega
      exact Finite.one_lt_card_iff_nontrivial.1 this
    have hAnorm : alternatingGroup Φ ≤ normalizer (P' : Set (Perm Φ)) := by
      rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
      intro σ hσ
      exact hDι σ (by rw [hσ.orderOf]; exact (by decide : Odd 3))
    have hP'A : P' ≤ alternatingGroup Φ := fun x hx =>
      Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_odd' (hoddP' x hx))
    let N : Subgroup ↥(alternatingGroup Φ) := P'.subgroupOf (alternatingGroup Φ)
    have hN : N.Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have := (Subgroup.mem_normalizer_iff.1 (hAnorm g.2) (x : Perm Φ)).1 hx
      simpa using this
    have hsimple : IsSimpleGroup ↥(alternatingGroup Φ) := alternatingGroup.isSimpleGroup hm
    rcases hsimple.eq_bot_or_eq_top_of_normal N with h | h
    · apply hP'1
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hP'A hx⟩ : ↥(alternatingGroup Φ)) ∈ N := Subgroup.mem_subgroupOf.2 hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    · have hNp : IsPGroup p ↥N := hP'p.comap_of_injective (alternatingGroup Φ).subtype
        (alternatingGroup Φ).subtype_injective
      obtain ⟨j, hj⟩ := hNp.exists_card_eq
      have hcard : Nat.card ↥(alternatingGroup Φ) = p ^ j := by
        rw [← hj, h]
        exact (Nat.card_congr (Subgroup.topEquiv (G := ↥(alternatingGroup Φ))).toEquiv).symm
      have h2 := two_mul_nat_card_alternatingGroup (α := Φ)
      have h3 : Nat.card (Perm Φ) = (Nat.card Φ).factorial := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.card_eq_fintype_card]
      have h4 : 4 ∣ (Nat.card Φ).factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have h5 : Even (Nat.card ↥(alternatingGroup Φ)) := by
        obtain ⟨t, ht⟩ := h4
        exact ⟨t, by omega⟩
      have h6 : Odd (p ^ j) := (hp.odd_of_ne_two hp2).pow
      rw [← hcard] at h6
      exact (Nat.not_even_iff_odd.2 h6) h5
  · push Not at hm
    obtain ⟨j, hj⟩ := hPp.exists_card_eq
    have hPP' : Nat.card ↥P = Nat.card ↥P' := by
      rw [← hmap]
      exact Subgroup.card_map_of_injective hι
    have h1 : Nat.card ↥P' ∣ Nat.card (Perm Φ) := Subgroup.card_subgroup_dvd_card P'
    have h3 : Nat.card (Perm Φ) = (Nat.card Φ).factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.card_eq_fintype_card]
    have h24 : (Nat.card Φ).factorial ∣ 24 :=
      (Nat.factorial_dvd_factorial (by omega : Nat.card Φ ≤ 4)).trans (by decide)
    have h2 : p ^ j ∣ 8 * 3 := by
      rw [← hj, hPP']
      exact h1.trans (h3 ▸ h24)
    have hcop : Nat.Coprime (p ^ j) 8 := by
      have : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
      simpa using Nat.Coprime.pow j 3 this
    have h3' : p ^ j ∣ 3 := hcop.dvd_of_dvd_mul_left h2
    have hcard3 : Nat.card ↥P ∣ 3 := by rw [hj]; exact h3'
    rcases (Nat.dvd_prime Nat.prime_three).1 hcard3 with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hP1
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card h

end Step2


theorem alt_core2 {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {y : Perm α} (hy : y * y = 1) {P : Subgroup (Perm α)} (hPp : IsPGroup p ↥P) (hP1 : P ≠ ⊥)
    (hcomm : ∀ e ∈ P, e * y = y * e)
    (hD : ∀ v : Perm α, Odd (orderOf v) → v * y = y * v →
      v ∈ normalizer (P : Set (Perm α))) : IsCyclic ↥P :=
  cyclic_core hp hp2 hy hPp hP1 (fix_support hp hp2 hy hPp hcomm hD) hcomm hD

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.KAAlt
