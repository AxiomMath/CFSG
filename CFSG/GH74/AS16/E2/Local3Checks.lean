module

public import CFSG.GH74.AS16.E2.Std
public import CFSG.GH74.AS16.E2.Local3ChecksInputs
public import CFSG.GH74.KGroups.Checks

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups

section Generic

theorem exists_elemAb9 {K : Type*} [Group K] [Finite K]
    (hsyl : ∀ S : Sylow 3 K, 9 ∣ Nat.card S ∧ Nat.card S ∣ 27)
    (hexp : ∀ x : K, x ^ 27 = 1 → x ^ 3 = 1) :
    ∃ E : Subgroup K, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 3 = 1) ∧
      Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 K) := inferInstance
  obtain ⟨h9, h27⟩ := hsyl S
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(S : Subgroup K)) 3 (n := 2)
    (by simpa using h9)
  have hE₀' : Nat.card E₀ = 3 ^ 2 := hE₀
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hE₀'
  refine ⟨E₀.map (S : Subgroup K).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg (fun z : E₀ => ((z : (S : Subgroup K)) : K)) this
  · rintro _ ⟨a, ha, rfl⟩
    apply hexp
    have h1 : orderOf a ∣ 27 := (orderOf_dvd_natCard a).trans h27
    have := orderOf_dvd_iff_pow_eq_one.1 h1
    simpa using congrArg (fun z : (S : Subgroup K) => (z : K)) this
  · rw [Subgroup.card_map_of_injective (S : Subgroup K).subtype_injective]
    exact hE₀

theorem factorization_pow_mul_of_not_dvd {p k m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) (hm0 : m ≠ 0) :
    (p ^ k * m).factorization p = k := by
  have h0 : m.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hm
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Nat.factorization_pow,
    hp.factorization]
  simp [h0]

theorem sylow_card_of {K : Type*} [Group K] [Finite K] {p k m : ℕ} [hp : Fact p.Prime]
    (hK : Nat.card K = p ^ k * m) (hm : ¬ p ∣ m) (S : Sylow p K) : Nat.card S = p ^ k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card K := Nat.card_pos
    omega
  rw [Sylow.card_eq_multiplicity, hK, factorization_pow_mul_of_not_dvd hp.out hm hm0]

theorem local3_of_model {K G : Type*} [Group K] [Group G] (P : Subgroup G) (e : K ≃* P)
    (t : G) (htP : t ∈ P) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hone : ∀ u v : K, orderOf u = 2 → orderOf v = 2 → ∃ g : K, g * u * g⁻¹ = v)
    (hex : ∃ c ∈ P, c ^ 3 = 1 ∧ c ≠ 1 ∧ c * t = t * c)
    (hcent : ∀ a ∈ P, (∀ c ∈ P, c ^ 3 = 1 → c * t = t * c → a * c = c * a) → a = 1 ∨ a = t) :
    (∀ v : K, orderOf v = 2 → ∃ c : K, orderOf c = 3 ∧ c * v = v * c) ∧
    (∀ v : K, orderOf v = 2 → ∀ a : K,
      (∀ c : K, orderOf c = 3 → c * v = v * c → a * c = c * a) → a = 1 ∨ a = v) := by
  set u₀ : K := e.symm ⟨t, htP⟩ with hu₀
  have heu₀ : e u₀ = ⟨t, htP⟩ := e.apply_symm_apply _
  have hu₀2 : u₀ ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, heu₀, map_one]
    exact Subtype.ext (by simpa using ht2)
  have hu₀1 : u₀ ≠ 1 := by
    intro h
    apply ht1
    have := congrArg (fun z => ((e z : P) : G)) h
    simpa [heu₀] using this
  have hu₀o : orderOf u₀ = 2 := orderOf_eq_prime hu₀2 hu₀1
  have hE3 : ∃ c₀ : K, orderOf c₀ = 3 ∧ c₀ * u₀ = u₀ * c₀ := by
    obtain ⟨c, hcP, hc3, hc1, hct⟩ := hex
    refine ⟨e.symm ⟨c, hcP⟩, ?_, ?_⟩
    · have h3 : (e.symm ⟨c, hcP⟩) ^ 3 = 1 := by
        apply e.injective
        rw [map_pow, MulEquiv.apply_symm_apply, map_one]
        exact Subtype.ext (by simpa using hc3)
      have h1 : e.symm ⟨c, hcP⟩ ≠ 1 := by
        intro h
        apply hc1
        have := congrArg (fun z => ((e z : P) : G)) h
        simpa using this
      exact orderOf_eq_prime h3 h1
    · apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, heu₀]
      exact Subtype.ext (by simpa using hct)
  have hC3 : ∀ a : K, (∀ c : K, orderOf c = 3 → c * u₀ = u₀ * c → a * c = c * a) →
      a = 1 ∨ a = u₀ := by
    intro a ha
    have hcentA := hcent (e a : P) (e a).2 (by
      intro c hcP hc3 hct
      by_cases hc1 : c = 1
      · rw [hc1]; simp
      · have hcK : orderOf (e.symm ⟨c, hcP⟩) = 3 := by
          have h3 : (e.symm ⟨c, hcP⟩) ^ 3 = 1 := by
            apply e.injective
            rw [map_pow, MulEquiv.apply_symm_apply, map_one]
            exact Subtype.ext (by simpa using hc3)
          have h1 : e.symm ⟨c, hcP⟩ ≠ 1 := by
            intro h
            apply hc1
            have := congrArg (fun z => ((e z : P) : G)) h
            simpa using this
          exact orderOf_eq_prime h3 h1
        have hcomm : e.symm ⟨c, hcP⟩ * u₀ = u₀ * e.symm ⟨c, hcP⟩ := by
          apply e.injective
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply, heu₀]
          exact Subtype.ext (by simpa using hct)
        have := ha _ hcK hcomm
        have h2 := congrArg (fun z => ((e z : P) : G)) this
        simpa using h2)
    rcases hcentA with h | h
    · left
      apply e.injective
      rw [map_one]
      exact Subtype.ext h
    · right
      apply e.injective
      rw [heu₀]
      exact Subtype.ext h
  constructor
  · intro v hv
    obtain ⟨g, hg⟩ := hone u₀ v hu₀o hv
    obtain ⟨c₀, hc₀, hc₀u⟩ := hE3
    refine ⟨g * c₀ * g⁻¹, ?_, ?_⟩
    · calc orderOf (g * c₀ * g⁻¹) = orderOf ((MulAut.conj g) c₀) := by simp
        _ = orderOf c₀ := (MulAut.conj g).orderOf_eq c₀
        _ = 3 := hc₀
    · rw [← hg]
      calc g * c₀ * g⁻¹ * (g * u₀ * g⁻¹) = g * (c₀ * u₀) * g⁻¹ := by group
        _ = g * (u₀ * c₀) * g⁻¹ := by rw [hc₀u]
        _ = g * u₀ * g⁻¹ * (g * c₀ * g⁻¹) := by group
  · intro v hv a ha
    obtain ⟨g, hg⟩ := hone u₀ v hu₀o hv
    have := hC3 (g⁻¹ * a * g) (by
      intro c hc3 hcu
      have hc' : orderOf (g * c * g⁻¹) = 3 := by
        calc orderOf (g * c * g⁻¹) = orderOf ((MulAut.conj g) c) := by simp
          _ = orderOf c := (MulAut.conj g).orderOf_eq c
          _ = 3 := hc3
      have hcomm : g * c * g⁻¹ * v = v * (g * c * g⁻¹) := by
        rw [← hg]
        calc g * c * g⁻¹ * (g * u₀ * g⁻¹) = g * (c * u₀) * g⁻¹ := by group
          _ = g * (u₀ * c) * g⁻¹ := by rw [hcu]
          _ = g * u₀ * g⁻¹ * (g * c * g⁻¹) := by group
      have h1 := ha _ hc' hcomm
      calc g⁻¹ * a * g * c = g⁻¹ * (a * (g * c * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * c * g⁻¹) * a) * g := by rw [h1]
        _ = c * (g⁻¹ * a * g) := by group)
    rcases this with h | h
    · left
      have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      rw [this, h]; group
    · right
      have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      rw [this, h, ← hg]

theorem local3Table_of_model {K G : Type*} [Group K] [Group G] [Finite K] (P : Subgroup G)
    (e : K ≃* P) (t : G) (htP : t ∈ P) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hone : ∀ u v : K, orderOf u = 2 → orderOf v = 2 → ∃ g : K, g * u * g⁻¹ = v)
    (hex : ∃ c ∈ P, c ^ 3 = 1 ∧ c ≠ 1 ∧ c * t = t * c)
    (hcent : ∀ a ∈ P, (∀ c ∈ P, c ^ 3 = 1 → c * t = t * c → a * c = c * a) → a = 1 ∨ a = t)
    (hsyl : ∀ S : Sylow 3 K, 9 ∣ Nat.card S ∧ Nat.card S ∣ 27)
    (hexp : ∀ x ∈ P, x ^ 27 = 1 → x ^ 3 = 1) : Local3Table K := by
  obtain ⟨h1, h2⟩ := local3_of_model P e t htP ht2 ht1 hone hex hcent
  refine ⟨?_, h1, h2⟩
  have hexpK : ∀ x : K, x ^ 27 = 1 → x ^ 3 = 1 := by
    intro x hx
    have hx' : ((e x : P) : G) ^ 27 = 1 := by
      have := congrArg (fun z : P => (z : G)) (show (e x) ^ 27 = 1 by rw [← map_pow, hx, map_one])
      simpa using this
    have h3 := hexp _ (e x).2 hx'
    apply e.injective
    rw [map_pow, map_one]
    exact Subtype.ext (by simpa using h3)
  obtain ⟨E, hEc, hE3, hE9⟩ := exists_elemAb9 hsyl hexpK
  exact ⟨E, ⟨hEc, hE3⟩, hE9⟩

end Generic

section Checks

variable {n : ℕ}

theorem local3Check_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {t : Equiv.Perm (Fin n)} (h : local3Check (elemsT Q) t = true) :
    t ∈ Q.originalSubgroup ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧
      (∃ c ∈ Q.originalSubgroup, c ^ 3 = 1 ∧ c ≠ 1 ∧ c * t = t * c) ∧
      (∀ a ∈ Q.originalSubgroup, (∀ c ∈ Q.originalSubgroup, c ^ 3 = 1 → c * t = t * c →
        a * c = c * a) → a = 1 ∨ a = t) := by
  unfold local3Check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hmem : ∀ c : Equiv.Perm (Fin n), c ∈ c3list (elemsT Q) t ↔
      c ∈ Q.originalSubgroup ∧ c ^ 3 = 1 ∧ c * t = t * c := by
    intro c
    simp only [c3list, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, mem_elemsT Q hQ]
  refine ⟨(mem_elemsT Q hQ t).1 h1, h2, h3, ?_, ?_⟩
  · obtain ⟨c, hc, hc1⟩ := List.any_eq_true.1 h4
    obtain ⟨hcP, hc3, hct⟩ := (hmem c).1 hc
    exact ⟨c, hcP, hc3, by simpa using hc1, hct⟩
  · intro a ha hac
    have := (bif_imp _ _).1 (List.all_eq_true.1 h5 a ((mem_elemsT Q hQ a).2 ha)) (by
      rw [List.all_eq_true]
      intro c hc
      obtain ⟨hcP, hc3, hct⟩ := (hmem c).1 hc
      simpa using hac c hcP hc3 hct)
    simpa using this

theorem expCheck_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) {k m : ℕ}
    (h : expCheck (elemsT Q) k m = true) :
    ∀ x ∈ Q.originalSubgroup, x ^ k = 1 → x ^ m = 1 := by
  intro x hx hxk
  have := (bif_imp _ _).1 (List.all_eq_true.1 h x ((mem_elemsT Q hQ x).2 hx)) (by simpa using hxk)
  simpa using this

end Checks

end CFSG.GH74.AS16.E2
