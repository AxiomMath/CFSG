module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaOmega

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Quasithin CFSG.Sporadic.Schreier
open SolomonWong (mul_comm_of_sq_eq_one)

section G

variable {G : Type} [Group G]

theorem conj_mem_closure_of_invariant {S : Set G} {c : G} (hS : ∀ s ∈ S, c * s * c⁻¹ ∈ S)
    {b : G} (hb : b ∈ closure S) : c * b * c⁻¹ ∈ closure S := by
  have hle : (closure S).map (MulAut.conj c).toMonoidHom ≤ closure S := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact subset_closure (hS s hs)
  exact hle ⟨b, hb, by simp⟩

end G

namespace Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

theorem closure_delta₁ (h : Setting G L D t) :
    closure (conjClass (toddK D) (D.a₁ : G)) = toddA D := by
  refine h.eq_toddA_of_invariant ((closure_le _).2 (conjClass_toddK_subset D D.a_mem.1))
    (fun k hk b hb => conj_mem_closure_of_invariant (fun s hs => conj_mem_conjClass hk hs) hb)
    fun hbot => (a_ne_one D).1 ?_
  have : (D.a₁ : G) ∈ closure (conjClass (toddK D) (D.a₁ : G)) :=
    subset_closure (self_mem_conjClass _ _)
  rwa [hbot, mem_bot] at this

theorem subset_toddA_of_invariant (h : Setting G L D t) {S : Set G} (hSE : S ⊆ toddE D t)
    (hS : ∀ c ∈ toddK D, ∀ y ∈ S, c * y * c⁻¹ ∈ S) (h0 : t ∉ S) (h1 : (D.a₁ : G) * t ∉ S)
    (h2 : (D.a₂ : G) * t ∉ S) (h3 : (D.a₃ : G) * t ∉ S) : S ⊆ toddA D := by
  intro y hy
  obtain ⟨b, hb, hyb | hyb⟩ := h.eq_or_eq_mul_of_mem_toddE (hSE hy)
  · rw [hyb]
    exact hb
  · exfalso
    by_cases hb1 : b = 1
    · rw [hyb, hb1, one_mul] at hy
      exact h0 hy
    have key : ∀ a : G, b ∈ conjClass (toddK D) a → a * t ∈ S := by
      rintro a ⟨c, hc, rfl⟩
      have := hS c⁻¹ (inv_mem hc) y hy
      have hct : c⁻¹ * t * c = t := by rw [mul_assoc, ← h.comm_toddK hc, inv_mul_cancel_left]
      have e : c⁻¹ * y * c⁻¹⁻¹ = a * t := by
        rw [hyb]
        calc c⁻¹ * (c * a * c⁻¹ * t) * c⁻¹⁻¹ = a * (c⁻¹ * t * c) := by group
          _ = a * t := by rw [hct]
      rwa [e] at this
    rcases mem_delta_of_mem D hb hb1 with h' | h' | h'
    · exact h1 (key _ h')
    · exact h2 (key _ h')
    · exact h3 (key _ h')

omit [Finite G] in
theorem not_mem_toddA_of_invariant {S : Set G}
    (hS : ∀ c ∈ toddK D, ∀ y ∈ S, c * y * c⁻¹ ∈ S) (h0 : (1 : G) ∉ S) (h1 : (D.a₁ : G) ∉ S)
    (h2 : (D.a₂ : G) ∉ S) (h3 : (D.a₃ : G) ∉ S) {y : G} (hy : y ∈ S) : y ∉ toddA D := by
  intro hyA
  by_cases hy1 : y = 1
  · exact h0 (hy1 ▸ hy)
  have key : ∀ a : G, y ∈ conjClass (toddK D) a → a ∈ S := by
    rintro a ⟨c, hc, rfl⟩
    have := hS c⁻¹ (inv_mem hc) _ hy
    rwa [show c⁻¹ * (c * a * c⁻¹) * c⁻¹⁻¹ = a by group] at this
  rcases mem_delta_of_mem D hyA hy1 with h' | h' | h'
  · exact h1 (key _ h')
  · exact h2 (key _ h')
  · exact h3 (key _ h')

theorem normalizer_le_of_orbit_subset (h : Setting G L D t)
    (hO : conjOrbit (normalizer (toddE D t : Set G)) (D.a₁ : G) ⊆ toddA D) :
    normalizer (toddE D t : Set G) ≤ normalizer (toddA D : Set G) := by
  have hcl : closure (conjOrbit (normalizer (toddE D t : Set G)) (D.a₁ : G)) = toddA D := by
    refine le_antisymm ((closure_le _).2 hO) ?_
    rw [← h.closure_delta₁]
    apply Subgroup.closure_mono
    rintro _ ⟨c, hc, rfl⟩
    exact conj_mem_conjOrbit' (h.toddK_le_X hc) (self_mem_conjOrbit _ _)
  intro x hx
  refine mem_normalizer_of_conj (fun a ha => ?_) (fun a ha => ?_)
  · rw [← hcl] at ha ⊢
    exact conj_mem_closure_of_invariant (fun s hs => conj_mem_conjOrbit' hx hs) ha
  · rw [← hcl] at ha ⊢
    have := conj_mem_closure_of_invariant (c := x⁻¹) (fun s hs => by
      rw [inv_inv]
      exact conj_mem_conjOrbit hx hs) ha
    rwa [inv_inv] at this

theorem not_mem_omega_of_normalizer (h : Setting G L D t)
    (hXA : normalizer (toddE D t : Set G) ≤ normalizer (toddA D : Set G)) {a : G}
    (ha : a ∈ toddA D) : a ∉ omegaSet D t := by
  rintro ⟨n, hn, rfl⟩
  apply h.t_not_mem
  have := (mem_normalizer_iff.1 (hXA hn) _).1 ha
  rw [show n * (n⁻¹ * t * n) * n⁻¹ = t by group] at this
  exact toddA_le D this

theorem ncard_conjOrbit_dvd {X : Subgroup G} {e : G} (he : e ∈ X) :
    (conjOrbit X e).ncard ∣ Nat.card X :=
  Dvd.intro _ (ncard_conjOrbit_mul he)

theorem false_of_prime_dvd_omega (h : Setting G L D t) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpΩ : p ∣ (omegaSet D t).ncard) (hnot : ∀ j, 1 ≤ j → j ≤ 10 → ¬ p ∣ 2 ^ j - 1) : False := by
  obtain ⟨j, hj1, hj2, hj⟩ :=
    h.exists_dvd_two_pow_sub_one hp hp2 (hpΩ.trans (Dvd.intro _ h.ncard_omega_mul))
  exact hnot j hj1 hj2 hj

theorem not_mem_orbit_a₁ (h : Setting G L D t) {y : G} (hy : y ∈ omegaSet D t) :
    y ∉ conjOrbit (normalizer (toddE D t : Set G)) (D.a₁ : G) := fun hy' => by
  apply h.a₁_not_mem_omega
  rw [omegaSet_eq, ← conjOrbit_eq_of_mem hy, conjOrbit_eq_of_mem hy']
  exact self_mem_conjOrbit _ _

theorem false_of_case_i (h : Setting G L D t) (hΩA : ∀ y ∈ omegaSet D t, y ∉ toddA D)
    (hc1 : (D.a₁ : G) * t ∈ omegaSet D t) (h22 : (omegaSet D t).ncard = 22) : False := by
  have hΩt : ∀ y ∈ omegaSet D t, ∃ b ∈ toddA D, y = b * t := fun y hy => by
    obtain ⟨b, hb, hyb | hyb⟩ := h.eq_or_eq_mul_of_mem_toddE (omegaSet_subset hy)
    · exact absurd (hyb ▸ hb) (hΩA y hy)
    · exact ⟨b, hb, hyb⟩
  have hO : conjOrbit (normalizer (toddE D t : Set G)) (D.a₁ : G) ⊆ toddA D := by
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨b₁, hb₁, e₁⟩ := hΩt _ (conj_mem_conjOrbit hn hc1)
    obtain ⟨b₂, hb₂, e₂⟩ := hΩt _ (conj_mem_conjOrbit hn t_mem_omega)
    have e : n⁻¹ * (D.a₁ : G) * n = (n⁻¹ * ((D.a₁ : G) * t) * n) * (n⁻¹ * t * n)⁻¹ := by group
    rw [e, e₁, e₂, mul_inv_rev, ← mul_assoc, mul_assoc b₁, mul_inv_cancel, mul_one]
    exact mul_mem hb₁ (inv_mem hb₂)
  have hXA := h.normalizer_le_of_orbit_subset hO
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h11 : 11 ∣ Nat.card (normalizer (toddE D t : Set G)) :=
    (show 11 ∣ (omegaSet D t).ncard by rw [h22]; norm_num).trans (Dvd.intro _ h.ncard_omega_mul)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 11 h11
  exact h.false_of_mem_normalizer_toddA (p := 11) x.2 (hXA x.2) (by norm_num) (by norm_num)
    (by rw [Subgroup.orderOf_coe, hx]) (by intro j hj1 hj2; interval_cases j <;> norm_num)

theorem false_of_case_ii_v (h : Setting G L D t) (hb3 : (D.a₃ : G) ∈ omegaSet D t)
    (hc1 : (D.a₁ : G) * t ∈ omegaSet D t) (hc2 : (D.a₂ : G) * t ∈ omegaSet D t)
    (hc3 : (D.a₃ : G) * t ∈ omegaSet D t ∨ (omegaSet D t).ncard = 2 ^ 9) : False := by
  classical
  have hA₁ : (D.a₁ : G) ∈ toddA D := ⟨_, D.a_mem.1, rfl⟩
  have ha₁X : (D.a₁ : G) ∈ normalizer (toddE D t : Set G) :=
    le_normalizer (toddA_le_toddE D t hA₁)
  have hOE : conjOrbit (normalizer (toddE D t : Set G)) (D.a₁ : G) ⊆ toddE D t := by
    rintro _ ⟨n, hn, rfl⟩
    have := (mem_normalizer_iff.1 (inv_mem hn) _).1 (toddA_le_toddE D t hA₁)
    rwa [inv_inv] at this
  have hOK : ∀ c ∈ toddK D, ∀ y ∈ conjOrbit (normalizer (toddE D t : Set G)) (D.a₁ : G),
      c * y * c⁻¹ ∈ conjOrbit (normalizer (toddE D t : Set G)) (D.a₁ : G) :=
    fun c hc y hy => conj_mem_conjOrbit' (h.toddK_le_X hc) hy
  have h3 : (D.a₃ : G) * t ∉ conjOrbit (normalizer (toddE D t : Set G)) (D.a₁ : G) := by
    rcases hc3 with hc3 | h512
    · exact h.not_mem_orbit_a₁ hc3
    · intro h3
      have hcard := h.ncard_eq_of_invariant hOE hOK
      have h1O : (1 : G) ∉ conjOrbit (normalizer (toddE D t : Set G)) (D.a₁ : G) := by
        rintro ⟨n, -, hn⟩
        apply (a_ne_one D).1
        calc (D.a₁ : G) = n * (n⁻¹ * D.a₁ * n) * n⁻¹ := by group
          _ = 1 := by rw [hn]; group
      simp only [h1O, self_mem_conjOrbit, h.not_mem_orbit_a₁ hb3, h.not_mem_orbit_a₁ t_mem_omega,
        h.not_mem_orbit_a₁ hc1, h.not_mem_orbit_a₁ hc2, h3, ite_true, ite_false] at hcard
      have hdvd : (conjOrbit (normalizer (toddE D t : Set G)) (D.a₁ : G)).ncard ∣
          2 ^ 9 * (2 ^ 10 * 20160 * 6) := by
        refine (ncard_conjOrbit_dvd ha₁X).trans ?_
        rw [← h.ncard_omega_mul, h512]
        exact Nat.mul_dvd_mul_left _ h.card_NHA.2
      rw [hcard] at hdvd
      split_ifs at hdvd <;> norm_num at hdvd
  have hOA := h.subset_toddA_of_invariant hOE hOK (h.not_mem_orbit_a₁ t_mem_omega)
    (h.not_mem_orbit_a₁ hc1) (h.not_mem_orbit_a₁ hc2) h3
  exact h.not_mem_omega_of_normalizer (h.normalizer_le_of_orbit_subset hOA)
    ⟨_, D.a_mem.2.2, rfl⟩ hb3

@[expose] def CaseFour (D : ToddParabolic L) (t : G) : Prop :=
  ∀ e ∈ toddE D t, e ∈ omegaSet D t ↔
    (e = t ∨ e ∈ conjClass (toddK D) (D.a₃ : G) ∨ e ∈ conjClass (toddK D) ((D.a₃ : G) * t))

theorem caseFour_of (h : Setting G L D t) (hb1 : (D.a₁ : G) ∉ omegaSet D t)
    (hb2 : (D.a₂ : G) ∉ omegaSet D t) (hb3 : (D.a₃ : G) ∈ omegaSet D t)
    (hc1 : (D.a₁ : G) * t ∉ omegaSet D t) (hc2 : (D.a₂ : G) * t ∉ omegaSet D t)
    (hc3 : (D.a₃ : G) * t ∈ omegaSet D t) : CaseFour D t := by
  have hinv := h.omega_invariant
  have key : ∀ a : G, a ∈ omegaSet D t → conjClass (toddK D) a ⊆ omegaSet D t := by
    rintro a ha _ ⟨c, hc, rfl⟩
    exact hinv c hc a ha
  have back : ∀ a y : G, y ∈ conjClass (toddK D) a → y ∈ omegaSet D t → a ∈ omegaSet D t := by
    rintro a _ ⟨c, hc, rfl⟩ hy
    have := hinv c⁻¹ (inv_mem hc) _ hy
    rwa [show c⁻¹ * (c * a * c⁻¹) * c⁻¹⁻¹ = a by group] at this
  intro e he
  constructor
  · intro heΩ
    obtain ⟨b, hb, heb | heb⟩ := h.eq_or_eq_mul_of_mem_toddE he
    · rw [heb] at heΩ ⊢
      have hb1' : b ≠ 1 := fun h1 => h.one_not_mem_omega (h1 ▸ heΩ)
      rcases mem_delta_of_mem D hb hb1' with h' | h' | h'
      · exact absurd (back _ _ h' heΩ) hb1
      · exact absurd (back _ _ h' heΩ) hb2
      · exact Or.inr (Or.inl h')
    · rw [heb] at heΩ ⊢
      by_cases hb1' : b = 1
      · left
        rw [hb1', one_mul]
      have hmt : ∀ a : G, b ∈ conjClass (toddK D) a → b * t ∈ conjClass (toddK D) (a * t) :=
        fun a hba => by rw [h.conjClass_mul_t]; exact ⟨b, hba, rfl⟩
      rcases mem_delta_of_mem D hb hb1' with h' | h' | h'
      · exact absurd (back _ _ (hmt _ h') heΩ) hc1
      · exact absurd (back _ _ (hmt _ h') heΩ) hc2
      · exact Or.inr (Or.inr (hmt _ h'))
  · rintro (rfl | h' | h')
    · exact t_mem_omega
    · exact key _ hb3 h'
    · exact key _ hc3 h'

open Classical in
theorem omegaSet_eq_of_not_caseFour (h : Setting G L D t) (hiv : ¬ CaseFour D t) :
    omegaSet D t = {e | ∃ a ∈ toddA D, e = a * t} := by
  have hcard := h.ncard_eq_of_invariant omegaSet_subset h.omega_invariant
  simp only [h.one_not_mem_omega, h.a₁_not_mem_omega, h.a₂_not_mem_omega, t_mem_omega,
    ite_true, ite_false, zero_add] at hcard
  have hne := h.exists_mem_omega_ne
  have hP : ∀ p, p.Prime → p ≠ 2 → p ∣ (omegaSet D t).ncard →
      (∀ j, 1 ≤ j → j ≤ 10 → ¬ p ∣ 2 ^ j - 1) → False :=
    fun p hp hp2 hpΩ hnot => h.false_of_prime_dvd_omega hp hp2 hpΩ hnot
  have hA : ∀ (b3 : (D.a₃ : G) ∉ omegaSet D t) (y : G), y ∈ omegaSet D t → y ∉ toddA D :=
    fun b3 _ hy => not_mem_toddA_of_invariant h.omega_invariant h.one_not_mem_omega
      h.a₁_not_mem_omega h.a₂_not_mem_omega b3 hy
  by_cases b3 : (D.a₃ : G) ∈ omegaSet D t <;> by_cases c1 : (D.a₁ : G) * t ∈ omegaSet D t <;>
    by_cases c2 : (D.a₂ : G) * t ∈ omegaSet D t <;>
    by_cases c3 : (D.a₃ : G) * t ∈ omegaSet D t <;>
    simp only [b3, c1, c2, c3, ite_true, ite_false] at hcard <;> norm_num at hcard
  · exact (h.false_of_case_ii_v b3 c1 c2 (Or.inl c3)).elim
  · exact (h.false_of_case_ii_v b3 c1 c2 (Or.inr (by rw [hcard]; norm_num))).elim
  · exfalso
    exact hP 97 (by norm_num) (by norm_num) (by rw [hcard]; norm_num)
      (by intro j hj1 hj2; interval_cases j <;> norm_num)
  · exfalso
    exact hP 151 (by norm_num) (by norm_num) (by rw [hcard]; norm_num)
      (by intro j hj1 hj2; interval_cases j <;> norm_num)
  · exfalso
    exact hP 257 (by norm_num) (by norm_num) (by rw [hcard]; norm_num)
      (by intro j hj1 hj2; interval_cases j <;> norm_num)
  · exfalso
    exact hP 491 (by norm_num) (by norm_num) (by rw [hcard])
      (by intro j hj1 hj2; interval_cases j <;> norm_num)
  · exact (hiv (h.caseFour_of h.a₁_not_mem_omega h.a₂_not_mem_omega b3 c1 c2 c3)).elim
  · exfalso
    exact hP 281 (by norm_num) (by norm_num) (by rw [hcard])
      (by intro j hj1 hj2; interval_cases j <;> norm_num)
  · have hsub : omegaSet D t ⊆ {e | ∃ a ∈ toddA D, e = a * t} := fun y hy => by
      obtain ⟨b, hb, hyb | hyb⟩ := h.eq_or_eq_mul_of_mem_toddE (omegaSet_subset hy)
      · exact absurd (hyb ▸ hb) (hA b3 y hy)
      · exact ⟨b, hb, hyb⟩
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_toddA_mul_t, hcard]; norm_num)
      (Set.toFinite _)
  · exfalso
    exact hP 29 (by norm_num) (by norm_num) (by rw [hcard]; norm_num)
      (by intro j hj1 hj2; interval_cases j <;> norm_num)
  · exfalso
    exact hP 151 (by norm_num) (by norm_num) (by rw [hcard]; norm_num)
      (by intro j hj1 hj2; interval_cases j <;> norm_num)
  · exact (h.false_of_case_i (hA b3) c1 hcard).elim
  · exfalso
    exact hP 491 (by norm_num) (by norm_num) (by rw [hcard])
      (by intro j hj1 hj2; interval_cases j <;> norm_num)
  · exfalso
    exact hP 211 (by norm_num) (by norm_num) (by rw [hcard])
      (by intro j hj1 hj2; interval_cases j <;> norm_num)
  · exfalso
    exact hP 281 (by norm_num) (by norm_num) (by rw [hcard])
      (by intro j hj1 hj2; interval_cases j <;> norm_num)
  · exfalso
    obtain ⟨e, he, het⟩ := hne
    have hc1 : (omegaSet D t).ncard = 1 := by
      first
        | exact hcard
        | exact Set.ncard_eq_one.2 hcard
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hc1
    have h1 : t ∈ ({a} : Set G) := ha ▸ t_mem_omega
    have h2 : e ∈ ({a} : Set G) := ha ▸ he
    exact het ((Set.mem_singleton_iff.1 h2).trans (Set.mem_singleton_iff.1 h1).symm)

end Setting

end CFSG.EvenSmallLie.UnitarySix.Yamada
