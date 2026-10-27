module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionEntriesCriteria

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

private def mkP11 (f g : Fin 11 → Fin 11)
    (h : ∀ i, g (f i) = i ∧ f (g i) = i := by decide) : Equiv.Perm (Fin 11) :=
  ⟨f, g, fun i => (h i).1, fun i => (h i).2⟩

private def c7P : Equiv.Perm (Fin 11) :=
  mkP11 ![1, 2, 3, 4, 5, 6, 0, 7, 8, 9, 10] ![6, 0, 1, 2, 3, 4, 5, 7, 8, 9, 10]

private def g7P : Equiv.Perm (Fin 11) :=
  mkP11 ![0, 3, 6, 2, 5, 1, 4, 8, 7, 9, 10] ![0, 5, 3, 1, 6, 4, 2, 8, 7, 9, 10]

private def c11P : Equiv.Perm (Fin 11) :=
  mkP11 ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0] ![10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

private def g11P : Equiv.Perm (Fin 11) :=
  mkP11 ![0, 4, 8, 1, 5, 9, 2, 6, 10, 3, 7] ![0, 3, 6, 9, 1, 4, 7, 10, 2, 5, 8]

private theorem sign_c7P : Equiv.Perm.sign c7P = 1 := by decide

private theorem sign_g7P : Equiv.Perm.sign g7P = 1 := by decide

private theorem sign_c11P : Equiv.Perm.sign c11P = 1 := by decide

private theorem sign_g11P : Equiv.Perm.sign g11P = 1 := by decide

private theorem c7P_pow : c7P ^ 7 = 1 := by decide

private theorem c7P_ne_one : c7P ≠ 1 := by decide

private theorem c11P_ne_one : c11P ≠ 1 := by decide

private theorem c11P_pow : c11P ^ 11 = 1 := by decide

private theorem g7P_conj : g7P * c7P * g7P⁻¹ = c7P ^ 3 := by decide

private theorem g7P_conj_inv : g7P⁻¹ * c7P * g7P = c7P ^ 5 := by decide

private theorem g11P_conj : g11P * c11P * g11P⁻¹ = c11P ^ 4 := by decide

private theorem g11P_conj_inv : g11P⁻¹ * c11P * g11P = c11P ^ 3 := by decide

private def c7 : alternatingGroup (Fin 11) :=
  ⟨c7P, by rw [Equiv.Perm.mem_alternatingGroup]; exact sign_c7P⟩

private def g7 : alternatingGroup (Fin 11) :=
  ⟨g7P, by rw [Equiv.Perm.mem_alternatingGroup]; exact sign_g7P⟩

private def c11 : alternatingGroup (Fin 11) :=
  ⟨c11P, by rw [Equiv.Perm.mem_alternatingGroup]; exact sign_c11P⟩

private def g11 : alternatingGroup (Fin 11) :=
  ⟨g11P, by rw [Equiv.Perm.mem_alternatingGroup]; exact sign_g11P⟩

private theorem c7_pow : c7 ^ 7 = 1 := by
  apply Subtype.ext
  change c7P ^ 7 = 1
  exact c7P_pow

private theorem c11_pow : c11 ^ 11 = 1 := by
  apply Subtype.ext
  change c11P ^ 11 = 1
  exact c11P_pow

private theorem c7_ne_one : c7 ≠ 1 := by
  intro h
  have h' : (c7 : Equiv.Perm (Fin 11)) = 1 := congrArg Subtype.val h
  exact c7P_ne_one h'

private theorem c11_ne_one : c11 ≠ 1 := by
  intro h
  have h' : (c11 : Equiv.Perm (Fin 11)) = 1 := congrArg Subtype.val h
  exact c11P_ne_one h'

private theorem g7_conj : g7 * c7 * g7⁻¹ = c7 ^ (3 : ℤ) := by
  apply Subtype.ext
  change g7P * c7P * g7P⁻¹ = c7P ^ (3 : ℤ)
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
  exact g7P_conj

private theorem g7_conj_inv : g7⁻¹ * c7 * g7 = c7 ^ (5 : ℤ) := by
  apply Subtype.ext
  change g7P⁻¹ * c7P * g7P = c7P ^ (5 : ℤ)
  rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast]
  exact g7P_conj_inv

private theorem g11_conj : g11 * c11 * g11⁻¹ = c11 ^ (4 : ℤ) := by
  apply Subtype.ext
  change g11P * c11P * g11P⁻¹ = c11P ^ (4 : ℤ)
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
  exact g11P_conj

private theorem g11_conj_inv : g11⁻¹ * c11 * g11 = c11 ^ (3 : ℤ) := by
  apply Subtype.ext
  change g11P⁻¹ * c11P * g11P = c11P ^ (3 : ℤ)
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
  exact g11P_conj_inv

private theorem g7_move_three : g7 ^ 3 * c7 * (g7 ^ 3)⁻¹ ≠ c7 := by
  intro h
  have h' : g7P ^ 3 * c7P * (g7P ^ 3)⁻¹ = c7P := congrArg Subtype.val h
  exact (by decide : g7P ^ 3 * c7P * (g7P ^ 3)⁻¹ ≠ c7P) h'

private theorem g7_move_four : g7 ^ 4 * c7 * (g7 ^ 4)⁻¹ ≠ c7 := by
  intro h
  have h' : g7P ^ 4 * c7P * (g7P ^ 4)⁻¹ = c7P := congrArg Subtype.val h
  exact (by decide : g7P ^ 4 * c7P * (g7P ^ 4)⁻¹ ≠ c7P) h'

private theorem g11_move_three : g11 ^ 3 * c11 * (g11 ^ 3)⁻¹ ≠ c11 := by
  intro h
  have h' : g11P ^ 3 * c11P * (g11P ^ 3)⁻¹ = c11P := congrArg Subtype.val h
  exact (by decide : g11P ^ 3 * c11P * (g11P ^ 3)⁻¹ ≠ c11P) h'

private theorem g11_move_four : g11 ^ 4 * c11 * (g11 ^ 4)⁻¹ ≠ c11 := by
  intro h
  have h' : g11P ^ 4 * c11P * (g11P ^ 4)⁻¹ = c11P := congrArg Subtype.val h
  exact (by decide : g11P ^ 4 * c11P * (g11P ^ 4)⁻¹ ≠ c11P) h'

theorem mem_normalizer_zpowers_of_conj {K : Type*} [Group K] {c g : K} {k l : ℤ}
    (h1 : g * c * g⁻¹ = c ^ k) (h2 : g⁻¹ * c * g = c ^ l) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨k * m, ?_⟩
    rw [← conj_zpow, h1, ← zpow_mul]
  · rintro ⟨m, hm⟩
    refine ⟨l * m, ?_⟩
    have h3 : g⁻¹ * c ^ m * g = c ^ (l * m) := by
      calc g⁻¹ * c ^ m * g = (g⁻¹ * c * g) ^ m := by
            simpa only [inv_inv] using (conj_zpow (i := m) (a := g⁻¹) (b := c)).symm
        _ = c ^ (l * m) := by rw [h2, zpow_mul]
    change c ^ (l * m) = x
    change c ^ m = g * x * g⁻¹ at hm
    rw [← h3, hm]
    group

theorem not_smallAutomizer_of_prime_sylow {p : ℕ} [Fact p.Prime] {K : Type} [Group K] [Finite K]
    (hsq : ¬ p ^ 2 ∣ Nat.card K) {c g : K} (hc : orderOf c = p)
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set K))
    (h3 : g ^ 3 * c * (g ^ 3)⁻¹ ≠ c) (h4 : g ^ 4 * c * (g ^ 4)⁻¹ ≠ c) :
    ¬ SmallAutomizer p K := by
  intro hS
  have hcyc : IsPGroup p (Subgroup.zpowers c) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hc, pow_one]
  obtain ⟨T, hle⟩ := IsPGroup.exists_le_sylow hcyc
  have hcT : c ∈ (T : Subgroup K) := hle (Subgroup.mem_zpowers c)
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq T.isPGroup'
  have hpdvd : p ∣ Nat.card T := by
    have h := Subgroup.orderOf_dvd_natCard (T : Subgroup K) hcT
    rwa [hc] at h
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, pow_zero] at hn
      rw [hn] at hpdvd
      have hp1 : p = 1 := Nat.dvd_one.mp hpdvd
      have hp2 := (Fact.out : Nat.Prime p).two_le
      omega
    · exact h
  have hnlt : n < 2 := by
    by_contra h
    have h2 : 2 ≤ n := by omega
    have hdvdK : p ^ n ∣ Nat.card K := hn ▸ Subgroup.card_subgroup_dvd_card (T : Subgroup K)
    exact hsq (dvd_trans (Nat.pow_dvd_pow p h2) hdvdK)
  have hn1 : n = 1 := by omega
  have hTcard : Nat.card T = p := by rw [hn, hn1, pow_one]
  have hpc : Nat.card (Subgroup.zpowers c) = p := by rw [Nat.card_zpowers, hc]
  have hTeq : (T : Subgroup K) = Subgroup.zpowers c := by
    have h := Subgroup.eq_of_le_of_card_ge hle (by rw [hTcard, hpc])
    exact h.symm
  obtain ⟨-, hnorm⟩ := hS T
  have hgT : g ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) := by
    rw [hTeq]
    exact hg
  rcases hnorm g hgT with hcentral | hcentral
  · exact h3 (hcentral c hcT)
  · exact h4 (hcentral c hcT)

theorem not_smallAutomizer_alternatingGroup_eleven_seven :
    ¬ SmallAutomizer 7 (alternatingGroup (Fin 11)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hsq : ¬ 7 ^ 2 ∣ Nat.card (alternatingGroup (Fin 11)) := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hc : orderOf c7 = 7 := orderOf_eq_prime c7_pow c7_ne_one
  exact not_smallAutomizer_of_prime_sylow (p := 7) hsq (c := c7) (g := g7) hc
    (mem_normalizer_zpowers_of_conj g7_conj g7_conj_inv) g7_move_three g7_move_four

theorem not_smallAutomizer_alternatingGroup_eleven_eleven :
    ¬ SmallAutomizer 11 (alternatingGroup (Fin 11)) := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hsq : ¬ 11 ^ 2 ∣ Nat.card (alternatingGroup (Fin 11)) := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hc : orderOf c11 = 11 := orderOf_eq_prime c11_pow c11_ne_one
  exact not_smallAutomizer_of_prime_sylow (p := 11) hsq (c := c11) (g := g11) hc
    (mem_normalizer_zpowers_of_conj g11_conj g11_conj_inv) g11_move_three g11_move_four

theorem not_surjective_of_mulEquiv_alternatingGroup_eleven {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {V : Type} [Group V] [Finite V] (hV : IsPGroup q V)
    (hr : CFSG.Open.pRank q (⊤ : Subgroup V) ≤ 3) (A : Subgroup (MulAut V))
    {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 11)) (φ : ↥A →* K) :
    ¬ Function.Surjective φ := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite K := Finite.of_equiv (alternatingGroup (Fin 11)) e.symm.toEquiv
  intro hφ
  by_cases hq7 : q = 7
  · haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    have hpq : 11 ≠ q := by rw [hq7]; norm_num
    have hS : SmallAutomizer 11 K :=
      smallAutomizer_of_surjective (p := 11) (q := q) (by norm_num) hpq
        (automizerBound_holds (by norm_num) hq hpq) (hasSmallLinearModel hq2 hV hr) A φ hφ
    exact not_smallAutomizer_alternatingGroup_eleven_eleven (SmallAutomizer.of_mulEquiv e hS)
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hpq : 7 ≠ q := Ne.symm hq7
    have hS : SmallAutomizer 7 K :=
      smallAutomizer_of_surjective (p := 7) (q := q) (by norm_num) hpq
        (automizerBound_holds (by norm_num) hq hpq) (hasSmallLinearModel hq2 hV hr) A φ hφ
    exact not_smallAutomizer_alternatingGroup_eleven_seven (SmallAutomizer.of_mulEquiv e hS)

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
