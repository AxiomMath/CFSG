module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrders
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart

public section

namespace CFSG.EvenSmallLie.CatalogOrders

open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem catalog_order_cases'
    {T : Type} [Group T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a) (hfin : Nat.card T ≠ 0) :
    (∃ n : ℕ, 5 ≤ n ∧ Nat.card T = n.factorial / 2) ∨
    (∃ (t : StatedLieTag) (n p f : ℕ), t ∈ searchTags ∧ p.Prime ∧ 1 ≤ f ∧ lieMin t ≤ n ∧
      n ≤ lieExp t n + 1 ∧ lieAdm t p f = true ∧ Nat.card T = lieOrd t n (p ^ f) ∧
      (t = .PSL → StatedClassicalModel T .PSL n p f) ∧
      (t = .PSU → StatedClassicalModel T .PSU n p f) ∧ (t = .G2 → 3 ≤ p ^ f)) ∨
    13 ∣ Nat.card T ∨ 19 ∣ Nat.card T ∨ Nat.card T ∈ sporadicOrders ∨ 25 ∣ Nat.card T := by
  have : Finite T := Nat.finite_of_card_ne_zero hfin
  obtain ⟨a, b, hab⟩ := hnonab
  rcases hT with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, h⟩ |
      (⟨t, p, f, ht, h⟩ | ⟨t, p, f, ht, h⟩ | ⟨p, f, h⟩) | hs
  · exfalso
    apply hab
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · left
    refine ⟨n, hn, ?_⟩
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  · right; left
    obtain ⟨hp, hf, hcl⟩ := h.1
    have hc := card_eq_lieOrd_of_classical h
    cases t
    case PSL =>
      exact ⟨.PSL, n, p, f, by decide, hp, hf, hcl.1,
        le_lieExp_add_one hcl.1 (Or.inr (Or.inl rfl)), rfl, hc, fun _ => h, nofun,
        nofun⟩
    case PSU =>
      exact ⟨.PSU, n, p, f, by decide, hp, hf, hcl.1,
        le_lieExp_add_one hcl.1 (Or.inr (Or.inr (Or.inl rfl))), rfl, hc, nofun,
        fun _ => h, nofun⟩
    case PSp =>
      exact ⟨.PSp, n, p, f, by decide, hp, hf, hcl.1,
        le_lieExp_add_one hcl.1 (by simp), rfl, hc, nofun, nofun,
        nofun⟩
    case POmegaOdd =>
      exact ⟨.POmegaOdd, n, p, f, by decide, hp, hf, hcl.1,
        le_lieExp_add_one hcl.1 (by simp), rfl, hc, nofun, nofun,
        nofun⟩
    case POmegaPlus =>
      exact ⟨.POmegaPlus, n, p, f, by decide, hp, hf, hcl,
        le_lieExp_add_one hcl (by simp), rfl, hc, nofun, nofun,
        nofun⟩
    case POmegaMinus =>
      exact ⟨.POmegaMinus, n, p, f, by decide, hp, hf, hcl,
        le_lieExp_add_one hcl (by simp), rfl, hc, nofun, nofun,
        nofun⟩
    all_goals exact h.2.elim
  · right; left
    obtain ⟨hp, hf, -⟩ := h.1
    have hc := card_eq_lieOrd_of_exceptional h
    have hts : t ∈ searchTags := by
      revert ht; cases t <;> decide
    have hPSL : t ≠ .PSL := by rintro rfl; exact absurd ht (by decide)
    have hmin : lieMin t ≤ 0 := by
      revert ht; cases t <;> simp [lieMin, chevalleyExceptionalTags]
    have hadm : lieAdm t p f = true := by
      revert ht; cases t <;> simp [lieAdm, chevalleyExceptionalTags]
    have hPSU : t ≠ .PSU := by rintro rfl; exact absurd ht (by decide)
    have hG2 : t = .G2 → 3 ≤ p ^ f := by
      rintro rfl
      exact h.1.2.2.2
    exact ⟨t, 0, p, f, hts, hp, hf, hmin, by omega, hadm, hc, fun h' => absurd h' hPSL,
      fun h' => absurd h' hPSU, hG2⟩
  · have htt : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
      revert ht; cases t <;> simp [reeTitsTags]
    rcases htt with rfl | rfl | rfl
    · right; left
      obtain ⟨rfl, ⟨a, ha, rfl⟩, hc⟩ := card_eq_lieOrd_of_ree h
      refine ⟨.twistedG2, 0, 3, 2 * a + 1, by decide, Nat.prime_three, by omega, le_rfl,
        by omega, ?_, hc, nofun, nofun, nofun⟩
      simp only [lieAdm, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq]
      omega
    · exact Or.inr (Or.inr (Or.inl (thirteen_dvd_card_of_reeTitsModel_twistedF4 h)))
    · exact Or.inr (Or.inr (Or.inl (thirteen_dvd_card_of_reeTitsModel_Tits h)))
  · right; left
    obtain ⟨rfl, ⟨a, ha, rfl⟩, hc⟩ := card_eq_lieOrd_of_suzuki h
    refine ⟨.twistedB2, 0, 2, 2 * a + 1, by decide, Nat.prime_two, by omega, le_rfl,
      by omega, ?_, hc, nofun, nofun, nofun⟩
    simp only [lieAdm, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    omega
  · rcases card_mem_sporadicOrders_or_M hs with hm | h19 | hM
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h19)))
    · obtain ⟨e⟩ := hM
      have : Nontrivial T := ⟨⟨a * b, b * a, hab⟩⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (twentyfive_dvd_card_of_mulEquiv_M e)))))

theorem card_mulAut_dvd (T : Type) [Group T] [Finite T] :
    Nat.card (MulAut T) ∣ Nat.card T * Nat.card (Outer T) := by
  have h := (ComponentClassification.OuterAutomorphisms.inner T).card_mul_index
  rw [Subgroup.index_eq_card] at h
  rw [← h]
  exact Nat.mul_dvd_mul_right (Subgroup.card_range_dvd _) _

theorem prime_pow_eq_prime_pow {p f r e : ℕ} (hp : p.Prime) (hr : r.Prime) (hf : 1 ≤ f)
    (h : p ^ f = r ^ e) : p = r ∧ f = e := by
  have hpr : p ∣ r ^ e := h ▸ dvd_pow_self p (by omega)
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h
    exact absurd h (Nat.one_lt_pow (by omega) hp.one_lt).ne'
  have hpr' : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow hpr)
  subst hpr'
  exact ⟨rfl, Nat.pow_right_injective hp.two_le h⟩

theorem c7_not_dvd
    {T : Type} [Group T] (hT : Catalog T) (hnonab : ∃ a b : T, a * b ≠ b * a)
    (hdvd : Nat.card T ∣ 2 ^ 16 * 3 ^ 4 * 7) (h7 : 7 ∣ Nat.card T) :
    ¬ 81 ∣ Nat.card T * Nat.card (Outer T) := by
  have hN : (2 ^ 16 * 3 ^ 4 * 7 : ℕ) ≠ 0 := by norm_num
  have hfin : Nat.card T ≠ 0 := fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  have : Finite T := Nat.finite_of_card_ne_zero hfin
  rcases catalog_order_cases' hT hnonab hfin with ⟨n, hn, hc⟩ |
      ⟨t, n, p, f, ht, hp, hf, hmin, hnB, hadm, hc, hPSL, hPSU, hG2⟩ | h13 | h19 | hs | h25
  · exfalso
    rw [hc] at hdvd h7
    have h12 := le_twelve_of_factorial_div_two_dvd (by omega) (by norm_num) hdvd
    revert hdvd h7
    interval_cases n <;> decide
  · have hdvd' := hdvd
    rw [hc] at hdvd' h7
    have hS : lieSearch [2, 3, 7] (2 ^ 16 * 3 ^ 4 * 7) (fun t n q o =>
        !(o % 7 == 0) || (t == .PSL && ((n == 2 && (q == 7 || q == 8)) || (n == 3 && q == 2))) ||
          (t == .PSU && n == 3 && q == 3) || (t == .G2 && q == 2)) = true := by
      decide +kernel
    have hps : ∀ q : ℕ, q.Prime → q ∣ 2 ^ 16 * 3 ^ 4 * 7 → q ∈ [2, 3, 7] := fun q hq hd => by
      simpa using mem_of_prime_dvd [(2, 16), (3, 4), (7, 1)] (by decide) (by decide) hq hd
    have h := lieSearch_sound hN hps hS ht hp hf hmin hnB hadm hdvd'
    have h0 : lieOrd t n (p ^ f) % 7 = 0 := Nat.mod_eq_zero_of_dvd h7
    simp only [h0, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      beq_iff_eq, Bool.or_eq_true] at h
    intro h81
    rw [hc] at h81
    rcases h with (⟨rfl, ⟨rfl, hq | hq⟩ | ⟨rfl, hq⟩⟩ | ⟨⟨rfl, rfl⟩, hq⟩) | ⟨rfl, hq⟩
    · obtain ⟨rfl, rfl⟩ := prime_pow_eq_prime_pow hp (by norm_num : Nat.Prime 7) hf
        (hq.trans (pow_one 7).symm)
      have hout := (LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound T 2 7 1
        (hPSL rfl)).2.2.2.1 rfl
      have := h81.trans (Nat.mul_dvd_mul_left _ hout)
      rw [show lieOrd .PSL 2 (7 ^ 1) = 168 by decide] at this
      norm_num at this
    · obtain ⟨rfl, rfl⟩ := prime_pow_eq_prime_pow hp Nat.prime_two hf
        (hq.trans (by norm_num : (8 : ℕ) = 2 ^ 3))
      have hout := (LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound T 2 2 3
        (hPSL rfl)).2.2.2.1 rfl
      have := h81.trans (Nat.mul_dvd_mul_left _ hout)
      rw [show lieOrd .PSL 2 (2 ^ 3) = 504 by decide] at this
      norm_num at this
    · obtain ⟨rfl, rfl⟩ := prime_pow_eq_prime_pow hp Nat.prime_two hf
        (hq.trans (pow_one 2).symm)
      have hout := (LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound T 3 2 1
        (hPSL rfl)).2.2.2.2 le_rfl
      have := h81.trans (Nat.mul_dvd_mul_left _ hout)
      rw [show lieOrd .PSL 3 (2 ^ 1) = 168 by decide] at this
      norm_num at this
    · obtain ⟨rfl, rfl⟩ := prime_pow_eq_prime_pow hp Nat.prime_three hf
        (hq.trans (pow_one 3).symm)
      have hout := (LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound T 3 3 1
        (hPSU rfl)).2.2.1
      rw [hout, show lieOrd .PSU 3 (3 ^ 1) = 6048 by decide] at h81
      norm_num at h81
    · exact absurd (hq ▸ hG2 rfl) (by norm_num)
  · exact absurd (h13.trans hdvd) (by norm_num)
  · exact absurd (h19.trans hdvd) (by norm_num)
  · have key : ∀ m ∈ sporadicOrders, ¬ m ∣ 2 ^ 16 * 3 ^ 4 * 7 := by decide
    exact absurd hdvd (key _ hs)
  · exact absurd (h25.trans hdvd) (by norm_num)

theorem c7_not_dvd_card_mulAut
    {T : Type} [Group T] (hT : Catalog T) (hnonab : ∃ a b : T, a * b ≠ b * a)
    (hdvd : Nat.card T ∣ 2 ^ 16 * 3 ^ 4 * 7) (h7 : 7 ∣ Nat.card T) :
    ¬ 81 ∣ Nat.card (MulAut T) := by
  have hN : (2 ^ 16 * 3 ^ 4 * 7 : ℕ) ≠ 0 := by norm_num
  have hfin : Nat.card T ≠ 0 := fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  have : Finite T := Nat.finite_of_card_ne_zero hfin
  exact fun h81 => c7_not_dvd hT hnonab hdvd h7 (h81.trans (card_mulAut_dvd T))

end CFSG.EvenSmallLie.CatalogOrders
