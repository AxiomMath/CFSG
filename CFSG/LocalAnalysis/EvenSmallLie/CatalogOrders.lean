module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersSporadic
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersRee
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersMonster
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLieFast

public section

namespace CFSG.EvenSmallLie.CatalogOrders

open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Blueprint

theorem mem_of_prime_dvd_prod_pow {p : ℕ} (hp : p.Prime) :
    ∀ l : List (ℕ × ℕ), (∀ x ∈ l, x.1.Prime) → p ∣ (l.map fun x => x.1 ^ x.2).prod →
      p ∈ l.map Prod.fst
  | [], _, h => absurd (Nat.dvd_one.mp h) hp.one_lt.ne'
  | (q, e) :: l, hl, h => by
    rw [List.map_cons, List.prod_cons] at h
    rw [List.map_cons, List.mem_cons]
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (hl _ (by simp))).1
        (hp.dvd_of_dvd_pow h1))
    · exact Or.inr (mem_of_prime_dvd_prod_pow hp l (fun x hx => hl x (by simp [hx])) h1)

theorem le_twelve_of_factorial_div_two_dvd {n N : ℕ} (hn : 2 ≤ n) (h13 : ¬ 13 ∣ N)
    (h : n.factorial / 2 ∣ N) : n ≤ 12 := by
  by_contra hlt
  push Not at hlt
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  have h13f : 13 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hlt
  have he : n.factorial = 2 * (n.factorial / 2) := (Nat.mul_div_cancel' h2).symm
  rw [he] at h13f
  have h13' : 13 ∣ n.factorial / 2 :=
    ((Nat.Prime.dvd_mul (by norm_num : Nat.Prime 13)).1 h13f).resolve_left (by norm_num)
  exact h13 (h13'.trans h)

theorem mem_of_prime_dvd {p N : ℕ} (l : List (ℕ × ℕ)) (hl : ∀ x ∈ l, x.1.Prime)
    (hN : (l.map fun x => x.1 ^ x.2).prod = N) (hp : p.Prime) (h : p ∣ N) :
    p ∈ l.map Prod.fst :=
  mem_of_prime_dvd_prod_pow hp l hl (hN ▸ h)

theorem catalog_order_cases
    {T : Type} [Group T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a) (hfin : Nat.card T ≠ 0) :
    (∃ n : ℕ, 5 ≤ n ∧ Nat.card T = n.factorial / 2) ∨
    (∃ (t : StatedLieTag) (n p f : ℕ), t ∈ searchTags ∧ p.Prime ∧ 1 ≤ f ∧ lieMin t ≤ n ∧
      n ≤ lieExp t n + 1 ∧ lieAdm t p f = true ∧ Nat.card T = lieOrd t n (p ^ f) ∧
      (t = .PSL → StatedClassicalModel T .PSL n p f)) ∨
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
        le_lieExp_add_one hcl.1 (Or.inr (Or.inl rfl)), rfl, hc, fun _ => h⟩
    case PSU =>
      exact ⟨.PSU, n, p, f, by decide, hp, hf, hcl.1,
        le_lieExp_add_one hcl.1 (Or.inr (Or.inr (Or.inl rfl))), rfl, hc, fun h' => by cases h'⟩
    case PSp =>
      exact ⟨.PSp, n, p, f, by decide, hp, hf, hcl.1,
        le_lieExp_add_one hcl.1 (by simp), rfl, hc, fun h' => by cases h'⟩
    case POmegaOdd =>
      exact ⟨.POmegaOdd, n, p, f, by decide, hp, hf, hcl.1,
        le_lieExp_add_one hcl.1 (by simp), rfl, hc, fun h' => by cases h'⟩
    case POmegaPlus =>
      exact ⟨.POmegaPlus, n, p, f, by decide, hp, hf, hcl,
        le_lieExp_add_one hcl (by simp), rfl, hc, fun h' => by cases h'⟩
    case POmegaMinus =>
      exact ⟨.POmegaMinus, n, p, f, by decide, hp, hf, hcl,
        le_lieExp_add_one hcl (by simp), rfl, hc, fun h' => by cases h'⟩
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
    exact ⟨t, 0, p, f, hts, hp, hf, hmin, by omega, hadm, hc, fun h' => absurd h' hPSL⟩
  · have htt : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
      revert ht; cases t <;> simp [reeTitsTags]
    rcases htt with rfl | rfl | rfl
    · right; left
      obtain ⟨rfl, ⟨a, ha, rfl⟩, hc⟩ := card_eq_lieOrd_of_ree h
      refine ⟨.twistedG2, 0, 3, 2 * a + 1, by decide, Nat.prime_three, by omega, le_rfl,
        by omega, ?_, hc, fun h' => by cases h'⟩
      simp only [lieAdm, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq]
      omega
    · exact Or.inr (Or.inr (Or.inl (thirteen_dvd_card_of_reeTitsModel_twistedF4 h)))
    · exact Or.inr (Or.inr (Or.inl (thirteen_dvd_card_of_reeTitsModel_Tits h)))
  · right; left
    obtain ⟨rfl, ⟨a, ha, rfl⟩, hc⟩ := card_eq_lieOrd_of_suzuki h
    refine ⟨.twistedB2, 0, 2, 2 * a + 1, by decide, Nat.prime_two, by omega, le_rfl,
      by omega, ?_, hc, fun h' => by cases h'⟩
    simp only [lieAdm, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    omega
  · rcases card_mem_sporadicOrders_or_M hs with hm | h19 | hM
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h19)))
    · obtain ⟨e⟩ := hM
      have : Nontrivial T := ⟨⟨a * b, b * a, hab⟩⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (twentyfive_dvd_card_of_mulEquiv_M e)))))

theorem card_mulAut_le (T : Type) [Group T] [Finite T] :
    Nat.card (MulAut T) ≤
      Nat.card T * Nat.card (ComponentClassification.OuterAutomorphisms.Outer T) := by
  have h := (ComponentClassification.OuterAutomorphisms.inner T).card_mul_index
  rw [Subgroup.index_eq_card] at h
  rw [← h]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd _))

theorem c1_not_two_pow_seven_dvd
    {T : Type} [Group T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a) (hdvd : Nat.card T ∣ 2 ^ 16 * 3 ^ 3 * 5 * 7)
    (h7 : 7 ∣ Nat.card T) : ¬ 2 ^ 7 ∣ Nat.card T := by
  have hN : (2 ^ 16 * 3 ^ 3 * 5 * 7 : ℕ) ≠ 0 := by norm_num
  have hfin : Nat.card T ≠ 0 := fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  rcases catalog_order_cases hT hnonab hfin with ⟨n, hn, hc⟩ |
      ⟨t, n, p, f, ht, hp, hf, hmin, hnB, hadm, hc, -⟩ | h13 | h19 | hs | h25
  · rw [hc] at hdvd h7 ⊢
    have h12 := le_twelve_of_factorial_div_two_dvd (by omega) (by norm_num) hdvd
    revert hdvd h7
    interval_cases n <;> decide
  · rw [hc] at hdvd h7 ⊢
    have hS : lieSearch [2, 3, 5, 7] (2 ^ 16 * 3 ^ 3 * 5 * 7)
        (fun _ _ _ o => !(o % 7 == 0) || !(o % 128 == 0)) = true :=
      lieSearch_of_lieSearchB (L := 25) (by decide +kernel)
    have hps : ∀ q : ℕ, q.Prime → q ∣ 2 ^ 16 * 3 ^ 3 * 5 * 7 → q ∈ [2, 3, 5, 7] := fun q hq hd =>
      by simpa using
        mem_of_prime_dvd [(2, 16), (3, 3), (5, 1), (7, 1)] (by decide) (by decide) hq hd
    have h := lieSearch_sound hN hps hS ht hp hf hmin hnB hadm hdvd
    simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at h
    omega
  · exact absurd (h13.trans hdvd) (by norm_num)
  · exact absurd (h19.trans hdvd) (by norm_num)
  · have key : ∀ m ∈ sporadicOrders, ¬ m ∣ 2 ^ 16 * 3 ^ 3 * 5 * 7 := by decide
    exact absurd hdvd (key _ hs)
  · exact absurd (h25.trans hdvd) (by norm_num)

theorem c1_card_mem
    {T : Type} [Group T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a) (hdvd : Nat.card T ∣ 2 ^ 16 * 3 ^ 3 * 5 * 7)
    (h7 : 7 ∣ Nat.card T) : Nat.card T ∈ [168, 504, 2520, 6048, 12096, 20160] := by
  have hN : (2 ^ 16 * 3 ^ 3 * 5 * 7 : ℕ) ≠ 0 := by norm_num
  have hfin : Nat.card T ≠ 0 := fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  rcases catalog_order_cases hT hnonab hfin with ⟨n, hn, hc⟩ |
      ⟨t, n, p, f, ht, hp, hf, hmin, hnB, hadm, hc, -⟩ | h13 | h19 | hs | h25
  · rw [hc] at hdvd h7 ⊢
    have h12 := le_twelve_of_factorial_div_two_dvd (by omega) (by norm_num) hdvd
    revert hdvd h7
    interval_cases n <;> decide
  · rw [hc] at hdvd h7 ⊢
    have hS : lieSearch [2, 3, 5, 7] (2 ^ 16 * 3 ^ 3 * 5 * 7)
        (fun _ _ _ o => !(o % 7 == 0) || [168, 504, 2520, 6048, 12096, 20160].contains o) =
          true := lieSearch_of_lieSearchB (L := 25) (by decide +kernel)
    have hps : ∀ q : ℕ, q.Prime → q ∣ 2 ^ 16 * 3 ^ 3 * 5 * 7 → q ∈ [2, 3, 5, 7] := fun q hq hd =>
      by simpa using
        mem_of_prime_dvd [(2, 16), (3, 3), (5, 1), (7, 1)] (by decide) (by decide) hq hd
    have h := lieSearch_sound hN hps hS ht hp hf hmin hnB hadm hdvd
    have h0 : lieOrd t n (p ^ f) % 7 = 0 := Nat.mod_eq_zero_of_dvd h7
    simp only [h0, beq_self_eq_true, Bool.not_true, Bool.false_or, List.contains_eq_any_beq,
      List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact h
  · exact absurd (h13.trans hdvd) (by norm_num)
  · exact absurd (h19.trans hdvd) (by norm_num)
  · have key : ∀ m ∈ sporadicOrders, ¬ m ∣ 2 ^ 16 * 3 ^ 3 * 5 * 7 := by decide
    exact absurd hdvd (key _ hs)
  · exact absurd (h25.trans hdvd) (by norm_num)

theorem prime_pow_eq_sixteen_or_seventeen {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hq : p ^ f = 16 ∨ p ^ f = 17) : (p = 2 ∧ f = 4) ∨ (p = 17 ∧ f = 1) := by
  have hpq : p ∣ p ^ f := dvd_pow_self p (by omega)
  rcases hq with hq | hq
  · have h16 : p ^ f = 2 ^ 4 := hq.trans (by norm_num)
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 4 by rw [← h16]; exact hpq))
    subst hp2
    exact Or.inl ⟨rfl, Nat.pow_right_injective le_rfl (hq.trans (by norm_num))⟩
  · have hp17 : p = 17 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hq ▸ hpq)
    subst hp17
    exact Or.inr ⟨rfl, Nat.pow_right_injective (by norm_num) (hq.trans (pow_one 17).symm)⟩

theorem c2_card_mulAut_le
    {T : Type} [Group T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a) (hdvd : Nat.card T ∣ 2 ^ 11 * 3 ^ 5 * 5 * 17)
    (h17 : 17 ∣ Nat.card T) : Nat.card (MulAut T) ≤ 16320 := by
  have hN : (2 ^ 11 * 3 ^ 5 * 5 * 17 : ℕ) ≠ 0 := by norm_num
  have hfin : Nat.card T ≠ 0 := fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  have : Finite T := Nat.finite_of_card_ne_zero hfin
  rcases catalog_order_cases hT hnonab hfin with ⟨n, hn, hc⟩ |
      ⟨t, n, p, f, ht, hp, hf, hmin, hnB, hadm, hc, hPSL⟩ | h13 | h19 | hs | h25
  · exfalso
    rw [hc] at hdvd h17
    have h12 := le_twelve_of_factorial_div_two_dvd (by omega) (by norm_num) hdvd
    revert hdvd h17
    interval_cases n <;> decide
  · have hdvd' := hdvd
    rw [hc] at hdvd' h17
    have hS : lieSearch [2, 3, 5, 17] (2 ^ 11 * 3 ^ 5 * 5 * 17) (fun t n q o =>
        !(o % 17 == 0) || (t == .PSL && n == 2 && (q == 16 || q == 17))) = true :=
      lieSearch_of_lieSearchB (L := 25) (by decide +kernel)
    have hps : ∀ q : ℕ, q.Prime → q ∣ 2 ^ 11 * 3 ^ 5 * 5 * 17 → q ∈ [2, 3, 5, 17] :=
      fun q hq hd => by
        simpa using mem_of_prime_dvd [(2, 11), (3, 5), (5, 1), (17, 1)] (by decide) (by decide)
          hq hd
    have h := lieSearch_sound hN hps hS ht hp hf hmin hnB hadm hdvd'
    have h0 : lieOrd t n (p ^ f) % 17 = 0 := Nat.mod_eq_zero_of_dvd h17
    simp only [h0, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨⟨rfl, rfl⟩, hq⟩ := h
    have hout := (LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound T 2 p f
      (hPSL rfl)).2.2.2.1 rfl
    refine (card_mulAut_le T).trans ?_
    rcases prime_pow_eq_sixteen_or_seventeen hp hf hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hO : Nat.card (ComponentClassification.OuterAutomorphisms.Outer T) ≤ 4 :=
        Nat.le_of_dvd (by norm_num) (by simpa using hout)
      rw [hc, show lieOrd .PSL 2 (2 ^ 4) = 4080 by decide]
      omega
    · have hO : Nat.card (ComponentClassification.OuterAutomorphisms.Outer T) ≤ 2 :=
        Nat.le_of_dvd (by norm_num) (by simpa using hout)
      rw [hc, show lieOrd .PSL 2 (17 ^ 1) = 2448 by decide]
      omega
  · exact absurd (h13.trans hdvd) (by norm_num)
  · exact absurd (h19.trans hdvd) (by norm_num)
  · have key : ∀ m ∈ sporadicOrders, ¬ m ∣ 2 ^ 11 * 3 ^ 5 * 5 * 17 := by decide
    exact absurd hdvd (key _ hs)
  · exact absurd (h25.trans hdvd) (by norm_num)

theorem c3_false
    {T : Type} [Group T] (hT : Catalog T) (hnonab : ∃ a b : T, a * b ≠ b * a)
    (hdvd : Nat.card T ∣ 2 ^ 7 * 3 ^ 4 * 5 * 7 * 11 * 17) (h187 : 11 * 17 ∣ Nat.card T) :
    False := by
  have hN : (2 ^ 7 * 3 ^ 4 * 5 * 7 * 11 * 17 : ℕ) ≠ 0 := by norm_num
  have hfin : Nat.card T ≠ 0 := fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  rcases catalog_order_cases hT hnonab hfin with ⟨n, hn, hc⟩ |
      ⟨t, n, p, f, ht, hp, hf, hmin, hnB, hadm, hc, -⟩ | h13 | h19 | hs | h25
  · rw [hc] at hdvd h187
    have h12 := le_twelve_of_factorial_div_two_dvd (by omega) (by norm_num) hdvd
    revert hdvd h187
    interval_cases n <;> decide
  · rw [hc] at hdvd h187
    have hS : lieSearch [2, 3, 5, 7, 11, 17] (2 ^ 7 * 3 ^ 4 * 5 * 7 * 11 * 17)
        (fun _ _ _ o => !(o % 187 == 0)) = true :=
      lieSearch_of_lieSearchB (L := 26) (by decide +kernel)
    have hps : ∀ q : ℕ, q.Prime → q ∣ 2 ^ 7 * 3 ^ 4 * 5 * 7 * 11 * 17 →
        q ∈ [2, 3, 5, 7, 11, 17] := fun q hq hd => by
      simpa using mem_of_prime_dvd [(2, 7), (3, 4), (5, 1), (7, 1), (11, 1), (17, 1)]
        (by decide) (by decide) hq hd
    have h := lieSearch_sound hN hps hS ht hp hf hmin hnB hadm hdvd
    have h0 : lieOrd t n (p ^ f) % 187 = 0 := Nat.mod_eq_zero_of_dvd h187
    simp [h0] at h
  · exact absurd (h13.trans hdvd) (by norm_num)
  · exact absurd (h19.trans hdvd) (by norm_num)
  · have key : ∀ m ∈ sporadicOrders, m ∣ 2 ^ 7 * 3 ^ 4 * 5 * 7 * 11 * 17 → ¬ 11 * 17 ∣ m := by
      decide
    exact key _ hs hdvd h187
  · exact absurd (h25.trans hdvd) (by norm_num)

theorem catalog_of_kProper_of_surjective {G : Type} [Group G]
    (hK : CFSG.Assembly.KProper Catalog G) (K : Subgroup G) (hKtop : K ≠ ⊤) (S : Type) [Group S]
    [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a) (φ : K →* S)
    (hφ : Function.Surjective φ) : Catalog S :=
  CFSG.KCore.KProperNonab.catalogue_of_surjective CFSG.SectionRank.catalog_isoInvariant hK K hKtop
    hnonab φ hφ

theorem catalog_of_kProper_of_le_quotient {G : Type} [Group G]
    (hK : CFSG.Assembly.KProper Catalog G) {Y : Subgroup G} (hY : Y ≠ ⊤) {X : Type} [Group X]
    (φ : Y →* X) (hφ : Function.Surjective φ) (T : Subgroup X) [IsSimpleGroup T]
    (hnonab : ∃ a b : T, a * b ≠ b * a) : Catalog T := by
  let K : Subgroup G := (T.comap φ).map Y.subtype
  have hKY : K ≤ Y := Subgroup.map_subtype_le _
  have hKtop : K ≠ ⊤ := fun h => hY (top_unique (h ▸ hKY))
  have hmem : ∀ k : K, (φ.comp (Subgroup.inclusion hKY)) k ∈ T := by
    rintro ⟨_, y, hy, rfl⟩
    exact hy
  let ψ : K →* T := (φ.comp (Subgroup.inclusion hKY)).codRestrict T hmem
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := hφ x
    exact ⟨⟨y, y, hx, rfl⟩, rfl⟩
  exact catalog_of_kProper_of_surjective hK K hKtop T hnonab ψ hψ

end CFSG.EvenSmallLie.CatalogOrders
