module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrdersData
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrders
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.Monster.AxisCount.HSCount

public section

namespace CFSG.EvenSmallLie.Child3

open CFSG.EvenSmallLie.CatalogOrders CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem lieSearchV_sound {pv : List (ℕ × ℕ)} {N : ℕ}
    (hpv : ∀ p : ℕ, p.Prime → p ∣ N → ∃ e, (p, e) ∈ pv ∧ ¬ p ^ (e + 1) ∣ N)
    {C : StatedLieTag → ℕ → ℕ → ℕ → ℕ → Bool} (hS : lieSearchV pv N C = true)
    {t : StatedLieTag} (ht : t ∈ searchTags) {n p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hn : lieMin t ≤ n) (hn0 : lieMin t = 0 → n = 0) (hnB : n ≤ lieExp t n + 1)
    (hadm : lieAdm t p f = true) (hd : lieOrd t n (p ^ f) ∣ N) :
    C t n p f (lieOrd t n (p ^ f)) = true := by
  have hqd : p ^ (f * lieExp t n) ∣ N := by
    rw [pow_mul]
    exact (pow_lieExp_dvd hn _).trans hd
  have he := one_le_lieExp ht hn
  have hpN : p ∣ N := (dvd_pow_self p (by positivity)).trans hqd
  obtain ⟨e, hpe, hmax⟩ := hpv p hp hpN
  have hfe : f * lieExp t n ≤ e := by
    by_contra hlt
    exact hmax ((pow_dvd_pow p (by omega)).trans hqd)
  have hfe' : f ≤ e := le_trans (Nat.le_mul_of_pos_right f he) hfe
  have hle : lieExp t n ≤ f * lieExp t n := Nat.le_mul_of_pos_left _ (by omega)
  unfold lieSearchV at hS
  rw [List.all_eq_true] at hS
  have h1 := hS (p, e) hpe
  rw [List.all_eq_true] at h1
  have h2 := h1 (f - 1) (List.mem_range.2 (by omega))
  rw [List.all_eq_true] at h2
  have h3 := h2 t ht
  rw [List.all_eq_true] at h3
  have hnr : n ∈ List.range (if lieMin t = 0 then 1 else (p, e).2 + 2) := by
    rw [List.mem_range]
    split_ifs with h0
    · rw [hn0 h0]
      omega
    · simp only
      omega
  have h4 := h3 n hnr
  rw [Nat.sub_add_cancel hf] at h4
  have hg : (decide (lieMin t ≤ n) && lieAdm t (p, e).1 f &&
      decide (f * lieExp t n ≤ (p, e).2) && N % lieOrd t n ((p, e).1 ^ f) == 0) = true := by
    simp [hn, hadm, hfe, Nat.mod_eq_zero_of_dvd hd]
  rw [hg] at h4
  simpa using h4

theorem primes_of_factorization {pv : List (ℕ × ℕ)} {N : ℕ} (hpr : ∀ x ∈ pv, x.1.Prime)
    (hN : (pv.map fun x => x.1 ^ x.2).prod = N) (hmax : ∀ x ∈ pv, ¬ x.1 ^ (x.2 + 1) ∣ N) :
    ∀ p : ℕ, p.Prime → p ∣ N → ∃ e, (p, e) ∈ pv ∧ ¬ p ^ (e + 1) ∣ N := by
  intro p hp hpN
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (mem_of_prime_dvd pv hpr hN hp hpN)
  exact ⟨x.2, hx, hmax x hx⟩

section Cases


theorem catalog_model_cases {T : Type} [Group T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a) :
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (T ≃* alternatingGroup (Fin n))) ∨
    (∃ (t : StatedLieTag) (n p f : ℕ), t ∈ searchTags ∧ p.Prime ∧ 1 ≤ f ∧ lieMin t ≤ n ∧
      (lieMin t = 0 → n = 0) ∧ n ≤ lieExp t n + 1 ∧ lieAdm t p f = true ∧
      Nat.card T = lieOrd t n (p ^ f) ∧ LieModel T t n p f) ∨
    (∃ p f : ℕ, ReeTitsModel T .twistedF4 p f) ∨ (∃ p f : ℕ, ReeTitsModel T .Tits p f) ∨
    ∃ s, Nonempty (T ≃* NativeSporadic.Carrier s) := by
  obtain ⟨a, b, hab⟩ := hnonab
  rcases hT with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, he⟩ | ⟨t, n, p, f, h⟩ |
      (⟨t, p, f, ht, h⟩ | ⟨t, p, f, ht, h⟩ | ⟨p, f, h⟩) | ⟨s, hs⟩
  · exfalso
    apply hab
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · exact Or.inl ⟨n, hn, he⟩
  ·
    right; left
    obtain ⟨hp, hf, hcl⟩ := h.1
    have hc := card_eq_lieOrd_of_classical h
    cases t
    case PSL =>
      exact ⟨.PSL, n, p, f, by decide, hp, hf, hcl.1, by simp [lieMin],
        le_lieExp_add_one hcl.1 (Or.inr (Or.inl rfl)), rfl, hc, Or.inl ⟨by decide, h⟩⟩
    case PSU =>
      exact ⟨.PSU, n, p, f, by decide, hp, hf, hcl.1, by simp [lieMin],
        le_lieExp_add_one hcl.1 (Or.inr (Or.inr (Or.inl rfl))), rfl, hc, Or.inl ⟨by decide, h⟩⟩
    case PSp =>
      exact ⟨.PSp, n, p, f, by decide, hp, hf, hcl.1, by simp [lieMin],
        le_lieExp_add_one hcl.1 (by simp), rfl, hc, Or.inl ⟨by decide, h⟩⟩
    case POmegaOdd =>
      exact ⟨.POmegaOdd, n, p, f, by decide, hp, hf, hcl.1, by simp [lieMin],
        le_lieExp_add_one hcl.1 (by simp), rfl, hc, Or.inl ⟨by decide, h⟩⟩
    case POmegaPlus =>
      exact ⟨.POmegaPlus, n, p, f, by decide, hp, hf, hcl, by simp [lieMin],
        le_lieExp_add_one hcl (by simp), rfl, hc, Or.inl ⟨by decide, h⟩⟩
    case POmegaMinus =>
      exact ⟨.POmegaMinus, n, p, f, by decide, hp, hf, hcl, by simp [lieMin],
        le_lieExp_add_one hcl (by simp), rfl, hc, Or.inl ⟨by decide, h⟩⟩
    all_goals exact h.2.elim
  ·
    right; left
    obtain ⟨hp, hf, -⟩ := h.1
    have hc := card_eq_lieOrd_of_exceptional h
    have hts : t ∈ searchTags := by
      revert ht; cases t <;> decide
    have hmin : lieMin t = 0 := by
      revert ht; cases t <;> simp [lieMin, chevalleyExceptionalTags]
    have hadm : lieAdm t p f = true := by
      revert ht; cases t <;> simp [lieAdm, chevalleyExceptionalTags]
    exact ⟨t, 0, p, f, hts, hp, hf, hmin.le, fun _ => rfl, by omega, hadm, hc,
      Or.inr (Or.inl ⟨rfl, ht, h⟩)⟩
  ·
    have htt : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
      revert ht; cases t <;> simp [reeTitsTags]
    rcases htt with rfl | rfl | rfl
    · right; left
      obtain ⟨rfl, ⟨a, ha, rfl⟩, hc⟩ := card_eq_lieOrd_of_ree h
      refine ⟨.twistedG2, 0, 3, 2 * a + 1, by decide, Nat.prime_three, by omega, le_rfl,
        fun _ => rfl, by omega, ?_, hc, Or.inr (Or.inr (Or.inl ⟨rfl, ht, h⟩))⟩
      simp only [lieAdm, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq]
      omega
    · exact Or.inr (Or.inr (Or.inl ⟨p, f, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, h⟩)))
  ·
    right; left
    obtain ⟨rfl, ⟨a, ha, rfl⟩, hc⟩ := card_eq_lieOrd_of_suzuki h
    refine ⟨.twistedB2, 0, 2, 2 * a + 1, by decide, Nat.prime_two, by omega, le_rfl,
      fun _ => rfl, by omega, ?_, hc, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩))⟩
    simp only [lieAdm, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, hs⟩)))

theorem filter_cases {T : Type} [Group T] (hT : Catalog T) (hnonab : ∃ a b : T, a * b ≠ b * a)
    {l : List (StatedLieTag × ℕ × ℕ × ℕ)} {pv : List (ℕ × ℕ)} {N : ℕ}
    (hpv : ∀ p : ℕ, p.Prime → p ∣ N → ∃ e, (p, e) ∈ pv ∧ ¬ p ^ (e + 1) ∣ N)
    (hS : lieSearchV pv N (filterCheck l) = true) (hord : Nat.card T ∣ N)
    (h168 : 168 ∣ Nat.card T) :
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (T ≃* alternatingGroup (Fin n))) ∨
    (∃ (t : StatedLieTag) (n p f : ℕ), p.Prime ∧ sectorTuple t n p f = true ∧
      LieModel T t n p f) ∨
    (∃ x ∈ l, LieModel T x.1 x.2.1 x.2.2.1 x.2.2.2) ∨
    (∃ p f : ℕ, ReeTitsModel T .twistedF4 p f) ∨ (∃ p f : ℕ, ReeTitsModel T .Tits p f) ∨
    ∃ s, Nonempty (T ≃* NativeSporadic.Carrier s) := by
  rcases catalog_model_cases hT hnonab with h | ⟨t, n, p, f, ht, hp, hf, hn, hn0, hnB, hadm,
    hc, hm⟩ | h | h | h
  · exact Or.inl h
  · rw [hc] at hord h168
    have hC := lieSearchV_sound hpv hS ht hp hf hn hn0 hnB hadm hord
    simp only [filterCheck, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
      List.contains_iff_mem] at hC
    rcases hC with (hC | hC) | hC
    · exact absurd (Nat.mod_eq_zero_of_dvd h168) hC
    · exact Or.inr (Or.inl ⟨t, n, p, f, hp, hC, hm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨(t, n, p, f), hC, hm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Cases

section Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree


theorem card_dvd_of_reeTitsModel_Tits {T : Type} [Group T] {p f : ℕ}
    (h : ReeTitsModel T .Tits p f) : Nat.card T ∣ 35942400 := by
  obtain ⟨⟨-, -, -, hp, hf1⟩, a, hf, hmodel⟩ := h
  subst hp hf1
  obtain rfl : a = 0 := by omega
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_of_reeTitsRelationModel_F4 hmodel
  rw [pow_one] at hK
  rw [Nat.card_congr (e.trans ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.center_commutator_reeFixed_eq_bot hK)).trans
      QuotientGroup.quotientBot)).toEquiv]
  have hcard := CFSG.SectionRank.TitsOrder.Tits_card hK
  rw [← hcard]
  exact Subgroup.card_subgroup_dvd_card _

theorem not_seven_dvd_of_reeTitsModel_Tits {T : Type} [Group T] {p f : ℕ}
    (h : ReeTitsModel T .Tits p f) : ¬ 7 ∣ Nat.card T := fun h7 =>
  absurd (h7.trans (card_dvd_of_reeTitsModel_Tits h)) (by decide)

theorem false_of_reeTitsModel_twistedF4 {T : Type} [Group T] {p f N : ℕ}
    (h : ReeTitsModel T .twistedF4 p f) (hord : Nat.card T ∣ N) (h2 : ¬ 2 ^ 67 ∣ N)
    (h37 : ¬ 37 ∣ N) (h41 : ¬ 41 ∣ N) : False := by
  obtain ⟨-, -, -, hp2, -, hiso⟩ := ReeTag.large_Ree_model_Schreier T p f h
  obtain ⟨hadm, a, hfa, K, _, _, hK, ⟨e⟩⟩ := h
  subst hp2
  have ha : 1 ≤ a := by
    have := hadm.2.2.2.2.2
    omega
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hc := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    a K hK').1
  rw [Nat.card_congr E.toEquiv, hc] at hord
  rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with rfl | rfl | ha3
  · exact h37 ((by decide : 37 ∣ _).trans hord)
  · exact h41 ((by decide : 41 ∣ _).trans hord)
  · apply h2
    refine (pow_dvd_pow 2 (by omega : 67 ≤ (2 * a + 1) * 12)).trans ?_
    rw [pow_mul]
    refine dvd_trans ?_ hord
    simp only [mul_assoc]
    exact dvd_mul_right _ _

end Ree

section Sporadic


theorem card_carrier (s : TauCeti.SporadicName) (hTh : s ≠ .Th) (hM : s ≠ .M) :
    Nat.card (NativeSporadic.Carrier s) = sporadicCard s := by
  cases s
  case M11 => exact CFSG.Sporadic.Mathieu.card_M11
  case M12 => exact CFSG.Sporadic.Mathieu.card_M12
  case M22 => exact CFSG.Sporadic.Mathieu.card_M22
  case M23 => exact card_M23
  case M24 => exact CFSG.Sporadic.Mathieu.card_M24
  case J1 => exact CFSG.Sporadic.J1.card_J1
  case J2 => exact CFSG.Sporadic.J2.card_J2
  case J3 => exact CFSG.Sporadic.J3.card_J3
  case J4 => exact CFSG.Sporadic.J4.card_J4
  case HS => exact CFSG.Sporadic.HS.card_HS
  case McL => exact CFSG.Sporadic.McL.card_McL
  case He => exact CFSG.Sporadic.He.fam_he_order.1
  case Ru => exact CFSG.Sporadic.Ru.card_Ru
  case Suz => exact CFSG.Sporadic.Suz.card_Suz
  case ONan => exact CFSG.Sporadic.ON.card_ON
  case Co1 => exact CFSG.Sporadic.Co1.card_Co1
  case Co2 => exact CFSG.Sporadic.Co2.card_Co2
  case Co3 => exact CFSG.Sporadic.Co3.card_Co3
  case Fi22 => exact CFSG.Sporadic.Fi22.card_Fi22
  case Fi23 => exact CFSG.Sporadic.Fi23.card_Fi23
  case Fi24Prime => exact CFSG.Sporadic.Fi24.card_Fi24prime
  case HN => exact CFSG.Sporadic.HN.card_HN
  case Ly => exact CFSG.Sporadic.Ly.card_Ly
  case Th => exact absurd rfl hTh
  case B => exact CFSG.Monster.Existence.card_nativeB
  case M => exact absurd rfl hM

end Sporadic

section Monster


theorem twentynine_dvd_of_mulEquiv_M {T : Type} [Group T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) : 29 ∣ Nat.card T := by
  obtain ⟨E⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  rw [Nat.card_congr E.toEquiv, CFSG.Monster.AxisCount.HS.natCard_Gmat]
  exact Dvd.dvd.mul_right (by norm_num) _

end Monster

section SporadicCases


theorem sporadic_cases {T : Type} [Group T] [IsSimpleGroup T] {N : ℕ}
    {s : TauCeti.SporadicName} (e : T ≃* NativeSporadic.Carrier s) (hord : Nat.card T ∣ N)
    (h19 : ¬ 19 ∣ N) (h29 : ¬ 29 ∣ N) : s ≠ .Th ∧ s ≠ .M ∧ Nat.card T = sporadicCard s := by
  have hTh : s ≠ .Th := by
    rintro rfl
    refine h19 (dvd_trans ?_ hord)
    rw [Nat.card_congr e.toEquiv]
    exact nineteen_dvd_card_Th
  have hM : s ≠ .M := by
    rintro rfl
    exact h29 ((twentynine_dvd_of_mulEquiv_M e).trans hord)
  exact ⟨hTh, hM, (Nat.card_congr e.toEquiv).trans (card_carrier s hTh hM)⟩

end SporadicCases

section Filters


theorem filter_twelve {T : Type} [Group T] [IsSimpleGroup T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a) (hord : Nat.card T ∣ glOrd 12)
    (h168 : 168 ∣ Nat.card T) :
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (T ≃* alternatingGroup (Fin n))) ∨
    (∃ (t : StatedLieTag) (n p f : ℕ), p.Prime ∧ sectorTuple t n p f = true ∧
      LieModel T t n p f) ∨
    (∃ x ∈ residualTuples12, LieModel T x.1 x.2.1 x.2.2.1 x.2.2.2) ∨
    ∃ s ∈ residualSporadic12, Nonempty (T ≃* NativeSporadic.Carrier s) := by
  have hpv : ∀ p : ℕ, p.Prime → p ∣ glOrd 12 → ∃ e, (p, e) ∈ glPrimes12 ∧
      ¬ p ^ (e + 1) ∣ glOrd 12 := by
    refine primes_of_factorization ?_ (by decide +kernel) (by decide +kernel)
    simp only [glPrimes12, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq]
    norm_num
  have hS : lieSearchV glPrimes12 (glOrd 12) (filterCheck residualTuples12) = true := by
    decide +kernel
  rcases filter_cases hT hnonab hpv hS hord h168 with h | h | h | ⟨p, f, h⟩ | ⟨p, f, h⟩ |
    ⟨s, ⟨e⟩⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact (false_of_reeTitsModel_twistedF4 h hord (by decide +kernel) (by decide +kernel)
      (by decide +kernel)).elim
  · exact (not_seven_dvd_of_reeTitsModel_Tits h ((by norm_num : 7 ∣ 168).trans h168)).elim
  · obtain ⟨hTh, hM, hc⟩ := sporadic_cases e hord (by decide +kernel) (by decide +kernel)
    rw [hc] at hord h168
    have key : ∀ s : TauCeti.SporadicName, s ≠ .Th → s ≠ .M → sporadicCard s ∣ glOrd 12 →
        168 ∣ sporadicCard s → s ∈ residualSporadic12 := by
      decide +kernel
    exact Or.inr (Or.inr (Or.inr ⟨s, key s hTh hM hord h168, ⟨e⟩⟩))

theorem filter_nine {T : Type} [Group T] [IsSimpleGroup T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a) (hord : Nat.card T ∣ glOrd 9)
    (h168 : 168 ∣ Nat.card T) :
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (T ≃* alternatingGroup (Fin n))) ∨
    (∃ (t : StatedLieTag) (n p f : ℕ), p.Prime ∧ sectorTuple t n p f = true ∧
      LieModel T t n p f) ∨
    (∃ x ∈ residualTuples9, LieModel T x.1 x.2.1 x.2.2.1 x.2.2.2) ∨
    ∃ s ∈ residualSporadic9, Nonempty (T ≃* NativeSporadic.Carrier s) := by
  have hpv : ∀ p : ℕ, p.Prime → p ∣ glOrd 9 → ∃ e, (p, e) ∈ glPrimes9 ∧
      ¬ p ^ (e + 1) ∣ glOrd 9 := by
    refine primes_of_factorization ?_ (by decide +kernel) (by decide +kernel)
    simp only [glPrimes9, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq]
    norm_num
  have hS : lieSearchV glPrimes9 (glOrd 9) (filterCheck residualTuples9) = true := by
    decide +kernel
  rcases filter_cases hT hnonab hpv hS hord h168 with h | h | h | ⟨p, f, h⟩ | ⟨p, f, h⟩ |
    ⟨s, ⟨e⟩⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact (false_of_reeTitsModel_twistedF4 h hord (by decide +kernel) (by decide +kernel)
      (by decide +kernel)).elim
  · exact (not_seven_dvd_of_reeTitsModel_Tits h ((by norm_num : 7 ∣ 168).trans h168)).elim
  · obtain ⟨hTh, hM, hc⟩ := sporadic_cases e hord (by decide +kernel) (by decide +kernel)
    rw [hc] at hord h168
    have key : ∀ s : TauCeti.SporadicName, s ≠ .Th → s ≠ .M → sporadicCard s ∣ glOrd 9 →
        168 ∣ sporadicCard s → s ∈ residualSporadic9 := by
      decide +kernel
    exact Or.inr (Or.inr (Or.inr ⟨s, key s hTh hM hord h168, ⟨e⟩⟩))

end Filters

end CFSG.EvenSmallLie.Child3
