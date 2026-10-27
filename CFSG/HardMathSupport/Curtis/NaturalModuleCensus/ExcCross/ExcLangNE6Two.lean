module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E6CartanIndexOne
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNEmbed
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenFix
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenTorus
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNSylow
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcWeylWords
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Two

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Curtis.UnitaryLevi CFSG.RankThree.Lattice
  Polynomial

section Valuation

private lemma padicValNat_three_four' : padicValNat 3 4 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by norm_num)

private lemma padicValNat_three_six'' : padicValNat 3 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]

private lemma not_three_dvd_pow_sub_one_odd {q : ℕ} (hq : 1 < q) (h3 : 3 ∣ q + 1) {k : ℕ}
    (hk : Odd k) : ¬ 3 ∣ q ^ k - 1 := by
  intro h
  have hq3 : q % 3 = 2 := by omega
  have h1 : q ^ k % 3 = 2 := by
    obtain ⟨m, rfl⟩ := hk
    rw [Nat.pow_mod, hq3, pow_succ, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have h2 : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
  omega

theorem padicValNat_three_ordE6_neg {q : ℕ} (hq : 1 < q) (h3 : 3 ∣ q + 1) :
    padicValNat 3 (CFSG.Open.ordE6 q) = 4 * padicValNat 3 (q + 1) + 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnq : ¬ 3 ∣ q := by omega
  have sub_one_pos' : ∀ {n : ℕ}, n ≠ 0 → 0 < q ^ n - 1 := fun hn =>
    Nat.sub_pos_of_lt (Nat.one_lt_pow hn hq)
  have h12 := sub_one_pos' (n := 12) (by norm_num)
  have h9 := sub_one_pos' (n := 9) (by norm_num)
  have h8 := sub_one_pos' (n := 8) (by norm_num)
  have h6 := sub_one_pos' (n := 6) (by norm_num)
  have h5 := sub_one_pos' (n := 5) (by norm_num)
  have h2 := sub_one_pos' (n := 2) (by norm_num)
  have hg : Nat.gcd 3 (q - 1) = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
  unfold CFSG.Open.ordE6
  rw [hg, Nat.div_one, padicValNat.mul (by positivity) h2.ne',
    padicValNat.mul (by positivity) h5.ne', padicValNat.mul (by positivity) h6.ne',
    padicValNat.mul (by positivity) h8.ne', padicValNat.mul (by positivity) h9.ne',
    padicValNat.mul (by positivity) h12.ne',
    padicValNat.pow q 36, padicValNat.eq_zero_of_not_dvd hnq,
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 12 ≠ 0) (by norm_num),
    padicValNat.eq_zero_of_not_dvd (not_three_dvd_pow_sub_one_odd hq h3 (by decide : Odd 9)),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 8 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 6 ≠ 0) (by norm_num),
    padicValNat.eq_zero_of_not_dvd (not_three_dvd_pow_sub_one_odd hq h3 (by decide : Odd 5)),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 2 ≠ 0) (by norm_num)]
  simp only [Nat.reduceDiv]
  rw [padicValNat_three_six'', padicValNat_three_four', show padicValNat 3 3 = 1 from padicValNat_self,
    show padicValNat 3 1 = 0 from padicValNat.eq_zero_of_not_dvd (by norm_num)]
  omega

end Valuation

section Centralizer


@[expose] def laE6 : List (Fin Tag.E6.rank) := ([3, 1] : List (Fin 6))

@[expose] def lbE6 : List (Fin Tag.E6.rank) :=
  ([5, 4, 3, 2, 1, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 1, 3, 2, 0] : List (Fin 6))

@[expose] def wE6 : List (Fin Tag.E6.rank) := e6TwoWord

theorem laE6_cube : wordW Tag.E6 (laE6 ++ laE6 ++ laE6) = wordW Tag.E6 [] :=
  wordW_eq_of_matrix _ _ _ (by decide +kernel)

theorem lbE6_cube : wordW Tag.E6 (lbE6 ++ lbE6 ++ lbE6) = wordW Tag.E6 [] :=
  wordW_eq_of_matrix _ _ _ (by decide +kernel)

theorem laE6_lbE6_comm : wordW Tag.E6 (laE6 ++ lbE6) = wordW Tag.E6 (lbE6 ++ laE6) :=
  wordW_eq_of_matrix _ _ _ (by decide +kernel)

theorem laE6_comm : wordW Tag.E6 (laE6 ++ wE6) = wordW Tag.E6 (wE6 ++ laE6) :=
  wordW_eq_of_matrix _ _ _ (by decide +kernel)

theorem lbE6_comm : wordW Tag.E6 (lbE6 ++ wE6) = wordW Tag.E6 (wE6 ++ lbE6) :=
  wordW_eq_of_matrix _ _ _ (by decide +kernel)

@[expose] def wa6 : WeylGroup Tag.E6 := wordW Tag.E6 laE6

@[expose] def wb6 : WeylGroup Tag.E6 := wordW Tag.E6 lbE6

@[expose] def ww6 : WeylGroup Tag.E6 := wordW Tag.E6 wE6

theorem ww6_eq : ww6 = (coxeterSystem Tag.E6).wordProd e6TwoWord := rfl

theorem wa6_cube : wa6 ^ 3 = 1 := by
  have := laE6_cube
  rw [wordW_append, wordW_append] at this
  simpa [wa6, wordW, pow_succ, mul_assoc] using this

theorem wb6_cube : wb6 ^ 3 = 1 := by
  have := lbE6_cube
  rw [wordW_append, wordW_append] at this
  simpa [wb6, wordW, pow_succ, mul_assoc] using this

theorem wa6_wb6_comm : wa6 * wb6 = wb6 * wa6 := by
  have := laE6_lbE6_comm
  rw [wordW_append, wordW_append] at this
  exact this

theorem wa6_ww6_comm : wa6 * ww6 = ww6 * wa6 := by
  have := laE6_comm
  rw [wordW_append, wordW_append] at this
  exact this

theorem wb6_ww6_comm : wb6 * ww6 = ww6 * wb6 := by
  have := lbE6_comm
  rw [wordW_append, wordW_append] at this
  exact this

theorem wa6_ne_one : wa6 ≠ 1 := fun h => by
  have := matrix_eq_of_wordW_eq Tag.E6 laE6 [] (by simpa [wa6, wordW] using h)
  revert this
  decide +kernel

theorem wb6_ne_one : wb6 ≠ 1 := fun h => by
  have := matrix_eq_of_wordW_eq Tag.E6 lbE6 [] (by simpa [wb6, wordW] using h)
  revert this
  decide +kernel

theorem wb6_ne_wa6 : wb6 ≠ wa6 := fun h => by
  have := matrix_eq_of_wordW_eq Tag.E6 lbE6 laE6 h
  revert this
  decide +kernel

theorem wb6_ne_wa6_sq : wb6 ≠ wa6 ^ 2 := fun h => by
  have h' : wordW Tag.E6 lbE6 = wordW Tag.E6 (laE6 ++ laE6) := by
    rw [wordW_append]; simpa [wa6, wb6, sq] using h
  have := matrix_eq_of_wordW_eq Tag.E6 lbE6 (laE6 ++ laE6) h'
  revert this
  decide +kernel

theorem pair_comm_of_closure6 {G : Type*} [Group G] (a b : G) (h : a * b = b * a) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set G), ∀ y ∈ Subgroup.closure ({a, b} : Set G),
      x * y = y * x := by
  have hcomm : ∀ x ∈ ({a, b} : Set G), x ∈ Subgroup.centralizer ({a, b} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | rfl | exact h | exact h.symm
  intro x hx y hy
  have h1 : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({a, b} : Set G) :=
    (Subgroup.closure_le _).2 hcomm
  have h2 := h1 hx
  rw [← Subgroup.centralizer_closure] at h2
  exact (Subgroup.mem_centralizer_iff.1 h2 y hy).symm

theorem zpow_mod_three_aux6 {G : Type*} [Group G] (g : G) (h3 : g ^ 3 = 1) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g ∨ g ^ k = g ^ 2 := by
  have hg3 : g ^ (3 : ℤ) = 1 := by exact_mod_cast h3
  have hk : k = 3 * (k / 3) + k % 3 := (Int.mul_ediv_add_emod k 3).symm
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have h2 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hpow : g ^ k = g ^ (k % 3) := by
    conv_lhs => rw [hk]
    rw [zpow_add, zpow_mul, hg3, one_zpow, one_mul]
  rw [hpow]
  obtain ⟨r, hr⟩ : ∃ r, r = k % 3 := ⟨_, rfl⟩
  rw [← hr] at h0 h2 ⊢
  interval_cases r
  · exact Or.inl (zpow_zero g)
  · exact Or.inr (Or.inl (zpow_one g))
  · exact Or.inr (Or.inr (by simp))

theorem wb6_not_mem_zpowers : wb6 ∉ Subgroup.zpowers wa6 := fun h => by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  rcases zpow_mod_three_aux6 wa6 wa6_cube k with h | h | h
  · exact wb6_ne_one (hk.symm.trans h)
  · exact wb6_ne_wa6 (hk.symm.trans h)
  · exact wb6_ne_wa6_sq (hk.symm.trans h)

@[expose] def Q6 : Subgroup (WeylGroup Tag.E6) := Subgroup.closure {wa6, wb6}

theorem wa6_mem : wa6 ∈ Q6 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem wb6_mem : wb6 ∈ Q6 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem Q6_comm : ∀ x ∈ Q6, ∀ y ∈ Q6, x * y = y * x :=
  pair_comm_of_closure6 wa6 wb6 wa6_wb6_comm

theorem Q6_cube : ∀ x ∈ Q6, x ^ 3 = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => rcases hy with rfl | rfl; exact wa6_cube; exact wb6_cube
  | one => simp
  | mul a b ha hb ha3 hb3 =>
    rw [(show Commute a b from Q6_comm a ha b hb).mul_pow, ha3, hb3, one_mul]
  | inv a ha ha3 => simp [inv_pow, ha3]

theorem Q6_pGroup : IsPGroup 3 Q6 := fun x => ⟨1, by
  ext
  simpa using Q6_cube x x.2⟩

theorem mem_Q6 {x : WeylGroup Tag.E6} (hx : x ∈ Q6) : ∃ i j : ℕ, x = wa6 ^ i * wb6 ^ j := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨i, j, rfl⟩ := ha
    obtain ⟨i', j', rfl⟩ := hb
    refine ⟨i + i', j + j', ?_⟩
    have hc : Commute (wb6 ^ j) (wa6 ^ i') :=
      ((show Commute wa6 wb6 from wa6_wb6_comm).symm.pow_pow j i')
    calc wa6 ^ i * wb6 ^ j * (wa6 ^ i' * wb6 ^ j') =
          wa6 ^ i * (wb6 ^ j * wa6 ^ i') * wb6 ^ j' := by group
      _ = wa6 ^ i * (wa6 ^ i' * wb6 ^ j) * wb6 ^ j' := by rw [hc.eq]
      _ = _ := by rw [pow_add, pow_add]; group
  | inv a _ ha =>
    obtain ⟨i, j, rfl⟩ := ha
    refine ⟨2 * i, 2 * j, ?_⟩
    have hc : Commute (wa6 ^ i) (wb6 ^ j) :=
      ((show Commute wa6 wb6 from wa6_wb6_comm).pow_pow i j)
    have h1 : (wa6 ^ i)⁻¹ = wa6 ^ (2 * i) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, wa6_cube,
        one_pow]
    have h2 : (wb6 ^ j)⁻¹ = wb6 ^ (2 * j) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, wb6_cube,
        one_pow]
    rw [mul_inv_rev, h1, h2]
    exact ((show Commute wa6 wb6 from wa6_wb6_comm).symm.pow_pow (2 * j) (2 * i)).eq

theorem Q6_card : Nat.card Q6 = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsurj : Function.Surjective
      (fun p : Fin 3 × Fin 3 => (⟨wa6 ^ (p.1 : ℕ) * wb6 ^ (p.2 : ℕ),
        mul_mem (pow_mem wa6_mem _) (pow_mem wb6_mem _)⟩ : Q6)) := by
    rintro ⟨x, hx⟩
    obtain ⟨i, j, rfl⟩ := mem_Q6 hx
    refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    apply Subtype.ext
    simp only
    rw [← pow_eq_pow_mod i wa6_cube, ← pow_eq_pow_mod j wb6_cube]
  have hle : Nat.card Q6 ≤ 9 := by
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa using this
  obtain ⟨k, hk⟩ := Q6_pGroup.exists_card_eq
  have hwaQ : wa6 ∈ Q6 := wa6_mem
  have hord : orderOf wa6 = 3 := orderOf_eq_prime wa6_cube wa6_ne_one
  have hz : Nat.card (Subgroup.zpowers wa6) = 3 := by rw [Nat.card_zpowers, hord]
  have hle' : Subgroup.zpowers wa6 ≤ Q6 := (Subgroup.zpowers_le).2 hwaQ
  have hfin : Finite Q6 := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hk2 : k ≤ 2 := by
    by_contra h
    push Not at h
    have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hk1 : 2 ≤ k := by
    by_contra h
    push Not at h
    have hle3 : Nat.card Q6 ≤ 3 := by
      rw [hk]
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 3 := by norm_num
    have heq : Subgroup.zpowers wa6 = Q6 :=
      Subgroup.eq_of_le_of_card_ge hle' (by rw [hz]; exact hle3)
    exact wb6_not_mem_zpowers (heq ▸ wb6_mem)
  have : k = 2 := le_antisymm hk2 hk1
  rw [hk, this]
  norm_num

theorem Q6_le_centralizer : Q6 ≤ Subgroup.centralizer ({ww6} : Set (WeylGroup Tag.E6)) := by
  rw [Q6, Subgroup.closure_le]
  intro x hx
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff.1 hg]
  rcases hx with rfl | rfl
  · exact wa6_ww6_comm.symm
  · exact wb6_ww6_comm.symm

theorem nine_dvd_card_centralizer_e6 :
    9 ∣ Nat.card (Subgroup.centralizer
      ({(coxeterSystem Tag.E6).wordProd e6TwoWord} : Set (WeylGroup Tag.E6))) := by
  have hfin : Finite (WeylGroup Tag.E6) :=
    inferInstance
  rw [← ww6_eq, ← Q6_card]
  exact Subgroup.card_dvd_of_le Q6_le_centralizer

end Centralizer

section Main


theorem card_twistedTorusOf_E6 {F : Type} [Field F] [Finite F] {L : Type} [Field L] [Algebra F L]
    [IsAlgClosure F L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F) :
    Nat.card (twistedTorusOf
        (canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd e6TwoWord))
        (Units.map (entrywiseHom Fr))) =
      (Nat.card F - 1) ^ 2 * (Nat.card F + 1) ^ 4 := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  rw [card_twistedTorusOf_gen Fr _ (wordProd_smul_eq_wordMat_mulVec Tag.E6 e6TwoWord) hFr
    (e := 2) two_ne_zero e6Two_pow, e6Two_charpoly]
  have hev : (([1, 1, 2, 2, 2, 2].map fun d => cyclotomic d ℤ).prod).eval
      (Nat.card F : ℤ) = ((Nat.card F - 1 : ℕ) : ℤ) ^ 2 * ((Nat.card F + 1 : ℕ) : ℤ) ^ 4 := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, cyclotomic_one,
      cyclotomic_two, eval_mul, eval_sub, eval_add, eval_X, eval_one]
    push_cast [Nat.cast_sub (by omega : 1 ≤ Nat.card F)]
    ring
  rw [hev, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_mul, Int.natAbs_natCast]

theorem finite_NFix_E6 {F : Type} [Field F] [Finite F] {L : Type} [Field L] [Algebra F L]
    [IsAlgClosure F L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F) :
    Finite (NFix
      (canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd e6TwoWord)) Fr) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hT := finite_twistedTorusOf_gen Fr _ (wordProd_smul_eq_wordMat_mulVec Tag.E6 e6TwoWord)
    hFr (e := 2) two_ne_zero e6Two_pow
  have hW : Finite (WeylGroup Tag.E6) := inferInstance
  refine Nat.finite_of_card_ne_zero ?_
  rw [card_NFix_gen Fr _ (by omega : 2 ≤ Nat.card F) hFr]
  exact mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

theorem v3_card_NFix_E6 {F : Type} [Field F] [Finite F] {L : Type} [Field L] [Algebra F L]
    [IsAlgClosure F L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F)
    (h3 : 3 ∣ Nat.card F + 1) :
    4 * padicValNat 3 (Nat.card F + 1) + 2 ≤ padicValNat 3 (Nat.card (NFix
      (canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd e6TwoWord)) Fr)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hne : Nat.card (NFix
      (canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd e6TwoWord)) Fr) ≠ 0 :=
    haveI := finite_NFix_E6 Fr hFr
    Nat.card_pos.ne'
  have hW : Finite (WeylGroup Tag.E6) := inferInstance
  rw [← padicValNat_dvd_iff_le hne, card_NFix_gen Fr _ (by omega : 2 ≤ Nat.card F) hFr,
    card_twistedTorusOf_E6 Fr hFr]
  have hT : 3 ^ (4 * padicValNat 3 (Nat.card F + 1)) ∣
      (Nat.card F - 1) ^ 2 * (Nat.card F + 1) ^ 4 := by
    refine Dvd.dvd.mul_left ?_ _
    rw [mul_comm, pow_mul]
    exact pow_dvd_pow_of_dvd pow_padicValNat_dvd 4
  have hC : 3 ^ 2 ∣ Nat.card (Subgroup.centralizer
      ({(coxeterSystem Tag.E6).wordProd e6TwoWord} : Set (WeylGroup Tag.E6))) := by
    simpa using nine_dvd_card_centralizer_e6
  rw [pow_add]
  exact Nat.mul_dvd_mul hT hC

theorem exists_E6_two_sylow {F : Type} [Field F] [Finite F] {L : Type} [Field L] [Algebra F L]
    [IsAlgClosure F L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F)
    (h3 : 3 ∣ Nat.card F + 1) :
    ∃ ι : NFix (canonicalRep (coxeterSystem Tag.E6) L
        ((coxeterSystem Tag.E6).wordProd e6TwoWord)) Fr →* ↥(adjointGroup Tag.E6 F),
      Function.Injective ι ∧
      ∃ P : Subgroup (NFix (canonicalRep (coxeterSystem Tag.E6) L
          ((coxeterSystem Tag.E6).wordProd e6TwoWord)) Fr),
        IsPGroup 3 P ∧ Nat.card P = 3 ^ (Nat.card ↥(adjointGroup Tag.E6 F)).factorization 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hfin := finite_NFix_E6 Fr hFr
  have hJfin : Finite ↥(adjointGroup Tag.E6 F) := generated_group_finite Tag.E6 F
  obtain ⟨ι, hι⟩ := exists_embedding_nfix
    ((coxeterSystem Tag.E6).wordProd e6TwoWord) Fr hFr
    (fun X _ hXC hXF => relIndex_dvd_E6_of_not_three_dvd F (by omega) L Fr hFr X hXC hXF) hfin
  refine ⟨ι, hι, ?_⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 (NFix (canonicalRep (coxeterSystem Tag.E6) L
      ((coxeterSystem Tag.E6).wordProd e6TwoWord)) Fr)) := inferInstance
  refine ⟨(S : Subgroup _), S.isPGroup', ?_⟩
  rw [Sylow.card_eq_multiplicity]
  congr 1
  have hJ : Nat.card ↥(adjointGroup Tag.E6 F) ≠ 0 := Nat.card_pos.ne'
  have hN : Nat.card (NFix (canonicalRep (coxeterSystem Tag.E6) L
      ((coxeterSystem Tag.E6).wordProd e6TwoWord)) Fr) ≠ 0 := Nat.card_pos.ne'
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three]
  have hlow := v3_card_NFix_E6 Fr hFr h3
  have hdvd : Nat.card (NFix (canonicalRep (coxeterSystem Tag.E6) L
      ((coxeterSystem Tag.E6).wordProd e6TwoWord)) Fr) ∣ Nat.card ↥(adjointGroup Tag.E6 F) :=
    Subgroup.card_dvd_of_injective ι hι
  have hup := (padicValNat_dvd_iff_le hJ).1
    ((pow_padicValNat_dvd (p := 3)).trans hdvd)
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, padicValNat_three_ordE6_neg hq h3]
    at hup ⊢
  omega

end Main

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
