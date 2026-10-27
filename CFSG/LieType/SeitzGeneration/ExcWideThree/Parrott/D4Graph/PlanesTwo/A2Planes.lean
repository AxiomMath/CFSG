module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.A2Gen
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.A2Card
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.Defs

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph


@[expose] def pW (a b e : ℕ) : List ℕ :=
  (List.replicate a rW).flatten ++ (List.replicate b dW).flatten ++ (List.replicate e y0W).flatten

@[expose] def triples : List (Fin 3 × Fin 3 × Fin 3) :=
  List.product (List.finRange 3) (List.product (List.finRange 3) (List.finRange 3))

theorem mem_triples (t : Fin 3 × Fin 3 × Fin 3) : t ∈ triples := by
  rcases t with ⟨a, b, c⟩
  exact List.mem_product.2 ⟨List.mem_finRange a,
    List.mem_product.2 ⟨List.mem_finRange b, List.mem_finRange c⟩⟩

theorem pW_nodup : (triples.map fun t => wordN (pW t.1 t.2.1 t.2.2)).Nodup := by
  decide +kernel

variable {K : Type} [Field K] [Finite K]

theorem wordG_replicate (n : ℕ) (w : List ℕ) :
    wordG K (List.replicate n w).flatten = wordG K w ^ n := by
  induction n with
  | zero => simp [wordG_nil]
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, wordG_append, ih, pow_succ']

theorem wordG_pW (a b e : ℕ) :
    wordG K (pW a b e) = wordG K rW ^ a * wordG K dW ^ b * wordG K y0W ^ e := by
  rw [pW, wordG_append, wordG_append, wordG_replicate, wordG_replicate, wordG_replicate]

theorem letters_replicate {w : List ℕ} (hw : Letters w) (n : ℕ) :
    Letters (List.replicate n w).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons]; exact letters_append hw ih

theorem letters_pW (a b e : ℕ) : Letters (pW a b e) :=
  letters_append
    (letters_append (letters_replicate (by decide) a) (letters_replicate (by decide) b))
    (letters_replicate (by decide) e)

variable (K) in
@[expose] noncomputable def subP : Subgroup ↥(adjointGroup Tag.D4 K) :=
  Subgroup.closure {wordG K dW, wordG K rW, wordG K y0W}

theorem subP_le (hK : Nat.card K = 2) : subP K ≤ fixedSubgroup (gammaP K (uSL 1 * vSL 1)) := by
  rw [subP, Subgroup.closure_le]
  rintro g (rfl | rfl | rfl)
  exacts [d_mem hK, r_mem hK, y₀_mem hK]

theorem pow_mod_three {G : Type*} [Group G] {g : G} (h : g ^ 3 = 1) (a : ℕ) :
    g ^ a = g ^ (a % 3) := by
  conv_lhs => rw [← Nat.mod_add_div a 3, pow_add, pow_mul, h, one_pow, mul_one]

theorem exists_pW_of_mem (hK : Nat.card K = 2) {g : ↥(adjointGroup Tag.D4 K)} (hg : g ∈ subP K) :
    ∃ a b e : ℕ, a < 3 ∧ b < 3 ∧ e < 3 ∧ g = wordG K (pW a b e) := by
  set r := wordG K rW
  set d := wordG K dW
  set y := wordG K y0W
  have hyr : y * r = r * d * y := by
    have := y₀_conj_r hK
    rwa [mul_inv_eq_iff_eq_mul] at this
  have hdy : Commute d y := d_comm_y₀ hK
  have hdr : Commute d r := d_comm_r hK
  have hye : ∀ e : ℕ, y ^ e * r = r * d ^ e * y ^ e := by
    intro e
    induction e with
    | zero => simp
    | succ e ih =>
      calc y ^ (e + 1) * r = y ^ e * (y * r) := by rw [pow_succ, mul_assoc]
        _ = (y ^ e * r) * d * y := by rw [hyr]; group
        _ = r * d ^ e * (y ^ e * d) * y := by rw [ih]; group
        _ = r * d ^ e * (d * y ^ e) * y := by rw [((hdy.pow_right e).symm).eq]
        _ = r * d ^ (e + 1) * y ^ (e + 1) := by group
  set Q : ↥(adjointGroup Tag.D4 K) → Prop := fun x => ∃ a b e : ℕ, x = r ^ a * d ^ b * y ^ e
  have step : ∀ x z, z ∈ ({d, r, y} : Set ↥(adjointGroup Tag.D4 K)) → Q x → Q (x * z) := by
    rintro x z (rfl | rfl | rfl) ⟨a, b, e, rfl⟩
    · refine ⟨a, b + 1, e, ?_⟩
      calc r ^ a * d ^ b * y ^ e * d = r ^ a * d ^ b * (y ^ e * d) := by group
        _ = r ^ a * d ^ b * (d * y ^ e) := by rw [((hdy.pow_right e).symm).eq]
        _ = r ^ a * d ^ (b + 1) * y ^ e := by group
    · refine ⟨a + 1, b + e, e, ?_⟩
      calc r ^ a * d ^ b * y ^ e * r = r ^ a * d ^ b * (y ^ e * r) := by group
        _ = r ^ a * (d ^ b * r) * d ^ e * y ^ e := by rw [hye]; group
        _ = r ^ a * (r * d ^ b) * d ^ e * y ^ e := by rw [(hdr.pow_left b).eq]
        _ = r ^ (a + 1) * d ^ (b + e) * y ^ e := by group
    · exact ⟨a, b, e + 1, by group⟩
  have hinv : ∀ z ∈ ({d, r, y} : Set ↥(adjointGroup Tag.D4 K)), z⁻¹ = z * z := by
    rintro z (rfl | rfl | rfl)
    · rw [inv_eq_iff_mul_eq_one, ← pow_three]; exact d_pow_three hK
    · rw [inv_eq_iff_mul_eq_one, ← pow_three]; exact r_pow_three hK
    · rw [inv_eq_iff_mul_eq_one, ← pow_three]; exact y₀_pow_three hK
  have hQ : Q g := by
    refine Subgroup.closure_induction_right (p := fun x _ => Q x) ⟨0, 0, 0, by simp⟩
      (fun x _ z hz hx => step x z hz hx) (fun x _ z hz hx => ?_) hg
    rw [hinv z hz, ← mul_assoc]
    exact step _ z hz (step x z hz hx)
  obtain ⟨a, b, e, rfl⟩ := hQ
  refine ⟨a % 3, b % 3, e % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), ?_⟩
  rw [wordG_pW, pow_mod_three (r_pow_three hK) a, pow_mod_three (d_pow_three hK) b,
    pow_mod_three (y₀_pow_three hK) e]

theorem wordG_pW_mem (a b e : ℕ) : wordG K (pW a b e) ∈ subP K := by
  rw [wordG_pW]
  refine (subP K).mul_mem ((subP K).mul_mem ((subP K).pow_mem ?_ a) ((subP K).pow_mem ?_ b))
    ((subP K).pow_mem ?_ e)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inr rfl))

theorem card_subP (hK : Nat.card K = 2) : Nat.card (subP K) = 27 := by
  have h2 := two_eq_zero_of_card_two' hK
  let f : Fin 3 × Fin 3 × Fin 3 → subP K := fun t =>
    ⟨wordG K (pW t.1 t.2.1 t.2.2), wordG_pW_mem _ _ _⟩
  have hf : Function.Bijective f := by
    refine ⟨fun t t' h => ?_, fun g => ?_⟩
    · have e := congrArg Subtype.val h
      have e' := wordN_eq_of_wordG_eq h2 (rt_lt_of_mem (letters_pW _ _ _))
        (rt_lt_of_mem (letters_pW _ _ _)) e
      exact List.inj_on_of_nodup_map pW_nodup (mem_triples t) (mem_triples t') e'
    · obtain ⟨a, b, e, ha, hb, he, hg⟩ := exists_pW_of_mem hK g.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨e, he⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp

theorem factorization_three_eq {n : ℕ} (h27 : 27 ∣ n) (hn : n ∣ 12096) : n.factorization 3 = 3 := by
  have hn0 : n ≠ 0 := fun h => by rw [h] at hn; norm_num at hn
  have h1 : 3 ≤ n.factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hn0).1 (by simpa using h27)
  have h2 : n.factorization 3 ≤ (12096 : ℕ).factorization 3 :=
    (Nat.factorization_le_iff_dvd hn0 (by norm_num)).2 hn 3
  have h3 : (12096 : ℕ).factorization 3 = 3 := by
    have e : (12096 : ℕ) = 3 ^ 3 * 448 := by norm_num
    rw [e, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  omega

theorem exists_conj_mem_subP (hK : Nat.card K = 2) {x : ↥(adjointGroup Tag.D4 K)}
    (hx : gammaP K (uSL 1 * vSL 1) x = x) (hx3 : x ^ 3 = 1) :
    ∃ c : ↥(adjointGroup Tag.D4 K), gammaP K (uSL 1 * vSL 1) c = c ∧ c * x * c⁻¹ ∈ subP K := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (Module.End K (RootModule Tag.D4 K)) := Module.finite_of_finite K
  have : Finite ↥(adjointGroup Tag.D4 K) := inferInstance
  set C := fixedSubgroup (gammaP K (uSL 1 * vSL 1))
  set P' := (subP K).subgroupOf C
  have hP' : Nat.card P' = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (subP_le hK)).toEquiv, card_subP hK]
  have hdvd : Nat.card C ∣ 12096 := cardFixGammaPTwo_holds K hK
  have h27 : 27 ∣ Nat.card C := by rw [← hP']; exact Subgroup.card_subgroup_dvd_card P'
  have hfac := factorization_three_eq h27 hdvd
  let S : Sylow 3 C := Sylow.ofCard P' (by rw [hP', hfac]; norm_num)
  set xC : C := ⟨x, hx⟩
  have hE : IsPGroup 3 (Subgroup.zpowers xC) := by
    refine IsPGroup.of_card (n := if xC = 1 then 0 else 1) ?_
    rw [Nat.card_zpowers]
    have hxC3 : xC ^ 3 = 1 := Subtype.ext (by simp [xC, hx3])
    split_ifs with h1
    · rw [h1, orderOf_one, pow_zero]
    · rw [pow_one]
      exact orderOf_eq_prime hxC3 h1
  obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.exists_conj_le_sylow' S _ hE
  have hmem : (MulAut.conj y).toMonoidHom xC ∈ (S : Subgroup C) :=
    hy (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers xC))
  refine ⟨(y : ↥(adjointGroup Tag.D4 K)), y.2, ?_⟩
  have h' : y * xC * y⁻¹ ∈ P' := hmem
  rw [Subgroup.mem_subgroupOf] at h'
  simpa [xC] using h'

@[expose] def conjWords : List (List ℕ) :=
  [[], rW, rW.reverse, qW, qW ++ y0W, qW ++ y0W.reverse]

@[expose] def repWords : List (List ℕ) :=
  [dW, y0W, rW ++ y0W, rW ++ y0W ++ y0W]

@[expose] def redTab : List (ℕ × ℕ × Bool) :=
  [(0, 0, false), (0, 1, false), (0, 1, true), (0, 0, false), (1, 1, false), (2, 1, true),
    (0, 0, true), (2, 1, false), (1, 1, true), (3, 0, true), (0, 2, false), (0, 3, false),
    (5, 0, true), (1, 2, false), (2, 3, false), (4, 0, true), (2, 2, false), (1, 3, false),
    (3, 0, false), (1, 3, true), (1, 2, true), (4, 0, false), (2, 3, true), (0, 2, true),
    (5, 0, false), (0, 3, true), (2, 2, true)]

@[expose] def redCheck (a b e : ℕ) : Bool :=
  (a == 0 && b == 0 && e == 0) ||
    (decide ((redTab.getD (9 * a + 3 * b + e) (0, 0, false)).1 < 6) &&
      decide ((redTab.getD (9 * a + 3 * b + e) (0, 0, false)).2.1 < 4) &&
      (wordN (conjWords.getD (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).1 [] ++ pW a b e ++
          (conjWords.getD (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).1 []).reverse) ==
        wordN (if (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).2.2 then
          repWords.getD (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).2.1 [] ++
            repWords.getD (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).2.1 []
          else repWords.getD (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).2.1 [])))

theorem redCheck_all : ∀ a < 3, ∀ b < 3, ∀ e < 3, redCheck a b e = true := by
  decide +kernel

theorem redTab_spec {a b e : ℕ} (ha : a < 3) (hb : b < 3) (he : e < 3)
    (hne : (a, b, e) ≠ (0, 0, 0)) :
    (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).1 < 6 ∧
    (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).2.1 < 4 ∧
    wordN (conjWords.getD (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).1 [] ++ pW a b e ++
        (conjWords.getD (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).1 []).reverse) =
      wordN (if (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).2.2 then
        repWords.getD (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).2.1 [] ++
          repWords.getD (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).2.1 []
        else repWords.getD (redTab.getD (9 * a + 3 * b + e) (0, 0, false)).2.1 []) := by
  have h := redCheck_all a ha b hb e he
  have h0 : (a == 0 && b == 0 && e == 0) = false := by
    rw [Bool.eq_false_iff]
    intro h'
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    exact hne (by rw [h'.1.1, h'.1.2, h'.2])
  rw [redCheck, h0, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem conjWords_mem (hK : Nat.card K = 2) :
    ∀ c < 6, wordG K (conjWords.getD c []) ∈ fixedSubgroup (gammaP K (uSL 1 * vSL 1)) := by
  have h2 := two_eq_zero_of_card_two' hK
  intro c hc
  interval_cases c
  · exact Subgroup.one_mem _
  · exact r_mem hK
  · show wordG K rW.reverse ∈ _
    rw [← wordG_inv h2]
    exact Subgroup.inv_mem _ (r_mem hK)
  · exact q_mem hK
  · show wordG K (qW ++ y0W) ∈ _
    rw [wordG_append]
    exact Subgroup.mul_mem _ (q_mem hK) (y₀_mem hK)
  · show wordG K (qW ++ y0W.reverse) ∈ _
    rw [wordG_append, ← wordG_inv h2]
    exact Subgroup.mul_mem _ (q_mem hK) (Subgroup.inv_mem _ (y₀_mem hK))

theorem repWords_pow_three (hK : Nat.card K = 2) :
    ∀ ρ < 4, wordG K (repWords.getD ρ []) ^ 3 = 1 := by
  have h2 := two_eq_zero_of_card_two' hK
  intro ρ hρ
  interval_cases ρ
  · exact d_pow_three hK
  · exact y₀_pow_three hK
  · show wordG K (rW ++ y0W) ^ 3 = 1
    rw [pow_succ, pow_two, ← wordG_append, ← wordG_append, ← wordG_nil]
    exact wordG_eq h2 (by decide) (by decide) (by decide +kernel)
  · show wordG K (rW ++ y0W ++ y0W) ^ 3 = 1
    rw [pow_succ, pow_two, ← wordG_append, ← wordG_append, ← wordG_nil]
    exact wordG_eq h2 (by decide) (by decide) (by decide +kernel)

theorem repWords_gen (hK : Nat.card K = 2) : ∀ ρ < 4,
    Subgroup.closure (quadSet (wordG K (repWords.getD ρ [])) (gammaP K (uSL 1 * vSL 1))) = ⊤ := by
  intro ρ hρ
  interval_cases ρ
  · exact closure_quadSet_d hK
  · exact closure_quadSet_y₀
  · exact closure_quadSet_ry₀ hK
  · exact closure_quadSet_ry₀sq hK

theorem closure_quadSet_pW (hK : Nat.card K = 2) {a b e : ℕ} (ha : a < 3) (hb : b < 3)
    (he : e < 3) (hne : (a, b, e) ≠ (0, 0, 0)) :
    Subgroup.closure (quadSet (wordG K (pW a b e)) (gammaP K (uSL 1 * vSL 1))) = ⊤ := by
  have h2 := two_eq_zero_of_card_two' hK
  obtain ⟨hc6, hr4, hid⟩ := redTab_spec ha hb he hne
  set t := redTab.getD (9 * a + 3 * b + e) (0, 0, false)
  set c := conjWords.getD t.1 []
  set ρ := repWords.getD t.2.1 []
  have hcl : Letters c := by
    show Letters (conjWords.getD t.1 [])
    interval_cases h : t.1 <;> decide
  have hρl : Letters ρ := by
    show Letters (repWords.getD t.2.1 [])
    interval_cases h : t.2.1 <;> decide
  refine closure_quadSet_eq_top_of_conj_fixed (c := wordG K c) (conjWords_mem hK _ hc6) ?_
  rw [conj_wordG h2]
  cases hsq : t.2.2
  · rw [hsq] at hid
    rw [wordG_eq h2 (letters_append (letters_append hcl (letters_pW a b e)) (letters_reverse hcl))
      hρl hid]
    exact repWords_gen hK _ hr4
  · rw [hsq] at hid
    rw [wordG_eq h2 (letters_append (letters_append hcl (letters_pW a b e)) (letters_reverse hcl))
      (letters_append hρl hρl) hid, wordG_append, ← pow_two,
      quadSet_sq (repWords_pow_three hK _ hr4)]
    exact repWords_gen hK _ hr4

theorem quadGenTwoA2_holds : QuadGenTwoA2 := by
  intro K _ _ hK x hx3 hx1 hfix
  obtain ⟨c, hc, hcP⟩ := exists_conj_mem_subP hK hfix hx3
  obtain ⟨a, b, e, ha, hb, he, hEq⟩ := exists_pW_of_mem hK hcP
  refine closure_quadSet_eq_top_of_conj_fixed hc ?_
  rw [hEq]
  refine closure_quadSet_pW hK ha hb he ?_
  rintro ⟨rfl, rfl, rfl⟩
  apply hx1
  have h1 : c * x * c⁻¹ = 1 := by rw [hEq]; rfl
  calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
    _ = 1 := by rw [h1]; group

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo
