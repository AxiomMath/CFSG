module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurEight
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurGoldAut
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurGoldGen
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidt
public import CFSG.Walter.J1Props.Elt

public section

namespace CFSG.ComponentClassification.WalterSchur

open CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt
open CFSG.QuasithinUnique.RankOneRecog

section Arithmetic

theorem three_pow_odd_mod_eight (m : ℕ) : 3 ^ (2 * m + 1) % 8 = 3 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

theorem ordRee_eq_eight_mul (m : ℕ) : ∃ u, Odd u ∧ ordRee (3 ^ (2 * m + 1)) = 8 * u := by
  have h8 : 3 ^ (2 * m + 1) % 8 = 3 := three_pow_odd_mod_eight m
  generalize 3 ^ (2 * m + 1) = q at h8 ⊢
  have hQ8 : q ^ 3 % 8 = 3 := by rw [Nat.pow_mod, h8]
  rw [show ordRee q = q ^ 3 * (q ^ 3 + 1) * (q - 1) from rfl]
  generalize q ^ 3 = Q at hQ8 ⊢
  obtain ⟨a, ha, ha2⟩ : ∃ a, Q + 1 = 4 * a ∧ a % 2 = 1 := ⟨(Q + 1) / 4, by omega, by omega⟩
  obtain ⟨b, hb, hb2⟩ : ∃ b, q - 1 = 2 * b ∧ b % 2 = 1 := ⟨(q - 1) / 2, by omega, by omega⟩
  refine ⟨Q * a * b, ?_, ?_⟩
  · exact ((Nat.odd_iff.mpr (by omega)).mul (Nat.odd_iff.mpr ha2)).mul (Nat.odd_iff.mpr hb2)
  · rw [ha, hb]
    ring

theorem factorization_two_eight_mul {u : ℕ} (hu : Odd u) : (8 * u).factorization 2 = 3 := by
  rw [Nat.factorization_mul (by norm_num) (by rintro rfl; simp at hu), Finsupp.add_apply,
    show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by
      rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hu)]

theorem three_pow_odd_mod_five (m : ℕ) :
    3 ^ (2 * m + 1) % 5 = 2 ∨ 3 ^ (2 * m + 1) % 5 = 3 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, pow_add, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem ordRee_ne_2520 (m : ℕ) : ordRee (3 ^ (2 * m + 1)) ≠ 2520 := by
  have h5 := three_pow_odd_mod_five m
  generalize 3 ^ (2 * m + 1) = q at h5 ⊢
  intro h
  have hdvd : 5 ∣ ordRee q := by rw [h]; norm_num
  rw [show ordRee q = q ^ 3 * (q ^ 3 + 1) * (q - 1) from rfl] at hdvd
  have hp : Nat.Prime 5 := by norm_num
  have hq3 : q ^ 3 % 5 = 3 ∨ q ^ 3 % 5 = 2 := by
    rcases h5 with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2 <;> omega
  · omega

theorem padicValNat_three_pow_mul {a B : ℕ} (hB : ¬ 3 ∣ B) : padicValNat 3 (3 ^ a * B) = a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB0 : B ≠ 0 := fun h0 => hB (h0 ▸ dvd_zero 3)
  rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) hB0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hB, add_zero]

theorem ree_size_lt {T Q r : ℤ} (hT : 27 ≤ T) (hQ : Q = T ^ 3) (hr : Q - 1 ≤ r) :
    2 * Q * (Q + 1) * (T - 1) < r * (r ^ 2 - 1) := by
  have hT2 : 27 ≤ T ^ 2 := by nlinarith
  have hQT : 27 * T ≤ Q := by rw [hQ]; nlinarith
  have hQ1 : 0 ≤ Q - 1 := by nlinarith
  have h1 : (Q - 1) * ((Q - 1) ^ 2 - 1) ≤ r * (r ^ 2 - 1) := by
    have hd : 0 ≤ r - (Q - 1) := by linarith
    have hs : 0 ≤ r ^ 2 + r * (Q - 1) + (Q - 1) ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg hd hs]
  have h2 : 2 * Q * (Q + 1) * (T - 1) < (Q - 1) * ((Q - 1) ^ 2 - 1) := by
    have e : (Q - 1) * ((Q - 1) ^ 2 - 1) = Q * ((Q - 1) * (Q - 2)) := by ring
    rw [e]
    have hQpos : 0 < Q := by nlinarith
    have h3 : 2 * (Q + 1) * (T - 1) < (Q - 1) * (Q - 2) := by nlinarith
    nlinarith
  linarith

theorem ordRee_ne_psl2 {m : ℕ} (hm : 1 ≤ m) {p k : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hk : 1 ≤ k) : ordRee (3 ^ (2 * m + 1)) ≠ p ^ k * ((p ^ k) ^ 2 - 1) / 2 := by
  intro h
  have hT27 : 27 ≤ 3 ^ (2 * m + 1) := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hT3 : 3 ∣ 3 ^ (2 * m + 1) := dvd_pow_self 3 (by omega)
  have hQ : (3 ^ (2 * m + 1)) ^ 3 = 3 ^ (3 * (2 * m + 1)) := by rw [← pow_mul, mul_comm]
  have hrodd : Odd (p ^ k) := hpodd.pow
  have hp3le : 3 ≤ p := by
    rcases Nat.lt_or_ge p 3 with hlt | hge
    · exfalso
      have h2 := hp.two_le
      interval_cases p
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
    · exact hge
  have hr3 : 3 ≤ p ^ k :=
    calc 3 ≤ p := hp3le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
  have hev : 2 ∣ p ^ k * ((p ^ k) ^ 2 - 1) :=
    Dvd.dvd.mul_left (Nat.Odd.sub_odd hrodd.pow odd_one).two_dvd _
  have heq : p ^ k * ((p ^ k) ^ 2 - 1) = 2 * ordRee (3 ^ (2 * m + 1)) := by
    rw [h, Nat.mul_div_cancel' hev]
  rw [show ordRee (3 ^ (2 * m + 1)) = (3 ^ (2 * m + 1)) ^ 3 *
    (((3 ^ (2 * m + 1)) ^ 3 + 1) * (3 ^ (2 * m + 1) - 1)) by rw [ordRee, mul_assoc]] at heq
  have hA3 : ¬ 3 ∣ 2 * (((3 ^ (2 * m + 1)) ^ 3 + 1) * (3 ^ (2 * m + 1) - 1)) := by
    have hT3' : 3 ∣ (3 ^ (2 * m + 1)) ^ 3 := dvd_pow hT3 (by norm_num)
    generalize (3 ^ (2 * m + 1)) ^ 3 = Q at hT3'
    generalize 3 ^ (2 * m + 1) = T at hT3 hT27
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with h1 | h1
    · omega
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2 <;> omega
  by_cases hp3 : p = 3
  ·
    subst hp3
    have hR3 : ¬ 3 ∣ (3 ^ k) ^ 2 - 1 := by
      have h1 : 3 ∣ (3 ^ k) ^ 2 := dvd_pow (dvd_pow_self 3 (by omega)) (by norm_num)
      have h2 : 1 ≤ (3 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    have hv : k = 3 * (2 * m + 1) := by
      have e : 2 * ((3 ^ (2 * m + 1)) ^ 3 *
          (((3 ^ (2 * m + 1)) ^ 3 + 1) * (3 ^ (2 * m + 1) - 1))) =
          3 ^ (3 * (2 * m + 1)) * (2 * (((3 ^ (2 * m + 1)) ^ 3 + 1) * (3 ^ (2 * m + 1) - 1))) := by
        rw [← hQ]; ring
      have h1 := congrArg (padicValNat 3) heq
      rw [e, padicValNat_three_pow_mul hR3, padicValNat_three_pow_mul hA3] at h1
      exact h1
    rw [hv, ← hQ] at heq
    generalize hTdef : 3 ^ (2 * m + 1) = T at heq hT27
    have hT1 : 1 ≤ T := by omega
    have hQ1 : 1 ≤ (T ^ 3) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    zify [hT1, hQ1] at heq
    have hTz : (27 : ℤ) ≤ T := by exact_mod_cast hT27
    have hpos : (0 : ℤ) < (T : ℤ) ^ 3 := by positivity
    have h1 : ((T : ℤ) ^ 3) ^ 2 - 1 = 2 * (((T : ℤ) ^ 3 + 1) * ((T : ℤ) - 1)) :=
      mul_left_cancel₀ (ne_of_gt hpos) (heq.trans (by ring))
    have h2 : (T : ℤ) ^ 3 - 1 = 2 * ((T : ℤ) - 1) := by
      have h3 : ((T : ℤ) ^ 3 + 1) * ((T : ℤ) ^ 3 - 1) =
          ((T : ℤ) ^ 3 + 1) * (2 * ((T : ℤ) - 1)) :=
        calc ((T : ℤ) ^ 3 + 1) * ((T : ℤ) ^ 3 - 1) = ((T : ℤ) ^ 3) ^ 2 - 1 := by ring
          _ = 2 * (((T : ℤ) ^ 3 + 1) * ((T : ℤ) - 1)) := h1
          _ = ((T : ℤ) ^ 3 + 1) * (2 * ((T : ℤ) - 1)) := by ring
      exact mul_left_cancel₀ (by positivity) h3
    have hT2 : (27 : ℤ) ≤ (T : ℤ) ^ 2 := by nlinarith
    have h4 : 27 * (T : ℤ) ≤ (T : ℤ) ^ 3 := by nlinarith
    linarith [h2, h4, hTz]
  ·
    have hr3' : ¬ 3 ∣ p ^ k := fun h3 => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three
      hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)).symm
    have hcop : ∀ n : ℕ, ¬ 3 ∣ n → Nat.Coprime ((3 ^ (2 * m + 1)) ^ 3) n := fun n hn => by
      rw [hQ]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn)
    have hdvd : (3 ^ (2 * m + 1)) ^ 3 ∣ p ^ k * ((p ^ k) ^ 2 - 1) := by
      rw [heq]
      exact Dvd.dvd.mul_left (Dvd.intro _ rfl) 2
    have hdvd2 : (3 ^ (2 * m + 1)) ^ 3 ∣ (p ^ k - 1) * (p ^ k + 1) := by
      have h1 := (hcop _ hr3').dvd_of_dvd_mul_left hdvd
      rwa [show (p ^ k) ^ 2 - 1 = (p ^ k - 1) * (p ^ k + 1) by
        rw [mul_comm, ← Nat.sq_sub_sq, one_pow]] at h1
    have hge : (3 ^ (2 * m + 1)) ^ 3 ≤ p ^ k + 1 := by
      by_cases h3 : 3 ∣ p ^ k - 1
      · have h3' : ¬ 3 ∣ p ^ k + 1 := by omega
        have h1 := (hcop _ h3').dvd_of_dvd_mul_right hdvd2
        have := Nat.le_of_dvd (by omega) h1
        omega
      · exact Nat.le_of_dvd (by omega) ((hcop _ h3).dvd_of_dvd_mul_left hdvd2)
    generalize hTdef : 3 ^ (2 * m + 1) = T at heq hge hT27
    generalize hrdef : p ^ k = r at heq hge hr3
    have hT1 : 1 ≤ T := by omega
    have hr1 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hT1, hr1] at heq
    have hlt := ree_size_lt (T := (T : ℤ)) (Q := (T : ℤ) ^ 3) (r := (r : ℤ))
      (by exact_mod_cast hT27) rfl (by linarith [hge])
    nlinarith [heq, hlt]

theorem j1_ne_psl2 (r : ℕ) : (175560 : ℕ) ≠ r * (r ^ 2 - 1) / 2 := by
  intro h
  have h1 : 351120 ≤ r * (r ^ 2 - 1) := by omega
  have h2 : r * (r ^ 2 - 1) ≤ 351121 := by omega
  rcases le_or_gt r 70 with hr | hr
  · have : r * (r ^ 2 - 1) ≤ 70 * 70 ^ 2 :=
      calc r * (r ^ 2 - 1) ≤ r * r ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ 70 * 70 ^ 2 := Nat.mul_le_mul hr (Nat.pow_le_pow_left hr 2)
    omega
  · have : 71 * (71 ^ 2 - 1) ≤ r * (r ^ 2 - 1) :=
      Nat.mul_le_mul hr (Nat.sub_le_sub_right (Nat.pow_le_pow_left hr 2) 1)
    omega

end Arithmetic

section Sylow

variable {Y : Type} [Group Y] [Finite Y] {X : Subgroup Y}

theorem goldschmidtJ1_eq_walterJ1 : goldschmidtJ1 = walterJ1 := rfl

theorem card_of_reeJ1 (hX : IsSimpleGroup X)
    (hType : (∃ m : ℕ, 1 ≤ m ∧ Nat.card (X ⧸ Subgroup.center X) = ordRee (3 ^ (2 * m + 1))) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* goldschmidtJ1)) :
    Subgroup.center X = ⊥ ∧
      ((∃ m : ℕ, 1 ≤ m ∧ Nat.card X = ordRee (3 ^ (2 * m + 1))) ∨ Nat.card X = 175560) := by
  have : IsSimpleGroup X := hX
  have hnt : Nontrivial (X ⧸ Subgroup.center X) := by
    rcases hType with ⟨m, -, hm⟩ | he
    · apply Finite.one_lt_card_iff_nontrivial.mp
      rw [hm]
      obtain ⟨u, hu, hu8⟩ := ordRee_eq_eight_mul m
      rw [hu8]
      have := hu.pos
      omega
    · obtain ⟨e⟩ := he
      apply Finite.one_lt_card_iff_nontrivial.mp
      rw [Nat.card_congr e.toEquiv, goldschmidtJ1_eq_walterJ1, Walter.J1Props.card_walterJ1]
      norm_num
  have hZ := center_eq_bot_of_nontrivial hnt
  refine ⟨hZ, ?_⟩
  have hcard : Nat.card X = Nat.card (X ⧸ Subgroup.center X) := by
    rw [hZ]
    exact (Nat.card_congr (QuotientGroup.quotientBot (G := X)).toEquiv).symm
  rcases hType with ⟨m, hm1, hm⟩ | he
  · exact Or.inl ⟨m, hm1, hcard.trans hm⟩
  · obtain ⟨e⟩ := he
    right
    rw [hcard, Nat.card_congr e.toEquiv, goldschmidtJ1_eq_walterJ1,
      Walter.J1Props.card_walterJ1]

theorem sylow_elementary_of_reeJ1 (hX : IsSimpleGroup X)
    (hType : (∃ m : ℕ, 1 ≤ m ∧ Nat.card (X ⧸ Subgroup.center X) = ordRee (3 ^ (2 * m + 1))) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* goldschmidtJ1)) (Q : Sylow 2 X) :
    (∃ a b : X, a * b ≠ b * a) ∧ Nat.card (Q : Subgroup X) = 8 ∧
      IsMulCommutative (Q : Subgroup X) ∧ ∀ q ∈ (Q : Subgroup X), q * q = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup X := hX
  obtain ⟨hZ, hcard⟩ := card_of_reeJ1 hX hType
  have hnonab : ∃ a b : X, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : Subgroup.center X = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun g => h g x
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    apply hab
    have ha : a ∈ Subgroup.center X := htop ▸ Subgroup.mem_top a
    have hb : b ∈ Subgroup.center X := htop ▸ Subgroup.mem_top b
    rw [hZ, Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have hdata : (∃ u, Odd u ∧ Nat.card X = 8 * u) ∧ Nat.card X ≠ 2520 ∧
      ∀ p k : ℕ, p.Prime → Odd p → 1 ≤ k → Nat.card X ≠ p ^ k * ((p ^ k) ^ 2 - 1) / 2 := by
    rcases hcard with ⟨m, hm1, hm⟩ | hJ
    · rw [hm]
      exact ⟨ordRee_eq_eight_mul m, ordRee_ne_2520 m, fun p k hp hpodd hk =>
        ordRee_ne_psl2 hm1 hp hpodd hk⟩
    · rw [hJ]
      exact ⟨⟨21945, by decide, by norm_num⟩, by norm_num, fun p k _ _ _ => j1_ne_psl2 _⟩
  obtain ⟨⟨u, hu, hu8⟩, hA7, hL2⟩ := hdata
  have hQ8 : Nat.card (Q : Subgroup X) = 8 := by
    rw [Q.card_eq_multiplicity, hu8, factorization_two_eight_mul hu]
    norm_num
  have hQc := isMulCommutative_of_card_eight hnonab Q hQ8 hA7 hL2
  exact ⟨hnonab, hQ8, hQc, mul_self_eq_one_of_abelian_card_eight hnonab Q hQc hQ8⟩

omit [Finite Y] in
theorem sylow_elementary_map {P : Subgroup Y} {Q : Sylow 2 X}
    (hQ : (Q : Subgroup X).map X.subtype = P) (hQc : IsMulCommutative (Q : Subgroup X))
    (hQ2 : ∀ q ∈ (Q : Subgroup X), q * q = 1) :
    (∀ p ∈ P, p * p = 1) ∧ ∀ p ∈ P, ∀ p' ∈ P, p * p' = p' * p := by
  subst hQ
  constructor
  · rintro _ ⟨q, hq, rfl⟩
    exact congrArg Subtype.val (hQ2 q hq)
  · rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩
    exact congrArg Subtype.val (congrArg Subtype.val (hQc.is_comm.comm ⟨q, hq⟩ ⟨q', hq'⟩))

end Sylow

theorem goldschmidtTypeAutomorphismsReeJ1_holds : GoldschmidtTypeAutomorphismsReeJ1 := by
  intro Y _ _ X P E hX hType hP hE hEX _ hEcent _
  obtain ⟨Q, hQ⟩ := hP
  obtain ⟨hnonab, -, hQc, hQ2⟩ := sylow_elementary_of_reeJ1 hX hType Q
  obtain ⟨hP2, hPc⟩ := sylow_elementary_map hQ hQc hQ2
  exact card_le_omegaOne_of_elementary hX hnonab ⟨Q, hQ⟩ hP2 hPc hE hEX hEcent

theorem goldschmidtTypeGenerationReeJ1_holds : GoldschmidtTypeGenerationReeJ1 := by
  intro Y _ _ X P hX hType hP
  classical
  obtain ⟨Q, hQ⟩ := hP
  obtain ⟨-, hQ8, hQc, hQ2⟩ := sylow_elementary_of_reeJ1 hX hType Q
  obtain ⟨-, hPc⟩ := sylow_elementary_map hQ hQc hQ2
  have : Fintype (Q : Subgroup X) := Fintype.ofFinite _
  obtain ⟨a, b, c, hab, hac, hbc⟩ := (Fintype.two_lt_card_iff (α := (Q : Subgroup X))).mp (by
    rw [← Nat.card_eq_fintype_card, hQ8]; norm_num)
  obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v : (Q : Subgroup X), u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
    by_cases ha : a = 1
    · exact ⟨b, c, fun h => hab (ha.trans h.symm), fun h => hac (ha.trans h.symm), hbc⟩
    by_cases hb : b = 1
    · exact ⟨a, c, ha, fun h => hbc (hb.trans h.symm), hac⟩
    · exact ⟨a, b, ha, hb, hab⟩
  have hord : ∀ w : (Q : Subgroup X), w ≠ 1 → orderOf ((w : X) : Y) = 2 := by
    intro w hw
    apply orderOf_eq_prime
    · rw [sq]
      exact congrArg Subtype.val (hQ2 w w.2)
    · intro h
      exact hw (Subtype.ext (Subtype.ext h))
  have hmem : ∀ w : (Q : Subgroup X), ((w : X) : Y) ∈ P := fun w => hQ ▸ ⟨w, w.2, rfl⟩
  exact le_iSup_centralizer_or_isBenderType hX ⟨Q, hQ⟩ hPc (hmem u) (hmem v) (hord u hu)
    (hord v hv) (fun h => huv (Subtype.ext (Subtype.ext h)))

theorem theorem3KnownGroupFacts_holds : Theorem3KnownGroupFacts :=
  theorem3KnownGroupFacts_of_reeJ1 goldschmidtTypeAutomorphismsReeJ1_holds
    goldschmidtTypeGenerationReeJ1_holds

end CFSG.ComponentClassification.WalterSchur
