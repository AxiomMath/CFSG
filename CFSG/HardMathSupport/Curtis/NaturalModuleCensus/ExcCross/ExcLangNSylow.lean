module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.CubeCentralizer
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E78Sylow
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNFix
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNTorus
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Two

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Curtis.UnitaryLevi CFSG.RankThree.Lattice

section Valuation

private lemma padicValNat_three_one' : padicValNat 3 1 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)

private lemma padicValNat_three_four : padicValNat 3 4 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by norm_num)

private lemma padicValNat_three_five : padicValNat 3 5 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by norm_num)

private lemma padicValNat_three_seven : padicValNat 3 7 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by norm_num)

private lemma padicValNat_three_ten' : padicValNat 3 10 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by norm_num)

private lemma padicValNat_three_three : padicValNat 3 3 = 1 := padicValNat_self

private lemma padicValNat_three_nine : padicValNat 3 9 = 2 := by
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num, padicValNat.prime_pow]

private lemma padicValNat_three_six' : padicValNat 3 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]

private lemma padicValNat_three_twelve' : padicValNat 3 12 = 1 := by
  rw [show (12 : ℕ) = 3 * 4 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self, padicValNat_three_four]

private lemma padicValNat_three_fifteen : padicValNat 3 15 = 1 := by
  rw [show (15 : ℕ) = 3 * 5 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self, padicValNat_three_five]

private lemma sq_sub_one_eq {q : ℕ} (hq : 1 < q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1, hq.le]
  ring

theorem padicValNat_three_sq_sub_one {q : ℕ} (hq : 1 < q) (h3 : 3 ∣ q + 1) :
    padicValNat 3 (q ^ 2 - 1) = padicValNat 3 (q + 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [sq_sub_one_eq hq, padicValNat.mul (by omega) (by omega),
    padicValNat.eq_zero_of_not_dvd (p := 3) (n := q - 1) (by omega), zero_add]

theorem padicValNat_three_pow_sub_one_neg {q e : ℕ} (hq : 1 < q) (h3 : 3 ∣ q + 1) (he : e ≠ 0)
    (h2 : 2 ∣ e) :
    padicValNat 3 (q ^ e - 1) = padicValNat 3 (q + 1) + padicValNat 3 (e / 2) := by
  obtain ⟨m, rfl⟩ := h2
  have hm : m ≠ 0 := by omega
  have hQ : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hq
  have h3Q : 3 ∣ q ^ 2 - 1 := by
    rw [sq_sub_one_eq hq]
    exact Dvd.dvd.mul_left h3 _
  rw [pow_mul, padicValNat_three_pow_sub_one hQ h3Q hm, padicValNat_three_sq_sub_one hq h3]
  simp

theorem padicValNat_three_ordE7_neg {q : ℕ} (hq : 1 < q) (h3 : 3 ∣ q + 1) :
    padicValNat 3 (CFSG.Open.ordE7 q) = 7 * padicValNat 3 (q + 1) + 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnq : ¬ 3 ∣ q := by omega
  have sub_one_pos' : ∀ {n : ℕ}, n ≠ 0 → 0 < q ^ n - 1 := fun hn =>
    Nat.sub_pos_of_lt (Nat.one_lt_pow hn hq)
  have h18 := sub_one_pos' (n := 18) (by norm_num)
  have h14 := sub_one_pos' (n := 14) (by norm_num)
  have h12 := sub_one_pos' (n := 12) (by norm_num)
  have h10 := sub_one_pos' (n := 10) (by norm_num)
  have h8 := sub_one_pos' (n := 8) (by norm_num)
  have h6 := sub_one_pos' (n := 6) (by norm_num)
  have h2 := sub_one_pos' (n := 2) (by norm_num)
  have hX : q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 2 - 1) ≠ 0 := by positivity
  have hdvd : Nat.gcd 2 (q - 1) ∣ q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
      (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    have := Nat.sub_dvd_pow_sub_pow q 1 2
    rw [one_pow] at this
    exact (Nat.gcd_dvd_right 2 (q - 1)).trans this
  have hg : padicValNat 3 (Nat.gcd 2 (q - 1)) = 0 :=
    padicValNat.eq_zero_of_not_dvd fun h => by
      have := h.trans (Nat.gcd_dvd_left 2 (q - 1))
      omega
  have hgpos : Nat.gcd 2 (q - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have hmul := Nat.div_mul_cancel hdvd
  have hne : (q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) / Nat.gcd 2 (q - 1) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact hX hmul.symm
  have key := congrArg (padicValNat 3) hmul
  rw [padicValNat.mul hne hgpos, hg, add_zero] at key
  unfold CFSG.Open.ordE7
  rw [key, padicValNat.mul (by positivity) h2.ne', padicValNat.mul (by positivity) h6.ne',
    padicValNat.mul (by positivity) h8.ne', padicValNat.mul (by positivity) h10.ne',
    padicValNat.mul (by positivity) h12.ne', padicValNat.mul (by positivity) h14.ne',
    padicValNat.mul (by positivity) h18.ne',
    padicValNat.pow q 63, padicValNat.eq_zero_of_not_dvd hnq,
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 18 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 14 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 12 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 10 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 8 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 6 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 2 ≠ 0) (by norm_num)]
  simp only [Nat.reduceDiv]
  rw [padicValNat_three_nine, padicValNat_three_seven, padicValNat_three_six',
    padicValNat_three_five, padicValNat_three_four, padicValNat_three_three,
    padicValNat_three_one']
  omega

theorem padicValNat_three_ordE8_neg {q : ℕ} (hq : 1 < q) (h3 : 3 ∣ q + 1) :
    padicValNat 3 (CFSG.Open.ordE8 q) = 8 * padicValNat 3 (q + 1) + 5 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnq : ¬ 3 ∣ q := by omega
  have sub_one_pos' : ∀ {n : ℕ}, n ≠ 0 → 0 < q ^ n - 1 := fun hn =>
    Nat.sub_pos_of_lt (Nat.one_lt_pow hn hq)
  have h30 := sub_one_pos' (n := 30) (by norm_num)
  have h24 := sub_one_pos' (n := 24) (by norm_num)
  have h20 := sub_one_pos' (n := 20) (by norm_num)
  have h18 := sub_one_pos' (n := 18) (by norm_num)
  have h14 := sub_one_pos' (n := 14) (by norm_num)
  have h12 := sub_one_pos' (n := 12) (by norm_num)
  have h8 := sub_one_pos' (n := 8) (by norm_num)
  have h2 := sub_one_pos' (n := 2) (by norm_num)
  unfold CFSG.Open.ordE8
  rw [padicValNat.mul (by positivity) h2.ne', padicValNat.mul (by positivity) h8.ne',
    padicValNat.mul (by positivity) h12.ne', padicValNat.mul (by positivity) h14.ne',
    padicValNat.mul (by positivity) h18.ne', padicValNat.mul (by positivity) h20.ne',
    padicValNat.mul (by positivity) h24.ne', padicValNat.mul (by positivity) h30.ne',
    padicValNat.pow q 120, padicValNat.eq_zero_of_not_dvd hnq,
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 30 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 24 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 20 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 18 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 14 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 12 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 8 ≠ 0) (by norm_num),
    padicValNat_three_pow_sub_one_neg hq h3 (by norm_num : 2 ≠ 0) (by norm_num)]
  simp only [Nat.reduceDiv]
  rw [padicValNat_three_fifteen, padicValNat_three_twelve', padicValNat_three_ten',
    padicValNat_three_nine, padicValNat_three_seven, padicValNat_three_six',
    padicValNat_three_four, padicValNat_three_one']
  omega

end Valuation

section Abstract

theorem exists_sylow_ge_normal_pgroup {M : Type} [Group M] (N V : Subgroup M) [Finite N]
    (hVN : V ≤ N) (hVn : ∀ x ∈ N, ∀ v ∈ V, x * v * x⁻¹ ∈ V) (hV : IsPGroup 3 V) :
    ∃ P : Subgroup M, P ≤ N ∧ V ≤ P ∧ IsPGroup 3 P ∧
      Nat.card P = 3 ^ (Nat.card N).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 N) := inferInstance
  set V' : Subgroup N := V.subgroupOf N with hV'
  have hV'p : IsPGroup 3 V' := hV.comap_of_injective N.subtype N.subtype_injective
  have hV'n : V'.Normal := ⟨fun v hv x => by
    have := hVn x x.2 v hv
    exact this⟩
  have hnorm : (S : Subgroup N) ≤ Subgroup.normalizer (V' : Set N) := by
    intro p _
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hV'n.conj_mem v hv p, fun hv => ?_⟩
    have := hV'n.conj_mem _ hv p⁻¹
    rwa [show p⁻¹ * (p * v * p⁻¹) * p⁻¹⁻¹ = v by group] at this
  have hsup := hV'p.to_sup_of_normal_left' S.isPGroup' hnorm
  have hV'S : V' ≤ (S : Subgroup N) := le_sup_left.trans (le_of_eq (S.3 hsup le_sup_right))
  refine ⟨(S : Subgroup N).map N.subtype, Subgroup.map_subtype_le _, fun v hv => ?_,
    S.isPGroup'.map _, ?_⟩
  · exact ⟨⟨v, hVN hv⟩, hV'S hv, rfl⟩
  · rw [Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity]

theorem le_of_relIndex_dvd_two {M : Type} [Group M] (A X Q : Subgroup M) [Finite Q] (hQX : Q ≤ X)
    (hQ : IsPGroup 3 Q) (hrel : A.relIndex X ∣ 2) (hX : A.relIndex X ≠ 0) : Q ≤ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : A.relIndex Q ≤ A.relIndex X := Subgroup.relIndex_le_of_le_right hQX hX
  have h2 : A.relIndex X ≤ 2 := Nat.le_of_dvd (by norm_num) hrel
  obtain ⟨k, hk⟩ := (hQ : IsPGroup 3 Q).index (A.subgroupOf Q)
  have hk' : A.relIndex Q = 3 ^ k := hk
  have hk0 : k = 0 := by
    by_contra hne
    have : 3 ≤ A.relIndex Q := by
      rw [hk']
      exact Nat.le_self_pow hne 3
    omega
  rw [hk0, pow_zero] at hk'
  exact Subgroup.relIndex_eq_one.1 hk'

theorem kill_of_embedding {G H : Type} [Group G] [Finite G] [Group H] (ι : G →* H)
    (hι : Function.Injective ι) (Q V : Subgroup H) (hQp : IsPGroup 3 Q) (hVQ : V ≤ Q)
    (hQr : Q ≤ ι.range) (hVn : ∀ p ∈ Q, ∀ v ∈ V, p * v * p⁻¹ ∈ V)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV3 : ∀ a ∈ V, a ^ 3 = 1)
    (hcard : 3 ^ 7 ≤ Nat.card V) (hQcard : Nat.card Q = 3 ^ (Nat.card G).factorization 3) :
    ∃ P : Subgroup G, Nat.card P = 3 ^ (Nat.card G).factorization 3 ∧
      ∀ w ∈ P, orderOf w = 3 →
        81 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer ({w} : Set G)) := by
  have hVr : V ≤ ι.range := hVQ.trans hQr
  have hPcard : Nat.card (Q.comap ι) = Nat.card Q := by
    rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq, inf_of_le_right hQr]
  have hVcard : Nat.card (V.comap ι) = Nat.card V := by
    rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq, inf_of_le_right hVr]
  refine ⟨Q.comap ι, hPcard.trans hQcard, fun w hwP hw3 => ?_⟩
  have hw1 : w ^ 3 = 1 := by
    have h := pow_orderOf_eq_one w
    rwa [hw3] at h
  refine dvd81_card_inf_centralizer_of_cube (V := V.comap ι) (hQp.comap_of_injective ι hι)
    (Subgroup.comap_mono hVQ) (fun p hp v hv => ?_) (fun a ha b hb => ?_) (fun a ha => ?_)
    (hcard.trans_eq hVcard.symm) hwP hw1
  · change ι (p * v * p⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    exact hVn _ hp _ hv
  · apply hι
    rw [map_mul, map_mul]
    exact hVc _ ha _ hb
  · apply hι
    rw [map_pow, map_one]
    exact hV3 _ ha

end Abstract

section Main


theorem exists_weyl_neg_E7 : ∃ w0 : WeylGroup Tag.E7, ∀ u : Fin Tag.E7.rank → ℤ, w0 • u = -u := by
  refine ⟨(coxeterSystem Tag.E7).wordProd e7TwoWord, fun u => ?_⟩
  have h : toMat Tag.E7.rank e7TwoMat = (-1 : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ) := by
    decide +kernel
  rw [wordProd_smul_eq_wordMat_mulVec, e7Two_wordMat, h, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem exists_weyl_neg_E8 : ∃ w0 : WeylGroup Tag.E8, ∀ u : Fin Tag.E8.rank → ℤ, w0 • u = -u := by
  refine ⟨(coxeterSystem Tag.E8).wordProd e8TwoWord, fun u => ?_⟩
  have h : toMat Tag.E8.rank e8TwoMat = (-1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) := by
    decide +kernel
  rw [wordProd_smul_eq_wordMat_mulVec, e8Two_wordMat, h, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem exists_kill_subgroup_neg_aux {τ : Tag} (d : ℕ)
    (hτ : (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) (hr : 7 ≤ τ.rank) {w0 : WeylGroup τ}
    (hw0 : ∀ u : Fin τ.rank → ℤ, w0 • u = -u) {F : Type} [Field F] [Finite F]
    (h3 : 3 ∣ Nat.card F + 1)
    (hval : (Nat.card ↥(adjointGroup τ F)).factorization 3 =
      ((Nat.card F + 1) ^ τ.rank * Nat.card (WeylGroup τ)).factorization 3) :
    ∃ P : Subgroup ↥(adjointGroup τ F),
      Nat.card P = 3 ^ (Nat.card ↥(adjointGroup τ F)).factorization 3 ∧
      ∀ w ∈ P, orderOf w = 3 →
        81 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer ({w} : Set ↥(adjointGroup τ F))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite ↥(adjointGroup τ F) := generated_group_finite τ F
  have : Fintype F := Fintype.ofFinite F
  have hd2 : d ∣ 2 := by rcases hτ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hd0 : d ≠ 0 := by rcases hτ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hτ3 : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1) := by
    rcases hτ with h | h
    exacts [Or.inr (Or.inl h), Or.inr (Or.inr h)]
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hℓ⟩
  have hq : Nat.card F = ringChar F ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP F (ringChar F) := ringChar.charP F
  let L := AlgebraicClosure F
  have : CharP L (ringChar F) := charP_of_injective_algebraMap (algebraMap F L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  let Fr : L →+* L := iterateFrobenius L (ringChar F) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card F := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar F) (f : ℕ) c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator τ F (ℓ := ringChar F) (f := (f : ℕ)) f.pos L w0
  have hcardN : Nat.card (NFix (canonicalRep (coxeterSystem τ) L w0) Fr) =
      (Nat.card F + 1) ^ τ.rank * Nat.card (WeylGroup τ) := by
    rw [card_NFix Fr hw0 hFr, card_twistedTorusOf_negOne (K := F) Fr w0 hw0 hFr]
  have hNfin : Finite (NFix (canonicalRep (coxeterSystem τ) L w0) Fr) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcardN]
      exact mul_ne_zero (pow_ne_zero _ (by omega)) Nat.card_pos.ne')
  have hcommT := isMulCommutative_twistedTorusOf Fr w0 hw0
  have hV0N : V3 (canonicalRep (coxeterSystem τ) L w0) (Units.map (entrywiseHom Fr)) ≤
      NFix (canonicalRep (coxeterSystem τ) L w0) Fr :=
    V3_le.trans (twistedTorusOf_le_NFix _ Fr)
  have hVn0 : ∀ x ∈ NFix (canonicalRep (coxeterSystem τ) L w0) Fr,
      ∀ v ∈ V3 (canonicalRep (coxeterSystem τ) L w0) (Units.map (entrywiseHom Fr)),
        x * v * x⁻¹ ∈ V3 (canonicalRep (coxeterSystem τ) L w0) (Units.map (entrywiseHom Fr)) := by
    intro x hx v hv
    rw [mem_V3 hcommT]
    refine ⟨NFix_conj_mem_twistedTorusOf hx (V3_le hv), ?_⟩
    rw [conj_pow, pow_three_eq_one_of_mem_V3 hv]
    group
  have hV0p : IsPGroup 3
      (V3 (canonicalRep (coxeterSystem τ) L w0) (Units.map (entrywiseHom Fr))) := fun v =>
    ⟨1, by simpa using Subtype.ext (pow_three_eq_one_of_mem_V3 v.2)⟩
  obtain ⟨P0, hP0N, hV0P0, hP0p, hP0card⟩ := exists_sylow_ge_normal_pgroup _ _ hV0N hVn0 hV0p
  let c : ModGL τ L →* ModGL τ L := (MulAut.conj g0).toMonoidHom
  have hc : Function.Injective c := (MulAut.conj g0).injective
  have hc_apply : ∀ x, c x = g0 * x * g0⁻¹ := fun x => rfl
  set X : Subgroup (ModGL τ L) := (NFix (canonicalRep (coxeterSystem τ) L w0) Fr).map c with hX
  have hXfin : Finite X :=
    Finite.of_surjective (c.subgroupMap _) (c.subgroupMap_surjective _)
  have hXC : X ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hg0C (monomialSubgroup_le_adjointGroup' (hx.1))) (inv_mem hg0C)
  have hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x := by
    rintro _ ⟨x, hx, rfl⟩
    have hxfix : negPhi Fr (canonicalRep (coxeterSystem τ) L w0) x = x := hx.2
    rw [negPhi_apply] at hxfix
    rw [hc_apply, map_mul, map_mul, map_inv, hg0]
    calc g0 * canonicalRep (coxeterSystem τ) L w0 * Units.map (entrywiseHom Fr) x *
          (g0 * canonicalRep (coxeterSystem τ) L w0)⁻¹ =
        g0 * (canonicalRep (coxeterSystem τ) L w0 * Units.map (entrywiseHom Fr) x *
          (canonicalRep (coxeterSystem τ) L w0)⁻¹) * g0⁻¹ := by group
      _ = g0 * x * g0⁻¹ := by rw [hxfix]
  let ι : ↥(adjointGroup τ F) →* ModGL τ L :=
    (baseChangeGL (algebraMap F L)).comp (adjointGroup τ F).subtype
  have hrange : ι.range = (adjointGroup τ F).map (baseChangeGL (algebraMap F L)) := by
    change ((baseChangeGL (algebraMap F L)).comp (adjointGroup τ F).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  obtain ⟨hrel, -⟩ := finite_fixed_subgroup_rational_perfect (K := F) d hτ3 Fr hFr X hXC hXF
  have hrel0 : ((adjointGroup τ F).map (baseChangeGL (algebraMap F L))).relIndex X ≠ 0 :=
    ne_zero_of_dvd_ne_zero hd0 hrel
  have hQX : P0.map c ≤ X := Subgroup.map_mono hP0N
  have hQfin : Finite (P0.map c) := Finite.of_injective _ (Subgroup.inclusion_injective hQX)
  have hQp : IsPGroup 3 (P0.map c) := hP0p.map c
  have hQr : P0.map c ≤ ι.range := by
    rw [hrange]
    exact le_of_relIndex_dvd_two _ X _ hQX hQp (hrel.trans hd2) hrel0
  refine kill_of_embedding ι hι (P0.map c)
    ((V3 (canonicalRep (coxeterSystem τ) L w0) (Units.map (entrywiseHom Fr))).map c) hQp
    (Subgroup.map_mono hV0P0) hQr ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨p0, hp0, rfl⟩ _ ⟨v0, hv0, rfl⟩
    exact ⟨p0 * v0 * p0⁻¹, hVn0 p0 (hP0N hp0) v0 hv0, by rw [map_mul, map_mul, map_inv]⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm_of_mem_V3 hcommT ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, pow_three_eq_one_of_mem_V3 ha, map_one]
  · rw [Subgroup.card_map_of_injective hc, card_V3_negOne (K := F) Fr w0 hw0 hFr h3]
    exact Nat.pow_le_pow_right (by norm_num) hr
  · rw [Subgroup.card_map_of_injective hc, hP0card, hcardN, hval]

theorem exists_kill_subgroup_E78_neg {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8) {F : Type}
    [Field F] [Finite F] (h3 : 3 ∣ Nat.card F + 1) :
    ∃ P : Subgroup ↥(adjointGroup τ F),
      Nat.card P = 3 ^ (Nat.card ↥(adjointGroup τ F)).factorization 3 ∧
      ∀ w ∈ P, orderOf w = 3 →
        81 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer ({w} : Set ↥(adjointGroup τ F))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hF1 : Nat.card F + 1 ≠ 0 := by omega
  rcases hτ with rfl | rfl
  · obtain ⟨w0, hw0⟩ := exists_weyl_neg_E7
    refine exists_kill_subgroup_neg_aux 2 (Or.inl ⟨rfl, rfl⟩) (by decide) hw0 h3 ?_
    have hne : (Nat.card F + 1) ^ Tag.E7.rank ≠ 0 := pow_ne_zero _ hF1
    rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, padicValNat_three_ordE7_neg hq h3,
      card_weylGroup_E7', padicValNat.mul hne (by norm_num), padicValNat.pow (Nat.card F + 1) Tag.E7.rank]
    have e : padicValNat 3 2903040 = 4 := by
      rw [show (2903040 : ℕ) = 3 ^ 4 * 35840 by norm_num,
        padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [e]
    rfl
  · obtain ⟨w0, hw0⟩ := exists_weyl_neg_E8
    refine exists_kill_subgroup_neg_aux 1 (Or.inr ⟨rfl, rfl⟩) (by decide) hw0 h3 ?_
    have hne8 : (Nat.card F + 1) ^ Tag.E8.rank ≠ 0 := pow_ne_zero _ hF1
    rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, padicValNat_three_ordE8_neg hq h3,
      card_weylGroup_E8', padicValNat.mul hne8 (by norm_num), padicValNat.pow (Nat.card F + 1) Tag.E8.rank]
    have e : padicValNat 3 696729600 = 5 := by
      rw [show (696729600 : ℕ) = 3 ^ 5 * 2867200 by norm_num,
        padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [e]
    rfl

end Main

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
