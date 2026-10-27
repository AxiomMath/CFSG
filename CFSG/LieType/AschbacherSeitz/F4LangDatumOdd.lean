module

public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvLangDatum
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExc
public import CFSG.LieType.SeitzGeneration.ExcTorusF4Two

public section

namespace CFSG.LieType.AschbacherSeitz

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType CFSG.StandardType.ExcMaxToral CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice Polynomial
open CFSG.Open (IsElemAbelian)
open scoped Matrix

theorem exists_elemAbelian_F4_two_three
    (K : Type) [Field K] [Finite K]
    (he : orderOf ((Nat.card K : ℕ) : ZMod 3) = 2) :
    ∃ E : Subgroup (adjointGroup Tag.F4 K), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hpq : ¬ 3 ∣ Nat.card K := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hchar : (wordMat Tag.F4 f4TwoWord).charpoly = cyclotomic 2 ℤ ^ 4 * 1 := by
    rw [f4Two_charpoly]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  have hR : ¬ ((3 : ℤ) ∣ (1 : ℤ[X]).eval (Nat.card K : ℤ)) := by
    rw [Polynomial.eval_one]
    norm_num
  refine exists_elemAbelian_untwisted K hp hpq ?_ (IsWeylMatrix.of_word Tag.F4 f4TwoWord)
    (1 : ℤ[X]) (by norm_num) f4Two_pow (by norm_num) hchar he hR
  intro L _ _ _ Fr hFr X _ hXC hXF P hPX _ x hx
  have hXle : X ≤ (adjointGroup Tag.F4 K).map (baseChangeGL (algebraMap K L)) := by
    intro y hy
    rw [← (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices Tag.F4
      (Or.inr rfl) K L Fr hFr).1]
    exact ⟨hXC hy, hXF y hy⟩
  exact hXle (hPX hx)

theorem f4_three_pow_four_le_card_of_order_two
    (K : Type) [Field K] [Finite K]
    (he : orderOf ((Nat.card K : ℕ) : ZMod 3) = 2)
    (E : Subgroup (adjointGroup Tag.F4 K))
    (hmax : ∀ A : Subgroup (adjointGroup Tag.F4 K), IsElemAbelian 3 A → Nat.card A ≤ Nat.card E) :
    3 ^ 4 ≤ Nat.card E := by
  obtain ⟨A, hA, hAc⟩ := exists_elemAbelian_F4_two_three K he
  calc 3 ^ 4 = Nat.card A := hAc.symm
    _ ≤ Nat.card E := hmax A hA

theorem f4_pow_excDegCount_le_card
    (K : Type) [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (adjointGroup Tag.F4 K)) (hE : IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E)
    (hmax : ∀ A : Subgroup (adjointGroup Tag.F4 K), IsElemAbelian p A → Nat.card A ≤ Nat.card E) :
    p ^ excDegCount Tag.F4 (orderOf (Nat.card K : ZMod p)) ≤ Nat.card E := by
  have hdeg : 4 ≤ excDegCount Tag.F4 (orderOf (Nat.card K : ZMod p)) := by
    by_contra hcon
    have hle := excPRankBound (τ := Tag.F4) (Or.inr (Or.inr rfl)) K hp hp2 (by omega) E hE
    have hlt : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact not_lt_of_ge hle (lt_of_lt_of_le hlt h4)
  rcases excDegCount_ge_four hdeg with ⟨_hτ, hd, ha⟩ | ⟨hE8, _hd, _ha⟩
  · rw [ha]
    have hrank : Tag.F4.rank = 4 := rfl
    rw [hrank]
    by_cases hp3 : p = 3
    · subst hp3
      rcases hd with hd1 | hd2
      ·
        have h1 : ((Nat.card K : ℕ) : ZMod 3) = 1 := orderOf_eq_one_iff.1 hd1
        have hone : 1 ≤ Nat.card K := Nat.card_pos
        have h0 : (((Nat.card K - 1 : ℕ)) : ZMod 3) = 0 := by
          rw [Nat.cast_sub hone, h1, Nat.cast_one, sub_self]
        have hpq3 : 3 ∣ Nat.card K - 1 := (ZMod.natCast_eq_zero_iff (Nat.card K - 1) 3).mp h0
        calc 3 ^ 4 = Nat.card (TableBF4.torusPow K 3) :=
              (TableBF4.card_torusPow (K := K) (p := 3) Nat.prime_three hpq3).symm
          _ ≤ Nat.card E := hmax _ (OrdPInnerExc.isElemAbelian_torusPow Tag.F4 K 3)
      ·
        exact f4_three_pow_four_le_card_of_order_two K hd2 E hmax
    · have hp3' : 3 < p := by
        have h2 : 2 ≤ p := hp.two_le
        omega
      rcases hd with hd1 | hd2
      · obtain ⟨A, hA, hAc⟩ := exists_elemAbelian_F4_one K hp hp3' hd1
        calc p ^ 4 = Nat.card A := hAc.symm
          _ ≤ Nat.card E := hmax A hA
      · obtain ⟨A, hA, hAc⟩ := exists_elemAbelian_F4_two K hp hp3' hd2
        calc p ^ 4 = Nat.card A := hAc.symm
          _ ≤ Nat.card E := hmax A hA
  · cases hE8

theorem exists_langDatum_of_maxElem_F4
    (K : Type) [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (adjointGroup Tag.F4 K)) (hE : IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E)
    (hmax : ∀ A : Subgroup (adjointGroup Tag.F4 K), IsElemAbelian p A → Nat.card A ≤ Nat.card E) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
      (w : WeylGroup Tag.F4) (g0 : ModGL Tag.F4 (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
      (hg0 : Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w),
      ∀ x ∈ E, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) * g0 ∈
        (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).torus := by
  have hdeg : 4 ≤ excDegCount Tag.F4 (orderOf (Nat.card K : ZMod p)) := by
    by_contra hcon
    have hle := excPRankBound (τ := Tag.F4) (Or.inr (Or.inr rfl)) K hp hp2 (by omega) E hE
    have hlt : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact not_lt_of_ge hle (lt_of_lt_of_le hlt h4)
  have hcard := f4_pow_excDegCount_le_card K hp hp2 E hE h4 hmax
  obtain ⟨Fr, hFr, D, hΦ, _hqK, ⟨w, hwn, _hshape⟩, hmem, _hiff⟩ :=
    adjointMaxElemToral Tag.F4 K p (inferInstance : Finite K) (inferInstance : CharP K 2)
      hp hp2 hdeg E hE hcard
  have hg0 : Units.map (entrywiseHom Fr) D.g0 =
      D.g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w := by
    rw [← hΦ, ← hwn]
    exact D.lang
  have htorus : (LangDatum.ofFrobenius Fr (Nat.card K) hFr w D.g0_mem hg0).torus = D.torus := by
    change CFSG.RankThree.PartOne.KE.twistedTorusOf
      (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)
      (Units.map (entrywiseHom Fr)) = CFSG.RankThree.PartOne.KE.twistedTorusOf D.n D.Φ
    rw [hwn, hΦ]
  refine ⟨Fr, hFr, w, D.g0, D.g0_mem, hg0, ?_⟩
  intro x hx
  rw [htorus]
  exact hmem x hx

end CFSG.LieType.AschbacherSeitz
