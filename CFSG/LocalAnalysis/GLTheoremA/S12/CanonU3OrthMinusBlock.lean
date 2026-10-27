module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthOrthIdent
import CFSG.LieType.SemisimpleCentralizers.OrderThree.CenterQuot
import CFSG.LieType.SemisimpleCentralizers.HeldLangU64Ord
import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Comp
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.RankThree.PartOne.K159.RowFourType
import CFSG.ClassicalInvolution.RouteD.TWYType
public import CFSG.Timmesfeld.Orders.Bang
import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusArith
import CFSG.Quasithin.EmptyFaithful.Insp7NumB
import CFSG.RankThree.PartOne.S15K.OrthMult
import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverUni
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeCore
import CFSG.Quasithin.Vol2.Ch11SecBL2UPSU
import CFSG.ClassicalInvolution.RouteD.TWRExoticArith
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Background.B1
import CFSG.Quasithin.Background.B3Q
import CFSG.Quasithin.Background.B3ThreeModel
import CFSG.Quasithin.Background.B3ThreeStruct
import CFSG.Quasithin.Background.G2Omega4PlusModule
import CFSG.Quasithin.Background.InternalSecIso
import CFSG.Quasithin.EmptyFaithful.Insp7NumA
import CFSG.Quasithin.EmptyFaithful.S143FF
import CFSG.Quasithin.EmptyFaithful.S143Final
import CFSG.Quasithin.EmptyFaithful.S143HD
import CFSG.Quasithin.EmptyFaithful.S143IG
import CFSG.Quasithin.EmptyFaithful.S143JB
import CFSG.Quasithin.EmptyFaithful.S143KO
import CFSG.Quasithin.EmptyFaithful.S143KP
import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
import CFSG.Quasithin.Vol2.Ch10SecD33
import CFSG.Quasithin.Vol2.Ch10SecDClA
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA03Basic
import CFSG.Quasithin.Vol2.Ch11SecA04Glue
import CFSG.Quasithin.Vol2.Ch11SecA11Main
import CFSG.Quasithin.Vol2.Ch11SecA14Conj
import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
import CFSG.Quasithin.Vol2.Ch11SecAViN13
import CFSG.Quasithin.Vol2.Ch11SecBDerived35
import CFSG.Quasithin.Vol2.Ch11SecBL2ODone
import CFSG.Quasithin.Vol2.Ch11SecBL2UOver
import CFSG.Quasithin.Vol2.Ch11SecBTCStar
import CFSG.Quasithin.Vol2.Ch11SecSMain
import CFSG.Quasithin.Vol2.Ch11SecSShape2
import CFSG.Quasithin.Vol2.Ch11SecSSym2
import CFSG.Quasithin.Vol2.Ch11SecSSym4
import CFSG.Quasithin.Vol2.Ch11SecSSym5
import CFSG.Quasithin.Vol2.Ch11StatementsE
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel
import CFSG.RankThree.PartTwo.Sec8.Item86ResProofTwo
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Fixed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3.OrthMinus

open CFSG.Open Polynomial Module QuadraticMap
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal
  CFSG.GroupTheory.WeirSylow CFSG.ClassicalInvolution.RouteD.TWY
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

theorem oddOrderIsometry_of_pow_eq_one {p : ℕ} (hp : p.Prime) {K : Type} [Field K]
    [Finite K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (hpℓ : p ≠ ringChar K) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (x : ↥(orthDerived Q)) (hxp : x ^ p = 1) : OddOrderIsometry Q p (x : V ≃ₗ[K] V) := by
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h1 := (ringChar.spec K p).mp h0
    have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
    rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
    · exact hℓ.one_lt.ne' h2
    · exact hpℓ h2.symm
  exact ⟨orthDerived_le_orthogonalGroup x.2, congrArg Subtype.val hxp, hpK, fun v hv =>
    hQ.1 v fun w => by simpa using hv w⟩

theorem even_finrank_of_polarNondegOn {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {W : Submodule K V} (hW : PolarNondegOn Q W) : Even (finrank K W) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have halt : (polarBilin (Q.restrict W)).IsAlt := fun w => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul,
      show ((2 : ℕ) : K) = 0 from h2, zero_mul]
  exact LinearMap.BilinForm.IsAlt.even_finrank halt (nondegenerate_polarBilin_restrict hW)

theorem polarNondegOn_fixedSpace {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {W R : Submodule K V}
    (hc : IsCompl W R) (horth : ∀ w ∈ W, ∀ r ∈ R, polar Q w r = 0)
    (hreg : ∀ v, (∀ w, polar Q v w = 0) → v = 0) : PolarNondegOn Q W := by
  intro w hw hperp
  refine hreg w fun v => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_add_of_isCompl hc v
  rw [QuadraticMap.polar_add_right, hperp a ha, horth w hw b hb, add_zero]

theorem polarNondegOn_othersSpace {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {W R : Submodule K V}
    (hc : IsCompl W R) (horth : ∀ w ∈ W, ∀ r ∈ R, polar Q w r = 0)
    (hreg : ∀ v, (∀ w, polar Q v w = 0) → v = 0) : PolarNondegOn Q R := by
  intro r hr hperp
  refine hreg r fun v => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_add_of_isCompl hc v
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_comm, horth a ha r hr, hperp b hb,
    add_zero]

theorem card_orthogonalGroup_six_plus {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {R : QuadraticForm K W} (hR : (polarBilin R).Nondegenerate)
    (hplus : IsPlusType R) (hdim : finrank K W = 6) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) =
      2 * Nat.card K ^ 6 * (Nat.card K ^ 3 - 1) * (Nat.card K ^ 2 - 1) *
        (Nat.card K ^ 4 - 1) := by
  have h := natCard_orthogonalGroup_of_type (K := K) hR (m := 2) (by omega)
    (Or.inl ⟨rfl, hplus⟩)
  simp only [Nat.reduceMul, Nat.reduceAdd] at h
  have hprod : (∏ i ∈ Finset.Icc 1 2, (((Nat.card K : ℤ) ^ 2) ^ i - 1)) =
      ((Nat.card K : ℤ) ^ 2 - 1) * ((Nat.card K : ℤ) ^ 4 - 1) := by
    have h12 : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
    rw [h12, Finset.prod_pair (by norm_num : (1 : ℕ) ≠ 2)]
    simp only [pow_one]
    ring_nf
  rw [hprod] at h
  refine Nat.cast_injective (R := ℤ) ?_
  rw [h]
  have hq1 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hsub : ∀ i : ℕ, 0 < i → ((Nat.card K ^ i - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ i - 1 := by
    intro i hi
    rw [Nat.cast_sub (Nat.one_le_pow i (Nat.card K) hq1), Nat.cast_pow]
    norm_num
  push_cast
  rw [hsub 3 (by norm_num), hsub 2 (by norm_num), hsub 4 (by norm_num)]
  ring

theorem not_dvd_card_orthogonalGroup_six_plus_of_primitive {K : Type} [Field K] [Finite K]
    [CharP K 2] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {R : QuadraticForm K W} (hR : (polarBilin R).Nondegenerate)
    (hplus : IsPlusType R) (hdim : finrank K W = 6) {m r : ℕ}
    (hK : Nat.card K = 2 ^ m) (hm : Odd m)
    (hr : CFSG.Timmesfeld.IsPrimitivePrimeDivisor r (6 * m)) :
    ¬ r ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) := by
  have hN : Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) =
      2 * (2 ^ m) ^ 6 * ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1) := by
    rw [card_orthogonalGroup_six_plus hR hplus hdim, hK]
  rw [hN]
  have hmpos : 0 < m := hm.pos
  have hkpos : 0 < 6 * m := by omega
  have hr2 : ¬ r ∣ 2 := by
    have hne := hr.ne_two hkpos
    exact fun h => hne ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_two).mp h)
  have hpow6 : ¬ r ∣ 2 ^ (6 * m) := by
    intro h
    have h1 : r ∣ 2 ^ (6 * m) - (2 ^ (6 * m) - 1) := Nat.dvd_sub h hr.dvd
    have h2 : 2 ^ (6 * m) - (2 ^ (6 * m) - 1) = 1 := by
      have hle : 1 ≤ 2 ^ (6 * m) := Nat.one_le_two_pow
      omega
    rw [h2] at h1
    exact hr.prime.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpow3 : ¬ r ∣ 2 ^ (3 * m) - 1 := by
    intro h
    have h1 := (hr.dvd_sub_one_iff hkpos (3 * m)).mp h
    have hle := Nat.le_of_dvd (by omega : 0 < 3 * m) h1
    omega
  have hpow2 : ¬ r ∣ 2 ^ (2 * m) - 1 := by
    intro h
    have h1 := (hr.dvd_sub_one_iff hkpos (2 * m)).mp h
    have hle := Nat.le_of_dvd (by omega : 0 < 2 * m) h1
    omega
  have hpow4 : ¬ r ∣ 2 ^ (4 * m) - 1 := by
    intro h
    have h1 := (hr.dvd_sub_one_iff hkpos (4 * m)).mp h
    have hle := Nat.le_of_dvd (by omega : 0 < 4 * m) h1
    omega
  have hp6 : ¬ r ∣ (2 ^ m) ^ 6 := by
    rw [← pow_mul, Nat.mul_comm m 6]
    exact hpow6
  have hp3 : ¬ r ∣ (2 ^ m) ^ 3 - 1 := by
    rw [← pow_mul, Nat.mul_comm m 3]
    exact hpow3
  have hp2 : ¬ r ∣ (2 ^ m) ^ 2 - 1 := by
    rw [← pow_mul, Nat.mul_comm m 2]
    exact hpow2
  have hp4 : ¬ r ∣ (2 ^ m) ^ 4 - 1 := by
    rw [← pow_mul, Nat.mul_comm m 4]
    exact hpow4
  intro h
  rcases hr.prime.dvd_mul.mp h with h | h
  · rcases hr.prime.dvd_mul.mp h with h | h
    · rcases hr.prime.dvd_mul.mp h with h | h
      · rcases hr.prime.dvd_mul.mp h with h | h
        · exact hr2 h
        · exact hp6 h
      · exact hp3 h
    · exact hp2 h
  · exact hp4 h

theorem dvd_ordTwistedA_of_primitive {m r : ℕ} (hm : Odd m)
    (hr : CFSG.Timmesfeld.IsPrimitivePrimeDivisor r (6 * m)) :
    r ∣ ordTwistedA 2 (2 ^ m) := by
  have hmpos : 0 < m := hm.pos
  have hkpos : 0 < 6 * m := by omega
  have hrne3 : r ≠ 3 := by
    intro h3
    have h2 := hr.eq_two_of_dvd_three hkpos (by simp [h3])
    omega
  have h6 : 6 * m ∣ 2 * (3 * m) := ⟨1, by ring⟩
  have h6' : ¬ 6 * m ∣ 3 * m := by
    intro h
    have hle := Nat.le_of_dvd (by omega : 0 < 3 * m) h
    omega
  have h3m : r ∣ 2 ^ (3 * m) + 1 := (hr.dvd_add_one_iff hkpos (3 * m)).mpr ⟨h6, h6'⟩
  have hq3 : r ∣ (2 ^ m) ^ 3 + 1 := by
    rw [← pow_mul, Nat.mul_comm m 3]
    exact h3m
  have hq : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hnum : r ∣ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hq3 _) _
  rw [CFSG.Quasithin.Vol2.Ch11.SecB.ordTwistedA_two_eq (q := 2 ^ m) hq]
  have hd : 2 ^ m + 1 ∣ (2 ^ m) ^ 3 + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ m) 1 (by decide : Odd 3)
  have hdiv : Nat.gcd 3 (2 ^ m + 1) ∣ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_right ((Nat.gcd_dvd_right _ _).trans hd) _) _
  have hgcd3 : ¬ r ∣ Nat.gcd 3 (2 ^ m + 1) := by
    intro h
    have h3 : r ∣ 3 := h.trans (Nat.gcd_dvd_left _ _)
    exact hrne3 ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_three).mp h3)
  have hcop : Nat.Coprime (Nat.gcd 3 (2 ^ m + 1)) r := by
    rw [Nat.coprime_comm]
    exact (hr.prime.coprime_iff_not_dvd).mpr hgcd3
  exact (Nat.dvd_div_iff_mul_dvd hdiv).mpr (hcop.mul_dvd_of_dvd_of_dvd hdiv hnum)


theorem false_of_fixedLayer {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) (hV : ¬ IsPlusType Q) (hdim : finrank K V = 8)
    {m n : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m) (hn : Odd n) (hn3 : 3 ≤ n)
    (hmn : m ∣ n) {y : V ≃ₗ[K] V} (hy : OddOrderIsometry Q 3 y) (hy1 : y ≠ 1)
    {J : Subgroup (ProjOrthDerived Q)}
    (hJlay : ∃ F : Subgroup (V ≃ₗ[K] V), F ≤ supportedFixedDerived Q y ∧
      J = (F.subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))
    (hcard : Nat.card (J ⧸ Subgroup.center J) = ordTwistedA 2 (2 ^ n)) : False := by
  classical
  obtain ⟨F, hF, hJF⟩ := hJlay
  have h3q : 3 ∣ Nat.card K + 1 := by
    rw [hK]
    exact CFSG.RankThree.PartTwo.Sec8.Item82OneProof.three_dvd_two_pow_add_one_of_odd hm
  set W : Submodule K V := fixedSpace y with hW
  set R : Submodule K V := othersSpace y.toLinearMap (X - 1) with hR
  have hcompl : IsCompl W R := hy.fixed_others.1
  have horth := hy.fixed_others.2
  have hWnd : PolarNondegOn Q W := polarNondegOn_fixedSpace hcompl horth hy.regular
  have hRnd : PolarNondegOn Q R := polarNondegOn_othersSpace hcompl horth hy.regular
  have hWnd' : (polarBilin (Q.restrict W)).Nondegenerate := by
    rw [hW]
    exact hy.polarBilin_fixed_nondegenerate
  have hEvenW : Even (finrank K W) := even_finrank_of_polarNondegOn hWnd
  obtain ⟨j, hj⟩ := hEvenW
  have hj2 : finrank K W = 2 * j := by omega
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  have hRdim : finrank K R = 2 * (4 - j) := by omega
  have hRne : R ≠ ⊥ := by
    intro hR0
    apply hy1
    have hWtop : W = ⊤ := by
      have h := hcompl.sup_eq_top
      rw [hR0] at h
      simpa using h
    ext v
    have hv : v ∈ fixedSpace y := by
      rw [← hW, hWtop]
      exact Submodule.mem_top
    exact mem_fixedSpace.mp hv
  have hRpos : 0 < finrank K R := by
    by_contra h
    have h0 : finrank K R = 0 := by omega
    exact hRne (Submodule.finrank_eq_zero.mp h0)
  have hj3le : j ≤ 3 := by omega
  have hRinv : ∀ u ∈ R, y u ∈ R := by
    intro u hu
    have hmap : R.map y.toLinearMap ≤ R := by
      rw [hR]
      unfold othersSpace
      rw [Submodule.map_iSup]
      refine iSup_le fun k => ?_
      rw [Submodule.map_iSup]
      refine iSup_le fun hk => ?_
      refine le_iSup₂_of_le k hk ?_
      rintro _ ⟨v, hv, rfl⟩
      exact apply_mem_primaryComponent (Commute.refl _) hv
    exact hmap ⟨u, hu, rfl⟩
  have hRfix : ∀ u ∈ R, y u = u → u = 0 := by
    intro u hu hyu
    exact (Submodule.disjoint_def.mp hcompl.disjoint) u (mem_fixedSpace.mpr hyu) hu
  have hquotdvd : Nat.card (J ⧸ Subgroup.center J) ∣
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W)) := by
    have h3 : Nat.card (J ⧸ Subgroup.center J) ∣ Nat.card J :=
      ⟨Nat.card (Subgroup.center J), Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
    have h4 : Nat.card J ∣ Nat.card ↥(F.subgroupOf (orthDerived Q)) := by
      rw [hJF]
      exact Subgroup.card_map_dvd _ _
    have hFle : F ≤ orthDerived Q := hF.trans hy.supportedFixedDerived_le_orthDerived
    have h5 : Nat.card ↥(F.subgroupOf (orthDerived Q)) = Nat.card ↥F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFle).toEquiv
    have h6 : Nat.card ↥F ∣ Nat.card ↥(supportedFixedDerived Q y) := Subgroup.card_dvd_of_le hF
    have h7 : Nat.card ↥(supportedFixedDerived Q y) =
        Nat.card ↥(orthDerived (Q.restrict W)) := by
      rw [hW]
      exact Nat.card_congr (supportedFixedDerivedEquiv hy).toEquiv
    have h8 : Nat.card ↥((orthDerived (Q.restrict W)).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W))) ∣
        Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W)) :=
      Subgroup.card_subgroup_dvd_card _
    have h8' : Nat.card ↥((orthDerived (Q.restrict W)).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W))) =
        Nat.card ↥(orthDerived (Q.restrict W)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (orthDerived_le_orthogonalGroup)).toEquiv
    exact h3.trans (h4.trans (h5.symm ▸ (h6.trans (h7.symm ▸ (h8' ▸ h8)))))
  have h2dvd : 2 ^ (3 * n) ∣
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W)) := by
    refine (CFSG.Quasithin.Insp7.two_pow_dvd_ordTwistedA_two (f := n)).trans ?_
    rw [← hcard]
    exact hquotdvd
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  ·
    have hWbot : W = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      rw [hj2, hj0]
    haveI : Subsingleton W := by
      rw [hWbot]
      infer_instance
    have hO1 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W)) = 1 := by
      refine Nat.card_eq_one_iff_unique.mpr ⟨?_, ⟨1⟩⟩
      refine ⟨fun a b => Subtype.ext ?_⟩
      exact LinearEquiv.ext fun v => Subsingleton.elim _ _
    rw [hO1] at h2dvd
    have hgt : 1 < 2 ^ (3 * n) := Nat.one_lt_pow (by omega) (by norm_num)
    have h1 : 2 ^ (3 * n) = 1 := Nat.dvd_one.mp h2dvd
    omega
  ·
    have hfac :=
      CFSG.HardMathSupport.Dickson.Bal207.OrthFix.factorization_two_card_orthogonalGroup
        (R := Q.restrict W) hWnd'
      (m := j - 1) (f := m) (by omega) hK
    have hOpos : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W)) ≠ 0 :=
      Nat.card_pos.ne'
    have hle : 3 * n ≤
        (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W))).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hOpos).mp h2dvd
    rw [hfac] at hle
    have hmle : m ≤ n := Nat.le_of_dvd hn.pos hmn
    have hj3 : j = 3 := by
      interval_cases j
      · norm_num at hle
        omega
      · norm_num at hle
        omega
      · rfl
    have hle6 : 3 * n ≤ 1 + m * 6 := by
      have h := hle
      rw [hj3] at h
      norm_num at h
      omega
    have hm3 : 3 ≤ m := by
      obtain ⟨b, hb⟩ := hm
      omega
    have hneq : n = m := by
      obtain ⟨a, ha⟩ := hn
      obtain ⟨b, hb⟩ := hm
      obtain ⟨t, ht⟩ := hmn
      have hn2m : n ≤ 2 * m := by omega
      have h2 : m * t ≤ m * 2 := by
        calc m * t = n := ht.symm
          _ ≤ 2 * m := hn2m
          _ = m * 2 := by ring
      have htle : t ≤ 2 := Nat.le_of_mul_le_mul_left h2 (by omega : 0 < m)
      interval_cases t
      · have h0 : n = 0 := by simpa using ht
        omega
      · simpa using ht
      · have h2t : n = 2 * m := by simpa [mul_comm] using ht
        omega
    rw [hneq] at hcard
    have hWdim : finrank K W = 6 := by rw [hj2, hj3]
    have hRdim2 : finrank K R = 2 * 1 := by rw [hRdim, hj3]
    have hRnotPlus : ¬ IsPlusType (Q.restrict R) := by
      intro hpR
      have hiff := CFSG.RankThree.PartOne.K159.isPlusType_iff_even_of_fixedFree
        (Q := Q) (x := y) hy Nat.prime_three (by norm_num) h3q 1 R hRinv hRnd hRfix
        (by rw [hRdim2])
      exact absurd (hiff.mp hpR) (by norm_num)
    have hWplus : IsPlusType (Q.restrict W) := by
      have hiff := CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_iff_of_isCompl
        (Q := Q) hcompl horth hWnd hRnd (a := 3) (b := 1) (by norm_num) (by norm_num)
        (by rw [hWdim]) (by rw [hRdim2])
      have hnot : ¬ (IsPlusType (Q.restrict W) ↔ IsPlusType (Q.restrict R)) :=
        fun h => hV (hiff.mpr h)
      by_contra hA
      exact hnot ⟨fun h => absurd h hA, fun h => absurd h hRnotPlus⟩
    obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 6 * m)
      (by omega) (by omega)
    have hrdiv : r ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W)) :=
      (dvd_ordTwistedA_of_primitive hm hr).trans (by
        rw [← hcard]
        exact hquotdvd)
    exact not_dvd_card_orthogonalGroup_six_plus_of_primitive hWnd' hWplus hWdim hK hm hr hrdiv


theorem injective_mk'_of_charTwo {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Function.Injective (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := by
  obtain ⟨-, -, hcardS, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', Subgroup.eq_bot_iff_forall]
  intro z hz
  have hz2 : z ^ 2 = 1 := by
    have h1 : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣
        Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := orderOf_dvd_natCard _
    have h2 : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣ 2 := by
      have hpos : 0 < Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := Nat.card_pos
      interval_cases hc : Nat.card ↥((scalars K V).subgroupOf (orthDerived Q))
      · exact h1.trans (one_dvd _)
      · exact h1
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h2)
  obtain ⟨c, hc⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp hz)
  obtain ⟨U, hU, -⟩ := hT
  have hUne : U ≠ ⊥ := by
    rintro rfl
    rw [finrank_bot] at hU
    omega
  obtain ⟨v, -, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  have hcv : c ^ 2 = 1 := by
    have h1 : (z : V ≃ₗ[K] V) ((z : V ≃ₗ[K] V) v) = v := by
      have h : ((z : V ≃ₗ[K] V) ^ 2) v = v := by
        simpa using congrArg (fun e : ↥(orthDerived Q) => ((e : V ≃ₗ[K] V)) v) hz2
      rwa [pow_two, LinearEquiv.mul_apply] at h
    rw [hc, hc] at h1
    have h2 : (c * c) • v = (1 : K) • v := by rw [← smul_smul, h1, one_smul]
    simpa [pow_two] using smul_left_injective K hv h2
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hcv with h | h
    · exact h
    · rw [h, neg_one_eq_one_iff.mpr (ringChar.eq K 2)]
  refine Subtype.ext (LinearEquiv.ext fun w => ?_)
  rw [hc w, hc1]
  simp

theorem injective_of_odd_primaryMultiplicity {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {S : Type} [Group S] (e : S ≃* ProjOrthDerived Q) {J : Subgroup S}
    {x : V ≃ₗ[K] V} {h : K[X]} [Fact (Irreducible h)]
    (hx : OddOrderIsometry Q 3 x) (hh : h ∈ primaryFactors x.toLinearMap)
    (hSB : specialBlock Q x h ≤ orthDerived Q)
    (hkerq : ∀ z ∈ (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))).ker,
      z ^ 2 = 1)
    {lam : ↥(specialBlock Q x h) →* ↥J}
    (hlamval : ∀ g, ((lam g : ↥J) : S) =
      e.symm ((QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))
        (Subgroup.inclusion hSB g)))
    {H : Type} [Group H] (ε : ↥(specialBlock Q x h) ≃* H) (φ : H →* ↥J)
    (hφε : ∀ w, φ (ε w) = lam w) (hodd : Odd (primaryMultiplicity x.toLinearMap h)) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨g₁, rfl⟩ := ε.surjective z
  rw [hφε] at hz
  have h1 : (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))
      (Subgroup.inclusion hSB g₁) = 1 := by
    have h2 := hlamval g₁
    rw [hz] at h2
    have h3 : e.symm ((QuotientGroup.mk' ((scalars K V).subgroupOf
      (orthDerived Q))) (Subgroup.inclusion hSB g₁)) = 1 := h2.symm
    simpa using h3
  have hmemker : Subgroup.inclusion hSB g₁ ∈
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))).ker := h1
  have hsc : (g₁ : V ≃ₗ[K] V) ∈ scalars K V := by
    have h4 := hmemker
    rw [QuotientGroup.ker_mk'] at h4
    exact Subgroup.mem_subgroupOf.mp h4
  have hsq : (g₁ : V ≃ₗ[K] V) ^ 2 = 1 := by
    have h5 := congrArg Subtype.val (hkerq _ hmemker)
    simpa using h5
  rw [eq_one_of_scalar_of_odd hx hh hodd hsc hsq, map_one]

theorem selfDual_of_block {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hdim : finrank K V = 8) {m n : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m)
    (hn : Odd n) (hn3 : 3 ≤ n) (hmn : m ∣ n)
    {y : V ≃ₗ[K] V} (hy : OddOrderIsometry Q 3 y) (hy1 : y ≠ 1)
    {h : K[X]} (hh : h ∈ primaryFactors y.toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q y h))
    {J : Subgroup (ProjOrthDerived Q)}
    (hJ : J = componentImage Q y h)
    (hcard : Nat.card (J ⧸ Subgroup.center J) = ordTwistedA 2 (2 ^ n)) :
    n = m ∧ h = reciprocalPolynomial h ∧ h.natDegree = 2 ∧
      primaryMultiplicity y.toLinearMap h = 3 := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hm1 : 1 ≤ m := by
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [hK] at h2
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at h2
      omega
    omega
  obtain ⟨-, hcenter, hcardS, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  let ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  have hkerρ : ρ.ker = (scalars K V).subgroupOf (orthDerived Q) := QuotientGroup.ker_mk' _
  have hkerc : ρ.ker ≤ Subgroup.center ↥(orthDerived Q) := by rw [hkerρ, hcenter]
  have hkerq : ∀ z ∈ ρ.ker, z ^ 2 = 1 := by
    intro z hz
    rw [hkerρ] at hz
    have h1 : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣
        Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := orderOf_dvd_natCard _
    have h2 : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣ 2 := by
      have hpos : 0 < Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := Nat.card_pos
      interval_cases hc : Nat.card ↥((scalars K V).subgroupOf (orthDerived Q))
      · exact h1.trans (one_dvd _)
      · exact h1
    have h3 := orderOf_dvd_iff_pow_eq_one.mp h2
    exact congrArg Subtype.val h3
  have hSB : specialBlock Q y h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  obtain ⟨lam, hlam, hlamker, hlamval⟩ :=
    exists_specialBlock_hom_onto (MulEquiv.refl (ProjOrthDerived Q)) (J := J) y h hSB
      (by rw [hJ]; simp) hkerc
  obtain ⟨hω0, hωord⟩ := hy.orderOf_root Nat.prime_three hh hne1
  by_cases hself : h = reciprocalPolynomial h
  ·
    set k : ℕ := primaryMultiplicity y.toLinearMap h with hk
    obtain ⟨hdeg, b, hb⟩ := exists_selfDual_matrix_data hy hh hne1 hself (m := k) rfl
    obtain ⟨ε, hε⟩ := exists_specialBlock_equiv_SU hy hh b hb
    obtain ⟨φ, hφs, hφk, hφε⟩ := exists_phi_of_mulEquiv _ ε lam hlam hlamker
    have hfin : finrank K (AdjoinRoot h) = h.natDegree := by
      rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
        AdjoinRoot.powerBasis_dim]
    have hcardE : Nat.card (AdjoinRoot h) = Nat.card K ^ h.natDegree := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot h), hfin]
    have hcardQ : Nat.card (AdjoinRoot h) = (2 ^ m) ^ 2 := by
      rw [hcardE, hdeg, hK]
    have hqSU : CFSG.IsQuasisimple ↥(StatedSU k (Nat.card K) (AdjoinRoot h)) :=
      CFSG.IsQuasisimple.of_mulEquiv ε.symm hq
    have hqAsm : CFSG.Assembly.IsQuasisimple ↥(StatedSU k (Nat.card K) (AdjoinRoot h)) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        hqSU
    have hperf : Group.IsPerfect ↥(StatedSU k (Nat.card K) (AdjoinRoot h)) :=
      Group.isPerfect_def.mpr hqAsm.1
    have hk2 : 2 ≤ k :=
      CFSG.LieType.SemisimpleCentralizers.OrderThree.two_le_of_isQuasisimple_statedSU hqAsm
    have hyord : orderOf y = 3 := orderOf_eq_prime hy.pow_eq_one hy1
    have hk4 : 2 * k ≤ 8 := by
      have h := CFSG.RankThree.PartOne.S15K.two_mul_multiplicity_le_finrank hQ
        Nat.prime_three (by norm_num) (by rw [hring]; norm_num) hy.mem hyord hh hne1
      rw [hdim] at h
      exact h
    have hk1 : 1 ≤ k := by omega
    have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m (AdjoinRoot h) :=
      ⟨Nat.prime_two, hm1, by rw [hcardQ, ← pow_mul, mul_comm]⟩
    haveI : CharP (AdjoinRoot h) 2 := hdata.charP
    haveI : Finite (AdjoinRoot h) := hdata.finite
    have hZodd' : Odd (Nat.card ↥(Subgroup.center
        (StatedSU k (2 ^ m) (AdjoinRoot h)))) := by
      rcases (show k = 2 ∨ 3 ≤ k by omega) with hk2' | hk3
      · rw [hk2', CFSG.ComponentClassification.RankTwoClassical.center_statedSU_two_eq_bot
          hcardQ, Subgroup.card_bot]
        exact odd_one
      · rw [CFSG.LieType.SemisimpleCentralizers.HeldLang.center_statedSU_eq hdata hk3]
        exact CFSG.LieType.SemisimpleCentralizers.HeldLang.odd_card_subgroupOf_scalars hcardQ
          (Even.pow_of_ne_zero (by norm_num : Even 2) (by omega)) (by positivity) _
    have hZodd : Odd (Nat.card ↥(Subgroup.center
        (StatedSU k (Nat.card K) (AdjoinRoot h)))) := by
      rw [← hK] at hZodd'
      exact hZodd'
    have hvX' := CFSG.LieType.SemisimpleCentralizers.HeldLang.padicValNat_card_statedSU
      (K := AdjoinRoot h) (a := m) (d := k) hm1 hk1 hcardQ
    have hvX : padicValNat 2 (Nat.card (StatedSU k (Nat.card K) (AdjoinRoot h))) =
        m * (k * (k - 1) / 2) := by
      simpa [hK] using hvX'
    have hXcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (StatedSU k (Nat.card K) (AdjoinRoot h)))
    have hZ0 : padicValNat 2 (Nat.card ↥(Subgroup.center
        (StatedSU k (Nat.card K) (AdjoinRoot h)))) = 0 :=
      padicValNat.eq_zero_of_not_dvd (by simpa [even_iff_two_dvd] using hZodd.not_two_dvd_nat)
    have hvquot : padicValNat 2 (Nat.card
        (↥(StatedSU k (Nat.card K) (AdjoinRoot h)) ⧸
          Subgroup.center (StatedSU k (Nat.card K) (AdjoinRoot h)))) =
        m * (k * (k - 1) / 2) := by
      have hpos1 : 0 < Nat.card (↥(StatedSU k (Nat.card K) (AdjoinRoot h)) ⧸
          Subgroup.center (StatedSU k (Nat.card K) (AdjoinRoot h))) := Nat.card_pos
      have hpos2 : 0 < Nat.card ↥(Subgroup.center
          (StatedSU k (Nat.card K) (AdjoinRoot h))) := Nat.card_pos
      rw [hXcard, padicValNat.mul hpos1.ne' hpos2.ne', hZ0, add_zero] at hvX
      exact hvX
    obtain ⟨eZ⟩ :=
      CFSG.LieType.SemisimpleCentralizers.OrderThree.nonempty_quotientCenter_mulEquiv_of_surjective
        hperf φ hφs hφk
    have hvJ : padicValNat 2 (Nat.card (J ⧸ Subgroup.center J)) = m * (k * (k - 1) / 2) := by
      have hJcard : Nat.card (J ⧸ Subgroup.center J) = Nat.card
          (↥(StatedSU k (Nat.card K) (AdjoinRoot h)) ⧸
            Subgroup.center (StatedSU k (Nat.card K) (AdjoinRoot h))) :=
        Nat.card_congr eZ.symm.toEquiv
      rw [hJcard]
      exact hvquot
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hvord : padicValNat 2 (ordTwistedA 2 (2 ^ n)) = 3 * n := by
      rw [CFSG.ClassicalInvolution.RouteD.TWR.padicValNat_ordTwistedA (p := 2) (q := 2 ^ n)
        (f := n) (n := 2) rfl (by omega) (by norm_num)]
      ring
    have hEq : m * (k * (k - 1) / 2) = 3 * n := by
      rw [← hvJ, hcard]
      exact hvord
    have hmle : m ≤ n := Nat.le_of_dvd hn.pos hmn
    have hk4' : k ≤ 4 := by omega
    have hkm : k = 3 ∧ n = m := by
      obtain ⟨a, ha⟩ := hn
      interval_cases k <;> omega
    obtain ⟨hk3, hnm⟩ := hkm
    exact ⟨hnm, hself, hdeg, hk3⟩
  ·
    have hdeg1 : h.natDegree = 1 := natDegree_eq_one_of_primary_paired hy hh hne1 hself
    have hfin : finrank K (AdjoinRoot h) = h.natDegree := by
      rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
        AdjoinRoot.powerBasis_dim]
    have hcardE : Nat.card (AdjoinRoot h) = Nat.card K ^ h.natDegree := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot h), hfin]
    have hEcard : Nat.card (AdjoinRoot h) = 2 ^ m := by
      rw [hcardE, hdeg1, hK, pow_one]
    have h3dvd : 3 ∣ Nat.card (AdjoinRoot h)ˣ := by
      rw [← hωord]
      exact orderOf_dvd_natCard _
    rw [Nat.card_units, hEcard] at h3dvd
    exact (CFSG.LocalAnalysis.GLTheoremA.three_not_dvd_two_pow_sub_one_of_odd hm h3dvd).elim

theorem three_dvd_card_center_of_block {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hdim : finrank K V = 8) {m n : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m)
    (hn : Odd n) (hn3 : 3 ≤ n) (hmn : m ∣ n)
    {y : V ≃ₗ[K] V} (hy : OddOrderIsometry Q 3 y) (hy1 : y ≠ 1)
    {h : K[X]} (hh : h ∈ primaryFactors y.toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q y h))
    {J : Subgroup (ProjOrthDerived Q)}
    (hJ : J = componentImage Q y h)
    (hcard : Nat.card (J ⧸ Subgroup.center J) = ordTwistedA 2 (2 ^ n)) :
    3 ∣ Nat.card ↥(Subgroup.center ↥J) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨-, hcenter, hcardS, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨hnm, hself, hdeg, hmult⟩ :=
    selfDual_of_block hQ hT hdim hK hm hn hn3 hmn hy hy1 hh hne1 hq hJ hcard
  let ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  have hkerρ : ρ.ker = (scalars K V).subgroupOf (orthDerived Q) := QuotientGroup.ker_mk' _
  have hkerc : ρ.ker ≤ Subgroup.center ↥(orthDerived Q) := by rw [hkerρ, hcenter]
  have hkerq : ∀ z ∈ ρ.ker, z ^ 2 = 1 := by
    intro z hz
    rw [hkerρ] at hz
    have h1 : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣
        Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := orderOf_dvd_natCard _
    have h2 : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣ 2 := by
      have hpos : 0 < Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := Nat.card_pos
      interval_cases hc : Nat.card ↥((scalars K V).subgroupOf (orthDerived Q))
      · exact h1.trans (one_dvd _)
      · exact h1
    have h3 := orderOf_dvd_iff_pow_eq_one.mp h2
    exact congrArg Subtype.val h3
  have hSB : specialBlock Q y h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  obtain ⟨lam, hlam, hlamker, hlamval⟩ :=
    exists_specialBlock_hom_onto (MulEquiv.refl (ProjOrthDerived Q)) (J := J) y h hSB
      (by rw [hJ]; simp) hkerc
  obtain ⟨-, b, hb⟩ := exists_selfDual_matrix_data hy hh hne1 hself (m := 3) hmult
  obtain ⟨ε, hε⟩ := exists_specialBlock_equiv_SU hy hh b hb
  obtain ⟨φ, hφs, hφk, hφε⟩ := exists_phi_of_mulEquiv _ ε lam hlam hlamker
  have hodd : Odd (primaryMultiplicity y.toLinearMap h) := by
    rw [hmult]
    exact ⟨1, rfl⟩
  have hinj : Function.Injective φ :=
    injective_of_odd_primaryMultiplicity (MulEquiv.refl (ProjOrthDerived Q)) hy hh hSB hkerq
      hlamval ε φ hφε hodd
  let eJ : ↥(StatedSU 3 (Nat.card K) (AdjoinRoot h)) ≃* ↥J :=
    MulEquiv.ofBijective φ ⟨hinj, hφs⟩
  have hZcard : Nat.card ↥(Subgroup.center ↥J) =
      Nat.card ↥(Subgroup.center (StatedSU 3 (2 ^ m) (AdjoinRoot h))) := by
    have h1 : Nat.card ↥(Subgroup.center ↥J) =
        Nat.card ↥(Subgroup.center (StatedSU 3 (Nat.card K) (AdjoinRoot h))) :=
      Nat.card_congr (Subgroup.centerCongr eJ).symm.toEquiv
    rw [h1, ← hK]
  have hcardQ : Nat.card (AdjoinRoot h) = (2 ^ m) ^ 2 := by
    have hfin : finrank K (AdjoinRoot h) = h.natDegree := by
      rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
        AdjoinRoot.powerBasis_dim]
    have hcardE : Nat.card (AdjoinRoot h) = Nat.card K ^ h.natDegree := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot h), hfin]
    rw [hcardE, hdeg, hK]
  have hcenter3 : Nat.card ↥(Subgroup.center (StatedSU 3 (2 ^ m) (AdjoinRoot h))) = 3 :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.card_center_statedSU_three
      (f := m) hm (by omega) hcardQ
  rw [hZcard, hcenter3]

theorem exists_selfDual_block_of_component {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hV : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) (hdim : Module.finrank K V = 8)
    {m n : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m) (hn : Odd n) (hn3 : 3 ≤ n) (hmn : m ∣ n)
    {y : ↥(orthDerived Q)} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    {J : Subgroup (ProjOrthDerived Q)}
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer
      ({(QuotientGroup.mk y : ProjOrthDerived Q)} : Set (ProjOrthDerived Q))))
    (hcard : Nat.card (↥J ⧸ Subgroup.center ↥J) = CFSG.Open.ordTwistedA 2 (2 ^ n)) :
    n = m ∧ ∃ h : K[X], h ∈ primaryFactors (y : V ≃ₗ[K] V).toLinearMap ∧ h ≠ X - 1 ∧
      h = reciprocalPolynomial h ∧ h.natDegree = 2 ∧
      primaryMultiplicity (y : V ≃ₗ[K] V).toLinearMap h = 3 ∧
      CFSG.IsQuasisimple ↥(specialBlock Q (y : V ≃ₗ[K] V) h) ∧
      J = componentImage Q (y : V ≃ₗ[K] V) h := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := m)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hpℓ : 3 ≠ ringChar K := by rw [hring]; norm_num
  have hy : OddOrderIsometry Q 3 (y : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_pow_eq_one Nat.prime_three hpℓ hQ y hy3
  have hy1' : (y : V ≃ₗ[K] V) ≠ 1 := fun h => hy1 (Subtype.ext h)
  let ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  have hinj : Function.Injective ρ := injective_mk'_of_charTwo hQ hT
  have hsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  let eρ : ↥(orthDerived Q) ≃* ProjOrthDerived Q := MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩
  have hcent : Subgroup.centralizer ({(QuotientGroup.mk y : ProjOrthDerived Q)} :
      Set (ProjOrthDerived Q)) =
      (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))).map ρ := by
    have h := CFSG.Walter.map_centralizer_singleton_mulEquiv eρ y
    exact h.symm
  rcases CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.orth_component_cases
      Nat.prime_three (by norm_num) hQ hpℓ y hy3 hcent J hJ with
    ⟨h, hh, hne1, hq, hJh⟩ | ⟨F, hF, hJF⟩
  · obtain ⟨hnm, hself, hdeg, hmult⟩ :=
      selfDual_of_block hQ hT hdim hK hm hn hn3 hmn hy hy1' hh hne1 hq hJh hcard
    exact ⟨hnm, h, hh, hne1, hself, hdeg, hmult, hq, hJh⟩
  · exact (false_of_fixedLayer hQ hV hdim hK hm hn hn3 hmn hy hy1' ⟨F, hF, hJF⟩ hcard).elim

theorem three_dvd_card_center_of_component {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hV : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) (hdim : Module.finrank K V = 8)
    {m n : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m) (hn : Odd n) (hn3 : 3 ≤ n) (hmn : m ∣ n)
    {x : ProjOrthDerived Q} (hx : orderOf x = 3) {J : Subgroup (ProjOrthDerived Q)}
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({x} : Set (ProjOrthDerived Q))))
    (hcard : Nat.card (↥J ⧸ Subgroup.center ↥J) = CFSG.Open.ordTwistedA 2 (2 ^ n)) :
    3 ∣ Nat.card ↥(Subgroup.center ↥J) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := m)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hpℓ : 3 ≠ ringChar K := by rw [hring]; norm_num
  obtain ⟨-, hcenter, hcardS, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  let ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  obtain ⟨y, ⟨hya, hyp⟩, -, hcent⟩ := hlift 3 Nat.prime_three (by norm_num) x hx
  have hy3 : y ^ 3 = 1 := by rw [← hyp]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h
    have : orderOf y = 1 := by rw [h]; exact orderOf_one
    omega
  have hy1' : (y : V ≃ₗ[K] V) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hy : OddOrderIsometry Q 3 (y : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_pow_eq_one Nat.prime_three hpℓ hQ y hy3
  have hcent' : Subgroup.centralizer ({(y : ProjOrthDerived Q)} : Set (ProjOrthDerived Q)) =
      (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))).map ρ := by
    rw [hya]
    exact hcent
  have hJ' : CFSG.Open.IsComponentOf J
      (Subgroup.centralizer ({(y : ProjOrthDerived Q)} : Set (ProjOrthDerived Q))) := by
    rw [hya]
    exact hJ
  rcases CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.orth_component_cases
      Nat.prime_three (by norm_num) hQ hpℓ y hy3 hcent' J hJ' with
    ⟨h, hh, hne1, hq, hJh⟩ | ⟨F, hF, hJF⟩
  · exact three_dvd_card_center_of_block hQ hT hdim hK hm hn hn3 hmn hy hy1' hh hne1 hq hJh hcard
  · exact (false_of_fixedLayer hQ hV hdim hK hm hn hn3 hmn hy hy1' ⟨F, hF, hJF⟩ hcard).elim

end CFSG.LocalAnalysis.GLTheoremA.CanonU3.OrthMinus
