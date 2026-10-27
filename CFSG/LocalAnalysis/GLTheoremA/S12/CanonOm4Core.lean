module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClOrthCases
public import CFSG.HardMathSupport.Dickson.Bal207.OrthFixedType
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonOm4

open Polynomial Module QuadraticMap CFSG.Open
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.K159 CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.GroupTheory.WeirSylow CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
open scoped MatrixGroups

private theorem card_quot_le {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    Nat.card (G ⧸ H) ≤ Nat.card G :=
  Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card H)

private theorem ordTwistedD_lt_ordA : ordTwistedD 4 4 < ordA 5 4 := by decide

private theorem omega_arith {m : ℕ} (hm : 3 ≤ m) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {N : ℕ}
    (h : (N : ℤ) = 4 ^ (m * (m + 1)) * (4 ^ (m + 1) - ε) *
      ∏ i ∈ Finset.Icc 1 m, (((4 : ℤ) ^ 2) ^ i - 1)) :
    N ≠ ordA 5 4 ∧ (N = ordTwistedD 4 4 → m = 3 ∧ ε = -1) := by
  have hdvd : ((4 ^ (m * (m + 1)) : ℕ) : ℤ) ∣ (N : ℤ) :=
    ⟨(4 ^ (m + 1) - ε) * ∏ i ∈ Finset.Icc 1 m, (((4 : ℤ) ^ 2) ^ i - 1), by
      rw [h]; push_cast; ring⟩
  have hdvdN : 4 ^ (m * (m + 1)) ∣ N := Int.natCast_dvd_natCast.mp hdvd
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  · obtain rfl : m = 3 := by omega
    rcases hε with rfl | rfl
    · have hv : (N : ℤ) = 67010895544320000 := by rw [h]; decide
      have hv' : N = 67010895544320000 := by exact_mod_cast hv
      subst hv'
      exact ⟨by decide, fun hN => absurd hN (by decide)⟩
    · have hv : (N : ℤ) = 67536471195648000 := by rw [h]; decide
      have hv' : N = 67536471195648000 := by exact_mod_cast hv
      subst hv'
      exact ⟨by decide, fun _ => ⟨rfl, rfl⟩⟩
  · have h20 : 4 ^ 20 ∣ N :=
      (Nat.pow_dvd_pow 4 (Nat.mul_le_mul hm4 (by omega : 5 ≤ m + 1))).trans hdvdN
    refine ⟨fun hN => ?_, fun hN => ?_⟩ <;> rw [hN] at h20 <;> exact absurd h20 (by decide)

private theorem su_arith {m z M : ℕ} (hm : 6 ≤ m) (hz : z ∣ 5)
    (h : ((M * z : ℕ) : ℤ) = (4 : ℤ) ^ (m * (m - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 m, ((4 : ℤ) ^ i - (-1) ^ i)) :
    M ≠ ordA 5 4 ∧ M ≠ ordTwistedD 4 4 := by
  have hz15 : z = 1 ∨ z = 5 := (Nat.dvd_prime Nat.prime_five).1 hz
  have hdvd : ((4 ^ (m * (m - 1) / 2) : ℕ) : ℤ) ∣ ((M * z : ℕ) : ℤ) :=
    ⟨∏ i ∈ Finset.Icc 2 m, ((4 : ℤ) ^ i - (-1) ^ i), by rw [h]; push_cast; ring⟩
  have hdvdN : 4 ^ (m * (m - 1) / 2) ∣ M * z := Int.natCast_dvd_natCast.mp hdvd
  rcases Nat.lt_or_ge m 7 with hm7 | hm7
  · obtain rfl : m = 6 := by omega
    have hv : ((M * z : ℕ) : ℤ) = 1120527288631296000000 := by rw [h]; decide
    have hv' : M * z = 1120527288631296000000 := by exact_mod_cast hv
    rcases hz15 with rfl | rfl <;> refine ⟨fun hM => ?_, fun hM => ?_⟩ <;> rw [hM] at hv' <;>
      exact absurd hv' (by decide)
  · have h21 : 21 ≤ m * (m - 1) / 2 := by
      have : 7 * 6 ≤ m * (m - 1) := Nat.mul_le_mul hm7 (by omega)
      omega
    have h4 : 4 ^ 21 ∣ M * z := (Nat.pow_dvd_pow 4 h21).trans hdvdN
    rcases hz15 with rfl | rfl <;> refine ⟨fun hM => ?_, fun hM => ?_⟩ <;> rw [hM] at h4 <;>
      exact absurd h4 (by decide)

section Space

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem block_card_ne (hK4 : Nat.card K = 4) (hx : OddOrderIsometry Q 5 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    Nat.card (↥(componentImage Q x h) ⧸ Subgroup.center ↥(componentImage Q x h)) ≠ ordA 5 4 ∧
      Nat.card (↥(componentImage Q x h) ⧸ Subgroup.center ↥(componentImage Q x h)) ≠
        ordTwistedD 4 4 := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : CharP K 2 := charP_two_of_card_four hK4
  have hFΩ : specialBlock Q x h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  have hc : Nat.card (↥(componentImage Q x h) ⧸ Subgroup.center ↥(componentImage Q x h)) =
      Nat.card (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) :=
    card_quotient_center_map_projective hFΩ hq.1.commutator_eq_top
  rw [hc]
  have hself := selfDual_of_dvd_card_add_one hx (by rw [hK4]) hh hne1
  have hdeg2 := natDegree_eq_two_of_selfDual hx hK4 hh hne1 hself
  obtain ⟨d, ℓ, f, hU, B, hdeg, hq0, hchar, -, hBsymm, hBl, ⟨e₁⟩⟩ :=
    selfDual_unitary_data hx hh hne1 hself
  have hd1 : d = 1 := by omega
  subst hd1
  have hℓ : ℓ = 2 := hchar.symm.trans (ringChar.eq K 2)
  subst hℓ
  have hf : f = 2 := Nat.pow_right_injective le_rfl (hq0.symm.trans hK4)
  subst hf
  haveI := hU.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hU.charP
  have hm := two_le_multiplicity_of_quasisimple hx hh hq
  have hN := ordTwistedD_lt_ordA
  have hcardSU := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl
    (n := primaryMultiplicity x.toLinearMap h) rfl (by omega)).2.1
  have hFcard : (Nat.card ↥(specialBlock Q x h) : ℤ) =
      (4 : ℤ) ^ (primaryMultiplicity x.toLinearMap h * (primaryMultiplicity x.toLinearMap h - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 (primaryMultiplicity x.toLinearMap h), ((4 : ℤ) ^ i - (-1) ^ i) := by
    rw [Nat.card_congr e₁.toEquiv, hcardSU]
    norm_num
  rcases Nat.lt_or_ge (primaryMultiplicity x.toLinearMap h) 6 with hm6 | hm6
  ·
    have hlt : (Nat.card ↥(specialBlock Q x h) : ℤ) < ordTwistedD 4 4 := by
      rw [hFcard]
      generalize primaryMultiplicity x.toLinearMap h = m at hm hm6
      interval_cases m <;> decide
    have h1 := card_quot_le (Subgroup.center ↥(specialBlock Q x h))
    have h2 : Nat.card ↥(specialBlock Q x h) < ordTwistedD 4 4 := by exact_mod_cast hlt
    omega
  ·
    have hE : Nat.card (AdjoinRoot h) = (2 ^ (2 * 1)) ^ 2 := by
      rw [hU.card, ← pow_mul, mul_comm]
    obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBsymm hBl
    obtain ⟨e₂⟩ :=
      CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid hU e₀ he₀
    have hS : CFSG.LieType.Universal.Unitary.SUid hU.barEquiv
        (primaryMultiplicity x.toLinearMap h) =
        StatedSU (primaryMultiplicity x.toLinearMap h) (2 ^ (2 * 1)) (AdjoinRoot h) := by
      rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hU]
      exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE _
    let e₃ : ↥(specialBlock Q x h) ≃*
        ↥(StatedSU (primaryMultiplicity x.toLinearMap h) (2 ^ (2 * 1)) (AdjoinRoot h)) :=
      (e₁.trans e₂).trans (MulEquiv.subgroupCongr hS)
    have hZ := CFSG.StandardType.card_center_statedSU_dvd hE (by omega :
      4 ≤ primaryMultiplicity x.toLinearMap h)
    have hq' : Nat.card (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h)) =
        Nat.card (↥(StatedSU (primaryMultiplicity x.toLinearMap h) (2 ^ (2 * 1)) (AdjoinRoot h)) ⧸
          Subgroup.center ↥(StatedSU (primaryMultiplicity x.toLinearMap h) (2 ^ (2 * 1))
            (AdjoinRoot h))) :=
      Nat.card_congr (QuotientGroup.congr _ _ e₃ (Subgroup.map_center_eq e₃)).toEquiv
    have hmul := (Subgroup.center ↥(StatedSU (primaryMultiplicity x.toLinearMap h) (2 ^ (2 * 1))
      (AdjoinRoot h))).card_eq_card_quotient_mul_card_subgroup
    rw [hq']
    refine su_arith hm6 (hZ.trans (dvd_of_eq (by norm_num))) ?_
    rw [← hmul, ← Nat.card_congr e₃.toEquiv]
    exact hFcard

theorem split_card_le (hK4 : Nat.card K = 4) {p : ℕ} (hx : OddOrderIsometry Q p x)
    (e : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ≃*
      DeterminantIsometries K)
    (hF : ∀ i : Fin 2, supportedFactor hx (splitFourFactors e i) ≤ orthDerived Q) (i : Fin 2) :
    Nat.card (↥(fixedFactorImage hx (splitFourFactors e i)) ⧸
      Subgroup.center ↥(fixedFactorImage hx (splitFourFactors e i))) ≤ 60 := by
  obtain ⟨φ⟩ := nonempty_equiv_splitFactor hx e i
  have hperf : commutator ↥(supportedFactor hx (splitFourFactors e i)) = ⊤ :=
    commutator_eq_top_of_mulEquiv φ.symm
      (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K
        (by omega)).commutator_eq_top
  have h : Nat.card (↥(fixedFactorImage hx (splitFourFactors e i)) ⧸
      Subgroup.center ↥(fixedFactorImage hx (splitFourFactors e i))) =
      Nat.card (↥(supportedFactor hx (splitFourFactors e i)) ⧸
        Subgroup.center ↥(supportedFactor hx (splitFourFactors e i))) :=
    card_quotient_center_map_projective (hF i) hperf
  rw [h]
  calc _ ≤ Nat.card ↥(supportedFactor hx (splitFourFactors e i)) := card_quot_le _
    _ = Nat.card SL(2, K) := Nat.card_congr φ.toEquiv
    _ = 60 := card_sl_two_of_card_four hK4

theorem fixed_card (hK4 : Nat.card K = 4) [Nontrivial V] (hQ : (polarBilin Q).Nondegenerate)
    (hx : OddOrderIsometry Q 5 x) (hlist : FixedLayerListed Q x) :
    Nat.card (↥(fixedComponentImage Q x) ⧸ Subgroup.center ↥(fixedComponentImage Q x)) ≠
        ordA 5 4 ∧
      (Nat.card (↥(fixedComponentImage Q x) ⧸ Subgroup.center ↥(fixedComponentImage Q x)) =
          ordTwistedD 4 4 →
        finrank K (fixedSpace x) = 8 ∧ ¬ IsPlusType (Q.comp (fixedSpace x).subtype)) := by
  classical
  haveI : CharP K 2 := charP_two_of_card_four hK4
  have hR : (polarBilin (Q.comp (fixedSpace x).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hW3 : 3 ≤ finrank K (fixedSpace x) := hlist.1
  haveI : Nontrivial (fixedSpace x) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  let e : ↥(fixedComponentImage Q x) ≃* ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
    fixedComponentImageEquiv hQ hx
  have hc : Nat.card (↥(fixedComponentImage Q x) ⧸ Subgroup.center ↥(fixedComponentImage Q x)) =
      Nat.card (↥(orthDerived (Q.comp (fixedSpace x).subtype)) ⧸
        Subgroup.center ↥(orthDerived (Q.comp (fixedSpace x).subtype))) :=
    Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv
  rw [hc]
  obtain ⟨r, hr⟩ := CFSG.StandardType.OrthRestOdd.even_finrank_of_regular _ hR
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hdim : finrank K (fixedSpace x) = 2 * (m + 1) := by omega
  have hq : (Nat.card K : ℤ) = 4 := by exact_mod_cast hK4
  have hle : orthDerived (Q.comp (fixedSpace x).subtype) ≤
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) :=
    Subgroup.commutator_le_self _
  have hN := ordTwistedD_lt_ordA
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  ·
    have hm1 : 1 ≤ m := by omega
    have hO : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype)) : ℤ) < ordTwistedD 4 4 := by
      by_cases hp : IsPlusType (Q.comp (fixedSpace x).subtype)
      · rw [natCard_orthogonalGroup_of_type hR hdim (Or.inl ⟨rfl, hp⟩), hq]
        interval_cases m <;> decide
      · rw [natCard_orthogonalGroup_of_type hR hdim (Or.inr ⟨rfl, hp⟩), hq]
        interval_cases m <;> decide
    have h1 := card_quot_le (Subgroup.center ↥(orthDerived (Q.comp (fixedSpace x).subtype)))
    have h2 := Subgroup.card_le_of_le hle
    have h3 : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype)) < ordTwistedD 4 4 := by exact_mod_cast hO
    exact ⟨by omega, fun h => by omega⟩
  ·
    obtain ⟨T, hT3, hT0⟩ :=
      CFSG.StandardType.OrthRestOdd.exists_totallySingular_three _ hR (by omega)
    have hZ := center_orthDerived_eq_bot hR ⟨T, hT3, hT0⟩
    have hΩ := card_orthDerived_mul_two _ hR ⟨T, hT3, hT0⟩
    rw [card_quotient_center_of_center_eq_bot hZ]
    have key : ∀ ε : ℤ, (ε = 1 ∧ IsPlusType (Q.comp (fixedSpace x).subtype)) ∨
        (ε = -1 ∧ ¬ IsPlusType (Q.comp (fixedSpace x).subtype)) →
        ((Nat.card ↥(orthDerived (Q.comp (fixedSpace x).subtype)) : ℕ) : ℤ) =
          4 ^ (m * (m + 1)) * (4 ^ (m + 1) - ε) *
            ∏ i ∈ Finset.Icc 1 m, (((4 : ℤ) ^ 2) ^ i - 1) := by
      intro ε hε
      have h1 := natCard_orthogonalGroup_of_type hR hdim hε
      rw [hq] at h1
      have h2 : ((Nat.card ↥(orthDerived (Q.comp (fixedSpace x).subtype)) : ℕ) : ℤ) * 2 =
          (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :
            ℤ) := by exact_mod_cast hΩ
      rw [h1] at h2
      linarith
    by_cases hp : IsPlusType (Q.comp (fixedSpace x).subtype)
    · obtain ⟨hA, hD⟩ := omega_arith hm3 (Or.inl rfl) (key 1 (Or.inl ⟨rfl, hp⟩))
      exact ⟨hA, fun h => absurd (hD h).2 (by norm_num)⟩
    · obtain ⟨hA, hD⟩ := omega_arith hm3 (Or.inr rfl) (key (-1) (Or.inr ⟨rfl, hp⟩))
      exact ⟨hA, fun h => ⟨by have := (hD h).1; omega, hp⟩⟩

theorem others_even [CharP K 2] (hQ : (polarBilin Q).Nondegenerate) (hx : OddOrderIsometry Q 5 x)
    (hpq : 5 ∣ Nat.card K + 1) (hV : ¬ IsPlusType Q)
    (hW : ¬ IsPlusType (Q.comp (fixedSpace x).subtype)) {s : ℕ}
    (hs : finrank K (fixedSpace x) = 2 * s) (hs1 : 1 ≤ s) (hx1 : x ≠ 1) :
    ∃ k : ℕ, finrank K V = 2 * s + 2 * k ∧ Even k ∧ 1 ≤ k := by
  classical
  obtain ⟨hcompl, horth⟩ := hx.fixed_others
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  obtain ⟨n, hn⟩ := CFSG.StandardType.OrthRestOdd.even_finrank_of_regular Q hQ
  have hRfix : ∀ u ∈ othersSpace x.toLinearMap (X - 1), x u = u → u = 0 := fun u hu hxu =>
    (Submodule.disjoint_def.1 hcompl.disjoint) u (mem_fixedSpace.2 hxu) hu
  have hRreg : RegOn Q (othersSpace x.toLinearMap (X - 1)) := by
    intro u hu hperp
    refine hx.regular u fun v => ?_
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
    rw [QuadraticMap.polar_add_right, hperp r hr, QuadraticMap.polar_comm Q u w,
      horth w hw u hu, add_zero]
  have hRdim : finrank K (othersSpace x.toLinearMap (X - 1)) = 2 * (n - s) := by omega
  have hRtype := isPlusType_iff_even_of_fixedFree hx Nat.prime_five (by norm_num) hpq (n - s)
    (othersSpace x.toLinearMap (X - 1))
    (fun u hu => CFSG.HardMathSupport.Dickson.Bal207.OrthFix.othersSpace_invariant hu) hRreg hRfix
    hRdim
  have hk1 : 1 ≤ n - s := by
    by_contra hk0
    apply hx1
    have hRb : othersSpace x.toLinearMap (X - 1) = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have hWtop : fixedSpace x = ⊤ := by
      have h := hcompl.sup_eq_top
      rwa [hRb, sup_bot_eq] at h
    ext v
    have : v ∈ fixedSpace x := hWtop ▸ Submodule.mem_top
    exact mem_fixedSpace.1 this
  have eV : Q.IsometryEquiv ((Q.comp (fixedSpace x).subtype).prod
      (Q.comp (othersSpace x.toLinearMap (X - 1)).subtype)) :=
    (isometryTop Q).trans ((isometryOfEq Q hcompl.sup_eq_top.symm).trans
      (isometryEquivSup Q _ _ hcompl.disjoint horth))
  have htype : IsPlusType Q ↔ (IsPlusType (Q.comp (fixedSpace x).subtype) ↔
      IsPlusType (Q.comp (othersSpace x.toLinearMap (X - 1)).subtype)) :=
    (isPlusType_congr eV).trans
      (isPlusType_prod_iff hx.polarBilin_fixed_nondegenerate (nondegenerate_of_regOn hRreg) hs1
        hk1 hs hRdim)
  have hRplus : IsPlusType (Q.comp (othersSpace x.toLinearMap (X - 1)).subtype) := by tauto
  exact ⟨n - s, by omega, hRtype.1 hRplus, hk1⟩

end Space

theorem om4_core {K : Type} [Field K] [Finite K] (hK4 : Nat.card K = 4) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hminus : ¬ IsPlusType Q)
    (a : ProjOrthDerived Q) (ha : a ^ 5 = 1) (ha1 : a ≠ 1) (J : Subgroup (ProjOrthDerived Q))
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ ordA 5 4 ∧
      (Nat.card (↥J ⧸ Subgroup.center ↥J) = ordTwistedD 4 4 → 12 ≤ finrank K V) := by
  classical
  haveI : CharP K 2 := charP_two_of_card_four hK4
  have hring : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨U, hU3, hU0⟩ := hT
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K)
    (by have := Submodule.finrank_le U; omega)
  have hN := ordTwistedD_lt_ordA
  have h60 : 60 < ordTwistedD 4 4 := by decide
  obtain ⟨x, Rep, hx, Cset, hxa, hRep, hcomp, htype⟩ :=
    exists_components_named Nat.prime_five (by norm_num) hQ ⟨U, hU3, hU0⟩
      (by rw [hring]; norm_num) a ha ha1
  have hx1 : (x : V ≃ₗ[K] V) ≠ 1 := by
    intro h1
    apply ha1
    rw [← hxa, show x = 1 from Subtype.ext h1, QuotientGroup.mk_one]
  rcases hcomp J hJ with ⟨h, hR, hne1, hq, rfl⟩ | hJC
  · obtain ⟨h1, h2⟩ := block_card_ne hK4 hx (hRep.1 hR) hne1 hq
    exact ⟨h1, fun h => absurd h h2⟩
  · rcases htype with ⟨-, rfl⟩ | ⟨hlist, -, -, rfl⟩ | ⟨-, e, -, -, -, hF, rfl⟩
    · exact absurd hJC (Set.notMem_empty J)
    · rw [Set.mem_singleton_iff] at hJC
      subst hJC
      obtain ⟨h1, h2⟩ := fixed_card hK4 hQ hx hlist
      refine ⟨h1, fun hD => ?_⟩
      obtain ⟨hW8, hWm⟩ := h2 hD
      obtain ⟨k, hk, ⟨j, rfl⟩, hk1⟩ :=
        others_even hQ hx (by rw [hK4]) hminus hWm (s := 4) (by omega) (by norm_num) hx1
      omega
    · have hle := split_card_le hK4 hx e hF
      rcases hJC with rfl | hJC
      · have := hle 0
        exact ⟨by omega, fun h => by omega⟩
      · rw [Set.mem_singleton_iff] at hJC
        subst hJC
        have := hle 1
        exact ⟨by omega, fun h => by omega⟩

end CFSG.LocalAnalysis.GLTheoremA.CanonOm4

end
