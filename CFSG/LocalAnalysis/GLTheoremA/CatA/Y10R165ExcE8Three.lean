module

public import CFSG.RankThree.PartOne.KE6.E8T3Perx
public import CFSG.RankThree.PartOne.KE6.E6LLayer
public import CFSG.LocalAnalysis.StandardType.SupportedTorusFixedKernel
public import CFSG.LocalAnalysis.StandardType.E8SevenLayerOrderCenter
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Gen
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate1952
public import Certificates.Certificate14972
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.D4LayerAlgebraic
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E7FourLattice
public import CFSG.RankThree.PartOne.KE.E7FourStabBase
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.E8T3Torus
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KE6.Phi6Torsion
public import CFSG.RankThree.PartOne.S8.Statements
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open CFSG.HardMathSupport.Lang.TwE6Step3 (monoHom monoHom_apply monoHom_monoHom)
open CFSG.HardMathSupport.Foote.Coordinator (monoHom_sub_one)
open CFSG.HardMathSupport.Foote.Coordinator (blockP)
open CFSG.HardMathSupport.Foote.Coordinator
  (extJ' extJ'_apply_mem extJ'_apply_notMem weylMatrix_mulVec_extJ' weylMatrix_pow_mulVec_extJ')
open scoped Matrix MatrixGroups

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem natCard_ker_monoHom_cyclotomic_int {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    {P G : Matrix ι ι ℤ} (hP : P * P + P + 1 = 0) (hG : Pᵀ * G * P = G)
    (hdet : G.det ≠ 0) (q : ℤ) (hq : ((q : Ω) ^ 2 + (q : Ω) + 1) ≠ 0) :
    Nat.card (monoHom (G := Ωˣ) (q • P - 1)).ker ^ 2 =
      (q ^ 2 + q + 1).natAbs ^ Fintype.card ι := by
  have hsq := det_smul_sub_one_sq hP hG hdet q
  have hne : (((q • P - 1).det : ℤ) : Ω) ≠ 0 := by
    intro h0
    have h1 : ((((q • P - 1).det ^ 2 : ℤ) : Ω)) = 0 := by
      rw [Int.cast_pow, h0]
      norm_num
    rw [hsq] at h1
    have h2 : (((q ^ 2 + q + 1 : ℤ) : Ω) ^ Fintype.card ι) = 0 := by simpa using h1
    have hcast : (((q ^ 2 + q + 1 : ℤ) : Ω)) = (q : Ω) ^ 2 + (q : Ω) + 1 := by
      push_cast
      ring
    exact hq (by rw [← hcast]; exact (pow_eq_zero_iff'.1 h2).1)
  rw [natCard_ker_monoHom _ hne]
  have h3 := congrArg Int.natAbs hsq
  simpa only [Int.natAbs_pow] using h3

theorem natCard_ker_monoHom_cyclotomic_sub {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    {P G : Matrix ι ι ℤ} (hP : P * P - P + 1 = 0) (hG : Pᵀ * G * P = G)
    (hdet : G.det ≠ 0) {q : ℕ} (hq2 : 2 ≤ q) (hq : ((q : Ω) ^ 2 - q + 1) ≠ 0) :
    Nat.card (monoHom (G := Ωˣ) ((q : ℤ) • P - 1)).ker ^ 2 =
      (q ^ 2 - q + 1) ^ Fintype.card ι := by
  have hP' : (-P) * (-P) + (-P) + 1 = 0 := by
    rw [neg_mul_neg]
    simpa [sub_eq_add_neg] using hP
  have hG' : (-P)ᵀ * G * (-P) = G := by
    rw [Matrix.transpose_neg, neg_mul, neg_mul_neg, hG]
  have hq' : (((-(q : ℤ) : ℤ) : Ω) ^ 2 + ((-(q : ℤ) : ℤ) : Ω) + 1) ≠ 0 := by
    rw [Int.cast_neg, Int.cast_natCast, neg_sq]
    simpa [sub_eq_add_neg] using hq
  have h := natCard_ker_monoHom_cyclotomic_int hP' hG' hdet (-(q : ℤ)) hq'
  have hcast : ((q ^ 2 - q + 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - (q : ℤ) + 1 := by
    have hle : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow]
    push_cast
    ring
  rwa [show (-(q : ℤ)) • (-P) = (q : ℤ) • P by rw [neg_smul_neg],
    show ((-(q : ℤ)) ^ 2 + (-(q : ℤ)) + 1 : ℤ) = (q : ℤ) ^ 2 - (q : ℤ) + 1 by ring,
    ← hcast, Int.natAbs_natCast] at h

end Algebra

section Block

variable
  {τ : Tag} {J : Set (Fin τ.rank)} [Fintype J] [DecidableEq J]

theorem blockP_sq_sub_self_add_one {w : WeylGroup τ}
    (hJ : ∀ β ∈ parabolicRoots τ J, w • β ∈ parabolicRoots τ J)
    (hrel : ∀ x : Fin τ.rank → ℤ, w • w • x - w • x + x = 0) :
    blockP w J * blockP w J - blockP w J + 1 = 0 := by
  classical
  refine Matrix.ext_of_mulVec_single fun c => ?_
  set u : J → ℤ := Pi.single c 1
  have h2 := weylMatrix_pow_mulVec_extJ' (J := J) hJ 2 u
  have h1 := weylMatrix_mulVec_extJ' (J := J) hJ u
  have hrelx : weylMatrix w ^ 2 *ᵥ extJ' J u - weylMatrix w *ᵥ extJ' J u + extJ' J u = 0 := by
    have h := hrel (extJ' J u)
    simp only [← weylMatrix_mulVec, Matrix.mulVec_mulVec, ← pow_two] at h
    exact h
  rw [h2, h1] at hrelx
  have key : ∀ j : J, (blockP w J ^ 2 *ᵥ u) j - (blockP w J *ᵥ u) j + u j = 0 := by
    intro j
    have hj := congrFun hrelx j
    simpa [extJ', Pi.sub_apply, Pi.add_apply, j.2] using hj
  funext j
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec,
    Pi.add_apply, Pi.sub_apply]
  simpa [pow_two] using key j

end Block

section Torus

theorem dvd_card_rootSpan_inf_twistedFixedPoints_add {τ : Tag} {Ω : Type} [Field Ω]
    [IsAlgClosed Ω] (hsym : τ.symmetrizer = 1) {Fr : Ω →+* Ω} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (n : ModGL τ Ω) (hnm : n ∈ monomialSubgroup τ Ω)
    (J : Set (Fin τ.rank)) [Fintype J] [DecidableEq J] [Nonempty J]
    (hJ : ∀ β ∈ parabolicRoots τ J, weylQuotientHom τ Ω ⟨n, hnm⟩ • β ∈ parabolicRoots τ J)
    (hrel : ∀ x : Fin τ.rank → ℤ,
      weylQuotientHom τ Ω ⟨n, hnm⟩ • weylQuotientHom τ Ω ⟨n, hnm⟩ • x +
        weylQuotientHom τ Ω ⟨n, hnm⟩ • x + x = 0)
    (hdet : (cartanBlock τ J).det ≠ 0) {p : ℕ} (hp : p.Prime)
    (hpd : ¬ p ∣ (cartanBlock τ J).det.natAbs) (hq : ((q : Ω) ^ 2 + q + 1) ≠ 0)
    (hdvd : p ∣ q ^ 2 + q + 1) :
    p ∣ Nat.card ↥(rootSpan τ Ω (parabolicRoots τ J) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr))) := by
  classical
  set w : WeylGroup τ := weylQuotientHom τ Ω ⟨n, hnm⟩ with hw
  set K' : Subgroup (J → Ωˣ) := (monoHom (G := Ωˣ) ((q : ℤ) • blockP w J - 1)).ker with hK'
  let g : K' →* ModGL τ Ω := (CFSG.LieType.Chevalley.supportedTorusHom τ Ω J).comp K'.subtype
  have hP : blockP w J * blockP w J + blockP w J + 1 = 0 := blockP_sq_add_self_add_one hJ hrel
  have hG : (blockP w J)ᵀ * cartanBlock τ J * blockP w J = cartanBlock τ J :=
    blockP_transpose_mul_cartanBlock_mul_self hsym hJ
  have hcard : Nat.card K' ^ 2 = (q ^ 2 + q + 1) ^ Fintype.card J :=
    natCard_ker_monoHom_cyclotomic hP hG hdet hq
  have hposK : 0 < Nat.card K' := by
    by_contra h
    have h0 : Nat.card K' = 0 := Nat.eq_zero_of_not_pos h
    rw [h0] at hcard
    have : (q ^ 2 + q + 1) ^ Fintype.card J ≠ 0 := pow_ne_zero _ (by positivity)
    exact this hcard.symm
  haveI : Finite K' := Nat.finite_of_card_ne_zero (ne_of_gt hposK)
  have hdvdK : p ∣ Nat.card K' := by
    have h1 : p ∣ (q ^ 2 + q + 1) ^ Fintype.card J :=
      hdvd.trans (dvd_pow_self _ Fintype.card_ne_zero)
    rw [← hcard] at h1
    exact hp.dvd_of_dvd_pow h1
  have hfix_of_mem : ∀ c : J → Ωˣ, c ∈ K' →
      monoHom ((q : ℤ) • blockP w J) c = c := by
    intro c hc
    have h : monoHom ((q : ℤ) • blockP w J - 1) c = 1 := by
      simpa only [hK', MonoidHom.mem_ker] using hc
    rw [monoHom_sub_one] at h
    exact mul_inv_eq_one.mp h
  have hmem : ∀ c : K', g c ∈ rootSpan τ Ω (parabolicRoots τ J) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
    intro c
    refine Subgroup.mem_inf.2 ⟨supportedTorusHom_mem_rootSpan c.1, ?_⟩
    change g c ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr))
    rw [mem_twistedFixedPoints]
    show n * Units.map (entrywiseHom Fr)
      (CFSG.LieType.Chevalley.supportedTorusHom τ Ω J c.1) * n⁻¹ =
      CFSG.LieType.Chevalley.supportedTorusHom τ Ω J c.1
    rw [supportedTorusHom_conj_twisted hsym hFr n hnm hJ c.1, hfix_of_mem c.1 c.2]
  have hker : ∀ c : g.ker, orderOf c ∣ (cartanBlock τ J).det.natAbs := by
    intro c
    have hprod : ∀ i : J, ∏ j : J, ((c : K') : J → Ωˣ) j ^ τ.cartan j i = 1 :=
      fun i => (supportedTorusHom_eq_one_iff J ((c : K') : J → Ωˣ)).1
        (show supportedTorusHom τ Ω J ((c : K') : J → Ωˣ) = 1 from c.2) i
    have hpow : ((c : K') : J → Ωˣ) ^ (cartanBlock τ J).det.natAbs = 1 := by
      funext j
      have h := pow_det_eq_one_of_prod_cartan_eq_one ((c : K') : J → Ωˣ) hprod j
      rcases Int.eq_nat_or_neg (cartanBlock τ J).det with ⟨m, hm | hm⟩
      · rw [hm] at h ⊢
        rw [Int.natAbs_natCast, Pi.one_apply, Pi.pow_apply, ← _root_.zpow_natCast]
        exact h
      · rw [hm] at h ⊢
        rw [Int.natAbs_neg, Int.natAbs_natCast, Pi.one_apply, Pi.pow_apply,
          ← _root_.zpow_natCast]
        have h' : (((c : K') : J → Ωˣ) j ^ ((m : ℤ)))⁻¹ = 1 := by
          simpa only [_root_.zpow_neg] using h
        simpa using inv_eq_one.1 h'
    have hcK : c ^ (cartanBlock τ J).det.natAbs = 1 :=
      Subtype.ext (Subtype.ext (by simpa using hpow))
    exact orderOf_dvd_iff_pow_eq_one.2 hcK
  have hpk : ¬ p ∣ Nat.card g.ker := by
    intro hpdv
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Finite g.ker := inferInstance
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := g.ker) p hpdv
    have h1 : p ∣ orderOf c := hc ▸ dvd_refl p
    exact hpd (h1.trans (hker c))
  have hmul := Subgroup.card_ker_mul_card_range g
  have hdvdR : p ∣ Nat.card g.range := by
    have h1 : p ∣ Nat.card g.ker * Nat.card g.range := hmul ▸ hdvdK
    rcases hp.dvd_mul.1 h1 with h | h
    · exact absurd h hpk
    · exact h
  exact hdvdR.trans (Subgroup.card_dvd_of_le (by
    rintro _ ⟨c, rfl⟩
    exact hmem c))

theorem dvd_card_rootSpan_inf_twistedFixedPoints_sub {τ : Tag} {Ω : Type} [Field Ω]
    [IsAlgClosed Ω] (hsym : τ.symmetrizer = 1) {Fr : Ω →+* Ω} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (n : ModGL τ Ω) (hnm : n ∈ monomialSubgroup τ Ω)
    (J : Set (Fin τ.rank)) [Fintype J] [DecidableEq J] [Nonempty J]
    (hJ : ∀ β ∈ parabolicRoots τ J, weylQuotientHom τ Ω ⟨n, hnm⟩ • β ∈ parabolicRoots τ J)
    (hrel : ∀ x : Fin τ.rank → ℤ,
      weylQuotientHom τ Ω ⟨n, hnm⟩ • weylQuotientHom τ Ω ⟨n, hnm⟩ • x -
        weylQuotientHom τ Ω ⟨n, hnm⟩ • x + x = 0)
    (hdet : (cartanBlock τ J).det ≠ 0) {p : ℕ} (hp : p.Prime)
    (hpd : ¬ p ∣ (cartanBlock τ J).det.natAbs) (hq2 : 2 ≤ q)
    (hq : ((q : Ω) ^ 2 - q + 1) ≠ 0)
    (hdvd : p ∣ q ^ 2 - q + 1) :
    p ∣ Nat.card ↥(rootSpan τ Ω (parabolicRoots τ J) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr))) := by
  classical
  set w : WeylGroup τ := weylQuotientHom τ Ω ⟨n, hnm⟩ with hw
  set K' : Subgroup (J → Ωˣ) := (monoHom (G := Ωˣ) ((q : ℤ) • blockP w J - 1)).ker with hK'
  let g : K' →* ModGL τ Ω := (CFSG.LieType.Chevalley.supportedTorusHom τ Ω J).comp K'.subtype
  have hP : blockP w J * blockP w J - blockP w J + 1 = 0 := blockP_sq_sub_self_add_one hJ hrel
  have hG : (blockP w J)ᵀ * cartanBlock τ J * blockP w J = cartanBlock τ J :=
    blockP_transpose_mul_cartanBlock_mul_self hsym hJ
  have hcard : Nat.card K' ^ 2 = (q ^ 2 - q + 1) ^ Fintype.card J :=
    natCard_ker_monoHom_cyclotomic_sub hP hG hdet hq2 hq
  have hposK : 0 < Nat.card K' := by
    by_contra h
    have h0 : Nat.card K' = 0 := Nat.eq_zero_of_not_pos h
    rw [h0] at hcard
    have : (q ^ 2 - q + 1) ^ Fintype.card J ≠ 0 := pow_ne_zero _ (by nlinarith)
    exact this hcard.symm
  haveI : Finite K' := Nat.finite_of_card_ne_zero (ne_of_gt hposK)
  have hdvdK : p ∣ Nat.card K' := by
    have h1 : p ∣ (q ^ 2 - q + 1) ^ Fintype.card J :=
      hdvd.trans (dvd_pow_self _ Fintype.card_ne_zero)
    rw [← hcard] at h1
    exact hp.dvd_of_dvd_pow h1
  have hfix_of_mem : ∀ c : J → Ωˣ, c ∈ K' →
      monoHom ((q : ℤ) • blockP w J) c = c := by
    intro c hc
    have h : monoHom ((q : ℤ) • blockP w J - 1) c = 1 := by
      simpa only [hK', MonoidHom.mem_ker] using hc
    rw [monoHom_sub_one] at h
    exact mul_inv_eq_one.mp h
  have hmem : ∀ c : K', g c ∈ rootSpan τ Ω (parabolicRoots τ J) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
    intro c
    refine Subgroup.mem_inf.2 ⟨supportedTorusHom_mem_rootSpan c.1, ?_⟩
    change g c ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr))
    rw [mem_twistedFixedPoints]
    show n * Units.map (entrywiseHom Fr)
      (CFSG.LieType.Chevalley.supportedTorusHom τ Ω J c.1) * n⁻¹ =
      CFSG.LieType.Chevalley.supportedTorusHom τ Ω J c.1
    rw [supportedTorusHom_conj_twisted hsym hFr n hnm hJ c.1, hfix_of_mem c.1 c.2]
  have hker : ∀ c : g.ker, orderOf c ∣ (cartanBlock τ J).det.natAbs := by
    intro c
    have hprod : ∀ i : J, ∏ j : J, ((c : K') : J → Ωˣ) j ^ τ.cartan j i = 1 :=
      fun i => (supportedTorusHom_eq_one_iff J ((c : K') : J → Ωˣ)).1
        (show supportedTorusHom τ Ω J ((c : K') : J → Ωˣ) = 1 from c.2) i
    have hpow : ((c : K') : J → Ωˣ) ^ (cartanBlock τ J).det.natAbs = 1 := by
      funext j
      have h := pow_det_eq_one_of_prod_cartan_eq_one ((c : K') : J → Ωˣ) hprod j
      rcases Int.eq_nat_or_neg (cartanBlock τ J).det with ⟨m, hm | hm⟩
      · rw [hm] at h ⊢
        rw [Int.natAbs_natCast, Pi.one_apply, Pi.pow_apply, ← _root_.zpow_natCast]
        exact h
      · rw [hm] at h ⊢
        rw [Int.natAbs_neg, Int.natAbs_natCast, Pi.one_apply, Pi.pow_apply,
          ← _root_.zpow_natCast]
        have h' : (((c : K') : J → Ωˣ) j ^ ((m : ℤ)))⁻¹ = 1 := by
          simpa only [_root_.zpow_neg] using h
        simpa using inv_eq_one.1 h'
    have hcK : c ^ (cartanBlock τ J).det.natAbs = 1 :=
      Subtype.ext (Subtype.ext (by simpa using hpow))
    exact orderOf_dvd_iff_pow_eq_one.2 hcK
  have hpk : ¬ p ∣ Nat.card g.ker := by
    intro hpdv
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Finite g.ker := inferInstance
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := g.ker) p hpdv
    have h1 : p ∣ orderOf c := hc ▸ dvd_refl p
    exact hpd (h1.trans (hker c))
  have hmul := Subgroup.card_ker_mul_card_range g
  have hdvdR : p ∣ Nat.card g.range := by
    have h1 : p ∣ Nat.card g.ker * Nat.card g.range := hmul ▸ hdvdK
    rcases hp.dvd_mul.1 h1 with h | h
    · exact absurd h hpk
    · exact h
  exact hdvdR.trans (Subgroup.card_dvd_of_le (by
    rintro _ ⟨c, rfl⟩
    exact hmem c))

end Torus

section Frame

theorem dvd_card_rootSpan_image_inf_twistedFixedPoints_e6 {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (K : Type) [Field K] [Finite K]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε)
    (v : WeylGroup Tag.E8)
    (hmaps : ∀ β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      (v⁻¹ * e8T3We ε * v) • β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8))
    (hrel : ∀ x : Fin Tag.E8.rank → ℤ,
      (v⁻¹ * e8T3We ε * v) • (v⁻¹ * e8T3We ε * v) • x +
        ε • ((v⁻¹ * e8T3We ε * v) • x) + x = 0) :
    p ∣ Nat.card ↥(rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8
      (e6Nodes Tag.E8)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c : L, Fr c = c ^ Nat.card K := fun c => by
    rw [hK, iterateFrobenius_def]
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ :=
      IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos (Fact.out : ℓ.Prime).pos f)
    exact ⟨x, by rw [hFr, hK, hx]⟩⟩
  set V : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E8 L := canonicalRep_mem_monomialSubgroup L v
  set n' : ModGL Tag.E8 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E8 L := mul_mem (mul_mem (inv_mem hVm) hnm) hVm
  have hπV : weylQuotientHom Tag.E8 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E8 L ⟨n', hn'm⟩ = v⁻¹ * e8T3We ε * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E8 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hnm⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV, hnW]
  have hq0 : ((Nat.card K : ℕ) : L) = 0 := by
    rw [hK, Nat.cast_pow, CharP.cast_eq_zero L ℓ, zero_pow (by omega : f ≠ 0)]
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  haveI : Nonempty ↥(e6Nodes Tag.E8) := ⟨⟨0, by simp [e6Nodes]⟩⟩
  have hroots : ∀ r ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8), IsRoot Tag.E8 r :=
    fun r hr => hr.1
  have hdet : (cartanBlock Tag.E8 (e6Nodes Tag.E8)).det ≠ 0 := by
    rw [det_cartanBlock_e6Nodes]
    norm_num
  have hpd : ¬ p ∣ (cartanBlock Tag.E8 (e6Nodes Tag.E8)).det.natAbs := by
    rw [det_cartanBlock_e6Nodes]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  rcases hε with rfl | rfl
  ·
    have hpf' : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := by
      have h : ((p : ℤ) ∣ ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ℤ)) := by
        push_cast
        simpa using hpf
      exact_mod_cast h
    have hq : ((Nat.card K : L) ^ 2 + Nat.card K + 1) ≠ 0 := by
      rw [hq0]
      norm_num
    have h := dvd_card_rootSpan_inf_twistedFixedPoints_add (τ := Tag.E8) (Ω := L)
      (by rfl : Tag.E8.symmetrizer = 1) hFr n' hn'm (e6Nodes Tag.E8)
      (by rw [hπn']; exact hmaps) (fun x => by rw [hπn']; simpa using hrel x) hdet hp hpd hq hpf'
    have hmap := map_conj_rootSpan_inf_twistedFixedPoints Fr hFrbij v n hroots
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj V).injective]
    exact h
  ·
    have hpf' : p ∣ Nat.card K ^ 2 - Nat.card K + 1 := by
      have hcast : ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ) =
          (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1 := by
        have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
        rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow]
        push_cast
        ring
      have h : ((p : ℤ) ∣ ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ)) := by
        rw [hcast]
        simpa [sub_eq_add_neg] using hpf
      exact_mod_cast h
    have hq : ((Nat.card K : L) ^ 2 - Nat.card K + 1) ≠ 0 := by
      rw [hq0]
      norm_num
    have h := dvd_card_rootSpan_inf_twistedFixedPoints_sub (τ := Tag.E8) (Ω := L)
      (by rfl : Tag.E8.symmetrizer = 1) hFr n' hn'm (e6Nodes Tag.E8)
      (by rw [hπn']; exact hmaps) (fun x => by rw [hπn']; simpa [sub_eq_add_neg] using hrel x)
      hdet hp hpd hq2 hq hpf'
    have hmap := map_conj_rootSpan_inf_twistedFixedPoints Fr hFrbij v n hroots
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj V).injective]
    exact h

end Frame

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
