module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Wreath
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ThreeRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.G2Subgroup
public import CFSG.RankThree.PartTwo.KFacts.K71TrialityFix
public import CFSG.HardMathSupport.Lang.AnisoE6.E6InF4
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.QuadExt
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersRankOne
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsLocal
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import CFSG.RankThree.PartOne.SEITZ8.D4Order
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
import CFSG.Open.StatedAPI
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Lang.AnisoE6.CatBridge
public import CFSG.HardMathSupport.Lang.Triality.G2ClassOrder
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTwistedClasses
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.SEITZ2.D4Outer
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate9124

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)

open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

namespace RankTwo

variable {L : Type} [Field L]

theorem hasNoncommPair_three {ω : Lˣ} (hω : orderOf ω = 3) (H : Subgroup (GL (Fin 3) L))
    (hdiag : ∀ u : Fin 3 → Lˣ, (∀ i, u i ∈ Subgroup.zpowers ω) → ∏ i, u i = 1 →
      diagGL 3 u ∈ H)
    (hperm : permGL 3 (finRotate 3) ∈ H) : HasNoncommPair 3 H := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    omega
  set uu : Fin 3 → Lˣ := ![ω, ω⁻¹, 1] with huu
  set vv : Fin 3 → Lˣ := ![1, ω, ω⁻¹] with hvv
  set ww : Fin 3 → Lˣ := ![ω⁻¹, 1, ω] with hww
  have hz : ∀ u : Fin 3 → Lˣ, (∀ i, u i = 1 ∨ u i = ω ∨ u i = ω⁻¹) →
      ∀ i, u i ∈ Subgroup.zpowers ω := by
    intro u hu i
    rcases hu i with h | h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers ω
    · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers ω)
  have hmu : diagGL 3 uu ∈ H :=
    hdiag _ (hz _ (fun i => by fin_cases i <;> simp [huu])) (by simp [huu, Fin.prod_univ_three])
  have hmv : diagGL 3 vv ∈ H :=
    hdiag _ (hz _ (fun i => by fin_cases i <;> simp [hvv])) (by simp [hvv, Fin.prod_univ_three])
  have hmw : diagGL 3 ww ∈ H :=
    hdiag _ (hz _ (fun i => by fin_cases i <;> simp [hww])) (by simp [hww, Fin.prod_univ_three])
  have hσ : ∀ i : Fin 3, (finRotate 3)⁻¹ i = ![2, 0, 1] i := by decide
  have hconj : ∀ u : Fin 3 → Lˣ, permGL 3 (finRotate 3) * diagGL 3 u *
      (permGL 3 (finRotate 3))⁻¹ = diagGL 3 ![u 2, u 0, u 1] := by
    intro u
    rw [permGL_mul_diagGL_mul_inv]
    congr 1
    funext i
    rw [hσ i]
    fin_cases i <;> rfl
  have hpow : ∀ u : Fin 3 → Lˣ, (∀ i, u i ^ 3 = 1) → diagGL 3 u ^ 3 = 1 := fun u hu => by
    rw [← map_pow, show u ^ 3 = 1 from funext hu, map_one]
  let a : H := ⟨diagGL 3 uu, hmu⟩
  let b : H := ⟨diagGL 3 vv, hmv⟩
  let c : H := ⟨diagGL 3 ww, hmw⟩
  let y : H := ⟨permGL 3 (finRotate 3), hperm⟩
  have hcomm : ∀ u v : Fin 3 → Lˣ, diagGL 3 u * diagGL 3 v = diagGL 3 v * diagGL 3 u :=
    fun u v => by rw [← map_mul, ← map_mul, mul_comm]
  have hab : a * b = b * a := Subtype.ext (hcomm uu vv)
  have hac : a * c = c * a := Subtype.ext (hcomm uu ww)
  have hbc : b * c = c * b := Subtype.ext (hcomm vv ww)
  have ha3 : a ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hpow _ (fun i => by fin_cases i <;> simp [huu, hω3]))
  have hb3 : b ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hpow _ (fun i => by fin_cases i <;> simp [hvv, hω3]))
  have hc3 : c ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hpow _ (fun i => by fin_cases i <;> simp [hww, hω3]))
  have hy3 : y ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show permGL 3 (finRotate 3) ^ 3 = 1
    rw [← map_pow, show finRotate 3 ^ 3 = 1 by decide, map_one])
  have h1 : y * a * y⁻¹ = b := Subtype.ext (by
    show permGL 3 (finRotate 3) * diagGL 3 uu * (permGL 3 (finRotate 3))⁻¹ = diagGL 3 vv
    rw [hconj]
    rfl)
  have h2 : y * b * y⁻¹ = c := Subtype.ext (by
    show permGL 3 (finRotate 3) * diagGL 3 vv * (permGL 3 (finRotate 3))⁻¹ = diagGL 3 ww
    rw [hconj]
    rfl)
  have h3 : y * c * y⁻¹ = a := Subtype.ext (by
    show permGL 3 (finRotate 3) * diagGL 3 ww * (permGL 3 (finRotate 3))⁻¹ = diagGL 3 uu
    rw [hconj]
    rfl)
  have hU := isPGroup_closure_cycle hab hac hbc ha3 hb3 hc3 hy3 h1 h2 h3
  refine ⟨a, y, ha3, hy3, fun h => ?_, hU.to_le (Subgroup.closure_mono ?_)⟩
  · have hba : b = a := by rw [← h1, ← h, mul_assoc, mul_inv_cancel, mul_one]
    have h00 := congrArg (fun g : H => ((g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 0 0) hba
    simp only [b, a, coe_diagGL, Matrix.diagonal_apply_eq] at h00
    exact hω1 (Units.ext (by simpa [huu, hvv] using h00.symm))
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr rfl))

noncomputable def slEquiv (F : Type) [Field F] :
    ↥(StatedSL 3 F) ≃* Matrix.SpecialLinearGroup (Fin (2 + 1)) F :=
  (MulEquiv.subgroupCongr (statedSL_eq_range_toGL 3 F)).trans
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm

theorem hasNoncommPair_of_injective {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (ι : G →* H) (hι : Function.Injective ι)
    (hcard : (Nat.card G).factorization 3 = (Nat.card H).factorization 3)
    (h : HasNoncommPair 3 H) : HasNoncommPair 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, y, hx, hy, hxy, hP⟩ := h
  obtain ⟨P₂, hP₂⟩ := hP.exists_le_sylow
  obtain ⟨P⟩ : Nonempty (Sylow 3 G) := inferInstance
  have hPc : Nat.card ((P : Subgroup G).map ι) = 3 ^ (Nat.card H).factorization 3 := by
    rw [Subgroup.card_map_of_injective hι, P.card_eq_multiplicity, hcard]
  let P' : Sylow 3 H := Sylow.ofCard ((P : Subgroup G).map ι) hPc
  have hP' : (P' : Subgroup H) = (P : Subgroup G).map ι := Sylow.coe_ofCard _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P₂ P'
  have h2 : ((g • P₂ : Sylow 3 H) : Subgroup H) = (P' : Subgroup H) := congrArg _ hg
  have hS : (P' : Subgroup H) = (P₂ : Subgroup H).map (MulAut.conj g).toMonoidHom := by
    rw [← h2, Sylow.coe_subgroup_smul]
    ext z
    simp [Subgroup.mem_map, Subgroup.mem_smul_pointwise_iff_exists]
  let c : H →* H := (MulAut.conj g).toMonoidHom
  have hc : Function.Injective c := (MulAut.conj g).injective
  have hmem : ∀ z ∈ Subgroup.closure ({x, y} : Set H), ∃ z' ∈ (P : Subgroup G), ι z' = c z := by
    intro z hz
    have : c z ∈ (P' : Subgroup H) := hS ▸ Subgroup.mem_map_of_mem _ (hP₂ hz)
    rw [hP'] at this
    obtain ⟨z', hz', hz'z⟩ := this
    exact ⟨z', hz', hz'z⟩
  obtain ⟨x', hx'P, hx'⟩ := hmem x (Subgroup.subset_closure (by simp))
  obtain ⟨y', hy'P, hy'⟩ := hmem y (Subgroup.subset_closure (by simp))
  refine ⟨x', y', hι ?_, hι ?_, fun he => hxy (hc ?_), P.isPGroup'.to_le ((Subgroup.closure_le _).2
    (Set.insert_subset_iff.2 ⟨hx'P, Set.singleton_subset_iff.2 hy'P⟩))⟩
  · rw [map_pow, hx', ← map_pow, hx, map_one, map_one]
  · rw [map_pow, hy', ← map_pow, hy, map_one, map_one]
  · rw [map_mul, map_mul, ← hx', ← hy', ← map_mul, ← map_mul, he]

end RankTwo

private theorem card_subfield_eq_pow {K : Type} [Field K] [Finite K] {ℓ : ℕ} [CharP K ℓ]
    (k : Subfield K) : ∃ m : ℕ, 1 ≤ m ∧ Nat.card k = ℓ ^ m := by
  classical
  haveI : Fintype k := Fintype.ofFinite _
  haveI : CharP k ℓ := (k.subtype.charP_iff k.subtype_injective ℓ).2 inferInstance
  obtain ⟨n, -, hcard⟩ := FiniteField.card k ℓ
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩

section Certified

theorem hasNoncommPair_three_G2_of_dvd_sub (k : Type) [Field k] [Finite k]
    (h1 : 3 ∣ Nat.card k - 1) : HasNoncommPair 3 ↥(adjointGroup .G2 k) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := kˣ) 3 (by rwa [Nat.card_units])
  obtain ⟨φ, hφ, -⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_a2Hom_injective (K := k)
  have hSL := RankTwo.hasNoncommPair_three hω (StatedSL 3 k)
    (fun u _ hprod => by
      rw [mem_statedSL_iff, det_diagGL, ← Units.coe_prod, hprod, Units.val_one])
    (by rw [mem_statedSL_iff, det_permGL, sign_finRotate]; simp)
  exact hSL.map (φ.comp (RankTwo.slEquiv k).toMonoidHom) (hφ.comp (RankTwo.slEquiv k).injective)

private theorem lieModel_adjointG2 (k : Type) [Field k] [Finite k] {ℓ f : ℕ}
    (hadm : StatedLieAdmissible .G2 0 ℓ f) (hk : Nat.card k = ℓ ^ f) :
    LieModel ↥(adjointGroup .G2 k) .G2 0 ℓ f := by
  have hZ : Subgroup.center ↥(adjointGroup .G2 k) = ⊥ := center_adjointGroup_eq_bot
  exact Or.inr (Or.inl ⟨rfl, by decide, hadm, k, inferInstance, inferInstance, hk,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm⟩⟩)

private theorem card_adjointG2 (hLie : LieOrderFormulasInput) (k : Type) [Field k] [Finite k]
    (hk : 3 ≤ Nat.card k) :
    Nat.card ↥(adjointGroup .G2 k) * 1 =
      Nat.card k ^ 6 * (Nat.card k ^ 6 - 1) * (Nat.card k ^ 2 - 1) := by
  classical
  haveI := Fintype.ofFinite k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k (ringChar k)
  have hk' : Nat.card k = ringChar k ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hadm : StatedLieAdmissible .G2 0 (ringChar k) n :=
    ⟨hp, n.pos, rfl, by rw [← hk']; exact hk⟩
  have := (hLie _ .G2 0 _ _ hadm (lieModel_adjointG2 k hadm hk')).2.1
  rw [← hk'] at this
  exact this

private theorem g2_factorization_eq {q N N₂ : ℕ} (hq : 2 ≤ q) (h1 : 3 ∣ q + 1)
    (hN : N * 1 = q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1))
    (hN₂ : N₂ * 1 = (q ^ 2) ^ 6 * ((q ^ 2) ^ 6 - 1) * ((q ^ 2) ^ 2 - 1)) :
    N.factorization 3 = N₂.factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [mul_one] at hN hN₂
  set x := q ^ 2 with hx
  have hx4 : 4 ≤ x := by rw [hx]; nlinarith
  have hnq : ¬ 3 ∣ q := by omega
  have hnx : ¬ 3 ∣ x := fun h => hnq (Nat.prime_three.dvd_of_dvd_pow h)
  have hx1 : 3 ∣ x - 1 := by
    rw [hx, show q ^ 2 - 1 = (q + 1) * (q - 1) by
      rw [← Nat.sq_sub_sq, one_pow]]
    exact h1.mul_right _
  have hq6 : q ^ 6 = x ^ 3 := by rw [hx, ← pow_mul]
  rw [hq6] at hN
  have lte : ∀ m : ℕ, m ≠ 0 → padicValNat 3 (x ^ m - 1) = padicValNat 3 (x - 1) +
      padicValNat 3 m := fun m hm => by
    have := padicValNat.pow_sub_pow (p := 3) (by decide) (by omega : 1 < x) hx1 hnx hm
    rwa [one_pow] at this
  have l1 := lte 1 one_ne_zero
  have l2 := lte 2 two_ne_zero
  have l3 := lte 3 (by norm_num)
  have l6 := lte 6 (by norm_num)
  have v2 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have v3 : padicValNat 3 3 = 1 := padicValNat_self
  have v6 : padicValNat 3 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num), v3, v2]
  have hpos : ∀ m : ℕ, m ≠ 0 → x ^ m - 1 ≠ 0 := fun m hm => by
    have : 1 < x ^ m := Nat.one_lt_pow hm (by omega)
    omega
  have hx3 : x ^ 3 ≠ 0 := pow_ne_zero _ (by omega)
  have hx6 : x ^ 6 ≠ 0 := pow_ne_zero _ (by omega)
  have w3 : padicValNat 3 (x ^ 3) = 0 := padicValNat.eq_zero_of_not_dvd
    (fun h => hnx (Nat.prime_three.dvd_of_dvd_pow h))
  have w6 : padicValNat 3 (x ^ 6) = 0 := padicValNat.eq_zero_of_not_dvd
    (fun h => hnx (Nat.prime_three.dvd_of_dvd_pow h))
  rw [pow_one] at l1
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact (mul_ne_zero (mul_ne_zero hx3 (hpos 3 (by norm_num))) (hpos 1 one_ne_zero))
      (by rw [pow_one]; exact hN.symm)
  have hN₂0 : N₂ ≠ 0 := by
    rintro rfl
    exact (mul_ne_zero (mul_ne_zero hx6 (hpos 6 (by norm_num))) (hpos 2 two_ne_zero)) hN₂.symm
  have k1 := congrArg (padicValNat 3) hN
  have k2 := congrArg (padicValNat 3) hN₂
  have hx1' : x - 1 ≠ 0 := by omega
  rw [padicValNat.mul (mul_ne_zero hx3 (hpos 3 (by norm_num))) hx1',
    padicValNat.mul hx3 (hpos 3 (by norm_num)), w3, l3, v3] at k1
  rw [padicValNat.mul (mul_ne_zero hx6 (hpos 6 (by norm_num))) (hpos 2 two_ne_zero),
    padicValNat.mul hx6 (hpos 6 (by norm_num)), w6, l6, v6, l2, v2] at k2
  rw [Nat.factorization_def N Nat.prime_three, Nat.factorization_def N₂ Nat.prime_three]
  omega

theorem hasNoncommPair_three_G2_of_dvd_add (hLie : LieOrderFormulasInput) (k : Type) [Field k]
    [Finite k] (hk : 3 ≤ Nat.card k) (h1 : 3 ∣ Nat.card k + 1) :
    HasNoncommPair 3 ↥(adjointGroup .G2 k) := by
  obtain ⟨k₂, _, _, hdeg, -⟩ :=
    CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.exists_quadratic_frobenius_all k
  haveI : Module.Finite k k₂ := Module.finite_of_finrank_pos (by omega)
  haveI : Finite k₂ := Module.finite_of_finite k
  have hk₂ : Nat.card k₂ = Nat.card k ^ 2 :=
    CFSG.RankThree.Chevalley.natCard_eq_sq_of_finrank_eq_two hdeg
  have h₂ : 3 ∣ Nat.card k₂ - 1 := by
    rw [hk₂, show Nat.card k ^ 2 - 1 = (Nat.card k + 1) * (Nat.card k - 1) by
      rw [← Nat.sq_sub_sq, one_pow]]
    exact h1.mul_right _
  let ι : ↥(adjointGroup .G2 k) →* ↥(adjointGroup .G2 k₂) :=
    ((CFSG.LieType.Chevalley.baseChangeGL (τ := .G2) (algebraMap k k₂)).comp
      (adjointGroup .G2 k).subtype).codRestrict _
      (fun g => CFSG.HardMathSupport.Lang.AnisoE6.baseChangeGL_mem_adjointGroup_of_mem _ g.2)
  have hι : Function.Injective ι := fun a b h => Subtype.ext
    (CFSG.LieType.Chevalley.baseChangeGL_injective (τ := .G2) (algebraMap k k₂)
      (congrArg Subtype.val h))
  refine RankTwo.hasNoncommPair_of_injective ι hι ?_ (hasNoncommPair_three_G2_of_dvd_sub k₂ h₂)
  have hN := card_adjointG2 hLie k hk
  have hN₂ := card_adjointG2 hLie k₂ (by rw [hk₂]; nlinarith)
  rw [hk₂] at hN₂
  exact g2_factorization_eq (by omega) h1 hN hN₂

theorem hasNoncommPair_three_G2 (hLie : LieOrderFormulasInput) (k : Type) [Field k] [Finite k]
    (hk : 3 ≤ Nat.card k) (h3 : ¬ 3 ∣ Nat.card k) : HasNoncommPair 3 ↥(adjointGroup .G2 k) := by
  by_cases h1 : 3 ∣ Nat.card k - 1
  · exact hasNoncommPair_three_G2_of_dvd_sub k h1
  · exact hasNoncommPair_three_G2_of_dvd_add hLie k hk (by omega)

private theorem exists_equiv_adjointG2 {K : Type} [Group K] {n ℓ f : ℕ}
    (hadm : StatedLieAdmissible .G2 n ℓ f) (hmodel : LieModel K .G2 n ℓ f) (hℓ3 : ℓ ≠ 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), 3 ≤ Nat.card F ∧ ¬ 3 ∣ Nat.card F ∧
      Nonempty (K ≃* ↥(adjointGroup .G2 F)) := by
  obtain ⟨⟨-, -, -, h3q⟩, F, _, _, hF, ⟨e⟩⟩ := hmodel.chevalleyExceptionalModel (by decide)
  have hZ : Subgroup.center ↥(adjointGroup .G2 F) = ⊥ := center_adjointGroup_eq_bot
  have hℓ : ℓ.Prime := hadm.1
  refine ⟨F, inferInstance, inferInstance, hF ▸ h3q, ?_,
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩⟩
  rw [hF]
  intro h
  exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm

theorem heisDichLieCross_G2 : HeisDichLieCrossAt .G2 := by
  intro K _ _ _ _ n ℓ f hadm hmodel hℓ3 _
  obtain ⟨F, _, _, -, hF3, ⟨e3⟩⟩ := exists_equiv_adjointG2 hadm hmodel hℓ3
  exact Or.inl (SylowDichotomyAt.of_card_elemAbelian_le Nat.prime_three
    (RankLE2.of_mulEquiv e3.symm
      (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_adjointGroup_G2 F hF3)))

theorem dichLieCross_G2 (hLie : LieOrderFormulasInput) : DichLieCrossAt .G2 := by
  intro K _ _ hs hnab n ℓ f hadm hmodel hℓ3 h3
  obtain ⟨F, _, _, hF, hF3, ⟨e3⟩⟩ := exists_equiv_adjointG2 hadm hmodel hℓ3
  exact ⟨Or.inr (Or.inl ((hasNoncommPair_three_G2 hLie F hF hF3).map e3.symm.toMonoidHom
    e3.symm.injective)), heisDichLieCross_G2 K hs hnab n ℓ f hadm hmodel hℓ3 h3⟩

private theorem exists_equiv_cat_trialityD4 {K : Type} [Group K] {n ℓ f : ℕ}
    (hmodel : LieModel K .trialityD4 n ℓ f) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      q.p = ℓ ∧ q.exponent = f ∧
        Nonempty (K ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) := by
  obtain ⟨⟨hℓ, hf1, -⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have hm' : TwistedChevalleyModel K .D4 (ℓ ^ f) := hm
  obtain ⟨F, _, _, hF, σ, hσ, ⟨e⟩⟩ := hm'
  let q : TauCeti.PrimePower := ⟨ℓ, f, hℓ, hf1⟩
  have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid := TauCeti.LieTypeIndex.valid_trialityD4 q
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv F
    (by rw [TauCeti.PrimePower.card_def]; exact hF) σ
    (fun x => by rw [TauCeti.PrimePower.card_def]; exact hσ x)
  exact ⟨q, hv, rfl, rfl, ⟨e.trans b⟩⟩

theorem heisDichLieCross_trialityD4 : HeisDichLieCrossAt .trialityD4 := by
  intro K _ _ _ _ n ℓ f _ hmodel hℓ3 _
  obtain ⟨q, hv, hqp, -, ⟨e⟩⟩ := exists_equiv_cat_trialityD4 hmodel
  exact Or.inl (SylowDichotomyAt.of_card_elemAbelian_le Nat.prime_three
    (RankLE2.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv
        (by rw [hqp]; exact hℓ3))))

private theorem hasNoncommPair_graphFixedD4 (hLie : LieOrderFormulasInput) {L : Type} [Field L]
    [Finite L] (Fr : L ≃+* L) (hk3 : 3 ≤ Nat.card (CFSG.LieType.Chevalley.fixSubfield Fr))
    (hk : ¬ 3 ∣ Nat.card (CFSG.LieType.Chevalley.fixSubfield Fr)) :
    HasNoncommPair 3 ↥(graphFixedRootGroup TwistTag.D4 L Fr.toRingHom) := by
  have hk3e : (3 : ℕ∞) ≤ ENat.card (CFSG.LieType.Chevalley.fixSubfield Fr) := by
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast hk3
  have hJ := (hasNoncommPair_three_G2 hLie (CFSG.LieType.Chevalley.fixSubfield Fr) hk3 hk).map
    (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.trialityFieldImageEquivG2 Fr
      hk3e).symm.toMonoidHom (MulEquiv.injective _)
  exact hJ.map (Subgroup.inclusion
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_trialityFieldImage_self_le Fr))
    (Subgroup.inclusion_injective _)

private theorem factorization_three_eq {n k : ℕ} (hn : n ≠ 0) (h1 : 3 ^ k ∣ n)
    (h2 : ¬ 3 ^ (k + 1) ∣ n) : n.factorization 3 = k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def n Nat.prime_three]
  have := (padicValNat_dvd_iff_le hn).1 h1
  have h' : ¬ k + 1 ≤ padicValNat 3 n := fun h => h2 ((padicValNat_dvd_iff_le hn).2 h)
  omega

private theorem hasNoncommPair_graphFixedD4_two (hLie : LieOrderFormulasInput) {K₈ : Type}
    [Field K₈] [Finite K₈] (σ : K₈ ≃+* K₈) (hK : Nat.card K₈ = 8) (hσ : ∀ c, σ c = c ^ 2) :
    HasNoncommPair 3 ↥(graphFixedRootGroup TwistTag.D4 K₈ σ.toRingHom) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K₈ 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := 3) (by norm_num) (by rw [hK]; norm_num)
  let L := FiniteField.Extension K₈ 2 4
  have hL : Nat.card L = 2 ^ 12 := by
    rw [FiniteField.natCard_extension, hK]
    norm_num
  obtain ⟨σ₀, hσ₀, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by norm_num : 1 ≤ 12) hL
  have hpow : ∀ (n : ℕ) (x : L), (σ₀ ^ n) x = x ^ (2 ^ n) := by
    intro n x
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      show σ₀ ((σ₀ ^ n) x) = _
      rw [ih, hσ₀, ← pow_mul, ← pow_succ]
  let Fr : L ≃+* L := σ₀ ^ 4
  have hFr : ∀ x, Fr x = x ^ 16 := fun x => by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    exact hpow 4 x
  have hc8 : ∀ c : K₈, c ^ 8 = c := fun c => by
    haveI := Fintype.ofFinite K₈
    have := FiniteField.pow_card c
    rwa [Fintype.card_eq_nat_card, hK] at this
  have hcompat : ∀ c : K₈, Fr.toRingHom (algebraMap K₈ L c) =
      algebraMap K₈ L (σ.toRingHom c) := by
    intro c
    show Fr (algebraMap K₈ L c) = algebraMap K₈ L (σ c)
    rw [hFr, ← map_pow, hσ, show c ^ 16 = (c ^ 8) ^ 2 by ring, hc8]
  have hle := CFSG.LieType.Chevalley.map_baseChangeGL_graphFixedRootGroup_le
    (t := TwistTag.D4) (σ := σ.toRingHom) (Fr := Fr.toRingHom) (ι := algebraMap K₈ L)
    σ.surjective hcompat
  let ψ : ↥(graphFixedRootGroup TwistTag.D4 K₈ σ.toRingHom) →*
      ↥(graphFixedRootGroup TwistTag.D4 L Fr.toRingHom) :=
    ((CFSG.LieType.Chevalley.baseChangeGL (τ := TwistTag.D4.tag) (algebraMap K₈ L)).comp
      (graphFixedRootGroup TwistTag.D4 K₈ σ.toRingHom).subtype).codRestrict _
      (fun x => hle ⟨x, x.2, rfl⟩)
  have hψ : Function.Injective ψ := fun x y h => Subtype.ext
    (CFSG.LieType.Chevalley.baseChangeGL_injective _ (congrArg Subtype.val h))
  have hfix : Nat.card (CFSG.LieType.Chevalley.fixSubfield Fr) = 2 ^ 4 :=
    CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_of_cube (f := 4) (by norm_num)
      (by rw [hL]; norm_num) (fun c => by rw [hFr]; norm_num)
  refine RankTwo.hasNoncommPair_of_injective ψ hψ ?_ (hasNoncommPair_graphFixedD4 hLie Fr
    (by rw [hfix]; norm_num) (by rw [hfix]; norm_num))
  have hcC := CFSG.RankThree.PartOne.SEITZ8.card_graphFixedRootGroup_D4_orient (f := 1) (r := 1)
    le_rfl (Or.inl rfl) (by rw [hK]; norm_num) σ.toRingHom (fun c => by
      show σ c = _
      rw [hσ]
      norm_num)
  have hcL := CFSG.RankThree.PartOne.SEITZ8.card_graphFixedRootGroup_D4_orient (f := 4) (r := 1)
    (by norm_num) (Or.inl rfl) (by rw [hL]; norm_num) Fr.toRingHom (fun c => by
      show Fr c = _
      rw [hFr]
      norm_num)
  rw [hcC, hcL, factorization_three_eq (k := 4) (by norm_num [CFSG.Open.ordTrialityD4])
      (Nat.dvd_of_mod_eq_zero (by norm_num [CFSG.Open.ordTrialityD4]))
      (fun h => by
        have := Nat.mod_eq_zero_of_dvd h
        norm_num [CFSG.Open.ordTrialityD4] at this),
    factorization_three_eq (k := 4) (by norm_num [CFSG.Open.ordTrialityD4])
      (Nat.dvd_of_mod_eq_zero (by norm_num [CFSG.Open.ordTrialityD4]))
      (fun h => by
        have := Nat.mod_eq_zero_of_dvd h
        norm_num [CFSG.Open.ordTrialityD4] at this)]

theorem dichLieCross_trialityD4 (hLie : LieOrderFormulasInput) : DichLieCrossAt .trialityD4 := by
  intro K _ _ hs hnab n ℓ f hadm hmodel hℓ3 h3
  refine ⟨Or.inr (Or.inl ?_), heisDichLieCross_trialityD4 K hs hnab n ℓ f hadm hmodel hℓ3 h3⟩
  obtain ⟨q, hv, rfl, rfl, ⟨e⟩⟩ := exists_equiv_cat_trialityD4 hmodel
  have hℓ := q.prime_p
  have hf1 := q.exponent_pos
  obtain ⟨K', _, _, σ', hK', hσ', -, ⟨c⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  refine HasNoncommPair.map ((e.trans c).symm.toMonoidHom) (MulEquiv.injective _) ?_
  by_cases h21 : q.p = 2 ∧ q.exponent = 1
  · exact hasNoncommPair_graphFixedD4_two hLie σ' (by rw [hK', h21.1, h21.2]; norm_num)
      (fun x => by rw [hσ' x, h21.1, h21.2]; norm_num)
  have hK'3 : Nat.card K' = q.p ^ (3 * q.exponent) := by
    rw [hK', ← pow_mul, mul_comm]
  haveI : CharP K' q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
      (by omega) hK'3
  obtain ⟨m, hm1, hmcard⟩ := card_subfield_eq_pow (ℓ := q.p)
    (CFSG.LieType.Chevalley.fixSubfield σ')
  have hk3 : ¬ 3 ∣ Nat.card (CFSG.LieType.Chevalley.fixSubfield σ') := by
    rw [hmcard]
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hk3' : 3 ≤ Nat.card (CFSG.LieType.Chevalley.fixSubfield σ') := by
    by_cases hℓ2 : q.p = 2
    · have hf2 : 2 ≤ q.exponent := by
        by_contra hf
        exact h21 ⟨hℓ2, by omega⟩
      rw [CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_of_cube hf1
        (by rw [hK', hℓ2]) (fun c => by rw [hσ' c, hℓ2])]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf2
    · have h3l : 3 ≤ q.p := by
        have := hℓ.two_le
        omega
      rw [hmcard]
      exact h3l.trans (Nat.le_self_pow (by omega) q.p)
  exact hasNoncommPair_graphFixedD4 hLie σ' hk3' hk3

private theorem exists_equiv_reeGamma {K : Type} [Group K] {n ℓ f : ℕ}
    (hmodel : LieModel K .twistedF4 n ℓ f) :
    ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F)
      (_ : CharP F CFSG.LieType.Ree.ReeTag.F4.prime), Nat.card F = 2 ^ (2 * a + 1) ∧
        Nonempty (K ≃* ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma F a)) := by
  obtain ⟨-, hX⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
  obtain ⟨-, -, -, hℓ2, -, hiso⟩ := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier K ℓ f hX
  subst hℓ2
  obtain ⟨-, a, hfa, F, _, _, hF, ⟨e⟩⟩ := hX
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F CFSG.LieType.Ree.ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hF]
    rfl)
  exact ⟨a, F, inferInstance, inferInstance, inferInstance, by rw [hF, hfa],
    hiso a F hfa hF ⟨e⟩⟩

private theorem hasNoncommPair_reeGamma_zero (K : Type) [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2) :
    HasNoncommPair 3 ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K 0) := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ :=
    CFSG.SectionRank.Tits_sylow3_cubic_witness (K := K) hK
  have hpair := CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc
  let j : ↥(CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0) →*
      ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K 0) :=
    ((adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag K).subtype.comp
      (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0).subtype).codRestrict _
      (fun x => by
        rw [← CFSG.LieType.Ree.LargeReeInvolution.map_reeFixed_eq_reeGamma]
        exact ⟨x, x.2, rfl⟩)
  have hj : Function.Injective j := fun a b h => by
    have h1 := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  exact hpair.map (j.comp (commutator _).subtype) (hj.comp Subtype.val_injective)

theorem hasNoncommPair_reeGamma (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    HasNoncommPair 3 ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := by
  induction a using Nat.strong_induction_on generalizing K with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact hasNoncommPair_reeGamma_zero K (by simpa using hK)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 * a + 1 ≠ 1 by omega)
    have hp2 : p ≠ 2 := by
      rintro rfl
      omega
    obtain ⟨σ₀, -, hσ₀, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two (by omega) hK
    have hσ : orderOf (σ₀ ^ ((2 * a + 1) / p)) = p := by
      rw [← hσ₀] at hpd ⊢
      exact orderOf_pow_orderOf_div (by rw [hσ₀]; omega) hpd
    obtain ⟨b, hb, hcard, hmap⟩ :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK hp hp2 _ hσ
    have hba : b < a := by
      have := hp.two_le
      have h3 : 3 ≤ p := by omega
      nlinarith
    have IH := ih b hba (CFSG.LieType.Chevalley.fixSubfield (σ₀ ^ ((2 * a + 1) / p))) hcard
    have hle : (CFSG.LieType.Ree.ReeTag.F4.reeGamma
        (CFSG.LieType.Chevalley.fixSubfield (σ₀ ^ ((2 * a + 1) / p))) b).map
          (CFSG.LieType.Chevalley.baseChangeGL
            (CFSG.LieType.Chevalley.fixSubfield (σ₀ ^ ((2 * a + 1) / p))).subtype) ≤
        CFSG.LieType.Ree.ReeTag.F4.reeGamma K a := by
      rw [← hmap]
      exact Subgroup.map_subtype_le _
    let ι : ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma
        (CFSG.LieType.Chevalley.fixSubfield (σ₀ ^ ((2 * a + 1) / p))) b) →*
        ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) :=
      ((CFSG.LieType.Chevalley.baseChangeGL
        (CFSG.LieType.Chevalley.fixSubfield (σ₀ ^ ((2 * a + 1) / p))).subtype).comp
          (CFSG.LieType.Ree.ReeTag.F4.reeGamma _ b).subtype).codRestrict _
        (fun x => hle ⟨x, x.2, rfl⟩)
    have hι : Function.Injective ι := fun x y h => Subtype.ext
      (CFSG.LieType.Chevalley.baseChangeGL_injective _ (congrArg Subtype.val h))
    exact IH.map ι hι

theorem heisDichLieCross_twistedF4 : HeisDichLieCrossAt .twistedF4 := by
  intro K _ _ _ _ n ℓ f _ hmodel _ _
  obtain ⟨a, F, _, _, _, hF', ⟨E⟩⟩ := exists_equiv_reeGamma hmodel
  have hR : RankLE2 3 ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma F a) := fun E' hE' =>
    (CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma a F hF' E'
      ⟨hE'.1, hE'.2⟩).trans (by norm_num)
  exact Or.inl (SylowDichotomyAt.of_card_elemAbelian_le Nat.prime_three
    (RankLE2.of_mulEquiv E.symm hR))

theorem dichLieCross_twistedF4 : DichLieCrossAt .twistedF4 := by
  intro K _ _ hs hnab n ℓ f hadm hmodel hℓ3 h3
  refine ⟨Or.inr (Or.inl ?_), heisDichLieCross_twistedF4 K hs hnab n ℓ f hadm hmodel hℓ3 h3⟩
  obtain ⟨a, F, _, _, _, hF', ⟨E⟩⟩ := exists_equiv_reeGamma hmodel
  exact (hasNoncommPair_reeGamma a F hF').map E.symm.toMonoidHom E.symm.injective

end Certified

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
