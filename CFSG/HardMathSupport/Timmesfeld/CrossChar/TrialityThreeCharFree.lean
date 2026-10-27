module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThree
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFixedLine
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnV
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Toral
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ringChar_eq_two_or_odd_pow {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    ringChar K = 2 ∨ ∃ m, Odd m ∧ ∀ c, σ c = c ^ m := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · left
    have : Fintype K := Fintype.ofFinite K
    have h : Fintype.card K = 2 ^ (f * 3) := by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul]
    have : CharP K 2 := charP_of_card_eq_prime_pow h
    exact ringChar.eq K 2
  · exact Or.inr ⟨p ^ f, hodd.pow, hσ⟩

section Monomial


open CFSG.GH74.GLS.Stage2.Bender.Thm1 (d4_monomial_card not_dvd_of_card_mul_eq d4B0
  exists_conj_mem_of_isPGroup_three)

theorem d4_monomial_le_root_all {p f : ℕ} (hp : p.Prime) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    graphFixedMonomial TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  rw [← twistedFixedGroup_eq_graphFixedRootGroup_triality σ (ringEquiv_cube_apply_eq hK hσ)
    (ringChar_eq_two_or_odd_pow hp hK σ hσ)]
  exact graphFixedMonomial_le _ _ _

theorem d4_monomial_index_not_dvd_all {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 1) :
    ¬ 3 ∣ ((graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).index := by
  have hle := d4_monomial_le_root_all hp K hK σ hσ
  obtain ⟨hC, -, -⟩ := triality_both_orientations_exact_finite_order p f hp hf K hK 1
    (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)
  have h := Subgroup.card_mul_index ((graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    d4_monomial_card hp hf K hK σ hσ, hC] at h
  exact not_dvd_of_card_mul_eq (p ^ f) _ hq (Nat.one_lt_pow (by omega) hp.one_lt) h

theorem d4B0_conj_mem_iff_all {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (y y' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    (MulAut.conj y)⁻¹ * MulAut.conj y' ∈ d4B0 K σ ↔
      y⁻¹ * y' ∈ (graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hNF := existsUnique_conj_mul_fieldActor_D4 hp hf hK σ hσ
  rw [← map_inv, ← map_mul]
  constructor
  · rintro ⟨g, hg, δ, h⟩
    have h1 : MulAut.conj (y⁻¹ * y') =
        MulAut.conj (y⁻¹ * y') * fieldActor (t := TwistTag.D4) σ 1 := by
      rw [fieldActor_one, mul_one]
    have h2 := (hNF (MulAut.conj (y⁻¹ * y'))).unique
      (y₁ := (y⁻¹ * y', 1)) (y₂ := (g, δ)) h1 h
    have h3 : y⁻¹ * y' = g := congrArg Prod.fst h2
    rw [h3]
    exact hg
  · intro h
    exact ⟨y⁻¹ * y', h, 1, by rw [fieldActor_one, mul_one]⟩

theorem d4B0_index_all {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    (d4B0 K σ).index = ((graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).index := by
  classical
  have hNF := existsUnique_conj_mul_fieldActor_D4 hp hf hK σ hσ
  let Φ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⧸
      (graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⧸ d4B0 K σ :=
    Quotient.lift (fun y => (QuotientGroup.mk (MulAut.conj y) : _ ⧸ d4B0 K σ))
      (fun a b hab => QuotientGroup.eq.2
        ((d4B0_conj_mem_iff_all hp hf K hK σ hσ a b).2 (QuotientGroup.leftRel_apply.1 hab)))
  have hinj : Function.Injective Φ := by
    intro a b hab
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective b
    exact QuotientGroup.eq.2 ((d4B0_conj_mem_iff_all hp hf K hK σ hσ y y').1
      (QuotientGroup.eq.1 hab))
  have hsurj : Function.Surjective Φ := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF α
    refine ⟨QuotientGroup.mk g, QuotientGroup.eq.2 ⟨1, one_mem _, δ, ?_⟩⟩
    rw [hgδ, map_one, one_mul, inv_mul_cancel_left]
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  exact (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm

theorem d4_exists_conj_le_B0_all {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 1)
    (V : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hV : IsPGroup 3 V) :
    ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ∀ x ∈ V,
      ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
        (g : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom ∧
        β⁻¹ * x * β = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hidx : ¬ 3 ∣ (d4B0 K σ).index := by
    rw [d4B0_index_all hp hf K hK σ hσ]
    exact d4_monomial_index_not_dvd_all hp hf K hK σ hσ hq
  obtain ⟨β, hβ⟩ := exists_conj_mem_of_isPGroup_three (d4B0 K σ) hidx V hV
  refine ⟨β, fun x hx => ?_⟩
  obtain ⟨g, hg, δ, h⟩ := hβ x hx
  exact ⟨g, δ, Subgroup.mem_subgroupOf.1 hg, h⟩

end Monomial

section FixedLine


open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (graphFixedRootWeylHom_mem_rootCharStabilizer
  d4_order_three_smul_single_zero rootChar_d4_apply d4LatVec)

theorem d4_fixed_line_all {p f : ℕ} (hq : (p ^ f) % 3 = 1) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K)
    (hv : (v : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hv1 : v ≠ 1) (hv3 : v ^ 3 = 1)
    (hnmono : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom)
    (hnT : (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hW3 : (graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom
      ⟨(n : ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hnmono, n.2⟩⟩) ^ 3 = 1)
    (hδ : δ = σ ∨ δ = σ⁻¹)
    (hfix : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) v = v) :
    ∃ ω : Kˣ, Units.map σ.toRingHom.toMonoidHom ω = ω ∧ ω ^ 3 = 1 ∧ ω ≠ 1 ∧
      (v : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![ω, ω, 1, ω] := by
  classical
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_inf.1 hv).1
  have hΓ : (v : ModGL TwistTag.D4.tag K) ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedRootGroup_le _ _ _ v.2
  have hcompat : ∀ i, a (TwistTag.D4.perm i) = Units.map σ.toRingHom.toMonoidHom (a i) := by
    apply compat_of_twistHom_rootDiagUnit
    rw [← ha]
    exact ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hΓ).2
  set σU : Kˣ →* Kˣ := Units.map σ.toRingHom.toMonoidHom with hσU
  have hσUpow : ∀ x : Kˣ, σU x = x ^ (p ^ f) := fun x => Units.ext (by simp [σU, hσ])
  have hcube : ∀ i, a i ^ 3 = 1 := by
    intro i
    have h := congrArg Subtype.val hv3
    rw [Subgroup.coe_pow, Subgroup.coe_one, ha, rootDiagUnit_pow,
      ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)] at h
    have := congrFun (rootDiagUnit_injective h) i
    simpa using this
  have hσfix : ∀ i, σU (a i) = a i := by
    intro i
    rw [hσUpow]
    have hq' : p ^ f = 3 * ((p ^ f) / 3) + 1 := by omega
    rw [hq', pow_succ, pow_mul, hcube i, one_pow, one_mul]
  have h10 : a (1 : Fin 4) = a (0 : Fin 4) := (hcompat (0 : Fin 4)).trans (hσfix _)
  have h30 : a (3 : Fin 4) = a (0 : Fin 4) :=
    (hcompat (1 : Fin 4)).trans ((hσfix _).trans h10)
  have hδfix : ∀ i, Units.map δ.toRingHom.toMonoidHom (a i) = a i := by
    intro i
    rcases hδ with rfl | rfl
    · exact hσfix i
    · refine Units.ext ?_
      have h1 : σ (a i : K) = (a i : K) := congrArg Units.val (hσfix i)
      change (σ⁻¹ : K ≃+* K) (a i : K) = (a i : K)
      rw [RingAut.inv_apply, RingEquiv.symm_apply_eq]
      exact h1.symm
  have hfa : fieldActor (t := TwistTag.D4) σ δ v = v := by
    refine Subtype.ext ?_
    rw [coe_fieldActor, ha, units_map_entrywiseHom_rootDiagUnit]
    exact congrArg _ (funext hδfix)
  have hfix' : (n : ModGL TwistTag.D4.tag K) * (v : ModGL TwistTag.D4.tag K) *
      (n : ModGL TwistTag.D4.tag K)⁻¹ = (v : ModGL TwistTag.D4.tag K) := by
    rw [MulAut.mul_apply, hfa, MulAut.conj_apply] at hfix
    exact congrArg Subtype.val hfix
  have hcomm : rootDiagUnit TwistTag.D4.tag a * (n : ModGL TwistTag.D4.tag K) *
      (rootDiagUnit TwistTag.D4.tag a)⁻¹ = n := by
    rw [ha] at hfix'
    rw [mul_inv_eq_iff_eq_mul]
    exact (mul_inv_eq_iff_eq_mul.1 hfix').symm
  set g : graphFixedRootMonomial TwistTag.D4 K σ.toRingHom :=
    ⟨(n : ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hnmono, n.2⟩⟩ with hg
  have hst : ∀ u, rootChar a (graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom g • u) =
      rootChar a u :=
    graphFixedRootWeylHom_mem_rootCharStabilizer TwistTag.D4 σ.toRingHom g a hcomm
  have hwmem : graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom g ∈ relWeylTwist TwistTag.D4 := by
    rw [← graphFixedRootWeylHom_range TwistTag.D4 K σ.toRingHom]
    exact ⟨g, rfl⟩
  have hw1 : graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom g ≠ 1 := by
    intro h
    have h' : g ∈ (graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom).ker := h
    rw [graphFixedRootWeylHom_ker, Subgroup.mem_subgroupOf] at h'
    exact hnT (Subgroup.mem_inf.1 h').1
  have hb : a (2 : Fin 4) = 1 := by
    have h0 := hst (d4LatVec 1 0 0 0)
    rcases d4_order_three_smul_single_zero hwmem hw1 hW3 with hk | hk
    · rw [hk, rootChar_d4_apply, rootChar_d4_apply] at h0
      simp [d4LatVec] at h0
      exact h0
    · rw [hk, rootChar_d4_apply, rootChar_d4_apply] at h0
      simp [d4LatVec] at h0
      rw [h10, h30] at h0
      have h2 : (a (2 : Fin 4))⁻¹ = 1 := by
        calc (a (2 : Fin 4))⁻¹ = a (0 : Fin 4) * ((a (0 : Fin 4))⁻¹ * (a (2 : Fin 4))⁻¹ *
              (a (0 : Fin 4))⁻¹) * a (0 : Fin 4) := by group
          _ = a (0 : Fin 4) * a (0 : Fin 4) * a (0 : Fin 4) := by rw [h0]
          _ = a (0 : Fin 4) ^ 3 := (pow_three' _).symm
          _ = 1 := hcube _
      exact inv_eq_one.1 h2
  have hω1 : a (0 : Fin 4) ≠ 1 := by
    intro h0
    apply hv1
    refine Subtype.ext ?_
    have h1 : a = 1 := by
      funext i
      fin_cases i
      · exact h0
      · exact h10.trans h0
      · exact hb
      · exact h30.trans h0
    rw [ha, h1, rootDiagUnit_one]
    rfl
  refine ⟨a (0 : Fin 4), hσfix _, hcube _, hω1, ?_⟩
  rw [ha]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact h10
  · exact hb
  · exact h30

end FixedLine

section Toral


open CFSG.GH74.GLS.Stage2.OddAut CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (normSeq_three exists_unit_pow_sub_one_eq d4_perm_zero
  d4_perm_one d4_perm_two d4_perm_three conj_twist_eq)

theorem d4_toral_reduction_all {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hn : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hN : normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = 1) :
    ∃ t s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      fieldActor (t := TwistTag.D4) σ σ s = s ∧ s ^ 3 = 1 ∧
      t * n * (fieldActor (t := TwistTag.D4) σ σ t)⁻¹ = s ∧
      ∃ d : Kˣ, Units.map σ.toRingHom.toMonoidHom d = d ∧ d ^ 3 = 1 ∧
        (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] := by
  classical
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hpar : ringChar K = 2 ∨ ∃ m, Odd m ∧ ∀ c, σ c = c ^ m :=
    ringChar_eq_two_or_odd_pow hp hK σ hσ
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_inf.1 hn).1
  have hΓ : (n : ModGL TwistTag.D4.tag K) ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedRootGroup_le _ _ _ n.2
  have hcompat : ∀ i, l (TwistTag.D4.perm i) = Units.map σ.toRingHom.toMonoidHom (l i) := by
    apply compat_of_twistHom_rootDiagUnit
    rw [← hl]
    exact ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hΓ).2
  set σU : Kˣ →* Kˣ := Units.map σ.toRingHom.toMonoidHom with hσU
  have hσUpow : ∀ x : Kˣ, σU x = x ^ (p ^ f) := fun x => Units.ext (by simp [σU, hσ])
  have hσU3 : ∀ x : Kˣ, σU (σU (σU x)) = x := fun x => Units.ext (hσ3 x)
  have hN' : rootDiagUnit TwistTag.D4.tag
      (l * (fun i => σU (l i)) * (fun i => σU (σU (l i)))) = 1 := by
    have h := congrArg Subtype.val hN
    rw [normSeq_three] at h
    change (n : ModGL TwistTag.D4.tag K) *
      Units.map (entrywiseHom σ.toRingHom) (n : ModGL TwistTag.D4.tag K) *
      Units.map (entrywiseHom σ.toRingHom)
        (Units.map (entrywiseHom σ.toRingHom) (n : ModGL TwistTag.D4.tag K)) = 1 at h
    rw [hl, units_map_entrywiseHom_rootDiagUnit, units_map_entrywiseHom_rootDiagUnit,
      ← rootDiagUnit_mul, ← rootDiagUnit_mul] at h
    exact h
  have hcocycle : ∀ i, l i * σU (l i) * σU (σU (l i)) = 1 := fun i => by
    have := congrFun (rootDiagUnit_injective (hN'.trans rootDiagUnit_one.symm)) i
    simpa using this
  have hq2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  set q := p ^ f with hqdef
  have hl0N : l (0 : Fin 4) ^ (q ^ 2 + q + 1) = 1 := by
    have h0 := hcocycle (0 : Fin 4)
    rw [hσUpow, hσUpow] at h0
    have e : l (0 : Fin 4) * l (0 : Fin 4) ^ q * (l (0 : Fin 4) ^ q) ^ q =
        l (0 : Fin 4) ^ (q ^ 2 + q + 1) := by
      rw [← pow_mul, sq, pow_add, pow_add, pow_one]
      ac_rfl
    rw [← e]
    exact h0
  obtain ⟨b, hb⟩ := exists_unit_pow_sub_one_eq hq2 hK (l (0 : Fin 4)) hl0N
  have hσb : σU b = b * l (0 : Fin 4) := by
    rw [hσUpow, ← hb, mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q)]
  have hl1 : l (1 : Fin 4) = σU (l (0 : Fin 4)) := by
    have := hcompat (0 : Fin 4)
    rwa [d4_perm_zero] at this
  have hl3 : l (3 : Fin 4) = σU (l (1 : Fin 4)) := by
    have := hcompat (1 : Fin 4)
    rwa [d4_perm_one] at this
  have hl2 : l (2 : Fin 4) = σU (l (2 : Fin 4)) := by
    have := hcompat (2 : Fin 4)
    rwa [d4_perm_two] at this
  have hσσb : σU (σU b) = σU b * l (1 : Fin 4) := by
    rw [hl1, ← map_mul, ← hσb]
  have hb3 : σU (σU b) * l (3 : Fin 4) = b := by
    have := hσU3 b
    rw [hσσb, map_mul, ← hl3] at this
    exact this
  have hσl2 : σU (l (2 : Fin 4)) = l (2 : Fin 4) := hl2.symm
  have hl2cube : l (2 : Fin 4) ^ 3 = 1 := by
    have := hcocycle (2 : Fin 4)
    rw [hσl2, hσl2] at this
    rw [pow_three]
    simpa [mul_assoc] using this
  let u : Fin TwistTag.D4.tag.rank → Kˣ := ![b, σU b, 1, σU (σU b)]
  let sv : Fin TwistTag.D4.tag.rank → Kˣ := ![1, 1, l (2 : Fin 4), 1]
  have hucompat : ∀ i, u (TwistTag.D4.perm i) = σU (u i) := by
    intro i
    fin_cases i
    · exact rfl
    · exact rfl
    · show u (TwistTag.D4.perm (2 : Fin 4)) = σU (u (2 : Fin 4))
      rw [d4_perm_two]
      exact (map_one σU).symm
    · show u (TwistTag.D4.perm (3 : Fin 4)) = σU (u (3 : Fin 4))
      rw [d4_perm_three]
      exact (hσU3 b).symm
  have hsvcompat : ∀ i, sv (TwistTag.D4.perm i) = σU (sv i) := by
    intro i
    fin_cases i
    · show sv (TwistTag.D4.perm (0 : Fin 4)) = σU (sv (0 : Fin 4))
      rw [d4_perm_zero]
      exact (map_one σU).symm
    · show sv (TwistTag.D4.perm (1 : Fin 4)) = σU (sv (1 : Fin 4))
      rw [d4_perm_one]
      exact (map_one σU).symm
    · show sv (TwistTag.D4.perm (2 : Fin 4)) = σU (sv (2 : Fin 4))
      rw [d4_perm_two]
      exact hl2
    · show sv (TwistTag.D4.perm (3 : Fin 4)) = σU (sv (3 : Fin 4))
      rw [d4_perm_three]
      exact (map_one σU).symm
  have hmemt := rootDiagUnit_mem_graphFixedRootGroup_triality σ hσ3 hpar hucompat
  have hmems := rootDiagUnit_mem_graphFixedRootGroup_triality σ hσ3 hpar hsvcompat
  have hfun : u * l * (fun i => (σU (u i))⁻¹) = sv := by
    funext i
    fin_cases i
    · show b * l (0 : Fin 4) * (σU b)⁻¹ = 1
      rw [hσb]
      exact mul_inv_cancel _
    · show σU b * l (1 : Fin 4) * (σU (σU b))⁻¹ = 1
      rw [hσσb]
      exact mul_inv_cancel _
    · show (1 : Kˣ) * l (2 : Fin 4) * (σU 1)⁻¹ = l (2 : Fin 4)
      simp
    · show σU (σU b) * l (3 : Fin 4) * (σU (σU (σU b)))⁻¹ = 1
      rw [hσU3 b, hb3]
      exact mul_inv_cancel _
  have hsvfix : ∀ i, σU (sv i) = sv i := by
    intro i
    fin_cases i
    · exact map_one σU
    · exact map_one σU
    · exact hσl2
    · exact map_one σU
  refine ⟨⟨_, hmemt⟩, ⟨_, hmems⟩, ?_, ?_, ?_, l (2 : Fin 4), hσl2, hl2cube, rfl⟩
  · apply Subtype.ext
    show Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit TwistTag.D4.tag sv) =
      rootDiagUnit TwistTag.D4.tag sv
    rw [units_map_entrywiseHom_rootDiagUnit]
    exact congrArg _ (funext hsvfix)
  · apply Subtype.ext
    show (rootDiagUnit TwistTag.D4.tag sv) ^ 3 = 1
    rw [rootDiagUnit_pow, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)]
    refine congrArg _ (funext fun i => ?_)
    fin_cases i
    · exact one_pow 3
    · exact one_pow 3
    · exact hl2cube
    · exact one_pow 3
  · apply Subtype.ext
    show rootDiagUnit TwistTag.D4.tag u * (n : ModGL TwistTag.D4.tag K) *
      (Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit TwistTag.D4.tag u))⁻¹ =
        rootDiagUnit TwistTag.D4.tag sv
    rw [hl, units_map_entrywiseHom_rootDiagUnit, rootDiagUnit_inv, ← rootDiagUnit_mul,
      ← rootDiagUnit_mul]
    exact congrArg _ hfun

theorem d4_toral_conj_all {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hn : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hN : normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = 1) :
    ∃ y s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      fieldActor (t := TwistTag.D4) σ σ s = s ∧ s ^ 3 = 1 ∧
      MulAut.conj y * (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) * (MulAut.conj y)⁻¹ =
        MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ ∧
      ∃ d : Kˣ, Units.map σ.toRingHom.toMonoidHom d = d ∧ d ^ 3 = 1 ∧
        (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] := by
  obtain ⟨t, s, hs, hs3, hts, hd⟩ := d4_toral_reduction_all hp hf K hK σ hσ n hn hN
  refine ⟨t, s, hs, hs3, ?_, hd⟩
  rw [← hts]
  exact conj_twist_eq _ _ _

end Toral

section Frame


open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  WithConv
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (diagramMap_comm_trialityOpposition)

open scoped CFSG.ConvolutionPoints

theorem d4_diagram_centralizer_lang_all (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [IsAlgClosed k] [CharP k p] {e : ℕ} (he : 1 ≤ e) (c : ModGL TwistTag.D4.tag k)
    (hc : c ∈ graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k)) :
    ∃ z ∈ graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k),
      z⁻¹ * Units.map (entrywiseHom (iterateFrobenius k p e)) z = c := by
  obtain ⟨hZ, -, -, -⟩ := D4_diagram_centralizer_connected (k := k)
  obtain ⟨-, -, -, hlang⟩ :=
    exists_frobTwist_restriction (τ := TwistTag.D4.tag) (k := k) p hZ he 1 fun g hg => by
      rw [frobTwistGL_apply, inv_one, one_mul, mul_one]
      exact entrywiseFrobGL_mem_graphCentralizer_d4 p e hg
  obtain ⟨z, hz, hzc⟩ := hlang c hc
  refine ⟨z, hz, ?_⟩
  rw [frobTwistGL_apply, inv_one, one_mul, mul_one] at hzc
  exact hzc

theorem d4Minus_exists_frame_all {L : Type} [Field L] [IsAlgClosed L] (p : ℕ) [Fact p.Prime]
    [CharP L p] {f : ℕ} (hf : 1 ≤ f) :
    ∃ g₀ : ModGL TwistTag.D4.tag L, g₀ ∈ adjointGroup TwistTag.D4.tag L ∧
      diagramMap TwistTag.D4 L * g₀ = g₀ * diagramMap TwistTag.D4 L ∧
      twistHom TwistTag.D4 L (iterateFrobenius L p f) g₀ = g₀ * trialityOpposition L := by
  have hzC : trialityOpposition L ∈ adjointGroup TwistTag.D4.tag L :=
    monomialSubgroup_le_adjointGroup' trialityOpposition_mem_monomialSubgroup
  have hz : trialityOpposition L ∈
      graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L) :=
    Subgroup.mem_inf.2 ⟨hzC, Subgroup.mem_centralizer_singleton_iff.2
      diagramMap_comm_trialityOpposition.symm⟩
  obtain ⟨g, hg, hgz⟩ := d4_diagram_centralizer_lang_all p L hf (trialityOpposition L) hz
  obtain ⟨hgC, hgP⟩ := Subgroup.mem_inf.1 hg
  have hgP' : diagramMap TwistTag.D4 L * g = g * diagramMap TwistTag.D4 L :=
    (Subgroup.mem_centralizer_singleton_iff.1 hgP).symm
  refine ⟨g, hgC, hgP', ?_⟩
  rw [twistHom_apply]
  have h1 : Units.map (entrywiseHom (iterateFrobenius L p f)) g = g * trialityOpposition L := by
    rw [← hgz]
    group
  have h2 : diagramMap TwistTag.D4 L * (g * trialityOpposition L) =
      (g * trialityOpposition L) * diagramMap TwistTag.D4 L := by
    rw [← mul_assoc, hgP', mul_assoc, diagramMap_comm_trialityOpposition, ← mul_assoc]
  rw [h1, h2, mul_inv_cancel_right]

end Frame

section Delta


open CFSG.GH74.GLS.Stage2.Bender.Thm1 (d4_fieldActor_pow_three ringEquiv_ne_one_of_pow
  innPowSubgroup exists_pow_eq_of_eq_one_or_eq_or_eq_inv eq_or_eq_inv_of_pow_three_eq_one
  exists_conj_mem_conjPowSubgroup pow_eq_one_or_eq_or_eq_inv_of_pow_three_eq_one)

theorem d4_exists_conj_le_Bδ_all {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (N : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hidx : ¬ 3 ∣ N.index)
    (hstab : ∀ n ∈ N, fieldActor (t := TwistTag.D4) σ σ n ∈ N)
    (V : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hV : ∀ x ∈ V, x ^ 3 = 1) :
    ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ∀ x ∈ V,
      ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K), g ∈ N ∧
        (δ = 1 ∨ δ = σ ∨ δ = σ⁻¹) ∧
        β⁻¹ * x * β = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ := by
  classical
  have hNF := existsUnique_conj_mul_fieldActor_D4 hp hf hK σ hσ
  obtain ⟨⟨Θ, hΘ, -⟩, hcyc, hcard⟩ := exists_fieldHom_D4 hp hf hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hδ3 : fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := d4_fieldActor_pow_three K hK σ hσ
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    have h := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ, RingAut.mul_apply] using h
  have hσ1 : σ ≠ 1 :=
    ringEquiv_ne_one_of_pow (Nat.one_lt_pow (by omega) hp.one_lt) hK σ hσ
  have hpow : ∀ j : ℕ, fieldActor (t := TwistTag.D4) σ σ ^ j = fieldActor σ (σ ^ j) := fun j =>
    (map_pow (fieldActorHom (t := TwistTag.D4) σ) σ j).symm
  have hinn : ∀ (h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (j : ℕ),
      MulAut.conj h = fieldActor (t := TwistTag.D4) σ σ ^ j → h = 1 := by
    intro h j hj
    have h1 : MulAut.conj h = MulAut.conj h * fieldActor (t := TwistTag.D4) σ 1 := by
      rw [fieldActor_one, mul_one]
    have h2 : MulAut.conj h = MulAut.conj 1 * fieldActor (t := TwistTag.D4) σ (σ ^ j) := by
      rw [hj, hpow, map_one, one_mul]
    exact congrArg Prod.fst ((hNF (MulAut.conj h)).unique
      (y₁ := (h, 1)) (y₂ := (1, σ ^ j)) h1 h2)
  have hVA : V ≤ innPowSubgroup (fieldActor (t := TwistTag.D4) σ σ) hδ3 := by
    intro x hx
    obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF x
    have hΘx : Θ x = δ := hΘ x g δ hgδ
    have hδ3' : δ ^ 3 = 1 := by rw [← hΘx, ← map_pow, hV x hx, map_one]
    obtain ⟨j, hj⟩ : ∃ j : ℕ, δ = σ ^ j := by
      by_cases hδ1 : δ = 1
      · exact ⟨0, by rw [hδ1, pow_zero]⟩
      · exact exists_pow_eq_of_eq_one_or_eq_or_eq_inv hσ3
          (Or.inr (eq_or_eq_inv_of_pow_three_eq_one hσ1 hσ3 hδ1 hδ3'))
    exact ⟨g, Subgroup.mem_top _, j, by rw [hgδ, hj, hpow]⟩
  obtain ⟨β, hβ⟩ := exists_conj_mem_conjPowSubgroup hδ3 hinn hidx hstab hVA hV
  refine ⟨β, fun x hx => ?_⟩
  obtain ⟨g, hg, j, hgj⟩ := hβ x hx
  exact ⟨g, σ ^ j, hg, pow_eq_one_or_eq_or_eq_inv_of_pow_three_eq_one hσ3 j, by
    rw [hgj, hpow]⟩

end Delta

section MinusFixedLine


open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.OddAut
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (D4MinusFrame d4MinusPsi d4MinusPsi_injective
  d4MinusPsi_mem_range_iff d4MnFL_psi_fieldActor_conj d4MnFL_conj_Q_rootDiagUnit
  d4MnFL_relWeylTwist_of_fixed d4MnFL_weyl_cube d4_fieldActor_pow_three normSeq_three
  d4_order_three_smul_single_zero rootChar_d4_apply d4LatVec)

theorem d4Minus_fixed_line_all {p f : ℕ} [Fact p.Prime] (hp : p.Prime) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p]
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀)
    (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K)
    (hv : d4MinusPsi σ L g₀ v ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L p f)))
    (hv1 : v ≠ 1) (hv3 : v ^ 3 = 1)
    (hnM : d4MinusPsi σ L g₀ n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnT : d4MinusPsi σ L g₀ n ∉ torusGroup TwistTag.D4.tag L)
    (hδ : δ = σ ∨ δ = σ⁻¹)
    (he3 : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) ^ 3 = 1)
    (hfix : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) v = v) :
    ∃ A : Lˣ, A ^ 3 = 1 ∧ A ≠ 1 ∧
      d4MinusPsi σ L g₀ v = rootDiagUnit TwistTag.D4.tag ![A, A, 1, A] := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  obtain ⟨hg₀C, hg₀P, hg₀F⟩ := hg₀
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  set ψ := d4MinusPsi σ L g₀ with hψdef
  have hinj : Function.Injective ψ := d4MinusPsi_injective g₀
  have hrange := d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F
  rw [d4Q_twistedTorus Fr] at hv
  obtain ⟨b, hb, hbv⟩ := Subgroup.mem_map.1 hv
  have hψv : ψ v = rootDiagUnit TwistTag.D4.tag b := hbv.symm
  have hcube : ∀ i, b i ^ 3 = 1 := by
    intro i
    have h : ψ (v ^ 3) = 1 := by rw [hv3, map_one]
    rw [map_pow, hψv, rootDiagUnit_pow, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L)] at h
    have := congrFun (rootDiagUnit_injective h) i
    simpa using this
  obtain ⟨hb1, hb3⟩ := d4Q_eq_of_pow_eq_one hFr (p := 3) (by omega) hb hcube
  have h10 : b (1 : Fin 4) = b (0 : Fin 4) := hb1
  have h30 : b (3 : Fin 4) = b (0 : Fin 4) := hb3
  have hbρ : ∀ i, b (TwistTag.D4.perm i) = b i := by
    intro i
    rcases fin_cases i with rfl | rfl | rfl | rfl
    · rw [perm_i0]
      exact hb1
    · rw [perm_i1]
      exact hb3.trans hb1.symm
    · rw [perm_i2]
    · rw [perm_i3]
      exact hb3.symm
  obtain ⟨Q, hQ, hΨ'⟩ := d4MnFL_psi_fieldActor_conj (g₀ := g₀) Fr hcomm hg₀P hδ
  have hΨ : ∀ y, ψ (fieldActor (t := TwistTag.D4) σ δ y) = Q⁻¹ * ψ y * Q := hΨ'
  have hΦv : fieldActor (t := TwistTag.D4) σ δ v = v := by
    apply hinj
    rw [hΨ, hψv, d4MnFL_conj_Q_rootDiagUnit hQ hbρ]
  have hnv : n * v * n⁻¹ = v := by
    rw [MulAut.mul_apply, hΦv, MulAut.conj_apply] at hfix
    exact hfix
  have hxv : ψ n * rootDiagUnit TwistTag.D4.tag b * (ψ n)⁻¹ = rootDiagUnit TwistTag.D4.tag b := by
    rw [← hψv, ← map_inv, ← map_mul, ← map_mul, hnv]
  obtain ⟨w, k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets hnM
  have hxF : trialityOpposition L * twistHom TwistTag.D4 L Fr (ψ n) *
      (trialityOpposition L)⁻¹ = ψ n := ((hrange (ψ n)).1 ⟨n, rfl⟩).2
  have hwrel : w ∈ relWeylTwist TwistTag.D4 := d4MnFL_relWeylTwist_of_fixed Fr hk hxk hxF
  have hxW : MapsRootLines (ψ n) w := hxk ▸ mapsRootLines_mul_canonicalRep hk w
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hnT
    rw [hxk, canonicalRep_one, mul_one]
    exact hk
  have hΦ3 : (fieldActor (t := TwistTag.D4) σ δ) ^ 3 = 1 := by
    have h := d4_fieldActor_pow_three K hK σ hσ
    rcases hδ with h' | h'
    · rw [h']
      exact h
    · have h2 : fieldActor (t := TwistTag.D4) σ σ⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹ :=
        map_inv (fieldActorHom (t := TwistTag.D4) σ) σ
      rw [h', h2, inv_pow, h, inv_one]
  have hN := normSeq_eq_one_of_pow_eq_one hZ hΦ3 he3
  rw [normSeq_three] at hN
  have hcyc : ψ n * (Q⁻¹ * ψ n * Q) * (Q⁻¹ * (Q⁻¹ * ψ n * Q) * Q) = 1 := by
    have h := congrArg ψ hN
    simpa only [map_mul, hΨ, map_one] using h
  have hw3 : w ^ 3 = 1 := d4MnFL_weyl_cube hQ hwrel hxW hcyc
  have hdbk : rootDiagUnit TwistTag.D4.tag b * k = k * rootDiagUnit TwistTag.D4.tag b :=
    rootDiagUnit_mul_comm_of_mem_torusGroup b hk
  have hconj : rootDiagUnit TwistTag.D4.tag b =
      canonicalRep (coxeterSystem TwistTag.D4.tag) L w * rootDiagUnit TwistTag.D4.tag b *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹ := by
    set nw := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hnw
    set db := rootDiagUnit TwistTag.D4.tag b with hdb
    rw [hxk] at hxv
    have h1 : k * (nw * db * nw⁻¹) * k⁻¹ = db := by
      calc k * (nw * db * nw⁻¹) * k⁻¹ = k * nw * db * (k * nw)⁻¹ := by group
        _ = db := hxv
    have h2 : nw * db * nw⁻¹ = k⁻¹ * db * k := by
      calc nw * db * nw⁻¹ = k⁻¹ * (k * (nw * db * nw⁻¹) * k⁻¹) * k := by group
        _ = k⁻¹ * db * k := by rw [h1]
    rw [h2, mul_assoc, hdbk, inv_mul_cancel_left]
  have hchar : ∀ u, rootChar b (w • u) = rootChar b u :=
    (rootDiagUnit_eq_conj_canonicalRep_iff b b w).1 hconj
  have hb2 : b (2 : Fin 4) = 1 := by
    have h0 := hchar (d4LatVec 1 0 0 0)
    rcases d4_order_three_smul_single_zero hwrel hw1 hw3 with hk | hk
    · rw [hk, rootChar_d4_apply, rootChar_d4_apply] at h0
      simp [d4LatVec] at h0
      exact h0
    · rw [hk, rootChar_d4_apply, rootChar_d4_apply] at h0
      simp [d4LatVec] at h0
      rw [h10, h30] at h0
      have h2 : (b (2 : Fin 4))⁻¹ = 1 := by
        calc (b (2 : Fin 4))⁻¹ = b (0 : Fin 4) * ((b (0 : Fin 4))⁻¹ * (b (2 : Fin 4))⁻¹ *
              (b (0 : Fin 4))⁻¹) * b (0 : Fin 4) := by group
          _ = b (0 : Fin 4) * b (0 : Fin 4) * b (0 : Fin 4) := by rw [h0]
          _ = b (0 : Fin 4) ^ 3 := (pow_three' _).symm
          _ = 1 := hcube _
      exact inv_eq_one.1 h2
  have hA1 : b (0 : Fin 4) ≠ 1 := by
    intro h0
    apply hv1
    apply hinj
    have h1 : b = 1 := by
      funext i
      fin_cases i
      · exact h0
      · exact h10.trans h0
      · exact hb2
      · exact h30.trans h0
    rw [hψv, h1, rootDiagUnit_one, map_one]
  refine ⟨b (0 : Fin 4), hcube _, hA1, ?_⟩
  rw [hψv]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact h10
  · exact hb2
  · exact h30

end MinusFixedLine

end CFSG.HardMathSupport.Timmesfeld.CrossChar
