module

public import CFSG.CharacterTheory.Semidihedral.SameParameterQuotientTransport
public import CFSG.Sporadic.Mathieu.M11
public meta import CFSG.Sporadic.Mathieu.M11
public meta import CFSG.Blueprint.NativeSporadic
public meta import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order
public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenter
public import CFSG.CharacterTheory.Wreathed.ProjectiveTwoParameterUniqueness
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeThreeReducedCentralizer
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeThreeModelRegularity
public import CFSG.CharacterTheory.Semidihedral.Local.OddKernelLocalParameter
public import CFSG.CharacterTheory.Semidihedral.SameParameterInheritance
public import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularityInputs
public import Certificates.Certificate8046
public import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularityCoordInputs
public import Certificates.Certificate8048
public import Certificates.Certificate8049
public import Certificates.Certificate3120
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public meta import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Semidihedral.Local.OddCoreQuotientSimple
public meta import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.Wreathed.BrauerWong
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierParityDescriptions
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.Semidihedral.ProperSubgroupRegularity

universe u v

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Sporadic.Mathieu
open CFSG.Blueprint
open CFSG.Open CFSG.Semidihedral
open CFSG.Semidihedral.Principal.DegreeThreeReducedCentralizer
open CFSG.Wreathed.OddLinearThreeCentralizerCore
open CFSG.TwoRankLowerBound.Helpers
open CFSG.Semidihedral.SameParameterQuotientTransport
open CFSG.Semidihedral.SameParameterInheritance

theorem m11_two_coordinates_closed :
    (∃ x, m11TwoCoordinates x = 1) ∧
      (∀ x y, ∃ z, m11TwoCoordinates x * m11TwoCoordinates y = m11TwoCoordinates z) ∧
      (∀ x, ∃ y, (m11TwoCoordinates x)⁻¹ = m11TwoCoordinates y) :=
  Certificates.certificate8046.1

theorem m11_two_coordinates_injective :
    Function.Injective m11TwoCoordinates :=
  Certificates.certificate8046.2.1

theorem m11_two_coordinates_involution_fusion :
    ∀ x, m11TwoCoordinates x ≠ 1 → m11TwoCoordinates x ^ 2 = 1 →
      ∃ i : Fin 5, m11InvolutionConjugator i * m11TwoCoordinates x *
        (m11InvolutionConjugator i)⁻¹ = m11a :=
  Certificates.certificate8046.2.2.1

theorem m11_centralizer_coordinates_injective :
    Function.Injective m11CentralizerCoordinates :=
  Certificates.certificate8046.2.2.2.1

@[expose] def m11TwoSubgroup : Subgroup NativeSporadic.M11 where
  carrier := Set.range m11TwoCoordinates
  one_mem' := m11_two_coordinates_closed.1
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := m11_two_coordinates_closed.2.1 x y
    exact ⟨z, hz.symm⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := m11_two_coordinates_closed.2.2 x
    exact ⟨y, hy.symm⟩

theorem card_m11TwoSubgroup : Nat.card m11TwoSubgroup = 16 := by
  change Nat.card (Set.range m11TwoCoordinates) = 16
  rw [Nat.card_range_of_injective m11_two_coordinates_injective]
  norm_num [Nat.card_prod]

@[expose] def m11BaseFour : Fin 4 ↪ Fin 11 where
  toFun i := ⟨i.val, by omega⟩
  inj' i j h := Fin.ext (show i.val = j.val from
    congrArg (fun x : Fin 11 => x.val) h)

@[expose] def m11FourImages (g : NativeSporadic.M11) : Fin 4 ↪ Fin 11 where
  toFun i := (g : Equiv.Perm (Fin 11)) (m11BaseFour i)
  inj' := (g : Equiv.Perm (Fin 11)).injective.comp m11BaseFour.injective

theorem m11_base_four_fix_eq_one (g : NativeSporadic.M11)
    (hfix : ∀ i, g.val (m11BaseFour i) = m11BaseFour i) : g = 1 := by
  have hmem : ∀ i, i ≤ 4 → g ∈ lvl Native.m11Data m11a m11b i := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [lvl_zero m11_hyp]
      exact Subgroup.mem_top g
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      apply ((chain m11_hyp).2.1 i (by change i < 4; omega) g hprev).mp
      have hbase : Native.m11Data.base[i]! = i := by
        have hi4 : i < 4 := by omega
        interval_cases i <;> rfl
      rw [hbase]
      change CFSG.Sporadic.Th.idx 11 g i = i
      rw [CFSG.Sporadic.Th.idx_of_lt g (by omega)]
      exact congrArg Fin.val (hfix ⟨i, by omega⟩)
  have hcard : Nat.card (lvl Native.m11Data m11a m11b 4) = 1 := by
    have hc := (chain m11_hyp).2.2 4 (by decide)
    change _ = ∏ l ∈ Finset.Ico 4 4, _ at hc
    simpa only [Finset.Ico_self, Finset.prod_empty] using hc
  have : Subsingleton (lvl Native.m11Data m11a m11b 4) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  exact congrArg Subtype.val
    (Subsingleton.elim (⟨g, hmem 4 le_rfl⟩ : lvl Native.m11Data m11a m11b 4) 1)

theorem m11_four_images_injective :
    Function.Injective m11FourImages := by
  intro g h hgh
  have hfix : h⁻¹ * g = 1 := m11_base_four_fix_eq_one _ fun i => by
    have hi := DFunLike.congr_fun hgh i
    change h.val.symm (g.val (m11BaseFour i)) = m11BaseFour i
    change g.val (m11BaseFour i) = h.val (m11BaseFour i) at hi
    rw [hi, h.val.symm_apply_apply]
  exact (inv_mul_eq_one.mp hfix).symm

theorem m11_four_images_surjective :
    Function.Surjective m11FourImages := by
  apply ((Nat.bijective_iff_injective_and_card m11FourImages).mpr ?_).surjective
  refine ⟨m11_four_images_injective, ?_⟩
  rw [card_M11, Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
  norm_num

theorem m11_four_point_determination
    (a : Fin 4 → Fin 11) (ha : Function.Injective a)
    (g h : NativeSporadic.M11)
    (heq : ∀ i, (g : Equiv.Perm (Fin 11)) (a i) = (h : Equiv.Perm (Fin 11)) (a i)) : g = h := by
  obtain ⟨k, hk⟩ := m11_four_images_surjective ⟨a, ha⟩
  apply mul_right_cancel (b := k)
  apply m11_four_images_injective
  apply Function.Embedding.ext
  intro i
  have hki : (k : Equiv.Perm (Fin 11)) (m11BaseFour i) = a i :=
    DFunLike.congr_fun hk i
  change (g : Equiv.Perm (Fin 11)) ((k : Equiv.Perm (Fin 11)) (m11BaseFour i)) =
    (h : Equiv.Perm (Fin 11)) ((k : Equiv.Perm (Fin 11)) (m11BaseFour i))
  rw [hki]
  exact heq i

theorem card_M11CentralizerImages :
    Nat.card M11CentralizerImages = 48 :=
  Certificates.certificate8046.2.2.2.2.2.2

theorem m11_centralizer_base_facts :
    Function.Injective m11CentralizerBase ∧
    (∀ i : Fin 3, m11gA (m11CentralizerBase i.castSucc) = m11CentralizerBase i.castSucc) ∧
    m11gA (m11CentralizerBase 3) ≠ m11CentralizerBase 3 :=
  Certificates.certificate8046.2.2.2.2.1

@[expose] def m11CentralizerImage
    (g : C m11a) : M11CentralizerImages :=
  ⟨fun i => (g.val.val : Equiv.Perm (Fin 11)) (m11CentralizerBase i), by
    refine ⟨g.val.val.injective.comp m11_centralizer_base_facts.1, ?_, ?_⟩
    · intro i
      have hc := congrArg (fun k : NativeSporadic.M11 => k.val (m11CentralizerBase i.castSucc))
        (Subgroup.mem_centralizer_singleton_iff.mp g.property)
      change g.val.val (m11gA (m11CentralizerBase i.castSucc)) =
        m11gA (g.val.val (m11CentralizerBase i.castSucc)) at hc
      rw [m11_centralizer_base_facts.2.1 i] at hc
      exact hc.symm
    · intro hfix
      have hc := congrArg (fun k : NativeSporadic.M11 => k.val (m11CentralizerBase 3))
        (Subgroup.mem_centralizer_singleton_iff.mp g.property)
      change g.val.val (m11gA (m11CentralizerBase 3)) =
        m11gA (g.val.val (m11CentralizerBase 3)) at hc
      rw [hfix] at hc
      exact m11_centralizer_base_facts.2.2 (g.val.val.injective hc)⟩

theorem m11_centralizer_image_injective :
    Function.Injective m11CentralizerImage := by
  intro g h heq
  apply Subtype.ext
  apply m11_four_point_determination m11CentralizerBase m11_centralizer_base_facts.1
  intro i
  exact congrFun (congrArg Subtype.val heq) i

theorem card_m11_generator_centralizer :
    Nat.card (C m11a) = 48 := by
  apply le_antisymm
  · have h := Nat.card_le_card_of_injective m11CentralizerImage
      m11_centralizer_image_injective
    rwa [card_M11CentralizerImages] at h
  · let F : (Fin 8 × Fin 2) × Fin 3 → C m11a := fun x =>
      ⟨m11CentralizerCoordinates x,
        Subgroup.mem_centralizer_singleton_iff.mpr (m11_centralizer_coordinates_commute x)⟩
    have hF : Function.Injective F := by
      intro x y h
      exact m11_centralizer_coordinates_injective (congrArg Subtype.val h)
    have h := Nat.card_le_card_of_injective F hF
    norm_num [Nat.card_prod] at h
    exact h

@[expose] def m11TwoSylow :
    Sylow 2 NativeSporadic.M11 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 m11TwoSubgroup :=
    IsPGroup.of_card (show Nat.card m11TwoSubgroup = 2 ^ 4 by
      rw [card_m11TwoSubgroup]; norm_num)
  apply hP.toSylow
  have hcard := m11TwoSubgroup.card_mul_index
  rw [card_m11TwoSubgroup, card_M11] at hcard
  have hindex : m11TwoSubgroup.index = 495 := by omega
  rw [hindex]
  decide

theorem m11_involution_conjugate
    (t : NativeSporadic.M11) (ht : orderOf t = 2) :
    ∃ g : NativeSporadic.M11, g * t * g⁻¹ = m11a := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Subgroup.zpowers t) := IsPGroup.of_card
    (show Nat.card (Subgroup.zpowers t) = 2 ^ 1 by rw [Nat.card_zpowers, ht]; norm_num)
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq NativeSporadic.M11 Q m11TwoSylow
  have hmap : Q.toSubgroup.map (MulAut.conj g).toMonoidHom = m11TwoSubgroup := by
    change (↑(g • Q) : Subgroup NativeSporadic.M11) = m11TwoSubgroup
    rw [hg]
    rfl
  let z := (MulAut.conj g) t
  have hzmem : z ∈ m11TwoSubgroup := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨t, hQ (Subgroup.mem_zpowers t), rfl⟩
  obtain ⟨x, hx⟩ := hzmem
  have hzord : orderOf z = 2 :=
    (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective t).trans ht
  have hxne : m11TwoCoordinates x ≠ 1 := by
    rw [hx]
    intro h
    rw [h, orderOf_one] at hzord
    omega
  have hxpow : m11TwoCoordinates x ^ 2 = 1 := by
    rw [hx, ← hzord]
    exact pow_orderOf_eq_one z
  obtain ⟨i, hi⟩ := m11_two_coordinates_involution_fusion x hxne hxpow
  refine ⟨m11InvolutionConjugator i * g, ?_⟩
  rw [hx] at hi
  simpa only [z, MulAut.conj_apply, mul_inv_rev, mul_assoc] using hi

theorem m11_centralizer_coordinates_surjective :
    Function.Surjective m11CentralizerCoordinate := by
  apply ((Nat.bijective_iff_injective_and_card m11CentralizerCoordinate).mpr ?_).surjective
  refine ⟨?_, ?_⟩
  · intro x y h
    exact m11_centralizer_coordinates_injective (congrArg Subtype.val h)
  · rw [card_m11_generator_centralizer]
    norm_num [Nat.card_prod]

theorem m11_local_three_obstruction_facts
    :
    m11LocalThreeC ≠ 1 ∧ m11LocalThreeC ^ 3 = 1 ∧
      (m11LocalThreeC * (m11ReflectionC * m11LocalThreeC * m11ReflectionC⁻¹)) ^ 2 ≠ 1 ∧
      (m11LocalThreeC * (m11ReflectionC * m11LocalThreeC * m11ReflectionC⁻¹)) ^ 4 = 1 :=
  Certificates.certificate8049

theorem m11_centralizer_three_fusion :
    ∀ x, m11CentralizerCoordinates x ≠ 1 → m11CentralizerCoordinates x ^ 3 = 1 →
      ∃ y, m11CentralizerCoordinates y * m11CentralizerCoordinates x *
        (m11CentralizerCoordinates y)⁻¹ = m11LocalThree :=
  Certificates.certificate8046.2.2.2.2.2.1

theorem m11_generator_centralizer_odd_core :
    N m11a = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := N m11a
  have hcop : (Nat.card K).Coprime (2 ^ 4) :=
    (CFSG.pPrimeCore_coprime_card (G := C m11a) (p := 2)).symm.pow_right 4
  have hcarddvd : Nat.card K ∣ 3 := hcop.dvd_mul_left.mp
    (show Nat.card K ∣ 2 ^ 4 * 3 by
      have hdvd := Subgroup.card_subgroup_dvd_card K
      rw [card_m11_generator_centralizer] at hdvd
      simpa using hdvd)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hcarddvd with hcardone | hcardthree
  · exact Subgroup.card_eq_one.mp hcardone
  · let : Fact (Nat.Prime 3) := ⟨by decide⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 (by rw [hcardthree])
    have hxord : orderOf (x : C m11a) = 3 :=
      (orderOf_injective K.subtype K.subtype_injective x).trans hx
    obtain ⟨z, hz⟩ := m11_centralizer_coordinates_surjective x
    have hzne : m11CentralizerCoordinates z ≠ 1 := by
      intro heq
      have hxone : (x : C m11a) = 1 := by
        rw [← hz]
        exact Subtype.ext heq
      rw [hxone, orderOf_one] at hxord
      omega
    have hzpow : m11CentralizerCoordinates z ^ 3 = 1 := by
      have h := congrArg Subtype.val (hxord ▸ pow_orderOf_eq_one (x : C m11a))
      rw [← hz] at h
      exact h
    obtain ⟨y, hy⟩ := m11_centralizer_three_fusion z hzne hzpow
    have hthree : m11LocalThreeC ∈ K := by
      have hmem := (inferInstance : K.Normal).conj_mem
        (x : C m11a) x.property (m11CentralizerCoordinate y)
      have heq : m11CentralizerCoordinate y * (x : C m11a) *
          (m11CentralizerCoordinate y)⁻¹ = m11LocalThreeC := by
        rw [← hz]
        apply Subtype.ext
        simpa [m11LocalThreeC, m11CentralizerCoordinate, m11CentralizerCoordinates,
          m11TwoCoordinates] using hy
      rwa [heq] at hmem
    let w := m11LocalThreeC * (m11ReflectionC * m11LocalThreeC * m11ReflectionC⁻¹)
    have hwmem : w ∈ K := K.mul_mem hthree
      ((inferInstance : K.Normal).conj_mem m11LocalThreeC hthree m11ReflectionC)
    have hword : orderOf w = 4 := orderOf_eq_prime_pow
      (p := 2) (n := 1) m11_local_three_obstruction_facts.2.2.1
        m11_local_three_obstruction_facts.2.2.2
    have hdvd : 4 ∣ Nat.card K := by
      rw [← hword, ← Subgroup.orderOf_mk w hwmem]
      exact orderOf_dvd_natCard (⟨w, hwmem⟩ : K)
    rw [hcardthree] at hdvd
    omega

theorem m11_involution_centralizer_card_and_odd_core
    (t : NativeSporadic.M11)
    (ht : orderOf t = 2) : Nat.card (C t) = 48 ∧ N t = ⊥ := by
  obtain ⟨g, hg⟩ := m11_involution_conjugate t ht
  have hgt : (MulAut.conj g) t = m11a := hg
  let theta : C t ≃* C m11a :=
    (CFSG.Wreathed.DegreeThreeModelFullCenter.originalCentralizerEquiv
      (MulAut.conj g) t).trans (MulEquiv.subgroupCongr (congrArg C hgt))
  refine ⟨(Nat.card_congr theta.toEquiv).trans card_m11_generator_centralizer, ?_⟩
  apply Subgroup.map_injective (f := theta.toMonoidHom) theta.injective
  rw [Subgroup.map_bot]
  change (CFSG.pPrimeCore 2 (C t)).map theta.toMonoidHom = ⊥
  rw [CFSG.pPrimeCore_map_iso]
  exact m11_generator_centralizer_odd_core

theorem centralizer_card_and_core_of_equiv {G : Type u} {G' : Type v}
    [Group G] [Group G'] (e : G ≃* G') (t : G)
    (hc : Nat.card (C (e t)) = 48) (hN : N (e t) = ⊥) :
    Nat.card (C t) = 48 ∧ N t = ⊥ := by
  let theta := CFSG.Wreathed.DegreeThreeModelFullCenter.originalCentralizerEquiv e t
  refine ⟨(Nat.card_congr theta.toEquiv).trans hc, ?_⟩
  apply Subgroup.map_injective (f := theta.toMonoidHom) theta.injective
  rw [Subgroup.map_bot]
  change (CFSG.pPrimeCore 2 (C t)).map theta.toMonoidHom = ⊥
  rw [CFSG.pPrimeCore_map_iso]
  exact hN

theorem stated_m11_involution_centralizer_card_and_core
    (G : Type u) [Group G]
    (hmodel : Nonempty (G ≃* CFSG.Assembly.LowTwoRank.StatedM11))
    (t : G) (ht : orderOf t = 2) : Nat.card (C t) = 48 ∧ N t = ⊥ := by
  obtain ⟨e⟩ := hmodel
  let theta := e.trans (MulEquiv.subgroupCongr
    CFSG.Semidihedral.GL2Recognition.lowTwoRankStatedM11_eq_nativeM11)
  have ht' : orderOf (theta t) = 2 :=
    (orderOf_injective theta.toMonoidHom theta.injective t).trans ht
  obtain ⟨hc, hN⟩ := m11_involution_centralizer_card_and_odd_core (theta t) ht'
  exact centralizer_card_and_core_of_equiv theta t hc hN

theorem sl3_field_three_center_eq_bot (F : Type u) [Field F]
    (hF : Nat.card F = 3) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  obtain ⟨c, hc3, he⟩ :=
    CFSG.Wreathed.OddLinearThreeCentralizerCore.center_eq_matrixScalar F g hg
  have hc2 : c ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := c)
    rw [Nat.card_units, hF] at h
    exact h
  have hc1 : c = 1 := by
    calc c = c ^ 3 := by rw [pow_succ, hc2, one_mul]
      _ = 1 := hc3
  subst c
  rw [← he]
  apply Subtype.ext
  simp [CFSG.Wreathed.OddLinearThreeCentralizerCore.matrixScalar]

theorem psl_three_three_involution_centralizer_card_and_core (G : Type) [Group G]
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 3 1)
    (t : G) (ht : orderOf t = 2) : Nat.card (C t) = 48 ∧ N t = ⊥ := by
  obtain ⟨_, F, hfield, hfinite, hcard, ⟨eModel⟩⟩ := hmodel
  have hF : Nat.card F = 3 := by simpa only [pow_one] using hcard
  let e := eModel.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
  have ht' : orderOf (e t) = 2 :=
    (orderOf_injective e.toMonoidHom e.injective t).trans ht
  let D := Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)
  have hD : D = ⊥ := sl3_field_three_center_eq_bot F hF
  have hDcard : Nat.card D = 1 := by rw [hD, Subgroup.card_bot]
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  have hq : 3 ≤ Nat.card F := by rw [hF]
  obtain ⟨z, ⟨hz, hzt⟩, _⟩ :=
    CFSG.Wreathed.OddLinearThreeCentralizerCore.unique_involution_lift F D le_rfl (e t) ht'
  have hc := CFSG.Wreathed.OddLinearThreeCentralizerCore.targetQuotientCentralizer_card
    F hodd D le_rfl z hz (e t) hzt
  have hn :=
    (targetQuotientCentralizer_core_structure F hodd hq D le_rfl z hz (e t) hzt).2.2.2
  have hcore : N (e t) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    change Nat.card (CFSG.pPrimeCore 2 (C (e t))) = 1
    rw [← CFSG.Wreathed.weakClosure_oddCore_eq_pPrimeCore]
    rw [hn, hF, hDcard, Nat.div_one]
    exact Nat.ordCompl_self_pow (p := 2) (k := 1) Nat.prime_two
  apply centralizer_card_and_core_of_equiv e t _ hcore
  rw [hc, hF, hDcard]
  norm_num

theorem card_intrinsic_gamma_of_centralizer48 {G : Type u} [Group G]
    (t : G) (ht : orderOf t = 2) (hc : Nat.card (C t) = 48) (hN : N t = ⊥) :
    Nat.card (Gamma t) = 24 := by
  have htC : orderOf (tInC t) = 2 :=
    (orderOf_injective (C t).subtype (C t).subtype_injective (tInC t)).symm.trans ht
  have hNZ : Nat.card (NZ t) = 2 := by
    change Nat.card (N t ⊔ Z t : Subgroup (C t)) = 2
    rw [hN, bot_sup_eq, Nat.card_zpowers, htC]
  have hcard := (NZ t).card_eq_card_quotient_mul_card_subgroup
  change Nat.card (C t) = Nat.card (Gamma t) * Nat.card (NZ t) at hcard
  rw [hc, hNZ] at hcard
  omega

theorem stated_psl_two_card_at_least_sixty (G : Type) [Group G]
    (p f : ℕ) (hpodd : Odd p) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 2 p f) :
    60 ≤ Nat.card G := by
  rw [CFSG.Wreathed.ProjectiveTwoParameterUniqueness.card_stated_psl_two_of_odd
    G p f hmodel hpodd]
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  have hq2 : 25 ≤ (p ^ f) ^ 2 := by nlinarith
  have hqsub : 24 ≤ (p ^ f) ^ 2 - 1 := by omega
  calc 60 * 2 = 5 * 24 := by norm_num
    _ ≤ p ^ f * ((p ^ f) ^ 2 - 1) := Nat.mul_le_mul hq hqsub

theorem reduced_quotient24_excludes_rank_two {G : Type} [Group G] [Finite G]
    (t : G) (hGamma : Nat.card (Gamma t) = 24) :
    ∀ (J : Subgroup (Gamma t)) (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 ≤ p ^ f →
      ¬ CFSG.Assembly.LowTwoRank.StatedClassicalModel J .PSL 2 p f := by
  intro J p f _ hpodd _ hq hmodel
  have hlarge := stated_psl_two_card_at_least_sixty J p f hpodd hq hmodel
  have hsmall := J.card_le_card_group
  rw [hGamma] at hsmall
  omega

theorem small_degree_three_and_Mathieu_models_exclude_large_rank_two_local_layer
    (G : Type) [Group G] [Finite G]
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 3 1 ∨
      Nonempty (G ≃* CFSG.Assembly.LowTwoRank.StatedM11)) (t : G) (ht : orderOf t = 2) :
    Nat.card (C t) = 48 ∧ N t = ⊥ ∧ Nat.card (Gamma t) = 24 ∧
      ∀ (J : Subgroup (Gamma t)) (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 ≤ p ^ f →
        ¬ CFSG.Assembly.LowTwoRank.StatedClassicalModel J .PSL 2 p f := by
  have hcN : Nat.card (C t) = 48 ∧ N t = ⊥ := by
    rcases hmodel with hlinear | hMathieu
    · exact psl_three_three_involution_centralizer_card_and_core G hlinear t ht
    · exact stated_m11_involution_centralizer_card_and_core G hMathieu t ht
  have hGamma := card_intrinsic_gamma_of_centralizer48 t ht hcN.1 hcN.2
  exact ⟨hcN.1, hcN.2, hGamma, reduced_quotient24_excludes_rank_two t hGamma⟩

@[expose] def SmallerSimpleModel (A : Type) [Group A] : Prop :=
  (∃ l a : ℕ, l.Prime ∧ Odd l ∧ 1 ≤ a ∧ l ^ a % 4 = 3 ∧
    CFSG.Assembly.LowTwoRank.StatedClassicalModel A .PSL 3 l a) ∨
  (∃ l a : ℕ, l.Prime ∧ Odd l ∧ 1 ≤ a ∧ l ^ a % 4 = 1 ∧
    CFSG.Assembly.LowTwoRank.StatedClassicalModel A .PSU 3 l a) ∨
  Nonempty (A ≃* CFSG.Assembly.LowTwoRank.StatedM11)

@[expose] def SmallerSimpleRecognition (X : Type) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] [IsSimpleGroup A],
    (∃ a b : A, a * b ≠ b * a) → Nat.card A < Nat.card X →
    ∀ (k : ℕ), 4 ≤ k → ∀ (S : Sylow 2 A),
      Nonempty (SemidihedralGroup k ≃* S) → SmallerSimpleModel A

theorem smaller_model_exact_local_parameter
    (G : Type) [Group G] [Finite G]
    (hrecognition : SmallerSimpleModel G) (t : G) (ht : orderOf t = 2)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ tau : CFSG.Assembly.LowTwoRank.StatedLieTag,
      (tau = .PSL ∨ tau = .PSU) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel G tau 3 p f ∧
      (tau = .PSL → p ^ f % 4 = 3) ∧ (tau = .PSU → p ^ f % 4 = 1) := by
  rcases hrecognition with hlinear | hunitary | hMathieu
  · obtain ⟨l, a, hl, hlodd, ha, hcong, hmodel⟩ := hlinear
    have hsmall : l ^ a ≠ 3 := by
      intro hthree
      obtain ⟨hlthree, haone⟩ := Nat.prime_three.pow_eq_iff.mp hthree
      subst l a
      exact (small_degree_three_and_Mathieu_models_exclude_large_rank_two_local_layer
        G (Or.inl hmodel) t ht).2.2.2 _ p f hp hpodd hf hq hlocal
    have hlarge : 5 ≤ l ^ a := by
      have hthree := (CFSG.Semidihedral.Principal.three_le_and_odd_of_prime_pow
        hl hlodd ha).1
      omega
    obtain ⟨_, _, _, _, _, _, hparameter⟩ :=
      degree_three_model_reduced_centralizer_local_parameter G .PSL (Or.inl rfl)
        l a hl hlodd ha hlarge hmodel ⟨fun _ => hcong, fun h => by cases h⟩ t ht
    obtain ⟨_, hprime, hexponent⟩ := hparameter p f hp hpodd hf hlocal
    refine ⟨.PSL, Or.inl rfl, ?_, ?_, fun h => by cases h⟩
    · simpa only [hprime, hexponent] using hmodel
    · intro _
      simpa only [hprime, hexponent] using hcong
  · obtain ⟨l, a, hl, hlodd, ha, hcong, hmodel⟩ := hunitary
    have hlarge : 5 ≤ l ^ a := by
      have hthree := (CFSG.Semidihedral.Principal.three_le_and_odd_of_prime_pow
        hl hlodd ha).1
      omega
    obtain ⟨_, _, _, _, _, _, hparameter⟩ :=
      degree_three_model_reduced_centralizer_local_parameter G .PSU (Or.inr rfl)
        l a hl hlodd ha hlarge hmodel ⟨(by intro h; cases h), fun _ => hcong⟩ t ht
    obtain ⟨_, hprime, hexponent⟩ := hparameter p f hp hpodd hf hlocal
    refine ⟨.PSU, Or.inr rfl, ?_, (by intro h; cases h), ?_⟩
    · simpa only [hprime, hexponent] using hmodel
    · intro _
      simpa only [hprime, hexponent] using hcong
  · exact ((small_degree_three_and_Mathieu_models_exclude_large_rank_two_local_layer
      G (Or.inr hMathieu) t ht).2.2.2 _ p f hp hpodd hf hq hlocal).elim

theorem smaller_simple_recognition_produces_actual_model_valuation
    (X : Type)
    (hrecognition : SmallerSimpleRecognition X) (A : Type) [Group A] [Finite A]
    [IsSimpleGroup A] (hnonab : ∃ a b : A, a * b ≠ b * a)
    (hcard : Nat.card A < Nat.card X) (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 A)
    (fS : SemidihedralGroup n ≃* S) (t : A)
    (ht : t = (fS (r n) : A) ^ 2 ^ (n - 2))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ tau : CFSG.Assembly.LowTwoRank.StatedLieTag,
      (tau = .PSL ∨ tau = .PSU) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel A tau 3 p f ∧
      (tau = .PSL → p ^ f % 4 = 3) ∧ (tau = .PSU → p ^ f % 4 = 1) ∧
      3 * (padicValNat p (Nat.card (C t)) : ℤ) -
        2 * (padicValNat p (Nat.card
          (C t ⊓ C (fS (s n) : A) : Subgroup A)) : ℤ) ≤ padicValNat p (Nat.card A) := by
  have hmodels := hrecognition A hnonab hcard n hn S ⟨fS⟩
  obtain ⟨_, ht2, _, _, hs2, _⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  obtain ⟨tau, htau, hmodel, hlinear, hunitary⟩ :=
    smaller_model_exact_local_parameter A hmodels t ht2 p f hp hpodd hf hq hlocal
  have hval := CFSG.Semidihedral.Principal.degree_three_model_characteristic_valuation_regularity
    tau htau p f hp hpodd hf hmodel
  exact ⟨tau, htau, hmodel, hlinear, hunitary, hval.2.2.2 t (fS (s n) : A) ht2 hs2⟩

theorem smaller_simple_recognition_produces_actual_regularity_at_ideal
    (X : Type) (hrecognition : SmallerSimpleRecognition X) (G : Type) [Group G] [Fintype G]
    (hsize : Nat.card G < Nat.card X) (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* S) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    (padicValNat p (Nat.card G) : ℤ) =
      3 * (padicValNat p (Nat.card (C t)) : ℤ) -
        2 * (padicValNat p (Nat.card (C t ⊓ C (fS (s n) : G) : Subgroup G)) : ℤ) ∧
    (Nat.card G : ℚ) = (Nat.card (C t) : ℚ) ^ 3 /
      (Nat.card (C t ⊓ C (fS (s n) : G) : Subgroup G) : ℚ) ^ 2 *
        ((((p ^ f : ℕ) : ℚ) ^ 2 - (if p ^ f % 4 = 1 then 1 else -1) * p ^ f + 1) /
          (((p ^ f : ℕ) : ℚ) - (if p ^ f % 4 = 1 then 1 else -1)) ^ 2) := by
  classical
  let K := CFSG.pPrimeCore 2 G
  let barG := G ⧸ K
  let pi : G →* barG := QuotientGroup.mk' K
  obtain ⟨_, A, hAmin, _, hAsimple, hAnonab, _, hAodd, _, _, hAcard, _⟩ :=
    CFSG.Semidihedral.Local.semidihedral_odd_core_quotient_simple_odd_index_subgroup
      hG n hn S fS
  have : A.Normal := hAmin.1
  have : IsSimpleGroup A := hAsimple
  have hAindex : ∀ U : Subgroup A, U.index ≠ 2 :=
    CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hAnonab
  have hKodd : Odd (Nat.card K) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := G))
  obtain ⟨hbarindex, ⟨barS, _, _, fbar, hbarimages⟩, _, hbarLsimple, hbarnonab,
    hbarcentral, hbarnc, hbarmodel, hregiff, hregboth⟩ :=
    CFSG.Semidihedral.Local.actual_odd_kernel_preserves_local_parameter_and_regularity
      n hn hG S fS t ht K hKodd hnonab hcentral hnc p f hp hpodd hf hq hmodel ideal
  have : IsSimpleGroup (CFSG.generalizedFitting (Gamma (pi t))) := hbarLsimple
  obtain ⟨SA, fA, _, hAimages⟩ :=
    CFSG.Semidihedral.SameParameterQuotientTransport.normal_odd_index_sylow_presentation
      A hAodd n barS fbar
  let tA : A := (fA (r n) : A) ^ 2 ^ (n - 2)
  have htA : (tA : barG) = pi t := by
    change ((fA (r n) : A) : barG) ^ 2 ^ (n - 2) = pi t
    rw [hAimages, hbarimages, ← map_pow, ← ht]
  have hbarrelation : pi t = (fbar (r n) : barG) ^ 2 ^ (n - 2) := by
    rw [hbarimages, ← map_pow, ← ht]
  obtain ⟨_, hbart2, _, _, _, _⟩ :=
    CFSG.Semidihedral.Principal.supplied_t_s_facts hn fbar hbarrelation
  obtain ⟨_, htA2, hAcent, _, _, _⟩ :=
    CFSG.Semidihedral.Principal.supplied_t_s_facts hn fA (rfl : tA = _)
  have hsimpleA : IsSimpleGroup (CFSG.generalizedFitting (Gamma (tA : barG))) := by
    rw [htA]
    exact hbarLsimple
  have := hsimpleA
  have hnonabA : ∃ a b : CFSG.generalizedFitting (Gamma (tA : barG)), a * b ≠ b * a := by
    rw [htA]
    exact hbarnonab
  have hcentralA : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (tA : barG)) : Set (Gamma (tA : barG))) = ⊥ := by
    rw [htA]
    exact hbarcentral
  have hncA : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma (tA : barG))), ¬ IsCyclic U := by
    rw [htA]
    exact hbarnc
  have hmodelA : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma (tA : barG))) .PSL 2 p f := by
    rw [htA]
    exact hbarmodel
  obtain ⟨hLAsimple, hLAnonab, hLAcentral, hLAnc, hLAmodel, _, _⟩ :=
    normal_odd_index_subgroup_preserves_intrinsic_local_layer A hAodd hAindex n hn SA fA
      tA htA2 hnonabA hcentralA hncA p f hp hpodd hf hmodelA
  have : IsSimpleGroup (CFSG.generalizedFitting (Gamma tA)) := hLAsimple
  have hAsmaller : Nat.card A < Nat.card X := hAcard.trans_lt hsize
  obtain ⟨_, _, _, _, _, hAval⟩ :=
    smaller_simple_recognition_produces_actual_model_valuation X hrecognition A hAnonab
      hAsmaller n hn SA fA tA rfl p f hp hpodd hf hq hLAmodel
  obtain ⟨_, _, _, _, _, _, hbarval, _, _, _⟩ :=
    actual_same_parameter_regularity_and_odd_core_intersection A tA htA2 n n hn hn
      barS fbar SA fA hbarindex hAindex hAcent hnonabA hLAnonab hcentralA hLAcentral
        hncA hLAnc p f hp hpodd hf hq hmodelA hLAmodel ideal hAval
  have hsA : ((fA (s n) : A) : barG) = pi (fS (s n) : G) := by
    rw [hAimages, hbarimages]
  rw [htA, hsA] at hbarval
  have hbarreg :
      3 * (padicValNat p (Nat.card (C (pi t))) : ℤ) -
        2 * (padicValNat p (Nat.card
          (C (pi t) ⊓ C (pi (fS (s n) : G)) : Subgroup barG)) : ℤ) ≤
          padicValNat p (Nat.card barG) := le_of_eq hbarval.symm
  have hreg := hregiff.mpr hbarreg
  have hGval := (hregboth (Or.inr hbarreg)).1
  obtain ⟨_, ht2, hcent, _, _, _⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
      (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨F, _, _, _, hFcard, _, _, _, hrest⟩ :=
    CFSG.Semidihedral.Principal.actual_nonsimple_layer_characteristic_valuation_degree_formulas
      n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel ideal basis principal
        hprincipal localBasis localPrincipal hlocalPrincipal fS hcent hreg
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hvalues⟩ := hrest
  have horder := hvalues.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hGval, ?_⟩
  simpa only [hFcard, Int.cast_ite, Int.cast_one, Int.cast_neg, Nat.cast_pow] using horder

theorem smaller_simple_recognition_produces_proper_subgroup_regularity
    (X : Type) [Group X] [Finite X] (hrecognition : SmallerSimpleRecognition X)
    (H : Subgroup X) (hproper : H ≠ ⊤) (hH : ∀ U : Subgroup H, U.index ≠ 2)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (fS : SemidihedralGroup n ≃* S) (t : H)
    (ht : t = (fS (r n) : H) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (padicValNat p (Nat.card H) : ℤ) =
      3 * (padicValNat p (Nat.card (C t)) : ℤ) -
        2 * (padicValNat p (Nat.card (C t ⊓ C (fS (s n) : H) : Subgroup H)) : ℤ) ∧
    (Nat.card H : ℚ) = (Nat.card (C t) : ℚ) ^ 3 /
      (Nat.card (C t ⊓ C (fS (s n) : H) : Subgroup H) : ℚ) ^ 2 *
        ((((p ^ f : ℕ) : ℚ) ^ 2 - (if p ^ f % 4 = 1 then 1 else -1) * p ^ f + 1) /
          (((p ^ f : ℕ) : ℚ) - (if p ^ f % 4 = 1 then 1 else -1)) ^ 2) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  have hsize : Nat.card H < Nat.card X := by
    rw [← Subgroup.card_top (G := X)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hproper)
  obtain ⟨⟨ideal, hmax, htwo⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hchar ideal hmax htwo
  exact smaller_simple_recognition_produces_actual_regularity_at_ideal X hrecognition H hsize
    hH n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel ideal

end CFSG.Semidihedral.ProperSubgroupRegularity
