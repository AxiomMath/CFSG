module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8D4Adj
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8D4Orbit
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8D4Desc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8ClsOm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.LieType.SeitzGeneration
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadPlus StatedLieAdmissible
  StatedLieTag StatedClassicalModel)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem d4_inner_part {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    (hg : OrthogonalGates (coordinateQuadPlus 4 K) 3)
    (hconjinj : Function.Injective (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))))
    (AP : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))))
    (hAab : IsElemAbelian 3 AP) (hcard : Nat.card AP = 3 ^ 4) (h4 : CFSG.Open.pRank 3 AP ≤ 4)
    (hout : ∀ a ∈ AP, a ∉ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
        MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))).range →
      ∀ E : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)), E ≤ fixSubgroup a →
        IsElemAbelian 3 E → CFSG.Open.pRank 3 E + 1 ≤ CFSG.Open.pRank 3 AP) :
    ∃ Eb : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)), IsElemAbelian 3 Eb ∧
      3 ^ 3 ≤ Nat.card Eb ∧ ∀ c ∈ AP, ∀ x ∈ Eb, c x = x := by
  classical
  obtain ⟨A₀, hA₀le, hA₀card, hA₀E⟩ := exists_index_three_family (coordinateQuadPlus 4 K) hg AP
  have hA₀inner : ∀ a ∈ A₀, a ∈ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))).range := by
    intro a ha
    by_contra hnin
    have haA := hA₀le ha
    have ha3 : a ^ 3 = 1 := hAab.2 a haA
    have ha1 : a ≠ 1 := fun h => hnin (h ▸ one_mem _)
    have hao : IsOuterOfOrder 3 a :=
      ⟨orderOf_eq_prime ha3 ha1, fun g hg' => hnin ⟨g, hg'.symm⟩⟩
    obtain ⟨k, ι, hk, hιinj, hιfix, -⟩ := exists_descent_om_plus_of_mem (n := 4) (ℓ := 2) (f := 3)
      le_rfl Nat.prime_two (by norm_num) (by norm_num) hK hao (hA₀E ha)
    have hk2 : Nat.card k = 2 := by simpa using hk
    obtain ⟨E₀, hE₀, hcard₀⟩ := bigElem_matrixProj_plus_four hk2
    have hEfix : E₀.map ι ≤ fixSubgroup a := by
      rintro _ ⟨v, -, rfl⟩
      exact mem_fixSubgroup.2 (hιfix v)
    have hEab : IsElemAbelian 3 (E₀.map ι) := isElemAbelian_map_gen ι hE₀
    have h1 := hout a haA hnin _ hEfix hEab
    have h2 : 4 ≤ CFSG.Open.pRank 3 (E₀.map ι) := by
      apply four_le_pRank_of_card hEab
      rw [Subgroup.card_map_of_injective hιinj]
      exact hcard₀
    omega
  let Eb : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    A₀.comap (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
  have hEbmap : Eb.map (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) = A₀ := by
    have h1 := Subgroup.map_comap_eq (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K)
      →* MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) A₀
    rw [h1]
    exact inf_of_le_right (fun a ha => hA₀inner a ha)
  have hEbcard : Nat.card Eb = Nat.card A₀ := by
    have h1 := Subgroup.card_map_of_injective (K := Eb) hconjinj
    rw [hEbmap] at h1
    exact h1.symm
  have hEbab : IsElemAbelian 3 Eb :=
    om_isElemAbelian_of_map_injective _ hconjinj (by
      rw [hEbmap]
      exact om_isElemAbelian_of_le hA₀le hAab)
  refine ⟨Eb, hEbab, ?_, ?_⟩
  · rw [hEbcard]
    have : 3 ^ 4 ≤ 3 * Nat.card A₀ := by rw [← hcard]; exact hA₀card
    omega
  · intro c hc x hx
    have hcomm : Commute c (MulAut.conj x) := kd264F8_commute hAab hc (hA₀le hx)
    have h1 : MulAut.conj (c x) = MulAut.conj x := by
      rw [← mulAut_conj_conj, hcomm.eq]
      group
    exact hconjinj h1

theorem d4_adjoint_part {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    (hconjinj : Function.Injective (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))))
    (AP : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))))
    (hAab : IsElemAbelian 3 AP) (h4 : CFSG.Open.pRank 3 AP ≤ 4)
    (hout : ∀ a ∈ AP, a ∉ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
        MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))).range →
      ∀ E : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)), E ≤ fixSubgroup a →
        IsElemAbelian 3 E → CFSG.Open.pRank 3 E + 1 ≤ CFSG.Open.pRank 3 AP)
    (Eb : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) (hEbab : IsElemAbelian 3 Eb)
    (hEb27 : 3 ^ 3 ≤ Nat.card Eb) (hEbfix : ∀ c ∈ AP, ∀ x ∈ Eb, c x = x)
    (bP : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) (hbPA : bP ∈ AP)
    (hbPout : bP ∉ innAutDerived (matrixProjectiveDerived (coordinateQuadPlus 4 K))) : False := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hbP3 : bP ^ 3 = 1 := hAab.2 bP hbPA
  have hbPnin : bP ∉ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))).range := fun h =>
    hbPout (inner_le_innAutDerived _ h)
  obtain ⟨bridge⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup (F := K)
  let Φ : matrixProjectiveDerived (coordinateQuadPlus 4 K) ≃* adjointGroup Tag.D4 K :=
    (coordinatePlusWitnessEquiv K (MulEquiv.refl _)).symm.trans bridge
  let bC : MulAut (adjointGroup Tag.D4 K) := MulAut.congr Φ bP
  have hbC3 : bC ^ 3 = 1 := by
    show (MulAut.congr Φ bP) ^ 3 = 1
    rw [← map_pow, hbP3, map_one]
  have hbCout : bC ∉ innAutDerived (adjointGroup Tag.D4 K) := by
    intro h
    exact hbPout ((mem_innAutDerived_congr Φ).1 h)
  rcases d4_outer_dichotomy hK hbC3 hbCout with ⟨E, hEfixC, hEab, hEcard⟩ | hmodel
  ·
    have hfixP : E.map (Φ.symm : adjointGroup Tag.D4 K →* matrixProjectiveDerived
        (coordinateQuadPlus 4 K)) ≤ fixSubgroup bP := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : bC y = y := mem_fixSubgroup.1 (hEfixC hy)
      rw [mem_fixSubgroup]
      show bP (Φ.symm y) = Φ.symm y
      have h1 : Φ (bP (Φ.symm y)) = y := by
        have : bC y = Φ (bP (Φ.symm y)) := rfl
        rw [← this, hy']
      apply Φ.injective
      rw [h1, MulEquiv.apply_symm_apply]
    have hEabP : IsElemAbelian 3 (E.map (Φ.symm : adjointGroup Tag.D4 K →*
        matrixProjectiveDerived (coordinateQuadPlus 4 K))) := isElemAbelian_map_gen _ hEab
    have h1 := hout bP hbPA hbPnin _ hfixP hEabP
    have h2 : 4 ≤ CFSG.Open.pRank 3 (E.map (Φ.symm : adjointGroup Tag.D4 K →*
        matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
      apply four_le_pRank_of_card hEabP
      rw [Subgroup.card_map_of_injective Φ.symm.injective]
      exact hEcard
    omega
  ·
    let EC : Subgroup (adjointGroup Tag.D4 K) :=
      Eb.map (Φ : matrixProjectiveDerived (coordinateQuadPlus 4 K) →* adjointGroup Tag.D4 K)
    have hECfix : EC ≤ fixSubgroup bC := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_fixSubgroup]
      show Φ (bP (Φ.symm (Φ x))) = Φ x
      rw [MulEquiv.symm_apply_apply, hEbfix bP hbPA x hx]
    have hECab : IsElemAbelian 3 EC := isElemAbelian_map_gen _ hEbab
    have hECcard : 3 ^ 3 ≤ Nat.card EC := by
      rw [Subgroup.card_map_of_injective Φ.injective]
      exact hEb27
    obtain ⟨j, hj⟩ := X1Sp.Gen.card_eq_three_pow' hECab
    have hj3 : 3 ≤ j := by
      rw [hj] at hECcard
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hECcard
    haveI : Finite ↥EC := inferInstance
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥EC) 3
      (n := 3) (by rw [hj]; exact pow_dvd_pow 3 hj3)
    let E27 : Subgroup (adjointGroup Tag.D4 K) := H.map EC.subtype
    have hE27le : E27 ≤ fixSubgroup bC := fun x hx => by
      obtain ⟨y, -, rfl⟩ := hx
      exact hECfix y.2
    have hE27card : Nat.card E27 = 27 := by
      rw [Subgroup.card_map_of_injective EC.subtype_injective, hH]
      norm_num
    have hE27ab : IsElemAbelian 3 E27 := om_isElemAbelian_of_le
      (show E27 ≤ EC from fun x hx => by obtain ⟨y, -, rfl⟩ := hx; exact y.2) hECab
    let Ef : Subgroup ↥(fixSubgroup bC) := E27.subgroupOf (fixSubgroup bC)
    haveI : Finite ↥(fixSubgroup bC) := inferInstance
    refine CFSG.GF2Type.Smith1980Orth.not_lieModel_trialityD4_of_elementary Ef ?_ ?_ ?_ hmodel
    · intro x hx y hy
      have := hE27ab.1.is_comm.comm (⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩ : E27)
        ⟨y.1, Subgroup.mem_subgroupOf.1 hy⟩
      exact Subtype.ext (congrArg (Subtype.val : E27 → adjointGroup Tag.D4 K) this)
    · intro x hx
      apply Subtype.ext
      exact hE27ab.2 x.1 (Subgroup.mem_subgroupOf.1 hx)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE27le).toEquiv]
      exact hE27card

theorem d4_glue {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    (hg : OrthogonalGates (coordinateQuadPlus 4 K) 3)
    (hconjinj : Function.Injective (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))))
    (AP : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))))
    (hAab : IsElemAbelian 3 AP) (hcard : Nat.card AP = 3 ^ 4) (h4 : CFSG.Open.pRank 3 AP ≤ 4)
    (hout : ∀ a ∈ AP, a ∉ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
        MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))).range →
      ∀ E : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)), E ≤ fixSubgroup a →
        IsElemAbelian 3 E → CFSG.Open.pRank 3 E + 1 ≤ CFSG.Open.pRank 3 AP)
    (bP : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) (hbPA : bP ∈ AP)
    (hbPout : bP ∉ innAutDerived (matrixProjectiveDerived (coordinateQuadPlus 4 K))) : False := by
  obtain ⟨Eb, hEbab, hEb27, hEbfix⟩ := d4_inner_part hK hg hconjinj AP hAab hcard h4 hout
  exact d4_adjoint_part hK hconjinj AP hAab h4 hout Eb hEbab hEb27 hEbfix bP hbPA hbPout

theorem clsD4_model {S : Type} [Group S] [Finite S] (hM : StatedClassicalModel S .POmegaPlus 4 2 3)
    (A : Subgroup (MulAut S)) (hA : KD264F8Hyp S A) : False := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAab : IsElemAbelian 3 A := hA.1
  have h4 : CFSG.Open.pRank 3 A ≤ 4 := hA.2.2.1
  have hm3 : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ CFSG.Open.pRank 3 A := hA.2.2.2.1
  have hnot : ¬ A ≤ innAutDerived S := hA.2.2.2.2.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hM
  have hchar : ringChar K = 2 := ringChar_eq_of_card_eq_pow Nat.prime_two (by norm_num) hK
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  obtain ⟨hAab', hout', -⟩ := F8Trans.hyp_transport (coordinatePlusWitnessEquiv K e) A hA
  have hpAP := pRank_map_mulEquiv (p := 3) (MulAut.congr (coordinatePlusWitnessEquiv K e)) A
  have hM' : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K))) .POmegaPlus 4 2 3 :=
    ⟨⟨Nat.prime_two, by norm_num, le_rfl⟩, K, inferInstance, inferInstance, hK,
      ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadPlus 4 K) 3 :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus (Or.inr (Or.inl rfl))
      4 2 3 hM' K hK (MulEquiv.refl _)
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus hM K hK e
  have hcen := center_matrix_eq_bot (by norm_num : 0 < 2 * 4) hnd hT
  have hconjinj := conj_injective' hcen
  have hrank4 : 4 ≤ CFSG.Open.pRank 3 A := by
    let k : Subfield K := ⊥
    have hk2 : Nat.card k = 2 := Subfield.card_bot K 2
    obtain ⟨E₀, hE₀, hcard₀⟩ := bigElem_matrixProj_plus_four hk2
    have hinj := incl_injective k (coordinateQuadPlus_isExtension k 4) (by norm_num : 0 < 2 * 4)
    have hEab : IsElemAbelian 3 (E₀.map (incl k (coordinateQuadPlus_isExtension k 4))) :=
      isElemAbelian_map_gen _ hE₀
    have h1 : 4 ≤ CFSG.Open.pRank 3
        (⊤ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
      obtain ⟨j, hj⟩ := X1Sp.Gen.card_eq_three_pow' hEab
      have hcard : 3 ^ 4 ≤ 3 ^ j := by
        rw [← hj, Subgroup.card_map_of_injective hinj]
        exact hcard₀
      have hj4 : 4 ≤ j := (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
      exact le_trans hj4 (X1Sp.Gen.le_pRank_of_card le_top hEab hj)
    have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (coordinatePlusWitnessEquiv K e)
    omega
  have hpA : CFSG.Open.pRank 3 A = 4 := le_antisymm h4 hrank4
  have hcardA : Nat.card A = 3 ^ 4 := by
    rw [card_eq_pow_pRank hAab, hpA]
  have hcardAP := Subgroup.card_map_of_injective (K := A)
    (f := (MulAut.congr (coordinatePlusWitnessEquiv K e)).toMonoidHom)
    (MulAut.congr (coordinatePlusWitnessEquiv K e)).injective
  rw [hcardA] at hcardAP
  obtain ⟨b, hbA, hbout⟩ := SetLike.not_le_iff_exists.1 hnot
  exact d4_glue hK hg hconjinj _ hAab' hcardAP (hpAP ▸ h4) hout' _
    (Subgroup.mem_map_of_mem _ hbA)
    (fun h => hbout ((mem_innAutDerived_congr (coordinatePlusWitnessEquiv K e)).1 h))

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


theorem KD264F8ClsD4_holds : KD264F8ClsD4 := by
  intro d _hfin _hns _hk2 _hk3 hov hP _ _ _ A hA
  obtain ⟨d1, hd1⟩ := d
  obtain ⟨q, rfl⟩ := hP
  have hq : q.card = 8 := hov
  have hp2 := primePower_p_eq_two_of_card_eight q hq
  have hexp : q.exponent = 3 := by
    have h8 : q.card = 2 ^ 3 := by rw [hq]; norm_num
    rw [TauCeti.PrimePower.card_def, hp2] at h8
    exact Nat.pow_right_injective (le_refl 2) h8
  have hm := CFSG.Models.lieModel_D
    (G := (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D 4 q, hd1⟩).Group) 4 q hd1
    (MulEquiv.refl _)
  obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := hm
  · rw [hp2, hexp] at hSC
    exact (F8Om.clsD4_model hSC A hA).elim
  · omega

theorem KD264F8ClsOrthPlus_holds : KD264F8ClsOrthPlus :=
  KD264F8ClsOrthPlus_of_D4 KD264F8ClsD4_holds

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
