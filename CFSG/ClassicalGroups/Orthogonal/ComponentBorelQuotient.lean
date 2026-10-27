module

public import CFSG.ClassicalGroups.SpecialLinear.ComponentBorelQuotient
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2PlusSyl
public import CFSG.GroupTheory.SylowTwoEquiv
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusCentrallyClosed
public import CFSG.RankThree.PartOne.KF.ClsOmega

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open scoped commutatorElement

theorem isMulCommutative_plusProjectiveBorel_quotient {K : Type} [Field K] [Finite K]
    {k : ℕ} (hk : Nat.card K = 2 ^ k) (m : ℕ) (hm : 3 ≤ m) :
    IsMulCommutative (↥(plusProjectiveBorel m K) ⧸ CFSG.pCore 2 ↥(plusProjectiveBorel m K)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := k) (by simpa [Nat.card_eq_fintype_card] using hk)
  have hUle : plusProjectiveUnipotent m K ≤ plusProjectiveBorel m K := by
    rw [← plusProjectiveUnipotent_normalizer m K hm]
    exact Subgroup.le_normalizer
  have hUnorm : ((plusProjectiveUnipotent m K).subgroupOf (plusProjectiveBorel m K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUle).mpr (by
      rw [plusProjectiveUnipotent_normalizer m K hm])
  obtain ⟨S, hS⟩ := plusProjectiveUnipotent_isSylow (n := m) (K := K) 2 hm
  have hUP : IsPGroup 2 (plusProjectiveUnipotent m K) := hS ▸ S.isPGroup'
  have hUsubP : IsPGroup 2 ((plusProjectiveUnipotent m K).subgroupOf (plusProjectiveBorel m K)) :=
    hUP.comap_subtype
  have hUlePc : (plusProjectiveUnipotent m K).subgroupOf (plusProjectiveBorel m K) ≤
      CFSG.pCore 2 ↥(plusProjectiveBorel m K) := le_sSup ⟨hUnorm, hUsubP⟩
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
  change ⁅(⊤ : Subgroup ↥(plusProjectiveBorel m K)), ⊤⁆ ≤
    CFSG.pCore 2 ↥(plusProjectiveBorel m K)
  rw [Subgroup.commutator_le]
  intro x _ y _
  refine hUlePc (Subgroup.mem_subgroupOf.2 ?_)
  change (plusProjectiveBorel m K).subtype ⁅x, y⁆ ∈ plusProjectiveUnipotent m K
  have hcoe : (plusProjectiveBorel m K).subtype ⁅x, y⁆ =
      ⁅(plusProjectiveBorel m K).subtype x, (plusProjectiveBorel m K).subtype y⁆ :=
    map_commutatorElement (plusProjectiveBorel m K).subtype x y
  rw [hcoe]
  exact CFSG.AGLEmbedding.ParabAutIrr.plus_commutator_mem_unipotent m hm x.2 y.2

theorem isMulCommutative_normalizer_quotient_pCore_of_component_orth
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 4 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.D m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.D m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hQcard : 4 ≤ Q.card)
    {U : Subgroup L} (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    IsMulCommutative
      (↥(Subgroup.normalizer (U : Set L)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (U : Set L))) := by
  classical
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.D m Q, hv⟩
  let F := ↥(TauCeti.ValidLieTypeIndex.fixedField d)
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  haveI : Fintype F := Fintype.ofFinite F
  let D := (TauCeti.CFSGIndex.lie d).Group
  let E := StatedProj (StatedOmega (StatedQuadPlus m F))
  have hQcardpow : Q.card = 2 ^ Q.exponent := by
    rw [TauCeti.PrimePower.card_def, hQ]
  have hdchar : d.characteristic = 2 := by
    change TauCeti.LieTypeIndex.characteristic (TauCeti.LieTypeIndex.D m Q) = 2
    rw [TauCeti.LieTypeIndex.characteristic_D, hQ]
  have hdfexp : d.fieldExponent = Q.exponent := by
    change TauCeti.LieTypeIndex.fieldExponent (TauCeti.LieTypeIndex.D m Q) = Q.exponent
    rw [TauCeti.LieTypeIndex.fieldExponent_D]
  have hFcardpow : Nat.card F = 2 ^ Q.exponent := by
    change Nat.card ↥d.fixedField = 2 ^ Q.exponent
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, hdchar, hdfexp]
  haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := Q.exponent)
      (by simpa [Nat.card_eq_fintype_card] using hFcardpow)
  have hf : 2 ≤ Q.exponent := by
    have h4 : 2 ^ 2 ≤ 2 ^ Q.exponent := by
      rw [← hQcardpow]
      omega
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : 3 ≤ m := by omega
  have eD : D ≃* E :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid m Q hv
  let qmap : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  let ψ : L →* E := eD.toMonoidHom.comp (e.toMonoidHom.comp qmap)
  have hψ : Function.Surjective ψ :=
    eD.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : ψ.ker ≤ Subgroup.center L := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : e (qmap y) = 1 := eD.injective (by simpa [ψ] using hy)
    have h2 : qmap y = 1 := e.injective (by simpa using h1)
    exact (QuotientGroup.eq_one_iff y).mp h2
  have hbot : (StatedScalars (Fin m ⊕ Fin m) F).subgroupOf
      (StatedOmega (StatedQuadPlus m F)) = ⊥ :=
    CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot
      (K := F) (by omega)
  let eΩ : E ≃* StatedOmega (StatedQuadPlus m F) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  have hclose : Function.Injective ψ := by
    have hψ' : Function.Surjective (eΩ.toMonoidHom.comp ψ) := eΩ.surjective.comp hψ
    have hker' : (eΩ.toMonoidHom.comp ψ).ker ≤ Subgroup.center L := by
      intro y hy
      apply hker
      rw [MonoidHom.mem_ker] at hy ⊢
      exact eΩ.injective (by simpa using hy)
    have hker'' : ((CFSG.StandardType.rPlusEquivStatedOmega F m).symm.toMonoidHom.comp
        (eΩ.toMonoidHom.comp ψ)).ker ≤ Subgroup.center L := by
      intro y hy
      apply hker'
      rw [MonoidHom.mem_ker] at hy ⊢
      exact (CFSG.StandardType.rPlusEquivStatedOmega F m).symm.injective (by simpa using hy)
    have h := CFSG.StandardType.rPlus_injective_of_cover (K := F) hFcardpow hf hm3 L
      ((CFSG.StandardType.rPlusEquivStatedOmega F m).symm.toMonoidHom.comp
        (eΩ.toMonoidHom.comp ψ))
      ((CFSG.StandardType.rPlusEquivStatedOmega F m).symm.surjective.comp hψ')
      hker'' hL.1
    intro a b hab
    exact h (congrArg
      (fun z => (CFSG.StandardType.rPlusEquivStatedOmega F m).symm (eΩ z)) hab)
  have hqinj : Function.Injective qmap := by
    intro a b hab
    exact hclose (by simp [ψ, hab])
  let eL : L ≃* E :=
    (MulEquiv.ofBijective qmap ⟨hqinj, QuotientGroup.mk'_surjective _⟩).trans (e.trans eD)
  have hPsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (plusProjectiveUnipotent m F) ⊤ := by
    obtain ⟨P, hP⟩ := plusProjectiveUnipotent_isSylow m F 2 (by omega)
    rw [← hP]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hUsylE : CFSG.QuasithinUnique.IsSylowTwoOf
      (U.map eL.toMonoidHom) ⊤ := by
    have h := CFSG.QuasithinUnique.IsSylowTwoOf.map_mulEquiv eL hUmax
    rwa [Subgroup.map_top_of_surjective _ eL.surjective] at h
  obtain ⟨g, -, hg⟩ := hPsyl.exists_conj hUsylE
  have hN : Subgroup.normalizer ((U.map eL.toMonoidHom : Subgroup E) : Set E) =
      (plusProjectiveBorel m F).map (MulAut.conj g).toMonoidHom := by
    rw [hg, ← Subgroup.map_equiv_normalizer_eq (plusProjectiveUnipotent m F) (MulAut.conj g),
      plusProjectiveUnipotent_normalizer m F (by omega)]
  have hcommPB : IsMulCommutative
      (↥(plusProjectiveBorel m F) ⧸ CFSG.pCore 2 ↥(plusProjectiveBorel m F)) :=
    isMulCommutative_plusProjectiveBorel_quotient (K := F) (k := Q.exponent) hFcardpow m hm3
  have hcommConj : IsMulCommutative
      (↥((plusProjectiveBorel m F).map (MulAut.conj g).toMonoidHom) ⧸
        CFSG.pCore 2 ↥((plusProjectiveBorel m F).map (MulAut.conj g).toMonoidHom)) :=
    CFSG.ClassicalGroups.SpecialLinear.isMulCommutative_quotient_pCore_of_surjective
      (Subgroup.equivMapOfInjective (plusProjectiveBorel m F) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toMonoidHom
      (MulEquiv.surjective _) hcommPB
  have hcommNE : IsMulCommutative
      (↥(Subgroup.normalizer ((U.map eL.toMonoidHom : Subgroup E) : Set E)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer
          ((U.map eL.toMonoidHom : Subgroup E) : Set E))) := by
    rw [hN]
    exact hcommConj
  have hmap := Subgroup.map_equiv_normalizer_eq (U : Subgroup L) eL
  let eN : ↥(Subgroup.normalizer ((U.map eL.toMonoidHom : Subgroup E) : Set E)) ≃*
      ↥(Subgroup.normalizer (U : Set L)) :=
    (MulEquiv.subgroupCongr hmap.symm).trans
      (Subgroup.equivMapOfInjective (Subgroup.normalizer (U : Set L)) eL.toMonoidHom
        eL.injective).symm
  exact CFSG.ClassicalGroups.SpecialLinear.isMulCommutative_quotient_pCore_of_surjective
    eN.toMonoidHom eN.surjective hcommNE

end CFSG.ClassicalGroups.Orthogonal

end
