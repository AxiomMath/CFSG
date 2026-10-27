module

public import CFSG.GroupTheory.SylowTwoEquiv
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
public import CFSG.RankThree.PartOne.KF.ClsOmega
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusCentrallyClosed

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

theorem isSolvable_posBorel {K : Type} [Field K] [Finite K] (r : ℕ) :
    Group.IsSolvable ↥(posBorel r K) := by
  haveI : Fintype K := Fintype.ofFinite K
  let p := ringChar K
  haveI : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  haveI : CharP K p := ringChar.charP K
  have hmain :=
    (orthogonal_geometry_split_positive_unipotent_matrices (r := r) (K := K)).2.2.2.2.2.2.2.2.2.2
      p ‹CharP K p› ‹Finite K›
  haveI hfin : Finite ↥(posBorel r K) :=
    Finite.of_injective
      (fun g : ↥(posBorel r K) =>
        (fun x : Fin r ⊕ Fin r → K =>
          (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) x))
      (fun a b h => Subtype.ext (LinearEquiv.ext (congrFun h)))
  haveI : Group.IsSolvable ↥((posUnip r K).subgroupOf (posBorel r K)) := by
    have hP : IsPGroup p ((posUnip r K).subgroupOf (posBorel r K)) :=
      hmain.2.1.of_equiv
        (Subgroup.subgroupOfEquivOfLe (posUnip_le_posBorel (r := r) (K := K))).symm
    haveI := IsPGroup.isNilpotent hP
    infer_instance
  haveI : Group.IsSolvable (Fin r → Kˣ) := Group.isSolvable_of_comm fun a b => mul_comm a b
  refine Group.isSolvable_of_ker_le_range
    ((posUnip r K).subgroupOf (posBorel r K)).subtype (posBorelDiag r K) ?_
  rw [posBorelDiag_ker, Subgroup.range_subtype]

theorem isSolvable_flagStab {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 3 ≤ r) :
    Group.IsSolvable ↥(flagStab r K) := by
  haveI : Group.IsSolvable ↥(posBorel r K) := isSolvable_posBorel r
  have hXX : ∀ a ∈ orthElementaryGroup (quadPlus r K),
      (flag r K r).map (a : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) ≠
        Xstar r K (by omega) := fun a ha => map_flag_top_ne_Xstar (K := K) hr ha
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (flagStab_le_posBorel (by omega) hXX))

theorem isSolvable_statedDerivedFlagStabilizer_plus {K : Type} [Field K] [Finite K] {k : ℕ}
    (hk : Nat.card K = 2 ^ k) (m : ℕ) (hm : 3 ≤ m) :
    Group.IsSolvable ↥(statedDerivedFlagStabilizer (StatedQuadPlus m K) (stdFlag m K)) := by
  haveI : Group.IsSolvable ↥(flagStab m K) := isSolvable_flagStab hm
  change Group.IsSolvable ↥(plusDerivedBorel m K)
  haveI hsub : Group.IsSolvable
      ↥((flagStab m K).subgroupOf (orthElementaryGroup (quadPlus m K))) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (flagStab_le (r := m) (K := K))).toMonoidHom)
      (MulEquiv.injective _)
  haveI himg : Group.IsSolvable
      ↥((plusDerivedBorel m K).map (plusDerivedEquiv m K hm).toMonoidHom) := by
    rw [plusDerivedBorel_map m K hm]
    exact hsub
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective (plusDerivedBorel m K)
      (plusDerivedEquiv m K hm).toMonoidHom (plusDerivedEquiv m K hm).injective).toMonoidHom)
    (MulEquiv.injective _)

theorem isSolvable_plusProjectiveBorel {K : Type} [Field K] [Finite K] {k : ℕ}
    (hk : Nat.card K = 2 ^ k) (m : ℕ) (hm : 3 ≤ m) :
    Group.IsSolvable ↥(plusProjectiveBorel m K) := by
  haveI hB : Group.IsSolvable ↥(plusDerivedBorel m K) :=
    isSolvable_statedDerivedFlagStabilizer_plus hk m hm
  let q : StatedOmega (StatedQuadPlus m K) →*
      StatedProj (StatedOmega (StatedQuadPlus m K)) :=
    QuotientGroup.mk' ((StatedScalars (Fin m ⊕ Fin m) K).subgroupOf
      (StatedOmega (StatedQuadPlus m K)))
  let f : ↥(plusDerivedBorel m K) →* ↥(plusProjectiveBorel m K) :=
    MonoidHom.codRestrict (q.comp (plusDerivedBorel m K).subtype) (plusProjectiveBorel m K)
      (fun x => by
        rw [← plusDerivedBorel_project m K]
        exact Subgroup.mem_map_of_mem q x.2)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : StatedProj (StatedOmega (StatedQuadPlus m K))) ∈
        (plusDerivedBorel m K).map q := by
      rw [plusDerivedBorel_project m K]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact Group.isSolvable_of_surjective hf

theorem isSolvable_normalizer_sylow_of_component_orth
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 4 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.D m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.D m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hQcard : 4 ≤ Q.card)
    {U : Subgroup L} (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    Group.IsSolvable ↥(Subgroup.normalizer (U : Set L)) := by
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
  haveI hPB : Group.IsSolvable ↥(plusProjectiveBorel m F) :=
    isSolvable_plusProjectiveBorel hFcardpow m (by omega)
  haveI hNE : Group.IsSolvable
      ↥(Subgroup.normalizer ((U.map eL.toMonoidHom : Subgroup E) : Set E)) := by
    rw [hN]
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective (plusProjectiveBorel m F)
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toMonoidHom)
      (MulEquiv.surjective _)
  have hmap := Subgroup.map_equiv_normalizer_eq (U : Subgroup L) eL
  haveI : Group.IsSolvable ↥((Subgroup.normalizer (U : Set L)).map eL.toMonoidHom) :=
    hmap.symm ▸ hNE
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective (Subgroup.normalizer (U : Set L))
      eL.toMonoidHom eL.injective).toMonoidHom)
    (MulEquiv.injective _)

end CFSG.ClassicalGroups.Orthogonal
