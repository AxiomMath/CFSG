module

public import CFSG.ClassicalGroups.Orthogonal.CartanBorelProjective
public import CFSG.GroupTheory.SylowTwoEquiv
public import CFSG.Quasithin.Background.E3Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusCentrallyClosed
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open CFSG.QuasithinUnique
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

theorem exists_piSubgroup_three_le_pRank_in_borel_orth
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 4 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.D m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.D m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {q : ℕ} (hq : q.Prime) (hq2 : q != 2) (hdvd : q ∣ Q.card - 1) (hQcard : 4 ≤ Q.card)
    {U : Subgroup L} (hU2 : IsPGroup 2 U)
    (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∃ H : Subgroup L, H ≤ Subgroup.normalizer (U : Set L) ∧
      IsPiSubgroup {p : Nat.Primes | (p : Nat) != 2} H ∧
      3 ≤ CFSG.Open.pRank q H := by
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
  have hdvdF : q ∣ Nat.card F - 1 := by
    rw [hFcardpow, ← hQcardpow]
    exact hdvd
  obtain ⟨T, hTN, hTpi, hTrk⟩ :=
    exists_piSubgroup_three_le_pRank_in_borel_projective (m := m) (F := F) hm hq hq2 hdvdF
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
  let Tg : Subgroup E := T.map (MulAut.conj g).toMonoidHom
  have hTgN : Tg ≤ Subgroup.normalizer ((U.map eL.toMonoidHom : Subgroup E) : Set E) := by
    calc Tg ≤ (Subgroup.normalizer ((plusProjectiveUnipotent m F : Subgroup E) : Set E)).map
          (MulAut.conj g).toMonoidHom := Subgroup.map_mono hTN
      _ = Subgroup.normalizer (((plusProjectiveUnipotent m F).map
            (MulAut.conj g).toMonoidHom : Subgroup E) : Set E) :=
          Subgroup.map_equiv_normalizer_eq _ (MulAut.conj g)
      _ = Subgroup.normalizer ((U.map eL.toMonoidHom : Subgroup E) : Set E) := by
          rw [← hg]
  let H : Subgroup L := Tg.map eL.symm.toMonoidHom
  have hUU : (U.map eL.toMonoidHom).map eL.symm.toMonoidHom = U := by
    rw [Subgroup.map_map]
    have hcomp : eL.symm.toMonoidHom.comp eL.toMonoidHom = MonoidHom.id L := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  have hHN : H ≤ Subgroup.normalizer (U : Set L) := by
    calc H ≤ (Subgroup.normalizer ((U.map eL.toMonoidHom : Subgroup E) : Set E)).map
          eL.symm.toMonoidHom := Subgroup.map_mono hTgN
      _ = Subgroup.normalizer
            ((((U.map eL.toMonoidHom).map eL.symm.toMonoidHom : Subgroup L)) : Set L) :=
          Subgroup.map_equiv_normalizer_eq _ eL.symm
      _ = Subgroup.normalizer (U : Set L) := by rw [hUU]
  refine ⟨H, hHN, ?_, ?_⟩
  ·
    have hTgpi : IsPiSubgroup {p : Nat.Primes | (p : Nat) != 2} Tg :=
      CFSG.LocalCores.isPiSubgroup_map hTpi (MulAut.conj g).toMonoidHom
    exact CFSG.LocalCores.isPiSubgroup_map hTgpi eL.symm.toMonoidHom
  ·
    have hTgrk : CFSG.Open.pRank q Tg = CFSG.Open.pRank q T :=
      CFSG.Quasithin.E3.pRank_map_mulEquiv' (MulAut.conj g) hq T
    have hHrk : CFSG.Open.pRank q H = CFSG.Open.pRank q Tg :=
      CFSG.Quasithin.E3.pRank_map_mulEquiv' eL.symm hq Tg
    rw [hHrk, hTgrk]
    exact hTrk

end CFSG.LocalAnalysis.RankThreeUC.S15

end
