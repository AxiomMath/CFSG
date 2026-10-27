module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LIComponentSp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LIComponentSpFour
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LIComponentOrth
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LIComponentOrthFour
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LIComponentOrthMinus
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15NoXBlockBorelDone

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem hLI_of_component_li
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hLI : ∀ {U : Subgroup ↥Ls}, IsPGroup 2 U → IsSylowTwoOf U ⊤ →
      ∀ {x : ↥Ls}, Odd (orderOf x) →
        x ∈ Subgroup.centralizer (U : Set ↥Ls) → ∀ l : ↥Ls, x * l = l * x) :
    ∀ x ∈ Subgroup.centralizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) :
        Set (X ⧸ gnC T)) ⊓ Ls, Odd (orderOf x) → ∀ l ∈ Ls, x * l = l * x := by
  intro x hx hxodd l hl
  have hxLs : x ∈ Ls := hx.2
  have hxc : x ∈ Subgroup.centralizer
      ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) := hx.1
  have hS : IsSylowTwoOf (gnImg T T ⊓ Ls) Ls :=
    isSylowTwoOf_gnImg_inf hX.sylow hLs.2.1
  have hUmax : IsSylowTwoOf ((gnImg T T ⊓ Ls).subgroupOf Ls) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    · rw [show (((gnImg T T ⊓ Ls).subgroupOf Ls).subgroupOf (⊤ : Subgroup ↥Ls)).index
          = ((gnImg T T ⊓ Ls).subgroupOf Ls).index from Subgroup.relIndex_top_right _]
      exact hS.2.2
  have hU2 : IsPGroup 2 ((gnImg T T ⊓ Ls).subgroupOf Ls) := hUmax.2.1
  let x' : ↥Ls := ⟨x, hxLs⟩
  have hxodd' : Odd (orderOf x') := by
    rw [← Subgroup.orderOf_coe x']
    exact hxodd
  have hxc' : x' ∈ Subgroup.centralizer
      (((gnImg T T ⊓ Ls).subgroupOf Ls : Subgroup ↥Ls) : Set ↥Ls) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxc (u : X ⧸ gnC T)
      (Subgroup.mem_subgroupOf.mp hu)
  have hcent := hLI hU2 hUmax hxodd' hxc'
  simpa using congrArg Subtype.val (hcent ⟨l, hl⟩)

theorem noXBlock_borelPre_done_B
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (m : ℕ) (hm : 3 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.B m Q).Valid)
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.B m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hcard : 5 ≤ Q.card ∨ Q.card = 4)
    (Y : Subgroup X) (hY : Y ≤ borelPre T Ls)
    (hsub : CFSG.Open.IsSubnormal Y (borelPre T Ls))
    (hblock : CFSG.AGLEmbedding.InClassXBlock Y) : False := by
  classical
  haveI : Finite (X ⧸ gnC T) :=
    Finite.of_surjective (QuotientGroup.mk' (gnC T)) (QuotientGroup.mk'_surjective (gnC T))
  refine noXBlock_borelPre_done hX hLs hinv ?_ Y hY hsub hblock
  refine hLI_of_component_li hX hLs ?_
  intro U hU2 hUmax x hxodd hxc
  rcases hcard with h5 | h4
  · exact odd_centralizer_centralizes_of_component_sp_of_card_ge_five hLs.2.2 m hm Q hQ hv e hU2
      hUmax hxodd hxc h5
  · exact odd_centralizer_centralizes_of_component_sp_card_four hLs.2.2 m hm Q hQ h4 hv e hU2 hUmax
      hxodd hxc

theorem noXBlock_borelPre_done_D
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (m : ℕ) (hm : 4 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.D m Q).Valid)
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.D m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hcard : 5 ≤ Q.card ∨ Q.card = 4)
    (Y : Subgroup X) (hY : Y ≤ borelPre T Ls)
    (hsub : CFSG.Open.IsSubnormal Y (borelPre T Ls))
    (hblock : CFSG.AGLEmbedding.InClassXBlock Y) : False := by
  classical
  haveI : Finite (X ⧸ gnC T) :=
    Finite.of_surjective (QuotientGroup.mk' (gnC T)) (QuotientGroup.mk'_surjective (gnC T))
  refine noXBlock_borelPre_done hX hLs hinv ?_ Y hY hsub hblock
  refine hLI_of_component_li hX hLs ?_
  intro U hU2 hUmax x hxodd hxc
  rcases hcard with h5 | h4
  · exact odd_centralizer_centralizes_of_component_orth_of_card_ge_five hLs.2.2 m hm Q hQ hv e
      hU2 hUmax hxodd hxc h5
  · exact odd_centralizer_centralizes_of_component_orth_card_four hLs.2.2 m hm Q hQ h4 hv e
      hU2 hUmax hxodd hxc

theorem noXBlock_borelPre_done_2D
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (m : ℕ) (hm : 4 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.twistedD m Q).Valid)
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.twistedD m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hcard : 5 ≤ Q.card ∨ Q.card = 4)
    (Y : Subgroup X) (hY : Y ≤ borelPre T Ls)
    (hsub : CFSG.Open.IsSubnormal Y (borelPre T Ls))
    (hblock : CFSG.AGLEmbedding.InClassXBlock Y) : False := by
  classical
  haveI : Finite (X ⧸ gnC T) :=
    Finite.of_surjective (QuotientGroup.mk' (gnC T)) (QuotientGroup.mk'_surjective (gnC T))
  refine noXBlock_borelPre_done hX hLs hinv ?_ Y hY hsub hblock
  refine hLI_of_component_li hX hLs ?_
  intro U hU2 hUmax x hxodd hxc
  rcases hcard with h5 | h4
  · exact odd_centralizer_centralizes_of_component_orth_minus_of_card_ge_five hLs.2.2 m hm Q hQ
      hv e hU2 hUmax hxodd hxc h5
  · exact odd_centralizer_centralizes_of_component_orth_minus_card_four hLs.2.2 m hm Q hQ h4 hv e
      hU2 hUmax hxodd hxc

end CFSG.LocalAnalysis.RankThreeUC.S15

end
