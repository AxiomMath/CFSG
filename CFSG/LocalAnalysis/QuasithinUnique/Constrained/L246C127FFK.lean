module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127KBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113
public import CFSG.Milestones.ASVolI.B1
public import CFSG.Quasithin.Background.C24PfE

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.SectionRank
open scoped commutatorElement

namespace L246C127

theorem Setting.b113_concl_K {G : Type} [Group G] [Finite G] {X T P K : Subgroup G}
    (S : Setting X T P K) (h113 : CFSG.ASVolI.B_1_13) (hKG : CFSG.SectionRank.IsKGroupCat ↥X)
    (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X) (hKJ : ⁅K, thompsonJ T⁆ = K)
    (hne : ⁅VZ T X, K⁆ ≠ ⊥) : Bridge.B113Concl (autI hV X) (autI hV K) := by
  have hst := S.isStableFF_offenderImages hV hKJ hne
  have hq := S.isQuasisimple_or_card_three_autI hV hUV
  have hsub := S.isSubnormal_autI_sup hV
  have hsq : ∀ v : IntMod (VZ T X) hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hSyl := B2F.isSylowTwoOf_autI hV S.hXV S.sylow
  have hKJ' := Bridge.commutator_ffJ_eq_of_stable B15P4.asB15Part4 hsq hSyl hst hq hsub
    (S.commutator_ffJP_eq hV hKJ)
  have hq' : CFSG.Open.IsQuasisimple ↥(autI hV K) ∨ Nat.card ↥(autI hV K) = 3 :=
    hq.imp B1Red.isQuasisimple_to_open id
  rcases h113 (IntMod (VZ T X) hV) hsq (autI hV X) (C24Pf.isKGroupCat_autI hV S.hXV hKG)
      (pCoreOf_autI_eq_bot hV S.hred) (autI hV T) (autI hV K) hSyl
      (autI_mono hV (S.KP.trans S.PX)) hq' hsub hKJ' with
    ⟨⟨e⟩, hF, hC⟩ | ⟨hcomp, -⟩ | ⟨L, hL, hKL, m, hm, hrest⟩
  · refine Or.inl ⟨?_, le_inf hF hC⟩
    rw [Nat.card_congr e.toEquiv]
    exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 3)
  · exact Or.inr (Or.inl hcomp)
  · refine Or.inr (Or.inr ⟨L, hL, hKL, m, hm, ?_⟩)
    rcases hrest with ⟨n, hn, hK⟩ | ⟨hK, hm7⟩
    · exact Or.inl ⟨n, hn, hK⟩
    · exact Or.inr ⟨Bridge.nonempty_sl3_of_isPSL hK, hm7⟩

end L246C127

end CFSG.QuasithinUnique

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.L246C127
open scoped commutatorElement

@[expose] def C127KBlockType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T P K : Subgroup G), CharTwo X → IsSylowTwoOf T X →
    CFSG.SectionRank.IsKGroupCat ↥X → P ∈ uFamHat X T → IsBlock2 P K → ⁅K, thompsonJ T⁆ = K →
    P = T ⊔ conjClosure K T → KBlockTypeOf K

structure C127FFKInput : Prop where
  b113 : CFSG.ASVolI.B_1_13
  blockType : C127KBlockType
  oddEven : AltEvenExcludedBig

theorem c127_of_ffK
    (hFF : C127FFKInput) {G : Type} [Group G] [Finite G] (X T P K : Subgroup G) (hX : CharTwo X)
    (hT : IsSylowTwoOf T X) (hKG : CFSG.SectionRank.IsKGroupCat ↥X) (hP : P ∈ uFamHat X T)
    (hK : IsBlock2 P K) (hKJ : ⁅K, thompsonJ T⁆ = K) (hPK : P = T ⊔ conjClosure K T) :
    ∃ L : Subgroup G, IsBlock2 X L ∧ K ≤ L ∧ blockU K ≤ blockU L ∧ blockU L ≤ VZ T X ∧
      (K = L ∨ ∃ m n : ℕ, Odd m ∧ Odd n ∧ 3 ≤ m ∧ 3 ≤ n ∧
        IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m ∧
        IsAltQuotient K (Subgroup.centralizer (VZ T X : Set G)) n) := by
  have htype := hFF.blockType G X T P K hX hT hKG hP hK hKJ hPK
  have S : Setting X T P K := ⟨hX, hT, hP.1.1, hP.1.2.1.le, hK⟩
  have hKZ := S.not_le_centralizer_omega_of_blockType htype hKJ
  have hUV := S.blockU_le_VZ hKZ
  have hV : IsElemAbelian 2 (VZ T X) := S.hred.2.2.1
  have hne := Setting.commutator_VZ_ne_bot (X := X) hKZ
  exact S.exists_block_of_concl_K altEvenExcluded hFF.oddEven hV hUV htype
    (S.b113_concl_K hFF.b113 hKG hV hUV hKJ hne)

theorem theoremC127_of_ffK
    (hFF : C127FFKInput) : TheoremC127 :=
  fun G _ _ X T P K hX hT hKG hP hK hKJ hPK => c127_of_ffK hFF X T P K hX hT hKG hP hK hKJ hPK

end CFSG.Quasithin
