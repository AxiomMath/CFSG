module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank621Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Reduce
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank621Faith
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank621KSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank621Sylow
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] [Finite G] {M B H S K : Subgroup G} {z b : G} {f : ↥K →* GL32}

local notation "W₃" => Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

theorem Data620.false_of_campbellFails (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD2 : TheoremD2 G) (hK : KFactLemma2813) {P : Sylow 3 G}
    (hsit : SmallRankSituation G 3 P M) (hsolv : Group.IsSolvable M)
    (e : (P : Subgroup G) ≃* W₃) {x : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z)
    (hB : B = zpowers x ⊔ zpowers z) (h : Data620 M B H S K z b f) (hSM : S ≤ M)
    {R : Subgroup G} (hSR : S ≤ R) (hRX : R ≤ K ⊔ pCoreOf 2 H) (hR2 : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ (R.subgroupOf (K ⊔ pCoreOf 2 H)).index)
    (hfail : ¬ ((K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter R : Subgroup G) : Set G) ≤
      normalizer (S : Set G))) : False := by
  subst hB
  have hSB : IsTwoInvariantIn (zpowers x ⊔ zpowers z) M S :=
    ⟨hSM, h.maxInv.1.2.1, h.maxInv.1.2.2⟩
  obtain ⟨T, Y, hST, hT2, hY3, hYM, hY81, hzY, hzc, hYT, hcen⟩ :=
    exists_two_group_sylow_three_normalizing hS hsit hsolv e hx hz hSB
  obtain ⟨hV16, hVX⟩ := h.k2813_conclusion hK hSR hRX hR2 hRi hfail
  have hz3 : z ^ 3 = 1 := by rw [← h.z_order]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h1 => by
    have := h.z_order
    rw [h1, orderOf_one] at this
    omega
  have hC : T ⊓ centralizer (S : Set G) ≤ S := by
    intro t ht
    obtain ⟨htT, htC⟩ := Subgroup.mem_inf.1 ht
    have htO : t ∈ centralizer (pCoreOf 2 H : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at htC ⊢
      exact fun o ho => htC o (h.core_le ho)
    have htH : t ∈ H := h.eq_normalizer.ge (Subgroup.centralizer_le_normalizer _ htO)
    exact h.core_le (h.charTwo H h.twoLocal ⟨htH, htO⟩)
  have hTV : omegaCenter T ≤ omegaCenter S := omegaCenter_le_omegaCenter hST hC
  have hcom : ∀ t ∈ omegaCenter T, z * t = t * z :=
    commutes_of_card_commutator_le hY3 (by omega) hzY hz1 hz3 hzc hcen
      (isElemAbelian_omegaCenter T) (hYT.trans (normalizer_le_normalizer_omegaCenter T)) hTV hV16
  have hKc : K ≤ normalizer ((omegaCenter T : Subgroup G) : Set G) := by
    refine le_trans ?_
      (Subgroup.centralizer_le_normalizer (s := ((omegaCenter T : Subgroup G) : Set G)))
    intro k hk
    rw [mem_centralizer_iff]
    intro t ht
    exact hVX t (hTV ht) (hcom t ht).symm k (mem_sup_left hk)
  have hT1 : omegaCenter T ≠ ⊥ :=
    omegaCenter_ne_bot hT2 (fun h0 => h.S_ne_bot (le_bot_iff.mp (h0 ▸ hST)))
  have hN : IsTwoLocal (normalizer ((omegaCenter T : Subgroup G) : Set G)) :=
    ⟨omegaCenter T, hT1, hT2.to_le (omegaCenter_le T), rfl⟩
  have hNM := le_of_twentySeven_le_card hS hU0 hD2 hsit hsolv e hN
    (hYT.trans (normalizer_le_normalizer_omegaCenter T)) hYM hY3 (by omega)
  exact h.K_not_le (hKc.trans hNM)

end CFSG.LocalAnalysis.RankThreeTheoremC
