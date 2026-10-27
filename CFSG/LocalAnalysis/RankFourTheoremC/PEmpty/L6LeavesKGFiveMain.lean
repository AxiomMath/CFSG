module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGFiveBlock
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGMain

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup

namespace KGFive

variable {G : Type} [Group G] [Finite G] {p : ℕ} {H D S B L M : Subgroup G} {z : G}

theorem pre_img_eq [(D.subgroupOf H).Normal] {U : Subgroup G} (hDU : D ≤ U) (hUH : U ≤ H) :
    KGC.pre H D (KGC.img H D U) = U := by
  ext g
  rw [KGC.mem_pre_img hDU]
  exact ⟨fun h => h.1, fun h => ⟨h, hUH h⟩⟩

theorem relIndex_sup_eq {L S : Subgroup G} (hS : S ≤ normalizer (L : Set G)) :
    S.relIndex (L ⊔ S) = S.relIndex L := by
  set X : Subgroup G := L ⊔ S with hX
  have hLX : L ≤ X := le_sup_left
  have hSX : S ≤ X := le_sup_right
  have hN : (L.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr (sup_le Subgroup.le_normalizer hS)
  have h1 := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (L.subgroupOf X)
    (S.subgroupOf X)
  rw [← Subgroup.subgroupOf_sup hLX hSX, ← hX, Subgroup.subgroupOf_self,
    Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hLX] at h1
  exact h1

theorem isSylowOf_sup (d : KGC.KGData p H D S B L M z) [hDn : (D.subgroupOf H).Normal]
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (KGC.img H D S ⊓ KGC.img H D L) (KGC.img H D L)) :
    CFSG.ABGLocalTools.IsSylowOf 2 S (L ⊔ S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hsyl ⊢
  obtain ⟨-, -, hodd⟩ := hsyl
  refine ⟨le_sup_right, d.S_two, ?_⟩
  have h1 : S.relIndex (L ⊔ S) = S.relIndex L := relIndex_sup_eq (S_le_normalizer d)
  have h2 : S.relIndex L = (KGC.img H D S).relIndex (KGC.img H D L) := by
    have := KGC.relIndex_pre (H := H) (D := D) (N := KGC.img H D S) (Y := KGC.img H D L)
    rwa [pre_img_eq d.D_lt_S.le d.S_le_H, pre_img_eq d.L_sec.1 d.L_le_H] at this
  rw [h1, h2, ← Subgroup.inf_relIndex_right]
  exact hodd

theorem false_of_sylow (h282 : KFact282) (d3 : KGC.KGData3 p H D S B L M z)
    [hDn : (D.subgroupOf H).Normal]
    (hc : KGStep4Concl (KGC.QA H D) (KGC.img H D L) (KGC.img H D S))
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (KGC.img H D S ⊓ KGC.img H D L) (KGC.img H D L))
    (hB : ¬ fusionIsBenderGroup ↥(KGC.img H D L)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have d : KGC.KGData p H D S B L M z := d3.toData
  have hXH : L ⊔ S ≤ H := sup_le d.L_le_H d.S_le_H
  have hLX : L ≤ L ⊔ S := le_sup_left
  have hDX : D ≤ L ⊔ S := d.D_lt_S.le.trans le_sup_right
  have hK : CFSG.Open.IsKGroup ↥(L ⊔ S) :=
    CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp (d3.catalog _ hXH)
  have hDXn : (D.subgroupOf (L ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDX).mpr (hXH.trans d.H_le_D)
  have hDle : D ≤ CFSG.Open.pCoreOf 2 (L ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hDX hDXn d.D_two
  have hF : (L ⊔ S) ⊓ centralizer (CFSG.Open.pCoreOf 2 (L ⊔ S) : Set G) ≤
      CFSG.Open.pCoreOf 2 (L ⊔ S) := by
    intro x hx
    have hxC : x ∈ centralizer (D : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hDle) hx.2
    exact hDle (d3.charTwo ⟨hXH hx.1, hxC⟩)
  have hS1 : S ≠ ⊥ := bot_lt_iff_ne_bot.mp (lt_of_le_of_lt bot_le d.D_lt_S)
  have hC : ∀ T₀ : Subgroup G, T₀ ≤ S → T₀ ≠ ⊥ → (T₀.subgroupOf S).Characteristic →
      normalizer (T₀ : Set G) ⊓ (L ⊔ S) ≤ M := fun T₀ h1 h2 h3 =>
    inf_le_left.trans (d3.char_le T₀ h1 h2 h3)
  by_cases hex : ∃ J : Subgroup G, IsChiBlock (L ⊔ S) J ∧ ¬ J ≤ M
  · obtain ⟨J, ⟨hJs, hJ2, hshape⟩, hJM⟩ := hex
    obtain ⟨e⟩ := exists_equiv d hJs hJ2 hJM
    exact false_of_shape e d.nonab_img hB hc.2.2 hshape
  · apply d.L_not_le
    refine hLX.trans (le_of_kfact282 h282 hK hF (isSylowOf_sup d hsyl) hS1 hC fun J hJ => ?_)
    by_contra hJM
    exact hex ⟨J, hJ, hJM⟩

end KGFive

theorem kgStep5Sylow_of_kfact282 (h282 : KFact282) : KGStep5Sylow := by
  intro G _ _ p P M x z hS hx hz H S hopt hO hΩ hnpc h2 L hDn d3 _ hc hcase
  exact KGFive.false_of_sylow h282 d3 hc hcase.2.1 hcase.2.2

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
