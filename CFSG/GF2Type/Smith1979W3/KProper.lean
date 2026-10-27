module

public import CFSG.GF2Type.Smith1979W3.Reducible
public import CFSG.Quasithin.Vol2.Ch12Sec2SettingK
public import CFSG.Assembly.Exhaustiveness
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeldBridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG CFSG.Blueprint CFSG.Open CFSG.LargeExtraspecial CFSG.ComponentClassification
open scoped MatrixGroups

@[expose] def ReducibleWidthThreeK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ S : Setting G,
    S.width = 3 → NotWeaklyClosed S → S.IsReducible →
      LieModel G .PSL 5 2 1 ∨ NativeSporadic.IsSporadic G .M24 ∨ NativeSporadic.IsSporadic G .He

theorem reducibleK_of_split (hSplit : DWSplitWidthThree)
    (hAsc : Quasithin.H13.Asc94_M24He_L52TypeK) : ReducibleWidthThreeK := by
  intro G _ _ _ hKP S hw hnwc hred
  obtain ⟨W₁, W₂, H, hsurj, x, hxM, hxQ, hx, A, hAel, hA, hAx⟩ := hSplit G S hw hnwc hred
  haveI := hAel
  obtain ⟨e⟩ := H.nonempty_centralizer_mulEquiv hsurj hxM hxQ hx hA hAx
  obtain ⟨g, hg, hne⟩ := hnwc
  have hwc : ∃ g' : G, g'⁻¹ * S.z * g' ∈ pCoreOf 2 (Subgroup.centralizer ({S.z} : Set G)) ∧
      g'⁻¹ * S.z * g' ≠ S.z := by
    refine ⟨g⁻¹, ?_, ?_⟩
    · rw [AS81.pCoreOf_two_eq_QG, inv_inv]
      exact hg
    · rw [inv_inv]
      exact hne
  have hC' : Nonempty (Subgroup.centralizer ({S.z} : Set G) ≃*
      Subgroup.centralizer ({Quasithin.H13.transvection15} : Set (SL(5, ZMod 2)))) := by
    rw [AS81.transvection15_eq_cornerTransvection]
    exact ⟨e⟩
  rcases (hAsc G S.z inferInstance hKP S.orderOf_z hC' hwc).1 with hL | hM | hH
  · exact Or.inl hL
  · exact Or.inr (Or.inl hM)
  · exact Or.inr (Or.inr hH)

@[expose] def Smith1979WidthThreeK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → (∃ a b : G, a * b ≠ b * a) →
      ∀ z : G, orderOf z = 2 →
        IsExtraspecialPGroup 2
          (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
        Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
          2 ^ (1 + 2 * 3) →
        LieModel G .PSL 5 2 1 ∨ LieModel G .PSU 5 2 1 ∨ NativeSporadic.IsSporadic G .M24 ∨
          NativeSporadic.IsSporadic G .He ∨ NativeSporadic.IsSporadic G .Suz

@[expose] def Smith1979WidthThreeCharTwoKP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      ∀ w : ℕ,
        Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
          2 ^ (1 + 2 * w) →
        w = 3 →
          LieModel G .PSL 5 2 1 ∨ LieModel G .PSU 5 2 1 ∨ NativeSporadic.IsSporadic G .M24 ∨
            NativeSporadic.IsSporadic G .He ∨ NativeSporadic.IsSporadic G .Suz

theorem smith1979WidthThreeCharTwoKP_of_K
    (hbridge : ∀ i, CFSG.QuasithinUnique.B1.CatalogBridgeFor i) (h : Smith1979WidthThreeK) :
    Smith1979WidthThreeCharTwoKP := by
  intro G _ _ _ hnonab hchar hKP z hz hext w hcard hw
  have hcat : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G :=
    (CFSG.KCore.kProperNonab_iff_kProperAllSimple (C := CFSG.Blueprint.Catalog) (X := G)
      CFSG.SectionRank.catalog_isoInvariant
      CFSG.SectionRank.catalog_containsAbelianSimple).mpr
      (CFSG.Assembly.isKProperCat_of_kProper_inCatalog hbridge hKP)
  subst hw
  exact h G hcat hnonab z hz hext hcard

end CFSG.GF2Type.Smith1979W3
