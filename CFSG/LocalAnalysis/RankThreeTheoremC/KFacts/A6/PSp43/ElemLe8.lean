module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.Transport
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFactsA6
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.TwoCentral

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6

open CFSG.Open CFSG.GH74.Exceptional Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

theorem kFactPSp43ElemLe8_holds : KFactPSp43ElemLe8 := by
  intro T _ _ L ⟨e⟩ z hzL hz2 hz1 hcard A hA hAle
  set φ := modelHom e
  have hφ := modelHom_injective e
  set z₀ : L := ⟨z, hzL⟩
  have hAL : A ≤ L := hAle.trans ((pCoreOf_le_self 2 _).trans inf_le_left)
  set A₀ := A.comap L.subtype
  have hA₀ : A₀.map L.subtype = A := map_comap_subtype hAL
  have hA₀le : A₀ ≤ pCoreOf 2 (centralizer ({z₀} : Set L)) := by
    rw [← Subgroup.map_le_map_iff_of_injective L.subtype_injective, hA₀,
      ← pCoreOf_map_of_injective' L.subtype_injective, map_subtype_centralizer]
    exact hAle
  have hA'le : A₀.map φ ≤ pCoreOf 2 (P ⊓ centralizer ({φ z₀} : Set (Equiv.Perm (Fin 45)))) := by
    rw [← map_model_centralizer, pCoreOf_map_of_injective' hφ]
    exact Subgroup.map_mono hA₀le
  have hA₀comm : ∀ x ∈ A₀, ∀ y ∈ A₀, x * y = y * x := by
    intro x hx y hy
    exact L.subtype_injective (by
      rw [map_mul, map_mul]
      exact comm_of_isElemAbelian hA _ hx _ hy)
  have hz₀2 : φ z₀ ^ 2 = 1 := by
    rw [← map_pow]
    have : z₀ ^ 2 = 1 := Subtype.ext (by simpa using hz2)
    rw [this, map_one]
  have hz₀1 : φ z₀ ≠ 1 := by
    intro h
    apply hz1
    have : z₀ = 1 := hφ (by rw [h, map_one])
    exact congrArg Subtype.val this
  have hcardP := card_model_centralizer e z₀
  rw [hcard] at hcardP
  have h8 := card_le_eight_of_le_pCoreOf (modelHom_mem e z₀) hz₀2 hz₀1 hcardP
    (comm_of_map hA₀comm) hA'le
  rw [Subgroup.card_map_of_injective hφ] at h8
  rw [← hA₀, Subgroup.card_map_of_injective L.subtype_injective]
  exact h8

end CFSG.LocalAnalysis.RankThreeTheoremC.A6
