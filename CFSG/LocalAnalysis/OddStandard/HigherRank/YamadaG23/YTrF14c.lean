module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrMap
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrSec

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] [Finite Γ₁] [Finite Γ₂] {f : Γ₁ →* Γ₂}

private lemma map_closure_singleton (x : Γ₁) :
    closure ({(f x)} : Set Γ₂) = (closure ({x} : Set Γ₁)).map f := by
  rw [← Set.image_singleton, ← MonoidHom.map_closure]

private lemma map_closure_pair (x y : Γ₁) :
    closure ({f x, f y} : Set Γ₂) = (closure ({x, y} : Set Γ₁)).map f := by
  rw [← Set.image_pair, ← MonoidHom.map_closure]

private lemma map_closure_triple (x y z : Γ₁) :
    closure ({f x, f y, f z} : Set Γ₂) = (closure ({x, y, z} : Set Γ₁)).map f := by
  rw [← Set.image_singleton, ← Set.image_insert_eq, ← Set.image_insert_eq,
    ← MonoidHom.map_closure]

private lemma forall_conjSub_map_iff (hf : Function.Injective f)
    {M L : Set (Subgroup Γ₁)} {S : Subgroup Γ₁} :
    (∀ Y ∈ Subgroup.map f '' M,
        ∃ s ∈ S.map f, ∃ Y₀ ∈ Subgroup.map f '' L, Y = conjSub s Y₀) ↔
      (∀ Y ∈ M, ∃ s ∈ S, ∃ Y₀ ∈ L, Y = conjSub s Y₀) := by
  constructor
  · intro h Y hY
    obtain ⟨s, hs, Y₀, hY₀, hEq⟩ := h (Y.map f) ⟨Y, hY, rfl⟩
    obtain ⟨s₁, hs₁, rfl⟩ := Subgroup.mem_map.mp hs
    simp only [Set.mem_image] at hY₀
    obtain ⟨Y₀₁, hY₀₁, hY₀Eq⟩ := hY₀
    rw [← hY₀Eq, conjSub_map] at hEq
    exact ⟨s₁, hs₁, Y₀₁, hY₀₁, Subgroup.map_injective hf hEq⟩
  · rintro h Y ⟨Y₁, hY₁, rfl⟩
    obtain ⟨s₁, hs₁, Y₀₁, hY₀₁, hEq⟩ := h Y₁ hY₁
    exact ⟨f s₁, Subgroup.mem_map_of_mem f hs₁, Y₀₁.map f, ⟨Y₀₁, hY₀₁, rfl⟩,
      by rw [hEq, conjSub_map]⟩

theorem f14c_map_iff (hf : Function.Injective f) (gf : GFrame Γ₁) :
    (gf.map f).F14c ↔ gf.F14c := by
  have hE : (gf.map f).E = gf.E.map f := GFrame.map_E f gf
  have hF : (gf.map f).F = gf.F.map f := GFrame.map_F f gf
  have hA : (gf.map f).A = gf.A.map f := GFrame.map_A f gf
  have hB : (gf.map f).B = gf.B.map f := GFrame.map_B f gf hf
  have hS : (gf.map f).S = gf.S.map f := GFrame.map_S f gf
  have hZ : (gf.map f).Z = gf.Z.map f := GFrame.map_Z f gf
  have himg : Function.Injective (Set.image (Subgroup.map f) :
      Set (Subgroup Γ₁) → Set (Subgroup Γ₂)) :=
    Set.image_injective.mpr (Subgroup.map_injective hf)
  have hb : ((gf.map f).b₁ * (gf.map f).b₂ : Γ₂) = f (gf.b₁ * gf.b₂) := by
    simp only [GFrame.map, map_mul]
  have hDd : closure ({(gf.map f).a₁ * (gf.map f).a₂, (gf.map f).b₁} : Set Γ₂)
      = (closure ({gf.a₁ * gf.a₂, gf.b₁} : Set Γ₁)).map f := by
    have hs : ({(gf.map f).a₁ * (gf.map f).a₂, (gf.map f).b₁} : Set Γ₂)
        = {f (gf.a₁ * gf.a₂), f gf.b₁} := by
      simp only [GFrame.map, map_mul]
    rw [hs, map_closure_pair]
  have hSupZ : cen ((gf.map f).B) ⊔ closure ({(gf.map f).h₀} : Set Γ₂)
      = (cen gf.B ⊔ closure ({gf.h₀} : Set Γ₁)).map f := by
    rw [hB]
    change cen (gf.B.map f) ⊔ closure ({(f gf.h₀)} : Set Γ₂) =
      (cen gf.B ⊔ closure ({gf.h₀} : Set Γ₁)).map f
    rw [cen_map hf gf.B, map_closure_singleton, Subgroup.map_sup]
  have hD1 : closure ({(gf.map f).a₁ * (gf.map f).b₂, (gf.map f).b₁ * (gf.map f).a₂,
      (gf.map f).z} : Set Γ₂)
      = (closure ({gf.a₁ * gf.b₂, gf.b₁ * gf.a₂, gf.z} : Set Γ₁)).map f := by
    have hs : ({(gf.map f).a₁ * (gf.map f).b₂, (gf.map f).b₁ * (gf.map f).a₂,
        (gf.map f).z} : Set Γ₂) = {f (gf.a₁ * gf.b₂), f (gf.b₁ * gf.a₂), f gf.z} := by
      rw [GFrame.map_z]
      change ({f gf.a₁ * f gf.b₂, f gf.b₁ * f gf.a₂, f gf.z} : Set Γ₂) =
        {f (gf.a₁ * gf.b₂), f (gf.b₁ * gf.a₂), f gf.z}
      simp only [map_mul]
    rw [hs, map_closure_triple]
  have hD2 : closure ({(gf.map f).a₁ * (gf.map f).b₂,
      (gf.map f).a₁ * (gf.map f).b₁ * (gf.map f).a₂, (gf.map f).z} : Set Γ₂)
      = (closure ({gf.a₁ * gf.b₂, gf.a₁ * gf.b₁ * gf.a₂, gf.z} : Set Γ₁)).map f := by
    have hs : ({(gf.map f).a₁ * (gf.map f).b₂,
        (gf.map f).a₁ * (gf.map f).b₁ * (gf.map f).a₂, (gf.map f).z} : Set Γ₂)
        = {f (gf.a₁ * gf.b₂), f (gf.a₁ * gf.b₁ * gf.a₂), f gf.z} := by
      rw [GFrame.map_z]
      change ({f gf.a₁ * f gf.b₂, f gf.a₁ * f gf.b₁ * f gf.a₂, f gf.z} : Set Γ₂) =
        {f (gf.a₁ * gf.b₂), f (gf.a₁ * gf.b₁ * gf.a₂), f gf.z}
      simp only [map_mul]
    rw [hs, map_closure_triple]
  have hMaxS : maxElemAbelian ((gf.map f).S) = Subgroup.map f '' maxElemAbelian gf.S := by
    rw [hS, maxElemAbelian_map hf gf.S]
  have hLit : ({(gf.map f).E, (gf.map f).F,
      cen ((gf.map f).B) ⊔ closure ({(gf.map f).h₀} : Set Γ₂),
      closure ({(gf.map f).a₁ * (gf.map f).b₂, (gf.map f).b₁ * (gf.map f).a₂,
        (gf.map f).z} : Set Γ₂),
      closure ({(gf.map f).a₁ * (gf.map f).b₂,
        (gf.map f).a₁ * (gf.map f).b₁ * (gf.map f).a₂, (gf.map f).z} : Set Γ₂)} :
        Set (Subgroup Γ₂))
      = Subgroup.map f '' ({gf.E, gf.F, cen gf.B ⊔ closure ({gf.h₀} : Set Γ₁),
        closure ({gf.a₁ * gf.b₂, gf.b₁ * gf.a₂, gf.z} : Set Γ₁),
        closure ({gf.a₁ * gf.b₂, gf.a₁ * gf.b₁ * gf.a₂, gf.z} : Set Γ₁)} :
          Set (Subgroup Γ₁)) := by
    rw [hE, hF, hSupZ, hD1, hD2]
    simp only [Set.image_insert_eq, Set.image_singleton]
  simp only [GFrame.F14c]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
    · rw [hE, hF, hA, hB, ← Subgroup.map_sup, ← Subgroup.map_inf_eq gf.A gf.B f hf]
      exact (Subgroup.map_injective hf).eq_iff
    · rw [hA, hB, ← Subgroup.map_inf_eq gf.A gf.B f hf, hb, hDd]
      exact isZ2xD8Decomp_map hf (gf.A ⊓ gf.B) (gf.b₁ * gf.b₂)
        (closure {gf.a₁ * gf.a₂, gf.b₁})
    · have hMax : maxElemAbelian ((gf.map f).A ⊓ (gf.map f).B)
          = Subgroup.map f '' maxElemAbelian (gf.A ⊓ gf.B) := by
        rw [hA, hB, ← Subgroup.map_inf_eq gf.A gf.B f hf,
          maxElemAbelian_map hf (gf.A ⊓ gf.B)]
      rw [hMax, hE, hF, ← Set.image_pair]
      exact himg.eq_iff
    · rw [hE, hF, ← Subgroup.map_inf_eq gf.E gf.F f hf, hB, cen_map hf gf.B]
      exact (Subgroup.map_injective hf).eq_iff
  · refine and_congr ?_ (and_congr ?_ ?_)
    · rw [hS, hF, hA, hB]
      exact secProp_maxElem_map hf gf.S gf.F gf.A gf.B
    · have hZ2 : zSeries 2 (gf.map f).S ⊔ closure ({(gf.map f).h₀} : Set Γ₂)
          = (zSeries 2 gf.S ⊔ closure ({gf.h₀} : Set Γ₁)).map f := by
        rw [hS, zSeries_map hf 2 gf.S]
        change (zSeries 2 gf.S).map f ⊔ closure ({(f gf.h₀)} : Set Γ₂)
          = (zSeries 2 gf.S ⊔ closure ({gf.h₀} : Set Γ₁)).map f
        rw [map_closure_singleton, Subgroup.map_sup]
      rw [hZ2, hS, hZ, hA]
      exact secProp_maxElem_map hf gf.S gf.Z gf.A (zSeries 2 gf.S ⊔ closure {gf.h₀})
    · have hZ2 : zSeries 2 (gf.map f).S ⊔ closure ({(gf.map f).h₀} : Set Γ₂)
          = (zSeries 2 gf.S ⊔ closure ({gf.h₀} : Set Γ₁)).map f := by
        rw [hS, zSeries_map hf 2 gf.S]
        change (zSeries 2 gf.S).map f ⊔ closure ({(f gf.h₀)} : Set Γ₂)
          = (zSeries 2 gf.S ⊔ closure ({gf.h₀} : Set Γ₁)).map f
        rw [map_closure_singleton, Subgroup.map_sup]
      rw [hZ2]
      exact nonempty_equiv_map hf (zSeries 2 gf.S ⊔ closure ({gf.h₀} : Set Γ₁))
        (Multiplicative (ZMod 2) × DihedralGroup 4)
  · refine and_congr ?_ ?_
    · rw [hS, maxElemAbelian_map hf gf.S,
        Set.ncard_image_of_injective (maxElemAbelian gf.S) (Subgroup.map_injective hf)]
    · rw [hMaxS, hS, hLit]
      exact forall_conjSub_map_iff hf
  · refine and_congr ?_ ?_
    · rw [hS, pRank_map hf 2 gf.S]
    · rw [hS, sectionalTwoRank_map hf gf.S]

end CFSG.OddStandard.HigherRank.YamadaG23
