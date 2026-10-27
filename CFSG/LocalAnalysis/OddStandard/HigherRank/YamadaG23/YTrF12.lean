module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrMap
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocC

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] [Finite Γ₁] [Finite Γ₂] {f : Γ₁ →* Γ₂}

private lemma f12_c1 (hf : Function.Injective f) (gf : GFrame Γ₁) :
    ({C : Set Γ₂ | ∃ y ∈ invols (gf.map f).S, C = conjClass (gf.map f).S y} =
        Set.range (gf.map f).classes12) ↔
      ({C : Set Γ₁ | ∃ y ∈ invols gf.S, C = conjClass gf.S y} =
        Set.range gf.classes12) := by
  have hL : {C : Set Γ₂ | ∃ y ∈ invols (gf.map f).S, C = conjClass (gf.map f).S y} =
      (Set.image f) '' {C : Set Γ₁ | ∃ y ∈ invols gf.S, C = conjClass gf.S y} := by
    rw [GFrame.map_S (f := f) (gf := gf)]
    ext C
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [invols_map hf (f := f) gf.S] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      exact ⟨conjClass gf.S y₀, ⟨y₀, hy₀, rfl⟩,
        (conjClass_map (f := f) gf.S y₀).symm⟩
    · rintro ⟨C₀, ⟨y₀, hy₀, rfl⟩, hC⟩
      refine ⟨f y₀, ?_, ?_⟩
      · rw [invols_map hf (f := f) gf.S]; exact ⟨y₀, hy₀, rfl⟩
      · rw [← hC, conjClass_map (f := f) gf.S y₀]
  have hR : Set.range (gf.map f).classes12 = (Set.image f) '' Set.range gf.classes12 := by
    ext C
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨gf.classes12 i, ⟨i, rfl⟩, (GFrame.map_classes12 (f := f) (gf := gf) i).symm⟩
    · rintro ⟨C₀, ⟨i, rfl⟩, hC⟩
      exact ⟨i, by rw [← hC]; exact GFrame.map_classes12 (f := f) (gf := gf) i⟩
  rw [hL, hR]
  exact Set.image_eq_image (f := Set.image f) ((Set.image_injective (f := f)).mpr hf)

private lemma f12_c2 (hf : Function.Injective f) (gf : GFrame Γ₁) :
    Function.Injective (gf.map f).classes12 ↔ Function.Injective gf.classes12 := by
  have hcomp : (gf.map f).classes12 = (Set.image f) ∘ gf.classes12 := by
    funext i
    exact GFrame.map_classes12 (f := f) (gf := gf) i
  rw [hcomp]
  exact Function.Injective.of_comp_iff (f := Set.image f)
    ((Set.image_injective (f := f)).mpr hf) gf.classes12

private lemma f12_c3 (hf : Function.Injective f) (gf : GFrame Γ₁) :
    (centEl (gf.map f).S (gf.map f).z = (gf.map f).S) ↔ (centEl gf.S gf.z = gf.S) := by
  constructor
  · intro h
    rw [GFrame.map_S (f := f) (gf := gf), GFrame.map_z (f := f) (gf := gf)] at h
    rw [centEl_map hf (f := f) gf.S gf.z] at h
    exact Subgroup.map_injective hf h
  · intro h
    rw [GFrame.map_S (f := f) (gf := gf), GFrame.map_z (f := f) (gf := gf)]
    rw [centEl_map hf (f := f) gf.S gf.z, h]

private lemma f12_c4 (hf : Function.Injective f) (gf : GFrame Γ₁) :
    (centEl (gf.map f).S ((gf.map f).b₁ * (gf.map f).b₂) =
        closure {(gf.map f).a₁ * (gf.map f).a₂, (gf.map f).b₁, (gf.map f).b₂,
          (gf.map f).h₀}) ↔
      (centEl gf.S (gf.b₁ * gf.b₂) = closure {gf.a₁ * gf.a₂, gf.b₁, gf.b₂, gf.h₀}) := by
  have hcl : (closure {gf.a₁ * gf.a₂, gf.b₁, gf.b₂, gf.h₀}).map f
      = closure {f gf.a₁ * f gf.a₂, f gf.b₁, f gf.b₂, f gf.h₀} := by
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, map_mul]
  have harg : f gf.b₁ * f gf.b₂ = f (gf.b₁ * gf.b₂) := (map_mul f gf.b₁ gf.b₂).symm
  constructor
  · intro h
    rw [← (Subgroup.map_injective hf).eq_iff]
    rw [← centEl_map hf (f := f) gf.S (gf.b₁ * gf.b₂), hcl]
    rw [GFrame.map_S (f := f) (gf := gf)] at h
    dsimp only [GFrame.map] at h
    rw [harg] at h
    exact h
  · intro h
    rw [GFrame.map_S (f := f) (gf := gf)]
    dsimp only [GFrame.map]
    rw [harg, centEl_map hf (f := f) gf.S (gf.b₁ * gf.b₂), ← hcl]
    exact congrArg (Subgroup.map f) h

private lemma f12_c5 (hf : Function.Injective f) (gf : GFrame Γ₁) :
    IsZ2xD8Decomp (centEl (gf.map f).S ((gf.map f).a₁ * (gf.map f).a₂))
        ((gf.map f).a₁ * (gf.map f).a₂)
        (closure {(gf.map f).a₁, (gf.map f).b₁ * (gf.map f).b₂}) ↔
      IsZ2xD8Decomp (centEl gf.S (gf.a₁ * gf.a₂)) (gf.a₁ * gf.a₂)
        (closure {gf.a₁, gf.b₁ * gf.b₂}) := by
  have hX : centEl (gf.map f).S ((gf.map f).a₁ * (gf.map f).a₂)
      = (centEl gf.S (gf.a₁ * gf.a₂)).map f := by
    rw [GFrame.map_S (f := f) (gf := gf)]
    dsimp only [GFrame.map]
    simp only [← map_mul]
    exact centEl_map hf (f := f) gf.S (gf.a₁ * gf.a₂)
  have hc : (gf.map f).a₁ * (gf.map f).a₂ = f (gf.a₁ * gf.a₂) := by
    dsimp only [GFrame.map]
    simp only [map_mul]
  have hD : closure {(gf.map f).a₁, (gf.map f).b₁ * (gf.map f).b₂}
      = (closure {gf.a₁, gf.b₁ * gf.b₂}).map f := by
    dsimp only [GFrame.map]
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, map_mul]
  rw [hX, hc, hD]
  exact isZ2xD8Decomp_map hf (f := f) (X := centEl gf.S (gf.a₁ * gf.a₂))
    (c := gf.a₁ * gf.a₂) (D := closure {gf.a₁, gf.b₁ * gf.b₂})

private lemma f12_c6 (hf : Function.Injective f) (gf : GFrame Γ₁) :
    IsZ2xD8Decomp (centEl (gf.map f).S ((gf.map f).a₁ * (gf.map f).b₂))
        ((gf.map f).a₁ * (gf.map f).b₂)
        (closure {(gf.map f).a₁, (gf.map f).b₁ * (gf.map f).a₂}) ↔
      IsZ2xD8Decomp (centEl gf.S (gf.a₁ * gf.b₂)) (gf.a₁ * gf.b₂)
        (closure {gf.a₁, gf.b₁ * gf.a₂}) := by
  have hX : centEl (gf.map f).S ((gf.map f).a₁ * (gf.map f).b₂)
      = (centEl gf.S (gf.a₁ * gf.b₂)).map f := by
    rw [GFrame.map_S (f := f) (gf := gf)]
    dsimp only [GFrame.map]
    simp only [← map_mul]
    exact centEl_map hf (f := f) gf.S (gf.a₁ * gf.b₂)
  have hc : (gf.map f).a₁ * (gf.map f).b₂ = f (gf.a₁ * gf.b₂) := by
    dsimp only [GFrame.map]
    simp only [map_mul]
  have hD : closure {(gf.map f).a₁, (gf.map f).b₁ * (gf.map f).a₂}
      = (closure {gf.a₁, gf.b₁ * gf.a₂}).map f := by
    dsimp only [GFrame.map]
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, map_mul]
  rw [hX, hc, hD]
  exact isZ2xD8Decomp_map hf (f := f) (X := centEl gf.S (gf.a₁ * gf.b₂))
    (c := gf.a₁ * gf.b₂) (D := closure {gf.a₁, gf.b₁ * gf.a₂})

private lemma f12_c7 (hf : Function.Injective f) (gf : GFrame Γ₁) :
    IsZ2xD8Decomp (centEl (gf.map f).S ((gf.map f).b₁ * (gf.map f).a₂))
        ((gf.map f).b₁ * (gf.map f).a₂)
        (closure {(gf.map f).b₁, (gf.map f).a₁ * (gf.map f).b₂}) ↔
      IsZ2xD8Decomp (centEl gf.S (gf.b₁ * gf.a₂)) (gf.b₁ * gf.a₂)
        (closure {gf.b₁, gf.a₁ * gf.b₂}) := by
  have hX : centEl (gf.map f).S ((gf.map f).b₁ * (gf.map f).a₂)
      = (centEl gf.S (gf.b₁ * gf.a₂)).map f := by
    rw [GFrame.map_S (f := f) (gf := gf)]
    dsimp only [GFrame.map]
    simp only [← map_mul]
    exact centEl_map hf (f := f) gf.S (gf.b₁ * gf.a₂)
  have hc : (gf.map f).b₁ * (gf.map f).a₂ = f (gf.b₁ * gf.a₂) := by
    dsimp only [GFrame.map]
    simp only [map_mul]
  have hD : closure {(gf.map f).b₁, (gf.map f).a₁ * (gf.map f).b₂}
      = (closure {gf.b₁, gf.a₁ * gf.b₂}).map f := by
    dsimp only [GFrame.map]
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, map_mul]
  rw [hX, hc, hD]
  exact isZ2xD8Decomp_map hf (f := f) (X := centEl gf.S (gf.b₁ * gf.a₂))
    (c := gf.b₁ * gf.a₂) (D := closure {gf.b₁, gf.a₁ * gf.b₂})

private lemma f12_c8 (hf : Function.Injective f) (gf : GFrame Γ₁) :
    IsZ2xD8Decomp (centEl (gf.map f).S ((gf.map f).a₁ * (gf.map f).b₁ * (gf.map f).a₂))
        ((gf.map f).a₁ * (gf.map f).b₁ * (gf.map f).a₂)
        (closure {(gf.map f).a₂, (gf.map f).a₁ * (gf.map f).b₂}) ↔
      IsZ2xD8Decomp (centEl gf.S (gf.a₁ * gf.b₁ * gf.a₂)) (gf.a₁ * gf.b₁ * gf.a₂)
        (closure {gf.a₂, gf.a₁ * gf.b₂}) := by
  have hX : centEl (gf.map f).S ((gf.map f).a₁ * (gf.map f).b₁ * (gf.map f).a₂)
      = (centEl gf.S (gf.a₁ * gf.b₁ * gf.a₂)).map f := by
    rw [GFrame.map_S (f := f) (gf := gf)]
    dsimp only [GFrame.map]
    simp only [← map_mul]
    exact centEl_map hf (f := f) gf.S (gf.a₁ * gf.b₁ * gf.a₂)
  have hc : (gf.map f).a₁ * (gf.map f).b₁ * (gf.map f).a₂ =
      f (gf.a₁ * gf.b₁ * gf.a₂) := by
    dsimp only [GFrame.map]
    simp only [map_mul]
  have hD : closure {(gf.map f).a₂, (gf.map f).a₁ * (gf.map f).b₂}
      = (closure {gf.a₂, gf.a₁ * gf.b₂}).map f := by
    dsimp only [GFrame.map]
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, map_mul]
  rw [hX, hc, hD]
  exact isZ2xD8Decomp_map hf (f := f) (X := centEl gf.S (gf.a₁ * gf.b₁ * gf.a₂))
    (c := gf.a₁ * gf.b₁ * gf.a₂) (D := closure {gf.a₂, gf.a₁ * gf.b₂})

private lemma f12_c9 (hf : Function.Injective f) (gf : GFrame Γ₁) :
    (centEl (gf.map f).S (gf.map f).h₀ =
        closure {(gf.map f).b₁ * (gf.map f).b₂, (gf.map f).h₀, (gf.map f).z} ∧
      IsE 3 ↥(centEl (gf.map f).S (gf.map f).h₀)) ↔
      (centEl gf.S gf.h₀ = closure {gf.b₁ * gf.b₂, gf.h₀, gf.z} ∧
        IsE 3 ↥(centEl gf.S gf.h₀)) := by
  have hX : centEl (gf.map f).S (gf.map f).h₀ = (centEl gf.S gf.h₀).map f := by
    rw [GFrame.map_S (f := f) (gf := gf)]
    exact centEl_map hf (f := f) gf.S gf.h₀
  have hD : closure {(gf.map f).b₁ * (gf.map f).b₂, (gf.map f).h₀, (gf.map f).z}
      = (closure {gf.b₁ * gf.b₂, gf.h₀, gf.z}).map f := by
    rw [GFrame.map_z (f := f) (gf := gf)]
    dsimp only [GFrame.map]
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, map_mul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [← (Subgroup.map_injective hf).eq_iff, ← hX, ← hD]
      exact h1
    · rw [← isE_map hf (f := f) 3 (centEl gf.S gf.h₀), ← hX]
      exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [hX, hD]
      exact congrArg (Subgroup.map f) h1
    · rw [hX, isE_map hf (f := f) 3 (centEl gf.S gf.h₀)]
      exact h2

theorem f12_map_iff (hf : Function.Injective f) (gf : GFrame Γ₁) :
    (gf.map f).F12 ↔ gf.F12 := by
  unfold GFrame.F12
  exact and_congr (f12_c1 hf gf) (and_congr (f12_c2 hf gf)
    (and_congr (f12_c3 hf gf) (and_congr (f12_c4 hf gf)
    (and_congr (f12_c5 hf gf) (and_congr (f12_c6 hf gf)
    (and_congr (f12_c7 hf gf) (and_congr (f12_c8 hf gf) (f12_c9 hf gf))))))))

end CFSG.OddStandard.HigherRank.YamadaG23
