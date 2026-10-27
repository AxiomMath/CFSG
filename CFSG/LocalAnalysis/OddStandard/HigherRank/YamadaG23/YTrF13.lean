module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrMap
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocA

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] [Finite Γ₁] [Finite Γ₂] {f : Γ₁ →* Γ₂}

private lemma closure_singleton_map (z : Γ₁) : closure {f z} = (closure {z}).map f := by
  rw [MonoidHom.map_closure]
  congr 1
  simp

private lemma image_eq_image_iff (hf : Function.Injective f) {A B : Set Γ₁} :
    f '' A = f '' B ↔ A = B :=
  ((Set.image_injective (f := f)).2 hf).eq_iff

private lemma image_image_eq_iff (hf : Function.Injective f) {A B : Set (Set Γ₁)} :
    (fun C : Set Γ₁ => f '' C) '' A = (fun C : Set Γ₁ => f '' C) '' B ↔ A = B :=
  ((Set.image_injective (f := Set.image f)).2
    ((Set.image_injective (f := f)).2 hf)).eq_iff

private lemma map_centEl_eq_map_iff (hf : Function.Injective f) {V W : Subgroup Γ₁} {y : Γ₁} :
    centEl (V.map f) (f y) = W.map f ↔ centEl V y = W := by
  rw [centEl_map hf V y]
  exact (Subgroup.map_injective hf).eq_iff

private lemma map_centEl_eq_iff (hf : Function.Injective f) {V W : Subgroup Γ₁} {y : Γ₁} :
    centEl (V.map f) (f y) = centEl (W.map f) (f y) ↔ centEl V y = centEl W y := by
  rw [centEl_map hf V y, centEl_map hf W y]
  exact (Subgroup.map_injective hf).eq_iff

private lemma map_centEl_sup_eq_iff (hf : Function.Injective f) {V W : Subgroup Γ₁} {y z : Γ₁} :
    centEl (V.map f) (f y) = centEl (W.map f) (f y) ⊔ closure {f z} ↔
      centEl V y = centEl W y ⊔ closure {z} := by
  rw [centEl_map hf V y, centEl_map hf W y, closure_singleton_map z, ← Subgroup.map_sup]
  exact (Subgroup.map_injective hf).eq_iff

private lemma map_involSet (gf : GFrame Γ₁) (hf : Function.Injective f) :
    {y : Γ₂ | (∃ s ∈ (gf.map f).S, y = s * (gf.map f).σ) ∧ orderOf y = 2} =
      f '' {y : Γ₁ | (∃ s ∈ gf.S, y = s * gf.σ) ∧ orderOf y = 2} := by
  ext y
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, ho⟩
    rw [GFrame.map_S] at hs
    obtain ⟨s₁, hs₁, rfl⟩ := Subgroup.mem_map.mp hs
    refine ⟨s₁ * gf.σ, ⟨⟨s₁, hs₁, rfl⟩, ?_⟩, map_mul f s₁ gf.σ⟩
    change orderOf (f s₁ * f gf.σ) = 2 at ho
    rw [← map_mul] at ho
    exact (orderOf_injective f hf (s₁ * gf.σ)) ▸ ho
  · rintro ⟨x, hx, rfl⟩
    rw [GFrame.map_S]
    rcases hx with ⟨⟨s, hs, rfl⟩, ho⟩
    refine ⟨⟨f s, Subgroup.mem_map.mpr ⟨s, hs, rfl⟩, map_mul f s gf.σ⟩, ?_⟩
    exact (orderOf_injective f hf (s * gf.σ)) ▸ ho

private lemma map_centElSet (gf : GFrame Γ₁) (hf : Function.Injective f) :
    {y : Γ₂ | ∃ c ∈ centEl (gf.map f).S (gf.map f).σ, y = c * (gf.map f).σ} =
      f '' {y : Γ₁ | ∃ c ∈ centEl gf.S gf.σ, y = c * gf.σ} := by
  have hcent : centEl (gf.map f).S (gf.map f).σ = (centEl gf.S gf.σ).map f := by
    rw [GFrame.map_S]
    exact centEl_map hf gf.S gf.σ
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [hcent] at hc
    obtain ⟨c₁, hc₁, rfl⟩ := Subgroup.mem_map.mp hc
    exact ⟨c₁ * gf.σ, ⟨c₁, hc₁, rfl⟩, map_mul f c₁ gf.σ⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨c, hc, rfl⟩
    refine ⟨f c, ?_, map_mul f c gf.σ⟩
    rw [hcent]
    exact Subgroup.mem_map.mpr ⟨c, hc, rfl⟩

private lemma map_classSet (gf : GFrame Γ₁) (hf : Function.Injective f) :
    {C : Set Γ₂ | ∃ y ∈ invols (gf.map f).Sσ, C = conjClass (gf.map f).Sσ y} =
      (fun C : Set Γ₁ => f '' C) ''
        {C : Set Γ₁ | ∃ y ∈ invols gf.Sσ, C = conjClass gf.Sσ y} := by
  ext C
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [GFrame.map_Sσ, invols_map hf gf.Sσ] at hy
    obtain ⟨y₁, hy₁, rfl⟩ := hy
    refine ⟨conjClass gf.Sσ y₁, ⟨y₁, hy₁, rfl⟩, ?_⟩
    rw [GFrame.map_Sσ]
    exact (conjClass_map gf.Sσ y₁).symm
  · rintro ⟨C₁, ⟨y, hy, rfl⟩, hC⟩
    refine ⟨f y, ?_, ?_⟩
    · rw [GFrame.map_Sσ, invols_map hf gf.Sσ]
      exact ⟨y, hy, rfl⟩
    · rw [← hC, GFrame.map_Sσ]
      exact (conjClass_map gf.Sσ y).symm

private lemma map_rangeClass (gf : GFrame Γ₁) :
    Set.range (fun i => conjClass (gf.map f).Sσ ((gf.map f).reps13 i)) =
      (fun C : Set Γ₁ => f '' C) ''
        Set.range (fun i => conjClass gf.Sσ (gf.reps13 i)) := by
  ext C
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨conjClass gf.Sσ (gf.reps13 i), ⟨i, rfl⟩, ?_⟩
    change f '' conjClass gf.Sσ (gf.reps13 i) =
      conjClass (gf.map f).Sσ ((gf.map f).reps13 i)
    rw [GFrame.map_Sσ, GFrame.map_reps13]
    exact (conjClass_map gf.Sσ (gf.reps13 i)).symm
  · rintro ⟨C₁, ⟨i, rfl⟩, hC⟩
    refine ⟨i, ?_⟩
    change conjClass (gf.map f).Sσ ((gf.map f).reps13 i) = C
    rw [GFrame.map_Sσ, GFrame.map_reps13]
    exact (conjClass_map gf.Sσ (gf.reps13 i)).trans hC

theorem f13_map_iff (hf : Function.Injective f) (gf : GFrame Γ₁) :
    (gf.map f).F13 ↔ gf.F13 := by
  have h1 : centEl (gf.map f).S (gf.map f).σ =
        closure {(gf.map f).a₁ * (gf.map f).a₂, (gf.map f).b₁ * (gf.map f).b₂,
          (gf.map f).z} ↔
      centEl gf.S gf.σ = closure {gf.a₁ * gf.a₂, gf.b₁ * gf.b₂, gf.z} := by
    have ha : (gf.map f).a₁ * (gf.map f).a₂ = f (gf.a₁ * gf.a₂) :=
      (map_mul f gf.a₁ gf.a₂).symm
    have hb : (gf.map f).b₁ * (gf.map f).b₂ = f (gf.b₁ * gf.b₂) :=
      (map_mul f gf.b₁ gf.b₂).symm
    have hσ : (gf.map f).σ = f gf.σ := rfl
    rw [GFrame.map_S, GFrame.map_z, ha, hb, hσ]
    have hcent : centEl (gf.S.map f) (f gf.σ) = (centEl gf.S gf.σ).map f :=
      centEl_map hf gf.S gf.σ
    have hcl : closure {f (gf.a₁ * gf.a₂), f (gf.b₁ * gf.b₂), f gf.z} =
        (closure {gf.a₁ * gf.a₂, gf.b₁ * gf.b₂, gf.z}).map f := by
      rw [MonoidHom.map_closure]
      congr 1
      simp only [Set.image_insert_eq, Set.image_singleton]
    rw [hcent, hcl]
    exact (Subgroup.map_injective hf).eq_iff
  have h2 : {y : Γ₂ | (∃ s ∈ (gf.map f).S, y = s * (gf.map f).σ) ∧ orderOf y = 2} =
        {y : Γ₂ | ∃ c ∈ centEl (gf.map f).S (gf.map f).σ, y = c * (gf.map f).σ} ↔
      {y : Γ₁ | (∃ s ∈ gf.S, y = s * gf.σ) ∧ orderOf y = 2} =
        {y : Γ₁ | ∃ c ∈ centEl gf.S gf.σ, y = c * gf.σ} := by
    rw [map_involSet gf hf, map_centElSet gf hf]
    exact image_eq_image_iff hf
  have h3 : {y : Γ₂ | ∃ c ∈ centEl (gf.map f).S (gf.map f).σ, y = c * (gf.map f).σ} =
        conjClass (gf.map f).S (gf.map f).σ ↔
      {y : Γ₁ | ∃ c ∈ centEl gf.S gf.σ, y = c * gf.σ} = conjClass gf.S gf.σ := by
    have hC : conjClass (gf.map f).S (gf.map f).σ = f '' conjClass gf.S gf.σ := by
      rw [GFrame.map_S]
      exact conjClass_map gf.S gf.σ
    rw [map_centElSet gf hf, hC]
    exact image_eq_image_iff hf
  have h4 : {C : Set Γ₂ | ∃ y ∈ invols (gf.map f).Sσ, C = conjClass (gf.map f).Sσ y} =
        Set.range (fun i => conjClass (gf.map f).Sσ ((gf.map f).reps13 i)) ↔
      {C : Set Γ₁ | ∃ y ∈ invols gf.Sσ, C = conjClass gf.Sσ y} =
        Set.range (fun i => conjClass gf.Sσ (gf.reps13 i)) := by
    rw [map_classSet gf hf, map_rangeClass gf]
    exact image_image_eq_iff hf
  have h5 : Function.Injective (fun i => conjClass (gf.map f).Sσ ((gf.map f).reps13 i)) ↔
      Function.Injective (fun i => conjClass gf.Sσ (gf.reps13 i)) := by
    have hfun : (fun i => conjClass (gf.map f).Sσ ((gf.map f).reps13 i)) =
        (Set.image f) ∘ (fun i => conjClass gf.Sσ (gf.reps13 i)) := by
      funext i
      simp only [Function.comp_apply]
      rw [GFrame.map_Sσ, GFrame.map_reps13]
      exact conjClass_map gf.Sσ (gf.reps13 i)
    rw [hfun]
    exact Function.Injective.of_comp_iff ((Set.image_injective (f := f)).2 hf) _
  have h6 : centEl (gf.map f).Sσ (gf.map f).z = (gf.map f).Sσ ↔
      centEl gf.Sσ gf.z = gf.Sσ := by
    rw [GFrame.map_Sσ, GFrame.map_z]
    exact map_centEl_eq_map_iff (V := gf.Sσ) (W := gf.Sσ) (y := gf.z) hf
  have h7 : centEl (gf.map f).Sσ ((gf.map f).b₁ * (gf.map f).b₂) =
        centEl (gf.map f).S ((gf.map f).b₁ * (gf.map f).b₂) ⊔ closure {(gf.map f).σ} ↔
      centEl gf.Sσ (gf.b₁ * gf.b₂) = centEl gf.S (gf.b₁ * gf.b₂) ⊔ closure {gf.σ} := by
    have hb : (gf.map f).b₁ * (gf.map f).b₂ = f (gf.b₁ * gf.b₂) :=
      (map_mul f gf.b₁ gf.b₂).symm
    have hσ : (gf.map f).σ = f gf.σ := rfl
    rw [GFrame.map_Sσ, GFrame.map_S, hb, hσ]
    exact map_centEl_sup_eq_iff (V := gf.Sσ) (W := gf.S) (y := gf.b₁ * gf.b₂)
      (z := gf.σ) hf
  have h8 : centEl (gf.map f).Sσ ((gf.map f).a₁ * (gf.map f).a₂) =
        centEl (gf.map f).S ((gf.map f).a₁ * (gf.map f).a₂) ⊔ closure {(gf.map f).σ} ↔
      centEl gf.Sσ (gf.a₁ * gf.a₂) = centEl gf.S (gf.a₁ * gf.a₂) ⊔ closure {gf.σ} := by
    have ha : (gf.map f).a₁ * (gf.map f).a₂ = f (gf.a₁ * gf.a₂) :=
      (map_mul f gf.a₁ gf.a₂).symm
    have hσ : (gf.map f).σ = f gf.σ := rfl
    rw [GFrame.map_Sσ, GFrame.map_S, ha, hσ]
    exact map_centEl_sup_eq_iff (V := gf.Sσ) (W := gf.S) (y := gf.a₁ * gf.a₂)
      (z := gf.σ) hf
  have h9 : centEl (gf.map f).Sσ ((gf.map f).a₁ * (gf.map f).b₂) =
        centEl (gf.map f).S ((gf.map f).a₁ * (gf.map f).b₂) ↔
      centEl gf.Sσ (gf.a₁ * gf.b₂) = centEl gf.S (gf.a₁ * gf.b₂) := by
    have hb : (gf.map f).a₁ * (gf.map f).b₂ = f (gf.a₁ * gf.b₂) :=
      (map_mul f gf.a₁ gf.b₂).symm
    rw [GFrame.map_Sσ, GFrame.map_S, hb]
    exact map_centEl_eq_iff (V := gf.Sσ) (W := gf.S) (y := gf.a₁ * gf.b₂) hf
  have h10 : centEl (gf.map f).Sσ ((gf.map f).a₁ * (gf.map f).b₁ * (gf.map f).a₂) =
        centEl (gf.map f).S ((gf.map f).a₁ * (gf.map f).b₁ * (gf.map f).a₂) ⊔
          closure {(gf.map f).h₀ * (gf.map f).σ} ↔
      centEl gf.Sσ (gf.a₁ * gf.b₁ * gf.a₂) =
        centEl gf.S (gf.a₁ * gf.b₁ * gf.a₂) ⊔ closure {gf.h₀ * gf.σ} := by
    have hb : (gf.map f).a₁ * (gf.map f).b₁ * (gf.map f).a₂ =
        f (gf.a₁ * gf.b₁ * gf.a₂) := by
      change f gf.a₁ * f gf.b₁ * f gf.a₂ = f (gf.a₁ * gf.b₁ * gf.a₂)
      rw [← map_mul, ← map_mul]
    have hσ : (gf.map f).h₀ * (gf.map f).σ = f (gf.h₀ * gf.σ) :=
      (map_mul f gf.h₀ gf.σ).symm
    rw [GFrame.map_Sσ, GFrame.map_S, hb, hσ]
    exact map_centEl_sup_eq_iff (V := gf.Sσ) (W := gf.S) (y := gf.a₁ * gf.b₁ * gf.a₂)
      (z := gf.h₀ * gf.σ) hf
  have h11 : centEl (gf.map f).Sσ (gf.map f).h₀ =
        centEl (gf.map f).S (gf.map f).h₀ ⊔ closure {(gf.map f).b₁ * (gf.map f).σ} ↔
      centEl gf.Sσ gf.h₀ = centEl gf.S gf.h₀ ⊔ closure {gf.b₁ * gf.σ} := by
    have hh : (gf.map f).h₀ = f gf.h₀ := rfl
    have hb : (gf.map f).b₁ * (gf.map f).σ = f (gf.b₁ * gf.σ) :=
      (map_mul f gf.b₁ gf.σ).symm
    rw [GFrame.map_Sσ, GFrame.map_S, hh, hb]
    exact map_centEl_sup_eq_iff (V := gf.Sσ) (W := gf.S) (y := gf.h₀) (z := gf.b₁ * gf.σ) hf
  have h12 : centEl (gf.map f).Sσ (gf.map f).σ =
        centEl (gf.map f).S (gf.map f).σ ⊔ closure {(gf.map f).σ} ↔
      centEl gf.Sσ gf.σ = centEl gf.S gf.σ ⊔ closure {gf.σ} := by
    have hσ : (gf.map f).σ = f gf.σ := rfl
    rw [GFrame.map_Sσ, GFrame.map_S, hσ]
    exact map_centEl_sup_eq_iff (V := gf.Sσ) (W := gf.S) (y := gf.σ) (z := gf.σ) hf
  unfold GFrame.F13
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

end CFSG.OddStandard.HigherRank.YamadaG23
