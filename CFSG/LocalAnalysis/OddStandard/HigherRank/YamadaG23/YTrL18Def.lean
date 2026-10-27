module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTransport

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def LF18_2a (s : Setting3 G L) : Prop := normIn L s.fr.A = centEl L s.fr.z

@[expose] def LF18_2b (s : Setting3 G L) : Prop :=
  SecProp (normIn L s.fr.A) (zL L ⊔ s.fr.A) (fun Y _ _ _ => IsFrobeniusOfOrder 18 Y)

@[expose] def LF18_2c (s : Setting3 G L) : Prop :=
  ∀ T : Subgroup G, IsSylowIn 3 (normIn L s.fr.A) T →
    IsOrbitMod T s.fr.Z ((closure {s.fr.a₁, s.fr.b₁} : Set G) \ (s.fr.Z : Set G)) ∧
    IsOrbitMod T s.fr.Z ((closure {s.fr.a₂, s.fr.b₂} : Set G) \ (s.fr.Z : Set G)) ∧
    IsOrbitMod T s.fr.Z ((s.fr.A : Set G) \
      ((closure {s.fr.a₁, s.fr.b₁} : Set G) ∪ (closure {s.fr.a₂, s.fr.b₂} : Set G)))

@[expose] def LF18_3a (s : Setting3 G L) : Prop := normIn L s.fr.B = normIn L (cen s.fr.B)

@[expose] def LF18_3b (s : Setting3 G L) : Prop := normIn L s.fr.B ≤ normIn L s.fr.F

@[expose] def LF18_3c (s : Setting3 G L) : Prop :=
  SecProp (normIn L s.fr.B) (zL L ⊔ s.fr.B) (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))

@[expose] def LF18_3d (s : Setting3 G L) : Prop :=
  ∃ k ∈ normIn L s.fr.B, IsPGroup 3 (zpowers k) ∧ k ∉ zL L

@[expose] def LF18_3e (s : Setting3 G L) : Prop :=
  ∀ k ∈ normIn L s.fr.B, IsPGroup 3 (zpowers k) → k ∉ zL L →
    normIn L s.fr.B = zL L ⊔ s.fr.B ⊔ zpowers k ⊔ zpowers (s.fr.a₁ * s.fr.b₁ * s.fr.b₂) ∧
    ActsTransitively (zpowers k) (cen s.fr.B) ⊥ ∧
    ActsTransitively (zpowers k) (thompsonSubgroup s.fr.B) (cen s.fr.B)

@[expose] def LF18_3f (s : Setting3 G L) : Prop := centIn L (cen s.fr.B) = zL L ⊔ s.fr.B

@[expose] def LF18_4a (s : Setting3 G L) : Prop := centIn L s.fr.E = zL L ⊔ s.fr.E

@[expose] def LF18_4b (s : Setting3 G L) : Prop := normIn L s.fr.E ≤ normIn L s.fr.A

@[expose] def LF18_4c (s : Setting3 G L) : Prop :=
  SecProp (normIn L s.fr.E) (zL L ⊔ s.fr.A) (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))

@[expose] def LF18_4d (s : Setting3 G L) : Prop :=
  ∀ u ∈ s.fr.E, u ∉ s.fr.Z → ∀ v ∈ s.fr.E, v ∉ s.fr.Z → ∃ k ∈ normIn L s.fr.E, k * u * k⁻¹ = v

@[expose] def LF18_4e (s : Setting3 G L) : Prop :=
  ∀ k ∈ normIn L s.fr.E, IsPGroup 3 (zpowers k) → k ∉ zL L →
    ActsTransitively (zpowers k) s.fr.E s.fr.Z ∧ ActsTransitively (zpowers k) s.fr.A s.fr.E

@[expose] def LF18_5a (s : Setting3 G L) : Prop := centIn L s.fr.F = zL L ⊔ s.fr.F

@[expose] def LF18_5b (s : Setting3 G L) : Prop :=
  SecProp (normIn L s.fr.F) (zL L ⊔ s.fr.F)
    (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))

@[expose] def LF18_5c (s : Setting3 G L) : Prop := ¬ SplitsOver (normIn L s.fr.F) s.fr.F

@[expose] def LF18_5d (s : Setting3 G L) : Prop :=
  normIn L s.fr.F = ⁅normIn L s.fr.F, normIn L s.fr.F⁆ ⊔ zL L ∧
    ⁅normIn L s.fr.F, normIn L s.fr.F⁆ ⊓ zL L = ⊥

@[expose] def LF18_5e (s : Setting3 G L) : Prop :=
  SecProp (normIn L s.fr.A ⊓ normIn L s.fr.F) (zL L ⊔ s.fr.A)
    (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))

@[expose] def LF18_5f (s : Setting3 G L) : Prop :=
  ∀ k ∈ normIn L s.fr.A ⊓ normIn L s.fr.F, IsPGroup 3 (zpowers k) → k ∉ zL L →
    ActsTransitively (zpowers k) s.fr.F s.fr.Z ∧ ActsTransitively (zpowers k) s.fr.A s.fr.F

theorem lf18_of_parts (s : Setting3 G L) (h2a : LF18_2a s) (h2b : LF18_2b s) (h2c : LF18_2c s)
    (h3a : LF18_3a s) (h3b : LF18_3b s) (h3c : LF18_3c s) (h3d : LF18_3d s) (h3e : LF18_3e s)
    (h3f : LF18_3f s) (h4a : LF18_4a s) (h4b : LF18_4b s) (h4c : LF18_4c s) (h4d : LF18_4d s)
    (h4e : LF18_4e s) (h5a : LF18_5a s) (h5b : LF18_5b s) (h5c : LF18_5c s) (h5d : LF18_5d s)
    (h5e : LF18_5e s) (h5f : LF18_5f s) : LF18 s :=
  ⟨⟨h2a, h2b, h2c⟩, ⟨h3a, h3b, h3c, h3d, h3e, h3f⟩, ⟨h4a, h4b, h4c, h4d, h4e⟩,
    ⟨h5a, h5b, h5c, h5d, h5e, h5f⟩⟩

@[expose] def LF110_1 (s : Setting3 G L) (g : G) : Prop :=
  SecProp (normIn L s.fr.A ⊔ closure {g}) (zL L ⊔ s.fr.A)
    (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))

@[expose] def LF110_2 (s : Setting3 G L) (g : G) : Prop :=
  {x : G | x ∈ L ⊔ closure {g} ∧ ∀ a ∈ s.fr.A, ⁅a, x⁆ ∈ s.fr.Z} =
    ((zL L ⊔ s.fr.A : Subgroup G) : Set G)

@[expose] def LF110_3 (s : Setting3 G L) (g : G) : Prop :=
  {x : G | x ∈ L ⊔ closure {g} ∧ ∀ y ∈ s.fr.E ⊔ s.fr.F, ⁅y, x⁆ ∈ s.fr.Z} =
    ((zL L ⊔ s.fr.A : Subgroup G) : Set G)

@[expose] def LF110_4 (s : Setting3 G L) (g : G) : Prop := g ∈ normalizer (s.fr.F : Set G)

@[expose] def LF110_5 (s : Setting3 G L) (g : G) : Prop :=
  ∀ x ∈ normIn L s.fr.F, ⁅g, x⁆ ∈ s.fr.F ⊔ zL L

theorem lf110_of_parts (s : Setting3 G L)
    (h1 : ∀ g : G, g ^ 2 = 1 → ActsAs L g s.fr'.σ → LF110_1 s g)
    (h2 : ∀ g : G, g ^ 2 = 1 → ActsAs L g s.fr'.σ → LF110_2 s g)
    (h3 : ∀ g : G, g ^ 2 = 1 → ActsAs L g s.fr'.σ → LF110_3 s g)
    (h4 : ∀ g : G, g ^ 2 = 1 → ActsAs L g s.fr'.σ → LF110_4 s g)
    (h5 : ∀ g : G, g ^ 2 = 1 → ActsAs L g s.fr'.σ → LF110_5 s g) : LF110 s :=
  fun g hg2 hg => ⟨⟨h1 g hg2 hg, h2 g hg2 hg, h3 g hg2 hg⟩, h4 g hg2 hg, h5 g hg2 hg⟩

end CFSG.OddStandard.HigherRank.YamadaG23
