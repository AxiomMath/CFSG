module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Setting3
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def zL (L : Subgroup G) : Subgroup G := (center ↥L).map L.subtype

@[expose] def frameWith (s : Setting3 G L) (g : G) : Frame G :=
  { toSFrame := s.fr, σ := g }

@[expose] def Pres11 (fr : Frame G) : Prop :=
  ∃ h : ∀ r ∈ Frame.rels11, FreeGroup.lift fr.gens11 r = 1,
    Function.Injective (PresentedGroup.toGroup h) ∧ (PresentedGroup.toGroup h).range = fr.Sσ

@[expose] def ActsTransitively (T V W : Subgroup G) : Prop :=
  T ≤ normalizer (V : Set G) ∧ T ≤ normalizer (W : Set G) ∧
    ∀ u ∈ V, u ∉ W → ∀ v ∈ V, v ∉ W → ∃ k ∈ T, v⁻¹ * (k * u * k⁻¹) ∈ W

@[expose] def LF18 (s : Setting3 G L) : Prop :=
  (normIn L s.fr.A = centEl L s.fr.z ∧
    SecProp (normIn L s.fr.A) (zL L ⊔ s.fr.A) (fun Y _ _ _ => IsFrobeniusOfOrder 18 Y) ∧
    ∀ T : Subgroup G, IsSylowIn 3 (normIn L s.fr.A) T →
      IsOrbitMod T s.fr.Z ((closure {s.fr.a₁, s.fr.b₁} : Set G) \ (s.fr.Z : Set G)) ∧
      IsOrbitMod T s.fr.Z ((closure {s.fr.a₂, s.fr.b₂} : Set G) \ (s.fr.Z : Set G)) ∧
      IsOrbitMod T s.fr.Z ((s.fr.A : Set G) \
        ((closure {s.fr.a₁, s.fr.b₁} : Set G) ∪ (closure {s.fr.a₂, s.fr.b₂} : Set G)))) ∧
  (normIn L s.fr.B = normIn L (cen s.fr.B) ∧ normIn L s.fr.B ≤ normIn L s.fr.F ∧
    SecProp (normIn L s.fr.B) (zL L ⊔ s.fr.B) (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∧
    (∃ k ∈ normIn L s.fr.B, IsPGroup 3 (zpowers k) ∧ k ∉ zL L) ∧
    (∀ k ∈ normIn L s.fr.B, IsPGroup 3 (zpowers k) → k ∉ zL L →
      normIn L s.fr.B = zL L ⊔ s.fr.B ⊔ zpowers k ⊔ zpowers (s.fr.a₁ * s.fr.b₁ * s.fr.b₂) ∧
      ActsTransitively (zpowers k) (cen s.fr.B) ⊥ ∧
      ActsTransitively (zpowers k) (thompsonSubgroup s.fr.B) (cen s.fr.B)) ∧
    centIn L (cen s.fr.B) = zL L ⊔ s.fr.B) ∧
  (centIn L s.fr.E = zL L ⊔ s.fr.E ∧ normIn L s.fr.E ≤ normIn L s.fr.A ∧
    SecProp (normIn L s.fr.E) (zL L ⊔ s.fr.A) (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∧
    (∀ u ∈ s.fr.E, u ∉ s.fr.Z → ∀ v ∈ s.fr.E, v ∉ s.fr.Z →
      ∃ k ∈ normIn L s.fr.E, k * u * k⁻¹ = v) ∧
    ∀ k ∈ normIn L s.fr.E, IsPGroup 3 (zpowers k) → k ∉ zL L →
      ActsTransitively (zpowers k) s.fr.E s.fr.Z ∧ ActsTransitively (zpowers k) s.fr.A s.fr.E) ∧
  (centIn L s.fr.F = zL L ⊔ s.fr.F ∧
    SecProp (normIn L s.fr.F) (zL L ⊔ s.fr.F)
      (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∧
    ¬ SplitsOver (normIn L s.fr.F) s.fr.F ∧
    (normIn L s.fr.F = ⁅normIn L s.fr.F, normIn L s.fr.F⁆ ⊔ zL L ∧
      ⁅normIn L s.fr.F, normIn L s.fr.F⁆ ⊓ zL L = ⊥) ∧
    SecProp (normIn L s.fr.A ⊓ normIn L s.fr.F) (zL L ⊔ s.fr.A)
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∧
    ∀ k ∈ normIn L s.fr.A ⊓ normIn L s.fr.F, IsPGroup 3 (zpowers k) → k ∉ zL L →
      ActsTransitively (zpowers k) s.fr.F s.fr.Z ∧ ActsTransitively (zpowers k) s.fr.A s.fr.F)

@[expose] def LF110 (s : Setting3 G L) : Prop :=
  ∀ g : G, g ^ 2 = 1 → ActsAs L g s.fr'.σ →
    (SecProp (normIn L s.fr.A ⊔ closure {g}) (zL L ⊔ s.fr.A)
        (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      {x : G | x ∈ L ⊔ closure {g} ∧ ∀ a ∈ s.fr.A, ⁅a, x⁆ ∈ s.fr.Z} =
        ((zL L ⊔ s.fr.A : Subgroup G) : Set G) ∧
      {x : G | x ∈ L ⊔ closure {g} ∧ ∀ y ∈ s.fr.E ⊔ s.fr.F, ⁅y, x⁆ ∈ s.fr.Z} =
        ((zL L ⊔ s.fr.A : Subgroup G) : Set G)) ∧
    (g ∈ normalizer (s.fr.F : Set G) ∧ ∀ x ∈ normIn L s.fr.F, ⁅g, x⁆ ∈ s.fr.F ⊔ zL L)

structure LFacts (s : Setting3 G L) : Prop where
  fact12 : (frameWith s 1).Fact12
  fact14 : (frameWith s 1).Fact14
  sigma : ∀ g : G, g ^ 2 = 1 → ActsAs L g s.fr'.σ →
    (frameWith s g).Fact13 ∧ (frameWith s g).Fact15 ∧ Pres11 (frameWith s g)
  fact18 : LF18 s
  fact110 : LF110 s

@[expose] def YTransport : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ s : Setting3 G L, LFacts s

end CFSG.OddStandard.HigherRank.YamadaG23
