module

public import CFSG.GroupTheory.GL52.SylowTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Small
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open Subgroup Module CFSG.GroupTheory.GL52

@[expose] def prodHom (V W : Type*) [AddCommMonoid V] [Module (ZMod 2) V] [AddCommMonoid W]
    [Module (ZMod 2) W] : (V ≃ₗ[ZMod 2] V) →* ((V × W) ≃ₗ[ZMod 2] (V × W)) where
  toFun g := g.prodCongr (LinearEquiv.refl (ZMod 2) W)
  map_one' := by ext <;> simp
  map_mul' g h := by ext <;> simp

theorem prodHom_injective(V W : Type*) [AddCommMonoid V] [Module (ZMod 2) V] [AddCommMonoid W]
    [Module (ZMod 2) W] : Function.Injective (prodHom V W) := by
  intro g h hgh
  apply LinearEquiv.ext
  intro v
  have := congrArg (fun φ : (V × W) ≃ₗ[ZMod 2] (V × W) => (φ (v, 0)).1) hgh
  simpa [prodHom] using this

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] noncomputable def embSpace (hV : finrank (ZMod 2) V ≤ 5) :
    (V × (Fin (5 - finrank (ZMod 2) V) → ZMod 2)) ≃ₗ[ZMod 2] (Fin 5 → ZMod 2) :=
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  LinearEquiv.ofFinrankEq _ _ (by
    simp only [Module.finrank_prod, Module.finrank_fin_fun]; omega)

@[expose] noncomputable def embG52 (hV : finrank (ZMod 2) V ≤ 5) :
    (V ≃ₗ[ZMod 2] V) →* GL (Fin 5) (ZMod 2) :=
  ((glStd 5).toMonoidHom.comp (conjGL (embSpace hV)).toMonoidHom).comp (prodHom V _)

theorem embG52_injective(hV : finrank (ZMod 2) V ≤ 5) : Function.Injective (embG52 hV) :=
  ((glStd 5).injective.comp (conjGL (embSpace hV)).injective).comp (prodHom_injective _ _)

theorem card_dvd_of_normal_prime (hV : finrank (ZMod 2) V ≤ 5) {r M : ℕ} [Fact r.Prime]
    (hr : ∀ Q : Sylow r (GL (Fin 5) (ZMod 2)), Nat.card Q = r)
    (hN : ∀ Q : Sylow r (GL (Fin 5) (ZMod 2)),
      Nat.card (Subgroup.normalizer (Q : Set (GL (Fin 5) (ZMod 2)))) = M)
    {Y P : Subgroup (V ≃ₗ[ZMod 2] V)} (hP : Nat.card P = r)
    (hnorm : ∀ g ∈ Y, ∀ a ∈ P, g * a * g⁻¹ ∈ P) : Nat.card Y ∣ M := by
  have hinj := embG52_injective hV
  have hP' : Nat.card (P.map (embG52 hV)) = r := by
    rw [Subgroup.card_map_of_injective hinj, hP]
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_of_card hP' hr
  have hle : Y.map (embG52 hV) ≤ Subgroup.normalizer (Q : Set (GL (Fin 5) (ZMod 2))) := by
    rintro _ ⟨y, hy, rfl⟩
    show _ ∈ Subgroup.normalizer ((Q : Subgroup (GL (Fin 5) (ZMod 2))) : Set (GL (Fin 5) (ZMod 2)))
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hQs : ((Q : Subgroup (GL (Fin 5) (ZMod 2)))) = P.map (embG52 hV) := hQ
    rw [hQs]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨y * a * y⁻¹, hnorm y hy a ha, by simp⟩
    · rintro ⟨a, ha, hah⟩
      refine ⟨y⁻¹ * a * y, ?_, ?_⟩
      · have := hnorm y⁻¹ (Y.inv_mem hy) a ha
        simpa using this
      · have : embG52 hV (y⁻¹ * a * y) = (embG52 hV y)⁻¹ * (embG52 hV a) * embG52 hV y := by simp
        rw [this, hah]; group
  have := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective hinj, hN Q] at this
  exact this

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
