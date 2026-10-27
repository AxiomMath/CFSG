module

public import CFSG.ClassicalInvolution.Phan.SimplyConnected

public section

namespace CFSG.ClassicalInvolution.PhanG

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary

section Equiv

variable {I C D : Type*} {X : ChamberSystem I C} {Y : ChamberSystem I D}

theorem simplyTwoConnected_of_equiv (φ : C ≃ D)
    (h : ∀ i x y, X.adj i x y ↔ Y.adj i (φ x) (φ y)) (hX : X.SimplyTwoConnected) :
    Y.SimplyTwoConnected := by
  intro y γ hγ hend
  have hf : IsMorphism Y X φ.symm := by
    intro i a b hab
    rw [h i, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hab
  have hg : IsMorphism X Y φ := fun i a b hab => (h i a b).1 hab
  have h1 : X.IsGallery (φ.symm y) (galleryMap φ.symm γ) := hf.isGallery hγ
  have h2 : galleryEnd (φ.symm y) (galleryMap φ.symm γ) = φ.symm y := by
    rw [galleryEnd_galleryMap, hend]
  have h3 := (hX _ _ h1 h2).map hg
  rw [Equiv.apply_symm_apply, galleryMap_galleryMap] at h3
  simpa using h3

end Equiv

section Frames

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

@[expose] noncomputable def frameCoset (n : ℕ) :
    ChamberSystem (Fin n) (Su K p f (n + 1) ⧸ torus (unitaryInvolution K p f) (n + 1)) :=
  cosetSystem (torus (unitaryInvolution K p f) (n + 1))
    (fun i : Fin n => torus (unitaryInvolution K p f) (n + 1) ⊔ (blockEmb2 K p f n i).range)
    (fun _ => le_sup_left)

variable {K p f}

theorem frameCoset_equiv (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ) (i : Fin n)
    (x y : Frame (unitaryInvolution K p f) (n + 1)) :
    (frameSystem (unitaryInvolution K p f) n).adj i x y ↔
      (frameCoset K p f n).adj i ((frameEquivQuotient
        (isUnitaryInvolution_unitaryInvolution hK)).symm x)
        ((frameEquivQuotient (isUnitaryInvolution_unitaryInvolution hK)).symm y) := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨a, rfl⟩ := exists_smul_stdFrame hσ x
  obtain ⟨b, rfl⟩ := exists_smul_stdFrame hσ y
  have hx : (frameEquivQuotient hσ).symm (a • stdFrame (unitaryInvolution K p f) (n + 1)) =
      (a : Su K p f (n + 1) ⧸ torus (unitaryInvolution K p f) (n + 1)) := by
    rw [Equiv.symm_apply_eq, frameEquivQuotient_mk]
  have hy : (frameEquivQuotient hσ).symm (b • stdFrame (unitaryInvolution K p f) (n + 1)) =
      (b : Su K p f (n + 1) ⧸ torus (unitaryInvolution K p f) (n + 1)) := by
    rw [Equiv.symm_apply_eq, frameEquivQuotient_mk]
  rw [hx, hy, frameCoset, cosetSystem_adj_mk, adj_smul_stdFrame_smul_iff]

theorem frameCoset_simplyTwoConnected (hK : Nat.card K = (p ^ f) ^ 2) (hq : 4 ≤ p ^ f)
    (n : ℕ) : (frameCoset K p f n).SimplyTwoConnected :=
  simplyTwoConnected_of_equiv (X := frameSystem (unitaryInvolution K p f) n)
    (frameEquivQuotient (isUnitaryInvolution_unitaryInvolution hK)).symm
    (fun i x y => frameCoset_equiv hK n i x y)
    (frameSystem_simplyTwoConnected (isUnitaryInvolution_unitaryInvolution hK) hK hq n)

end Frames

end CFSG.ClassicalInvolution.PhanG
