module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OSemi2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OSemi4

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite)

theorem no_semilinear_involution {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (σ : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) ≃+ (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (θ : F →+* F) (hθ : θ ≠ RingHom.id F) (hσ : ∀ (r : F) x, σ (r • x) = θ r • σ x)
    (hσσ : ∀ x, σ (σ x) = x)
    (hN : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∃ g' ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x,
        σ ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          x) =
          (g' : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
            σ x) :
    False := by
  have hθθ : ∀ r, θ (θ r) = r := by
    intro r
    have h1 := congrFun (hσσ (r • (Pi.single (Sum.inl idx0) 1 : OW F))) (Sum.inl idx0)
    rw [hσ, hσ, hσσ] at h1
    simpa using h1
  have hadd : ∀ x y, σ (x + y) = σ x + σ y := map_add σ
  obtain ⟨μ, hμ⟩ := semi_similitude hirr (⇑σ) θ hθθ hadd hσ hN
  obtain ⟨σ₁, hσ₁add, hσ₁sm, hσ₁inv, hσ₁q⟩ :=
    semi_normalize hirr (⇑σ) θ hθθ hadd hσ hσσ hμ
  have hS : SemiInvol b c θ σ₁ := ⟨hσ₁add, hσ₁sm, hσ₁inv, hσ₁q⟩
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hn
  obtain ⟨σ', hσ', hσ'e, v₁, hv1, hv2, hv3, hv4, t₁, hσ'v⟩ :=
    semi_exists_plane hirr hF (PNat.one_le n) hS
  have hli : LinearIndependent F ![eV F idx0, v₁] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hx := congrFun hst (Sum.inl idx0)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, hv1,
      mul_zero, add_zero, Pi.zero_apply] at hx
    refine ⟨hx, ?_⟩
    rw [hx, zero_smul, zero_add] at hst
    rcases smul_eq_zero.mp hst with ht | ht
    · exact ht
    · exact absurd ht hv3
  have hwu : polar (quadMinus 3 F b c) (eV F idx0) v₁ = 0 := by
    rw [polar_comm, polar_e_right, hv2]
  exact semi_plane_false hirr hθ hθθ hσ' hli (quad_eV idx0) hv4 hwu hσ'e hσ'v

end CFSG.LocalAnalysis.RankThreeUC
