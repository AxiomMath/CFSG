module

public import CFSG.GH74.Generic.S3.Leaves
public import CFSG.GH74.Generic.S3.Conf

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def B_S3_terminal_conf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)),
    S3Setup G x K → CentralizerCyclic2 x K →
    ∀ (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) → p.Prime → p ≠ 2 → 5 ≤ p ^ f →
      LieModel ↥K t 3 p f →
      ∃ (v : G) (Iv Iw Ivw P : Subgroup G), Conf2A G t p f v x Iv Iw Ivw P ∧ imgBar x Iw = K

@[expose] def B_S3_prop21_lin : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (p f : ℕ) (v w : G) (Iv Iw Ivw P : Subgroup G), Conf2A G .PSL p f v w Iv Iw Ivw P →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (z u : G) (Y : Fin 3 → Subgroup G),
        Nat.card F = p ^ f ∧ p ^ f % 4 = 1 ∧ GLS.LU.IsLinearA3Neighborhood F z u Y ∧
          z = v ∧ Y 0 = Iv ∧ Y 0 ⊔ Y 1 = Iw ∧ A3Reflection w u Y

@[expose] def B_S3_prop21_uni : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (p f : ℕ) (v w : G) (Iv Iw Ivw P : Subgroup G), Conf2A G .PSU p f v w Iv Iw Ivw P →
      ∃ (F₂ F : Type) (_ : Field F₂) (_ : Finite F₂) (_ : Field F) (_ : Finite F) (z u : G)
        (Y : Fin 3 → Subgroup G),
        Nat.card F₂ = (p ^ f) ^ 2 ∧ Nat.card F = p ^ f ∧ p ^ f % 4 = 3 ∧
          GLS.LU.IsUnitaryA3Neighborhood (p ^ f) F₂ F z u Y ∧
          z = v ∧ Y 0 = Iv ∧ Y 0 ⊔ Y 1 = Iw ∧ A3Reflection w u Y

theorem b_S3_terminal_of_conf (hC : B_S3_terminal_conf) (hL : B_S3_prop21_lin)
    (hU : B_S3_prop21_uni) : B_S3_terminal := by
  refine ⟨?_, ?_⟩
  · intro G _ _ x K hset hcyc p f hp hp2 hq hmod
    obtain ⟨v, Iv, Iw, Ivw, P, hconf, himg⟩ :=
      hC G x K hset hcyc .PSL p f (Or.inl rfl) hp hp2 hq hmod
    obtain ⟨F, hF1, hF2, z, u, Y, hFc, hmod4, hA3, -, -, hY01, hRefl⟩ :=
      hL G hset.global p f v x Iv Iw Ivw P hconf
    exact ⟨F, hF1, hF2, z, u, Y, hFc, hmod4, hA3, hRefl, by rw [hY01]; exact himg⟩
  · intro G _ _ x K hset hcyc p f hp hp2 hq hmod
    obtain ⟨v, Iv, Iw, Ivw, P, hconf, himg⟩ :=
      hC G x K hset hcyc .PSU p f (Or.inr rfl) hp hp2 hq hmod
    obtain ⟨F₂, F, hF1, hF2, hF3, hF4, z, u, Y, hFc2, hFc, hmod4, hA3, -, -, hY01, hRefl⟩ :=
      hU G hset.global p f v x Iv Iw Ivw P hconf
    exact ⟨F₂, F, hF1, hF2, hF3, hF4, z, u, Y, hFc2, hFc, hmod4, hA3, hRefl,
      by rw [hY01]; exact himg⟩

end CFSG.GH74.Generic.S3
