module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Model
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Ord

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelBlock

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Fin81

theorem exists_model_sylow_M128 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 0 < f)
    (hmod : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (h5 : 5 ≤ p ^ f) :
    ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs),
      ((p ^ f % 8 = 5 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 = 3 ∧ 3 < p ^ f ∧ LieModel Gs .PSU 4 p f)) ∧
      ∃ S' : Sylow 2 Gs, Nonempty (M128 ≃* ↥(S' : Subgroup Gs)) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hmod with h3 | h5'
  ·
    let K : Type := GaloisField p (2 * f)
    have hK : Nat.card K = (p ^ f) ^ 2 := by
      rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
    have hq3 : 3 < p ^ f := by omega
    have hL : LieModel (StatedProj (StatedSU 4 (p ^ f) K)) .PSU 4 p f := by
      refine Or.inl ⟨by simp [classicalTags], ⟨hp, hf, ?_⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
      refine ⟨by norm_num, ?_⟩
      intro h
      simp only [Prod.mk.injEq] at h
      omega
    have hv := v2_card_model_psu hp h3 hL
    obtain ⟨Φ, hΦ⟩ := exists_M128_embedding_uni (F := K) (p := p) (f := f) hK hp2 (by omega)
    obtain ⟨S', hS'⟩ := exists_sylow_M128_of_embedding Φ hΦ hv
    exact ⟨_, inferInstance, inferInstance, Or.inr ⟨h3, hq3, hL⟩, S', hS'⟩
  ·
    obtain ⟨F, hFfield, hFfin, hF⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f :=
      ⟨GaloisField p f, inferInstance, inferInstance, GaloisField.card p f (by omega)⟩
    have hL : LieModel (StatedProj (StatedSL 4 F)) .PSL 4 p f := by
      refine Or.inl ⟨by simp [classicalTags], ⟨hp, hf, ?_⟩, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
      refine ⟨by norm_num, ?_, ?_⟩ <;> intro h <;> simp only [Prod.mk.injEq] at h <;> omega
    have hv := v2_card_model_psl hp h5' hL
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
    obtain ⟨Φ, hΦ⟩ := exists_M128_embedding_lin (F := F) h2 (by rw [hF]; omega)
    obtain ⟨S', hS'⟩ := exists_sylow_M128_of_embedding Φ hΦ hv
    exact ⟨_, inferInstance, inferInstance, Or.inl ⟨h5', hL⟩, S', hS'⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
