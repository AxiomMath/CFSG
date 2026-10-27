module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenSylow
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Certificate9695

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem exists_model_data :
    ∃ (H₀ : Subgroup (Equiv.Perm (Fin 42))) (M : Fin 4 → Subgroup (Equiv.Perm (Fin 42))),
      H₀ ≤ R ∧ Nat.card H₀ = 27 ∧ (∀ k, Nat.card (M k) = 9) ∧
      (∀ u ∈ H₀, ∀ v ∈ H₀, u * v = v * u → ∃ k, u ∈ M k ∧ v ∈ M k) ∧ M 0 ≤ S ∧
      ∀ k : Fin 4, k ≠ 0 →
        Subgroup.closure {s | s ∈ S ∧ ∃ r ∈ M k, r ≠ 1 ∧ r * s * r⁻¹ = s} = S :=
  Certificates.certificate9695

theorem perm_gen
    {F : Subgroup (Equiv.Perm (Fin 42))} (hFR : F ≤ R) (hF : CFSG.Open.IsElemAbelian 3 F)
    (hFcard : Nat.card F = 9) :
    F ≤ S ∨ Subgroup.closure {s | s ∈ S ∧ ∃ r ∈ F, r ≠ 1 ∧ r * s * r⁻¹ = s} = S := by
  obtain ⟨H₀, M, hH₀R, hH₀, hM, hpair, hM0, hgen⟩ := exists_model_data
  exact model_gen R S H₀ M (fun g hg s hs => conj_mem_S hg hs) card_R hH₀R hH₀ hM hpair hM0 hgen
    hFR hF hFcard

end CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen
