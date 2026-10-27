module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] {D : TabData} {elt : ℕ → Γ}

theorem not_splitsOver_of_sylow [Finite Γ] {N F S : Subgroup Γ}
    (hFN : (F.subgroupOf N).Normal) (hS : IsSylowIn 2 N S) (hFS : F ≤ S)
    (hno : ∀ P : Subgroup Γ, P ≤ S → P ⊓ F = ⊥ → Nat.card P * Nat.card F ≠ Nat.card S) :
    ¬ SplitsOver N F := by
  rintro ⟨C, hCN, hFC, hsupFC⟩
  have hSN : S ≤ N := hS.1
  have hFNle : F ≤ N := le_trans hFS hSN
  have hNnorm : N ≤ normalizer (F : Set Γ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFNle).mp hFN
  have hCnorm : C ≤ normalizer (F : Set Γ) := le_trans hCN hNnorm
  have hNF : (N : Set Γ) = (C : Set Γ) * (F : Set Γ) := by
    rw [← hsupFC, sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right C F hCnorm
  let P : Subgroup Γ := S ⊓ C
  have hPS : P ≤ S := inf_le_left
  have hSP : S ≤ F ⊔ P := by
    intro s hs
    have hsN : s ∈ (N : Set Γ) := hSN hs
    rw [hNF, Set.mem_mul] at hsN
    obtain ⟨c, hcC, f, hfF, hcf⟩ := hsN
    have hcS : c ∈ S := by
      have hc_eq : c = s * f⁻¹ := by rw [← hcf]; group
      rw [hc_eq]
      exact S.mul_mem hs (S.inv_mem (hFS hfF))
    have hcP : c ∈ P := ⟨hcS, hcC⟩
    rw [← hcf]
    exact (F ⊔ P).mul_mem (Subgroup.mem_sup_right hcP) (Subgroup.mem_sup_left hfF)
  have hsupFS : F ⊔ P = S := le_antisymm (sup_le hFS inf_le_left) hSP
  have hFP : F ⊓ P = ⊥ := by
    change F ⊓ (S ⊓ C) = ⊥
    rw [← inf_assoc, inf_eq_left.mpr hFS, hFC]
  have hPF : P ⊓ F = ⊥ := by rw [inf_comm]; exact hFP
  have hPnorm : P ≤ normalizer (F : Set Γ) := le_trans hPS (le_trans hSN hNnorm)
  have hSPF : (S : Set Γ) = (P : Set Γ) * (F : Set Γ) := by
    rw [← hsupFS, sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right P F hPnorm
  have hcard : Nat.card P * Nat.card F = Nat.card S := by
    let φ : ↥P × ↥F → ↥S := fun q =>
      ⟨(q.1 : Γ) * (q.2 : Γ), S.mul_mem (hPS q.1.2) (hFS q.2.2)⟩
    have hφ : Function.Bijective φ := by
      constructor
      · rintro ⟨p₁, f₁⟩ ⟨p₂, f₂⟩ heq
        have hval : (p₁ : Γ) * (f₁ : Γ) = (p₂ : Γ) * (f₂ : Γ) := congrArg Subtype.val heq
        have hthis : (p₂ : Γ)⁻¹ * (p₁ : Γ) = (f₂ : Γ) * (f₁ : Γ)⁻¹ := by
          calc (p₂ : Γ)⁻¹ * (p₁ : Γ)
              = (p₂ : Γ)⁻¹ * ((p₁ : Γ) * (f₁ : Γ)) * (f₁ : Γ)⁻¹ := by group
            _ = (p₂ : Γ)⁻¹ * ((p₂ : Γ) * (f₂ : Γ)) * (f₁ : Γ)⁻¹ := by rw [hval]
            _ = (f₂ : Γ) * (f₁ : Γ)⁻¹ := by group
        have hmem : (p₂ : Γ)⁻¹ * p₁ ∈ P ⊓ F := by
          refine ⟨P.mul_mem (P.inv_mem p₂.2) p₁.2, ?_⟩
          rw [hthis]
          exact F.mul_mem f₂.2 (F.inv_mem f₁.2)
        have h1 : (p₂ : Γ)⁻¹ * p₁ = 1 := by
          have := hmem; rw [hPF] at this; exact Subgroup.mem_bot.mp this
        have hp : p₁ = p₂ := by
          apply Subtype.ext
          apply mul_left_cancel (a := (p₂ : Γ)⁻¹)
          rw [h1, inv_mul_cancel]
        have h2 : (f₂ : Γ) * (f₁ : Γ)⁻¹ = 1 := by rw [← hthis, h1]
        have hf : f₁ = f₂ := by
          apply Subtype.ext
          have hinv : (f₁ : Γ)⁻¹ = (f₂ : Γ)⁻¹ := by
            apply mul_left_cancel (a := (f₂ : Γ))
            rw [h2, mul_inv_cancel]
          exact inv_injective hinv
        exact Prod.ext hp hf
      · intro s
        have hs : (s : Γ) ∈ (P : Set Γ) * (F : Set Γ) := by
          rw [← hSPF]; exact s.2
        rw [Set.mem_mul] at hs
        obtain ⟨p, hpP, f, hfF, hpf⟩ := hs
        exact ⟨(⟨p, hpP⟩, ⟨f, hfF⟩), Subtype.ext hpf⟩
    have hcardφ : Nat.card (↥P × ↥F) = Nat.card ↥S :=
      Nat.card_congr (Equiv.ofBijective φ hφ)
    rwa [Nat.card_prod] at hcardφ
  exact (hno P hPS hPF) hcard

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
