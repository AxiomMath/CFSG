module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1F4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1G2Traces

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint (iform)

theorem g2_long_roots_check :
    ∀ x ∈ ([![1, 0], ![2, 3], ![1, 3]] : List (Fin (Tag.rank .G2) → ℤ)),
      x ∈ rootFinset .G2 ∧ iform x x = 6 := by
  decide +kernel

theorem eq_g2Long_of_iform : ∀ k : Fin (Tag.rank .G2),
    iform (Pi.single k 1 : Fin (Tag.rank .G2) → ℤ) (Pi.single k 1) = 6 → k = g2Long := by
  decide

theorem g2_long_kernel_check : ∀ m : Fin (Tag.rank .G2) → Bool,
    ∃ γ ∈ ([![1, 0], ![2, 3], ![1, 3]] : List (Fin (Tag.rank .G2) → ℤ)),
      maskChar m (Multiplicative.ofAdd γ) = 1 := by
  decide +kernel

theorem exists_long_mem_rootCharKernel_G2
    {K : Type} [Field K] (hK : ringChar K ≠ 2) {b : Fin Tag.G2.rank → Kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) :
    ∃ γ ∈ rootCharKernel b, ∀ (w : WeylGroup Tag.G2) (k : Fin Tag.G2.rank),
      w • (Pi.single k 1 : Fin Tag.G2.rank → ℤ) = γ → k = g2Long := by
  obtain ⟨γ, hγl, hγm⟩ := g2_long_kernel_check (signTupleBits b)
  refine ⟨γ, ?_, fun w k hwk => eq_g2Long_of_iform k ?_⟩
  · rw [rootCharKernel_eq_kernelRoots hK hb]
    exact ⟨mem_rootFinset.1 (g2_long_roots_check γ hγl).1, hγm⟩
  · rw [← iform_smul w, hwk]
    exact (g2_long_roots_check γ hγl).2

theorem burgOddCoreRow_G2_of_ne_three
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hK : Nat.card K = p ^ f) : BurgOddCoreRow (adjointGroup .G2 K) := by
  intro α hα
  have hf := one_le_of_card_eq_pow hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K p]; exact hp3
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  rcases odd_F4_E8_G2_involution_inner_or_quadratic (Or.inr (Or.inr ⟨rfl, hK3⟩)) hKodd hα2 with
    ⟨g, a, hαg⟩ | ⟨q, e, hq, he, hKe, δ, hδ, g, a, hαg⟩
  · refine burgOddCoreFor_innerDiagonal (Or.inl rfl) hK2 (fun k => k = g2Long)
      (fun b hb => exists_long_mem_rootCharKernel_G2 hK2 hb)
      (fun b hb hb1 => pPrimeCore_toralCentralizer_G2 hK2 hb hb1)
      (fun k hk h hU Z hZ η hη _ => ?_) hαg hα
    subst hk
    exact G2_descended_root_SL2_pointwise_inner K hp hp2 hp3 hf hK (AlgebraicClosure K) 1 h hU Z
      hZ η hη
  · have hqp : q = p := by
      have h : q ∣ p ^ f := by
        rw [← hK, hKe]
        exact dvd_pow (dvd_pow_self q (by omega)) two_ne_zero
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)
    subst hqp
    exact burgOddCoreFor_quadratic_field .G2 (by decide) hq hp2 he hKe δ hδ
      (fun k _ _ hk => (odd_F4_and_nonexceptional_G2_automorphism_normal_form hq hp2
        hk.choose_spec.1 k hk.choose_spec.2 .G2 (Or.inr ⟨rfl, hp3⟩)).1) hαg hα

end CFSG.ComponentClassification.CatLeafProof
