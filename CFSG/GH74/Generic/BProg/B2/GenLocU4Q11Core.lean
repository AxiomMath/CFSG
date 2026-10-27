module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q11Tv
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtBd
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtCore

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary GenLocU4QSu4

namespace GenLocU4Q11

open GenLocU4Q11Sg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem exists_half_skew (σ : K ≃+* K) (h2 : (2 : K) ≠ 0) (c : K) (hc : c + σ c = 0) :
    ∃ d : K, c = 2 * d ∧ σ d = -d := by
  refine ⟨c / 2, by field_simp, ?_⟩
  have h : σ c = -c := by linear_combination hc
  rw [map_div₀, h, map_ofNat]
  ring

theorem siegel_top (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (Γ : Subgroup (Su K p f 4))
    (h1 : ∀ (ι c : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι)
      (hc : unitaryInvolution K p f c = -c), sgElt1 ι c hι hσι hc ∈ Γ)
    (hY : ∀ (ι c : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι)
      (hc : unitaryInvolution K p f c = -c), sgEltY ι c hι hσι hc ∈ Γ)
    (hZ : ∀ (ι c : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι)
      (hc : unitaryInvolution K p f c = -c), sgEltZ ι c hι hσι hc ∈ Γ)
    (hX : ∀ (ι c : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι)
      (hc : unitaryInvolution K p f c = c), sgEltX ι c hι hσι hc ∈ Γ) : Γ = ⊤ := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK
  have hinv := hσ.invol
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have hq5 : 5 ≤ p ^ f := GenLocU4ExtCore.five_le_of_mod_four hK hq
  have hq2 : p ^ f ≠ 2 := by omega
  have keyA : ∀ (ι : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι) (c : K)
      (hc : c + unitaryInvolution K p f c = 0), tv hinv (herm_va hι hσι) hc ∈ Γ := by
    intro ι hι hσι c hc
    obtain ⟨d, rfl, hd⟩ := exists_half_skew _ h2 c hc
    rw [tv_va hσ hι hσι d hd hc]
    exact Γ.mul_mem (h1 ι d hι hσι hd) (hY ι (-d) hι hσι (by rw [map_neg, hd]))
  have keyB : ∀ (ι : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι) (c : K)
      (hc : c + unitaryInvolution K p f c = 0), tv hinv (herm_vb hι hσι) hc ∈ Γ := by
    intro ι hι hσι c hc
    obtain ⟨d, rfl, hd⟩ := exists_half_skew _ h2 c hc
    rw [tv_vb hσ hι hσι d hd hc]
    exact Γ.mul_mem (h1 ι d hι hσι hd) (hY ι d hι hσι hd)
  have keyC : ∀ (ι : K) (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι) (c : K)
      (hc : c + unitaryInvolution K p f c = 0), tv hinv (herm_vc hι hσι) hc ∈ Γ := by
    intro ι hι hσι c hc
    have hc' : unitaryInvolution K p f c = -c := by linear_combination hc
    rw [tv_vc hσ hι hσι c hc' hc]
    exact Γ.mul_mem (h1 ι c hι hσι hc') (hZ ι c hι hσι hc')
  obtain ⟨ι, hι, -⟩ := GenLocU4Su.exists_sqrt_neg_one hK hp2
  have hσι : unitaryInvolution K p f ι = ι := by
    rw [unitaryInvolution_apply K p f]; exact GenLocU4ExtBd.pow_eq_self_of_sq_neg_one hq hι
  have hιm : (-ι) * (-ι) = -1 := by linear_combination hι
  have hσιm : unitaryInvolution K p f (-ι) = -ι := by rw [map_neg, hσι]
  have hB0 := block0_of_tv hσ h2 hι hσι Γ (keyA ι hι hσι) (keyA (-ι) hιm hσιm)
  have hB2 := block2_of_tv hσ h2 hι hσι Γ (keyB ι hι hσι) (keyB (-ι) hιm hσιm)
  have hGmem : sgEltX (-ι) 1 hιm hσιm (by rw [map_one]) ∈ Γ := hX (-ι) 1 hιm hσιm (by rw [map_one])
  have hu := herm_vc hι hσι
  have hw : (![3, -ι, -1, 3 * ι] : Fin 4 → K) =
      (sgEltX (-ι) 1 hιm hσιm (by rw [map_one]) : Su K p f 4) • (![1, ι, 1, ι] : Fin 4 → K) := by
    show _ = SgX (-ι) 1 *ᵥ ![1, ι, 1, ι]
    funext j
    fin_cases j <;> simp [SgX, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    · linear_combination hι
    · linear_combination (-1 : K) * hι
    · ring
  have hv : herm (unitaryInvolution K p f) (![3, -ι, -1, 3 * ι] : Fin 4 → K) ![3, -ι, -1, 3 * ι] = 0 := by
    rw [hw, herm_smul_smul]; exact hu
  have h8 : (8 : K) ≠ 0 := by
    have : (8 : K) = 2 * 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h2
  have hv01 : unitaryInvolution K p f ((![3, -ι, -1, 3 * ι] : Fin 4 → K) 0) *
      (![3, -ι, -1, 3 * ι] : Fin 4 → K) 0 +
      unitaryInvolution K p f ((![3, -ι, -1, 3 * ι] : Fin 4 → K) 1) * (![3, -ι, -1, 3 * ι] : Fin 4 → K) 1 ≠ 0 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_ofNat, hσιm]
    intro h
    apply h8
    linear_combination h - hι
  have hT : ∀ (c' : K) (hc' : c' + unitaryInvolution K p f c' = 0), tv hinv hv hc' ∈ Γ :=
    fun c' hc' => GenLocU4Aux.tv_conj_mem hinv Γ hGmem hu (keyC ι hι hσι) hw hv c' hc'
  exact GenLocU4Aux.core_link hK hq2 Γ hB0 hB2 _ hv hv01 hT

end GenLocU4Q11

end CFSG.GH74.Generic.BProg.B2
