module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4GenBase
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtCore
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtBd
public import CFSG.GH74.Generic.BProg.B2.GenLocU4QSu4

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary GenLocU4QSu4

namespace GenLocU4Q10Link

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] def Mrot (c s1 s2 : K) : Matrix (Fin 4) (Fin 4) K :=
  !![c, 0, s1, 0; 0, c, 0, s2; s1, 0, c, 0; 0, s2, 0, c]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem det_Mrot (c s1 s2 : K) : (Mrot c s1 s2).det = (c * c - s1 * s1) * (c * c - s2 * s2) := by
  simp [Mrot, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

omit [Finite K] [CharP K p] in
theorem Mrot_unitary (c s1 s2 : K) (hc : c ^ (p ^ f) = c) (hs1 : s1 ^ (p ^ f) = -s1) (hs2 : s2 ^ (p ^ f) = -s2)
    (h1 : c * c - s1 * s1 = 1) (h2 : c * c - s2 * s2 = 1) :
    ((Mrot c s1 s2).map (· ^ (p ^ f)))ᵀ * Mrot c s1 s2 = 1 := by
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mrot, Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply, hc, hs1, hs2, zero_pow hq0] <;>
    first | ring1 | linear_combination h1 | linear_combination h2

@[expose] noncomputable def rotElt (c s1 s2 : K) (hc : c ^ (p ^ f) = c) (hs1 : s1 ^ (p ^ f) = -s1)
    (hs2 : s2 ^ (p ^ f) = -s2) (h1 : c * c - s1 * s1 = 1) (h2 : c * c - s2 * s2 = 1) : Su K p f 4 :=
  su4Mk (p := p) (f := f) (Mrot c s1 s2) (by rw [det_Mrot, h1, h2, one_mul]) (Mrot_unitary c s1 s2 hc hs1 hs2 h1 h2)

theorem rotElt_smul (c s1 s2 : K) (hc : c ^ (p ^ f) = c) (hs1 : s1 ^ (p ^ f) = -s1)
    (hs2 : s2 ^ (p ^ f) = -s2) (h1 : c * c - s1 * s1 = 1) (h2 : c * c - s2 * s2 = 1) (v : Fin 4 → K) :
    (rotElt c s1 s2 hc hs1 hs2 h1 h2 : Su K p f 4) • v = Mrot c s1 s2 *ᵥ v := rfl

theorem link10_core (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) (Γ : Subgroup (Su K p f 4))
    (h0 : ∀ B : Su K p f 2, blockEmb2 K p f 3 0 B ∈ Γ) (h2 : ∀ B : Su K p f 2, blockEmb2 K p f 3 2 B ∈ Γ)
    (hrot : ∀ (c s : K) (hc : c ^ (p ^ f) = c) (hs : s ^ (p ^ f) = -s) (hs' : (-s) ^ (p ^ f) = -(-s))
      (h : c * c - s * s = 1) (h' : c * c - (-s) * (-s) = 1),
      rotElt c s s hc hs hs h h ∈ Γ ∧ rotElt c (-s) s hc hs' hs h' h ∈ Γ) : Γ = ⊤ := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK
  have hinv := hσ.invol
  have hq3 : 3 ≤ p ^ f := by
    have := GenLocU4ExtCore.five_le_of_mod_four hK hq
    omega
  have hq2 : p ^ f ≠ 2 := by omega
  have h2K : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card (Fact.out) hp2 hK
  obtain ⟨c, s, hc, hs, hcs, hs0⟩ := GenLocU4Gen.exists_rot_pair hK hp2 hq3
  have hcq : c ^ (p ^ f) = c := by rw [← unitaryInvolution_apply K p f]; exact hc
  have hsq : s ^ (p ^ f) = -s := by rw [← unitaryInvolution_apply K p f]; exact hs
  have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hsq' : (-s) ^ (p ^ f) = -(-s) := by rw [Odd.neg_pow hodd, hsq]
  have hcs' : c * c - (-s) * (-s) = 1 := by linear_combination hcs
  obtain ⟨hG1, hG4⟩ := hrot c s hcq hsq hsq' hcs hcs'
  obtain ⟨ξ, hξ⟩ := hσ.exists_norm_neg_one
  have hz0 : herm (unitaryInvolution K p f) (![1, ξ, 0, 0] : Fin 4 → K) ![1, ξ, 0, 0] = 0 := by
    rw [herm_def, Fin.sum_univ_four]
    show unitaryInvolution K p f 1 * 1 + unitaryInvolution K p f ξ * ξ + unitaryInvolution K p f 0 * 0 +
      unitaryInvolution K p f 0 * 0 = 0
    rw [map_one, map_zero]
    linear_combination hξ
  have hTz : ∀ (c' : K) (hc' : c' + unitaryInvolution K p f c' = 0), tv hinv hz0 hc' ∈ Γ := by
    intro c' hc'
    have ha2 : herm (unitaryInvolution K p f) (![1, ξ] : Fin 2 → K) ![1, ξ] = 0 := by
      rw [herm_def, Fin.sum_univ_two]
      show unitaryInvolution K p f 1 * 1 + unitaryInvolution K p f ξ * ξ = 0
      rw [map_one]
      linear_combination hξ
    have := blockEmb2_zero_eq_tv (p := p) (f := f) hinv (tv hinv ha2 hc') ![1, ξ] c' hc'
      (fun y => tv_smul hinv ha2 hc' y) (by simpa using hz0)
    have hmem := h0 (tv hinv ha2 hc')
    rw [this] at hmem
    exact hmem
  have hG : (rotElt c s s hcq hsq hsq hcs hcs * rotElt c (-s) s hcq hsq' hsq hcs' hcs : Su K p f 4) ∈ Γ :=
    Γ.mul_mem hG1 hG4
  have hvv : ((rotElt c s s hcq hsq hsq hcs hcs * rotElt c (-s) s hcq hsq' hsq hcs' hcs : Su K p f 4) •
      (![1, ξ, 0, 0] : Fin 4 → K)) = ![1, (c * c + s * s) * ξ, 0, 2 * c * s * ξ] := by
    rw [mul_smul, rotElt_smul, rotElt_smul]
    funext j
    fin_cases j <;> simp [Mrot, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      first | ring1 | linear_combination hcs
  have hv : herm (unitaryInvolution K p f) (![1, (c * c + s * s) * ξ, 0, 2 * c * s * ξ] : Fin 4 → K)
      ![1, (c * c + s * s) * ξ, 0, 2 * c * s * ξ] = 0 := by
    rw [← hvv, herm_smul_smul]
    exact hz0
  have hv01 : unitaryInvolution K p f ((![1, (c * c + s * s) * ξ, 0, 2 * c * s * ξ] : Fin 4 → K) 0) *
      (![1, (c * c + s * s) * ξ, 0, 2 * c * s * ξ] : Fin 4 → K) 0 +
      unitaryInvolution K p f ((![1, (c * c + s * s) * ξ, 0, 2 * c * s * ξ] : Fin 4 → K) 1) *
      (![1, (c * c + s * s) * ξ, 0, 2 * c * s * ξ] : Fin 4 → K) 1 ≠ 0 := by
    intro h0
    have hσcs : unitaryInvolution K p f (c * c + s * s) = c * c + s * s := by
      rw [map_add, map_mul, map_mul, hc, hs]; ring
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_one, map_mul, hσcs] at h0
    have h1 : (c * c + s * s) ^ 2 = 1 := by linear_combination (-(1 : K)) * h0 + (c * c + s * s) ^ 2 * hξ
    have h4 : (4 : K) * (s * s) * (s * s + 1) = 0 := by
      linear_combination h1 - (c * c + 3 * (s * s) + 1) * hcs
    have h4' : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2K h2K
    have hss : s * s ≠ 0 := mul_ne_zero hs0 hs0
    have hneg : s * s = -1 := by
      have := (mul_eq_zero.1 h4).resolve_left (mul_ne_zero h4' hss)
      linear_combination this
    have h5 := GenLocU4ExtBd.pow_eq_self_of_sq_neg_one hq hneg
    rw [hsq] at h5
    apply hs0
    have : (2 : K) * s = 0 := by linear_combination -h5
    exact (mul_eq_zero.1 this).resolve_left h2K
  have hT : ∀ (c' : K) (hc' : c' + unitaryInvolution K p f c' = 0), tv hinv hv hc' ∈ Γ :=
    fun c' hc' => GenLocU4Aux.tv_conj_mem hinv Γ hG hz0 hTz hvv.symm hv c' hc'
  exact GenLocU4Aux.core_link hK hq2 Γ h0 h2 _ hv hv01 hT

end GenLocU4Q10Link

end CFSG.GH74.Generic.BProg.B2
