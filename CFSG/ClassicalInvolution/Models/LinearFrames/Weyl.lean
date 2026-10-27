module

public import CFSG.ClassicalInvolution.Models.LinearFrames.Pairs
public import CFSG.ClassicalInvolution.Models.LinearFrames.Rho

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Phan (blockMat rotMat)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem rho_Lc (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (hn : 4 ≤ n) {i j : Fin n}
    (hij : i ≠ j) (T' : Pair n) :
    (((toralFrame hodd h5 hn).rho ⟨Lc K (⟨{i, j}, Finset.card_pair hij⟩ : Pair n),
        Lc_mem_coordSet _⟩ ⟨Lc K T', Lc_mem_coordSet T'⟩ : ↥(coordSet K n)) :
      Subgroup SL(n, K)) = Lc K (Pair.map (Equiv.swap i j) T') := by
  have h2 := two_ne_zero_of_odd_natCard hodd
  have hT := (a2Dichotomy_coordSet hodd h5 hn).centTrivial
  obtain ⟨g, τ, hg, h0, h1⟩ := exists_monomial_pair (K := K) (by omega) hij
  set T₀ : Pair n := ⟨{i, j}, Finset.card_pair hij⟩ with hT₀
  have hT₀' : T₀.1 = {τ ⟨0, by omega⟩, τ ⟨0 + 1, by omega⟩} := by
    show ({i, j} : Finset (Fin n)) = _
    rw [h0, show τ ⟨0 + 1, by omega⟩ = j from h1]
  let w : SL(n, K) := chart (by omega) g rotSL
  have hwm : IsMonomialFor (w : Matrix (Fin n) (Fin n) K) (Equiv.swap i j) := by
    have hw : (w : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K) * blockMat n 0 (rotMat : Matrix (Fin 2) (Fin 2) K) *
          ((g⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) := by
      show ((chart (by omega : 2 ≤ n) g rotSL : SL(n, K)) : Matrix (Fin n) (Fin n) K) = _
      rw [chart_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        coe_blockSL]
      rfl
    have := (hg.mul (isMonomialFor_blockMat_rotMat (K := K) (by omega : 2 ≤ n))).mul
      (hg.of_mul_eq_one (coe_inv_mul_coe g))
    rw [hw, ← h0, ← h1, Equiv.swap_apply_apply]
    exact this
  have hwL : w ∈ Lc K T₀ := by
    rw [Lc_eq_map_conj h2 hg (by omega : 0 + 2 ≤ n) hT₀']
    exact ⟨blockSL K n 2 0 (by omega) rotSL, ⟨rotSL, rfl⟩, rfl⟩
  have hwN : w ∈ normPart (Lc K T₀) (signGroup K n) :=
    mem_normPart_iff.mpr ⟨hwL, monomial_mem_normalizer (mat := slMat K n) hwm⟩
  have hwC : w ∉ centPart (Lc K T₀) (signGroup K n) := by
    intro h
    obtain ⟨e, he, hne⟩ := exists_not_comm_of_monomial (mat := slMat K n) (z := zElt K (n := n))
      h2 (fun _ => rfl) (w := w) (σ := Equiv.swap i j) hwm (k := τ ⟨2, by omega⟩)
      (Equiv.swap_apply_left i j) hij
      (fun h' => by have := τ.injective (h0.trans h'); simp [Fin.ext_iff] at this)
      (fun h' => by have := τ.injective (h1.trans h'); simp [Fin.ext_iff] at this)
    exact hne ((mem_centPart_iff.mp h).2 e he)
  refine rho_apply_of_conj (toralFrame hodd h5 hn) hT (fun T => Lc_mem_coordSet T) hwN hwC ?_ T'
  intro T''
  have e := monomial_conj_zMat (mat := slMat K n) (w := w) (σ := Equiv.swap i j) hwm T''.1
  change (longRootGroup (zMat K n T''.1)).map (MulAut.conj w).toMonoidHom =
    longRootGroup (zMat K n (T''.1.map (Equiv.swap i j).toEmbedding))
  rw [← e]
  exact (longRootGroup_conj (zMat K n T''.1) w).symm

theorem weylDatum (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (hn : 4 ≤ n) :
    ∃ β : ↥(coordSet K n) ≃ Swaps n,
      (∀ K' L : ↥(coordSet K n), K' ≠ L → (Commutes (K' : Subgroup SL(n, K)) L ↔
        (β K').1.Disjoint (β L).1)) ∧
      ∀ K' L : ↥(coordSet K n),
        (β ((toralFrame hodd h5 hn).rho K' L)).1 = (β K').1 * (β L).1 * (β K').1⁻¹ := by
  have h2 := two_ne_zero_of_odd_natCard hodd
  have hF := isPairFamily_Lc (K := K) (n := n) h2 (by omega)
  refine ⟨hF.swapEquiv, fun K' L hne => hF.commutes_iff_disjoint_perm hne, ?_⟩
  intro K' L
  obtain ⟨T₀, rfl⟩ := hF.equiv.surjective K'
  obtain ⟨T', rfl⟩ := hF.equiv.surjective L
  obtain ⟨i, j, hij, hT₀⟩ := Finset.card_eq_two.mp T₀.2
  have e0 : T₀ = ⟨{i, j}, Finset.card_pair hij⟩ := Subtype.ext hT₀
  have hrho : (toralFrame hodd h5 hn).rho (hF.equiv T₀) (hF.equiv T') =
      hF.equiv (Pair.map (Equiv.swap i j) T') := by
    apply Subtype.ext
    subst e0
    exact rho_Lc hodd h5 hn hij T'
  have hβ : ((swapPairEquiv n).symm T₀).1 = Equiv.swap i j := by
    have : (swapPairEquiv n).symm T₀ = swapsElt hij :=
      (Equiv.symm_apply_eq (swapPairEquiv n)).mpr
        (Subtype.ext (hT₀.trans (swapPairEquiv_swapsElt hij).symm))
    rw [this]
    rfl
  rw [hrho, hF.swapEquiv_equiv, hF.swapEquiv_equiv, hF.swapEquiv_equiv, swapPairEquiv_symm_map,
    hβ]

end CFSG.ClassicalInvolution.Models
