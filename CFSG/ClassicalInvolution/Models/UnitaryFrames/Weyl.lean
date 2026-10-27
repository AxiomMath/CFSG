module

public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Pairs
public import CFSG.ClassicalInvolution.Models.LinearFrames.Rho

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem rho_LcU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (h5 : 5 ≤ p ^ f) (hn : 4 ≤ n)
    {i j : Fin n} (hij : i ≠ j) (T' : Pair n) :
    (((toralFrameU hK hp h5 hn).rho ⟨LcU K p f (⟨{i, j}, Finset.card_pair hij⟩ : Pair n),
        LcU_mem_coordSetU _⟩ ⟨LcU K p f T', LcU_mem_coordSetU T'⟩ : ↥(coordSetU K p f n)) :
      Subgroup (Su K p f n)) = LcU K p f (Pair.map (Equiv.swap i j) T') := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hT := (a2Dichotomy_coordSetU hK hp h5 hn).centTrivial
  obtain ⟨g, τ, hg, h0, h1⟩ := exists_suMonomial_pair (K := K) (p := p) (f := f) (by omega) hij
  set T₀ : Pair n := ⟨{i, j}, Finset.card_pair hij⟩ with hT₀
  have hT₀' : T₀.1 = {τ ⟨0, by omega⟩, τ ⟨0 + 1, by omega⟩} := by
    show ({i, j} : Finset (Fin n)) = _
    rw [h0, show τ ⟨0 + 1, by omega⟩ = j from h1]
  let w : Su K p f n :=
    g * blockEmb K p f n 2 0 (by omega) (rotSU (unitaryInvolution K p f)) * g⁻¹
  have hwm : IsMonomialFor (suMat w) (Equiv.swap i j) := by
    have hw : suMat w = suMat g * blockMat n 0 (rotMat : Matrix (Fin 2) (Fin 2) K) * suMat g⁻¹ :=
      rfl
    have := (hg.mul (isMonomialFor_blockMat_rotMat (K := K) (by omega : 2 ≤ n))).mul
      (hg.of_mul_eq_one (suMat_inv_mul_suMat g))
    rw [hw, ← h0, ← h1, Equiv.swap_apply_apply]
    exact this
  have hwL : w ∈ LcU K p f T₀ := by
    rw [LcU_eq_map_conj h2 hg (by omega : 0 + 2 ≤ n) hT₀']
    exact ⟨blockEmb K p f n 2 0 (by omega) (rotSU (unitaryInvolution K p f)),
      ⟨rotSU (unitaryInvolution K p f), rfl⟩, rfl⟩
  have hwN : w ∈ normPart (LcU K p f T₀) (signGroupU K p f n) :=
    mem_normPart_iff.mpr ⟨hwL, monomial_mem_normalizer (mat := suMatHom K p f n) hwm⟩
  have hwC : w ∉ centPart (LcU K p f T₀) (signGroupU K p f n) := by
    intro h
    obtain ⟨e, he, hne⟩ := exists_not_comm_of_monomial (mat := suMatHom K p f n)
      (z := zEltU K p f (n := n)) h2 (fun _ => rfl) (w := w) (σ := Equiv.swap i j) hwm
      (k := τ ⟨2, by omega⟩) (Equiv.swap_apply_left i j) hij
      (fun h' => by have := τ.injective (h0.trans h'); simp [Fin.ext_iff] at this)
      (fun h' => by have := τ.injective (h1.trans h'); simp [Fin.ext_iff] at this)
    exact hne ((mem_centPart_iff.mp h).2 e he)
  refine rho_apply_of_conj (toralFrameU hK hp h5 hn) hT (fun T => LcU_mem_coordSetU T) hwN hwC ?_ T'
  intro T''
  have e := monomial_conj_zMat (mat := suMatHom K p f n) (w := w) (σ := Equiv.swap i j) hwm T''.1
  change (longRootGroupSU K p f (zMat K n T''.1)).map (MulAut.conj w).toMonoidHom =
    longRootGroupSU K p f (zMat K n (T''.1.map (Equiv.swap i j).toEmbedding))
  rw [← e]
  exact (longRootGroupSU_conj (zMat K n T''.1) w).symm

theorem weylDatumU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (h5 : 5 ≤ p ^ f) (hn : 4 ≤ n) :
    ∃ β : ↥(coordSetU K p f n) ≃ Swaps n,
      (∀ K' L : ↥(coordSetU K p f n), K' ≠ L → (Commutes (K' : Subgroup (Su K p f n)) L ↔
        (β K').1.Disjoint (β L).1)) ∧
      ∀ K' L : ↥(coordSetU K p f n),
        (β ((toralFrameU hK hp h5 hn).rho K' L)).1 = (β K').1 * (β L).1 * (β K').1⁻¹ := by
  have hF := isPairFamily_LcU (K := K) (p := p) (f := f) (n := n) hK hp (by omega)
  refine ⟨hF.swapEquiv, fun K' L hne => hF.commutes_iff_disjoint_perm hne, ?_⟩
  intro K' L
  obtain ⟨T₀, rfl⟩ := hF.equiv.surjective K'
  obtain ⟨T', rfl⟩ := hF.equiv.surjective L
  obtain ⟨i, j, hij, hT₀⟩ := Finset.card_eq_two.mp T₀.2
  have e0 : T₀ = ⟨{i, j}, Finset.card_pair hij⟩ := Subtype.ext hT₀
  have hrho : (toralFrameU hK hp h5 hn).rho (hF.equiv T₀) (hF.equiv T') =
      hF.equiv (Pair.map (Equiv.swap i j) T') := by
    apply Subtype.ext
    subst e0
    exact rho_LcU hK hp h5 hn hij T'
  have hβ : ((swapPairEquiv n).symm T₀).1 = Equiv.swap i j := by
    have : (swapPairEquiv n).symm T₀ = swapsElt hij :=
      (Equiv.symm_apply_eq (swapPairEquiv n)).mpr
        (Subtype.ext (hT₀.trans (swapPairEquiv_swapsElt hij).symm))
    rw [this]
    rfl
  rw [hrho, hF.swapEquiv_equiv, hF.swapEquiv_equiv, hF.swapEquiv_equiv, swapPairEquiv_symm_map,
    hβ]

end CFSG.ClassicalInvolution.Models
