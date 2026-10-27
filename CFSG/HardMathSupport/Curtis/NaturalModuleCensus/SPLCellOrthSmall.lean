module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrthGlue
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrthDim

public section

open Matrix Module CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open scoped IsMulCommutative

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrth

open CFSG.HardMathSupport.Curtis

variable {K : Type} [Field K] [Finite K] {n f : ℕ} {Q : QuadraticForm K (Fin (2 * n) → K)}

theorem orth_small_false (h : OrthCellData Q f) (hn : 2 * n < 10) {p r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : ¬ r ∣ p - 1)
    (Ē : Subgroup (matrixProjectiveDerived Q)) (hE : CFSG.Open.IsElemAbelian p Ē)
    (hcard : Nat.card Ē = p ^ 4) (γ : MulAut (matrixProjectiveDerived Q)) (k : ℕ)
    (hγ : γ ^ r ^ k = 1) (hγE : ∀ e ∈ Ē, γ e ∈ Ē) (hnt : ∃ e ∈ Ē, γ e ≠ e) : False := by
  classical
  have : CharP K 2 := h.charP_two
  have hQ := h.exists_ne_zero
  obtain ⟨g, rfl, hσ⟩ := h.exists_pair_of_prime_power hr (by omega) hγ
  have : IsMulCommutative ↥Ē := hE.1
  have : Fintype ↥Ē := Fintype.ofFinite _
  have hpK : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0).symm
  have hGp : ∀ e : ↥Ē, e ^ p = 1 := fun e => Subtype.ext (hE.2 e e.2)
  have hGK : ((Fintype.card ↥Ē : ℕ) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    push_cast
    exact pow_ne_zero _ hpK
  have hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0 := fun v hv =>
    h.nondegenerate.1 v (fun w => by simpa using hv w)
  let ρ : ↥Ē →* ((Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) := (omegaLin Q hQ).comp Ē.subtype
  have hρQ : ∀ (e : ↥Ē) v, Q (ρ e v) = Q v := fun e v =>
    (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.mem_matrixIsometries_iff Q _).1
      (omegaRep_mem_isometries Q hQ e) v
  obtain ⟨e0, he0, hne⟩ := hnt
  have hdim := five_pieces_dimension_ge_ten (K := K) (V := Fin (2 * n) → K) h.card_eq hp hp2 hr hr5
    hrp hGp hGK ρ ((omegaLin_injective Q hQ).comp Subtype.val_injective) Q hreg hρQ
    (restrictAut (matrixProjectiveConjugationHom Q g) Ē hγE)
    (restrictAut_pow_eq_one _ _ _ _ hγ) ⟨e0, he0⟩ (fun h' => hne (congrArg Subtype.val h'))
    g.val.right hσ (Coordinator.SPLCell.semiMap g.val.left g.val.right)
    (Coordinator.SPLCell.semiMap_bijective _ _)
    (fun e v => semiMap_omegaLin Q hQ g e v)
  rw [Module.finrank_fin_fun] at hdim
  omega

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrth
