module

public import CFSG.LieType.Universal.Unitary.BinaryModel.FixedLine
public import CFSG.LieType.SpecialLinear.ExteriorModel.Fundamental
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.StatedTransport
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.QuadraticDescent
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.ExteriorCubeSixBound

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Module CFSG.Open CFSG.HardMathSupport.GuralnickMalle CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.SpecialLinear.ExteriorModel Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {k : Type} [Field k] [CharP k 2]

theorem bMat_sub_one_mul_sub_one_of_card_le_one {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (ε : τ → Finset (Fin n)) (hε : ∀ r, (ε r).card ≤ 1) {g h : τ → SpecialLinearGroup (Fin n) k}
    (hgh : (bRep ε g - 1) * (bRep ε h - 1) = 0) :
    (bMat ε (fun r => (g r : Matrix (Fin n) (Fin n) k)) - 1) *
      (bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) - 1) = 0 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  have hv := congrArg (bModelEquivOfCardLeOne (k := k) ε hε)
    (LinearMap.congr_fun hgh ((bModelEquivOfCardLeOne (k := k) ε hε).symm v))
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
    bModelEquivOfCardLeOne_bRep, LinearEquiv.apply_symm_apply, LinearMap.zero_apply,
    map_zero] at hv
  rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply]
  simp only [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
  exact hv

theorem card_le_of_suRep_cube (hK : Nat.card K = (2 ^ f) ^ 2) (φ₀ : K →+* k) {m : ℕ} (h6 : m = 6)
    (ε : Fin f → Finset (Fin m)) {P : Subgroup (SU (unitaryInvolution K 2 f) m)}
    (hPel : IsElemAbelian 2 P) (i₀ : Fin f) (hε' : ∀ i, i ≠ i₀ → ε i = ∅)
    (hε : ε i₀ = {⟨3, by omega⟩})
    (hquad : ∀ a ∈ P, ∀ b ∈ P, (suRep φ₀ m ε a - 1) * (suRep φ₀ m ε b - 1) = 0) :
    Nat.card P ≤ (2 ^ f) ^ 2 := by
  subst h6
  let ψ := suFrob φ₀ f i₀
  have hcard : ∀ r, (ε r).card ≤ 1 := fun r => by
    by_cases hr : r = i₀
    · rw [hr, hε, Finset.card_singleton]
    · rw [hε' r hr, Finset.card_empty]
      exact Nat.zero_le 1
  let e := bIdxEquivSingle ε i₀ ⟨3, by omega⟩ hε hε'
  have hreindex : ∀ g : SU (unitaryInvolution K 2 f) 6,
      bMat ε (fun r => (suTwist φ₀ f 6 g r : Matrix (Fin 6) (Fin 6) k)) =
        reindexRingEquiv k e.symm (minorMatrix 3 ((SUExtras.mat _ 6 g).map ψ)) := by
    intro g
    ext s t
    rw [bMat_apply_of_single ε i₀ ⟨3, by omega⟩ hε hε', coe_reindexRingEquiv, reindex_apply,
      Equiv.symm_symm, submatrix_apply, coe_suTwist_apply]
    rfl
  have hquadK : ∀ a ∈ P, ∀ b ∈ P, (minorMatrix 3 (SUExtras.mat _ 6 a) - 1) *
      (minorMatrix 3 (SUExtras.mat _ 6 b) - 1) = 0 := by
    intro a ha b hb
    refine minorMatrix_sub_one_mul_sub_one_of_map ψ 3 _ _ ?_
    have h := bMat_sub_one_mul_sub_one_of_card_le_one ε hcard (hquad a ha b hb)
    rw [hreindex, hreindex, ← map_one (reindexRingEquiv k e.symm), ← map_sub, ← map_sub,
      ← map_mul] at h
    exact (map_eq_zero_iff _ (reindexRingEquiv k e.symm).injective).mp h
  obtain ⟨A, hAS, hAel, hcardA, hA⟩ := exists_stated_transport hK hPel
  rw [← hcardA]
  refine card_le_sq_of_exteriorPower_three_of_le_statedSU hK hAS hAel fun a ha b hb => ?_
  obtain ⟨x, hx, rfl⟩ := hA a ha
  obtain ⟨y, hy, rfl⟩ := hA b hb
  rw [exteriorPower_map_sub_one_mul_sub_one_iff]
  simp only [Units.val_mul]
  exact minorMatrix_sub_one_mul_sub_one_conj 3 _ _ _ _ (Units.mul_inv _) (Units.inv_mul _)
    (hquadK x hx y hy)

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
