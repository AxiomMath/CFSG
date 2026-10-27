module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherInvariant
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGaussian
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module
open scoped Pointwise

variable {K : Type*} [Field K] {n : ℕ}

theorem map_diagonal_flagSpace {d : Fin n → K} (hd : ∀ i, d i ≠ 0) (i : ℕ) :
    (flagSpace n K i).map (mulVecLin (diagonal d)) = flagSpace n K i := by
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_flagSpace] at hv
    rw [mem_flagSpace]
    intro j hj
    rw [mulVecLin_apply, mulVec_diagonal, hv j hj, mul_zero]
  · refine ⟨diagonal (fun j => (d j)⁻¹) *ᵥ v, ?_, ?_⟩
    · rw [mem_flagSpace] at hv
      rw [SetLike.mem_coe, mem_flagSpace]
      intro j hj
      rw [mulVec_diagonal, hv j hj, mul_zero]
    · rw [mulVecLin_apply, mulVec_mulVec, diagonal_mul_diagonal]
      convert one_mulVec v
      rw [← diagonal_one]
      congr 1
      funext j
      exact mul_inv_cancel₀ (hd j)

theorem exists_map_flagSpace_eq (W : Submodule K (Fin n → K)) :
    ∃ g : SpecialLinearGroup (Fin n) K,
      (flagSpace n K (finrank K W)).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = W := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, Subsingleton.elim _ _⟩
  have hk : finrank K W ≤ n := by simpa using Submodule.finrank_le W
  have hFk : finrank K (flagSpace n K (finrank K W)) = finrank K W := finrank_flagSpace hk
  obtain ⟨g₀, hg₀⟩ := Submodule.exists_linearEquiv_restrict_eq (LinearEquiv.ofFinrankEq _ _ hFk)
  have hmap₀ : (flagSpace n K (finrank K W)).map (g₀ : (Fin n → K) →ₗ[K] Fin n → K) = W := by
    refine le_antisymm ?_ fun w hw => ?_
    · rintro _ ⟨v, hv, rfl⟩
      have h := hg₀ ⟨v, hv⟩
      change _ = g₀ v at h
      rw [LinearEquiv.coe_coe, ← h]
      exact Submodule.coe_mem _
    · set f := LinearEquiv.ofFinrankEq _ _ hFk
      refine ⟨f.symm ⟨w, hw⟩, (f.symm ⟨w, hw⟩).2, ?_⟩
      rw [LinearEquiv.coe_coe, ← hg₀, LinearEquiv.apply_symm_apply]
  set d := LinearMap.det (g₀ : (Fin n → K) →ₗ[K] Fin n → K) with hd
  have hd0 : d ≠ 0 := (LinearEquiv.isUnit_det' g₀).ne_zero
  set e : Fin n → K := Pi.mulSingle ⟨0, hn⟩ d⁻¹ with he
  have he0 : ∀ i, e i ≠ 0 := fun i => by
    rw [he, Pi.mulSingle_apply]
    split_ifs
    · exact inv_ne_zero hd0
    · exact one_ne_zero
  set M := LinearMap.toMatrix' (g₀ : (Fin n → K) →ₗ[K] Fin n → K) * diagonal e with hM
  have hdet : M.det = 1 := by
    rw [hM, det_mul, LinearMap.det_toMatrix', det_diagonal, he, Fintype.prod_pi_mulSingle', ← hd,
      mul_inv_cancel₀ hd0]
  refine ⟨⟨M, hdet⟩, ?_⟩
  change (flagSpace n K (finrank K W)).map (mulVecLin M) = W
  rw [hM, mulVecLin_mul, Submodule.map_comp, map_diagonal_flagSpace he0, ← toLin'_apply',
    toLin'_toMatrix', hmap₀]

theorem exists_map_eq_of_finrank_eq {W W' : Submodule K (Fin n → K)}
    (h : finrank K W = finrank K W') :
    ∃ g : SpecialLinearGroup (Fin n) K, W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = W' := by
  obtain ⟨g, hg⟩ := exists_map_flagSpace_eq W
  obtain ⟨g', hg'⟩ := exists_map_flagSpace_eq W'
  refine ⟨g' * g⁻¹, ?_⟩
  rw [← hg']
  conv_lhs => rw [← hg]
  rw [h, ← Submodule.map_comp, ← mulVecLin_mul, ← SpecialLinearGroup.coe_mul,
    inv_mul_cancel_right]

theorem smul_submodule_eq_map (g : SpecialLinearGroup (Fin n) K) (W : Submodule K (Fin n → K)) :
    g • W = W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) :=
  rfl

theorem stabilizer_eq_mulAction_stabilizer (W : Submodule K (Fin n → K)) :
    stabilizer W = MulAction.stabilizer (SpecialLinearGroup (Fin n) K) W := by
  ext g
  rfl

theorem card_finrank_eq [Finite K] {k : ℕ} (hk : k ≤ n) :
    (Nat.card {W : Submodule K (Fin n → K) // finrank K W = k} : ℚ) =
      gaussianCoeff n k (Nat.card K) := by
  classical
  have := Fintype.ofFinite K
  have : Fintype {W : Submodule K (Fin n → K) // finrank K W = k} := Fintype.ofFinite _
  set q := Nat.card K with hq
  have hq' : Fintype.card K = q := by rw [hq, Nat.card_eq_fintype_card]
  have hq2 : 2 ≤ q := by
    have := Finite.one_lt_card (α := K)
    omega
  let φ : {s : Fin k → (Fin n → K) // LinearIndependent K s} →
      {W : Submodule K (Fin n → K) // finrank K W = k} := fun s =>
    ⟨Submodule.span K (Set.range s.1), by rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩
  have hfiber : ∀ W : {W : Submodule K (Fin n → K) // finrank K W = k}, Nat.card {s // φ s = W} =
      Nat.card {t : Fin k → W.1 // LinearIndependent K t} := by
    intro W
    refine Nat.card_congr
      { toFun := fun s => ⟨fun i => ⟨s.1.1 i, ?_⟩, ?_⟩
        invFun := fun t => ⟨⟨W.1.subtype ∘ t.1, t.2.map' _ (Submodule.ker_subtype _)⟩, ?_⟩
        left_inv := fun s => rfl
        right_inv := fun t => rfl }
    · have h := congrArg Subtype.val s.2
      change Submodule.span K (Set.range s.1.1) = W.1 at h
      rw [← h]
      exact Submodule.subset_span (Set.mem_range_self i)
    · exact LinearIndependent.of_comp W.1.subtype s.1.2
    · apply Subtype.ext
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (t.1 i).2
      · rw [finrank_span_eq_card (t.2.map' _ (Submodule.ker_subtype _)), Fintype.card_fin, W.2]
  have hW : ∀ W : {W : Submodule K (Fin n → K) // finrank K W = k},
      Nat.card {t : Fin k → W.1 // LinearIndependent K t} =
      ∏ i : Fin k, (q ^ k - q ^ (i : ℕ)) := fun W => by
    rw [card_linearIndependent (W.2.symm ▸ le_rfl), W.2, hq']
  have htotal : Nat.card {s : Fin k → (Fin n → K) // LinearIndependent K s} =
      Nat.card {W : Submodule K (Fin n → K) // finrank K W = k} *
        ∏ i : Fin k, (q ^ k - q ^ (i : ℕ)) := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv φ), Nat.card_sigma]
    simp only [hfiber, hW, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.card_eq_fintype_card]
  rw [card_linearIndependent (by rw [finrank_fin_fun]; exact hk), finrank_fin_fun, hq'] at htotal
  have hcast : ∀ m : ℕ, k ≤ m → ((∏ i : Fin k, (q ^ m - q ^ (i : ℕ)) : ℕ) : ℚ) =
      ∏ i ∈ Finset.range k, ((q : ℚ) ^ i * ((q : ℚ) ^ (m - i) - 1)) := by
    intro m hm
    rw [Nat.cast_prod, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) (by omega)), Nat.cast_pow, Nat.cast_pow,
      mul_sub, mul_one, ← pow_add, show (i : ℕ) + (m - i) = m by omega]
  have hpos : (0 : ℚ) < ∏ i ∈ Finset.range k, ((q : ℚ) ^ i * ((q : ℚ) ^ (k - i) - 1)) :=
    Finset.prod_pos fun i hi => mul_pos (by positivity)
      (pow_sub_one_pos hq2 (by rw [Finset.mem_range] at hi; omega))
  have htotal' := congrArg (fun x : ℕ => (x : ℚ)) htotal
  simp only [Nat.cast_mul] at htotal'
  rw [hcast n hk, hcast k le_rfl] at htotal'
  rw [eq_div_iff hpos.ne' |>.mpr htotal'.symm, gaussianCoeff, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_div_mul_left _ _ (by positivity)]

theorem subspace_index [Finite K] {k : ℕ} (hk : k ≤ n) :
    (Nat.card {W : Submodule K (Fin n → K) // finrank K W = k} : ℚ) =
        gaussianCoeff n k (Nat.card K) ∧
      ∀ W : Submodule K (Fin n → K), finrank K W = k →
        ((projStabilizer W).index : ℚ) = gaussianCoeff n k (Nat.card K) := by
  refine ⟨card_finrank_eq hk, fun W hW => ?_⟩
  have hcomap : (projStabilizer W).comap (proj n K) = stabilizer W := by
    rw [projStabilizer, Subgroup.comap_map_eq_self]
    rw [ker_proj]
    exact scalars_le_stabilizer W
  rw [← Subgroup.index_comap_of_surjective _ (proj_surjective n K), hcomap,
    stabilizer_eq_mulAction_stabilizer, MulAction.index_stabilizer, ← card_finrank_eq hk,
    ← Nat.card_coe_set_eq]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun W' => ?_)
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    rw [smul_submodule_eq_map, ← hW]
    exact LinearEquiv.finrank_map_eq (Matrix.SpecialLinearGroup.toLin' g) W
  · intro h
    obtain ⟨g, hg⟩ := exists_map_eq_of_finrank_eq (h.trans hW.symm).symm
    exact ⟨g, hg⟩

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
