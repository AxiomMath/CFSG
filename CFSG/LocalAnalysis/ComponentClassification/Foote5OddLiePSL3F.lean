module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearBlocks

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup Matrix
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

variable {k : Type} [Field k] {n : ℕ}

section Finite

variable [Finite k]

section Three

variable (hk : Nat.card k = 3)
include hk

theorem three_eq_zero_of_card : (3 : k) = 0 := by
  let : Fintype k := Fintype.ofFinite k
  have h := FiniteField.cast_card_eq_zero k
  rw [← Nat.card_eq_fintype_card, hk] at h
  exact_mod_cast h

theorem two_ne_zero_of_card : (2 : k) ≠ 0 := by
  intro h
  have h3 := three_eq_zero_of_card hk
  have : (1 : k) = 0 := by
    calc (1 : k) = 3 - 2 := by norm_num
      _ = 0 := by rw [h3, h, sub_zero]
  exact one_ne_zero this

theorem eq_zero_or_one_or_neg_one (x : k) : x = 0 ∨ x = 1 ∨ x = -1 := by
  classical
  let : Fintype k := Fintype.ofFinite k
  have h2 := two_ne_zero_of_card hk
  have h01 : (0 : k) ≠ 1 := zero_ne_one
  have h0m : (0 : k) ≠ -1 := by
    intro h
    exact one_ne_zero (neg_eq_zero.mp h.symm)
  have h1m : (1 : k) ≠ -1 := by
    intro h
    apply h2
    calc (2 : k) = 1 + 1 := by norm_num
      _ = 0 := by rw [show (1 : k) + 1 = 1 - -1 by ring, ← h, sub_self]
  have hcard : ({0, 1, -1} : Finset k).card = Fintype.card k := by
    rw [Finset.card_insert_of_notMem (by simp [h01, h0m]), Finset.card_pair h1m,
      ← Nat.card_eq_fintype_card, hk]
  have heq := Finset.eq_univ_of_card _ hcard
  have hx : x ∈ ({0, 1, -1} : Finset k) := by rw [heq]; exact Finset.mem_univ x
  simpa using hx

theorem ringEquiv_eq_one (σ : k ≃+* k) : σ = 1 := by
  refine RingEquiv.ext fun x => ?_
  rcases eq_zero_or_one_or_neg_one hk x with rfl | rfl | rfl
  · exact map_zero σ
  · exact map_one σ
  · change σ (-1) = -1
    rw [map_neg, map_one]

theorem unit_mul_self (c : kˣ) : c * c = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  rcases eq_zero_or_one_or_neg_one hk (c : k) with h | h | h
  · exact absurd h c.ne_zero
  · rw [h, one_mul]
  · rw [h]
    ring

theorem center_mul_self {z : SL(n, k)} (hz : z ∈ center SL(n, k)) : z * z = 1 := by
  obtain ⟨r, hrn, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  apply Subtype.ext
  change (z : Matrix (Fin n) (Fin n) k) * z = 1
  rw [← hr]
  rcases eq_zero_or_one_or_neg_one hk r with h | h | h
  · rw [h] at hrn
    rcases Nat.eq_zero_or_pos (Fintype.card (Fin n)) with h0 | h0
    · ext i
      exact absurd i.2 (by simp at h0; omega)
    · rw [zero_pow h0.ne'] at hrn
      exact absurd hrn zero_ne_one
  · rw [h, map_one, one_mul]
  · rw [h, ← map_mul]
    simp

end Three

theorem eq_one_of_mul_self {G : Type*} [Group G] {z : G} (hz : z * z = 1) {m : ℕ} (hm : Odd m)
    (hzm : z ^ m = 1) : z = 1 := by
  obtain ⟨t, rfl⟩ := hm
  have h2 : z ^ 2 = 1 := by rw [sq]; exact hz
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hzm
  exact hzm

theorem isQuasisimple_coordBlockSL_three {J : Finset (Fin n)} (hJ : 3 ≤ J.card) :
    Open.IsQuasisimple (coordBlockSL k J) :=
  Components.quasisimple_of_equiv
    ((MonoidHom.ofInjective (blockSLOn_injective (k := k) J)).trans
      (MulEquiv.subgroupCongr (range_blockSLOn J))).symm
    ((AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CatalogueBGeneralLinear.specialLinear_quasisimple J.card k (by omega)
        (Or.inl (by omega)) (Or.inl (by omega))))

theorem isComponentOf_block_centralizer_three (h2 : (2 : k) ≠ 0) {X : Type} [Group X]
    (Ψ : SL(n, k) →* X) (hker : Ψ.ker ≤ center SL(n, k)) (f : X) (σ : Fin n → Bool)
    (hf : ∀ y, f * Ψ y * f⁻¹ = Ψ (slConjugation n k (signGL k σ) y)) (b : Bool)
    (hcard : 3 ≤ (coordSet σ b).card) :
    Open.IsComponentOf ((coordBlockSL k (coordSet σ b)).map Ψ)
      (Ψ.range ⊓ centralizer ({f} : Set X)) := by
  have hQ : Open.IsComponentOf (coordBlockSL k (coordSet σ b))
      (CFSG.ClassicalInvolution.Balance.fixedGroup (slConjugation n k (signGL k σ))) := by
    have hle : coordBlockSL k (coordSet σ b) ≤
        CFSG.ClassicalInvolution.Balance.fixedGroup (slConjugation n k (signGL k σ)) := by
      intro s hs
      rw [CFSG.ClassicalInvolution.Balance.mem_fixedGroup]
      refine slConjugation_diagGL_fixes_coordBlockSL _ ?_ hs
      intro i hi j hj
      rw [mem_coordSet] at hi hj
      rw [hi, hj]
    refine ⟨hle, CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hle ?_,
      isQuasisimple_coordBlockSL_three hcard⟩
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro s y hs hy
    exact conj_mem_coordBlockSL (compIndicator_comm_of_fixed_signGL h2
      (CFSG.ClassicalInvolution.Balance.mem_fixedGroup.mp hy) b) hs
  have hmain := CFSG.ClassicalInvolution.Balance.isComponentOf_map_centralizer hker 1 f
    (slConjugation n k (signGL k σ)) (fun y => by simpa using hf y) hQ
  have e : (MulAut.conj (1 : SL(n, k))).toMonoidHom = MonoidHom.id _ := by
    ext
    simp
  rwa [e, MonoidHom.comp_id] at hmain

end Finite

@[expose] noncomputable def slFinCongr {a b : ℕ} (h : a = b) : SL(a, k) ≃* SL(b, k) where
  toFun X := ⟨reindexAlgEquiv k k (finCongr h) (X : Matrix (Fin a) (Fin a) k), by
    rw [coe_reindexAlgEquiv, det_reindex_self]
    exact X.2⟩
  invFun X := ⟨reindexAlgEquiv k k (finCongr h.symm) (X : Matrix (Fin b) (Fin b) k), by
    rw [coe_reindexAlgEquiv, det_reindex_self]
    exact X.2⟩
  left_inv X := by
    ext i j
    simp
  right_inv X := by
    ext i j
    simp
  map_mul' X Y := Subtype.ext (map_mul (reindexAlgEquiv k k (finCongr h)) _ _)

theorem slFinCongr_apply {a b : ℕ} (h : a = b) (X : SL(a, k)) (i j : Fin b) :
    ((slFinCongr h X : SL(b, k)) : Matrix (Fin b) (Fin b) k) i j =
      (X : Matrix (Fin a) (Fin a) k) (Fin.cast h.symm i) (Fin.cast h.symm j) := rfl

@[expose] noncomputable def blockTwo (J : Finset (Fin n)) (hJ : J.card = 2) :
    SL(2, k) →* SL(n, k) :=
  (blockSLOn k J).comp (slFinCongr hJ.symm).toMonoidHom

theorem blockTwo_injective (J : Finset (Fin n)) (hJ : J.card = 2) :
    Function.Injective (blockTwo (k := k) J hJ) :=
  (blockSLOn_injective J).comp (slFinCongr hJ.symm).injective

theorem range_blockTwo (J : Finset (Fin n)) (hJ : J.card = 2) :
    (blockTwo (k := k) J hJ).range = coordBlockSL k J := by
  rw [blockTwo, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
    (slFinCongr hJ.symm).surjective, ← MonoidHom.range_eq_map, range_blockSLOn]

@[expose] noncomputable def blockPt (J : Finset (Fin n)) (hJ : J.card = 2) (a : Fin 2) :
    Fin n :=
  (J.equivFin.symm (Fin.cast hJ.symm a)).1

theorem blockPt_mem (J : Finset (Fin n)) (hJ : J.card = 2) (a : Fin 2) :
    blockPt J hJ a ∈ J :=
  (J.equivFin.symm (Fin.cast hJ.symm a)).2

theorem blockPt_injective (J : Finset (Fin n)) (hJ : J.card = 2) :
    Function.Injective (blockPt J hJ) := by
  intro a b h
  have h1 : J.equivFin.symm (Fin.cast hJ.symm a) = J.equivFin.symm (Fin.cast hJ.symm b) :=
    Subtype.ext h
  have h2 := J.equivFin.symm.injective h1
  exact Fin.cast_injective _ h2

theorem eq_blockPt_of_mem (J : Finset (Fin n)) (hJ : J.card = 2) {c : Fin n} (hc : c ∈ J) :
    c = blockPt J hJ 0 ∨ c = blockPt J hJ 1 := by
  have hca : c = blockPt J hJ (Fin.cast hJ (J.equivFin ⟨c, hc⟩)) := by
    simp [blockPt]
  have h2 : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  rcases h2 (Fin.cast hJ (J.equivFin ⟨c, hc⟩)) with h | h
  · left
    calc c = blockPt J hJ (Fin.cast hJ (J.equivFin ⟨c, hc⟩)) := hca
      _ = blockPt J hJ 0 := by rw [h]
  · right
    calc c = blockPt J hJ (Fin.cast hJ (J.equivFin ⟨c, hc⟩)) := hca
      _ = blockPt J hJ 1 := by rw [h]

theorem blockTwo_apply_pt (J : Finset (Fin n)) (hJ : J.card = 2) (X : SL(2, k)) (a b : Fin 2) :
    ((blockTwo J hJ X : SL(n, k)) : Matrix (Fin n) (Fin n) k) (blockPt J hJ a) (blockPt J hJ b) =
      (X : Matrix (Fin 2) (Fin 2) k) a b := by
  change blockOn k J _ _ _ = _
  rw [blockOn_apply_mem J _ (blockPt_mem J hJ a) (blockPt_mem J hJ b)]
  change ((slFinCongr hJ.symm X : SL(J.card, k)) : Matrix (Fin J.card) (Fin J.card) k) _ _ = _
  rw [slFinCongr_apply]
  simp [blockPt]

theorem blockTwo_apply_not_mem (J : Finset (Fin n)) (hJ : J.card = 2) (X : SL(2, k))
    {c d : Fin n} (hcd : c ∉ J ∨ d ∉ J) :
    ((blockTwo J hJ X : SL(n, k)) : Matrix (Fin n) (Fin n) k) c d = if c = d then 1 else 0 :=
  blockOn_apply_not_mem J _ hcd

end CFSG.ComponentClassification.Foote5.OddLieCore
