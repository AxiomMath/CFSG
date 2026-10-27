module

public import CFSG.Quasithin.H13.L32NKGSp6S0
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.KC.Sp6N

open CFSG.KGroups.Sp6 CFSG.Quasithin.H13 CFSG.Quasithin.H13.KGSp6 CFSG.Open Matrix

@[expose] def eF : Fin 6 ≃ Fin 3 ⊕ Fin 3 := (finSumFinEquiv (m := 3) (n := 3)).symm

@[expose] noncomputable def psi : Mat6ˣ ≃* GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) eF).toMulEquiv

theorem psi_val (u : Mat6ˣ) :
    ((psi u : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) =
      (u : Mat6).submatrix eF.symm eF.symm := rfl

theorem jstd_eq : (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) =
    KGCert.g22Form.submatrix eF.symm eF.symm := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> decide

theorem isIso_iff (M : Mat6) : IsIso M ↔ (M.submatrix eF.symm eF.symm)ᵀ *
    fromBlocks 0 1 (-1) 0 * M.submatrix eF.symm eF.symm = fromBlocks 0 1 (-1) 0 := by
  rw [jstd_eq, transpose_submatrix, submatrix_mul_equiv _ _ _ eF.symm _,
    submatrix_mul_equiv _ _ _ eF.symm _]
  unfold IsIso
  constructor
  · intro h
    rw [h]
  · intro h
    ext i j
    have := congrFun (congrFun h (eF i)) (eF j)
    simpa using this

theorem card_SpU_eq_sp : Nat.card SpU = Nat.card (StatedSp 3 (ZMod 2)) := by
  have hmap : SpU.map psi.toMonoidHom = StatedSp 3 (ZMod 2) := by
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [StatedAPI.mem_statedSp_iff]
      exact (isIso_iff _).1 hu
    · intro hg
      have hmem : psi.symm g ∈ SpU := by
        rw [mem_SpU, isIso_iff, ← psi_val, MulEquiv.apply_symm_apply]
        exact StatedAPI.mem_statedSp_iff.1 hg
      exact ⟨psi.symm g, hmem, by simp⟩
  rw [← hmap]
  exact Nat.card_congr (SpU.equivMapOfInjective _ psi.injective).toEquiv

theorem spLeaves_length : (spLeaves 64).length = 1451520 := by
  rw [← card_SpU_eq, card_SpU_eq_sp,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod,
    show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.prod_insert (by norm_num),
    Finset.prod_pair (by norm_num)]
  norm_num

theorem countCheck_ok : countCheck 64 1451520 = true := by
  have h : spCount 64 (fun _ => true) = 1451520 := by
    rw [spCount_eq, List.countP_true, spLeaves_length]
  rw [countCheck.eq_1]
  exact beq_iff_eq.2 h

@[expose] def Bc : List ℕ := [1, 16, 4, 28, 11, 34]

@[expose] def Bi : List ℕ := [1, 31, 4, 14, 2, 63]

@[expose] def candN (k w : ℕ) : List ℕ :=
  (List.range 6).map fun i => mulVecC (powC (powC s0 (k + 1)) i) w

@[expose] def leafB : List ℕ → Bool
  | [c0, c1, c2, c3, c4, c5] => cand1 c0 c1 && cand2 c0 c1 c2 && cand3 c0 c1 c2 c3 &&
      cand4 c0 c1 c2 c3 c4 && cand5 c0 c1 c2 c3 c4 c5
  | _ => false

@[expose] def normBN (N : List (List ℕ)) : Bool :=
  (List.range 6).all fun k => (List.range 64).all fun w =>
    N.contains (mulC (candN k w) Bi) || !leafB (mulC (candN k w) Bi) ||
      !(mulC (mulC (candN k w) Bi) s0 == mulC (powC s0 (k + 1)) (mulC (candN k w) Bi))

@[expose] def normB : Bool := normBN n0List

theorem leafB_of_mem {x : List ℕ} (hx : x ∈ spLeaves 64) : leafB x = true := by
  obtain ⟨c0, c1, c2, c3, c4, c5, rfl, -, -, -, h1, -, h2, -, h3, -, h4, -, h5⟩ :=
    mem_spLeaves.1 hx
  simp [leafB, h1, h2, h3, h4, h5]

theorem Bc_eq : Bc = (List.range 6).map fun i => mulVecC (powC s0 i) 1 := by decide

theorem Bc_Bi : mulC Bc Bi = oneC := by decide

theorem validC_Bi : KGCert.ValidC Bi := by
  unfold KGCert.ValidC Bi
  decide

theorem getD_map_range (f : ℕ → ℕ) (j : Fin 6) :
    ((List.range 6).map f).getD j 0 = f j := by
  fin_cases j <;> rfl

theorem decodeC_apply (A : List ℕ) (i j : Fin 6) :
    KGCert.decodeC A i j = KGCert.vec6 (A.getD j 0) i := rfl

theorem mul_decodeC_apply (A B : List ℕ) (i j : Fin 6) :
    (KGCert.decodeC A * KGCert.decodeC B) i j =
      (KGCert.decodeC A *ᵥ KGCert.vec6 (B.getD j 0)) i := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, decodeC_apply]

theorem validC_candN (k w : ℕ) : KGCert.ValidC (candN k w) := by
  refine ⟨by simp [candN], fun c hc => ?_⟩
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact KGCert.mulVecC_lt (validC_powC (validC_powC validC_s0 _) i) w

theorem eq_cand {x : List ℕ} (hx : KGCert.ValidC x) {k : ℕ}
    (h : mulC x s0 = mulC (powC s0 (k + 1)) x) : mulC (candN k (mulVecC x 1)) Bi = x := by
  have h' : KGCert.mulC x s0 = KGCert.mulC (powC s0 (k + 1)) x := h
  have hXS : KGCert.decodeC x * KGCert.decodeC s0 =
      KGCert.decodeC (powC s0 (k + 1)) * KGCert.decodeC x := by
    have := congrArg KGCert.decodeC h'
    rwa [KGCert.decodeC_mulC _ _ validC_s0.1, KGCert.decodeC_mulC _ _ hx.1] at this
  have hsc : ∀ i : ℕ, KGCert.decodeC x * KGCert.decodeC s0 ^ i =
      KGCert.decodeC (powC s0 (k + 1)) ^ i * KGCert.decodeC x :=
    fun i => (SemiconjBy.pow_right hXS i).eq
  have hcol : KGCert.decodeC (candN k (mulVecC x 1)) = KGCert.decodeC x * KGCert.decodeC Bc := by
    ext i j
    rw [mul_decodeC_apply, decodeC_apply, candN, getD_map_range, Bc_eq, getD_map_range,
      mulVecC_eq, ← KGCert.decodeC_mulVec, ← KGCert.decodeC_mulVec, ← KGCert.decodeC_mulVec,
      decodeC_powC (validC_powC validC_s0 _), decodeC_powC validC_s0 (j : ℕ),
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hsc]
  have hval : KGCert.ValidC (KGCert.mulC (candN k (mulVecC x 1)) Bi) :=
    KGCert.validC_mulC (validC_candN _ _) validC_Bi
  have hB : KGCert.decodeC Bc * KGCert.decodeC Bi = 1 := by
    have e : KGCert.mulC Bc Bi = KGCert.oneC := Bc_Bi
    rw [← KGCert.decodeC_mulC _ _ validC_Bi.1, e, KGCert.decodeC_oneC]
  apply KGCert.decodeC_injOn hval hx
  rw [KGCert.decodeC_mulC _ _ validC_Bi.1, hcol, Matrix.mul_assoc, hB, Matrix.mul_one]

theorem normCheck_of (hB : normB = true) : normCheck 64 s0 n0List = true := by
  have h' : spCount 64 (fun x => ((List.range 6).map fun k => powC s0 (k + 1)).any
      (fun p => mulC x s0 == mulC p x) && !n0List.contains x) = 0 := by
    rw [spCount_eq, List.countP_eq_zero]
    intro x hx hP
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, List.mem_map,
      List.mem_range, beq_iff_eq] at hP
    obtain ⟨⟨p, ⟨k, hk, rfl⟩, hxp⟩, hN⟩ := hP
    have hv := (mem_spLeaves_iff.1 hx).1
    have he := eq_cand hv hxp
    simp only [normB, normBN, List.all_eq_true, List.mem_range] at hB
    have h1 := hB k hk (mulVecC x 1) (KGCert.mulVecC_lt hv 1)
    rw [he, hN, leafB_of_mem hx, hxp] at h1
    simp at h1
  rw [normCheck.eq_1]
  exact beq_iff_eq.2 h'

end CFSG.KC.Sp6N

end
