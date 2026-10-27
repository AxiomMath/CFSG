module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParModelCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParD

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix

abbrev Mat16 : Type := Matrix (Fin 16) (Fin 16) (ZMod 2)

@[expose] def blk16 (A C : Mat8) : Mat16 :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A C 0 A)

theorem blk16_mul (A C A' C' : Mat8) :
    blk16 A C * blk16 A' C' = blk16 (A * A') (A * C' + C * A') := by
  simp only [blk16, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem blk16_one : blk16 1 0 = 1 := by
  rw [blk16, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

@[expose] def rhoM (A : Mat8) : Mat16 := blk16 A 0

@[expose] def tM16 : Mat16 := blk16 1 1

theorem rhoM_mul (A B : Mat8) : rhoM (A * B) = rhoM A * rhoM B := by
  simp [rhoM, blk16_mul]

theorem rhoM_one : rhoM 1 = 1 := blk16_one

theorem tM16_mul_tM16 : tM16 * tM16 = 1 := by
  rw [tM16, blk16_mul, mul_one, CharTwo.add_self_eq_zero, blk16_one]

theorem blk16_castAdd_castAdd (A C : Mat8) (i j : Fin 8) :
    blk16 A C (Fin.castAdd 8 i) (Fin.castAdd 8 j) = A i j := by
  simp only [blk16, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    fromBlocks_apply₁₁]

theorem blk16_castAdd_natAdd (A C : Mat8) (i j : Fin 8) :
    blk16 A C (Fin.castAdd 8 i) (Fin.natAdd 8 j) = C i j := by
  simp only [blk16, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂]

theorem blk16_natAdd_castAdd (A C : Mat8) (i j : Fin 8) :
    blk16 A C (Fin.natAdd 8 i) (Fin.castAdd 8 j) = 0 := by
  simp only [blk16, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₁, Matrix.zero_apply]

theorem blk16_natAdd_natAdd (A C : Mat8) (i j : Fin 8) :
    blk16 A C (Fin.natAdd 8 i) (Fin.natAdd 8 j) = A i j := by
  simp only [blk16, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    fromBlocks_apply₂₂]

@[expose] def embedM (ψ : Mat8) : Mat16 :=
  Matrix.of fun r c => if (inW0 r && inW1 c) = true then entry ψ (posW0 r) (posW1 c) else 0

theorem inW0_or_inW1 (r : Fin 16) : inW0 r = true ∨ inW1 r = true := by
  revert r; decide

theorem not_inW0_and_inW1 (r : Fin 16) : ¬ (inW0 r = true ∧ inW1 r = true) := by
  revert r; decide

theorem embedM_mul_embedM (ψ ψ' : Mat8) : embedM ψ * embedM ψ' = 0 := by
  ext r c
  rw [mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [embedM, Matrix.of_apply]
  rcases inW0_or_inW1 k with h | h
  · have : inW1 k = false := by
      cases h' : inW1 k
      · rfl
      · exact absurd ⟨h, h'⟩ (not_inW0_and_inW1 k)
    simp [this]
  · have : inW0 k = false := by
      cases h' : inW0 k
      · rfl
      · exact absurd ⟨h', h⟩ (not_inW0_and_inW1 k)
    simp [this]

theorem embedM_add (ψ ψ' : Mat8) : embedM (ψ + ψ') = embedM ψ + embedM ψ' := by
  ext r c
  simp only [embedM, Matrix.of_apply, Matrix.add_apply, entry_add]
  split_ifs <;> simp

theorem embedM_smul (a : ZMod 2) (ψ : Mat8) : embedM (a • ψ) = a • embedM ψ := by
  ext r c
  simp only [embedM, Matrix.of_apply, Matrix.smul_apply, entry_smul, smul_eq_mul]
  split_ifs <;> simp

theorem embedM_zero : embedM 0 = 0 := by
  ext r c
  simp [embedM, entry]

@[expose] def w0idx (a : Fin 8) : Fin 16 := if (a : ℕ) < 4 then ⟨a, by omega⟩ else ⟨a + 4, by omega⟩

@[expose] def w1idx (b : Fin 8) : Fin 16 :=
  if (b : ℕ) < 4 then ⟨b + 4, by omega⟩ else ⟨b + 8, by omega⟩

@[expose] def blockOf (N : Mat16) : Mat8 := Matrix.of fun a b => N (w0idx a) (w1idx b)

theorem w0idx_spec (a : Fin 8) : inW0 (w0idx a) = true ∧ posW0 (w0idx a) = a := by
  revert a; decide

theorem w1idx_spec (b : Fin 8) : inW1 (w1idx b) = true ∧ posW1 (w1idx b) = b := by
  revert b; decide

theorem blockOf_embedM (ψ : Mat8) : blockOf (embedM ψ) = ψ := by
  ext a b
  simp only [blockOf, embedM, Matrix.of_apply, (w0idx_spec a).1, (w1idx_spec b).1, Bool.and_self,
    ite_true, (w0idx_spec a).2, (w1idx_spec b).2]
  rw [entry, dite_eq_left ⟨a.isLt, b.isLt⟩]

theorem w0idx_posW0 (r : Fin 16) (h : inW0 r = true) :
    w0idx ⟨posW0 r, by revert r; decide⟩ = r := by
  revert r h; decide

theorem w1idx_posW1 (c : Fin 16) (h : inW1 c = true) :
    w1idx ⟨posW1 c, by revert c; decide⟩ = c := by
  revert c h; decide

theorem eq_embedM_blockOf (N : Mat16) (h0 : ∀ r c : Fin 16, inW0 c = true → N r c = 0)
    (h1 : ∀ r c : Fin 16, inW1 r = true → N r c = 0) : N = embedM (blockOf N) := by
  ext r c
  simp only [embedM, Matrix.of_apply]
  split_ifs with h
  · rw [Bool.and_eq_true] at h
    rw [entry, dite_eq_left ⟨by revert r; decide +revert, by revert c; decide +revert⟩]
    simp only [blockOf, Matrix.of_apply]
    rw [w0idx_posW0 r h.1, w1idx_posW1 c h.2]
  · rw [Bool.and_eq_true] at h
    rcases inW0_or_inW1 r with hr | hr
    · rcases inW0_or_inW1 c with hc | hc
      · exact h0 r c hc
      · exact absurd ⟨hr, hc⟩ h
    · exact h1 r c hr

theorem testBit_mod256 (a j : ℕ) (hj : j < 8) : (a % 256).testBit j = a.testBit j := by
  rw [show (256 : ℕ) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow]
  simp [hj]

theorem testBit_mod256_high (a j : ℕ) : (a % 256).testBit (j + 8) = false := by
  apply Nat.testBit_eq_false_of_lt
  calc a % 256 < 256 := Nat.mod_lt _ (by norm_num)
    _ ≤ 2 ^ (j + 8) := by
      rw [pow_add]; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos j)

theorem toMat_rho16 (A : Array ℕ) : toMat 16 16 (rho16 A) = rhoM (toMat 8 8 A) := by
  ext r c
  refine Fin.addCases (m := 8) (n := 8) (fun i => ?_) (fun i => ?_) r <;>
    refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) c
  · rw [rhoM, blk16_castAdd_castAdd, toMat_apply, toMat_apply, rho16, getD_ofFn]
    simp [testBit_mod256 _ _ j.isLt]
  · rw [rhoM, blk16_castAdd_natAdd, toMat_apply, rho16, getD_ofFn]
    simp [testBit_mod256_high]
  · rw [rhoM, blk16_natAdd_castAdd, toMat_apply, rho16, getD_ofFn]
    have : ¬ (8 ≤ (j : ℕ)) := by omega
    simp [Nat.testBit_shiftLeft, this]
  · rw [rhoM, blk16_natAdd_natAdd, toMat_apply, toMat_apply, rho16, getD_ofFn]
    simp [Nat.testBit_shiftLeft, testBit_mod256 _ _ j.isLt]

theorem toMat_id16 : toMat 16 16 id16 = 1 := by
  ext r c
  rw [toMat_apply, id16, getD_ofFn, Nat.testBit_two_pow, one_apply]
  by_cases h : r = c
  · subst h; simp
  · have : (r : ℕ) ≠ c := Fin.val_ne_of_ne h
    simp [h, this]

theorem toMat_embed16 (ψ : Array ℕ) : toMat 16 16 (embed16 ψ) = embedM (toMat 8 8 ψ) := by
  ext r c
  rw [toMat_apply, embed16, getD_ofFn, testBit_bitsOf]
  simp only [c.isLt, decide_true, Bool.true_and, embedM, Matrix.of_apply]
  split_ifs with h
  · rw [h, entry_toMat _ (by revert r c; decide +revert) (by revert r c; decide +revert)]
    simp
  · simp only [Bool.not_eq_true] at h
    simp [h]

theorem toMat_wordBits (w : List (Fin 3)) : toMat 8 8 (wordBits w) = (w.map genMat).prod := by
  induction w with
  | nil => exact toMat_id8
  | cons s w ih => rw [wordBits, toMat_bmul, ih]; rfl

theorem prod_eq_one_of_mem_h1Rels {w : List (Fin 3)} (hw : w ∈ h1Rels) :
    (w.map genMat).prod = 1 := by
  have h := relCheck_eq_true
  rw [relCheck, List.all_eq_true] at h
  rw [← toMat_wordBits, toMat_eq_one_of_bIsId (h w hw)]

theorem genMat_zero_mul_self : genMat 0 * genMat 0 = 1 := by
  have := prod_eq_one_of_mem_h1Rels (w := [0, 0]) (by simp [h1Rels])
  simpa using this

theorem genMat_one_mul_two : genMat 1 * genMat 2 = 1 := by
  have := prod_eq_one_of_mem_h1Rels (w := [1, 2]) (by simp [h1Rels])
  simpa using this

theorem genMat_two_mul_one : genMat 2 * genMat 1 = 1 :=
  (mul_eq_one_comm_of_card_eq (Fin 8) (Fin 8) (ZMod 2) rfl).mp genMat_one_mul_two

@[expose] noncomputable def genGL : Fin 3 → GL (Fin 8) (ZMod 2)
  | 0 => ⟨genMat 0, genMat 0, genMat_zero_mul_self, genMat_zero_mul_self⟩
  | 1 => ⟨genMat 1, genMat 2, genMat_one_mul_two, genMat_two_mul_one⟩
  | 2 => ⟨genMat 2, genMat 1, genMat_two_mul_one, genMat_one_mul_two⟩

theorem coe_genGL (s : Fin 3) : (genGL s : Mat8) = genMat s := by
  fin_cases s <;> rfl

theorem genGL_two : genGL 2 = (genGL 1)⁻¹ := by
  ext1; rfl

@[expose] noncomputable def SU42b : Subgroup (GL (Fin 8) (ZMod 2)) :=
  Subgroup.closure {genGL 0, genGL 1}

theorem genGL_mem (s : Fin 3) : genGL s ∈ SU42b := by
  fin_cases s
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · change genGL 2 ∈ SU42b
    rw [genGL_two]
    exact inv_mem (Subgroup.subset_closure (by simp))

@[expose] noncomputable def wordGL (w : List (Fin 3)) : GL (Fin 8) (ZMod 2) := (w.map genGL).prod

theorem wordGL_mem (w : List (Fin 3)) : wordGL w ∈ SU42b := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp hg
  exact genGL_mem s

theorem coe_wordGL (w : List (Fin 3)) : (wordGL w : Mat8) = toMat 8 8 (wordBits w) := by
  induction w with
  | nil => exact toMat_id8.symm
  | cons s w ih => rw [wordGL, List.map_cons, List.prod_cons, Units.val_mul, ← wordGL, ih,
      coe_genGL, wordBits, toMat_bmul]; rfl

theorem wordGL_eq_one_of_mem {w : List (Fin 3)} (hw : w ∈ h1Rels) : wordGL w = 1 := by
  ext1
  rw [coe_wordGL, toMat_wordBits, prod_eq_one_of_mem_h1Rels hw, Units.val_one]

theorem wordCheck_spec :
    (∀ m < 4, toMat 8 8 (wordBits (eWord m)) = toMat 8 8 (eBits m)) ∧
      ∀ j < 2, toMat 8 8 (wordBits (nuWord j)) = toMat 8 8 (nuBits j) ∧
        toMat 8 8 (wordBits (nuInvWord j)) = toMat 8 8 (nuInvBits j) ∧
        toMat 8 8 (nuBits j) * toMat 8 8 (nuInvBits j) = 1 := by
  have h := wordCheck_eq_true
  simp only [wordCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ⟨fun m hm => by rw [h.1 m hm], fun j hj => ⟨by rw [(h.2 j hj).1.1], by rw [(h.2 j hj).1.2],
    by rw [← toMat_bmul, toMat_eq_one_of_bIsId (h.2 j hj).2]⟩⟩

theorem toMat_unitBits (a b : Fin 8) : toMat 8 8 (unitBits a b) = Matrix.single a b 1 := by
  ext r c
  rw [toMat_apply, unitBits, getD_ofFn, Matrix.single_apply]
  by_cases hr : r = a
  · subst hr
    by_cases hc : b = c
    · subst hc; simp
    · have : (b : ℕ) ≠ c := Fin.val_ne_of_ne hc
      simp [hc, this]
  · have : (r : ℕ) ≠ a := Fin.val_ne_of_ne hr
    simp [this, Ne.symm hr]

theorem linearMap_ext_single {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    {f g : Mat8 →ₗ[ZMod 2] M} (h : ∀ a b : Fin 8, f (Matrix.single a b 1) = g (Matrix.single a b 1)) :
    f = g := by
  ext ψ
  rw [Matrix.matrix_eq_sum_single ψ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e : Matrix.single a b (ψ a b) = ψ a b • Matrix.single a b 1 := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e, map_smul, map_smul, h]

@[expose] def embedLin : Mat8 →ₗ[ZMod 2] Mat16 where
  toFun := embedM
  map_add' := embedM_add
  map_smul' := embedM_smul

theorem embedCheck_spec :
    (∀ m < 4, rhoM (toMat 8 8 (eBits m)) = 1 + embedM (aM m)) ∧
    (∀ a b : Fin 8, ∀ j < 2, rhoM (toMat 8 8 (nuBits j)) * embedM (Matrix.single a b 1) *
        rhoM (toMat 8 8 (nuInvBits j)) = embedM (n0M j * Matrix.single a b 1 * n1M j)) ∧
    (∀ a b : Fin 8, toMat 16 16 tBits16 * embedM (Matrix.single a b 1) * toMat 16 16 tBits16 =
        embedM (tM * Matrix.single a b 1 * tM)) ∧
    ∀ j < 2, tM * n0M j = n0M j * tM ∧ tM * n1M j = n1M j * tM := by
  have h := embedCheck_eq_true
  simp only [embedCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun m hm => ?_, fun a b j hj => ?_, fun a b => ?_, fun j hj => ?_⟩
  · have := congrArg (toMat 16 16) (h1 m hm)
    rwa [toMat_rho16, toMat_bxor, toMat_id16, toMat_embed16] at this
  · have := congrArg (toMat 16 16) ((h2 a a.isLt b b.isLt).1 j hj)
    simp only [toMat_bmul, toMat_rho16, toMat_embed16, toMat_unitBits] at this
    exact this
  · have := congrArg (toMat 16 16) (h2 a a.isLt b b.isLt).2
    simp only [toMat_bmul, toMat_embed16, toMat_unitBits] at this
    exact this
  · obtain ⟨e1, e2⟩ := h3 j hj
    have f1 := congrArg (toMat 8 8) e1
    have f2 := congrArg (toMat 8 8) e2
    rw [toMat_bmul, toMat_bmul] at f1 f2
    exact ⟨f1, f2⟩

@[expose] def sandLin (P Q : Mat16) : Mat8 →ₗ[ZMod 2] Mat16 where
  toFun ψ := P * embedM ψ * Q
  map_add' ψ ψ' := by rw [embedM_add, mul_add, add_mul]
  map_smul' c ψ := by rw [embedM_smul, mul_smul_comm, smul_mul_assoc]; rfl

@[expose] def sandLin8 (P Q : Mat8) : Mat8 →ₗ[ZMod 2] Mat8 where
  toFun ψ := P * ψ * Q
  map_add' ψ ψ' := by rw [mul_add, add_mul]
  map_smul' c ψ := by rw [mul_smul_comm, smul_mul_assoc]; rfl

theorem rhoM_nu_embedM (j : ℕ) (hj : j < 2) (ψ : Mat8) :
    rhoM (toMat 8 8 (nuBits j)) * embedM ψ * rhoM (toMat 8 8 (nuInvBits j)) =
      embedM (n0M j * ψ * n1M j) := by
  have := linearMap_ext_single (f := sandLin (rhoM (toMat 8 8 (nuBits j)))
    (rhoM (toMat 8 8 (nuInvBits j)))) (g := embedLin.comp (sandLin8 (n0M j) (n1M j)))
    fun a b => by
      simp only [sandLin, embedLin, sandLin8, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.comp_apply]
      exact embedCheck_spec.2.1 a b j hj
  have h2 := LinearMap.congr_fun this ψ
  simp only [sandLin, embedLin, sandLin8, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.comp_apply] at h2
  exact h2

theorem toMat_blk16Bits (A C : Array ℕ) :
    toMat 16 16 (blk16Bits A C) = blk16 (toMat 8 8 A) (toMat 8 8 C) := by
  ext r c
  refine Fin.addCases (m := 8) (n := 8) (fun i => ?_) (fun i => ?_) r <;>
    refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) c
  · rw [blk16_castAdd_castAdd, toMat_apply, toMat_apply, blk16Bits, getD_ofFn]
    have : ¬ (8 ≤ (j : ℕ)) := by omega
    simp [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_mod256 _ _ j.isLt, this]
  · rw [blk16_castAdd_natAdd, toMat_apply, toMat_apply, blk16Bits, getD_ofFn]
    simp [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_mod256_high, testBit_mod256 _ _ j.isLt]
  · rw [blk16_natAdd_castAdd, toMat_apply, blk16Bits, getD_ofFn]
    have : ¬ (8 ≤ (j : ℕ)) := by omega
    simp [Nat.testBit_shiftLeft, this]
  · rw [blk16_natAdd_natAdd, toMat_apply, toMat_apply, blk16Bits, getD_ofFn]
    simp [Nat.testBit_shiftLeft, testBit_mod256 _ _ j.isLt]

theorem toMat_tBits16 : toMat 16 16 tBits16 = tM16 := by
  rw [tBits16, toMat_blk16Bits, toMat_id8]; rfl

theorem tM16_embedM (ψ : Mat8) : tM16 * embedM ψ * tM16 = embedM (tM * ψ * tM) := by
  have := linearMap_ext_single (f := sandLin tM16 tM16) (g := embedLin.comp (sandLin8 tM tM))
    fun a b => by
      have := embedCheck_spec.2.2.1 a b
      rw [toMat_tBits16] at this
      simp only [sandLin, embedLin, sandLin8, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.comp_apply]
      exact this
  have h2 := LinearMap.congr_fun this ψ
  simp only [sandLin, embedLin, sandLin8, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.comp_apply] at h2
  exact h2

theorem blk16_mulVec_append (A C : Mat8) (u v : Fin 8 → ZMod 2) :
    blk16 A C *ᵥ Fin.append u v = Fin.append (A *ᵥ u + C *ᵥ v) (A *ᵥ v) := by
  ext r
  refine Fin.addCases (m := 8) (n := 8) (fun i => ?_) (fun i => ?_) r
  · rw [Fin.append_left, mulVec, dotProduct]
    rw [Fin.sum_univ_add (a := 8) (b := 8)
      (fun x => blk16 A C (Fin.castAdd 8 i) x * Fin.append u v x)]
    simp only [blk16_castAdd_castAdd, blk16_castAdd_natAdd, Fin.append_left, Fin.append_right,
      Pi.add_apply, mulVec, dotProduct]
  · rw [Fin.append_right, mulVec, dotProduct]
    rw [Fin.sum_univ_add (a := 8) (b := 8)
      (fun x => blk16 A C (Fin.natAdd 8 i) x * Fin.append u v x)]
    simp only [blk16_natAdd_castAdd, blk16_natAdd_natAdd, Fin.append_left, Fin.append_right,
      zero_mul, Finset.sum_const_zero, zero_add, mulVec, dotProduct]

theorem append_single_castAdd (j : Fin 8) :
    (Pi.single (Fin.castAdd 8 j) 1 : Fin 16 → ZMod 2) =
      Fin.append (Pi.single j (1 : ZMod 2)) (0 : Fin 8 → ZMod 2) := by
  ext r
  refine Fin.addCases (m := 8) (n := 8) (fun i => ?_) (fun i => ?_) r
  · rw [Fin.append_left]
    by_cases h : i = j
    · subst h; simp
    · rw [Pi.single_eq_of_ne h]
      exact Pi.single_eq_of_ne (fun e => h (Fin.castAdd_injective _ _ e)) _
  · rw [Fin.append_right, Pi.zero_apply, Pi.single_eq_of_ne]
    intro e
    have := congrArg Fin.val e
    simp at this; omega

theorem append_single_natAdd (j : Fin 8) :
    (Pi.single (Fin.natAdd 8 j) 1 : Fin 16 → ZMod 2) =
      Fin.append (0 : Fin 8 → ZMod 2) (Pi.single j (1 : ZMod 2)) := by
  ext r
  refine Fin.addCases (m := 8) (n := 8) (fun i => ?_) (fun i => ?_) r
  · rw [Fin.append_left, Pi.zero_apply, Pi.single_eq_of_ne]
    intro e
    have := congrArg Fin.val e
    simp at this; omega
  · rw [Fin.append_right]
    by_cases h : i = j
    · subst h; simp
    · rw [Pi.single_eq_of_ne h]
      exact Pi.single_eq_of_ne (fun e => h (Fin.natAdd_injective _ _ e)) _

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
