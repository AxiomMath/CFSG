module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Derivation
public import CFSG.LieType.SpecialLinear.ExteriorModel.Cyclic
public import CFSG.LieType.Universal.SpecialLinear

public section

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open Matrix

variable {k : Type} [Field k] {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]

@[expose] def bdeg (ε : τ → Finset (Fin n)) (p : τ × Fin n) : ℕ :=
  if p.2 ∈ ε p.1 then (p.2 : ℕ) else 0

omit [Fintype τ] [DecidableEq τ] in
theorem bdeg_le (ε : τ → Finset (Fin n)) (p : τ × Fin n) : bdeg ε p ≤ n := by
  unfold bdeg
  split_ifs
  · exact p.2.isLt.le
  · exact Nat.zero_le n

abbrev BIdx (ε : τ → Finset (Fin n)) : Type _ := KIdx n (bdeg ε)

@[expose] def btop (ε : τ → Finset (Fin n)) : BIdx ε := ktop (bdeg_le ε)

@[expose] noncomputable def bvec (ε : τ → Finset (Fin n)) : BIdx ε → k := Pi.single (btop ε) 1

@[expose] noncomputable def bDer (ε : τ → Finset (Fin n)) (x : τ × Fin n × Fin n) :
    Matrix (BIdx ε) (BIdx ε) k :=
  kronDer (fun p : τ × Fin n => p.1 = x.1) (Matrix.single x.2.1 x.2.2 1)

@[expose] noncomputable def bCyc (ε : τ → Finset (Fin n)) : Submodule k (BIdx ε → k) :=
  cyclicSub (bDer ε) (bvec ε)

@[expose] noncomputable def bRad (ε : τ → Finset (Fin n)) : Submodule k (BIdx ε → k) :=
  dotRad (bCyc (k := k) ε)

abbrev BModel (k : Type) [Field k] (ε : τ → Finset (Fin n)) : Type _ :=
  ↥(bCyc (k := k) ε) ⧸ (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype

@[expose] noncomputable def bMat (ε : τ → Finset (Fin n)) (h : τ → Matrix (Fin n) (Fin n) k) :
    Matrix (BIdx ε) (BIdx ε) k :=
  kronMinor (fun p : τ × Fin n => h p.1)

theorem bMat_mul (ε : τ → Finset (Fin n)) (g h : τ → Matrix (Fin n) (Fin n) k) :
    bMat ε (fun r => g r * h r) = bMat ε g * bMat ε h :=
  kronMinor_mul (fun p : τ × Fin n => g p.1) (fun p => h p.1)

omit [DecidableEq τ] in
theorem bMat_one (ε : τ → Finset (Fin n)) : bMat ε (fun _ => (1 : Matrix (Fin n) (Fin n) k)) = 1 :=
  kronMinor_one

omit [DecidableEq τ] in
theorem bMat_transpose (ε : τ → Finset (Fin n)) (h : τ → Matrix (Fin n) (Fin n) k) :
    bMat ε (fun r => (h r)ᵀ) = (bMat ε h)ᵀ :=
  kronMinor_transpose (fun p : τ × Fin n => h p.1)

theorem bvec_mem_bCyc (ε : τ → Finset (Fin n)) : bvec ε ∈ bCyc (k := k) ε :=
  mem_cyclicSub_self _ _

theorem bvec_dotProduct_bvec (ε : τ → Finset (Fin n)) : bvec (k := k) ε ⬝ᵥ bvec ε = 1 := by
  rw [bvec, dotProduct_single, Pi.single_eq_same, mul_one]

theorem bvec_notMem_bRad (ε : τ → Finset (Fin n)) : bvec (k := k) ε ∉ bRad ε := fun h =>
  one_ne_zero ((bvec_dotProduct_bvec ε).symm.trans
    ((mem_dotRad.mp (show bvec ε ∈ dotRad (bCyc (k := k) ε) from h)).2 _ (bvec_mem_bCyc ε)))

theorem bDer_mk (ε : τ → Finset (Fin n)) (r : τ) (a b : Fin n) :
    bDer (k := k) ε (r, a, b) =
      kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (Matrix.single a b 1) :=
  rfl

theorem bDer_transpose (ε : τ → Finset (Fin n)) (r : τ) (a b : Fin n) :
    (bDer (k := k) ε (r, a, b))ᵀ = bDer ε (r, b, a) := by
  rw [bDer_mk, bDer_mk, ← kronDer_transpose, Matrix.transpose_single]

theorem kronDer_mem_span_bDer (ε : τ → Finset (Fin n)) (r : τ) (Z : Matrix (Fin n) (Fin n) k) :
    kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) Z ∈
      Submodule.span k (Set.range (bDer (k := k) ε)) := by
  have hZ : Z = ∑ a, ∑ b, Z a b • Matrix.single a b (1 : k) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hZ, ← kronDerLin_apply, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [map_smul, kronDerLin_apply]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(r, a, b), rfl⟩)

theorem bDer_lie (ε : τ → Finset (Fin n)) (x y : τ × Fin n × Fin n) :
    bDer (k := k) ε x * bDer ε y - bDer ε y * bDer ε x ∈ Submodule.span k (Set.range (bDer ε)) := by
  obtain ⟨r, a, b⟩ := x
  obtain ⟨r', c, d⟩ := y
  rw [bDer_mk, bDer_mk]
  by_cases hr : r' = r
  · subst hr
    rw [kronDer_mul_sub_mul]
    exact kronDer_mem_span_bDer ε r' _
  · have hPQ : ∀ p : τ × Fin n, p.1 = r → ¬ p.1 = r' := fun p hp hp' => hr (hp'.symm.trans hp)
    rw [kronDer_mul_comm_of_disjoint hPQ, sub_self]
    exact Submodule.zero_mem _

theorem bDer_mulVec_bvec_of_lt (ε : τ → Finset (Fin n)) (r : τ) {a b : Fin n} (hab : a < b) :
    bDer (k := k) ε (r, a, b) *ᵥ bvec ε = 0 := by
  refine kronDer_mulVec_single_ktop _ (fun a' b' hba => ?_) (bdeg_le ε)
  rw [Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact absurd hba (not_le.mpr hab)
  · rfl

theorem bDer_mulVec_bvec_self (ε : τ → Finset (Fin n)) (r : τ) (a : Fin n) :
    ∃ c : k, bDer (k := k) ε (r, a, a) *ᵥ bvec ε = c • bvec ε := by
  refine ⟨((Finset.univ.filter fun p : τ × Fin n =>
    p.1 = r ∧ a ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n))).card : k), ?_⟩
  ext s
  rw [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, bDer_mk,
    kronDer_single_self_apply]
  by_cases hs : s = btop ε
  · subst hs
    simp
  · simp [hs]

theorem bDer_mulVec_mem_bRad (ε : τ → Finset (Fin n)) (x : τ × Fin n × Fin n) {w : BIdx ε → k}
    (hw : w ∈ bRad ε) : bDer ε x *ᵥ w ∈ bRad ε := by
  obtain ⟨r, a, b⟩ := x
  refine mulVec_mem_dotRad (fun y hy => mulVec_mem_cyclicSub (r, a, b) hy) (fun y hy => ?_) hw
  rw [bDer_transpose]
  exact mulVec_mem_cyclicSub (r, b, a) hy

theorem bMat_mulVec_bvec_of_unitriangular (ε : τ → Finset (Fin n))
    {h : τ → Matrix (Fin n) (Fin n) k}
    (hh : ∀ r a b, b < a → h r a b = 0) (hh1 : ∀ r a, h r a a = 1) :
    bMat ε h *ᵥ bvec ε = bvec ε := by
  have h1 := kronMinor_mulVec_single_ktop (R := k) (d := bdeg ε) (g := fun p : τ × Fin n => h p.1)
    (fun p a b hab => hh p.1 a b hab) (fun p a => hh1 p.1 a) (bdeg_le ε)
  unfold bMat bvec btop
  exact h1

theorem bMat_diagonal_mulVec_bvec (ε : τ → Finset (Fin n)) (e : τ → Fin n → k) :
    bMat ε (fun r => Matrix.diagonal (e r)) *ᵥ bvec ε =
      (∏ p : τ × Fin n, ∏ a ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)),
        e p.1 a) • bvec ε := by
  change kronMinor (d := bdeg ε) (fun p : τ × Fin n => Matrix.diagonal (e p.1)) *ᵥ bvec ε = _
  rw [kronMinor_diagonal]
  ext s
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, bvec]
  by_cases hs : s = btop ε
  · subst hs
    simp
  · simp [hs]

theorem bMat_update_one_add_single_mulVec_bvec [CharP k 2] (ε : τ → Finset (Fin n)) (r : τ)
    {i j : Fin n} (hij : (j : ℕ) = i + 1) (c : k) :
    bMat ε (Function.update (fun _ => (1 : Matrix (Fin n) (Fin n) k)) r (1 + Matrix.single j i c)) *ᵥ
        bvec ε = bvec ε + c • (bDer ε (r, j, i) *ᵥ bvec ε) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hji : j ≠ i := fun h => by rw [h] at hij; omega
  have hfam : (fun p : τ × Fin n =>
      Function.update (fun _ => (1 : Matrix (Fin n) (Fin n) k)) r (1 + Matrix.single j i c) p.1) =
      fun p => 1 + Matrix.single j i (if p.1 = r then c else 0) := by
    funext p
    by_cases hp : p.1 = r
    · rw [hp, Function.update_self, if_pos rfl]
    · rw [Function.update_of_ne hp, if_neg hp, Matrix.single_zero, add_zero]
  have hkey : ∀ p : τ × Fin n,
      i ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) →
      j ∉ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) → p.2 = j := by
    intro p hi hj
    have hi' := (mem_initSeg (bdeg_le ε p) i).mp hi
    have hj' : ¬ (j : ℕ) < bdeg ε p := fun h => hj ((mem_initSeg (bdeg_le ε p) j).mpr h)
    unfold bdeg at hi' hj'
    split_ifs at hi' hj' with hp
    · exact Fin.ext (by omega)
    · omega
  ext s
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bvec, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one, Matrix.col_apply, Matrix.col_apply]
  change kronMinor (d := bdeg ε) (fun p : τ × Fin n => Function.update
      (fun _ => (1 : Matrix (Fin n) (Fin n) k)) r (1 + Matrix.single j i c) p.1) s (btop ε) =
    (Pi.single (btop ε) (1 : k) : BIdx ε → k) s + c * kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r)
      (Matrix.single j i 1) s (btop ε)
  rw [hfam, kronMinor_one_add_single h2 hji, kronDer_single_apply h2 _ hji]
  have hA : ∀ p : τ × Fin n,
      (i ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) ∧
        j ∉ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) ∧
        ((s p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) =
          insert j (((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)).erase i)) →
      s p ≠ btop ε p := by
    rintro p ⟨-, hj, hs⟩ heq
    apply hj
    rw [← heq, hs]
    exact Finset.mem_insert_self _ _
  by_cases hst : s = btop ε
  · subst hst
    rw [Finset.prod_eq_one fun p _ => if_pos rfl, Pi.single_eq_same, if_neg, mul_zero, add_zero]
    rintro ⟨p, -, -, hC⟩
    exact hA p hC rfl
  · rw [Pi.single_eq_of_ne hst, zero_add]
    split_ifs with hex
    · rw [mul_one]
      obtain ⟨p, hp, hq, hC⟩ := hex
      rw [Finset.prod_eq_single p (fun q _ hqp => if_pos (hq q hqp))
        (fun h => absurd (Finset.mem_univ p) h), if_neg (hA p hC), if_pos hC, if_pos hp]
    · rw [mul_zero]
      obtain ⟨p₀, hp₀⟩ : ∃ p, s p ≠ btop ε p := by
        by_contra h
        push Not at h
        exact hst (funext h)
      by_contra hne
      have hf := Finset.prod_ne_zero_iff.mp hne
      have hfac : ∀ p, s p ≠ btop ε p → p.1 = r ∧
          (i ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) ∧
            j ∉ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) ∧
            ((s p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) =
              insert j (((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)).erase i)) := by
        intro p hp
        have h0 := hf p (Finset.mem_univ p)
        rw [if_neg hp] at h0
        split_ifs at h0 with hC hr
        · exact ⟨hr, hC⟩
        · exact absurd rfl h0
        · exact absurd rfl h0
      obtain ⟨hr₀, hC₀⟩ := hfac p₀ hp₀
      have hp₀j := hkey p₀ hC₀.1 hC₀.2.1
      apply hex
      refine ⟨p₀, hr₀, fun q hq => ?_, hC₀⟩
      by_contra hsq
      obtain ⟨hrq, hCq⟩ := hfac q hsq
      exact hq (Prod.ext (hrq.trans hr₀.symm) ((hkey q hCq.1 hCq.2.1).trans hp₀j.symm))

theorem bMat_mul_bDer (ε : τ → Finset (Fin n)) (h : τ → SpecialLinearGroup (Fin n) k)
    (x : τ × Fin n × Fin n) :
    ∃ X ∈ Submodule.span k (Set.range (bDer (k := k) ε)),
      bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) * bDer ε x =
        X * bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) := by
  obtain ⟨r, a, b⟩ := x
  refine ⟨kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r)
    ((h r : Matrix (Fin n) (Fin n) k) * Matrix.single a b 1 *
      (((h r)⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)),
    kronDer_mem_span_bDer ε r _, ?_⟩
  have hinv : ∀ p : τ × Fin n, (h p.1 : Matrix (Fin n) (Fin n) k) *
      (((h p.1)⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 := fun p => by
    show ((h p.1 * (h p.1)⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1
    rw [mul_inv_cancel]
    rfl
  have hinv' : ∀ p : τ × Fin n,
      (((h p.1)⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *
        (h p.1 : Matrix (Fin n) (Fin n) k) = 1 := fun p => by
    show (((h p.1)⁻¹ * h p.1 : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1
    rw [inv_mul_cancel]
    rfl
  have hconj := kronMinor_mul_kronDer_mul_kronMinor (d := bdeg ε) (fun p : τ × Fin n => p.1 = r)
    (g := fun p => (h p.1 : Matrix (Fin n) (Fin n) k))
    (g' := fun p => (((h p.1)⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)) hinv
    (g₀ := (h r : Matrix (Fin n) (Fin n) k))
    (g₀' := (((h r)⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k))
    (fun p hp => by simp only [hp]) (fun p hp => by simp only [hp]) (Matrix.single a b 1)
  have hone := kronMinor_mul_eq_one (d := bdeg ε) hinv'
  change kronMinor (d := bdeg ε) (fun p : τ × Fin n => (h p.1 : Matrix (Fin n) (Fin n) k)) *
      kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r) (Matrix.single a b 1) =
    _ * kronMinor (d := bdeg ε) (fun p : τ × Fin n => (h p.1 : Matrix (Fin n) (Fin n) k))
  rw [← hconj, Matrix.mul_assoc _ (kronMinor _) (kronMinor _), hone, Matrix.mul_one]

theorem bMat_mulVec_mem_bCyc_of_bvec (ε : τ → Finset (Fin n)) (h : τ → SpecialLinearGroup (Fin n) k)
    (hv : bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε ∈ bCyc ε)
    {w : BIdx ε → k} (hw : w ∈ bCyc ε) :
    bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) *ᵥ w ∈ bCyc ε :=
  mulVec_mem_cyclicSub_of_conj hv (bMat_mul_bDer ε h) hw

omit [Fintype τ] in
theorem coe_mulSingle_eq_update (r : τ) (M : SpecialLinearGroup (Fin n) k) (r' : τ) :
    (((Pi.mulSingle r M : τ → SpecialLinearGroup (Fin n) k) r' : SpecialLinearGroup (Fin n) k) :
      Matrix (Fin n) (Fin n) k) =
      Function.update (fun _ => (1 : Matrix (Fin n) (Fin n) k)) r (M : Matrix (Fin n) (Fin n) k) r' := by
  by_cases hr : r' = r
  · subst hr
    rw [Pi.mulSingle_eq_same, Function.update_self]
  · rw [Pi.mulSingle_eq_of_ne hr, Function.update_of_ne hr]
    rfl

theorem bMat_mulSingle_transvection_mulVec_bvec_mem [CharP k 2] (ε : τ → Finset (Fin n)) (r : τ)
    {i j : Fin n} (hij : i ≠ j) (hadj : (j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1) (c : k) :
    bMat ε (fun r' => (((Pi.mulSingle r (SpecialLinearGroup.transvection hij c) :
      τ → SpecialLinearGroup (Fin n) k) r' : SpecialLinearGroup (Fin n) k) :
        Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε ∈ bCyc ε := by
  have hfam : (fun r' => (((Pi.mulSingle r (SpecialLinearGroup.transvection hij c) :
      τ → SpecialLinearGroup (Fin n) k) r' : SpecialLinearGroup (Fin n) k) :
        Matrix (Fin n) (Fin n) k)) =
      Function.update (fun _ => (1 : Matrix (Fin n) (Fin n) k)) r (1 + Matrix.single i j c) := by
    funext r'
    rw [coe_mulSingle_eq_update, SpecialLinearGroup.transvection_coe]
  rw [hfam]
  rcases hadj with hji | hij'
  · rw [bMat_mulVec_bvec_of_unitriangular ε (fun r' a b hba => ?_) (fun r' a => ?_)]
    · exact bvec_mem_bCyc ε
    · by_cases hr : r' = r
      · subst hr
        rw [Function.update_self, Matrix.add_apply, Matrix.one_apply_ne hba.ne', Matrix.single_apply,
          if_neg, add_zero]
        rintro ⟨rfl, rfl⟩
        exact absurd (Fin.lt_iff_val_lt_val.mp hba) (by omega)
      · rw [Function.update_of_ne hr, Matrix.one_apply_ne hba.ne']
    · by_cases hr : r' = r
      · subst hr
        rw [Function.update_self, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply, if_neg,
          add_zero]
        rintro ⟨rfl, h⟩
        exact hij h.symm
      · rw [Function.update_of_ne hr, Matrix.one_apply_eq]
  · rw [bMat_update_one_add_single_mulVec_bvec ε r hij' c]
    exact Submodule.add_mem _ (bvec_mem_bCyc ε)
      (Submodule.smul_mem _ c (mulVec_mem_cyclicSub (r, i, j) (bvec_mem_bCyc ε)))

theorem eq_top_of_transvection_adjacent_mem (H : Subgroup (SpecialLinearGroup (Fin n) k))
    (hH : ∀ {i j : Fin n} (hij : i ≠ j), ((j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1) →
      ∀ c : k, SpecialLinearGroup.transvection hij c ∈ H) : H = ⊤ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine eq_top_iff.mpr fun M _ => ?_
    rw [show M = 1 from Subtype.ext (Matrix.ext fun a => a.elim0)]
    exact H.one_mem
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [eq_top_iff, ← CFSG.LieType.Universal.SpecialLinear.iSup_fundamentalRootSubgroup_eq_top]
    refine iSup_le fun a => iSup_le fun s => ?_
    have hroot : ∀ {i j : Fin (m + 1)} (hij : i ≠ j), ((j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1) →
        CFSG.LieType.Universal.SpecialLinear.rootSubgroup m k hij ≤ H := by
      intro i j hij hadj M hM
      obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup hij M).mp hM
      exact hH hij hadj c
    cases s
    · exact hroot _ (Or.inr (by simp))
    · exact hroot _ (Or.inl (by simp))

theorem pi_mem_of_transvection_adjacent_mem (H : Subgroup (τ → SpecialLinearGroup (Fin n) k))
    (hH : ∀ (r : τ) {i j : Fin n} (hij : i ≠ j), ((j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1) → ∀ c : k,
      (Pi.mulSingle r (SpecialLinearGroup.transvection hij c) : τ → SpecialLinearGroup (Fin n) k) ∈ H)
    (h : τ → SpecialLinearGroup (Fin n) k) : h ∈ H := by
  have hsingle : ∀ (r : τ) (M : SpecialLinearGroup (Fin n) k),
      (Pi.mulSingle r M : τ → SpecialLinearGroup (Fin n) k) ∈ H := by
    intro r
    let K : Subgroup (SpecialLinearGroup (Fin n) k) :=
      { carrier := {M | (Pi.mulSingle r M : τ → SpecialLinearGroup (Fin n) k) ∈ H}
        mul_mem' := fun {M M'} hM hM' => by
          change (Pi.mulSingle r (M * M') : τ → SpecialLinearGroup (Fin n) k) ∈ H
          rw [Pi.mulSingle_mul]
          exact H.mul_mem hM hM'
        one_mem' := by
          change (Pi.mulSingle r 1 : τ → SpecialLinearGroup (Fin n) k) ∈ H
          rw [Pi.mulSingle_one]
          exact H.one_mem
        inv_mem' := fun {M} hM => by
          change (Pi.mulSingle r M⁻¹ : τ → SpecialLinearGroup (Fin n) k) ∈ H
          rw [Pi.mulSingle_inv]
          exact H.inv_mem hM }
    have hK : K = ⊤ := eq_top_of_transvection_adjacent_mem K fun hij hadj c => hH r hij hadj c
    intro M
    have hM : M ∈ K := hK ▸ Subgroup.mem_top M
    exact hM
  have hfin : ∀ S : Finset τ, (fun r => if r ∈ S then h r else 1) ∈ H := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have h0 : (fun r => if r ∈ (∅ : Finset τ) then h r else 1) = 1 :=
        funext fun r => if_neg (Finset.notMem_empty r)
      rw [h0]
      exact H.one_mem
    | insert a S haS ih =>
      have h1 : (fun r => if r ∈ insert a S then h r else 1) =
          (Pi.mulSingle a (h a) : τ → SpecialLinearGroup (Fin n) k) *
            fun r => if r ∈ S then h r else 1 := by
        funext r
        rw [Pi.mul_apply]
        by_cases hr : r = a
        · subst hr
          rw [if_pos (Finset.mem_insert_self _ _), Pi.mulSingle_eq_same, if_neg haS, mul_one]
        · rw [Pi.mulSingle_eq_of_ne hr, one_mul]
          simp only [Finset.mem_insert, hr, false_or]
      rw [h1]
      exact H.mul_mem (hsingle a (h a)) ih
  have hu := hfin Finset.univ
  simpa only [Finset.mem_univ, if_true] using hu

theorem bMat_mulVec_mem_bCyc [CharP k 2] (ε : τ → Finset (Fin n))
    (h : τ → SpecialLinearGroup (Fin n) k) {w : BIdx ε → k} (hw : w ∈ bCyc ε) :
    bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) *ᵥ w ∈ bCyc ε := by
  have hmul : ∀ g g' : τ → SpecialLinearGroup (Fin n) k,
      bMat ε (fun r => (g r : Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε ∈ bCyc (k := k) ε →
      bMat ε (fun r => (g' r : Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε ∈ bCyc (k := k) ε →
      bMat ε (fun r => ((g * g') r : Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε ∈ bCyc (k := k) ε := by
    intro g g' hg hg'
    change bMat ε (fun r => (g r : Matrix (Fin n) (Fin n) k) * (g' r : Matrix (Fin n) (Fin n) k)) *ᵥ
      bvec ε ∈ bCyc ε
    rw [bMat_mul, ← Matrix.mulVec_mulVec]
    exact bMat_mulVec_mem_bCyc_of_bvec ε g hg hg'
  have hone : bMat ε (fun r => (((1 : τ → SpecialLinearGroup (Fin n) k) r : SpecialLinearGroup (Fin n) k) :
      Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε ∈ bCyc (k := k) ε := by
    change bMat ε (fun _ => (1 : Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε ∈ bCyc ε
    rw [bMat_one, Matrix.one_mulVec]
    exact bvec_mem_bCyc ε
  let H : Subgroup (τ → SpecialLinearGroup (Fin n) k) :=
    { carrier := {g | bMat ε (fun r => (g r : Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε ∈ bCyc (k := k) ε ∧
        bMat ε (fun r => ((g⁻¹ : τ → SpecialLinearGroup (Fin n) k) r : Matrix (Fin n) (Fin n) k)) *ᵥ
          bvec ε ∈ bCyc (k := k) ε}
      mul_mem' := fun {g g'} hg hg' =>
        ⟨hmul g g' hg.1 hg'.1, by rw [_root_.mul_inv_rev]; exact hmul _ _ hg'.2 hg.2⟩
      one_mem' := ⟨hone, by rw [inv_one]; exact hone⟩
      inv_mem' := fun {g} hg => ⟨hg.2, by rw [inv_inv]; exact hg.1⟩ }
  have hH : h ∈ H := pi_mem_of_transvection_adjacent_mem H (fun r i j hij hadj c =>
    ⟨bMat_mulSingle_transvection_mulVec_bvec_mem ε r hij hadj c, by
      rw [← Pi.mulSingle_inv, SpecialLinearGroup.transvection_inv]
      exact bMat_mulSingle_transvection_mulVec_bvec_mem ε r hij hadj (-c)⟩) h
  exact bMat_mulVec_mem_bCyc_of_bvec ε h hH.1 hw

theorem bMat_mulVec_mem_bRad [CharP k 2] (ε : τ → Finset (Fin n))
    (h : τ → SpecialLinearGroup (Fin n) k) {w : BIdx ε → k} (hw : w ∈ bRad ε) :
    bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) *ᵥ w ∈ bRad ε := by
  refine mulVec_mem_dotRad (fun y hy => bMat_mulVec_mem_bCyc ε h hy) (fun y hy => ?_) hw
  rw [← bMat_transpose]
  exact bMat_mulVec_mem_bCyc ε (fun r => SpecialLinearGroup.transpose (h r)) hy

@[expose] noncomputable def bRep [CharP k 2] (ε : τ → Finset (Fin n)) :
    Representation k (τ → SpecialLinearGroup (Fin n) k) (BModel k ε) :=
  Representation.quotient
    (Representation.subrepresentation
      ({ toFun := fun h => (bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k))).mulVecLin
         map_one' := by
           change (bMat ε (fun _ => (1 : Matrix (Fin n) (Fin n) k))).mulVecLin = LinearMap.id
           rw [bMat_one, Matrix.mulVecLin_one]
         map_mul' := fun g g' => by
           change (bMat ε (fun r => (g r : Matrix (Fin n) (Fin n) k) *
             (g' r : Matrix (Fin n) (Fin n) k))).mulVecLin = _
           rw [bMat_mul, Matrix.mulVecLin_mul]
           rfl } :
        Representation k (τ → SpecialLinearGroup (Fin n) k) (BIdx ε → k))
      (bCyc ε) fun h _ hw => bMat_mulVec_mem_bCyc ε h hw)
    ((bRad ε).comap (bCyc ε).subtype) fun h _ hw => bMat_mulVec_mem_bRad ε h hw

theorem bRep_mk [CharP k 2] (ε : τ → Finset (Fin n)) (h : τ → SpecialLinearGroup (Fin n) k)
    (w : bCyc (k := k) ε) :
    bRep ε h (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) *ᵥ (w : BIdx ε → k),
        bMat_mulVec_mem_bCyc ε h w.2⟩ :=
  rfl

theorem sub_smul_bvec_mem_bRad (ε : τ → Finset (Fin n)) {w : BIdx ε → k} (hw : w ∈ bCyc ε)
    (h : ∀ r a b, a < b → bDer ε (r, a, b) *ᵥ w ∈ bRad ε) :
    w - (w ⬝ᵥ bvec ε) • bvec ε ∈ bRad ε := by
  let sgn : τ × Fin n × Fin n → SignType := fun x =>
    if x.2.1 < x.2.2 then 1 else if x.2.1 = x.2.2 then 0 else -1
  let op : τ × Fin n × Fin n → τ × Fin n × Fin n := fun x => (x.1, x.2.2, x.2.1)
  refine sub_smul_mem_dotRad (D := bDer (k := k) ε) sgn op ?_ ?_ (bDer_lie ε) ?_ ?_
    (bvec_dotProduct_bvec ε) hw ?_
  · rintro ⟨r, a, b⟩
    rcases lt_trichotomy a b with hab | rfl | hab
    · simp only [sgn, op, if_pos hab, if_neg (not_lt.mpr hab.le), if_neg hab.ne']
      try rfl
    · simp only [sgn, op, lt_irrefl, if_false, if_true]
      try rfl
    · simp only [sgn, op, if_pos hab, if_neg (not_lt.mpr hab.le), if_neg hab.ne']
      try rfl
  · rintro ⟨r, a, b⟩
    exact bDer_transpose ε r a b
  · rintro ⟨r, a, b⟩ hb
    rcases lt_trichotomy a b with hab | rfl | hab
    · exact bDer_mulVec_bvec_of_lt ε r hab
    · simp only [sgn, lt_irrefl, if_false, if_true] at hb
      exact absurd hb (by decide)
    · simp only [sgn, if_neg (not_lt.mpr hab.le), if_neg hab.ne'] at hb
      exact absurd hb (by decide)
  · rintro ⟨r, a, b⟩ hb
    rcases lt_trichotomy a b with hab | rfl | hab
    · simp only [sgn, if_pos hab] at hb
      exact absurd hb (by decide)
    · exact bDer_mulVec_bvec_self ε r a
    · simp only [sgn, if_neg (not_lt.mpr hab.le), if_neg hab.ne'] at hb
      exact absurd hb (by decide)
  · rintro ⟨r, a, b⟩ hb
    rcases lt_trichotomy a b with hab | rfl | hab
    · exact h r a b hab
    · simp only [sgn, lt_irrefl, if_false, if_true] at hb
      exact absurd hb (by decide)
    · simp only [sgn, if_neg (not_lt.mpr hab.le), if_neg hab.ne'] at hb
      exact absurd hb (by decide)

@[expose] noncomputable def twistHom {F : Type*} [CommRing F] (φ : τ → F →+* k) :
    SpecialLinearGroup (Fin n) F →* (τ → SpecialLinearGroup (Fin n) k) :=
  Pi.monoidHom fun r => SpecialLinearGroup.map (φ r)

end CFSG.LieType.SpecialLinear.ExteriorModel
