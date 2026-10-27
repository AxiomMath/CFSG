module

public import CFSG.Certificates.Kernel.Spor.PK.O73Tab
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs
public import CFSG.Certificates.Kernel.MonsterB.Co2PermSound
public import Certificates.Data.Kernel.Misc.O73Chain

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.LieType.Multipliers.O73 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native Matrix

private theorem letB_eq' (y : Nat) (k : Nat → Bool) : CFSG.KC.LQT.P.letB y k = k y := by
  cases y <;> rfl

theorem matM7_eq (A : Matrix Idx Idx (ZMod 3)) : matM7 A = mEnc A := rfl

theorem getD_matM7 {Ms : List (Matrix Idx Idx (ZMod 3))} {j : ℕ} (hj : j < Ms.length) :
    (Ms.map matM7).getD j 0 = mEnc (Ms.getD j 1) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj, List.getElem_map,
    matM7_eq]

theorem iso_of_isoM7 {M : Matrix Idx Idx (ZMod 3)} (h : isoM7 (mEnc M) = true) :
    Mᵀ * (gram * M) = gram := by
  unfold isoM7 at h
  rw [gramM_eq, trM7_mEnc, mulM7_mEnc, mulM7_mEnc] at h
  exact mEnc_inj (Nat.eq_of_beq_eq_true h)

theorem tabOf_eq_unpack {w P : ℕ} {M : Matrix Idx Idx (ZMod 3)} (h : tabM7 w P (mEnc M) = true) :
    tabOf M = CFSG.KS.Raw.unpack 2187 w P := by
  apply Array.ext
  · rw [tabOf_size]
    simp [CFSG.KS.Raw.unpack]
  · intro i h1 h2
    have hi : i < 2187 := by rwa [tabOf_size] at h1
    unfold tabM7 at h
    rw [letB_eq'] at h
    have e := Nat.eq_of_beq_eq_true (allN_spec h i hi)
    rw [appM7_mEnc M hi] at e
    simp only [tabOf, CFSG.KS.Raw.unpack, Array.getElem_ofFn]
    exact e.symm

theorem det_wordMat (Ms : List (Matrix Idx Idx (ZMod 3))) : ∀ w : List ℕ,
    (∀ c ∈ w, c < Ms.length → (Ms.getD c 1).det = 1) → (wordMat Ms w).det = 1
  | [], _ => by simp [wordMat]
  | c :: w, h => by
    rw [wordMat, Matrix.det_mul, det_wordMat Ms w fun c' hc' => h c' (List.mem_cons_of_mem _ hc')]
    split_ifs with hc
    · rw [h c (List.mem_cons_self ..) hc, one_mul]
    · simp

private theorem det_eq_one_of_cube {M : Matrix Idx Idx (ZMod 3)} (h : M * (M * M) = 1) :
    M.det = 1 := by
  have e := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at e
  have key : ∀ d : ZMod 3, d * (d * d) = 1 → d = 1 := by decide
  exact key _ e

theorem det_of_wordOK {Ms : List (Matrix Idx Idx (ZMod 3))} {ord : List ℕ} {W : ℕ → List ℤ}
    (hcube : ∀ j < 2, Nat.beq (mulM7 ((Ms.map matM7).getD j 0)
      (mulM7 ((Ms.map matM7).getD j 0) ((Ms.map matM7).getD j 0))) oneM7 = true)
    (hw : ∀ j < Ms.length, 2 ≤ j → wordOK (Ms.map matM7) ord (W j) j = true) :
    ∀ j < Ms.length, (Ms.getD j 1).det = 1 := by
  have hK : Ms.map matM7 = Ms.map mEnc := rfl
  have hget : ∀ j < Ms.length, (Ms.map matM7).getD j 0 = mEnc (Ms.getD j 1) :=
    fun j hj => getD_matM7 hj
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases h2 : j < 2
    · have h := hcube j h2
      rw [hget j hj, mulM7_mEnc, mulM7_mEnc, oneM7_eq] at h
      exact det_eq_one_of_cube (mEnc_inj (Nat.eq_of_beq_eq_true h))
    · have h := hw j hj (by omega)
      unfold wordOK at h
      rw [Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨h1, h3⟩ := h
      rw [hget j hj, hK, wordM7_mEnc] at h1
      rw [mEnc_inj (Nat.eq_of_beq_eq_true h1)]
      refine det_wordMat _ _ fun c hc _ => ?_
      have hcj : c < j := by simpa using h3 c hc
      exact ih c hcj (by omega)

@[expose] def linSub : Subgroup (Equiv.Perm (Fin 2187)) where
  carrier := {σ | ∃ M : Matrix Idx Idx (ZMod 3), Mᵀ * (gram * M) = gram ∧ M.det = 1 ∧
    ∀ x : Fin 2187, (σ x : ℕ) = code (M *ᵥ dec x)}
  one_mem' := ⟨1, by simp, by simp, fun x => by simp [code_dec x.2]⟩
  mul_mem' := by
    rintro σ τ ⟨M, hM, dM, aM⟩ ⟨N, hN, dN, aN⟩
    refine ⟨M * N, ?_, by rw [Matrix.det_mul, dM, dN, one_mul], fun x => ?_⟩
    · have e : (M * N)ᵀ * (gram * (M * N)) = Nᵀ * ((Mᵀ * (gram * M)) * N) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [e, hM, hN]
    · rw [Equiv.Perm.mul_apply, aM, aN, dec_code, Matrix.mulVec_mulVec]
  inv_mem' := by
    rintro σ ⟨M, hM, dM, aM⟩
    have hu : IsUnit M.det := by
      rw [dM]
      exact isUnit_one
    have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hu
    have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hu
    refine ⟨M⁻¹, ?_, ?_, fun x => ?_⟩
    · have e : (M⁻¹)ᵀ * (gram * M⁻¹) = (M * M⁻¹)ᵀ * (gram * (M * M⁻¹)) := by
        conv_lhs => rw [← hM]
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [e, h1]
      simp
    · rw [Matrix.det_nonsing_inv, dM]
      simp
    · obtain ⟨y, rfl⟩ := σ.surjective x
      have e : σ⁻¹ (σ y) = y := by simp
      rw [e, aM y, dec_code, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec,
        code_dec y.2]

private theorem tabOf_inj {M : Matrix Idx Idx (ZMod 3)} (dM : M.det = 1) :
    ∀ i j, i < 2187 → j < 2187 → (tabOf M)[i]! = (tabOf M)[j]! → i = j := by
  have hu : IsUnit M.det := by
    rw [dM]
    exact isUnit_one
  intro i j hi hj h
  rw [tabOf_get M hi, tabOf_get M hj] at h
  have h' := congrArg (fun v => M⁻¹ *ᵥ v) (congrArg dec h)
  simp only [dec_code, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hu, Matrix.one_mulVec] at h'
  rw [← code_dec hi, ← code_dec hj, h']

private theorem tabOf_lt (M : Matrix Idx Idx (ZMod 3)) : ∀ i < 2187, (tabOf M)[i]! < 2187 :=
  fun i hi => by
    rw [tabOf_get M hi]
    exact code_lt _

theorem isInvA_tabOf {M : Matrix Idx Idx (ZMod 3)} (dM : M.det = 1) :
    isInvA 2187 (tabOf M) (invCand 2187 (tabOf M)) = true :=
  CFSG.KC.Co2Mem.isInvA_invCand (tabOf_lt M) (tabOf_inj dM)

theorem mem_linSub {M : Matrix Idx Idx (ZMod 3)} (hM : Mᵀ * (gram * M) = gram) (dM : M.det = 1) :
    permOfArr 2187 (tabOf M) ∈ linSub := by
  have hrep := (rep_permOfArr (isInvA_tabOf dM)).1
  exact ⟨M, hM, dM, fun x => by rw [← hrep x, tabOf_get M x.2]⟩

private theorem iso_dot {M : Matrix Idx Idx (ZMod 3)} (hM : Mᵀ * (gram * M) = gram)
    (u w : Idx → ZMod 3) : (M *ᵥ u) ⬝ᵥ (gram *ᵥ (M *ᵥ w)) = u ⬝ᵥ (gram *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose M u,
    Matrix.vecMul_vecMul, hM, ← Matrix.dotProduct_mulVec]

private theorem gram_mulVec (v : Idx → ZMod 3) : gram *ᵥ v = gv v := by
  funext a
  rcases a with k | k | u
  · fin_cases k <;> simp [Matrix.mulVec, dotProduct, gram, gv, Fintype.sum_sum_type, Fin.sum_univ_three]
  · fin_cases k <;> simp [Matrix.mulVec, dotProduct, gram, gv, Fintype.sum_sum_type, Fin.sum_univ_three]
  · cases u
    simp [Matrix.mulVec, dotProduct, gram, gv, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem single_dot (a : Idx) (v : Idx → ZMod 3) : Pi.single a 1 ⬝ᵥ v = v a := by
  simp [dotProduct, Pi.single_apply]

private theorem single_dot' (a : Idx) (c : ZMod 3) (v : Idx → ZMod 3) :
    Pi.single a c ⬝ᵥ v = c * v a := by
  simp [dotProduct, Pi.single_apply]

private theorem mulVec_single_apply (M : Matrix Idx Idx (ZMod 3)) (i j : Idx) :
    (M *ᵥ Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem eq_one_of_fix {M : Matrix Idx Idx (ZMod 3)} (hM : Mᵀ * (gram * M) = gram)
    (dM : M.det = 1) (hc : ∀ a : Idx, a ≠ .inr (.inr ()) → M *ᵥ Pi.single a 1 = Pi.single a 1) :
    M = 1 := by
  set z : Idx := .inr (.inr ()) with hzdef
  set v := M *ᵥ Pi.single z 1 with hv
  have hB : ∀ a, a ≠ z → gv v a = 0 := by
    intro a ha
    have h := iso_dot hM (Pi.single a 1) (Pi.single z 1)
    rw [hc a ha, ← hv, gram_mulVec, gram_mulVec, single_dot, single_dot] at h
    rw [h]
    rcases a with k | k | u
    · simp [gv, z]
    · simp [gv, z]
    · exact absurd rfl ha
  have hvz : v = Pi.single z (v z) := by
    funext a
    rcases a with k | k | u
    · have h := hB (.inr (.inl k)) (by simp [z])
      simp only [gv] at h
      simp [z, h]
    · have h := hB (.inl k) (by simp [z])
      simp only [gv] at h
      simp [z, h]
    · cases u
      simp [z]
  have hsq : v z * (2 * v z) = 2 := by
    have h := iso_dot hM (Pi.single z 1) (Pi.single z 1)
    rw [← hv, gram_mulVec, gram_mulVec, single_dot] at h
    rw [hvz, single_dot'] at h
    simpa [gv, z] using h
  have hd : M = Matrix.diagonal fun i => if i = z then v z else 1 := by
    ext i j
    rw [← mulVec_single_apply M i j, Matrix.diagonal_apply]
    by_cases hj : j = z
    · subst hj
      rw [← hv, hvz]
      by_cases hi : i = z
      · subst hi
        simp
      · simp [hi]
    · rw [hc j hj]
      by_cases hij : i = j
      · subst hij
        simp [hj]
      · simp [Pi.single_apply, hij]
  have hdet : M.det = v z := by
    rw [hd, Matrix.det_diagonal]
    simp [z, Fintype.prod_sum_type]
  have hc12 : ∀ c : ZMod 3, c * (2 * c) = 2 → c = 1 ∨ c = 2 := by decide
  rcases hc12 _ hsq with h1 | h2
  · rw [hd, h1]
    have e : (fun i => if i = z then (1 : ZMod 3) else 1) = fun _ => 1 := by
      funext i
      split_ifs <;> rfl
    rw [e]
    exact Matrix.diagonal_one
  · exfalso
    rw [hdet, h2] at dM
    exact absurd dM (by decide)

private theorem dec_pow (t : ℕ) (ht : t < 6) : dec (3 ^ t) = Pi.single (idxOf t) 1 := by
  interval_cases t <;> decide

theorem sep_of_mats {S : Array (Array ℕ)} {base : Array ℕ}
    (hS : ∀ j < S.size, ∃ M : Matrix Idx Idx (ZMod 3), S[j]! = tabOf M ∧
      Mᵀ * (gram * M) = gram ∧ M.det = 1)
    (hb : base.size = 6) (hbase : ∀ t < 6, base[t]! = 3 ^ t) : CFSG.KS.Raw.Sep 2187 S base := by
  intro G hG hfix
  have hmem : G ∈ linSub := by
    refine (Subgroup.closure_le linSub).2 ?_ hG
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨M, hM, hiso, hdet⟩ := hS j hj
    rw [hM]
    exact mem_linSub hiso hdet
  obtain ⟨M, hiso, hdet, hact⟩ := hmem
  have hcol : ∀ t < 6, M *ᵥ Pi.single (idxOf t) 1 = Pi.single (idxOf t) 1 := by
    intro t ht
    have h3 : base[t]! < 2187 := by
      rw [hbase t ht]
      interval_cases t <;> norm_num
    have e : code (M *ᵥ dec base[t]!) = base[t]! :=
      (hact ⟨_, h3⟩).symm.trans (congrArg Fin.val (hfix t (hb ▸ ht) h3))
    rw [hbase t ht] at e
    have e2 := congrArg dec e
    rw [dec_code, dec_pow t ht] at e2
    exact e2
  have hM1 : M = 1 := by
    refine eq_one_of_fix hiso hdet fun a ha => ?_
    have hlt : idx a < 6 := by
      rcases a with k | k | u
      · fin_cases k <;> decide
      · fin_cases k <;> decide
      · exact absurd rfl ha
    have := hcol (idx a) hlt
    rwa [idxOf_idx] at this
  subst hM1
  refine Equiv.ext fun x => Fin.ext ?_
  rw [hact x, Matrix.one_mulVec, code_dec x.2]
  rfl

end CFSG.KS.PK

end
