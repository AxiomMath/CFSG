module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3F0Subgroups

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.RankThree.Asc83Table Subgroup Matrix

@[expose] def sqM (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3) := mulM A A

@[expose] def ord8Chk (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Bool :=
  eqM (sqM (sqM (sqM M))) 1 && !eqM (sqM (sqM M)) 1

@[expose] def stabDChk (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (v : Fin 4 → ZMod 3) : Bool :=
  (List.range 3).any fun s => (List.range 3).any fun t =>
    decide (mulV M v 0 = (s : ZMod 3) * v 0) && decide (mulV M v 1 = (s : ZMod 3) * v 1) &&
    decide (mulV M v 2 = (s : ZMod 3) * v 2) && decide (mulV M v 3 = (s : ZMod 3) * v 3 + (t : ZMod 3))

@[expose] def nontrivDChk (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (v : Fin 4 → ZMod 3) : Bool :=
  !(decide (mulV M v 0 = v 0) && decide (mulV M v 1 = v 1) && decide (mulV M v 2 = v 2) &&
    decide (mulV M v 3 = v 3))

@[expose] def goodVChk (v : Fin 4 → ZMod 3) : Bool :=
  matS.any fun M => ord8Chk M && stabDChk M v && nontrivDChk M v

theorem good_all : allV.all (fun v => decide (v 0 = 0) || goodVChk v) = true := by
  decide +kernel

theorem sqM_eq (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) : sqM A = A * A := mulM_eq A A

theorem exists_matrix (v : Fin 4 → ZMod 3) (hv : v 0 ≠ 0) :
    ∃ M ∈ matS, M ^ 8 = 1 ∧ M ^ 4 ≠ 1 ∧
      (∃ s t : ZMod 3, M *ᵥ v = s • v + t • (![0, 0, 0, 1] : Fin 4 → ZMod 3)) ∧ M *ᵥ v ≠ v := by
  have h := good_all
  simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  have hv' := (h v (mem_allV v)).resolve_left hv
  simp only [goodVChk, List.any_eq_true, Bool.and_eq_true] at hv'
  obtain ⟨M, hM, ⟨ho, hst⟩, hnt⟩ := hv'
  refine ⟨M, hM, ?_, ?_, ?_, ?_⟩
  · simp only [ord8Chk, Bool.and_eq_true, eqM_iff, sqM_eq] at ho
    have := ho.1
    simpa [pow_succ, mul_assoc] using this
  · intro h4
    simp only [ord8Chk, Bool.and_eq_true] at ho
    have h4' : eqM (sqM (sqM M)) 1 = true := by
      rw [eqM_iff, sqM_eq, sqM_eq]
      simpa [pow_succ, mul_assoc] using h4
    rw [h4'] at ho
    exact absurd ho.2 (by decide)
  · simp only [stabDChk, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.mem_range] at hst
    obtain ⟨s, -, t, -, ⟨⟨h0, h1⟩, h2⟩, h3⟩ := hst
    refine ⟨(s : ZMod 3), (t : ZMod 3), ?_⟩
    rw [← mulV_eq]
    ext i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  · intro heq
    have hm : mulV M v = v := by rw [mulV_eq]; exact heq
    have : nontrivDChk M v = false := by simp [nontrivDChk, hm]
    rw [this] at hnt
    exact absurd hnt (by decide)

theorem matrix_eq_one_of_mulVec (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) (h : ∀ w, A *ᵥ w = w) :
    A = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

namespace J3Pkg

variable {X : Type*} [Group X] [Finite X] {k : Fin 6 → X} (h : J3Pkg k)
include h

theorem phi_nsmul (n : ℕ) (w : Fin 4 → ZMod 3) : h.phi (n • w) = (h.phi w) ^ n := by
  induction n with
  | zero => simpa using h.phi_zero
  | succ n ihn => rw [succ_nsmul, h.phi_add, ihn, pow_succ]

theorem phi_zsmul (s : ZMod 3) (w : Fin 4 → ZMod 3) : h.phi (s • w) = (h.phi w) ^ s.val := by
  have : s • w = s.val • w := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  rw [this, h.phi_nsmul]

theorem conj_pow_phi {y : X} {M : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (hy : ∀ w, y * h.phi w * y⁻¹ = h.phi (M *ᵥ w)) (n : ℕ) (w : Fin 4 → ZMod 3) :
    y ^ n * h.phi w * (y ^ n)⁻¹ = h.phi ((M ^ n) *ᵥ w) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    have e1 : y ^ (n + 1) * h.phi w * (y ^ (n + 1))⁻¹ =
        y ^ n * (y * h.phi w * y⁻¹) * (y ^ n)⁻¹ := by
      rw [pow_succ, _root_.mul_inv_rev]; group
    rw [e1, hy w, ih, pow_succ, ← Matrix.mulVec_mulVec]

theorem exists_u (hcard : Nat.card (Subgroup.closure (Set.range k)) = 5832)
    (v : Fin 4 → ZMod 3) (hv : v 0 ≠ 0) :
    ∃ u ∈ Subgroup.closure (Set.range k), orderOf u = 8 ∧
      u * h.phi v * u⁻¹ ∈ Subgroup.zpowers (h.phi v) ⊔ Subgroup.zpowers (xB k 3) ∧
      u * h.phi v * u⁻¹ ≠ h.phi v := by
  obtain ⟨M, hM, hM8, hM4, ⟨s, t, hMv⟩, hMne⟩ := exists_matrix v hv
  obtain ⟨y, hy, hn, hMy⟩ := h.exists_realize M hM
  have hconj : ∀ w, y * h.phi w * y⁻¹ = h.phi (M *ᵥ w) := fun w => by
    have := conj_coord h.bEq ⟨y, hn⟩ w
    rw [hMy] at this
    exact this
  have hM729 : M ^ 729 = M := by
    have e : 729 = 8 * 91 + 1 := by norm_num
    rw [e, pow_succ, pow_mul, hM8, one_pow, one_mul]
  have hu : ∀ w, y ^ 729 * h.phi w * (y ^ 729)⁻¹ = h.phi (M *ᵥ w) := by
    intro w
    rw [h.conj_pow_phi hconj, hM729]
  have hy5832 : y ^ 5832 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.closure (Set.range k)) (x := ⟨y, hy⟩)
    rw [hcard] at this
    exact congrArg Subtype.val this
  refine ⟨y ^ 729, Subgroup.pow_mem _ hy _, ?_, ?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h8 : (y ^ 729) ^ (2 ^ (2 + 1)) = 1 := by
      rw [← pow_mul]; exact hy5832
    have h4 : ¬ (y ^ 729) ^ (2 ^ 2) = 1 := by
      intro h4
      apply hM4
      have hall : ∀ w, M ^ 4 *ᵥ w = w := by
        intro w
        have h1 : (y ^ 729) ^ 4 * h.phi w * ((y ^ 729) ^ 4)⁻¹ = h.phi w := by
          have : (y ^ 729) ^ 4 = 1 := h4
          rw [this]; group
        have hM2916 : M ^ (729 * 4) = M ^ 4 := by
          have e : 729 * 4 = 8 * 364 + 4 := by norm_num
          rw [e, pow_add, pow_mul, hM8, one_pow, one_mul]
        have h2 : (y ^ 729) ^ 4 * h.phi w * ((y ^ 729) ^ 4)⁻¹ = h.phi (M ^ 4 *ᵥ w) := by
          rw [← pow_mul, h.conj_pow_phi hconj, hM2916]
        exact h.phi_inj (h2.symm.trans h1)
      exact matrix_eq_one_of_mulVec _ hall
    exact orderOf_eq_prime_pow h4 h8
  · rw [hu v, hMv, h.phi_add, h.phi_zsmul, h.phi_zsmul, ← h.phi_e3]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  · rw [hu v]
    intro heq
    exact hMne (h.phi_inj heq)

end J3Pkg

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
