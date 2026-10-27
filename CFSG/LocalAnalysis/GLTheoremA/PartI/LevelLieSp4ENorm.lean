module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4EMat
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E

open Matrix

variable {K : Type} [Field K] [CharP K 2]

section Classify

variable {K : Type} [Field K] [CharP K 2]

theorem neg_vec (x : Ix → K) : -x = x := funext fun i => CharTwo.neg_eq (x i)

theorem finrank_sum (A : Matrix Ix Ix K) :
    Module.finrank K (LinearMap.range (Matrix.mulVecLin (Pm A))) + Module.finrank K (Wsp A) = 4 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (Pm A))
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h
  exact h

theorem eigen_contra [Fintype K] (hcard : Fintype.card K = 8) {A : Matrix Ix Ix K} {u : Ix → K}
    (hu : u ≠ 0) (hPu : Pm A *ᵥ u = 0) {l : K} (hl : A *ᵥ u = l • u) : False := by
  have h := hPu
  unfold Pm at h
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hl,
    Matrix.mulVec_smul, hl] at h
  have h2 : (l * l + l + 1) • u = 0 := by
    calc (l * l + l + 1) • u = l • (l • u) + l • u + u := by module
      _ = 0 := h
  rcases smul_eq_zero.1 h2 with h4 | h4
  · exact no_root hcard l h4
  · exact hu h4

theorem finrank_Wsp_eq_two [Fintype K] (hcard : Fintype.card K = 8) {A : Matrix Ix Ix K}
    (hsp : Aᵀ * JJ K * A = JJ K) (h3 : A * A * A = 1)
    (hP0 : Pm A ≠ 0) (hP1 : Pm A ≠ 1) : Module.finrank K (Wsp A) = 2 := by
  have hs := finrank_sum A
  have hV : Module.finrank K (Ix → K) = 4 := by simp
  have hd4 : Module.finrank K (Wsp A) ≤ 4 := by omega
  have h0 : Module.finrank K (Wsp A) ≠ 0 := by
    intro hd
    rw [Submodule.finrank_eq_zero] at hd
    apply hP1
    apply Matrix.ext_iff_mulVec.2
    intro x
    have hx : x + Pm A *ᵥ x ∈ Wsp A := Wsp_split h3 x
    rw [hd, Submodule.mem_bot] at hx
    rw [Matrix.one_mulVec]
    calc Pm A *ᵥ x = x + Pm A *ᵥ x + x := (vec_add_self_add x (Pm A *ᵥ x)).symm
      _ = x := by rw [hx, zero_add]
  have h4 : Module.finrank K (Wsp A) ≠ 4 := by
    intro hd
    have htop : Wsp A = ⊤ := Submodule.eq_top_of_finrank_eq (hd.trans hV.symm)
    apply hP0
    apply Matrix.ext_iff_mulVec.2
    intro x
    have hx : x ∈ Wsp A := by rw [htop]; exact Submodule.mem_top
    rw [mem_Wsp] at hx
    rw [Matrix.zero_mulVec, hx]
  have h1 : Module.finrank K (Wsp A) ≠ 1 := by
    intro hd
    obtain ⟨v, hv0, hall⟩ := finrank_eq_one_iff'.1 hd
    have hvW : (v : Ix → K) ∈ Wsp A := v.2
    obtain ⟨c, hc⟩ := hall ⟨A *ᵥ (v : Ix → K), Wsp_A h3 hvW⟩
    have hc' : A *ᵥ (v : Ix → K) = c • (v : Ix → K) := by
      have := congrArg Subtype.val hc
      simpa using this.symm
    have hv' : (v : Ix → K) ≠ 0 := fun h => hv0 (Subtype.ext h)
    exact eigen_contra hcard hv' (mem_Wsp.1 hvW) hc'
  have h3' : Module.finrank K (Wsp A) ≠ 3 := by
    intro hd
    have hV1 : Module.finrank K (LinearMap.range (Matrix.mulVecLin (Pm A))) = 1 := by omega
    obtain ⟨v, hv0, hall⟩ := finrank_eq_one_iff'.1 hV1
    have hvR : (v : Ix → K) ∈ LinearMap.range (Matrix.mulVecLin (Pm A)) := v.2
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hvR
    rw [Matrix.mulVecLin_apply] at hy
    have hPv : Pm A *ᵥ (v : Ix → K) = v := by
      rw [← hy, Pm_mulVec_Pm h3 y]
    have hbf : ∀ x, bf (v : Ix → K) x = 0 := by
      intro x
      have hPx : Pm A *ᵥ x ∈ LinearMap.range (Matrix.mulVecLin (Pm A)) :=
        ⟨x, by simp [Matrix.mulVecLin_apply]⟩
      obtain ⟨c, hc⟩ := hall ⟨Pm A *ᵥ x, hPx⟩
      have hc' : Pm A *ᵥ x = c • (v : Ix → K) := by
        have := congrArg Subtype.val hc
        simpa using this.symm
      have h1' : bf (v : Ix → K) (Pm A *ᵥ x) = 0 := by
        rw [hc', bf_smul_right, bf_self_zero, mul_zero]
      have h2' : bf (v : Ix → K) (x + Pm A *ᵥ x) = 0 :=
        bf_fix_W' hsp h3 hPv (Wsp_split h3 x)
      have hsplit := congrArg (bf (v : Ix → K)) (split_vec (A := A) x)
      rw [bf_add_right, h1', h2', add_zero] at hsplit
      exact hsplit
    exact hv0 (Subtype.ext (bf_eq_zero_of_forall _ hbf))
  omega

theorem exists_u [Fintype K] (hcard : Fintype.card K = 8) {A : Matrix Ix Ix K}
    (hsp : Aᵀ * JJ K * A = JJ K) (h3 : A * A * A = 1) (hd2 : Module.finrank K (Wsp A) = 2) :
    ∃ u : Ix → K, Pm A *ᵥ u = 0 ∧ u ≠ 0 ∧ bf u (A *ᵥ u) ≠ 0 := by
  have hWne : Wsp A ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hd2
    exact absurd hd2 (by norm_num)
  obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have huP : Pm A *ᵥ u = 0 := mem_Wsp.1 huW
  refine ⟨u, huP, hu0, ?_⟩
  intro hbf0
  have hli : LinearIndependent K ![u, A *ᵥ u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      rcases hst with hs | hs
      · exact ⟨hs, rfl⟩
      · exact absurd hs hu0
    · exfalso
      have h' : t • (A *ᵥ u) = -(s • u) := eq_neg_of_add_eq_zero_right hst
      have hAu : A *ᵥ u = (-s * t⁻¹) • u := by
        calc A *ᵥ u = t⁻¹ • (t • (A *ᵥ u)) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-s * t⁻¹) • u := by rw [h']; module
      exact eigen_contra hcard hu0 huP hAu
  have hall : ∀ x ∈ Wsp A, bf u x = 0 := by
    intro x hx
    have hspan : Submodule.span K (Set.range ![u, A *ᵥ u]) = Wsp A := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact huW
        · exact Wsp_A h3 huW
      · rw [finrank_span_eq_card hli, hd2]
        rfl
    have hx' : x ∈ Submodule.span K (Set.range ![u, A *ᵥ u]) := hspan ▸ hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx'
    rw [← hc, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [bf_add_right, bf_smul_right, bf_smul_right, bf_self_zero, hbf0]
    ring
  apply hu0
  apply bf_eq_zero_of_forall
  intro y
  have hsplit := congrArg (bf u) (split_vec (A := A) y)
  rw [bf_add_right] at hsplit
  have h1 : bf u (Pm A *ᵥ y) = 0 := bf_fix_W'' hsp h3 (Pm_mulVec_Pm h3 y) huW
  have h2 : bf u (y + Pm A *ᵥ y) = 0 := hall _ (Wsp_split h3 y)
  rw [h1, h2, add_zero] at hsplit
  exact hsplit

theorem exists_normal_vectors [Fintype K] (hcard : Fintype.card K = 8) {A : Matrix Ix Ix K}
    (hsp : Aᵀ * JJ K * A = JJ K) (h3 : A * A * A = 1) (hP0 : Pm A ≠ 0) (hP1 : Pm A ≠ 1) :
    ∃ v w u : Ix → K, A *ᵥ v = v ∧ A *ᵥ w = w ∧ bf v w = 1 ∧ Pm A *ᵥ u = 0 ∧
      bf u (A *ᵥ u) ≠ 0 := by
  obtain ⟨u, huP, -, hbf⟩ := exists_u hcard hsp h3 (finrank_Wsp_eq_two hcard hsp h3 hP0 hP1)
  obtain ⟨y, hy⟩ : ∃ y, Pm A *ᵥ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hP0 (Matrix.ext_iff_mulVec.2 fun x => by simp [h x])
  have hv₀P : Pm A *ᵥ (Pm A *ᵥ y) = Pm A *ᵥ y := Pm_mulVec_Pm h3 y
  have hAv₀ : A *ᵥ (Pm A *ᵥ y) = Pm A *ᵥ y := A_mulVec_Pm h3 y
  obtain ⟨z, hz⟩ : ∃ z, bf (Pm A *ᵥ y) z ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (bf_eq_zero_of_forall _ h)
  have hz2 := congrArg (bf (Pm A *ᵥ y)) (split_vec (A := A) z)
  rw [bf_add_right, bf_fix_W' hsp h3 hv₀P (Wsp_split h3 z), add_zero] at hz2
  have hc1 : bf (Pm A *ᵥ y) (Pm A *ᵥ z) ≠ 0 := by rw [← hz2]; exact hz
  refine ⟨Pm A *ᵥ y, (bf (Pm A *ᵥ y) (Pm A *ᵥ z))⁻¹ • (Pm A *ᵥ z), u, hAv₀, ?_, ?_, huP, hbf⟩
  · rw [Matrix.mulVec_smul, A_mulVec_Pm h3]
  · rw [bf_smul_right, inv_mul_cancel₀ hc1]

end Classify

section NormalForm

variable {K : Type} [Field K] [CharP K 2]

@[expose] def basisVec (v w u u' : Ix → K) : Ix → Ix → K := Sum.elim ![v, u] ![w, u']

theorem gram_entry (e : Ix → Ix → K) (M : Matrix Ix Ix K) (b b' : Ix) :
    ((Matrix.of fun a c => e c a)ᵀ * M * Matrix.of fun a c => e c a) b b' =
      e b ⬝ᵥ (M *ᵥ e b') := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem exists_conj_planeMat [Fintype K] (hcard : Fintype.card K = 8) {A : Matrix Ix Ix K}
    (hsp : Aᵀ * JJ K * A = JJ K) (h3 : A * A * A = 1) (hP0 : Pm A ≠ 0) (hP1 : Pm A ≠ 1) :
    ∃ (c : K) (g : GL Ix K), c ≠ 0 ∧ (g : Matrix Ix Ix K)ᵀ * JJ K * (g : Matrix Ix Ix K) = JJ K ∧
      A * (g : Matrix Ix Ix K) = (g : Matrix Ix Ix K) * planeMat ![1, Tmat c] := by
  obtain ⟨v, w, u, hv, hw, hvw, huP, hbf⟩ := exists_normal_vectors hcard hsp h3 hP0 hP1
  set c := bf u (A *ᵥ u) with hcdef
  have hc : c ≠ 0 := hbf
  set u' := c⁻¹ • (A *ᵥ u) with hu'def
  have hPv : Pm A *ᵥ v = v := Pm_fix_of_fixed hv
  have hPw : Pm A *ᵥ w = w := Pm_fix_of_fixed hw
  have hWu : u ∈ Wsp A := mem_Wsp.2 huP
  have hWu' : u' ∈ Wsp A := Submodule.smul_mem _ _ (Wsp_A h3 hWu)
  have hAAu : A *ᵥ (A *ᵥ u) = A *ᵥ u + u := by
    have h := huP
    unfold Pm at h
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h
    have h' : A *ᵥ (A *ᵥ u) = -(A *ᵥ u + u) :=
      eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact h)
    rw [h', neg_vec]
  have hAu' : A *ᵥ u' = u' + c⁻¹ • u := by
    rw [hu'def, Matrix.mulVec_smul, hAAu, smul_add]
  have hAu_eq : A *ᵥ u = c • u' := by
    rw [hu'def, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hb_uu' : bf u u' = 1 := by
    rw [hu'def, bf_smul_right, inv_mul_cancel₀ hc]
  have hbv_u : bf v u = 0 := bf_fix_W' hsp h3 hPv hWu
  have hbv_u' : bf v u' = 0 := bf_fix_W' hsp h3 hPv hWu'
  have hbw_u : bf w u = 0 := bf_fix_W' hsp h3 hPw hWu
  have hbw_u' : bf w u' = 0 := bf_fix_W' hsp h3 hPw hWu'
  have hbw_v : bf w v = 1 := by rw [bf_comm, hvw]
  have hbu'_u : bf u' u = 1 := by rw [bf_comm, hb_uu']
  have hbu_v : bf u v = 0 := by rw [bf_comm, hbv_u]
  have hbu'_v : bf u' v = 0 := by rw [bf_comm, hbv_u']
  have hbu_w : bf u w = 0 := by rw [bf_comm, hbw_u]
  have hbu'_w : bf u' w = 0 := by rw [bf_comm, hbw_u']
  have hG : ∀ b b' : Ix, bf (basisVec v w u u' b) (basisVec v w u u' b') = JJ K b b' := by
    intro b b'
    rcases b with i | i <;> rcases b' with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [basisVec, JJ, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, bf_self_zero, hvw, hbw_v, hb_uu',
        hbu'_u, hbv_u, hbv_u', hbw_u, hbw_u', hbu_v, hbu'_v, hbu_w, hbu'_w, CharTwo.neg_eq]
  set gM : Matrix Ix Ix K := Matrix.of fun a b => basisVec v w u u' b a with hgMdef
  have hgram : gMᵀ * JJ K * gM = JJ K := by
    ext b b'
    rw [hgMdef, gram_entry]
    exact hG b b'
  set hM : Matrix Ix Ix K := JJ K * gMᵀ * JJ K with hhM
  have hhg : hM * gM = 1 := by
    calc hM * gM = JJ K * (gMᵀ * JJ K * gM) := by rw [hhM]; simp only [Matrix.mul_assoc]
      _ = JJ K * JJ K := by rw [hgram]
      _ = 1 := JJ_mul_JJ
  have hgh : gM * hM = 1 := mul_eq_one_comm.1 hhg
  have key : ∀ b : Ix, A *ᵥ basisVec v w u u' b =
      ∑ k : Ix, planeMat ![1, Tmat c] k b • basisVec v w u u' k := by
    intro b
    rcases b with i | i
    · fin_cases i
      · simp [basisVec, planeMat, Tmat, plane, pos, Fintype.sum_sum_type, Fin.sum_univ_two, hv]
      · simp [basisVec, planeMat, Tmat, plane, pos, Fintype.sum_sum_type, Fin.sum_univ_two,
          hAu_eq]
    · fin_cases i
      · simp [basisVec, planeMat, Tmat, plane, pos, Fintype.sum_sum_type, Fin.sum_univ_two, hw]
      · simp [basisVec, planeMat, Tmat, plane, pos, Fintype.sum_sum_type, Fin.sum_univ_two,
          hAu', add_comm]
  refine ⟨c, ⟨gM, hM, hgh, hhg⟩, hc, hgram, ?_⟩
  ext a b
  have hk := congrFun (key b) a
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk
  simp only [Matrix.mul_apply, hgMdef, Matrix.of_apply]
  rw [hk]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end NormalForm

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
