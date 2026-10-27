module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly Matrix CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement MatrixGroups

private def mUniForm {d : ℕ} {F : Type} [Field F] (n : ℕ) (u v : Fin d → F) : F :=
  ∑ i, u i ^ (2 ^ n) * v i

private lemma vecMul_eq_transpose_mulVec {d : ℕ} {F : Type} [Field F]
    (M : Matrix (Fin d) (Fin d) F) (y : Fin d → F) :
    y ᵥ* M = Mᵀ *ᵥ y := by
  conv_lhs => rw [← Matrix.transpose_transpose M]
  rw [Matrix.vecMul_transpose]

private lemma gl_inv_mulVec_self {d : ℕ} {F : Type} [Field F] (P : GL (Fin d) F)
    (w : Fin d → F) :
    (((P⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) *ᵥ
        (((P : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]

private lemma gl_conj_mulVec {d : ℕ} {F : Type} [Field F] (P A : GL (Fin d) F)
    (v : Fin d → F) :
    (((P * A * P⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) *ᵥ v =
      ((P : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ
        (((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ
          ((((P⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) *ᵥ v)) := by
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

private lemma gl_conj_mulVec_self {d : ℕ} {F : Type} [Field F] (P A : GL (Fin d) F)
    (w : Fin d → F) :
    (((P * A * P⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) *ᵥ
        (((P : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ w) =
      ((P : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ
        (((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ w) := by
  rw [gl_conj_mulVec P A ((P : Matrix (Fin d) (Fin d) F) *ᵥ w),
    gl_inv_mulVec_self P w]

private theorem mUniForm_eq_dotProduct {d : ℕ} {F : Type} [Field F] [ExpChar F 2]
    (n : ℕ) (u v : Fin d → F) :
    mUniForm n u v = ((iterateFrobenius F 2 n) ∘ u) ⬝ᵥ v := by
  simp only [mUniForm, dotProduct, Function.comp_apply, iterateFrobenius_def]

private theorem mUniForm_conformal {n d : ℕ} {F : Type} [Field F] [ExpChar F 2]
    {A : GL (Fin d) F} {μ : F}
    (hA : ((A : Matrix (Fin d) (Fin d) F).map (· ^ (2 ^ n)))ᵀ *
      (A : Matrix (Fin d) (Fin d) F) = μ • 1) (u v : Fin d → F) :
    mUniForm n ((A : Matrix (Fin d) (Fin d) F) *ᵥ u)
        ((A : Matrix (Fin d) (Fin d) F) *ᵥ v) = μ * mUniForm n u v := by
  have hf : ∀ x : F, iterateFrobenius F 2 n x = x ^ (2 ^ n) :=
    fun x => iterateFrobenius_def (p := 2) (n := n) x
  have hA' : ((A : Matrix (Fin d) (Fin d) F).map (iterateFrobenius F 2 n))ᵀ *
      (A : Matrix (Fin d) (Fin d) F) = μ • 1 := by
    rw [show (A : Matrix (Fin d) (Fin d) F).map (iterateFrobenius F 2 n) =
        (A : Matrix (Fin d) (Fin d) F).map (· ^ (2 ^ n)) from by
      ext i j; exact hf _]
    exact hA
  have hmap : (iterateFrobenius F 2 n) ∘ ((A : Matrix (Fin d) (Fin d) F) *ᵥ u) =
      (A : Matrix (Fin d) (Fin d) F).map (iterateFrobenius F 2 n) *ᵥ
        ((iterateFrobenius F 2 n) ∘ u) := by
    ext i
    simpa only [Function.comp_def, Matrix.map_apply] using
      RingHom.map_mulVec (iterateFrobenius F 2 n) (A : Matrix (Fin d) (Fin d) F) u i
  rw [mUniForm_eq_dotProduct, mUniForm_eq_dotProduct, hmap]
  conv_lhs =>
    rw [dotProduct_comm, dotProduct_mulVec, vecMul_eq_transpose_mulVec, dotProduct_comm,
      Matrix.mulVec_mulVec, hA', Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]

private noncomputable def vecSupp {d : ℕ} {F : Type} [Field F]
    (v : Fin d → F) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter (fun i => v i ≠ 0)

private lemma mem_vecSupp {d : ℕ} {F : Type} [Field F] {v : Fin d → F} {i : Fin d} :
    i ∈ vecSupp v ↔ v i ≠ 0 := by
  classical
  simp [vecSupp]

theorem m_uni_repeated_weight {n d : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (P : GL (Fin d) F)
    (hP : P ∈ LargeEvenGUSet (Fin d) F (2 ^ n)) {G : Subgroup (GL (Fin d) F)}
    (hGU : ∀ A ∈ G, A ∈ LargeEvenGUSet (Fin d) F (2 ^ n)) (hdiag : MDiagAt d F P G)
    (R : Submodule F (Fin d → F)) (hR0 : R ≠ ⊥)
    (hRiso : ∀ u ∈ R, ∀ v ∈ R, ∑ i, (u i) ^ (2 ^ n) * v i = 0)
    (hRG : ∀ A ∈ G, ∀ v ∈ R, (A : Matrix (Fin d) (Fin d) F).mulVec v ∈ R) :
    ∃ a a' : Fin d, a ≠ a' ∧ ∀ A ∈ G, MWt P A a = MWt P A a' := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI hchar : CharP F 2 := by
    have hring : ringChar F = 2 := by
      rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hF]
      have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul]; ring_nf
      rw [h2, ← Nat.dvd_iff_mod_eq_zero]
      exact dvd_pow_self 2 (by omega)
    rw [← hring]
    exact ringChar.charP F
  obtain ⟨μ, _hμ0, _hμq, hPμ⟩ := hP
  let S : Set ℕ := {k | ∃ w ∈ R, w ≠ 0 ∧
    (vecSupp ((P : Matrix (Fin d) (Fin d) F) *ᵥ w)).card = k}
  have hSne : S.Nonempty := by
    obtain ⟨w, hwR, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR0
    exact ⟨_, w, hwR, hw0, rfl⟩
  let k : ℕ := sInf S
  have hkS : k ∈ S := Nat.sInf_mem hSne
  obtain ⟨w, hwR, hw0, hwk⟩ := hkS
  set v : Fin d → F := (P : Matrix (Fin d) (Fin d) F) *ᵥ w with hv
  have hv_ne : v ≠ 0 := by
    intro h0
    apply hw0
    calc w = ((P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ
          (((P : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ w) :=
          (gl_inv_mulVec_self P w).symm
      _ = ((P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v := by rw [← hv]
      _ = 0 := by rw [h0, Matrix.mulVec_zero]
  have hv_iso : mUniForm n v v = 0 := by
    rw [hv, mUniForm_conformal hPμ w w,
      show mUniForm n w w = 0 from hRiso w hwR w hwR, mul_zero]
  have hkey : ∀ A ∈ G, ∀ i₀ ∈ vecSupp v, ∀ i ∈ vecSupp v,
      MWt P A i = MWt P A i₀ := by
    intro A hA i₀ hi₀ i hi
    obtain ⟨D, hD⟩ := hdiag A hA
    have hMWt : ∀ j : Fin d, MWt P A j = D j := by
      intro j
      change ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) j j = D j
      rw [hD, Matrix.diagonal_apply_eq]
    set α : F := MWt P A i₀ with hαdef
    have hα : α = D i₀ := by rw [hαdef, hMWt i₀]
    set w' : Fin d → F := (A : Matrix (Fin d) (Fin d) F) *ᵥ w - α • w with hw'def
    have hw'R : w' ∈ R :=
      Submodule.sub_mem R (hRG A hA w hwR) (Submodule.smul_mem R α hwR)
    set u : Fin d → F := (P : Matrix (Fin d) (Fin d) F) *ᵥ w' with hudef
    have hu_eq : u = ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v
        - α • v := by
      rw [hudef, hw'def, hv, Matrix.mulVec_sub, Matrix.mulVec_smul,
        gl_conj_mulVec_self P A w]
    have hu_apply : ∀ j, u j = (D j - α) * v j := by
      intro j
      rw [hu_eq, Pi.sub_apply, Pi.smul_apply, hD, Matrix.mulVec_diagonal, smul_eq_mul]
      ring
    have hu0 : u i₀ = 0 := by
      rw [hu_apply i₀, hα, sub_self, zero_mul]
    by_contra hne
    have hu_ne : u ≠ 0 := by
      intro h0
      apply hne
      have hDi : D i = α := by
        have h := congrFun h0 i
        rw [hu_apply i, Pi.zero_apply] at h
        rcases mul_eq_zero.mp h with h1 | h1
        · exact sub_eq_zero.mp h1
        · exact absurd h1 (mem_vecSupp.mp hi)
      rw [hMWt i, hDi]
    have hw'ne : w' ≠ 0 := by
      intro h0
      apply hu_ne
      rw [hudef, h0, Matrix.mulVec_zero]
    have hmemS : (vecSupp u).card ∈ S := by
      refine ⟨w', hw'R, hw'ne, ?_⟩
      rw [hudef]
    have hle : k ≤ (vecSupp u).card := Nat.sInf_le hmemS
    have hsupp_sub : vecSupp u ⊆ vecSupp v := by
      intro j hj
      rw [mem_vecSupp] at hj ⊢
      intro hvj
      exact hj (by rw [hu_apply j, hvj, mul_zero])
    have hsupp_ssub : vecSupp u ⊂ vecSupp v := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsupp_sub, ?_⟩
      intro hEq
      have : i₀ ∈ vecSupp u := by rw [hEq]; exact hi₀
      rw [mem_vecSupp] at this
      exact this hu0
    have hsupp_lt : (vecSupp u).card < (vecSupp v).card := Finset.card_lt_card hsupp_ssub
    have hvk : (vecSupp v).card = k := by rw [hv, hwk]
    omega
  have hcard_ne_zero : (vecSupp v).card ≠ 0 := by
    intro h
    have hempty : vecSupp v = ∅ := Finset.card_eq_zero.mp h
    apply hv_ne
    funext j
    have hj : j ∉ vecSupp v := by rw [hempty]; exact Finset.notMem_empty j
    rw [mem_vecSupp] at hj
    by_contra hvj
    exact hj hvj
  have hcard_ne_one : (vecSupp v).card ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    have hva : v a ≠ 0 := by
      rw [← mem_vecSupp, ha]
      exact Finset.mem_singleton_self a
    have hsum : mUniForm n v v = v a ^ (2 ^ n) * v a := by
      change (∑ j, v j ^ (2 ^ n) * v j) = v a ^ (2 ^ n) * v a
      refine Finset.sum_eq_single a ?_ ?_
      · intro j _ hja
        have hvj : v j = 0 := by
          have hmem : j ∉ vecSupp v := by rw [ha]; simp [hja]
          rw [mem_vecSupp] at hmem
          by_contra hvj
          exact hmem hvj
        rw [hvj, mul_zero]
      · intro ha'; exact absurd (Finset.mem_univ a) ha'
    rw [hv_iso] at hsum
    exact (mul_ne_zero (pow_ne_zero (2 ^ n) hva) hva) hsum.symm
  have hcard_ge_two : 2 ≤ (vecSupp v).card := by omega
  obtain ⟨a, ha, a', ha', hane⟩ :=
    Finset.one_lt_card.mp (show 1 < (vecSupp v).card by omega)
  refine ⟨a, a', hane, ?_⟩
  intro A hA
  exact hkey A hA a' ha' a ha

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
