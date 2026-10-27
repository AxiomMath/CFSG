module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinSL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups

private theorem sq_entry_smul_one_add_smul_single {d : ℕ} {F : Type} [Field F]
    (c : F) {i j : Fin d} (hij : i ≠ j) :
    ((((c - 1) • (1 : Matrix (Fin d) (Fin d) F) +
      c • Matrix.single j i (1 : F)) ^ 2) j j) = (c - 1) ^ 2 := by
  rw [pow_two, Matrix.mul_apply, Finset.sum_eq_single j]
  · have h1 : ((c - 1) • (1 : Matrix (Fin d) (Fin d) F) +
        c • Matrix.single j i (1 : F)) j j = c - 1 := by
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.single_apply]
      simp [hij]
    rw [h1]
    ring
  · intro k _ hk
    have h2 : ((c - 1) • (1 : Matrix (Fin d) (Fin d) F) +
        c • Matrix.single j i (1 : F)) k j = 0 := by
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.single_apply]
      simp [hk, hij]
    rw [h2, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

private theorem conj_transvection_eq_self {d : ℕ} {F : Type} [Field F]
    {G Gi : Matrix (Fin d) (Fin d) F} (hGGi : G * Gi = 1) (hGiG : Gi * G = 1)
    {c : F} {i j : Fin d} (hij : i ≠ j)
    (h1 : G * (1 + Matrix.single j i (1 : F)) * Gi =
      (c : F) • (1 + Matrix.single j i (1 : F))) :
    G * Matrix.single j i (1 : F) = Matrix.single j i (1 : F) * G := by
  set E : Matrix (Fin d) (Fin d) F := Matrix.single j i (1 : F) with hE
  have h1' : 1 + G * E * Gi = c • (1 + E) := by
    rw [← h1]
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hGGi, Matrix.one_mul,
      Matrix.mul_assoc]
  have hc1 : c • (1 : Matrix (Fin d) (Fin d) F) = (c - 1) • 1 + 1 := by
    conv_lhs => rw [← sub_add_cancel c 1]
    rw [add_smul, one_smul]
  have hX : c • (1 : Matrix (Fin d) (Fin d) F) + c • E = ((c - 1) • 1 + c • E) + 1 := by
    rw [hc1]; abel
  have hsplit : c • (1 + E) = c • (1 : Matrix (Fin d) (Fin d) F) + c • E := by
    rw [smul_add]
  have hM : G * E * Gi = (c - 1) • (1 : Matrix (Fin d) (Fin d) F) + c • E := by
    have hM' : G * E * Gi = c • (1 : Matrix (Fin d) (Fin d) F) + c • E - 1 := by
      rw [← hsplit, ← h1']; abel
    rw [hM', hX]; abel
  have hsq : (G * E * Gi) ^ 2 = 0 := by
    rw [pow_two]
    calc G * E * Gi * (G * E * Gi)
        = G * E * (Gi * G) * E * Gi := by simp only [Matrix.mul_assoc]
      _ = G * E * 1 * E * Gi := by rw [hGiG]
      _ = G * (E * E) * Gi := by simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by
        have hEE : E * E = 0 := by
          rw [hE]
          simp [Matrix.single_mul_single_of_ne, hij]
        simp [hEE]
  have hc1' : c = 1 := by
    have h := congrFun (congrFun hsq j) j
    rw [hM, hE] at h
    rw [sq_entry_smul_one_add_smul_single c hij] at h
    have : c - 1 = 0 := by
      rw [pow_two] at h
      exact mul_self_eq_zero.mp h
    exact sub_eq_zero.mp this
  have hME : G * E * Gi = E := by
    rw [hM, hc1']
    simp
  have hGEG : G * E = E * G := by
    have h := congrArg (fun x : Matrix (Fin d) (Fin d) F => x * G) hME
    simpa only [Matrix.mul_assoc, hGiG, Matrix.mul_one] using h
  rw [hE] at hGEG
  exact hGEG

private theorem entry_eq_zero_of_mul_eq_of_diag {d : ℕ} {F : Type} [Field F]
    {A : Matrix (Fin d) (Fin d) F} (hA : ∀ i j : Fin d, i ≠ j → A i j = 0)
    {G : Matrix (Fin d) (Fin d) F} (h : G * A = A * G) {i j : Fin d}
    (hij : A i i ≠ A j j) : G i j = 0 := by
  have h1 : (G * A) i j = G i j * A j j := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_single j (fun k _ hk => by rw [hA k j hk, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)
  have h2 : (A * G) i j = A i i * G i j := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_single i (fun k _ hk => by rw [hA i k (fun h => hk h.symm), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)
  have hh := congrFun (congrFun h i) j
  rw [h1, h2] at hh
  have hz : (A i i - A j j) * G i j = 0 := by
    rw [sub_mul, mul_comm (A j j) (G i j), hh, sub_self]
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hij
  · exact h0

private theorem entry_eq_zero_of_comm_blocks {d : ℕ} {F : Type} [Field F]
    {a g : ↥(LinSL d F)}
    (hcomm : ∀ I : Finset (Fin d), LinLevelSet (a : GL (Fin d) F) I → 2 ≤ I.card →
      ∀ e ∈ LinBlockSub d F I, e * LinMk d F g = LinMk d F g * e)
    {i j : Fin d} (hij : i ≠ j)
    (hval : ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i =
      ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) j j) :
    ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = 0 := by
  classical
  let A : Matrix (Fin d) (Fin d) F := ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
  let G : Matrix (Fin d) (Fin d) F := ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
  let Gi : Matrix (Fin d) (Fin d) F :=
    (((g : GL (Fin d) F)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
  let I : Finset (Fin d) := Finset.univ.filter
    (fun k => ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) k k =
      ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i)
  have hI_mem_i : i ∈ I := by simp [I]
  have hI_mem_j : j ∈ I := by simp [I, hval]
  have hlevel : LinLevelSet (a : GL (Fin d) F) I := by
    refine ⟨⟨i, hI_mem_i⟩, ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i, fun k => ?_⟩
    simp [I]
  have hcard : 2 ≤ I.card := by
    have hsub : ({i, j} : Finset (Fin d)) ⊆ I := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hI_mem_i
      · exact hI_mem_j
    have h2 : ({i, j} : Finset (Fin d)).card = 2 := Finset.card_pair_eq_two_iff.mpr hij
    rw [← h2]
    exact Finset.card_le_card hsub
  have hji : j ≠ i := hij.symm
  let t : Matrix.SpecialLinearGroup (Fin d) F := Matrix.SpecialLinearGroup.transvection hji 1
  let tGL : GL (Fin d) F := Matrix.SpecialLinearGroup.toGL t
  have htGL_mem : tGL ∈ LinSL d F := by
    change tGL ∈ LargeEvenSLGroup (Fin d) F
    rw [largeEvenSLGroup_eq_statedSL d, StatedAPI.statedSL_eq_range_toGL d F]
    exact ⟨t, rfl⟩
  have htGL_block : tGL ∈ LinBlockGrp d F I := by
    refine ⟨htGL_mem, fun p q hpq => ?_⟩
    have htmat : (tGL : Matrix (Fin d) (Fin d) F) = 1 + Matrix.single j i (1 : F) := by
      change (t : Matrix (Fin d) (Fin d) F) = 1 + Matrix.single j i (1 : F)
      rw [Matrix.SpecialLinearGroup.transvection_coe]
    rw [htmat, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have hne : ¬ (j = p ∧ i = q) := by
      rintro ⟨hp, hq⟩
      exact hpq.elim (fun h => h (hp ▸ hI_mem_j)) (fun h => h (hq ▸ hI_mem_i))
    rw [if_neg hne, add_zero]
  let e0 : ↥(LinSL d F) := ⟨tGL, htGL_mem⟩
  have he0mem : e0 ∈ (LinBlockGrp d F I).subgroupOf (LinSL d F) :=
    Subgroup.mem_subgroupOf.mpr htGL_block
  have he0sub : LinMk d F e0 ∈ LinBlockSub d F I := ⟨e0, he0mem, rfl⟩
  have hcommI : LinMk d F e0 * LinMk d F g = LinMk d F g * LinMk d F e0 :=
    hcomm I hlevel hcard (LinMk d F e0) he0sub
  have hz0ker : g * e0 * g⁻¹ * e0⁻¹ ∈ (LinMk d F).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [← hcommI]
    group
  have hz0sub : g * e0 * g⁻¹ * e0⁻¹ ∈
      (LargeEvenScalars (Fin d) F).subgroupOf (LinSL d F) := by
    have h : g * e0 * g⁻¹ * e0⁻¹ ∈
        (QuotientGroup.mk' ((LargeEvenScalars (Fin d) F).subgroupOf (LinSL d F))).ker :=
      hz0ker
    rwa [QuotientGroup.ker_mk'] at h
  have hz0scal : ((g * e0 * g⁻¹ * e0⁻¹ : ↥(LinSL d F)) : GL (Fin d) F) ∈
      LargeEvenScalars (Fin d) F := Subgroup.mem_subgroupOf.mp hz0sub
  rw [largeEvenScalars_def] at hz0scal
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hz0scal
  have hGconj : (g : GL (Fin d) F) * (e0 : GL (Fin d) F) * (g : GL (Fin d) F)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin d) c * (e0 : GL (Fin d) F) := by
    have hz0prod : ((g * e0 * g⁻¹ * e0⁻¹ : ↥(LinSL d F)) : GL (Fin d) F) =
        (g : GL (Fin d) F) * (e0 : GL (Fin d) F) * (g : GL (Fin d) F)⁻¹ *
          (e0 : GL (Fin d) F)⁻¹ := rfl
    have h := hc.symm
    rw [hz0prod] at h
    have h2 := congrArg (fun x : GL (Fin d) F => x * (e0 : GL (Fin d) F)) h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h2
  have he0mat : ((e0 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      1 + Matrix.single j i (1 : F) := by
    change (t : Matrix (Fin d) (Fin d) F) = 1 + Matrix.single j i (1 : F)
    rw [Matrix.SpecialLinearGroup.transvection_coe]
  have hscalar : (Matrix.GeneralLinearGroup.scalar (Fin d) c : Matrix (Fin d) (Fin d) F) =
      (c : F) • (1 : Matrix (Fin d) (Fin d) F) := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  have hmat : G * (1 + Matrix.single j i (1 : F)) * Gi =
      (c : F) • (1 + Matrix.single j i (1 : F)) := by
    have h := congrArg (fun x : GL (Fin d) F => (x : Matrix (Fin d) (Fin d) F)) hGconj
    simpa only [Units.val_mul, hscalar, he0mat, Matrix.smul_mul, Matrix.one_mul] using h
  have hGiG : Gi * G = 1 := by
    show (((g : GL (Fin d) F)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
      ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1
    exact Units.inv_mul (g : GL (Fin d) F)
  have hGGi : G * Gi = 1 := by
    show ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
      (((g : GL (Fin d) F)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1
    exact Units.mul_inv (g : GL (Fin d) F)
  have hGE := conj_transvection_eq_self hGGi hGiG hij hmat
  have hR : (Matrix.single j i (1 : F) * G) i i = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.single_apply]
    have hne : ¬ (j = i ∧ i = k) := fun hc => hij hc.1.symm
    rw [if_neg hne, zero_mul]
  have hh := congrFun (congrFun hGE i) i
  rw [Matrix.mul_single_apply_same] at hh
  rw [hR, mul_one] at hh
  exact hh

theorem lin_cent_blocks_diag {d : ℕ} {F : Type} [Field F] {a : ↥(LinSL d F)}
    (hdiag : ∀ i j : Fin d, i ≠ j → ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = 0)
    {g : ↥(LinSL d F)} (hga : (g : GL (Fin d) F) * a = a * g)
    (hcomm : ∀ I : Finset (Fin d), LinLevelSet (a : GL (Fin d) F) I → 2 ≤ I.card →
      ∀ e ∈ LinBlockSub d F I, e * LinMk d F g = LinMk d F g * e) :
    LinMk d F g ∈ LinDiagImage d F := by
  have hga_mat : ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
      ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
      ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
    have h := congrArg (fun x : GL (Fin d) F => (x : Matrix (Fin d) (Fin d) F)) hga
    simpa only [Units.val_mul] using h
  refine ⟨g, fun i j hij => ?_, rfl⟩
  by_cases hval : ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i =
      ((a : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) j j
  · exact entry_eq_zero_of_comm_blocks hcomm hij hval
  · exact entry_eq_zero_of_mul_eq_of_diag hdiag hga_mat hval

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
