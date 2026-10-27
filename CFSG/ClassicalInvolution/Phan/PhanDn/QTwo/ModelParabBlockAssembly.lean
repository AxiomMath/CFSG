module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabBlockFactor
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabChainLevi
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabBlockProduct
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabTorus

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg
open Matrix

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

private theorem su_one_subsingleton : Subsingleton (Su K 2 1 1) := by
  constructor
  intro x y
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i
  fin_cases j
  have hx : (((x : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K)) 0 0 = 1 := by
    have hxdet := ((mem_SUid_iff (unitaryInvolution K 2 1)).mp x.2).1
    simpa [Matrix.det_fin_one] using hxdet
  have hydet : (((y : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K)) 0 0 = 1 := by
    have hydet := ((mem_SUid_iff (unitaryInvolution K 2 1)).mp y.2).1
    simpa [Matrix.det_fin_one] using hydet
  change (((x : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) 0 0) =
    (((y : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) 0 0)
  rw [hx, hydet]


theorem qTwo_su_prod_of_intervals (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (k b : ι → ℕ) (hk : ∀ a, 0 < k a) (hbk : ∀ a, b a + k a ≤ m + 1)
    (hdisj : ∀ a c, a ≠ c → b a + k a ≤ b c ∨ b c + k c ≤ b a)
    (hcover : ∀ j : Fin (m + 1), ∃ a, b a ≤ j.val ∧ j.val < b a + k a)
    {C : Set (Fin (m + 1))}
    (hC : ∀ a, ∀ j : Fin (k a - 1),
      (⟨b a + j.val, by have hb := hbk a; have hj := j.isLt; omega⟩ : Fin (m + 1)) ∈ C)
    (s : Su K 2 1 (m + 1))
    (hoff : ∀ a (i : Fin (m + 1)) (j : Fin (k a)),
      (i.val < b a ∨ b a + k a ≤ i.val) →
        (((s : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K))
          i ⟨b a + j.val, by have hb := hbk a; have hj := j.isLt; omega⟩ = 0) :
    ∃ t ∈ ⨆ i, qTwoTor E m hm i,
      ∃ l ∈ (qTwoStdFamily E hK m hm).levi C,
        suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s =
          (t : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) *
            (l : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) := by
  classical
  let σ := unitaryInvolution K 2 1
  let sM : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    ((s : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
  have hs_unitary : conjTr σ sM * sM = 1 := by
    apply conjTr_mul_self_of_isometry σ
    exact ((mem_SUid_iff σ).mp s.2).2
  have hfac_exists : ∀ a, ∃ (d : Fin (k a) → normOne σ) (u : Su K 2 1 (k a)),
      ∀ i j : Fin (k a),
        sM (⟨b a + i.val, by have hb := hbk a; have hi := i.isLt; omega⟩ : Fin (m + 1))
          (⟨b a + j.val, by have hb := hbk a; have hj := j.isLt; omega⟩ : Fin (m + 1)) =
          (((d i : normOne σ) : Kˣ) : K) *
            (((u : GL (Fin (k a)) K) : Matrix (Fin (k a)) (Fin (k a)) K) i j) := by
    intro a
    exact qTwo_unitary_interval_factor (K := K) (n := m + 1) (k := k a) (b := b a)
      (hk a) (hbk a) sM hs_unitary (hoff a)
  choose d u hfac using hfac_exists
  let pick : Fin (m + 1) → ι := fun j => Classical.choose (hcover j)
  have hpick : ∀ j : Fin (m + 1),
      b (pick j) ≤ j.val ∧ j.val < b (pick j) + k (pick j) :=
    fun j => Classical.choose_spec (hcover j)
  let dglob : Fin (m + 1) → normOne σ := fun j =>
    d (pick j) ⟨j.val - b (pick j), by have h1 := (hpick j).1; have h2 := (hpick j).2; omega⟩
  have hdglob_block : ∀ (a : ι) (i : Fin (k a)),
      dglob (⟨b a + i.val, by have hb := hbk a; have hi := i.isLt; omega⟩ : Fin (m + 1)) = d a i := by
    intro a i
    let j : Fin (m + 1) := ⟨b a + i.val, by have hb := hbk a; have hi := i.isLt; omega⟩
    have hj : b a ≤ j.val ∧ j.val < b a + k a := by
      have hb := hbk a
      have hi := i.isLt
      simp only [j, Fin.val_mk]
      constructor <;> omega
    have hpa : pick j = a := by
      by_contra hne
      have hp := hpick j
      rcases hdisj a (pick j) (Ne.symm hne) with hle | hle <;> omega
    let idx : Fin (k (pick j)) := ⟨j.val - b (pick j), by
      have hp := hpick j; omega⟩
    have hk_eq : k (pick j) = k a := congrArg k hpa
    have hidx : HEq idx i := by
      apply (Fin.heq_ext_iff hk_eq).mpr
      simp only [idx, Fin.val_mk]
      have hjv : j.val = b a + i.val := by simp [j]
      have hb_eq : b (pick j) = b a := congrArg b hpa
      omega
    have hsigma : (⟨pick j, idx⟩ : Sigma fun x => Fin (k x)) = ⟨a, i⟩ := by
      refine Sigma.ext hpa ?_
      exact hidx
    have hd := congrArg (fun p : Sigma fun x => Fin (k x) => d p.1 p.2) hsigma
    simpa [dglob, idx] using hd

  let U : Su K 2 1 (m + 1) := qTwo_blockProduct (m + 1) k b hbk hdisj u
  let UM : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    ((U : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
  let D : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    Matrix.diagonal fun j => (((dglob j : normOne σ) : Kˣ) : K)
  have hmatrix : sM = D * UM := by
    ext i j
    let a : ι := pick j
    have hja : b a ≤ j.val ∧ j.val < b a + k a := hpick j
    let j' : Fin (k a) := ⟨j.val - b a, by omega⟩
    let col : Fin (m + 1) := ⟨b a + j'.val, by
      have hb := hbk a; have hj := j'.isLt; omega⟩
    have hja_col : b a ≤ col.val ∧ col.val < b a + k a := by
      constructor
      · simp [col]
      · simpa [col] using j'.isLt
    have hcol : col = j := by
      apply Fin.ext
      simp [col, j']
      omega
    rw [← hcol]
    have hcol_single : (⟨b a + j'.val, by
        have hb := hbk a; have hj := j'.isLt; omega⟩ : Fin (m + 1)) = col := rfl
    have hUcol := qTwo_blockProduct_single (K := K) (n := m + 1) (k := k) (b := b)
      (hbk := hbk) (hdisj := hdisj) (u := u) a col hja_col
    have hUentry : UM i col =
        (((blockEmb K 2 1 (m + 1) (k a) (b a) (hbk a) (u a) :
          GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i col) := by
      have hcoord := congrFun hUcol i
      simpa [U, UM, CFSG.ClassicalGroups.Unitary.smul_def,
        Matrix.mulVec_single_one, Matrix.col_apply] using hcoord
    have hblock_entry :
        (((blockEmb K 2 1 (m + 1) (k a) (b a) (hbk a) (u a) :
          GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i col) =
          if hi : b a ≤ i.val ∧ i.val < b a + k a then
            (((u a : GL (Fin (k a)) K) : Matrix (Fin (k a)) (Fin (k a)) K)
              ⟨i.val - b a, by omega⟩ j') else 0 := by
      rw [coe_coe_blockEmb]
      by_cases hi : b a ≤ i.val ∧ i.val < b a + k a
      · rw [dif_pos hi, blockMat_apply, dif_pos ⟨hi, hja_col⟩]
        have hcol_idx : (⟨col.val - b a, by omega⟩ : Fin (k a)) = j' := by
          apply Fin.ext
          simp [col]
        rw [hcol_idx]
      · rw [dif_neg hi]
        rw [blockMat_apply_of_not_mem_left (F := K) (m := m + 1) (k := k a) (i := b a)
          (((u a : GL (Fin (k a)) K) : Matrix (Fin (k a)) (Fin (k a)) K)) hi]
        have hne : i ≠ col := by
          intro h
          apply hi
          rw [h]
          exact hja_col
        simp [Matrix.one_apply, hne]
    by_cases hi : b a ≤ i.val ∧ i.val < b a + k a
    · have hleft : sM i col =
          (((d a ⟨i.val - b a, by omega⟩ : normOne σ) : Kˣ) : K) *
            (((u a : GL (Fin (k a)) K) : Matrix (Fin (k a)) (Fin (k a)) K)
              ⟨i.val - b a, by omega⟩ j') := by
        have h := hfac a ⟨i.val - b a, by omega⟩ j'
        have hi_eq : i = blockIdx (b a) (hbk a) ⟨i.val - b a, by omega⟩ := by
          apply Fin.ext
          simp [blockIdx]
          omega
        convert h using 2
        apply Fin.ext
        simp [blockIdx]
        omega
      have hdiag : dglob i = d a ⟨i.val - b a, by omega⟩ := by
        have hi_eq : i = blockIdx (b a) (hbk a) ⟨i.val - b a, by omega⟩ := by
          apply Fin.ext
          simp [blockIdx]
          omega
        convert hdglob_block a ⟨i.val - b a, by omega⟩ using 2
        apply Fin.ext
        simp [blockIdx]
        omega
      calc
        sM i col = (((d a ⟨i.val - b a, by omega⟩ : normOne σ) : Kˣ) : K) *
            (((u a : GL (Fin (k a)) K) : Matrix (Fin (k a)) (Fin (k a)) K)
              ⟨i.val - b a, by omega⟩ j') := hleft
        _ = (((dglob i : normOne σ) : Kˣ) : K) *
            (((u a : GL (Fin (k a)) K) : Matrix (Fin (k a)) (Fin (k a)) K)
              ⟨i.val - b a, by omega⟩ j') := by rw [hdiag]
        _ = (D * UM) i col := by
          rw [Matrix.diagonal_mul, hUentry, hblock_entry, dif_pos hi]
    · have hout : i.val < b a ∨ b a + k a ≤ i.val := by omega
      have hleft : sM i col = 0 := by
        have h := hoff a i j' hout
        exact h
      calc
        sM i col = 0 := hleft
        _ = (D * UM) i col := by
          rw [Matrix.diagonal_mul, hUentry, hblock_entry, dif_neg hi]
          simp

  have hdiag_mem : diagHom F σ (m + 1) dglob ∈ diagTorusV F σ (m + 1) := ⟨dglob, rfl⟩
  have hmapmem : diagHom F σ (m + 1) dglob ∈
      Subgroup.map (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
        (⨆ i, qTwoTor E m hm i) := by
    rw [map_qTwoTor_iSup_eq_diagTorus E hK m hm]
    exact hdiag_mem
  obtain ⟨t, ht, htraw⟩ := Subgroup.mem_map.mp hmapmem
  let L : Subgroup ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
    ((qTwoStdFamily E hK m hm).levi C).map
      (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
  have hUmem : suEndN (F := F) σ (m + 1) U ∈ L := by
    refine qTwo_blockProduct_mem (K := K) (n := m + 1) (k := k) (b := b)
      hbk hdisj u (φ := suEndN (F := F) σ (m + 1)) (H := L) ?_
    intro a
    by_cases hk1 : k a = 1
    · haveI : Subsingleton (Su K 2 1 (k a)) := by
        rw [hk1]
        exact su_one_subsingleton (K := K)
      have hu : u a = 1 := Subsingleton.elim (u a) 1
      rw [hu]
      simpa using L.one_mem
    · have hk2 : 2 ≤ k a := by
        have hkp := hk a
        omega
      obtain ⟨l, hl, hlraw⟩ := qTwo_blockEmb_mem_levi E hK m hm (k a) (b a) hk2 (hbk a) (hC a) (u a)
      exact Subgroup.mem_map.mpr ⟨l, hl, hlraw⟩
  obtain ⟨l, hl, hlraw⟩ := Subgroup.mem_map.mp hUmem
  have hraw : suEndN (F := F) σ (m + 1) s =
      diagHom F σ (m + 1) dglob * suEndN (F := F) σ (m + 1) U := by
    apply LinearEquiv.ext
    intro v
    calc
      suEndN (F := F) σ (m + 1) s v = sM *ᵥ v := by
        rw [suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def]
      _ = (D * UM) *ᵥ v := by rw [hmatrix]
      _ = D *ᵥ (UM *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = diagHom F σ (m + 1) dglob (UM *ᵥ v) := by
        ext i
        simp [D, Matrix.mulVec_diagonal, diagHom_apply]
      _ = diagHom F σ (m + 1) dglob
            (suEndN (F := F) σ (m + 1) U v) := by
        rw [suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def]
      _ = (diagHom F σ (m + 1) dglob * suEndN (F := F) σ (m + 1) U) v := rfl
  refine ⟨t, ht, l, hl, ?_⟩
  have ht' : (t : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      diagHom F σ (m + 1) dglob := htraw
  have hl' : (l : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      suEndN (F := F) σ (m + 1) U := hlraw
  rw [ht', hl']
  exact hraw


end CFSG.ClassicalInvolution.PhanDn.QTwo
