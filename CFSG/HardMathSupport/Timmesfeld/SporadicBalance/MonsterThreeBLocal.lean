module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBSys

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated CFSG.Monster.B.Pinned
open _root_.Timmesfeld.M3B (F3 Vec Mat E AD vget vofFn zeroV mget aget mofFn mOfRows adOfRows
  mRows xRows yRows c1 c2 B0 Da Db LA LM xiRows yiRows mmul mone matOf mpow)

@[expose] def toMatrix (A : Mat) : Matrix (Fin 12) (Fin 12) (ZMod 3) := Matrix.of (toMat A)

theorem toMatrix_apply (A : Mat) (i j : Fin 12) : toMatrix A i j = toZ (mget A i j) := rfl

theorem toMatrix_mmul (A B : Mat) : toMatrix (mmul A B) = toMatrix A * toMatrix B := by
  ext i j
  rw [Matrix.mul_apply, toMatrix_apply]
  unfold mmul
  rw [mget_mofFn, fsum_eq]
  simp only [toZ_mul]
  rfl

theorem toMatrix_mone : toMatrix mone = 1 := by
  ext i j
  rw [toMatrix_apply]
  unfold mone
  rw [mget_mofFn, Matrix.one_apply]
  split_ifs <;> rfl

theorem toMatrix_mpow (A : Mat) : ∀ k, toMatrix (mpow A k) = toMatrix A ^ k
  | 0 => by rw [mpow, toMatrix_mone, pow_zero]
  | k + 1 => by rw [mpow, toMatrix_mmul, toMatrix_mpow A k, pow_succ]

section Datum


noncomputable abbrev QQ : Subgroup Gmat := Subgroup.closure (Set.range tbq)

@[expose] noncomputable def tbL : Subgroup Gmat := Subgroup.closure ({tbb₁, tbb₂} ∪ Set.range tbq)

theorem ofFn_mem_QQ (e : Fin 12 → ℕ) (c : ℕ) :
    (List.ofFn fun j => tbq j ^ e j).prod * tbw ^ c ∈ QQ := by
  refine mul_mem (list_prod_mem fun g hg => ?_) (pow_mem tbCommData.mem_z c)
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  exact pow_mem (Subgroup.subset_closure (Set.mem_range_self j)) (e j)

theorem tbL_conj : ∀ b ∈ tbL, ∀ g ∈ QQ, b⁻¹ * g * b ∈ QQ := by
  intro b hb
  refine conj_mem_of_mem_closure (S := {tbb₁, tbb₂} ∪ Set.range tbq) ?_ hb
  rintro b' ((rfl | rfl) | ⟨j, rfl⟩) g hg
  · exact CommData.conj_mem (fun i => by rw [tbb₁_conj_U]; exact ofFn_mem_QQ _ _) hg
  · exact CommData.conj_mem (fun i => by rw [tbb₂_conj_U]; exact ofFn_mem_QQ _ _) hg
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _
      (Subgroup.subset_closure ⟨j, rfl⟩)) hg) (Subgroup.subset_closure ⟨j, rfl⟩)

theorem tbb₁_mem : tbb₁ ∈ tbL := Subgroup.subset_closure (Or.inl (Or.inl rfl))

theorem tbb₂_mem : tbb₂ ∈ tbL := Subgroup.subset_closure (Or.inl (Or.inr rfl))

theorem QQ_le_tbL : QQ ≤ tbL := Subgroup.closure_mono Set.subset_union_right

theorem tbq_mem (i : Fin 12) : tbq i ∈ QQ := Subgroup.subset_closure ⟨i, rfl⟩

theorem tbw_mem : tbw ∈ QQ := tbCommData.mem_z

theorem tbSys_nf_mem (x : Elt 12) : tbSys.nf x ∈ QQ := by
  rw [Sys.nf, secN3_eq_prod]
  exact ofFn_mem_QQ _ _

theorem exists_nf_of_mem {g : Gmat} (hg : g ∈ QQ) : ∃ x : Elt 12, g = tbSys.nf x := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    refine ⟨(Pi.single i 1, 0), ?_⟩
    rw [Sys.nf, secN3_single]
    simp [tbSys]
  | one => exact ⟨eone, (Sys.nf_eone tbSys).symm⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨emul tbSys.B x y, Sys.nf_mul tbSys_good x y⟩
  | inv a _ ha =>
    obtain ⟨x, rfl⟩ := ha
    exact ⟨epow tbSys.B x 2, Sys.nf_inv tbSys_good x⟩

theorem coord_nf (x : Elt 12) : coord 3 tbq tbw tbM (tbSys.nf x) = x.1 := by
  rw [Sys.nf, secN3_eq_prod]
  exact tbCommData.coord_prod x.1 x.2.val

theorem actMat_of_isAct {g : Gmat} {D : ActD 12} (h : IsAct tbSys g D) :
    CommData.actMat 3 tbq tbw tbM g = Matrix.of fun i => (D.1 i).1 := by
  ext i j
  have hi : g⁻¹ * tbq i * g = tbSys.nf (D.1 i) := h.1 i
  rw [CommData.actMat, Matrix.of_apply, hi, coord_nf]
  rfl

@[expose] noncomputable def rhoL : tbL →* GL (Fin 12) (ZMod 3) :=
  (tbCommData.actHom tbL fun b hb i => tbL_conj b hb _ (tbq_mem i)).toHomUnits

theorem coe_rhoL (b : tbL) :
    ((rhoL b : GL (Fin 12) (ZMod 3)) : Matrix (Fin 12) (Fin 12) (ZMod 3)) =
      CommData.actMat 3 tbq tbw tbM b := rfl

theorem conj_q_mem_of_mem {b : Gmat} (hb : b ∈ tbL) : ∀ i, b⁻¹ * tbq i * b ∈ QQ :=
  fun i => tbL_conj b hb _ (tbq_mem i)

theorem toMatrix_mOfRows (R : List (List ℕ)) : toMatrix (mOfRows R) = tbMat R := by
  ext i j
  rw [toMatrix_apply, mget_mOfRows]
  rfl

theorem tbL_mem_letter (i : ℕ) : letterG i ∈ tbL := by
  unfold letterG
  split_ifs
  · exact tbb₁_mem
  · exact tbb₂_mem
  · exact tbL.inv_mem tbb₁_mem
  · exact tbL.inv_mem tbb₂_mem
  · exact QQ_le_tbL (tbq_mem _)
  · exact tbL.one_mem

theorem tbL_mem_evalG : ∀ t, evalG letterG t ∈ tbL
  | .gen i => tbL_mem_letter i
  | .mul a b => tbL.mul_mem (tbL_mem_evalG a) (tbL_mem_evalG b)
  | .pow t k => tbL.pow_mem (tbL_mem_evalG t) k

theorem actMat_mul' {g h : Gmat} (hg : g ∈ tbL) (hh : h ∈ tbL) :
    CommData.actMat 3 tbq tbw tbM (g * h) =
      CommData.actMat 3 tbq tbw tbM g * CommData.actMat 3 tbq tbw tbM h :=
  tbCommData.actMat_mul (conj_q_mem_of_mem hg) (conj_q_mem_of_mem hh)

theorem actMat_pow' {g : Gmat} (hg : g ∈ tbL) :
    ∀ k, CommData.actMat 3 tbq tbw tbM (g ^ k) = CommData.actMat 3 tbq tbw tbM g ^ k
  | 0 => by rw [pow_zero, pow_zero]; exact tbCommData.actMat_one
  | k + 1 => by
    rw [pow_succ, actMat_mul' (tbL.pow_mem hg k) hg, actMat_pow' hg k, pow_succ]

theorem actMat_inv' {g : Gmat} (hg : g ∈ tbL) {A : Matrix (Fin 12) (Fin 12) (ZMod 3)}
    (hA : A * CommData.actMat 3 tbq tbw tbM g = 1) :
    CommData.actMat 3 tbq tbw tbM g⁻¹ = A := by
  have h1 := actMat_mul' (tbL.inv_mem hg) hg
  rw [inv_mul_cancel, tbCommData.actMat_one] at h1
  have h2 := actMat_mul' hg (tbL.inv_mem hg)
  rw [mul_inv_cancel, tbCommData.actMat_one] at h2
  calc CommData.actMat 3 tbq tbw tbM g⁻¹ = (A * CommData.actMat 3 tbq tbw tbM g) *
        CommData.actMat 3 tbq tbw tbM g⁻¹ := by rw [hA, one_mul]
    _ = A := by rw [mul_assoc, ← h2, mul_one]

theorem actMat_b₁ : CommData.actMat 3 tbq tbw tbM tbb₁ = tbXMat :=
  tbCommData.actMat_eq tbXMat tbc₁ tbb₁_conj

theorem actMat_b₂ : CommData.actMat 3 tbq tbw tbM tbb₂ = tbYMat :=
  tbCommData.actMat_eq tbYMat tbc₂ tbb₂_conj

theorem actMat_letter (i : ℕ) :
    CommData.actMat 3 tbq tbw tbM (letterG i) = toMatrix ((LM ()).getD i mone) := by
  rcases i with _ | _ | _ | _ | i
  · show _ = toMatrix (mOfRows xRows); rw [toMatrix_mOfRows, xRows_eq]; exact actMat_b₁
  · show _ = toMatrix (mOfRows yRows); rw [toMatrix_mOfRows, yRows_eq]; exact actMat_b₂
  · show CommData.actMat 3 tbq tbw tbM tbb₁⁻¹ = toMatrix (mOfRows xiRows)
    rw [toMatrix_mOfRows]
    refine actMat_inv' tbb₁_mem ?_
    rw [actMat_b₁]
    exact tbX_inv_mul
  · show CommData.actMat 3 tbq tbw tbM tbb₂⁻¹ = toMatrix (mOfRows yiRows)
    rw [toMatrix_mOfRows]
    refine actMat_inv' tbb₂_mem ?_
    rw [actMat_b₂]
    exact tbY_inv_mul
  · have hne : i + 4 ≠ 0 ∧ i + 4 ≠ 1 ∧ i + 4 ≠ 2 ∧ i + 4 ≠ 3 := by omega
    have h2 : (LM ()).getD (i + 4) mone = mone := by
      unfold LM; simp [Array.getD]
    rw [h2, toMatrix_mone]
    unfold letterG
    rw [ite_eq_right hne.1, ite_eq_right hne.2.1, ite_eq_right hne.2.2.1, ite_eq_right hne.2.2.2]
    split_ifs
    · exact tbCommData.actMat_of_mem (tbq_mem _)
    · exact tbCommData.actMat_one

theorem actMat_evalG : ∀ t, CommData.actMat 3 tbq tbw tbM (evalG letterG t) =
    toMatrix (matOf (LM ()) t)
  | .gen i => actMat_letter i
  | .mul a b => by
    rw [evalG, actMat_mul' (tbL_mem_evalG a) (tbL_mem_evalG b), actMat_evalG a, actMat_evalG b,
      _root_.Timmesfeld.M3B.matOf, toMatrix_mmul]
  | .pow t k => by
    rw [evalG, actMat_pow' (tbL_mem_evalG t), actMat_evalG t, _root_.Timmesfeld.M3B.matOf,
      toMatrix_mpow]

end Datum

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
