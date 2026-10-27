module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Group
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open scoped Matrix

theorem card_SU : Nat.card SU = 16547328 := by
  have h : Nat.card GF64 = (2 ^ 3) ^ 2 := by rw [GF64.card_eq]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.SectionRank.OddCover.card_statedSU_three (K := GF64) (p := 2) (f := 3) h
  show Nat.card (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 3) GF64) = 16547328
  rw [this]
  norm_num

theorem map_bar_eq (M : Matrix (Fin 3) (Fin 3) GF64) : M.map hU.bar = M.map barC :=
  Matrix.ext fun _ _ => bar_apply_eq _

theorem mem_SU_iff' {g : GL (Fin 3) GF64} :
    g ∈ SU ↔ (g : Matrix (Fin 3) (Fin 3) GF64).det = 1 ∧
      ((g : Matrix (Fin 3) (Fin 3) GF64).map barC)ᵀ * (g : Matrix (Fin 3) (Fin 3) GF64) = 1 := by
  rw [mem_unitarySU_iff hU, map_bar_eq]

theorem isSUArr_size {A : Array GF64} (h : isSUArr A = true) : A.size = 9 := by
  simp only [isSUArr, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem isSUArr_ofMat3 {g : GL (Fin 3) GF64} (hg : g ∈ SU) :
    isSUArr (ofMat3 (g : Matrix (Fin 3) (Fin 3) GF64)) = true := by
  obtain ⟨hdet, hmul⟩ := mem_SU_iff'.1 hg
  simp only [isSUArr, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨size_ofMat3 _, ?_⟩, ?_⟩
  · rw [← det_toMat3, toMat3_ofMat3, hdet]
  · apply eq_of_toMat_eq3 (size_mulArr3 _ _) size_oneArr3
    rw [toMat3_mulArr3, toMat3_conjTrArr3, toMat3_ofMat3, toMat3_oneArr3, hmul]

@[expose] noncomputable def GLof (A : Array GF64) : GL (Fin 3) GF64 :=
  if h : isSUArr A = true then ((Classical.choose (exists_su_of_isSUArr h) : SU) :
    GL (Fin 3) GF64) else 1

theorem coe_GLof {A : Array GF64} (h : isSUArr A = true) :
    ((GLof A : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) = toMat3 A := by
  unfold GLof
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec (exists_su_of_isSUArr h)

theorem GLof_mem {A : Array GF64} (h : isSUArr A = true) : GLof A ∈ SU := by
  unfold GLof
  simp only [h, ↓reduceDIte]
  exact (Classical.choose (exists_su_of_isSUArr h)).2

theorem isSUArr_mulArr3 {A B : Array GF64} (hA : isSUArr A = true) (hB : isSUArr B = true) :
    isSUArr (mulArr3 A B) = true := by
  have hsA : A.size = 9 := by simp only [isSUArr, Bool.and_eq_true, beq_iff_eq] at hA; exact hA.1.1
  have hsB : B.size = 9 := by simp only [isSUArr, Bool.and_eq_true, beq_iff_eq] at hB; exact hB.1.1
  have hmem : GLof A * GLof B ∈ SU := SU.mul_mem (GLof_mem hA) (GLof_mem hB)
  have h1 := isSUArr_ofMat3 hmem
  have h2 : mulArr3 A B = ofMat3 (((GLof A * GLof B : GL (Fin 3) GF64)) :
      Matrix (Fin 3) (Fin 3) GF64) := by
    apply eq_of_toMat_eq3 (size_mulArr3 _ _) (size_ofMat3 _)
    rw [toMat3_mulArr3, toMat3_ofMat3, Units.val_mul, coe_GLof hA, coe_GLof hB]
  rw [h2]
  exact h1

theorem isSUArr_conjTrArr3 {A : Array GF64} (hA : isSUArr A = true) :
    isSUArr (conjTrArr3 A) = true := by
  have hmem : (GLof A)⁻¹ ∈ SU := SU.inv_mem (GLof_mem hA)
  have h1 := isSUArr_ofMat3 hmem
  have hinv : (((GLof A)⁻¹ : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) =
      ((toMat3 A).map barC)ᵀ := by
    obtain ⟨-, hmul⟩ := mem_SU_iff'.1 (GLof_mem hA)
    rw [coe_GLof hA] at hmul
    exact Units.inv_eq_of_mul_eq_one_left (by rw [coe_GLof hA]; exact hmul)
  have h2 : conjTrArr3 A = ofMat3 ((((GLof A)⁻¹ : GL (Fin 3) GF64)) :
      Matrix (Fin 3) (Fin 3) GF64) := by
    apply eq_of_toMat_eq3 (size_conjTrArr3 _) (size_ofMat3 _)
    rw [toMat3_conjTrArr3, toMat3_ofMat3, hinv]
  rw [h2]
  exact h1

theorem coe_GLof_inv {A : Array GF64} (hA : isSUArr A = true) :
    (((GLof A)⁻¹ : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) =
      toMat3 (conjTrArr3 A) := by
  rw [toMat3_conjTrArr3]
  obtain ⟨-, hmul⟩ := mem_SU_iff'.1 (GLof_mem hA)
  rw [coe_GLof hA] at hmul
  exact Units.inv_eq_of_mul_eq_one_left (by rw [coe_GLof hA]; exact hmul)

@[expose] def RowVec : Type := Fin 3 → GF64

instance : Finite RowVec := inferInstanceAs (Finite (Fin 3 → GF64))

instance : DecidableEq RowVec := inferInstanceAs (DecidableEq (Fin 3 → GF64))

instance : MulAction (GL (Fin 3) GF64) RowVec where
  smul g v := Matrix.vecMul (show Fin 3 → GF64 from v)
    (((g⁻¹ : GL (Fin 3) GF64)) : Matrix (Fin 3) (Fin 3) GF64)
  one_smul v := by
    show Matrix.vecMul (show Fin 3 → GF64 from v)
      (((1⁻¹ : GL (Fin 3) GF64)) : Matrix (Fin 3) (Fin 3) GF64) = v
    rw [inv_one, Units.val_one]
    exact Matrix.vecMul_one (show Fin 3 → GF64 from v)
  mul_smul g h v := by
    show Matrix.vecMul (show Fin 3 → GF64 from v)
      ((((g * h)⁻¹ : GL (Fin 3) GF64)) : Matrix (Fin 3) (Fin 3) GF64) =
      Matrix.vecMul (Matrix.vecMul (show Fin 3 → GF64 from v)
        (((h⁻¹ : GL (Fin 3) GF64)) : Matrix (Fin 3) (Fin 3) GF64))
        (((g⁻¹ : GL (Fin 3) GF64)) : Matrix (Fin 3) (Fin 3) GF64)
    rw [Matrix.vecMul_vecMul, mul_inv_rev, Units.val_mul]

theorem smul_rowVec (g : GL (Fin 3) GF64) (v : RowVec) :
    (g • v : RowVec) = Matrix.vecMul (show Fin 3 → GF64 from v)
      (((g⁻¹ : GL (Fin 3) GF64)) : Matrix (Fin 3) (Fin 3) GF64) := rfl

@[expose] def vecOf (a : Array ℕ) : RowVec :=
  (![GF64.ofNat' (a.getD 0 0), GF64.ofNat' (a.getD 1 0), GF64.ofNat' (a.getD 2 0)] :
    Fin 3 → GF64)

end CFSG.AGLEmbedding.ChevOuter.U38
