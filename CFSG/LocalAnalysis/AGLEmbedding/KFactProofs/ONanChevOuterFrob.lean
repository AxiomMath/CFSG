module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42LinkCheck
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Check

public section

namespace CFSG.AGLEmbedding.ChevOuter

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.RankThree.PartTwo.Sec4.Item434D42

@[expose] def frobF : GF8 →+* GF8 where
  toFun a := a * a
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

theorem frobF_apply (a : GF8) : frobF a = a * a := rfl

theorem frobF_cube (a : GF8) : frobF (frobF (frobF a)) = a := by
  revert a
  decide

@[expose] def frobGL : GL (Fin 8) GF8 →* GL (Fin 8) GF8 :=
  Matrix.GeneralLinearGroup.map frobF

theorem coe_frobGL (g : GL (Fin 8) GF8) :
    ((frobGL g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
      (g : Matrix (Fin 8) (Fin 8) GF8).map frobF := by
  simp [frobGL, Matrix.GeneralLinearGroup.map]

theorem frobGL_cube (g : GL (Fin 8) GF8) : frobGL (frobGL (frobGL g)) = g := by
  apply Units.ext
  simp only [coe_frobGL, Matrix.map_map]
  ext i j
  exact frobF_cube _

@[expose] def sg (k : ℕ) : ℕ :=
  if k < 8 then (frobF (GF8.ofNat' k)).toNat
  else if k < 16 then 8 + (frobF (GF8.ofNat' (k - 8))).toNat else k

theorem sg_lt (k : ℕ) (hk : k < 18) : sg k < 18 := by
  have h : ∀ a : GF8, (frobF a).toNat < 8 := fun a => (frobF a).val.isLt
  unfold sg
  split_ifs with h1 h2
  · have := h (GF8.ofNat' k); omega
  · have := h (GF8.ofNat' (k - 8)); omega
  · exact hk

theorem frob_letterMat : ∀ k : Fin 18, (letterMat k).map frobF = letterMat (sg k) := by
  decide +kernel

theorem frobGL_letterGL (k : ℕ) (hk : k < 18) : frobGL (letterGL k) = letterGL (sg k) := by
  apply Units.ext
  rw [coe_frobGL]
  exact frob_letterMat ⟨k, hk⟩

theorem frobGL_mem {g : GL (Fin 8) GF8} (hg : g ∈ lineGroup) : frobGL g ∈ lineGroup := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, rfl⟩ := hy
    have hk' : k < 18 := hk
    rw [frobGL_letterGL k hk']
    exact Subgroup.subset_closure ⟨sg k, sg_lt k hk', rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  | inv y _ hy => rw [map_inv]; exact inv_mem hy

@[expose] def frobT : lineGroup →* lineGroup :=
  (frobGL.comp lineGroup.subtype).codRestrict lineGroup fun g => frobGL_mem g.2

theorem coe_frobT (g : lineGroup) :
    ((frobT g : lineGroup) : GL (Fin 8) GF8) = frobGL (g : GL (Fin 8) GF8) := rfl

theorem frobT_cube (g : lineGroup) : frobT (frobT (frobT g)) = g :=
  Subtype.ext (frobGL_cube _)

@[expose] def phiT : MulAut lineGroup where
  toFun := frobT
  invFun g := frobT (frobT g)
  left_inv g := frobT_cube g
  right_inv g := by
    show frobT (frobT (frobT g)) = g
    exact frobT_cube g
  map_mul' := map_mul frobT

theorem coe_phiT (g : lineGroup) :
    ((phiT g : lineGroup) : GL (Fin 8) GF8) = frobGL (g : GL (Fin 8) GF8) := rfl

theorem phiT_letterX (k : ℕ) (hk : k < 18) : phiT (letterX k) = letterX (sg k) := by
  apply Subtype.ext
  rw [coe_phiT]
  have h1 : ((letterX k : lineGroup) : GL (Fin 8) GF8) = letterGL k := by simp [letterX, hk]
  have h2 : ((letterX (sg k) : lineGroup) : GL (Fin 8) GF8) = letterGL (sg k) := by
    simp [letterX, sg_lt k hk]
  rw [h1, h2, frobGL_letterGL k hk]

theorem phiT_pow_three : phiT ^ 3 = 1 := by
  refine MulEquiv.ext fun g => ?_
  show phiT (phiT (phiT g)) = g
  exact frobT_cube g

theorem trace_frob (M : Matrix (Fin 8) (Fin 8) GF8) : (M.map frobF).trace = frobF M.trace := by
  simp [Matrix.trace, map_sum]

theorem trace_letters_ne :
    frobF (letterMat 1 * letterMat 10).trace ≠ (letterMat 1 * letterMat 10).trace := by
  decide +kernel

theorem phiT_ne_conj (g : lineGroup) : phiT ≠ MulAut.conj g := by
  intro h
  set x : lineGroup := letterX 1 * letterX 10 with hx
  have hxm : (((x : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
      letterMat 1 * letterMat 10 := by
    simp [hx, letterX, letterGL]
  have h1 : frobGL ((x : lineGroup) : GL (Fin 8) GF8) =
      ((g : lineGroup) : GL (Fin 8) GF8) * ((x : lineGroup) : GL (Fin 8) GF8) *
        ((g : lineGroup) : GL (Fin 8) GF8)⁻¹ := by
    have := congrArg (fun α : MulAut lineGroup => ((α x : lineGroup) : GL (Fin 8) GF8)) h
    simpa [coe_phiT, MulAut.conj_apply] using this
  have h2 := congrArg (fun M : GL (Fin 8) GF8 => (M : Matrix (Fin 8) (Fin 8) GF8).trace) h1
  simp only [coe_frobGL, Units.val_mul, trace_frob, hxm] at h2
  set G : Matrix (Fin 8) (Fin 8) GF8 := (((g : lineGroup) : GL (Fin 8) GF8) :
    Matrix (Fin 8) (Fin 8) GF8) with hG
  set Gi : Matrix (Fin 8) (Fin 8) GF8 := ((((g : lineGroup) : GL (Fin 8) GF8)⁻¹ :
    GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) with hGi
  have hinv : Gi * G = 1 := by
    rw [hG, hGi]
    exact Units.inv_mul ((g : lineGroup) : GL (Fin 8) GF8)
  have h3 : (G * (letterMat 1 * letterMat 10) * Gi).trace = (letterMat 1 * letterMat 10).trace := by
    rw [mul_assoc, Matrix.trace_mul_comm, mul_assoc, hinv, mul_one]
  rw [h3] at h2
  exact trace_letters_ne h2

end CFSG.AGLEmbedding.ChevOuter
