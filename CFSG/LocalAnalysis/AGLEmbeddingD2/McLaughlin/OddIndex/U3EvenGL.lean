module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreFrobPair

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def vMat (a b : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, a, b; 0, 1, 0; 0, 0, 1]

theorem vMat_mul (a b c d : ZMod 2) : vMat a b * vMat c d = vMat (a + c) (b + d) := by
  revert a b c d; unfold vMat; decide +kernel

theorem vMat_zero : vMat 0 0 = 1 := by unfold vMat; decide +kernel

theorem vMat_self (a b : ZMod 2) : vMat a b * vMat a b = 1 := by
  rw [vMat_mul, ← vMat_zero]
  congr 1 <;> revert a b <;> decide +kernel

@[expose] def vGL (a b : ZMod 2) : GL (Fin 3) (ZMod 2) :=
  ⟨vMat a b, vMat a b, vMat_self a b, vMat_self a b⟩

theorem vGL_mul (a b c d : ZMod 2) : vGL a b * vGL c d = vGL (a + c) (b + d) :=
  Units.ext (by simpa [vGL] using vMat_mul a b c d)

theorem vGL_zero : vGL 0 0 = 1 := Units.ext (by simpa [vGL] using vMat_zero)

theorem vGL_inv (a b : ZMod 2) : (vGL a b)⁻¹ = vGL a b := by
  rw [inv_eq_iff_mul_eq_one]; exact Units.ext (by simpa [vGL] using vMat_self a b)

@[expose] def vSub : Subgroup (GL (Fin 3) (ZMod 2)) where
  carrier := {m | ∃ a b, m = vGL a b}
  one_mem' := ⟨0, 0, vGL_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, vGL_mul a b c d⟩
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨a, b, vGL_inv a b⟩

theorem vGL_ne_one : vGL 1 0 ≠ 1 := by
  intro h
  have := congrArg Units.val h
  revert this; unfold vGL vMat; decide +kernel

theorem isPGroup_vSub : IsPGroup 2 vSub := by
  intro x
  refine ⟨1, ?_⟩
  obtain ⟨m, a, b, rfl⟩ := x
  apply Subtype.ext
  show (vGL a b) ^ (2 ^ 1) = 1
  rw [pow_one, pow_two]
  exact Units.ext (by simpa [vGL] using vMat_self a b)


@[expose] def matS : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem matS_mul : matS * matS = 1 := by unfold matS; decide +kernel

@[expose] def sGL : GL (Fin 3) (ZMod 2) := ⟨matS, matS, matS_mul, matS_mul⟩

theorem sGL_inv : sGL⁻¹ = sGL := by
  rw [inv_eq_iff_mul_eq_one]; exact Units.ext (by simpa [sGL] using matS_mul)

theorem matA_vMat (a b : ZMod 2) : matA * vMat a b = vMat (a + b) a * matA := by
  revert a b; unfold matA vMat; decide +kernel

theorem matS_vMat (a b : ZMod 2) : matS * vMat a b = vMat b a * matS := by
  revert a b; unfold matS vMat; decide +kernel

theorem matS_matA : matS * matA = matA ^ 2 * matS := by unfold matS matA; decide +kernel

theorem aGL_vGL (a b : ZMod 2) : aGL * vGL a b = vGL (a + b) a * aGL :=
  Units.ext (by simpa [aGL, vGL] using matA_vMat a b)

theorem sGL_vGL (a b : ZMod 2) : sGL * vGL a b = vGL b a * sGL :=
  Units.ext (by simpa [sGL, vGL] using matS_vMat a b)

theorem sGL_aGL : sGL * aGL * sGL⁻¹ = aGL⁻¹ := by
  have h3 : aGL * aGL ^ 2 = 1 := by rw [← pow_succ']; exact aGL_pow
  have hinv : aGL⁻¹ = aGL ^ 2 := inv_eq_of_mul_eq_one_right h3
  have h1 : sGL * aGL = aGL ^ 2 * sGL :=
    Units.ext (by simpa [sGL, aGL, Units.val_pow_eq_pow_val] using matS_matA)
  have h2 : sGL * sGL = 1 := Units.ext (by simpa [sGL] using matS_mul)
  rw [hinv, sGL_inv, h1, mul_assoc, h2, mul_one]

theorem matA_vMat' (a b : ZMod 2) : vMat a b * matA = matA * vMat b (a + b) := by
  revert a b; unfold matA vMat; decide +kernel

theorem aGL_vGL' (a b : ZMod 2) : vGL a b * aGL = aGL * vGL b (a + b) :=
  Units.ext (by simpa [aGL, vGL] using matA_vMat' a b)

theorem aGL_conj_vSub_inv {v : GL (Fin 3) (ZMod 2)} (hv : v ∈ vSub) : aGL⁻¹ * v * aGL ∈ vSub := by
  obtain ⟨a, b, rfl⟩ := hv
  rw [mul_assoc, aGL_vGL', ← mul_assoc, inv_mul_cancel, one_mul]
  exact ⟨_, _, rfl⟩

theorem aGL_conj_vSub {v : GL (Fin 3) (ZMod 2)} (hv : v ∈ vSub) : aGL * v * aGL⁻¹ ∈ vSub := by
  obtain ⟨a, b, rfl⟩ := hv
  rw [aGL_vGL, mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨_, _, rfl⟩

theorem sGL_conj_vSub {v : GL (Fin 3) (ZMod 2)} (hv : v ∈ vSub) : sGL * v * sGL⁻¹ ∈ vSub := by
  obtain ⟨a, b, rfl⟩ := hv
  rw [sGL_vGL, mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨_, _, rfl⟩

theorem sGL_conj_vSub_inv {v : GL (Fin 3) (ZMod 2)} (hv : v ∈ vSub) : sGL⁻¹ * v * sGL ∈ vSub := by
  rw [sGL_inv]
  have := sGL_conj_vSub hv
  rwa [sGL_inv] at this

theorem exists_s4_data {X : Type} [Group X] (hX : IsLThreeTwo X) :
    ∃ (V : Subgroup X) (s g : X), IsPGroup 2 V ∧ V ≠ ⊥ ∧ (∀ v ∈ V, s * v * s⁻¹ ∈ V) ∧
      (∀ v ∈ V, g * v * g⁻¹ ∈ V) ∧ g ^ 3 = 1 ∧ g ≠ 1 ∧ s * g * s⁻¹ = g⁻¹ ∧
      (∀ v ∈ V, s⁻¹ * v * s ∈ V) ∧ (∀ v ∈ V, g⁻¹ * v * g ∈ V) ∧ s ^ 2 = 1 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_GL_of_isLThreeTwo hX
  refine ⟨vSub.map e.symm.toMonoidHom, e.symm sGL, e.symm aGL, isPGroup_vSub.map _, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hm : e.symm (vGL 1 0) ∈ vSub.map e.symm.toMonoidHom := ⟨_, ⟨1, 0, rfl⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at hm
    exact vGL_ne_one (e.symm.injective (by rw [hm, map_one]))
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨_, sGL_conj_vSub hw, by simp⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨_, aGL_conj_vSub hw, by simp⟩
  · rw [← map_pow, aGL_pow, map_one]
  · exact fun h => aGL_ne (e.symm.injective (by rw [h, map_one]))
  · rw [← map_mul, ← map_inv, ← map_mul, sGL_aGL, map_inv]
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨_, sGL_conj_vSub_inv hw, by simp⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨_, aGL_conj_vSub_inv hw, by simp⟩
  · rw [pow_two, ← map_mul, show sGL * sGL = 1 from Units.ext (by simpa [sGL] using matS_mul),
      map_one]

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
