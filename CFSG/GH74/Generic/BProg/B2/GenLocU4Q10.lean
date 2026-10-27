module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q10Blk
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q10Link
public import CFSG.GH74.Generic.BProg.B2.GenLocU4QAsm

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

open GenLocU4Basic GenLocU4QLift GenLocU4QClass GenLocU4QHyp GenLocU4Q10Link GenLocU4Q CFSG.ClassicalInvolution.Phan

namespace GenLocU4Q10

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

omit [Finite K] in
theorem comm_conj {P r x D : GL (Fin 4) K} (hD : P⁻¹ * x * P = D)
    (h : (r : Matrix (Fin 4) (Fin 4) K) * (D : Matrix (Fin 4) (Fin 4) K) =
      (D : Matrix (Fin 4) (Fin 4) K) * (r : Matrix (Fin 4) (Fin 4) K)) :
    (P * r * P⁻¹) * x = x * (P * r * P⁻¹) := by
  have h' : r * D = D * r := Units.ext (by simpa [Units.val_mul] using h)
  have e : x = P * D * P⁻¹ := by rw [← hD]; group
  calc P * r * P⁻¹ * x = P * r * P⁻¹ * (P * D * P⁻¹) := by rw [← e]
    _ = P * (r * D) * P⁻¹ := by group
    _ = P * (D * r) * P⁻¹ := by rw [h']
    _ = (P * D * P⁻¹) * (P * r * P⁻¹) := by group
    _ = x * (P * r * P⁻¹) := by rw [← e]

omit [Finite K] in
theorem Mrot_comm_Dx (c s1 s2 : K) :
    Mrot c s1 s2 * (!![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K) =
      !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1] * Mrot c s1 s2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mrot, Matrix.mul_apply, Fin.sum_univ_four]

omit [Finite K] in
theorem Mrot_comm_Dy (c s : K) :
    Mrot c s s * (!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] : Matrix (Fin 4) (Fin 4) K) =
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] * Mrot c s s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mrot, Matrix.mul_apply, Fin.sum_univ_four]

omit [Finite K] in
theorem Mrot_comm_Dyz (c s : K) :
    Mrot c (-s) s * ((!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] : Matrix (Fin 4) (Fin 4) K) *
        !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]) =
      ((!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] : Matrix (Fin 4) (Fin 4) K) *
        !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]) * Mrot c (-s) s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mrot, Matrix.mul_apply, Fin.sum_univ_four]

variable [Fact p.Prime] [CharP K p]

theorem gammaAct_class10
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (hA : IsRank23 A) (hr : pRank 2 A = 3)
    (T : Triple α 1 1 1) : gammaAct α = ⊤ := by
  obtain ⟨a, b, c, x, y, z, hax, hby, hcz, hx, hy, hz, hxy, hxz, hyz, hzn⟩ := T
  have hH := hypPlanes_of_data hp hp2 hK α hA hr hax hby hcz hx hy hz hxy hxz hyz hzn
  obtain ⟨P, hP, hxP, hyP, hzP⟩ := GenLocU4QFrame2.frame10 hp hp2 hK x y z hax.1 hby.1 hcz.1 (gl_sq_one hx)
    (gl_sq_one hy) (gl_sq_one hz) hxy hxz hyz hzn
  let Γ₁ : Subgroup (Su K p f 4) := (gammaAct α).comap (GenLocU4Gen.frameConj (GenLocU4Gen.fieldData hK) P hP)
  have hblock : ∀ B : Su K p f 2, blockEmb2 K p f 3 0 B ∈ Γ₁ ∧ blockEmb2 K p f 3 2 B ∈ Γ₁ := fun B =>
    ⟨GenLocU4Q10Blk.block_le_class10 hp hp2 hK hq α hA hr hax hby hcz hx hy hz hxy hxz hyz hzn P hP hxP hzP 0
        (Or.inl rfl) B,
      GenLocU4Q10Blk.block_le_class10 hp hp2 hK hq α hA hr hax hby hcz hx hy hz hxy hxz hyz hzn P hP hxP hzP 2
        (Or.inr rfl) B⟩
  have hDyz : ((P⁻¹ * (y * z) * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
    have : P⁻¹ * (y * z) * P = (P⁻¹ * y * P) * (P⁻¹ * z * P) := by group
    rw [this, Units.val_mul, hyP, hzP]
  have hrot : ∀ (c' s' : K) (hc : c' ^ (p ^ f) = c') (hs : s' ^ (p ^ f) = -s') (hs' : (-s') ^ (p ^ f) = -(-s'))
      (h : c' * c' - s' * s' = 1) (h' : c' * c' - (-s') * (-s') = 1),
      rotElt c' s' s' hc hs hs h h ∈ Γ₁ ∧ rotElt c' (-s') s' hc hs' hs h' h ∈ Γ₁ := by
    intro c' s' hc hs hs' h h'
    refine ⟨?_, ?_⟩
    · refine hH.1 _ ?_ ?_
      · rw [GenLocU4Gen.coe_frameConj]
        refine comm_conj (D := P⁻¹ * x * P) rfl ?_
        rw [hxP]
        exact Mrot_comm_Dx c' s' s'
      · rw [GenLocU4Gen.coe_frameConj]
        refine comm_conj (D := P⁻¹ * y * P) rfl ?_
        rw [hyP]
        exact Mrot_comm_Dy c' s'
    · refine hH.2.2.2.1 _ ?_ ?_
      · rw [GenLocU4Gen.coe_frameConj]
        refine comm_conj (D := P⁻¹ * x * P) rfl ?_
        rw [hxP]
        exact Mrot_comm_Dx c' (-s') s'
      · rw [GenLocU4Gen.coe_frameConj]
        refine comm_conj (D := P⁻¹ * (y * z) * P) rfl ?_
        rw [hDyz]
        exact Mrot_comm_Dyz c' s'
  have hcore := link10_core hp2 hK hq Γ₁ (fun B => (hblock B).1) (fun B => (hblock B).2) hrot
  rw [eq_top_iff]
  intro g _
  obtain ⟨x', rfl⟩ := GenLocU4Gen.frameConj_surjective (GenLocU4Gen.fieldData hK) P hP g
  have hx' : x' ∈ Γ₁ := by
    rw [hcore]
    trivial
  exact hx'

end GenLocU4Q10

end CFSG.GH74.Generic.BProg.B2
