module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q2sLevi
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q2

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups
open GenLocU4Basic GenLocU4QClass GenLocU4QHyp GenLocU4Q2sLevi GenLocU4Q2sPsi

namespace GenLocU4Q2s

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

@[expose] noncomputable def cUaut (h : UnitaryFieldData p f K) (U : Matrix (Fin 4) (Fin 4) K)
    (hU : IsUnitaryU (p ^ f) U) : MulAut ↥(StatedSU 4 (p ^ f) K) :=
  GenLocDiagU.conjSUHom h 4
    ⟨⟨U, (U.map (· ^ (p ^ f)))ᵀ, mul_eq_one_comm.1 hU, hU⟩, GenLocU4ExtCore.mem_primeFormUnitary_of h hU⟩

theorem gMat_cUaut (h : UnitaryFieldData p f K) (U : Matrix (Fin 4) (Fin 4) K) (hU : IsUnitaryU (p ^ f) U)
    (g : ↥(StatedSU 4 (p ^ f) K)) :
    gMat (cUaut h U hU g) = U * gMat g * (U.map (· ^ (p ^ f)))ᵀ := by
  unfold cUaut gMat
  rw [GenLocDiagU.coe_conjSUHom]
  simp only [Units.val_mul]
  rfl

omit [Finite K] in
theorem comm_conj {U Us a a' g' : Matrix (Fin 4) (Fin 4) K} (h1 : Us * U = 1) (ha : a = U * a' * Us) :
    (U * g' * Us) * a = a * (U * g' * Us) ↔ g' * a' = a' * g' := by
  subst ha
  have e1 : (U * g' * Us) * (U * a' * Us) = U * (g' * a') * Us := by
    calc (U * g' * Us) * (U * a' * Us) = U * g' * (Us * U) * a' * Us := by simp only [Matrix.mul_assoc]
      _ = U * (g' * a') * Us := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have e2 : (U * a' * Us) * (U * g' * Us) = U * (a' * g') * Us := by
    calc (U * a' * Us) * (U * g' * Us) = U * a' * (Us * U) * g' * Us := by simp only [Matrix.mul_assoc]
      _ = U * (a' * g') * Us := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have cancel : ∀ M : Matrix (Fin 4) (Fin 4) K, Us * (U * M * Us) * U = M := by
    intro M
    calc Us * (U * M * Us) * U = (Us * U) * M * (Us * U) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [h1]; simp
  rw [e1, e2]
  constructor
  · intro h
    have := congrArg (fun M => Us * M * U) h
    simpa only [cancel] using this
  · intro h
    rw [h]

theorem levi_of_frame (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) {x y z U : Matrix (Fin 4) (Fin 4) K}
    (hU : IsUnitaryU (p ^ f) U) (hxU : x * U = U * GenLocU4Out.xi) (hyU : y * U = U * yM)
    (hzU : IsUnitaryU (p ^ f) z) (hz : z * z = 1) (hzx : z * x = x * z) (hzy : z * y = y * z)
    (hzn : ∀ c : K, z ≠ c • 1)
    (hxy : ∀ g : ↥(StatedSU 4 (p ^ f) K), gMat g * x = x * gMat g → gMat g * y = y * gMat g → g ∈ Γ)
    (hxz : ∀ g : ↥(StatedSU 4 (p ^ f) K), gMat g * x = x * gMat g → gMat g * z = z * gMat g → g ∈ Γ)
    (hxyz : ∀ g : ↥(StatedSU 4 (p ^ f) K), gMat g * x = x * gMat g →
      gMat g * (y * z) = (y * z) * gMat g → g ∈ Γ) :
    ∀ g : ↥(StatedSU 4 (p ^ f) K), gMat g * x = x * gMat g → g ∈ Γ := by
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  obtain ⟨Us, hUs⟩ : ∃ Us : Matrix (Fin 4) (Fin 4) K, Us = (U.map (· ^ (p ^ f)))ᵀ := ⟨_, rfl⟩
  have h1 : Us * U = 1 := by rw [hUs]; exact hU
  have h2' : U * Us = 1 := mul_eq_one_comm.1 h1
  have hbar : ∀ c : K, h.bar c = c ^ (p ^ f) := fun c => rfl
  have hfun : (fun x : K => x ^ (p ^ f)) = ⇑h.bar := funext fun c => (hbar c).symm
  have hUsb : (U.map h.bar)ᵀ = Us := by rw [hUs, hfun]
  have hUsU : (Us.map h.bar)ᵀ = U := by
    rw [← hUsb]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    exact h.bar_bar (U a b)
  have hxe : x = U * GenLocU4Out.xi * Us := by
    calc x = x * (U * Us) := by rw [h2', Matrix.mul_one]
      _ = (x * U) * Us := by rw [Matrix.mul_assoc]
      _ = U * GenLocU4Out.xi * Us := by rw [hxU]
  have hye : y = U * yM * Us := by
    calc y = y * (U * Us) := by rw [h2', Matrix.mul_one]
      _ = (y * U) * Us := by rw [Matrix.mul_assoc]
      _ = U * yM * Us := by rw [hyU]
  obtain ⟨z', hz'⟩ : ∃ z' : Matrix (Fin 4) (Fin 4) K, z' = Us * z * U := ⟨_, rfl⟩
  have hze : z = U * z' * Us := by
    rw [hz']
    calc z = (U * Us) * z * (U * Us) := by rw [h2']; simp
      _ = U * (Us * z * U) * Us := by simp only [Matrix.mul_assoc]
  have hz'z' : z' * z' = 1 := by
    rw [hz']
    calc Us * z * U * (Us * z * U) = Us * z * (U * Us) * z * U := by simp only [Matrix.mul_assoc]
      _ = Us * (z * z) * U := by rw [h2']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hz, Matrix.mul_one, h1]
  have hz'U : IsUnitaryU (p ^ f) z' := by
    rw [isUnitaryU_iff_bar h.bar hbar, hz', Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, hUsb, hUsU]
    have hzb : (z.map h.bar)ᵀ * z = 1 := (isUnitaryU_iff_bar h.bar hbar z).1 hzU
    calc Us * ((z.map h.bar)ᵀ * U) * (Us * z * U) = Us * ((z.map h.bar)ᵀ * (U * Us) * z) * U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2', Matrix.mul_one, hzb, Matrix.mul_one, h1]
  have hUsx : Us * x = GenLocU4Out.xi * Us := by
    calc Us * x = Us * x * (U * Us) := by rw [h2', Matrix.mul_one]
      _ = Us * (x * U) * Us := by simp only [Matrix.mul_assoc]
      _ = Us * (U * GenLocU4Out.xi) * Us := by rw [hxU]
      _ = GenLocU4Out.xi * Us := by rw [← Matrix.mul_assoc Us U, h1, Matrix.one_mul]
  have hUsy : Us * y = yM * Us := by
    calc Us * y = Us * y * (U * Us) := by rw [h2', Matrix.mul_one]
      _ = Us * (y * U) * Us := by simp only [Matrix.mul_assoc]
      _ = Us * (U * yM) * Us := by rw [hyU]
      _ = yM * Us := by rw [← Matrix.mul_assoc Us U, h1, Matrix.one_mul]
  have hz'x : z' * GenLocU4Out.xi = GenLocU4Out.xi * z' := by
    calc z' * GenLocU4Out.xi = Us * z * (U * GenLocU4Out.xi) := by rw [hz', Matrix.mul_assoc]
      _ = Us * z * (x * U) := by rw [hxU]
      _ = Us * (z * x) * U := by simp only [Matrix.mul_assoc]
      _ = Us * (x * z) * U := by rw [hzx]
      _ = (Us * x) * z * U := by simp only [Matrix.mul_assoc]
      _ = GenLocU4Out.xi * z' := by rw [hUsx, hz']; simp only [Matrix.mul_assoc]
  have hz'y : z' * yM = yM * z' := by
    calc z' * yM = Us * z * (U * yM) := by rw [hz', Matrix.mul_assoc]
      _ = Us * z * (y * U) := by rw [hyU]
      _ = Us * (z * y) * U := by simp only [Matrix.mul_assoc]
      _ = Us * (y * z) * U := by rw [hzy]
      _ = (Us * y) * z * U := by simp only [Matrix.mul_assoc]
      _ = yM * z' := by rw [hUsy, hz']; simp only [Matrix.mul_assoc]
  have hz'n : ∀ c : K, z' ≠ c • 1 := by
    intro c hc
    apply hzn c
    rw [hze, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h2']
  have hyz : y * z = U * (yM * z') * Us := by
    calc y * z = (U * yM * Us) * (U * z' * Us) := by rw [← hye, ← hze]
      _ = U * (yM * z') * Us := by
          calc (U * yM * Us) * (U * z' * Us) = U * yM * (Us * U) * z' * Us := by simp only [Matrix.mul_assoc]
            _ = U * (yM * z') * Us := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  let c := cUaut h U hU
  have hc : ∀ g' : ↥(StatedSU 4 (p ^ f) K), gMat (c g') = U * gMat g' * Us := fun g' => by
    rw [gMat_cUaut, hUs]
  have hxy' : ∀ g' : ↥(StatedSU 4 (p ^ f) K), gMat g' * GenLocU4Out.xi = GenLocU4Out.xi * gMat g' →
      gMat g' * yM = yM * gMat g' → g' ∈ Γ.comap c.toMonoidHom := by
    intro g' a b
    show c g' ∈ Γ
    apply hxy
    · rw [hc]; exact (comm_conj h1 hxe).2 a
    · rw [hc]; exact (comm_conj h1 hye).2 b
  have hxz' : ∀ g' : ↥(StatedSU 4 (p ^ f) K), gMat g' * GenLocU4Out.xi = GenLocU4Out.xi * gMat g' →
      gMat g' * z' = z' * gMat g' → g' ∈ Γ.comap c.toMonoidHom := by
    intro g' a b
    show c g' ∈ Γ
    apply hxz
    · rw [hc]; exact (comm_conj h1 hxe).2 a
    · rw [hc]; exact (comm_conj h1 hze).2 b
  have hxyz' : ∀ g' : ↥(StatedSU 4 (p ^ f) K), gMat g' * GenLocU4Out.xi = GenLocU4Out.xi * gMat g' →
      gMat g' * (yM * z') = (yM * z') * gMat g' → g' ∈ Γ.comap c.toMonoidHom := by
    intro g' a b
    show c g' ∈ Γ
    apply hxyz
    · rw [hc]; exact (comm_conj h1 hxe).2 a
    · rw [hc]; exact (comm_conj h1 hyz).2 b
  have hmain := cx_le_of_hyp_yM hp hp2 hK hq (Γ.comap c.toMonoidHom) z' hz'U hz'z' hz'x hz'y hz'n hxy' hxz' hxyz'
  intro g hg
  have hg' : gMat (c.symm g) * GenLocU4Out.xi = GenLocU4Out.xi * gMat (c.symm g) := by
    rw [← c.apply_symm_apply g, hc] at hg
    exact (comm_conj h1 hxe).1 hg
  have := hmain (c.symm g) hg'
  have h3 : c (c.symm g) ∈ Γ := this
  rwa [c.apply_symm_apply] at h3

theorem su4Q2SplitStmt_holds_of (hQ2 : GenLocU4Q.Su4Q2Stmt K p f) : GenLocU4Q.Su4Q2SplitStmt K p f := by
  intro hp hp2 hK hq Γ x y z hxU hyU hzU hx hy hz hxy hxz hyz hzn hH
  obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := hH
  have hxm : (x : Matrix (Fin 4) (Fin 4) K) * x = -1 := by
    have := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) hx
    simpa [Units.val_mul] using this
  have hym : (y : Matrix (Fin 4) (Fin 4) K) * y = -1 := by
    have := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) hy
    simpa [Units.val_mul] using this
  have hzm : (z : Matrix (Fin 4) (Fin 4) K) * z = 1 := by
    have := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) hz
    simpa [Units.val_mul] using this
  have hyx : (y : Matrix (Fin 4) (Fin 4) K) * x = -((x : Matrix (Fin 4) (Fin 4) K) * y) := by
    rw [hxy]
    simp
  have hzn' : ∀ c : K, (z : Matrix (Fin 4) (Fin 4) K) ≠ c • 1 := fun c hc => hzn ⟨c, hc⟩
  obtain ⟨Ux, hUxU, hxUx, hyUx⟩ := GenLocU4Q2.exists_q2_frame hp hp2 hK hq hxU hyU hxm hym hxy
  obtain ⟨Uy, hUyU, hyUy, hxUy⟩ := GenLocU4Q2.exists_q2_frame hp hp2 hK hq hyU hxU hym hxm hyx
  have hCx : ∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * x = x * g → g ∈ Γ := by
    intro g hg
    exact levi_of_frame hp hp2 hK hq Γ hUxU hxUx hyUx hzU hzm hxz.symm hyz.symm hzn'
      (fun g a b => h1 g ((comm_iff g x).2 a) ((comm_iff g y).2 b))
      (fun g a b => h2 g ((comm_iff g x).2 a) ((comm_iff g z).2 b))
      (fun g a b => h4 g ((comm_iff g x).2 a) ((comm_iff g (y * z)).2 b)) g ((comm_iff g x).1 hg)
  have hCy : ∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * y = y * g → g ∈ Γ := by
    intro g hg
    exact levi_of_frame hp hp2 hK hq Γ hUyU hyUy hxUy hzU hzm hyz.symm hxz.symm hzn'
      (fun g a b => h1 g ((comm_iff g x).2 b) ((comm_iff g y).2 a))
      (fun g a b => h3 g ((comm_iff g y).2 a) ((comm_iff g z).2 b))
      (fun g a b => h5 g ((comm_iff g y).2 a) ((comm_iff g (x * z)).2 b)) g ((comm_iff g y).1 hg)
  exact hQ2 hp hp2 hK hq Γ x y hx hy hxy hxU hyU hCx hCy

theorem su4Q2SplitStmt_holds : GenLocU4Q.Su4Q2SplitStmt K p f :=
  su4Q2SplitStmt_holds_of GenLocU4Q2.su4Q2Stmt_holds

end GenLocU4Q2s

end CFSG.GH74.Generic.BProg.B2
