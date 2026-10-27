module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Inner
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtMain
public import CFSG.GH74.Generic.BProg.B2.GenLocL4QRank3Core

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

open GenLocU4Basic

namespace GenLocU4QLift

variable {K : Type} [Field K] [Finite K] {A : Type} [Group A]

@[expose] def IsLiftU {q : ℕ} (α : A →* MulAut ↥(StatedSU 4 q K)) (e : A) (u : GL (Fin 4) K) : Prop :=
  IsUnitaryU q (u : Matrix (Fin 4) (Fin 4) K) ∧ ∀ g : ↥(StatedSU 4 q K),
    (((α e g : ↥(StatedSU 4 q K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (u : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((u⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

omit [Finite K] in
theorem isUnitaryU_mul {p f : ℕ} (h : UnitaryFieldData p f K) {M N : Matrix (Fin 4) (Fin 4) K}
    (hM : IsUnitaryU (p ^ f) M) (hN : IsUnitaryU (p ^ f) N) : IsUnitaryU (p ^ f) (M * N) := by
  unfold IsUnitaryU at *
  have e : (M * N).map (· ^ (p ^ f)) = M.map (· ^ (p ^ f)) * N.map (· ^ (p ^ f)) := by
    have := Matrix.map_mul (f := (h.bar : K →+* K)) (L := M) (M := N)
    simpa [bar_eq_pow h] using this
  rw [e, Matrix.transpose_mul]
  calc (N.map (· ^ (p ^ f)))ᵀ * (M.map (· ^ (p ^ f)))ᵀ * (M * N)
      = (N.map (· ^ (p ^ f)))ᵀ * ((M.map (· ^ (p ^ f)))ᵀ * M) * N := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hM, Matrix.mul_one, hN]

omit [Finite K] in
theorem IsLiftU.mul {p f : ℕ} (h : UnitaryFieldData p f K) {α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)} {e g : A}
    {u w : GL (Fin 4) K} (hu : IsLiftU α e u) (hw : IsLiftU α g w) : IsLiftU α (e * g) (u * w) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [Units.val_mul]; exact isUnitaryU_mul h hu.1 hw.1
  · rw [map_mul, MulAut.mul_apply, hu.2, hw.2, _root_.mul_inv_rev]
    simp only [Units.val_mul, Matrix.mul_assoc]

omit [Finite K] in
theorem IsLiftU.fix {q : ℕ} {α : A →* MulAut ↥(StatedSU 4 q K)} {e : A} {u : GL (Fin 4) K} (hu : IsLiftU α e u)
    (g : ↥(StatedSU 4 q K))
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (u : Matrix (Fin 4) (Fin 4) K) =
      (u : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) : α e g = g := by
  apply Subtype.ext
  apply Units.ext
  rw [hu.2 g, ← hg, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

omit [Finite K] in
theorem IsLiftU.smul {p f : ℕ} {α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)} {e : A} {u : GL (Fin 4) K}
    (hu : IsLiftU α e u) {l : K} (hl0 : l ≠ 0) (hl : l ^ (p ^ f + 1) = 1) :
    IsLiftU α e (GenLocU4ExtMain.smulGL l hl0 u) := by
  refine ⟨?_, fun g => ?_⟩
  · rw [GenLocU4ExtMain.coe_smulGL]
    exact GenLocU4Inner.isUnitaryU_smul hu.1 hl
  · have := GenLocU4ExtMain.conj_congr (GenLocU4ExtMain.smulGL l hl0 u) u hl0 (GenLocU4ExtMain.coe_smulGL l hl0 u)
      (g : GL (Fin 4) K)
    have h2 := congrArg (fun z : GL (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K)) this
    simp only [Units.val_mul] at h2
    rw [hu.2 g]
    exact h2.symm

theorem IsLiftU.ne_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    {α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)} {e : A} {u : GL (Fin 4) K} (hu : IsLiftU α e u)
    (hns : ¬ ∃ l : K, (u : Matrix (Fin 4) (Fin 4) K) = l • 1) : e ≠ 1 := by
  rintro rfl
  apply hns
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hconj : ∀ g : GL (Fin 4) K, g ∈ StatedSU 4 (p ^ f) K → u * g * u⁻¹ = (1 : GL (Fin 4) K) * g * (1 : GL (Fin 4) K)⁻¹ := by
    intro g hg
    have h1 := hu.2 ⟨g, hg⟩
    rw [map_one, MulAut.one_apply] at h1
    apply Units.ext
    simpa [Units.val_mul] using h1.symm
  obtain ⟨l, -, hl⟩ := GenLocU4Basic.proportional_of_conj_eq h hp2 hconj
  exact ⟨l, by simpa using hl⟩

theorem mem_gammaAct_of_pairU {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) [Finite A]
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (hA : IsRank23 A) (hr : pRank 2 A = 3) {e g : A} {u w : GL (Fin 4) K}
    (hu : IsLiftU α e u) (hw : IsLiftU α g w)
    (hnu : ¬ ∃ l : K, (u : Matrix (Fin 4) (Fin 4) K) = l • 1) (hnw : ¬ ∃ l : K, (w : Matrix (Fin 4) (Fin 4) K) = l • 1)
    (hnuw : ¬ ∃ l : K, ((u * w : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = l • 1)
    (x : ↥(StatedSU 4 (p ^ f) K))
    (hxu : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (u : Matrix (Fin 4) (Fin 4) K) =
      (u : Matrix (Fin 4) (Fin 4) K) * ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hxw : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (w : Matrix (Fin 4) (Fin 4) K) =
      (w : Matrix (Fin 4) (Fin 4) K) * ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) : x ∈ gammaAct α := by
  have he : e * e = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 e
  have hf : g * g = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 g
  have hef : e * g = g * e := by have := hA.1; exact mul_comm' e g
  have hh : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have he1 : e ≠ 1 := hu.ne_one hp hp2 hK hnu
  have hf1 : g ≠ 1 := hw.ne_one hp hp2 hK hnw
  have hef1 : e * g ≠ 1 := (hu.mul hh hw).ne_one hp hp2 hK hnuw
  have hadm := GenLocL4Q.pairSub_adm hA hr he hf hef he1 hf1 hef1
  refine le_gammaAct α hadm ?_
  rw [GenLocBasic.mem_fixedIn_map]
  intro h hh'
  have hh'' : h = 1 ∨ h = e ∨ h = g ∨ h = e * g := by simpa [GenLocL4Q.pairSub] using hh'
  have hge : α e x = x := hu.fix x hxu
  have hgf : α g x = x := hw.fix x hxw
  rcases hh'' with rfl | rfl | rfl | rfl
  · simp
  · exact hge
  · exact hgf
  · rw [map_mul, MulAut.mul_apply, hgf, hge]

theorem mem_gammaAct_of_oneU {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) [Finite A]
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (hA : IsRank23 A) (hr : pRank 2 A = 2) {e : A} {u : GL (Fin 4) K}
    (hu : IsLiftU α e u) (hnu : ¬ ∃ l : K, (u : Matrix (Fin 4) (Fin 4) K) = l • 1)
    (x : ↥(StatedSU 4 (p ^ f) K))
    (hxu : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (u : Matrix (Fin 4) (Fin 4) K) =
      (u : Matrix (Fin 4) (Fin 4) K) * ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) : x ∈ gammaAct α := by
  have he : e * e = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 e
  have he1 : e ≠ 1 := hu.ne_one hp hp2 hK hnu
  have hcard : Nat.card A = 4 := by
    rw [GenLocBasic.card_eq_two_pow_pRank_type hA.1, hr]; norm_num
  have hord : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact he) he1
  have hidx : (Subgroup.zpowers e).index ≤ 2 := by
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers e)
    rw [Nat.card_zpowers, hord, hcard] at h1
    omega
  refine le_gammaAct α ((GenLocBasic.adm_iff_index hA.1 _).2 hidx) ?_
  rw [GenLocBasic.mem_fixedIn_map]
  intro h hh'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (show h ∈ Subgroup.zpowers e by simpa using hh')
  have hge : α e x = x := hu.fix x hxu
  have hx : (α e) ∈ MulAction.stabilizer (MulAut ↥(StatedSU 4 (p ^ f) K)) x := by
    rw [MulAction.mem_stabilizer_iff]; exact hge
  have := (MulAction.stabilizer (MulAut ↥(StatedSU 4 (p ^ f) K)) x).zpow_mem hx k
  rw [MulAction.mem_stabilizer_iff] at this
  rw [map_zpow]
  exact this

end GenLocU4QLift

end CFSG.GH74.Generic.BProg.B2
