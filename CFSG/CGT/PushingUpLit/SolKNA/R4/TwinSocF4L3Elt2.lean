module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Defs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Aut
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Two

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.ClassicalInvolution.Q3.TL4.MF163 CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

variable {A : Type} [Group A] [Finite A] {T : Subgroup A} [T.Normal] {R : Subgroup A}
  {S : Sylow 2 R} {z : A} {K : Type} [Field K] [Finite K] {e : ↥T ≃* projectiveSL 3 K}
  (F : L3Frame T z K e) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
  (hK : Nat.card K = p ^ f) (h2 : (2 : K) ≠ 0) (hZ : Subgroup.center (projectiveSL 3 K) = ⊥)

include hp hp2 hf hK h2 hZ

theorem two_elt_conj {l ν : Kˣ} {k : ℕ} (hk : 2 ≤ k) (hlord : orderOf l = 2 ^ k)
    (hmax : ¬ 2 ^ (k + 1) ∣ Nat.card Kˣ) (hl : F.scal l ∈ sylowSet S) {b : A} (hb : b ∈ sylowSet S)
    (hbι : F.ι b = conjAut 3 K (sigMat ν) * dualAut 3 K) {ψ : MulAut ↥T}
    (hψ : ψ ∈ autCentOf T (sylowSet S)) {j : ℕ} (hψj : ψ ^ 2 ^ j = 1) :
    ∃ B : GL (Fin 2) K, (B : Matrix (Fin 2) (Fin 2) K).det = 1 ∧
      ψ = MulAut.conjNormal (F.π ⟨B, Subgroup.mem_top _⟩) := by
  rw [mem_autCentOf_iff] at hψ
  set β : MulAut (projectiveSL 3 K) := MulAut.congr F.e' ψ with hβdef
  have hcomm : ∀ s ∈ sylowSet S, β * F.ι s = F.ι s * β := fun s hs => by
    rw [F.ι_apply, hβdef, ← map_mul, ← map_mul, hψ s hs]
  have hβ : β ^ 2 ^ j = 1 := by rw [hβdef, ← map_pow, hψj, map_one]
  have hβc : β (proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l))) =
      proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l)) := by
    apply apply_eq_of_comm_conj hZ
    have h1 : F.ι (F.scal l) =
        MulAut.conj (proj 3 K (blkP 1 (GeneralLinearGroup.scalar (Fin 2) l))) :=
      F.ι_π ⟨GeneralLinearGroup.scalar (Fin 2) l, Subgroup.mem_top _⟩
    rw [← h1]
    exact hcomm _ hl
  have hβσ : β * (conjAut 3 K (sigMat ν) * dualAut 3 K) =
      (conjAut 3 K (sigMat ν) * dualAut 3 K) * β := by
    rw [← hbι]
    exact hcomm b hb
  obtain ⟨B', hB'det, hB'⟩ := eq_blk_of_pow hp hp2 hf hK h2 hlord hk hmax ν hβ hβc hβσ
  refine ⟨B', hB'det, ?_⟩
  have h1 : β = F.ι (F.π ⟨B', Subgroup.mem_top _⟩) := by
    rw [F.ι_π, hB']
    have := LinearFlag.conjAut_toGL (K := K) (blkP 1 B')
    rw [toGL_blkP, one_mul, inv_one, mul_one] at this
    exact this
  rw [F.ι_apply] at h1
  exact (MulAut.congr F.e').injective h1

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3
