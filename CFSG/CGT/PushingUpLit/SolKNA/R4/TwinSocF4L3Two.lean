module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Quat
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Frame
public import CFSG.ClassicalInvolution.Q3.TL4ExitDichA
public import CFSG.ClassicalInvolution.Q3.TL4MF163LU

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.ClassicalInvolution.Q3.TL4.MF163 CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups commutatorElement

variable {A : Type} [Group A] [Finite A] {T : Subgroup A} [T.Normal]
  (hC : Subgroup.centralizer (T : Set A) = ⊥) {R : Subgroup A} {S : Sylow 2 R} {z : A}
  (hd : TightDatum R S z) {K : Type} [Field K] [Finite K] {e : ↥T ≃* projectiveSL 3 K}
  (F : L3Frame T z K e)

@[expose] noncomputable def L3Frame.scal : Kˣ →* A :=
  F.π.comp ((GeneralLinearGroup.scalar (Fin 2)).codRestrict ⊤ (fun _ => Subgroup.mem_top _))

theorem L3Frame.scal_eq_one {μ : Kˣ} (h : F.scal μ = 1) : ∃ ω : Kˣ, ω ^ 3 = 1 ∧ μ = ω := by
  obtain ⟨ω, hω3, hω⟩ := F.hk _ h
  exact ⟨ω, hω3, scalar_injective hω⟩

include hC hd

theorem scalar_mem_tightCore {b : A} (hbK : b ∈ tightCore R) {ν : Kˣ}
    (hb : F.ι b = conjAut 3 K (sigMat ν) * dualAut 3 K) (μ : Kˣ) :
    F.π ⟨GeneralLinearGroup.scalar (Fin 2) μ, Subgroup.mem_top _⟩ ∈ tightCore R := by
  have hdet0 : (!![(μ : K), 0; 0, 1] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    simp [Matrix.det_fin_two_of]
  let A' : (⊤ : Subgroup (GL (Fin 2) K)) :=
    ⟨GeneralLinearGroup.mkOfDetNeZero !![(μ : K), 0; 0, 1] hdet0, Subgroup.mem_top _⟩
  have hA'C : F.π A' ∈ Subgroup.centralizer ({z} : Set A) := by
    have : F.π A' ∈ F.π.range := ⟨A', rfl⟩
    rw [F.hrange] at this
    exact this.2
  have hcK := commutator_mem_tightCore hd hA'C hbK
  have hdetA' : GeneralLinearGroup.det (A' : GL (Fin 2) K) = μ := Units.ext (by
    rw [GeneralLinearGroup.val_det_apply]
    simp [A', Matrix.det_fin_two_of])
  have h1 : F.ι ⁅F.π A', b⁆ =
      F.ι (F.π ⟨GeneralLinearGroup.scalar (Fin 2) μ, Subgroup.mem_top _⟩) := by
    rw [map_commutatorElement, F.ι_π, hb, commutator_conj, sig_dual_blkP, F.ι_π, ← map_inv,
      ← map_mul, ← map_inv, ← map_mul, hdetA']
    congr 3
    rw [_root_.mul_inv_rev, ← map_inv, inv_inv, ← mul_assoc, ← scalar_mul_comm, mul_assoc,
      mul_inv_cancel, mul_one]
  rw [← F.ι_injective hC h1]
  exact hcK

theorem not_dvd_card_units {r : ℕ} (hr : 4 ≤ r) (hcls : TightClsR r A R S z) {b : A}
    (hbS : b ∈ sylowSet S) {ν : Kˣ} (hb : F.ι b = conjAut 3 K (sigMat ν) * dualAut 3 K) :
    ¬ 2 ^ r ∣ Nat.card Kˣ := by
  intro hdvd
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  set μ : Kˣ := g ^ (Nat.card Kˣ / 2 ^ r) with hμ
  have hμord : orderOf μ = 2 ^ r := by
    have := orderOf_pow_orderOf_div (x := g) (n := 2 ^ r)
      (by rw [hg]; exact Nat.card_pos.ne') (hg ▸ hdvd)
    rwa [hg] at this
  have hsK := scalar_mem_tightCore hC hd F (sylow_le_tightCore S hbS) hb μ
  have hsR : F.scal μ ∈ R := tightCore_le R hsK
  have hs1 : (F.scal μ) ^ 2 ^ r = 1 := by
    rw [← map_pow, ← hμord, pow_orderOf_eq_one, map_one]
  obtain ⟨g', -, hg'⟩ := TA3.TightDatum.exists_conj_mem_of_pow S hsR hs1
  have h2 := pow_exp_of_datum (by omega) hcls hg'
  rw [conj_pow, mul_inv_eq_one, mul_eq_left, ← map_pow] at h2
  obtain ⟨ω, hω3, hω⟩ := F.scal_eq_one h2
  have hω2 : ω ^ 2 = 1 := by
    rw [← hω, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r), ← hμord,
      pow_orderOf_eq_one]
  rw [eq_one_of_sq_of_cube hω2 hω3] at hω
  have h3 : 2 ^ r ∣ 2 ^ (r - 1) := hμord ▸ orderOf_dvd_of_pow_eq_one hω
  have h4 := Nat.le_of_dvd (by positivity) h3
  have h5 : 2 ^ (r - 1) < 2 ^ r := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3
