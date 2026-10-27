module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscFusionR8
public import CFSG.ClassicalInvolution.AschTight.S19COrd
public import CFSG.ClassicalInvolution.Q3.Q3TLTDatum
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

theorem quat_sq_center (n : ℕ) :
    (QuaternionGroup.a n : QuaternionGroup n) * QuaternionGroup.a n = 1 := by
  rw [QuaternionGroup.a_mul_a, ← QuaternionGroup.a_zero, ← two_mul]
  congr 1
  exact_mod_cast ZMod.natCast_self (2 * n)

theorem quat_center_ne {n : ℕ} [NeZero n] :
    (QuaternionGroup.a n : QuaternionGroup n) ≠ 1 := by
  rw [← QuaternionGroup.a_zero]
  intro h
  have h1 : ((n : ℕ) : ZMod (2 * n)) = 0 := QuaternionGroup.a.inj h
  rw [ZMod.natCast_eq_zero_iff] at h1
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have := Nat.le_of_dvd hn h1
  omega

theorem quat_pair {n m : ℕ} (hnm : n = 2 * m) :
    (QuaternionGroup.a m : QuaternionGroup n) * QuaternionGroup.a m = QuaternionGroup.a n ∧
      (QuaternionGroup.xa 0 : QuaternionGroup n) * QuaternionGroup.xa 0 = QuaternionGroup.a n ∧
      (QuaternionGroup.a m * QuaternionGroup.xa 0 : QuaternionGroup n) *
          (QuaternionGroup.a m * QuaternionGroup.xa 0) = QuaternionGroup.a n := by
  refine ⟨?_, ?_, ?_⟩
  · rw [QuaternionGroup.a_mul_a]
    congr 1
    rw [hnm]
    push_cast
    ring
  · rw [QuaternionGroup.xa_mul_xa]
    congr 1
    ring
  · rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_xa]
    congr 1
    ring

theorem quat_split {n : ℕ} (x : QuaternionGroup n) :
    x * x = QuaternionGroup.a n ∨ ∃ y z : QuaternionGroup n,
      y * y = QuaternionGroup.a n ∧ z * z = QuaternionGroup.a n ∧ x = y * z := by
  rcases x with i | i
  · right
    refine ⟨QuaternionGroup.xa 0, QuaternionGroup.xa (i - n), ?_, ?_, ?_⟩
    · rw [QuaternionGroup.xa_mul_xa]
      congr 1
      ring
    · rw [QuaternionGroup.xa_mul_xa]
      congr 1
      ring
    · rw [QuaternionGroup.xa_mul_xa]
      congr 1
      ring
  · left
    rw [QuaternionGroup.xa_mul_xa]
    congr 1
    ring

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem quat_center_eq (hd : TightDatum R S t) {n : ℕ} [NeZero n]
    (e : ↥(S : Subgroup R) ≃* QuaternionGroup n) :
    (((e.symm (QuaternionGroup.a n) : ↥(S : Subgroup R)) : ↥R) : Y) = t := by
  set u : ↥(S : Subgroup R) := e.symm (QuaternionGroup.a n) with hu
  have hu2 : u * u = 1 := by
    rw [hu, ← map_mul, quat_sq_center, map_one]
  have hu1 : u ≠ 1 := by
    rw [hu]
    intro h
    exact quat_center_ne (by simpa using congrArg e h)
  have hord : orderOf (((u : ↥R) : Y)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      have := congrArg (fun v : ↥(S : Subgroup R) => ((v : ↥R) : Y)) hu2
      simpa using this
    · intro h
      apply hu1
      exact Subtype.ext (Subtype.ext h)
  exact hd.eq_of_orderOf_eq_two (u : ↥R).2 hord

omit [Finite Y] in
theorem sq_eq_of_quat {n : ℕ} (e : ↥(S : Subgroup R) ≃* QuaternionGroup n)
    (hct : (((e.symm (QuaternionGroup.a n) : ↥(S : Subgroup R)) : ↥R) : Y) = t)
    {q : QuaternionGroup n} (hq : q * q = QuaternionGroup.a n) :
    ((((e.symm q : ↥(S : Subgroup R)) : ↥R) : Y)) * ((((e.symm q : ↥(S : Subgroup R)) : ↥R) : Y)) =
      t := by
  have : e.symm q * e.symm q = e.symm (QuaternionGroup.a n) := by rw [← hq, map_mul]
  rw [← hct, ← this]
  rfl

theorem exists_S₀_pair_R (hd : TightDatum R S t) :
    ∃ r₁ ∈ (S : Subgroup R).map R.subtype, ∃ r₂ ∈ (S : Subgroup R).map R.subtype,
      r₁ * r₁ = t ∧ r₂ * r₂ = t ∧ (r₁ * r₂) * (r₁ * r₂) = t := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hd.quat
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hct := quat_center_eq hd e
  have hm : 2 ^ (r - 2) = 2 * 2 ^ (r - 3) := by
    rw [← pow_succ']
    congr 1
    omega
  obtain ⟨h1, h2, h3⟩ := quat_pair hm
  set u₁ : ↥(S : Subgroup R) := e.symm (QuaternionGroup.a (2 ^ (r - 3) : ℕ))
  set u₂ : ↥(S : Subgroup R) := e.symm (QuaternionGroup.xa 0)
  refine ⟨((u₁ : ↥R) : Y), ⟨u₁, u₁.2, rfl⟩, ((u₂ : ↥R) : Y), ⟨u₂, u₂.2, rfl⟩,
    sq_eq_of_quat e hct h1, sq_eq_of_quat e hct h2, ?_⟩
  have h3' := sq_eq_of_quat e hct h3
  rw [map_mul] at h3'
  exact h3'

theorem exists_sq_of_conjSub_ne (hd : TightDatum R S t) {A : Subgroup Y} {s : Y}
    (hs : s ∈ (S : Subgroup R).map R.subtype) (hsA : conjSub s A ≠ A) :
    ∃ s' ∈ (S : Subgroup R).map R.subtype, s' * s' = t ∧ conjSub s' A ≠ A := by
  obtain ⟨r, -, ⟨e⟩⟩ := hd.quat
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hct := quat_center_eq hd e
  obtain ⟨x, hx, rfl⟩ := hs
  have hxe : (⟨x, hx⟩ : ↥(S : Subgroup R)) = e.symm (e ⟨x, hx⟩) := (e.symm_apply_apply _).symm
  rcases quat_split (e ⟨x, hx⟩) with h | ⟨y, z, hy, hz, hyz⟩
  · refine ⟨R.subtype x, ⟨x, hx, rfl⟩, ?_, hsA⟩
    have := sq_eq_of_quat e hct h
    rwa [← hxe] at this
  · have hxyz : (R.subtype x : Y) = (((e.symm y : ↥(S : Subgroup R)) : ↥R) : Y) *
        (((e.symm z : ↥(S : Subgroup R)) : ↥R) : Y) := by
      have h1 : (⟨x, hx⟩ : ↥(S : Subgroup R)) = e.symm y * e.symm z := by
        rw [hxe, hyz, map_mul]
      have := congrArg (fun v : ↥(S : Subgroup R) => ((v : ↥R) : Y)) h1
      simpa using this
    by_cases hzA : conjSub (((e.symm z : ↥(S : Subgroup R)) : ↥R) : Y) A = A
    · refine ⟨(((e.symm y : ↥(S : Subgroup R)) : ↥R) : Y), ⟨_, (e.symm y).2, rfl⟩,
        sq_eq_of_quat e hct hy, fun hyA => hsA ?_⟩
      rw [hxyz, conjSub_mul, hzA, hyA]
    · exact ⟨(((e.symm z : ↥(S : Subgroup R)) : ↥R) : Y), ⟨_, (e.symm z).2, rfl⟩,
        sq_eq_of_quat e hct hz, hzA⟩

theorem mul_t_comm_of_mem_R (hd : TightDatum R S t) {s : Y} (hs : s ∈ R) : s * t = t * s := by
  have hst : orderOf (s * t * s⁻¹) = 2 := by
    have := orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective t
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [this]
    exact hd.order
  have h := hd.eq_of_orderOf_eq_two (R.mul_mem (R.mul_mem hs hd.mem_right) (R.inv_mem hs)) hst
  calc s * t = s * t * s⁻¹ * s := by group
    _ = t * s := by rw [h]

end CFSG.ClassicalInvolution.Q3.TL4
