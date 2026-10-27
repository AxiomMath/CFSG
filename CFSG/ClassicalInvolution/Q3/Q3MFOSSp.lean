module

public import CFSG.ClassicalInvolution.Q3.Q3MFOSSpB
public import CFSG.ClassicalInvolution.Q3.Q3PPFundAbs
public import CFSG.ClassicalInvolution.Q3.Q3NMInner

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFO.Sp

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3PP CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.Models.SymplecticPairs

section Group

variable {X : Type} [Group X]

theorem mem_center_of_conj_eq_one {z : X} (h : MulAut.conj z = 1) : z ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro g
  have := congrArg (fun φ : MulAut X => φ g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

end Group


theorem oddCoreIn_fixed_eq_bot_psp_std
    (ρ : MulAut (StatedSp 2 (GaloisField 3 1) ⧸ Subgroup.center (StatedSp 2 (GaloisField 3 1))))
    (hρ2 : ρ * ρ = 1)
    (hU : ρ (QuotientGroup.mk (tU (GaloisField 3 1))) = QuotientGroup.mk (tU (GaloisField 3 1)))
    (hL : ρ (QuotientGroup.mk (tL (GaloisField 3 1))) = QuotientGroup.mk (tL (GaloisField 3 1))) :
    oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hF : Nat.card (GaloisField 3 1) = 3 := by simpa using GaloisField.card 3 1 one_ne_zero
  have hadm : StatedLieAdmissible .PSp 2 3 1 := ⟨hp, le_rfl, by norm_num, by decide⟩
  have hKq : CFSG.Open.IsQuasisimple (StatedSp 2 (GaloisField 3 1)) :=
    (ModelFacts.modelClauseZero .PSp 2 3 1 hp trivial hadm).1
  have hFT : IsFundTag .PSp := trivial
  have hfin : Finite (StatedSp 2 (GaloisField 3 1)) :=
    ModelFacts.finite_modelUniv (by norm_num) hp hFT hadm
  have hperfS : Group.IsPerfect (StatedSp 2 (GaloisField 3 1)) := ⟨hKq.1⟩
  have hsimple : IsSimpleGroup (StatedSp 2 (GaloisField 3 1) ⧸
      Subgroup.center (StatedSp 2 (GaloisField 3 1))) := hKq.2
  obtain ⟨s, hs⟩ := exists_conj_of_fixes_quot hF hU hL
  have hxx : (QuotientGroup.mk s : StatedSp 2 (GaloisField 3 1) ⧸
      Subgroup.center (StatedSp 2 (GaloisField 3 1))) * QuotientGroup.mk s = 1 := by
    have h1 : MulAut.conj ((QuotientGroup.mk s : StatedSp 2 (GaloisField 3 1) ⧸
        Subgroup.center (StatedSp 2 (GaloisField 3 1))) * QuotientGroup.mk s) = 1 := by
      rw [map_mul, ← hs]
      exact hρ2
    have hc := mem_center_of_conj_eq_one h1
    rw [center_quotient_center_eq_bot_of_isQuasisimple hKq] at hc
    exact Subgroup.mem_bot.mp hc
  by_cases hx1 : (QuotientGroup.mk s : StatedSp 2 (GaloisField 3 1) ⧸
      Subgroup.center (StatedSp 2 (GaloisField 3 1))) = 1
  · have hρ1 : ρ = 1 := by rw [hs, hx1, map_one]
    have hperf : Group.IsPerfect (StatedSp 2 (GaloisField 3 1) ⧸
        Subgroup.center (StatedSp 2 (GaloisField 3 1))) :=
      isPerfect_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    rw [hρ1, fixedSubgroup_one_eq_top]
    exact oddCoreIn_top_eq_bot_of_perfect_simple hperf
  · have hx2 : orderOf (QuotientGroup.mk s : StatedSp 2 (GaloisField 3 1) ⧸
        Subgroup.center (StatedSp 2 (GaloisField 3 1))) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
    rw [hs, fixedSubgroup_conj_eq]
    let ψ : StatedSp 2 (GaloisField 3 1) →* (StatedSp 2 (GaloisField 3 1) ⧸
        Subgroup.center (StatedSp 2 (GaloisField 3 1))) := QuotientGroup.mk' _
    have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective _
    have hψk : ψ.ker ≤ Subgroup.center (StatedSp 2 (GaloisField 3 1)) :=
      le_of_eq (QuotientGroup.ker_mk' _)
    exact modelOddCentralizerFree3_proved .PSp 2 hp hFT hadm _ ψ hψs hψk _ hx2

theorem oddCoreIn_fixed_eq_bot_psp
    (ρ : MulAut (StatedSp 2 (GaloisField 3 1) ⧸ Subgroup.center (StatedSp 2 (GaloisField 3 1))))
    (hρ2 : ρ * ρ = 1) (R : Subgroup (StatedSp 2 (GaloisField 3 1)))
    (hR : R ∈ (CompData.model .PSp 2).fund)
    (hρR : ∀ r ∈ R, ρ (QuotientGroup.mk r) = QuotientGroup.mk r) :
    oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hadm : StatedLieAdmissible .PSp 2 3 1 := ⟨hp, le_rfl, by norm_num, by decide⟩
  have hR0 : longRootSp2 (GaloisField 3 1) 2 0 ∈ (CompData.model .PSp 2).fund :=
    (mem_fundamentalSubgroups_PSp_iff hadm _).mpr
      ((exists_conj_longBlock_iff 0 _).1 ⟨1, by ext x; simp [longRootSp2]⟩)
  obtain ⟨g, hg⟩ : ∃ g : StatedSp 2 (GaloisField 3 1), longRootSp2 (GaloisField 3 1) 2 0 =
      R.map (MulAut.conj g).toMonoidHom :=
    ModelFacts.fundamentalSingleClass .PSp 2 3 1 hp trivial hadm (by decide) (by decide) R hR _ hR0
  let e : (StatedSp 2 (GaloisField 3 1) ⧸ Subgroup.center (StatedSp 2 (GaloisField 3 1))) ≃*
      (StatedSp 2 (GaloisField 3 1) ⧸ Subgroup.center (StatedSp 2 (GaloisField 3 1))) :=
    MulAut.conj (QuotientGroup.mk g)
  have hfix : ∀ t ∈ longRootSp2 (GaloisField 3 1) 2 0,
      MulAut.congr e ρ (QuotientGroup.mk t) = QuotientGroup.mk t := by
    intro t ht
    rw [hg] at ht
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ht
    have h1 : e.symm (QuotientGroup.mk ((MulAut.conj g).toMonoidHom r)) = QuotientGroup.mk r := by
      change (MulAut.conj (QuotientGroup.mk g)).symm (QuotientGroup.mk (g * r * g⁻¹)) = _
      rw [MulAut.conj_symm_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      group
    change e (ρ (e.symm (QuotientGroup.mk ((MulAut.conj g).toMonoidHom r)))) = _
    rw [h1, hρR r hr]
    change MulAut.conj (QuotientGroup.mk g) (QuotientGroup.mk r) = QuotientGroup.mk (g * r * g⁻¹)
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
  have h1 := oddCoreIn_fixed_eq_bot_psp_std (MulAut.congr e ρ) (by rw [← map_mul, hρ2, map_one])
    (hfix _ ⟨_, rfl⟩) (hfix _ ⟨_, rfl⟩)
  have h2 := oddCoreIn_fixed_congr_eq_bot' e.symm _ h1
  have h3 : MulAut.congr e.symm (MulAut.congr e ρ) = ρ := by
    refine MulEquiv.ext fun x => ?_
    change e.symm (e (ρ (e.symm (e.symm.symm x)))) = ρ x
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]
  rwa [h3] at h2

theorem fixedOddFreeFund_psp : FixedOddFreeFund (CompData.model .PSp 2) := by
  intro ρ hρ2 ⟨R, hR, hρR⟩
  exact oddCoreIn_fixed_eq_bot_psp ρ hρ2 R hR hρR

end CFSG.ClassicalInvolution.Q3.Q3MFO.Sp
