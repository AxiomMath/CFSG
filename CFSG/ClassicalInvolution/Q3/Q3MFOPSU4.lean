module

public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Top
public import CFSG.ClassicalInvolution.Q3.Q3PPWireAll

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups


theorem fixedOddFreeFund_psu4 : FixedOddFreeFund (CompData.model .PSU 4) := by
  have hadm : StatedLieAdmissible .PSU 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hadmS : StatedLieAdmissible .PSp 2 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hSp : CFSG.Open.IsQuasisimple (StatedSp 2 (GaloisField 3 1)) :=
    (ModelFacts.modelClauseZero .PSp 2 3 1 Nat.prime_three trivial hadmS).1
  have hSpZ : IsPGroup 2 (Subgroup.center (StatedSp 2 (GaloisField 3 1))) :=
    (modelFiniteCenterTwoGroup3 .PSp 2 Nat.prime_three trivial hadmS).2
  have hq : CFSG.Open.IsQuasisimple (Su F9 3 1 4) :=
    open_isQuasisimple_su_of_three_le card_F9 (by norm_num) (by decide)
  obtain ⟨e, he⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
  obtain ⟨E, hE⟩ : ∃ E : (CompData.model .PSU 4).G ⧸ Subgroup.center (CompData.model .PSU 4).G ≃*
      Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4),
      ∀ r, E (QuotientGroup.mk r) = QuotientGroup.mk (e r) :=
    ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e), fun r => rfl⟩
  intro ρ hρ2 ⟨R, hR, hρR⟩
  obtain ⟨g₀, hg₀⟩ := (mem_longRootSetU_iff (by norm_num)).mp ((he R).mp hR)
  have hρ'2 : MulAut.congr E ρ * MulAut.congr E ρ = 1 := by
    rw [← map_mul, hρ2, map_one]
  have hfix' : ∀ r ∈ (rootSU2 F9 3 1 (by norm_num : 2 ≤ 4)).map (MulAut.conj g₀).toMonoidHom,
      MulAut.congr E ρ (QuotientGroup.mk r) = QuotientGroup.mk r := by
    intro r' hr'
    rw [← hg₀] at hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    have h1 : E.symm (QuotientGroup.mk (e r)) = QuotientGroup.mk r :=
      (MulEquiv.symm_apply_eq E).mpr (hE r).symm
    show E (ρ (E.symm (QuotientGroup.mk (e r)))) = QuotientGroup.mk (e r)
    rw [h1, hρR r hr, hE]
  have hcore := Q3MFOU4.oddCoreIn_fixed_eq_bot_su4 hq Q3MFOU4.isPGroup_center_su4 hSp hSpZ
    (MulAut.congr E ρ) hρ'2 g₀ hfix'
  have h2 := oddCoreIn_fixed_congr_eq_bot' E.symm _ hcore
  have h3 : MulAut.congr E.symm (MulAut.congr E ρ) = ρ := by
    ext x
    simp [MulAut.congr_apply]
  rwa [h3] at h2

theorem mfComp_psu4 : MFComp (CompData.model .PSU 4) := Or.inr fixedOddFreeFund_psu4

end CFSG.ClassicalInvolution.Q3.Q3PP
