module

public import CFSG.HardMathSupport.Curtis.Proving.SchurStepD
public import CFSG.HardMathSupport.Curtis.Proving.StepIHstep
public import CFSG.HardMathSupport.Curtis.Proving.ShortCentreFromStepI
public import CFSG.HardMathSupport.Curtis.Coordinator.AutCenterFFSplit

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.QuasithinUnique CFSG.AGLEmbedding

theorem commutator_blockU_mod_blockZ_trivial {G : Type} [Group G] [Finite G] {M L Q : Subgroup G}
    (hML : IsTwoPrimeComponent M L) (hL : IsShort2 L) (hQM : Q ≤ M)
    (hQN : Q ≤ Subgroup.normalizer (L : Set G))
    (hcent : barM M Q ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∀ t : ↥L, Odd (orderOf (t : G)) →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(t : G), hML.le t.2⟩ : ↥M) ∈
        ⁅barM M Q, barM M Q⁆ →
      ⁅blockU L, Subgroup.zpowers (t : G)⁆ ≤ blockZ L :=
  hstep_of_commutator_actsTriv hML (commutator_le_actsTrivSubgroup hML hL hQM hQN hcent)

theorem shortBlockCommutatorCentre_of_step :
    CFSG.HardMathSupport.Curtis.Coordinator.ShortBlockCommutatorCentre := by
  intro G _ _ M L Q hML hL hQM hQ3 hQN hcent
  exact commutator_inf_centre_of_step_i hML hL hQM hQ3 hQN hcent
    (commutator_blockU_mod_blockZ_trivial hML hL hQM hQN hcent)

end CFSG.HardMathSupport.Curtis.Proving

end
