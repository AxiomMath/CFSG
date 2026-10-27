module

public import CFSG.LieType.Steinberg.CentralExt.AdjointCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.LieType.Steinberg.Adjoint.Perfect
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

namespace CFSG.LieType.Steinberg.CentralExt.AdjointClosed

theorem hopfMultiplier_subsingleton {G : Type} [Group G] [Group.IsPerfect G]
    (hZ : Subgroup.center G = ⊥)
    (hsplit : ∀ {E : Type} [Group E] (π : E →* G), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ σ : G →* E, ∀ g, π (σ g) = g) :
    commutator (G ⧸ Subgroup.center G) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier (G ⧸ Subgroup.center G)) := by
  set q : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' _
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = Subgroup.center G := QuotientGroup.ker_mk' _
  have : Group.IsPerfect (G ⧸ Subgroup.center G) := Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier (G ⧸ Subgroup.center G) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq hker.le
      fun π hπ hcen => hsplit π hπ hcen)
  have hmem : ∀ a : q.ker, (a : G) = 1 := fun a =>
    (Subgroup.eq_bot_iff_forall _).1 hZ _ ((QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 a.2))
  have : Subsingleton q.ker := ⟨fun a b => Subtype.ext ((hmem a).trans (hmem b).symm)⟩
  exact ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans e1).toEquiv.subsingleton

section Closed

variable {K : Type} [Field K] [Finite K]

theorem f4_exists_section_of_central (hK : 5 ≤ Nat.card K) {E : Type*} [Group E]
    {π : E →* adjointGroup .F4 K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : adjointGroup .F4 K →* E, ∀ g, π (σ g) = g := by
  obtain ⟨-, ⟨O⟩, hP, -⟩ := f4_conclusionB K
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  exact exists_section_of_central (rootOperatorFamily .F4) hK cartan_mul_cartanInvF4
    (f4_chevalleyExtras K O C hC) hP hπ hcen

theorem e8_exists_section_of_central (hK : 5 ≤ Nat.card K) {E : Type*} [Group E]
    {π : E →* adjointGroup .E8 K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ σ : adjointGroup .E8 K →* E, ∀ g, π (σ g) = g := by
  obtain ⟨-, ⟨O⟩, hP, -⟩ := e8_conclusionB K
  obtain ⟨C, -, hC⟩ := e8_commutatorFormula K O
  exact exists_section_of_central (rootOperatorFamily .E8) hK cartan_mul_cartanInvE8
    (e8_chevalleyExtras K O C hC) hP hπ hcen

end Closed

section Multiplier

variable {K : Type} [Field K] [Finite K]

theorem f4_hopfMultiplier (hK : 5 ≤ Nat.card K) :
    commutator (AdjointQuotient .F4 K) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) := by
  have : Group.IsPerfect ↥(adjointGroup .F4 K) := isPerfect_f4 K
  exact hopfMultiplier_subsingleton center_adjointGroup_eq_bot
    fun π hπ hcen => f4_exists_section_of_central hK hπ hcen

theorem e8_hopfMultiplier (hK : 5 ≤ Nat.card K) :
    commutator (AdjointQuotient .E8 K) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E8 K)) := by
  have : Group.IsPerfect ↥(adjointGroup .E8 K) := isPerfect_e8 K
  exact hopfMultiplier_subsingleton center_adjointGroup_eq_bot
    fun π hπ hcen => e8_exists_section_of_central hK hπ hcen

end Multiplier

end CFSG.LieType.Steinberg.CentralExt.AdjointClosed
