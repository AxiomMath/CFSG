module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwKer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LieType.Multipliers.U43

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers.U43

theorem sw_exists_tau {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsOm6Z2 L)
    (hO : oddCoreIn L = ⊥) : ∃ τ : ↥L →* X₀, SwCentralTwo τ := by
  have hcore : CFSG.oddCore ↥L = ⊥ := by
    rw [oddCoreIn, CFSG.inSubgroup] at hO
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.oddCore ↥L) L.subtype_injective).mp hO
  obtain ⟨_, htwo⟩ := hL
  have hker : (QuotientGroup.mk' (CFSG.oddCore ↥L) : ↥L →* (↥L ⧸ CFSG.oddCore ↥L)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', hcore]
  have hinj : Function.Injective (QuotientGroup.mk' (CFSG.oddCore ↥L) : ↥L →* _) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hsurj : Function.Surjective (QuotientGroup.mk' (CFSG.oddCore ↥L) : ↥L →* _) :=
    QuotientGroup.mk'_surjective _
  let e : ↥L ≃* (↥L ⧸ CFSG.oddCore ↥L) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (CFSG.oddCore ↥L)) ⟨hinj, hsurj⟩
  have hcard : Nat.card (Subgroup.center ↥L) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, htwo.1]
  have hlie : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1 := by
    have heQ : (↥L ⧸ Subgroup.center ↥L) ≃*
        ((↥L ⧸ CFSG.oddCore ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.oddCore ↥L)) :=
      QuotientGroup.congr (Subgroup.center ↥L)
        (Subgroup.center (↥L ⧸ CFSG.oddCore ↥L)) e (Subgroup.map_center_eq e)
    exact CFSG.Blueprint.LieModel.of_mulEquiv heQ.symm htwo.2
  have hTwoL : IsTwoU43 ↥L := ⟨hcard, hlie⟩
  obtain ⟨f⟩ := nonempty_mulEquiv_X₀ hTwoL.2
  refine ⟨f.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L)), ?_, ?_, ?_⟩
  · exact f.surjective.comp (QuotientGroup.mk'_surjective _)
  · rw [MonoidHom.ker_comp_of_injective _ f.toMonoidHom f.injective,
      QuotientGroup.ker_mk', hTwoL.1]
  · rw [MonoidHom.ker_comp_of_injective _ f.toMonoidHom f.injective,
      QuotientGroup.ker_mk']

end CFSG.OddStandard.SmallF3.Omega
