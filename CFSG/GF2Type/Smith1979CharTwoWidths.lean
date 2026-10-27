module

public import CFSG.GF2Type.Widths1112.Width11
public import CFSG.GF2Type.Widths1112.Width12
public import CFSG.GF2Type.Widths1112.Co2ModuleUniqueness
public import CFSG.LargeExtraspecial.AS35Holds

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint CFSG.Open

section Certs

theorem smith1979_widths_eleven_twelve_charTwo {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hchar : IsCharTwoType G) {z : G} (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G)))) {w : ℕ}
    (hcard : Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
      2 ^ (1 + 2 * w))
    (Mbar : Type) [Group Mbar]
    (hMbar : timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar) :
    (w = 11 → Nonempty (Mbar ≃* NativeSporadic.Co2) → NativeSporadic.IsSporadic G .B) ∧
      (w = 12 → Nonempty (Mbar ≃* NativeSporadic.Co1) → NativeSporadic.IsSporadic G .M) := by
  refine ⟨fun hw hCo2 => ?_, fun hw hCo1 => ?_⟩
  · subst hw
    exact (Widths1112.widthEleven_false Widths1112.co2ModuleUniqueness_holds
      LargeExtraspecial.S14.aschbacherSmith35Input_holds hchar hz hext hcard hMbar hCo2).elim
  · subst hw
    exact (Widths1112.widthTwelve_false LargeExtraspecial.S14.aschbacherSmith35Input_holds hchar
      hz hext hcard hMbar hCo1).elim

end Certs

end CFSG.GF2Type
