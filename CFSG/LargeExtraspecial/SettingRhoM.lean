module

public import CFSG.LargeExtraspecial.Setting

public section

namespace CFSG.LargeExtraspecial.Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def ρM : S.M →* S.Mbar :=
  S.ρ.codRestrict S.Mbar fun m => ⟨m, rfl⟩

@[simp]
theorem coe_ρM (m : S.M) : (S.ρM m : S.O) = S.ρ m := rfl

theorem ρM_surjective : Function.Surjective S.ρM := by
  intro x
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp x.2
  exact ⟨m, Subtype.ext hm⟩

theorem ker_ρM : S.ρM.ker = S.Q := by
  ext m
  rw [MonoidHom.mem_ker]
  exact ⟨fun h => S.mem_Q_of_ρ_eq_one (congrArg Subtype.val h),
    fun h => Subtype.ext (S.ρ_eq_one_of_mem_Q h)⟩

theorem ρM_eq_one_iff {m : S.M} : S.ρM m = 1 ↔ (m : G) ∈ S.QG := by
  rw [← MonoidHom.mem_ker, S.ker_ρM]
  constructor
  · intro h
    exact S.mem_QG_iff.mpr ⟨m.2, h⟩
  · intro h
    simpa using (S.mem_QG_iff.mp h).2

end CFSG.LargeExtraspecial.Setting
