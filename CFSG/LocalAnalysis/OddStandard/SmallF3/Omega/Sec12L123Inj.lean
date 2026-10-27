module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec123_autIn_equiv {X A : Subgroup G} (hXN : X ≤ normalizer (A : Set G))
    (hker : X ⊓ centralizer (A : Set G) = ⊥) : Nonempty (↥(autIn X A) ≃* ↥X) := by
  classical
  have hAut : autIn X A =
      (A.normalizerMonoidHom.domRestrict (X.subgroupOf (normalizer (A : Set G)))).range := by
    unfold autIn
    rw [MonoidHom.domRestrict_range]
  have hinj : Function.Injective
      (A.normalizerMonoidHom.domRestrict (X.subgroupOf (normalizer (A : Set G)))) := by
    refine (injective_iff_map_eq_one _).mpr ?_
    intro k hk
    have hkker : (k : ↥(normalizer (A : Set G))) ∈ A.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker]
      simpa using hk
    rw [Subgroup.normalizerMonoidHom_ker] at hkker
    have hcent : ((k : ↥(normalizer (A : Set G))) : G) ∈ centralizer (A : Set G) := hkker
    have hX : ((k : ↥(normalizer (A : Set G))) : G) ∈ X :=
      Subgroup.mem_subgroupOf.mp k.2
    have hbot : ((k : ↥(normalizer (A : Set G))) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hker]
      exact ⟨hX, hcent⟩
    have hone : ((k : ↥(normalizer (A : Set G))) : G) = 1 := Subgroup.mem_bot.mp hbot
    exact Subtype.ext (Subtype.ext (by simpa using hone))
  rw [hAut]
  exact ⟨(MonoidHom.ofInjective hinj).symm.trans (Subgroup.subgroupOfEquivOfLe hXN)⟩

end CFSG.OddStandard.SmallF3.Omega
