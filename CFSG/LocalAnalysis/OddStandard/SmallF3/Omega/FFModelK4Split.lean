module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_K4_split (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {x : ProjSim Q} (hx2 : x * x = 1) (hx : KM4 x) :
    ∃ ρ : ↥(simGroup Q), (QuotientGroup.mk ρ : ProjSim Q) = x ∧
      IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1) ∧
      ((∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = v) ∨
        (∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v)) := by
  obtain ⟨ρ, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨c, hc⟩ := ρ.2
  have hunits : ∀ c : (ZMod 3)ˣ, c = 1 ∨ c = -1 := by decide
  rcases hunits c with rfl | rfl
  · exfalso
    apply hx
    have hmem : (ρ : V ≃ₗ[ZMod 3] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      isSimilitude_one_iff.mp hc
    refine ⟨toProj Q ⟨(ρ : V ≃ₗ[ZMod 3] V), hmem⟩, ?_⟩
    rw [projOrthToProjSim_toProj]
    exact congrArg QuotientGroup.mk (Subtype.ext rfl)
  · refine ⟨ρ, rfl, hc, ?_⟩
    have h1 : ρ * ρ ∈ piSim Q :=
      (QuotientGroup.eq_one_iff (ρ * ρ)).mp (by rw [QuotientGroup.mk_mul]; exact hx2)
    rcases mem_piSim_iff.mp h1 with h | h
    · left
      intro v
      have := congrArg (fun g : simGroup Q => (g : V ≃ₗ[ZMod 3] V) v) h
      simpa using this
    · right
      intro v
      have := congrArg (fun g : simGroup Q => (g : V ≃ₗ[ZMod 3] V) v) h
      simpa [coe_piOrth_apply] using this

end CFSG.OddStandard.SmallF3.Omega
