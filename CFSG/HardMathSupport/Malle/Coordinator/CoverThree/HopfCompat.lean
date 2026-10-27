module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PerfectCover.HopfCover

public section

open Subgroup CFSG.RankThree.PerfectCover

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThree

theorem exists_surjective_compat_of_card_hopfMultiplier_le
    {S₀ E J : Type} [Group S₀] [Group E] [Group J] [Finite S₀]
    [Finite (hopfMultiplier J)] (hS₀ : Group.IsPerfect S₀) (hE : Group.IsPerfect E)
    (p₀ : S₀ →* J) (hp₀ : Function.Surjective p₀) (hk₀ : p₀.ker ≤ center S₀)
    (p : E →* J) (hp : Function.Surjective p) (hk : p.ker ≤ center E)
    (hcard : Nat.card (hopfMultiplier J) ≤ Nat.card p₀.ker) :
    ∃ α : S₀ →* E, Function.Surjective α ∧ ∀ s, p (α s) = p₀ s := by
  have := hS₀
  have := hE
  have : Group.IsPerfect J := Group.IsPerfect.ofSurjective hp₀
  set h₀ : HopfCover J →* S₀ := hopfLift p₀ hp₀ hk₀
  have h₀s : Function.Surjective h₀ := hopfLift_surjective p₀ hp₀ hk₀
  have hmap : (hopfMultiplier J).map h₀ = p₀.ker := map_hopfMultiplier_hopfLift p₀ hp₀ hk₀
  have hcomp : ∀ u, p₀ (h₀ u) = hopfCoverMap J u := fun u =>
    DFunLike.congr_fun (comp_hopfLift p₀ hp₀ hk₀) u
  let ψ : hopfMultiplier J →* p₀.ker :=
    (h₀.comp (hopfMultiplier J).subtype).codRestrict p₀.ker fun m => by
      rw [← hmap]
      exact ⟨m, m.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨c, hc⟩
    rw [← hmap] at hc
    obtain ⟨m, hm, rfl⟩ := hc
    exact ⟨⟨m, hm⟩, rfl⟩
  have hψb : Function.Bijective ψ := hψs.bijective_of_nat_card_le hcard
  have h₀i : Function.Injective h₀ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hum : u ∈ hopfMultiplier J := by
      change hopfCoverMap J u = 1
      rw [← hcomp, hu, map_one]
    have h1 : ψ ⟨u, hum⟩ = 1 := Subtype.ext hu
    exact congrArg Subtype.val (hψb.1 (h1.trans (map_one ψ).symm))
  let e : HopfCover J ≃* S₀ := MulEquiv.ofBijective h₀ ⟨h₀i, h₀s⟩
  refine ⟨(hopfLift p hp hk).comp e.symm.toMonoidHom,
    (hopfLift_surjective p hp hk).comp e.symm.surjective, fun s => ?_⟩
  have h1 : p (hopfLift p hp hk (e.symm s)) = hopfCoverMap J (e.symm s) :=
    DFunLike.congr_fun (comp_hopfLift p hp hk) (e.symm s)
  have h2 : p₀ (h₀ (e.symm s)) = hopfCoverMap J (e.symm s) := hcomp _
  have h3 : h₀ (e.symm s) = s := e.apply_symm_apply s
  show p (hopfLift p hp hk (e.symm s)) = p₀ s
  rw [h1, ← h2, h3]

end CFSG.HardMathSupport.Malle.Coordinator.CoverThree
