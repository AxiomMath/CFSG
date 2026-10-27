module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.CoreFrobenius
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.CoreRestrict

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] {m n : ℕ}

theorem exists_heartEquiv_of_shape (hn : 7 ≤ n) (ι : Fin m ↪ Fin n) (hmn : m + 1 = n)
    (r : alternatingGroup (Fin n) →* AddMonoid.End X)
    (hirr : ∀ Y : AddSubgroup X, (∀ g, ∀ y ∈ Y, r g y ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (hfix : ∀ x : X, (∀ g, r g x = x) → x = 0)
    (hK : NatShapeA (r.comp (altLift ι)) (alternatingGroup (Fin m)).subtype) :
    ∃ Θ : altHeart n ≃+ X,
      ∀ (g : alternatingGroup (Fin n)) z, Θ (altAct (g : Perm (Fin n)) z) = r g (Θ z) := by
  classical
  obtain ⟨ω, hι⟩ := exists_range_iff_ne ι hmn
  by_cases hC : ∃ v : X, v ≠ 0 ∧ ∀ σ : alternatingGroup (Fin m), r (altLift ι σ) v = v
  · obtain ⟨v, hv0, hvK⟩ := hC
    exact exists_heartEquiv_of_fixed (by omega) ι hι r hirr hfix hv0 hvK
  push Not at hC
  have hK0 : ∀ v : X, (∀ σ : alternatingGroup (Fin m), r (altLift ι σ) v = v) → v = 0 :=
    fun v hv => by
      by_contra h
      obtain ⟨σ, hσ⟩ := hC v h
      exact hσ (hv σ)
  obtain ⟨M₀, M₁, hM, h₀, h₁, π, hπ, hker, heq⟩ := hK
  have hπinj : Function.Injective π := by
    refine (injective_iff_map_eq_zero π).2 fun u hu => ?_
    have hu' : u ∈ M₀.addSubgroupOf M₁ := by rw [← hker]; exact hu
    exact Subtype.ext (hK0 _ fun σ => h₀ σ _ hu')
  by_cases hM₁ : M₁ = ⊤
  ·
    have hmem : ∀ x : X, x ∈ M₁ := fun x => hM₁ ▸ AddSubgroup.mem_top x
    let θ₀ : X →+ altHeart m :=
      { toFun := fun x => π ⟨x, hmem x⟩
        map_zero' := by
          rw [← map_zero π]; rfl
        map_add' := fun x y => by
          rw [← map_add]; rfl }
    have hθ₀ : Function.Bijective θ₀ := by
      refine ⟨fun x y hxy => ?_, fun z => ?_⟩
      · exact congrArg Subtype.val (hπinj hxy)
      · obtain ⟨u, hu⟩ := hπ z
        exact ⟨u, by rw [← hu]; rfl⟩
    let θ : X ≃+ altHeart m := AddEquiv.ofBijective θ₀ hθ₀
    have hθ : ∀ (σ : alternatingGroup (Fin m)) x,
        θ (r (altLift ι σ) x) = altAct (σ : Perm (Fin m)) (θ x) := fun σ x =>
      heq σ ⟨x, hmem x⟩ ⟨_, hmem _⟩ rfl
    rcases Nat.even_or_odd n with hev | hodd
    · exact exists_heartEquiv_even hev (by omega) ι hι hmn r θ hθ
    · exfalso
      have hm : Even m := by
        obtain ⟨k, hk⟩ := hodd
        exact ⟨k, by omega⟩
      exact false_of_heartEquiv_odd hm (by omega) ι hι r θ hθ
  ·
    exfalso
    obtain ⟨f, hf0, hfM⟩ := exists_functional M₁ hM₁
    refine false_of_functional (by omega) ι hι r hirr hK0 f hf0 fun σ x => ?_
    have h := hfM _ (h₁ σ x)
    rw [map_sub, sub_eq_zero] at h
    exact h

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
