module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisTv
public import Mathlib.Algebra.Module.StablyFree.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Module CFSG.RankThree.PartOne.KCLinPlane

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem IsTv.mono {G G' : Subgroup (V ≃ₗ[K] V)} (hGG : G ≤ G') {w : V} {φ : Module.Dual K V}
    (h : IsTv G w φ) : IsTv G' w φ := by
  obtain ⟨hw, u, hu, huv⟩ := h
  exact ⟨hw, u, hGG hu, huv⟩

theorem exists_block_dual {f : Module.End K V} (hf : ∀ v, f (f v) = f v) {u x : V} (hu : f u = u)
    (hx : f x = x) (hxu : x ∉ Submodule.span K {u}) :
    ∃ l : Module.Dual K V, (∀ v, l (f v) = l v) ∧ l u = 0 ∧ l x ≠ 0 := by
  set p : Submodule K V := Submodule.span K {u} ⊔ LinearMap.ker f with hp
  have hxp : x ∉ p := by
    intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    apply hxu
    have h2 : f (c • u + z) = f x := by rw [hyz]
    rw [map_add, map_smul, hu, LinearMap.mem_ker.1 hz, add_zero, hx] at h2
    rw [← h2]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  obtain ⟨l, hl, hlp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxp inferInstance
  have hkill : ∀ z ∈ p, l z = 0 := fun z hz => by
    have : l z ∈ p.map l := ⟨z, hz, rfl⟩
    rwa [hlp, Submodule.mem_bot] at this
  refine ⟨l, fun v => ?_, hkill u (Submodule.mem_sup_left (Submodule.mem_span_singleton_self u)), hl⟩
  have h1 : v - f v ∈ p := Submodule.mem_sup_right (by
    rw [LinearMap.mem_ker, map_sub, hf, sub_self])
  have := hkill _ h1
  rw [map_sub, sub_eq_zero] at this
  exact this.symm

theorem exists_block_indep {f : Module.End K V} [FiniteDimensional K V] (hf : ∀ v, f (f v) = f v)
    (hdim : 2 ≤ finrank K (LinearMap.range f)) (u : V) :
    ∃ x, f x = x ∧ x ∉ Submodule.span K {u} := by
  by_contra hcon
  push Not at hcon
  have hle : LinearMap.range f ≤ Submodule.span K {u} := by
    rintro _ ⟨v, rfl⟩
    exact hcon _ (hf v)
  have h1 := Submodule.finrank_mono hle
  have h2 : finrank K (Submodule.span K {u}) ≤ 1 := by
    by_cases hu : u = 0
    · subst hu
      rw [Submodule.span_singleton_eq_bot.2 rfl]
      simp
    · exact (finrank_span_singleton hu).le
  omega

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
