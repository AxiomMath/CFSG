module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Ring.Int.Defs


public section

namespace CFSG.GroupTheory.CoprimeActionSupport.CyclicBlockStabilizerAbelian

theorem abelian {A : Type*} [Group A] (H : Subgroup (MulAut A)) {I : Type*}
    (E : I → Subgroup A) (hcyc : ∀ i, IsCyclic (E i))
    (hgen : Subgroup.closure {x : A | ∃ i, x ∈ E i} = ⊤)
    (hstab : ∀ φ ∈ H, ∀ i, (E i).map φ.toMonoidHom = E i) :
    IsMulCommutative H := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hpt : ∀ i, ∀ x ∈ E i, a.1 (b.1 x) = b.1 (a.1 x) := by
    intro i
    obtain ⟨g, hg⟩ := hcyc i
    have hmem : ∀ φ ∈ H, ∀ y : E i, φ (y : A) ∈ E i := by
      intro φ hφ y
      have h := Subgroup.mem_map_of_mem (MulEquiv.toMonoidHom φ) y.2
      rwa [hstab φ hφ i] at h
    have hpow : ∀ φ ∈ H, ∃ k : ℤ, (g : A) ^ k = φ (g : A) := by
      intro φ hφ
      obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).1 (hg ⟨φ (g : A), hmem φ hφ g⟩)
      refine ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨m, hm⟩ := hpow b b.2
    obtain ⟨k, hk⟩ := hpow a a.2
    have h1 : a.1 (b.1 (g : A)) = b.1 (a.1 (g : A)) := by
      rw [← hm, ← hk, map_zpow, map_zpow, ← hk, ← hm, ← zpow_mul, ← zpow_mul, mul_comm]
    intro x hx
    obtain ⟨n, hn⟩ := (Subgroup.mem_zpowers_iff).1 (hg ⟨x, hx⟩)
    have hn' : (g : A) ^ n = x := by
      have := congrArg Subtype.val hn
      simpa using this
    rw [← hn', map_zpow, map_zpow, map_zpow, map_zpow, h1]
  have key : (a.1 : MulAut A).toMonoidHom.comp (b.1 : MulAut A).toMonoidHom =
      (b.1 : MulAut A).toMonoidHom.comp (a.1 : MulAut A).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense hgen ?_
    intro x hx
    obtain ⟨i, hi⟩ := hx
    exact hpt i x hi
  apply MulEquiv.ext
  intro x
  exact DFunLike.congr_fun key x

end CFSG.GroupTheory.CoprimeActionSupport.CyclicBlockStabilizerAbelian
