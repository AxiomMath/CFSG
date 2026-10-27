module


public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

public section

open scoped LinearAlgebra.Projectivization

namespace CFSG.LinearAlgebra.CoprimeActions.FiniteFieldHyperplaneCount

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

theorem hyperplane_count [Finite F] [FiniteDimensional F W] :
    Nat.card {H : Submodule F W // IsCoatom H} =
      ∑ i ∈ Finset.range (Module.finrank F W), (Nat.card F) ^ i := by
  let kerMap (x : ℙ F (Module.Dual F W)) : {H : Submodule F W // IsCoatom H} :=
    Projectivization.lift (K := F)
      (fun f : {f : Module.Dual F W // f ≠ 0} =>
        (⟨LinearMap.ker f.1, by
          have hs : Function.Surjective f.1 := LinearMap.surjective_of_ne_zero f.2
          exact LinearMap.isCoatom_ker_of_surjective hs⟩ : {H : Submodule F W // IsCoatom H}))
      (by
        rintro ⟨a, ha⟩ ⟨b, hb⟩ t h
        have ht : t ≠ 0 := by rintro rfl; simp at h; exact ha h
        apply Subtype.ext
        simp only at h ⊢
        rw [h]
        exact LinearMap.ker_smul b t ht) x
  have kerMap_mk (f : Module.Dual F W) (hf : f ≠ 0) :
      (kerMap (Projectivization.mk F f hf)).1 = LinearMap.ker f := rfl
  have kerMap_bijective [FiniteDimensional F W] :
      Function.Bijective kerMap := by
    constructor
    · intro x y
      induction x using Projectivization.ind with | _ f hf =>
      induction y using Projectivization.ind with | _ g hg =>
      intro h
      have hk : LinearMap.ker f = LinearMap.ker g := congrArg Subtype.val h
      rw [Projectivization.mk_eq_mk_iff']
      obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
        by_contra hcon; push Not at hcon; exact hf (LinearMap.ext hcon)
      have hgx : g x ≠ 0 := by
        intro h0; apply hx; have : x ∈ LinearMap.ker g := h0
        rw [← hk] at this; exact this
      have hfx : f x ≠ 0 := hx
      have hne : (g x)⁻¹ * f x ≠ 0 := mul_ne_zero (inv_ne_zero hgx) hfx
      refine ⟨(g x)⁻¹ * f x, ?_⟩
      have happ : (((g x)⁻¹ * f x) • g) x = f x := by
        simp only [LinearMap.smul_apply, smul_eq_mul]; field_simp
      refine Module.Dual.eq_of_ker_eq_of_apply_eq x ?_ happ ?_
      · rw [LinearMap.ker_smul _ _ hne, hk]
      · rw [happ]; exact hfx
    · rintro ⟨H, hH⟩
      obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_lt_top H hH.lt_top
      have hs : Function.Surjective f := LinearMap.surjective_of_ne_zero hf
      have hc := LinearMap.isCoatom_ker_of_surjective hs
      refine ⟨Projectivization.mk F f hf, Subtype.ext ?_⟩
      rw [kerMap_mk]
      exact (hH.le_iff_eq hc.1).1 hle
  rw [← Nat.card_congr (Equiv.ofBijective _ kerMap_bijective)]
  exact Projectivization.card_of_finrank F (Module.Dual F W)
    (Subspace.dual_finrank_eq (K := F) (V := W))

end CFSG.LinearAlgebra.CoprimeActions.FiniteFieldHyperplaneCount
