module

public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.LieType.SpecialLinear

open scoped Matrix

@[expose] def IsIrreducibleAdd {K V : Type*} [AddCommGroup V] (act : K → V → V) : Prop :=
  ∀ W : AddSubgroup V, (∀ (g : K) {v : V}, v ∈ W → act g v ∈ W) → W = ⊥ ∨ W = ⊤

theorem exists_addHom_of_extend {K V I F k : Type*} [Fintype I] [Field F] [Field k]
    [Algebra F k] [Group K] [AddCommGroup V] [DistribMulAction K V] (T : K → Matrix I I F)
    (Φ : V →+ (I → k)) (hΦ : Φ ≠ 0)
    (hΦeq : ∀ g v, Φ (g • v) = (T g).map (algebraMap F k) *ᵥ Φ v) :
    ∃ Ψ : V →+ (I → F), Ψ ≠ 0 ∧ ∀ g v, Ψ (g • v) = T g *ᵥ Ψ v := by
  classical
  have hcoe : (⇑Φ : V → I → k) ≠ ⇑(0 : V →+ (I → k)) :=
    fun h ↦ hΦ (DFunLike.coe_injective h)
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hcoe
  have hv' : Φ v ≠ 0 := by simpa using hv
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv'
  have hi' : Φ v i ≠ 0 := by simpa using hi
  have hsep : ∃ lam : Module.Dual F k, lam (Φ v i) ≠ 0 := by
    by_contra h
    refine hi' ((Module.forall_dual_apply_eq_zero_iff F (Φ v i)).mp ?_)
    intro lam
    by_contra hl
    exact h ⟨lam, hl⟩
  obtain ⟨lam, hlam⟩ := hsep
  let Ψ : V →+ (I → F) := {
    toFun := fun x j ↦ lam (Φ x j)
    map_zero' := by
      ext j
      simp
    map_add' := fun x y ↦ by
      ext j
      simp [map_add] }
  refine ⟨Ψ, ?_, ?_⟩
  · intro h
    have h0 := congrFun (congrArg DFunLike.coe h) v
    have h1 := congrFun h0 i
    apply hlam
    simpa [Ψ] using h1
  · intro g x
    ext j
    calc
      Ψ (g • x) j = lam (Φ (g • x) j) := rfl
      _ = lam (((T g).map (algebraMap F k) *ᵥ Φ x) j) := by rw [hΦeq g x]
      _ = lam (∑ l : I, algebraMap F k (T g j l) * Φ x l) := by
        simp only [Matrix.mulVec_apply_eq_sum, Matrix.map_apply]
      _ = ∑ l : I, T g j l * lam (Φ x l) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [← Algebra.smul_def, map_smul, smul_eq_mul]
      _ = (T g *ᵥ Ψ x) j := by
        rw [Matrix.mulVec_apply_eq_sum]
        rfl

theorem bijective_of_ne_zero_of_irreducible {K V I F : Type*} [Fintype I] [Field F] [Group K]
    [AddCommGroup V] [DistribMulAction K V] (T : K → Matrix I I F)
    (hV : IsIrreducibleAdd (fun (g : K) (v : V) ↦ g • v))
    (hW : IsIrreducibleAdd (fun (g : K) (v : I → F) ↦ T g *ᵥ v))
    (Φ : V →+ (I → F)) (hΦ : Φ ≠ 0)
    (hΦeq : ∀ g v, Φ (g • v) = T g *ᵥ Φ v) : Function.Bijective Φ := by
  have hker : Φ.ker = ⊥ := by
    rcases hV Φ.ker (fun g v hv ↦ by
      rw [AddMonoidHom.mem_ker] at hv ⊢
      rw [hΦeq g v, hv, Matrix.mulVec_zero]) with h | h
    · exact h
    · exfalso
      exact hΦ ((AddMonoidHom.ker_eq_top_iff).mp h)
  have hrange : Φ.range = ⊤ := by
    rcases hW Φ.range (fun g v hy ↦ by
      obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hy
      exact AddMonoidHom.mem_range.mpr ⟨g • x, hΦeq g x⟩) with h | h
    · exfalso
      apply hΦ
      ext x i
      have hx : Φ x ∈ (⊥ : AddSubgroup (I → F)) := by
        rw [← h]
        exact AddMonoidHom.mem_range.mpr ⟨x, rfl⟩
      have hx' : Φ x = 0 := by simpa using hx
      simpa using congrFun hx' i
    · exact h
  exact ⟨(AddMonoidHom.ker_eq_bot_iff Φ).mp hker,
    (AddMonoidHom.range_eq_top).mp hrange⟩

end CFSG.LieType.SpecialLinear
