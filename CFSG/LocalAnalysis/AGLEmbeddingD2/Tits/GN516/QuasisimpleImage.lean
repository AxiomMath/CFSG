module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.NonabelianSylowHom
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

theorem isPGroup_range_of_quasisimple_quotient
    {E D : Type*} [Group E] [Finite E] [Group D] (N : Subgroup E) [N.Normal]
    (hN : IsPGroup 2 N)
    (hperf : commutator (E ⧸ N) = ⊤)
    (hsimple : IsSimpleGroup ((E ⧸ N) ⧸ Subgroup.center (E ⧸ N)))
    (hodd : ∀ z ∈ Subgroup.center (E ⧸ N), Odd (orderOf z))
    (P : Subgroup (E ⧸ N)) (hP : IsPGroup 2 P) (hnon : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a)
    (φ : E →* D) (hφ : Function.Surjective φ)
    (hab : ∀ Q : Subgroup D, IsPGroup 2 Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    IsPGroup 2 D := by
  set M : Subgroup D := N.map φ with hM
  have : M.Normal := Subgroup.Normal.map inferInstance φ hφ
  have hM2 : IsPGroup 2 M := hN.map φ
  have hNM : N ≤ M.comap φ := fun x hx => ⟨x, hx, rfl⟩
  let ψ : E ⧸ N →* D ⧸ M := QuotientGroup.map N M φ hNM
  have hab' : ∀ Q : Subgroup (D ⧸ M), IsPGroup 2 Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    intro Q hQ x hx y hy
    have hQc : IsPGroup 2 (Q.comap (QuotientGroup.mk' M)) := by
      refine hQ.comap_of_ker_isPGroup (QuotientGroup.mk' M) ?_
      rwa [QuotientGroup.ker_mk']
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    have := hab _ hQc x' hx y' hy
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  have h1 := hom_eq_one_of_abelian_two_subgroups hperf hsimple hodd P hP hnon ψ hab'
  have hDM : ∀ d : D, d ∈ M := by
    intro d
    obtain ⟨e, rfl⟩ := hφ d
    have := h1 (QuotientGroup.mk e)
    have h2 : ψ (QuotientGroup.mk e) = QuotientGroup.mk (φ e) := rfl
    rw [h2] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  intro d
  obtain ⟨m, hm⟩ := hM2 ⟨d, hDM d⟩
  exact ⟨m, congrArg Subtype.val hm⟩

end CFSG.AGLEmbeddingD2.Tits.GN516
