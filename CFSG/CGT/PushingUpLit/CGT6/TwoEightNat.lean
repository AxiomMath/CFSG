module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6

theorem natSection_equiv {V : Type} [CommGroup V] {E : Subgroup (MulAut V)} {P : Subgroup V}
    {S M : Type} [Group S] [Group M] {act : S → M → M}
    (hnat : IsNatSectionBy act E P ⊥) :
    (∀ e ∈ E, ∀ p ∈ P, e p ∈ P) ∧ ∃ (θ : ↥E ≃* S) (β : ↥P ≃* M),
      ∀ (e : ↥E) (p : ↥P) (hp : (e : MulAut V) p ∈ P), β ⟨(e : MulAut V) p, hp⟩ = act (θ e) (β p) := by
  obtain ⟨hPE, θ, β, hβs, hβk, hβact⟩ := hnat
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  exact ⟨hPE, θ, MulEquiv.ofBijective β ⟨hβinj, hβs⟩, hβact⟩

theorem transfer_normalizer {V : Type} [CommGroup V] {E A : Subgroup (MulAut V)} {S : Type}
    [Group S] (θ : ↥E ≃* S) (S₁ : Subgroup S)
    (h : A ≤ Subgroup.normalizer
      (((S₁.map θ.symm.toMonoidHom).map E.subtype : Subgroup (MulAut V)) : Set (MulAut V))) :
    ∀ a ∈ A, ∀ e : ↥E, θ e ∈ S₁ →
      ∃ e' : ↥E, θ e' ∈ S₁ ∧ (e' : MulAut V) = a * e * a⁻¹ := by
  intro a ha e he
  have h1 : (e : MulAut V) ∈ ((S₁.map θ.symm.toMonoidHom).map E.subtype : Subgroup (MulAut V)) :=
    ⟨θ.symm (θ e), ⟨θ e, he, rfl⟩, by simp⟩
  have h2 := (Subgroup.mem_normalizer_iff.mp (h ha) (e : MulAut V)).mp h1
  obtain ⟨y, ⟨s, hs, rfl⟩, hy⟩ := h2
  refine ⟨θ.symm s, ?_, hy⟩
  simpa using hs

theorem isSubnormal_normalizer {V : Type} [CommGroup V] (E : Subgroup (MulAut V)) :
    CFSG.Open.IsSubnormal E (Subgroup.normalizer (E : Set (MulAut V))) :=
  CFSG.Open.IsSubnormal.step Subgroup.le_normalizer Subgroup.normal_in_normalizer
    (CFSG.Open.IsSubnormal.refl _)

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
