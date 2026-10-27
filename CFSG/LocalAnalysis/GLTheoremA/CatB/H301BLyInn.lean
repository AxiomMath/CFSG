module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLyRes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.ComponentClassification.OuterAutomorphisms

theorem mem_inner_of_mem_commutator {S : Type*} [Group S] (h : Nat.card (Outer S) ∣ 2)
    {R : Subgroup (MulAut S)} {c : R} (hc : c ∈ commutator R) : (c : MulAut S) ∈ inner S := by
  have hcomm : ∀ a b : Outer S, a * b = b * a := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
    · haveI : Subsingleton (Outer S) := (Nat.card_eq_one_iff_unique.1 h1).1
      exact fun a b => Subsingleton.elim _ _
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : IsCyclic (Outer S) := isCyclic_of_prime_card h2
      exact fun a b => mul_comm' a b
  let f : R →* Outer S := (QuotientGroup.mk' (inner S)).comp R.subtype
  have hker : commutator R ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
  exact (QuotientGroup.eq_one_iff (N := inner S) (c : MulAut S)).1 (hker hc)

private theorem exists_conj_hom {A H : Type*} [Group A] [Group H] (f : A →* H)
    (hf : Function.Injective f) (a : H) :
    ∃ θ : A →* H, Function.Injective θ ∧ ∀ g, θ g = a * f g * a⁻¹ :=
  ⟨(MulAut.conj a).toMonoidHom.comp f, (MulAut.conj a).injective.comp hf, fun _ => rfl⟩

section Congr


noncomputable def autCongrJ {S : Type*} [Group S] (e : S ≃* J) : MulAut S ≃* MulAut J :=
  MulAut.congr (G := S) (H := J) (by exact e)

theorem autCongrJ_conj {S : Type*} [Group S] (e : S ≃* J) (s : S) :
    autCongrJ e (MulAut.conj s) = MulAut.conj (e s) := by
  apply MulEquiv.ext
  intro u
  change e (s * e.symm u * s⁻¹) = e s * u * (e s)⁻¹
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]

end Congr

section Fusion


theorem exists_hom_central {S : Type*} [Group S] (e₀ : S ≃* J) (hOut : Nat.card (Outer S) ∣ 2)
    {R : Subgroup (MulAut S)} {c : R} (hc : c ∈ commutator R)
    (hord : orderOf (c : MulAut S) = 2) :
    ∃ θ : MulAut S →* MulAut J, Function.Injective θ ∧ θ (c : MulAut S) = MulAut.conj lyz := by
  obtain ⟨s, hs⟩ := mem_inner_of_mem_commutator hOut hc
  have h3 : orderOf (MulAut.conj (e₀ s)) = 2 := by
    rw [← autCongrJ_conj e₀ s, hs, MulEquiv.orderOf_eq, hord]
  have h2 : orderOf (e₀ s) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · refine conj_injective_lyJ ?_
      rw [map_pow, map_one, ← h3]
      exact pow_orderOf_eq_one _
    · intro h
      rw [h, map_one, orderOf_one] at h3
      exact absurd h3 (by norm_num)
  obtain ⟨x, hx⟩ := involution_centralizer_fusion_generator.2 (e₀ s) h2
  have key : x⁻¹ * e₀ s * x⁻¹⁻¹ = lyz := by
    rw [← hx]
    group
  obtain ⟨a, ha⟩ : ∃ a : MulAut J, a = MulAut.conj x⁻¹ := ⟨_, rfl⟩
  obtain ⟨θ, hθ, hθg⟩ := exists_conj_hom (autCongrJ e₀).toMonoidHom (autCongrJ e₀).injective a
  refine ⟨θ, hθ, ?_⟩
  rw [hθg]
  change a * autCongrJ e₀ (c : MulAut S) * a⁻¹ = MulAut.conj lyz
  rw [← hs, autCongrJ_conj, ha, ← map_inv, ← map_mul, ← map_mul, key]

end Fusion

end CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

end
