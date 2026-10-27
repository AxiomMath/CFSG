module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Hyp89
public import CFSG.GH74.GLS.Stage2.Signalizer.L53Dickson

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.LinearGroups

theorem isPGroup_closure_one_pair_of_pow {Γ : Type*} [Group Γ] {p : ℕ} (hp : p.Prime) {y : Γ}
    (hy : y ^ p = 1) : IsPGroup p ↥(closure ({1, y} : Set Γ)) := by
  rw [Subgroup.closure_insert_one, ← Subgroup.zpowers_eq_closure]
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hy) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

section Irreducible

variable {p : ℕ} [Fact p.Prime] {J : Type} [Group J]

private theorem quad_apply {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {φ : U →ₗ[ZMod p] U} (h : (φ - 1) ^ 2 = 0) (v : U) : (φ - 1) ((φ - 1) v) = 0 := by
  have := congrArg (fun f : U →ₗ[ZMod p] U => f v) h
  simpa [sq] using this

private theorem quad_of_apply {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {φ : U →ₗ[ZMod p] U} (h : ∀ v, (φ - 1) ((φ - 1) v) = 0) : (φ - 1) ^ 2 = 0 := by
  apply LinearMap.ext
  intro v
  simpa [sq] using h v

theorem exists_irreducible_section [Finite J] (S : Set J) :
    ∀ (n : ℕ) (U : Type) [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U],
      Module.finrank (ZMod p) U = n → ∀ σ : J →* LinearMap.GeneralLinearGroup (ZMod p) U,
        ¬ IsPGroup p σ.range →
        (∀ g ∈ S, (((σ g : LinearMap.GeneralLinearGroup (ZMod p) U) : U →ₗ[ZMod p] U) - 1) ^ 2 =
          0) →
        ∃ (U' : Type) (_ : AddCommGroup U') (_ : Module (ZMod p) U')
          (_ : Module.Finite (ZMod p) U') (τ : J →* LinearMap.GeneralLinearGroup (ZMod p) U'),
          ¬ IsPGroup p τ.range ∧
          (∀ g ∈ S, (((τ g : LinearMap.GeneralLinearGroup (ZMod p) U') : U' →ₗ[ZMod p] U') - 1) ^
            2 = 0) ∧
          ∀ W : Submodule (ZMod p) U', (∀ g : J, ∀ w ∈ W,
            ((τ g : LinearMap.GeneralLinearGroup (ZMod p) U') : U' →ₗ[ZMod p] U') w ∈ W) →
            W = ⊥ ∨ W = ⊤ := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U _ _ _ hn σ hσ hq
  by_cases hirr : ∀ W : Submodule (ZMod p) U, (∀ g : J, ∀ w ∈ W,
      ((σ g : LinearMap.GeneralLinearGroup (ZMod p) U) : U →ₗ[ZMod p] U) w ∈ W) →
      W = ⊥ ∨ W = ⊤
  · exact ⟨U, inferInstance, inferInstance, inferInstance, σ, hσ, hq, hirr⟩
  · obtain ⟨W, hWinv, hW0, hWt⟩ : ∃ W : Submodule (ZMod p) U, (∀ g : J, ∀ w ∈ W,
        ((σ g : LinearMap.GeneralLinearGroup (ZMod p) U) : U →ₗ[ZMod p] U) w ∈ W) ∧
        W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra hcon
      apply hirr
      intro W hW
      by_contra h2
      push Not at h2
      exact hcon ⟨W, hW, h2.1, h2.2⟩
    let H : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) U) := σ.range
    have hW : ∀ g ∈ H, ∀ w ∈ W,
        ((g : LinearMap.GeneralLinearGroup (ZMod p) U) : U →ₗ[ZMod p] U) w ∈ W := by
      rintro _ ⟨g, rfl⟩ w hw
      exact hWinv g w hw
    have hfin : Finite ↥H := Finite.of_surjective _ σ.rangeRestrict_surjective
    have hnot : ¬ (IsPGroup p (invariantRestrict H W hW).range ∧
        IsPGroup p (invariantQuotient H W hW).range) :=
      fun ⟨h1, h2⟩ => hσ (linear_p_extension H W p hW h1 h2)
    have hlt1 : Module.finrank (ZMod p) W < n := hn ▸ Submodule.finrank_lt hWt
    have hlt2 : Module.finrank (ZMod p) (U ⧸ W) < n := by
      have h1 := Submodule.finrank_quotient_add_finrank W
      have : Nontrivial ↥W := Submodule.nontrivial_iff_ne_bot.mpr hW0
      have h2 : 0 < Module.finrank (ZMod p) W := Module.finrank_pos
      omega
    by_cases h1 : IsPGroup p (invariantRestrict H W hW).range
    · have h2 : ¬ IsPGroup p (invariantQuotient H W hW).range := fun h2 => hnot ⟨h1, h2⟩
      let τ : J →* LinearMap.GeneralLinearGroup (ZMod p) (U ⧸ W) :=
        (invariantQuotient H W hW).comp σ.rangeRestrict
      have hτr : τ.range = (invariantQuotient H W hW).range := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr σ.rangeRestrict_surjective,
          ← MonoidHom.range_eq_map]
      refine ih _ hlt2 (U ⧸ W) rfl τ (by rw [hτr]; exact h2) (fun g hg => ?_)
      apply quad_of_apply
      intro v
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective W v
      have e : ∀ x : U, ((τ g : LinearMap.GeneralLinearGroup (ZMod p) (U ⧸ W)) :
          (U ⧸ W) →ₗ[ZMod p] U ⧸ W) (Submodule.Quotient.mk x) =
          Submodule.Quotient.mk (((σ g : LinearMap.GeneralLinearGroup (ZMod p) U) :
            U →ₗ[ZMod p] U) x) := fun x => rfl
      have h3 := quad_apply (hq g hg) u
      simp only [LinearMap.sub_apply, Module.End.one_apply] at h3 ⊢
      rw [e, ← Submodule.Quotient.mk_sub, e, ← Submodule.Quotient.mk_sub, h3]
      rfl
    · let τ : J →* LinearMap.GeneralLinearGroup (ZMod p) W :=
        (invariantRestrict H W hW).comp σ.rangeRestrict
      have hτr : τ.range = (invariantRestrict H W hW).range := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr σ.rangeRestrict_surjective,
          ← MonoidHom.range_eq_map]
      refine ih _ hlt1 W rfl τ (by rw [hτr]; exact h1) (fun g hg => ?_)
      apply quad_of_apply
      intro v
      apply Subtype.ext
      have e : ∀ x : W, (((τ g : LinearMap.GeneralLinearGroup (ZMod p) W) : W →ₗ[ZMod p] W) x :
          U) = ((σ g : LinearMap.GeneralLinearGroup (ZMod p) U) : U →ₗ[ZMod p] U) x :=
        fun x => rfl
      have h3 := quad_apply (hq g hg) (v : U)
      simp only [LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_sub, e] at h3 ⊢
      exact h3

end Irreducible

section Pair


variable {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Module.Finite (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ}
  {a : Γ}

theorem sl2Quot_of_nonPGroup_pair (hf : Hyp89 p ρ K a) {k : Γ}
    (hJ : ¬ IsPGroup p ↥(closure ({a, k * a * k⁻¹} : Set Γ))) :
    L53.Sl2Quot p ↥(closure ({a, k * a * k⁻¹} : Set Γ)) ⊥ := by
  classical
  have : Fact p.Prime := ⟨hf.prime⟩
  set b : Γ := k * a * k⁻¹ with hb
  set J : Subgroup Γ := closure ({a, b} : Set Γ) with hJdef
  have haJ : a ∈ J := subset_closure (Set.mem_insert _ _)
  have hbJ : b ∈ J := subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  let a' : ↥J := ⟨a, haJ⟩
  let b' : ↥J := ⟨b, hbJ⟩
  have hgen : closure ({a', b'} : Set ↥J) = ⊤ := by
    have h1 : Subtype.val ⁻¹' ({a, b} : Set Γ) = ({a', b'} : Set ↥J) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (h | h)
        · left; exact Subtype.ext h
        · right; exact Subtype.ext h
      · rintro (h | h)
        · left; rw [h]
        · right; rw [h]
    rw [← h1]
    exact Subgroup.closure_closure_coe_preimage
  let σ : ↥J →* LinearMap.GeneralLinearGroup (ZMod p) V := ρ.comp J.subtype
  have hσinj : Function.Injective σ := hf.faithful.comp J.subtype_injective
  have hσp : ¬ IsPGroup p σ.range := by
    intro h
    exact hJ (h.of_injective σ.rangeRestrict (fun x y hxy => hσinj (congrArg Subtype.val hxy)))
  have hqa : (((ρ a : (V →ₗ[ZMod p] V)ˣ) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 := hf.quad
  have hqb : (((ρ b : (V →ₗ[ZMod p] V)ˣ) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 := by
    have := (quadratic_linear_p_elements p (ρ a) hqa).2 (ρ k)⁻¹
    simpa [hb, map_mul, map_inv, mul_assoc] using this
  have hS : ∀ g ∈ ({a', b'} : Set ↥J),
      (((σ g : LinearMap.GeneralLinearGroup (ZMod p) V) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 := by
    intro g hg
    rcases hg with rfl | rfl
    · exact hqa
    · exact hqb
  obtain ⟨U, _, _, _, τ, hτp, hτq, hτirr⟩ := exists_irreducible_section ({a', b'} : Set ↥J) _ V
    rfl σ hσp hS
  have hrange : τ.range = closure {τ a', τ b'} := by
    rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, Set.image_pair]
  have hτa : ((τ a' : LinearMap.GeneralLinearGroup (ZMod p) U) : U →ₗ[ZMod p] U) ≠ 1 := by
    intro h1
    apply hτp
    have hτa1 : τ a' = 1 := Units.ext h1
    rw [hrange, hτa1]
    have hp1 := (quadratic_linear_p_elements p (τ b') (hτq b' (by simp))).1
    exact isPGroup_closure_one_pair_of_pow hf.prime hp1
  have hfinU : Finite U := Module.finite_of_finite (ZMod p)
  let τ' : ↥J →* Module.End (ZMod p) U :=
    (Units.coeHom (Module.End (ZMod p) U)).comp τ
  have hSuz : L53.SuzukiData (τ' a' - 1) (τ' b' - 1) := by
    refine ⟨?_, ?_, sub_ne_zero.mpr hτa, ?_⟩
    · rw [← sq]
      exact hτq a' (by simp)
    · rw [← sq]
      exact hτq b' (by simp)
    · intro T hTa hTb
      apply hτirr T
      let M : Submonoid ↥J :=
        { carrier := {g | ∀ w ∈ T, ((τ g : LinearMap.GeneralLinearGroup (ZMod p) U) :
            U →ₗ[ZMod p] U) w ∈ T}
          one_mem' := fun w hw => by simpa using hw
          mul_mem' := fun {g h} hg hh w hw => by
            simpa using hg _ (hh w hw) }
      have hgenM : ∀ g ∈ ({a', b'} : Set ↥J), g ∈ M := by
        intro g hg w hw
        rcases hg with rfl | rfl
        · have := T.add_mem hw (hTa w hw)
          simpa [τ'] using this
        · have := T.add_mem hw (hTb w hw)
          simpa [τ'] using this
      have hall : ∀ g : ↥J, g ∈ M := by
        intro g
        have hg : g ∈ closure ({a', b'} : Set ↥J) := by rw [hgen]; exact Subgroup.mem_top g
        refine Subgroup.closure_induction (p := fun g _ => g ∈ M) hgenM M.one_mem
          (fun x y _ _ hx hy => M.mul_mem hx hy) (fun x _ hx => ?_) hg
        have h1 : x⁻¹ = x ^ (orderOf x - 1) := by
          have := pow_orderOf_eq_one x
          have hpos := orderOf_pos x
          calc x⁻¹ = x⁻¹ * x ^ orderOf x := by rw [this, mul_one]
            _ = x ^ (orderOf x - 1) := by
              conv_lhs => rw [show orderOf x = (orderOf x - 1) + 1 by omega, pow_succ']
              rw [← mul_assoc, inv_mul_cancel, one_mul]
        rw [h1]
        exact M.pow_mem hx _
      exact fun g w hw => hall g w hw
  exact (L53.sl2_of_irreducible (p := p) (W := U) hf.odd a' b' hgen τ' hSuz).mono bot_le

end Pair

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
