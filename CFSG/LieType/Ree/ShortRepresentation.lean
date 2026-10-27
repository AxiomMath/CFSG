module

public import CFSG.LieType.Ree.Faithful

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K]

variable (t K) in
@[expose] def shortRestrictHom
    (hp : (t.prime : K) = 0) :
    adjointGroup t.tag K →* Module.End K (t.shortModule K) where
  toFun g := (g.1 : Module.End K (RootModule t.tag K)).restrict
    fun _ hv => mem_shortModule_of_mem hp g.2 hv
  map_one' := LinearMap.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearMap.ext fun _ => Subtype.ext rfl

theorem coe_shortRestrictHom_apply
    (hp : (t.prime : K) = 0) (g : adjointGroup t.tag K)
    (v : t.shortModule K) :
    (shortRestrictHom t K hp g v : RootModule t.tag K) =
      (g.1 : Module.End K (RootModule t.tag K)) v :=
  rfl

variable (t K) in
@[expose] def shortRep
    (hp : (t.prime : K) = 0) :
    adjointGroup t.tag K →* (t.shortModule K ≃ₗ[K] t.shortModule K) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (t.shortModule K)).toMonoidHom.comp
    (shortRestrictHom t K hp).toHomUnits

theorem coe_shortRep_apply
    (hp : (t.prime : K) = 0) (g : adjointGroup t.tag K)
    (v : t.shortModule K) :
    (shortRep t K hp g v : RootModule t.tag K) = (g.1 : Module.End K (RootModule t.tag K)) v :=
  rfl

theorem shortRep_injective
    [Finite K] [CharP K t.prime] :
    Function.Injective (shortRep t K (CharP.cast_eq_zero K t.prime)) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => Subtype.ext ?_
  refine exceptional_short_faithful t K g.2 fun v hv => ?_
  have h := congrArg (fun e : t.shortModule K ≃ₗ[K] t.shortModule K =>
    (e ⟨v, hv⟩ : RootModule t.tag K)) hg
  exact h

variable (t K) in
theorem finrank_shortModule
    : Module.finrank K (t.shortModule K) = t.shortDim := by
  rw [Module.finrank_eq_nat_card_basis (t.shortBasis K), card_shortLabels]

end ReeTag

open ReeTag

theorem finite_short_module_faithful
    (t : ReeTag) (f : ℕ) (_hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = t.prime ^ f) :
    ∃ ρ : adjointGroup t.tag K →* (t.shortModule K ≃ₗ[K] t.shortModule K),
      Function.Injective ρ ∧
      (∀ (g : adjointGroup t.tag K) (v : t.shortModule K),
        (ρ g v : RootModule t.tag K) = (g.1 : Module.End K (RootModule t.tag K)) v) ∧
      (t = .G2 → Module.finrank K (t.shortModule K) = 7) ∧
      (t = .F4 → Module.finrank K (t.shortModule K) = 26) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact t.prime.Prime := ⟨by cases t <;> decide⟩
  have : CharP K t.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  refine ⟨shortRep t K (CharP.cast_eq_zero K t.prime), shortRep_injective,
    coe_shortRep_apply _, fun ht => ?_, fun ht => ?_⟩
  · subst ht
    exact finrank_shortModule _ K
  · subst ht
    exact finrank_shortModule _ K

end CFSG.LieType.Ree
