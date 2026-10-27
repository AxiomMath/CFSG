module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFactsA6
import CFSG.CGT.Foote82.T66.CaseIPerm

public section

namespace CFSG.CGT.Foote82

namespace CaseIAut

open Equiv Equiv.Perm

variable {Γ : Type*} [Group Γ] {m : ℕ}

abbrev conjA (σ : Perm (Fin m)) (a : alternatingGroup (Fin m)) : alternatingGroup (Fin m) :=
  MulAut.conjNormal σ a

theorem coe_conjA (σ : Perm (Fin m)) (a : alternatingGroup (Fin m)) :
    ((conjA σ a : alternatingGroup (Fin m)) : Perm (Fin m)) = σ * a * σ⁻¹ := rfl

theorem eq_one_of_commute_alternatingGroup (hm : 5 ≤ m) {τ : Perm (Fin m)}
    (h : ∀ a ∈ alternatingGroup (Fin m), τ * a = a * τ) : τ = 1 := by
  have hF : 5 ≤ Nat.card (Set.univ : Set (Fin m)) := by
    rw [Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hm
  refine Equiv.Perm.ext fun x => ?_
  refine CaseIPerm.fixes_of_commute_altOn hF (fun k hk => h k ?_) (Set.mem_univ x)
  exact (CaseIPerm.mem_altOn_iff.1 hk).1

theorem perm_unique (hm : 5 ≤ m) {σ σ' : Perm (Fin m)}
    (h : ∀ a : alternatingGroup (Fin m), conjA σ a = conjA σ' a) : σ = σ' := by
  have h1 : σ'⁻¹ * σ = 1 := by
    refine eq_one_of_commute_alternatingGroup hm fun a ha => ?_
    have := congrArg Subtype.val (h ⟨a, ha⟩)
    rw [coe_conjA, coe_conjA] at this
    calc σ'⁻¹ * σ * a = σ'⁻¹ * (σ * a * σ⁻¹) * σ := by group
      _ = σ'⁻¹ * (σ' * a * σ'⁻¹) * σ := by rw [this]
      _ = a * (σ'⁻¹ * σ) := by group
  rw [mul_eq_one_iff_eq_inv] at h1
  exact (inv_inj.1 h1).symm

noncomputable def inducedAut (j : alternatingGroup (Fin m) →* Γ) (hj : Function.Injective j)
    (x : Γ) (hx : x ∈ Subgroup.normalizer (j.range : Set Γ)) : MulAut (alternatingGroup (Fin m)) :=
  let e : alternatingGroup (Fin m) ≃* j.range := MonoidHom.ofInjective hj
  let c : j.range ≃* j.range :=
    { toFun := fun y => ⟨x * y * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx y).1 y.2⟩
      invFun := fun y => ⟨x⁻¹ * y * x, by
        have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hx) y).1 y.2
        simpa only [inv_inv] using h⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun y y' => Subtype.ext (by simp [mul_assoc]) }
  (e.trans c).trans e.symm

theorem j_inducedAut (j : alternatingGroup (Fin m) →* Γ) (hj : Function.Injective j)
    (x : Γ) (hx : x ∈ Subgroup.normalizer (j.range : Set Γ)) (a : alternatingGroup (Fin m)) :
    j (inducedAut j hj x hx a) = x * j a * x⁻¹ := by
  simp only [inducedAut, MulEquiv.trans_apply]
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

theorem exists_perm_conj_of_ge_seven (hm : m = 5 ∨ 7 ≤ m) (j : alternatingGroup (Fin m) →* Γ)
    (hj : Function.Injective j) {x : Γ} (hx : x ∈ Subgroup.normalizer (j.range : Set Γ)) :
    ∃ σ : Perm (Fin m), ∀ a, x * j a * x⁻¹ = j (conjA σ a) := by
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation hm
    (inducedAut j hj x hx)
  refine ⟨σ, fun a => ?_⟩
  rw [← j_inducedAut j hj x hx a]
  congr 1
  exact Subtype.ext (hσ a)

theorem exists_perm_conj_of_six (j : alternatingGroup (Fin 6) →* Γ) (hj : Function.Injective j)
    {x : Γ} (hx : x ∈ Subgroup.normalizer (j.range : Set Γ))
    (h3 : ∀ b : alternatingGroup (Fin 6),
      x * j CFSG.ComponentClassification.RankTwoAlt.a6c012 * x⁻¹ = j b →
        (b : Perm (Fin 6)).IsThreeCycle) :
    ∃ σ : Perm (Fin 6), ∀ a, x * j a * x⁻¹ = j (conjA σ a) := by
  obtain ⟨σ, hσ⟩ := CFSG.ComponentClassification.RankTwoAlt.exists_perm_of_isThreeCycle
    (inducedAut j hj x hx) (h3 _ (j_inducedAut j hj x hx _).symm)
  refine ⟨σ, fun a => ?_⟩
  rw [← j_inducedAut j hj x hx a]
  congr 1
  exact Subtype.ext (hσ a)

theorem exists_theta (hm : 5 ≤ m) (j : alternatingGroup (Fin m) →* Γ) (hj : Function.Injective j)
    (X : Subgroup Γ)
    (hperm : ∀ x ∈ X, ∃ σ : Perm (Fin m), ∀ a, x * j a * x⁻¹ = j (conjA σ a)) :
    ∃ θ : X →* Perm (Fin m), ∀ (x : X) (a : alternatingGroup (Fin m)),
      (x : Γ) * j a * (x : Γ)⁻¹ = j (conjA (θ x) a) := by
  choose f hf using hperm
  have huniq : ∀ (x : Γ) (σ σ' : Perm (Fin m)), (∀ a, x * j a * x⁻¹ = j (conjA σ a)) →
      (∀ a, x * j a * x⁻¹ = j (conjA σ' a)) → σ = σ' := fun x σ σ' h h' =>
    perm_unique hm fun a => hj ((h a).symm.trans (h' a))
  refine ⟨MonoidHom.mk' (fun x => f x x.2) fun x y => ?_, fun x a => hf x x.2 a⟩
  refine huniq ((x : Γ) * y) _ _ (hf _ (X.mul_mem x.2 y.2)) fun a => ?_
  have e1 : (x : Γ) * (y : Γ) * j a * ((x : Γ) * (y : Γ))⁻¹ =
      (x : Γ) * ((y : Γ) * j a * (y : Γ)⁻¹) * (x : Γ)⁻¹ := by group
  rw [e1, hf y y.2, hf x x.2]
  congr 1

theorem theta_eq (hm : 5 ≤ m) (j : alternatingGroup (Fin m) →* Γ) (hj : Function.Injective j)
    {X : Subgroup Γ} {θ : X →* Perm (Fin m)}
    (hθ : ∀ (x : X) (a : alternatingGroup (Fin m)), (x : Γ) * j a * (x : Γ)⁻¹ = j (conjA (θ x) a))
    (x : X) {σ : Perm (Fin m)} (hσ : ∀ a, (x : Γ) * j a * (x : Γ)⁻¹ = j (conjA σ a)) :
    θ x = σ :=
  perm_unique hm fun a => hj ((hθ x a).symm.trans (hσ a))

theorem theta_eq_one_iff (hm : 5 ≤ m) (j : alternatingGroup (Fin m) →* Γ)
    (hj : Function.Injective j) {X : Subgroup Γ} {θ : X →* Perm (Fin m)}
    (hθ : ∀ (x : X) (a : alternatingGroup (Fin m)), (x : Γ) * j a * (x : Γ)⁻¹ = j (conjA (θ x) a))
    (x : X) : θ x = 1 ↔ ∀ a, (x : Γ) * j a = j a * x := by
  constructor
  · intro h a
    have := hθ x a
    rw [h] at this
    have h1 : conjA (1 : Perm (Fin m)) a = a := Subtype.ext (by simp [coe_conjA])
    rw [h1] at this
    calc (x : Γ) * j a = (x : Γ) * j a * (x : Γ)⁻¹ * x := by group
      _ = j a * x := by rw [this]
  · intro h
    refine theta_eq hm j hj hθ x fun a => ?_
    have h1 : conjA (1 : Perm (Fin m)) a = a := Subtype.ext (by simp [coe_conjA])
    rw [h1, h a]
    group

end CaseIAut

end CFSG.CGT.Foote82
