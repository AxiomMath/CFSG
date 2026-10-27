module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3ExtFixed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3ExtClassify

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace Matrix

universe u

theorem GL32_isPerfect : Group.IsPerfect GL32 := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  exact Group.IsPerfect.ofSurjective (f := (slEquivGL 3).toMonoidHom) (slEquivGL 3).surjective

theorem natCard_fixedSub_of_modIso {G : Type*} [Group G] {E E' : Type*} [AddCommGroup E]
    [Module (ZMod 2) E] [AddCommGroup E'] [Module (ZMod 2) E'] {ρ' : G →* (E' ≃ₗ[ZMod 2] E')}
    {ρ : G →* (E ≃ₗ[ZMod 2] E)} (h : ModIso ρ' ρ) (A : Subgroup G) :
    Nat.card (fixedSub ρ A) = Nat.card (fixedSub ρ' A) := by
  obtain ⟨φ, hφ⟩ := h
  refine Nat.card_congr
    { toFun := fun y => ⟨φ.symm y.1, fun a ha => ?_⟩
      invFun := fun x => ⟨φ x.1, fun a ha => ?_⟩
      left_inv := fun y => Subtype.ext (φ.apply_symm_apply y.1)
      right_inv := fun x => Subtype.ext (φ.symm_apply_apply x.1) }
  · apply φ.injective
    have h1 : φ (ρ' a (φ.symm y.1)) = ρ a (φ (φ.symm y.1)) := hφ a _
    rw [h1, φ.apply_symm_apply]
    exact y.2 a ha
  · have h1 : φ (ρ' a x.1) = ρ a (φ x.1) := hφ a _
    rw [← h1, x.2 a ha]

theorem mul_lt_of_fixed (a cE cD cQ d q : ℕ) (h1 : cE ≤ cD * cQ) (h2 : a * cD < d)
    (h3 : cQ ≤ q) (hQ : 0 < cQ) : a * cE < d * q := by
  calc a * cE ≤ a * (cD * cQ) := Nat.mul_le_mul_left a h1
    _ = (a * cD) * cQ := by ring
    _ < d * cQ := Nat.mul_lt_mul_of_pos_right h2 hQ
    _ ≤ d * q := Nat.mul_le_mul_left d h3

theorem mul_lt_of_fixed' (a cE cD cQ d q : ℕ) (h1 : cE ≤ cD * cQ) (h2 : a * cQ < q)
    (h3 : cD ≤ d) (hD : 0 < cD) : a * cE < d * q := by
  calc a * cE ≤ a * (cD * cQ) := Nat.mul_le_mul_left a h1
    _ = cD * (a * cQ) := by ring
    _ < cD * q := Nat.mul_lt_mul_of_pos_left h2 hD
    _ ≤ d * q := Nat.mul_le_mul_right q h3

theorem ff_exclusion_aux : ∀ (n : ℕ) {E : Type u} [AddCommGroup E] [Module (ZMod 2) E] [Finite E],
    Nat.card E = n → ∀ (ρ : H32 →* (E ≃ₗ[ZMod 2] E)),
    (∃ (g : GL32) (x : E), ρ (sIncl g) x ≠ x) → ∀ A : Subgroup H32, A ≠ ⊥ →
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card A * Nat.card (fixedSub ρ A) < Nat.card E := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ _ _ hn ρ hS A hA0 hcomm hsq
    by_cases hirr : IsIrrRep ρ
    · rcases irreducible_GL3_ext_classification ρ hirr with h | h | h
      · exfalso
        obtain ⟨φ, hφ⟩ := h
        obtain ⟨g, x, hx⟩ := hS
        apply hx
        obtain ⟨c, rfl⟩ := φ.surjective x
        exact (hφ (sIncl g) c).symm
      · have hcard := natCard_fixedSub_of_modIso h A
        have hE : Nat.card E = 64 := (card_eq_of_modIso_H h).symm.trans natCard_P6
        rw [hcard, hE]
        exact (fixed_bounds hA0 hcomm hsq).2.1
      · have hcard := natCard_fixedSub_of_modIso h A
        have hE : Nat.card E = 256 := (card_eq_of_modIso_H h).symm.trans natCard_traceZero
        rw [hcard, hE]
        exact (fixed_bounds hA0 hcomm hsq).2.2
    · have hnt : Nontrivial E := by
        obtain ⟨g, x, hx⟩ := hS
        exact ⟨ρ (sIncl g) x, x, hx⟩
      obtain ⟨D, hD, hD0, hDtop⟩ : ∃ D : Submodule (ZMod 2) E, IsInvRep ρ D ∧ D ≠ ⊥ ∧ D ≠ ⊤ := by
        by_contra hcon
        apply hirr
        refine ⟨hnt, fun g => map_zero (ρ g), fun N hN => ?_⟩
        by_contra hN'
        push Not at hN'
        exact hcon ⟨N, fun g x hx => hN g x hx, hN'.1, hN'.2⟩
      have hcardE : Nat.card E = Nat.card D * Nat.card (E ⧸ D) :=
        Submodule.card_eq_card_quotient_mul_card D
      have : Finite (E ⧸ D) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective D)
      have hDnt : Nontrivial D := (Submodule.nontrivial_iff_ne_bot).2 hD0
      have hQnt : Nontrivial (E ⧸ D) := by
        obtain ⟨x, hx⟩ : ∃ x : E, x ∉ D := by
          by_contra h
          push Not at h
          exact hDtop (eq_top_iff.2 fun x _ => h x)
        exact ⟨Submodule.Quotient.mk x, 0, fun h => hx ((Submodule.Quotient.mk_eq_zero D).1 h)⟩
      have hd2 : 1 < Nat.card D := Finite.one_lt_card_iff_nontrivial.2 hDnt
      have hq2 : 1 < Nat.card (E ⧸ D) := Finite.one_lt_card_iff_nontrivial.2 hQnt
      have hdlt : Nat.card D < n := by rw [← hn, hcardE]; nlinarith
      have hqlt : Nat.card (E ⧸ D) < n := by rw [← hn, hcardE]; nlinarith
      have hsub := natCard_fixedSub_le ρ D hD A
      have hcD : Nat.card (fixedSub (subRep ρ D hD) A) ≤ Nat.card D :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      have hcQ : Nat.card (fixedSub (quotRep ρ D hD) A) ≤ Nat.card (E ⧸ D) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      have hposD : 0 < Nat.card (fixedSub (subRep ρ D hD) A) := Nat.card_pos
      have hposQ : 0 < Nat.card (fixedSub (quotRep ρ D hD) A) := Nat.card_pos
      by_cases hSD : ∃ (g : GL32) (x : D), subRep ρ D hD (sIncl g) x ≠ x
      · have := ih (Nat.card D) hdlt rfl (subRep ρ D hD) hSD A hA0 hcomm hsq
        rw [hcardE]
        exact mul_lt_of_fixed _ _ _ _ _ _ hsub this hcQ hposQ
      · by_cases hSQ : ∃ (g : GL32) (x : E ⧸ D), quotRep ρ D hD (sIncl g) x ≠ x
        · have := ih (Nat.card (E ⧸ D)) hqlt rfl (quotRep ρ D hD) hSQ A hA0 hcomm hsq
          rw [hcardE]
          exact mul_lt_of_fixed' _ _ _ _ _ _ hsub this hcD hposD
        · exfalso
          push Not at hSD hSQ
          have h1 : ∀ g, ∀ x ∈ D, (ρ.comp sIncl) g x = x := fun g x hx =>
            congrArg Subtype.val (hSD g ⟨x, hx⟩)
          have h2 : ∀ g x, (ρ.comp sIncl) g x - x ∈ D := fun g x => by
            have := hSQ g (Submodule.Quotient.mk x)
            rw [quotRep_mk] at this
            have h3 : Submodule.Quotient.mk (ρ (sIncl g) x - x) = (0 : E ⧸ D) := by
              rw [Submodule.Quotient.mk_sub, this, sub_self]
            exact (Submodule.Quotient.mk_eq_zero D).1 h3
          have := rep_trivial_of_sub_quot GL32_isPerfect (ρ.comp sIncl) D h1 h2
          obtain ⟨g, x, hx⟩ := hS
          exact hx (this g x)

theorem GL3_ext_excludes_FF {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (ρ : H32 →* (E ≃ₗ[ZMod 2] E)) (hS : ∃ (g : GL32) (x : E), ρ (sIncl g) x ≠ x)
    (A : Subgroup H32) (hA0 : A ≠ ⊥) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hsq : ∀ a ∈ A, a ^ 2 = 1) : Nat.card A * Nat.card (fixedSub ρ A) < Nat.card E :=
  ff_exclusion_aux _ rfl ρ hS A hA0 hcomm hsq

theorem finrank_eq_of_natCard_eq {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    {k : ℕ} (h : Nat.card M = 2 ^ k) : Module.finrank (ZMod 2) M = k := by
  have h1 := FiniteField.pow_finrank_eq_natCard 2 M
  rw [h] at h1
  exact Nat.pow_right_injective le_rfl h1

instance : Finite H32 := Finite.of_equiv _ SemidirectProduct.equivProd.symm

end CFSG.QuasithinUnique.Setup.Family