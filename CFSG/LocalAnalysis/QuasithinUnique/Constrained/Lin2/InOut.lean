module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.GorensteinWalter CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

section Generic

variable {L K A : Type*} [Group L] [Group K] [Group A]

theorem exists_act_quot (α : L →* K) (hα : Function.Surjective α) (act : A →* MulAut L)
    (hker : ∀ a : A, ∀ ℓ : L, α (act a ℓ) = 1 ↔ α ℓ = 1) :
    ∃ Ψ : A →* MulAut K, ∀ a ℓ, Ψ a (α ℓ) = α (act a ℓ) := by
  have h1 : ∀ a : A, ∃ ψ : K →* K, ∀ ℓ, ψ (α ℓ) = α (act a ℓ) := by
    intro a
    refine ⟨MonoidHom.liftOfSurjective α hα ⟨α.comp (act a).toMonoidHom, ?_⟩, ?_⟩
    · intro ℓ hℓ
      exact (hker a ℓ).2 hℓ
    · intro ℓ
      exact MonoidHom.liftOfRightInverse_comp_apply α (Function.surjInv hα)
        (Function.rightInverse_surjInv hα) _ ℓ
  choose ψ hψ using h1
  have hψ_mul : ∀ a b : A, ∀ k : K, ψ (a * b) k = ψ a (ψ b k) := by
    intro a b k
    obtain ⟨ℓ, rfl⟩ := hα k
    rw [hψ, hψ, hψ, map_mul]
    rfl
  have hψ_one : ∀ k : K, ψ 1 k = k := by
    intro k
    obtain ⟨ℓ, rfl⟩ := hα k
    rw [hψ]
    simp
  let Ψ0 : A → MulAut K := fun a =>
    { toFun := ψ a
      invFun := ψ a⁻¹
      left_inv := fun k => by rw [← hψ_mul, inv_mul_cancel, hψ_one]
      right_inv := fun k => by rw [← hψ_mul, mul_inv_cancel, hψ_one]
      map_mul' := fun x y => map_mul (ψ a) x y }
  refine ⟨{ toFun := Ψ0
            map_one' := by ext k; exact hψ_one k
            map_mul' := fun a b => by ext k; exact hψ_mul a b k }, hψ⟩

theorem exists_injective_of_act_quot (α : L →* K) (hα : Function.Surjective α) (act : A →* MulAut L)
    (hker : ∀ a : A, ∀ ℓ : L, α (act a ℓ) = 1 ↔ α ℓ = 1)
    (hinner : ∀ a : A, (∃ k : K, ∀ ℓ, α (act a ℓ) = k * α ℓ * k⁻¹) → a = 1) :
    ∃ φ : A →* Outer K, Function.Injective φ := by
  obtain ⟨Ψ, hΨ⟩ := exists_act_quot α hα act hker
  refine ⟨(QuotientGroup.mk' (inner K)).comp Ψ, ?_⟩
  rw [injective_iff_map_eq_one]
  intro a ha
  apply hinner
  have : Ψ a ∈ inner K := by
    have h2 : (QuotientGroup.mk' (inner K)) (Ψ a) = 1 := ha
    exact (QuotientGroup.eq_one_iff _).1 h2
  obtain ⟨k, hk⟩ := this
  refine ⟨k, fun ℓ => ?_⟩
  rw [← hΨ, ← hk]
  simp [MulAut.conj_apply]

end Generic

section CharTwo

variable (K : Type) [Field K]

theorem center_specialLinearGroup_eq_bot (hK : (2 : K) = 0) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Subgroup.mem_bot]
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr2 - r * hK + hK
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
  subst hr1
  apply Subtype.ext
  rw [← hrA]
  simp

@[expose] noncomputable def psl2EquivSl2 (hK : (2 : K) = 0) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* SL(2, K) :=
  (QuotientGroup.quotientMulEquivOfEq (center_specialLinearGroup_eq_bot K hK)).trans
    QuotientGroup.quotientBot

theorem psl2EquivSl2_mk (hK : (2 : K) = 0) (Y : SL(2, K)) :
    psl2EquivSl2 K hK (QuotientGroup.mk' (Subgroup.center SL(2, K)) Y) = Y := rfl

theorem quotientFieldProjection_injective_of_char_two [Finite K] (hK : (2 : K) = 0) :
    Function.Injective (quotientFieldProjection K) := by
  have hcp : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast hK)
  have hrc : ringChar K = 2 := ringChar.eq K 2
  rw [injective_iff_map_eq_one]
  intro x hx
  have hker : x ∈ (quotientFieldProjection K).ker := hx
  rw [quotientFieldProjection_ker K] at hker
  obtain ⟨g, rfl⟩ := hker
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  obtain ⟨y, hy⟩ := (pgl2_mk_mem_psl2_range_iff_det_isSquare A).2
    (FiniteField.isSquare_of_char_two hrc _)
  change QuotientGroup.mk' (pGammaL2PSLRange K) (SemidirectProduct.inl _) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (mem_pGammaL2PSLRange_iff K _).2 ⟨y, congrArg SemidirectProduct.inl hy⟩

theorem exists_injective_outer_sl2_char_two [Finite K] (hK : (2 : K) = 0) :
    ∃ ψ : Outer SL(2, K) →* (K ≃+* K), Function.Injective ψ := by
  refine ⟨(quotientFieldProjection K).comp
    ((outerEquivSemilinearQuotient K).symm.toMonoidHom.comp
      (equivalence (psl2EquivSl2 K hK).symm).toMonoidHom), ?_⟩
  exact (quotientFieldProjection_injective_of_char_two K hK).comp
    ((outerEquivSemilinearQuotient K).symm.injective.comp
      (equivalence (psl2EquivSl2 K hK).symm).injective)

end CharTwo

end CFSG.QuasithinUnique.Lin2
