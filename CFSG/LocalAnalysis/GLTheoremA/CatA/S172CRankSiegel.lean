module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
open scoped commutatorElement

private theorem vec_add_self (F : Type*) [Field F] [CharP F 2] {V : Type*} [AddCommGroup V]
    [Module F V] (w : V) : w + w = 0 := by
  rw [← two_smul F w, CharTwo.two_eq_zero, zero_smul]

variable {F : Type*} [Field F] [CharP F 2] {V : Type*} [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V}

theorem mul_self_eq_one_of_mem_rootGroup {e : V} {g : V ≃ₗ[F] V} (hg : g ∈ rootGroup Q e) :
    g * g = 1 := by
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.1 hg
  rw [eichler_mul hw hw, vec_add_self F w, eichler_zero_right]

theorem isPGroup_two_subgroupOf_rootGroup (e : V) :
    IsPGroup 2 ((rootGroup Q e).subgroupOf (orthDerived Q)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : g * g = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact mul_self_eq_one_of_mem_rootGroup (Subgroup.mem_subgroupOf.1 g.2)
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact ⟨0, by rw [h]; rfl⟩
  · exact ⟨1, by rw [h]; rfl⟩

theorem eichler_mem_orthDerived {e a w : V} (ha : Q a ≠ 0) (hea : polar Q e a = 0)
    (hew : polar Q e w = 0) (hwa : polar Q a w = Q a) : eichler Q e a ∈ orthDerived Q := by
  have hae : polar Q a e = 0 := by rw [polar_comm]; exact hea
  have hr : reflect Q a w = w + a := by
    rw [reflect_apply ha, hwa, div_self ha, one_smul, sub_eq_add_neg,
      neg_eq_of_add_eq_zero_right (vec_add_self F a)]
  have hwa' : polar Q e (w + a) = 0 := by rw [polar_add_right, hew, hea, add_zero]
  have key : ⁅reflect Q a, eichler Q e w⁆ = eichler Q e a := by
    have h1 := eichler_conj (reflect_mem_orthogonalGroup Q a) e w
    rw [reflect_apply_of_polar_eq_zero hae, hr] at h1
    rw [commutatorElement_def, h1, eichler_inv hew,
      eichler_mul hwa' (by rw [polar_neg_right, hew, neg_zero])]
    congr 1
    abel
  rw [← key]
  exact Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q a)
    (eichler_mem_orthogonalGroup Q e w)

theorem subgroupOf_rootGroup_ne_bot {e f a w : V} (he : Q e = 0) (ha : Q a ≠ 0)
    (hea : polar Q e a = 0) (hew : polar Q e w = 0) (hwa : polar Q a w = Q a)
    (hfe : polar Q f e = 1) (hfa : polar Q f a = 0) :
    (rootGroup Q e).subgroupOf (orthDerived Q) ≠ ⊥ := by
  intro hbot
  have hmem : eichler Q e a ∈ orthDerived Q := eichler_mem_orthDerived ha hea hew hwa
  have h1 : (⟨eichler Q e a, hmem⟩ : ↥(orthDerived Q)) ∈
      (rootGroup Q e).subgroupOf (orthDerived Q) :=
    Subgroup.mem_subgroupOf.2 (eichler_mem_rootGroup hea)
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : eichler Q e a = 1 := congrArg Subtype.val h1
  have h3 := congrArg (fun g : V ≃ₗ[F] V => g f) h2
  simp only [eichler_apply he hea, hfe, hfa, LinearEquiv.coe_one, id_eq, one_smul, zero_add,
    mul_one] at h3
  have h4 : a = Q a • e := by
    have h5 : f + a - Q a • e = f := h3
    have : a - Q a • e = 0 := by
      calc a - Q a • e = (f + a - Q a • e) - f := by abel
        _ = 0 := by rw [h5, sub_self]
    exact sub_eq_zero.1 this
  apply ha
  have h6 := congrArg Q h4
  rwa [map_smul_eq_sq, he, mul_zero] at h6

theorem mem_normalizer_subgroupOf_rootGroup {e : V} {g : ↥(orthDerived Q)}
    (hg : (g : V ≃ₗ[F] V) e = e) :
    g ∈ Subgroup.normalizer
      (((rootGroup Q e).subgroupOf (orthDerived Q) : Subgroup ↥(orthDerived Q)) :
        Set ↥(orthDerived Q)) := by
  have key : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) e = e →
      ∀ h ∈ (rootGroup Q e).subgroupOf (orthDerived Q),
        g * h * g⁻¹ ∈ (rootGroup Q e).subgroupOf (orthDerived Q) := by
    intro g hg h hh
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    have hgO : (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      Subgroup.commutator_le_self _ g.2
    exact conj_mem_rootGroup_of_apply_eq_smul hgO (by rw [hg, one_smul]) hh
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have hginv : ((g⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V) e = e := by
    calc ((g⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V) e
        = ((g⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) e) := by rw [hg]
      _ = e := by
        rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
        rfl
  have := key g⁻¹ hginv _ hh
  simpa [mul_assoc] using this

end CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

end
