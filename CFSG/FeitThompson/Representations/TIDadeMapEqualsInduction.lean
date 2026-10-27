module

public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
public import CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily
public import CFSG.FeitThompson.Definitions.PowerOperationOnClassFunctions
import CFSG.FeitThompson.Representations.TISetDadeData

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {A : Set G} {L : Subgroup G} {f : L → ℂ} {g : G}

open Classical in
noncomputable def tiDadeMap (A : Set G) (L : Subgroup G) (f : L → ℂ) (g : G) : ℂ :=
  if h : ∃ x : L, (x : G) ∈ A ∧ IsConj (x : G) g then f h.choose else 0

theorem tiDadeMap_eq_zero (hg : ∀ x : L, (x : G) ∈ A → ¬ IsConj (x : G) g) :
    tiDadeMap A L f g = 0 := by
  rw [tiDadeMap, dif_neg]
  rintro ⟨x, hx, hxg⟩
  exact hg x hx hxg

theorem tiDadeMap_add (f₁ f₂ : L → ℂ) :
    tiDadeMap A L (f₁ + f₂) = tiDadeMap A L f₁ + tiDadeMap A L f₂ := by
  funext g
  simp only [tiDadeMap, Pi.add_apply]
  split <;> simp

theorem tiDadeMap_smul (c : ℂ) (f : L → ℂ) :
    tiDadeMap A L (c • f) = c • tiDadeMap A L f := by
  funext g
  simp only [tiDadeMap, Pi.smul_apply]
  split <;> simp

@[simp] theorem tiDadeMap_zero : tiDadeMap A L (0 : L → ℂ) = 0 := by
  funext g
  simp only [tiDadeMap, Pi.zero_apply]
  split <;> simp

theorem tiDadeMap_apply_of_isConj (h : IsTIWithNormalizer A L) (hf : IsClassFun f)
    (x : L) (hx : (x : G) ∈ A) (hxg : IsConj (x : G) g) :
    tiDadeMap A L f g = f x := by
  have hex : ∃ y : L, (y : G) ∈ A ∧ IsConj (y : G) g := ⟨x, hx, hxg⟩
  rw [tiDadeMap, dif_pos hex]
  obtain ⟨hy, hyg⟩ := hex.choose_spec
  obtain ⟨c, hc, hcx⟩ := h.fusion hy hx (hyg.trans hxg.symm)
  exact hf.apply_eq (isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext (by simpa using hcx)⟩)

theorem tiDadeMap_apply_mem (h : IsTIWithNormalizer A L) (hf : IsClassFun f)
    (x : L) (hx : (x : G) ∈ A) : tiDadeMap A L f (x : G) = f x :=
  tiDadeMap_apply_of_isConj h hf x hx (IsConj.refl _)

theorem isClassFun_tiDadeMap (h : IsTIWithNormalizer A L) (hf : IsClassFun f) :
    IsClassFun (tiDadeMap A L f) := by
  refine isClassFun_iff.2 fun x g => ?_
  have hg : IsConj (x * g * x⁻¹) g := isConj_iff.2 ⟨x⁻¹, by group⟩
  by_cases hex : ∃ y : L, (y : G) ∈ A ∧ IsConj (y : G) g
  · obtain ⟨y, hy, hyg⟩ := hex
    rw [tiDadeMap_apply_of_isConj h hf y hy (hyg.trans hg.symm),
      tiDadeMap_apply_of_isConj h hf y hy hyg]
  · rw [tiDadeMap_eq_zero (fun y hy hyg => hex ⟨y, hy, hyg.trans hg⟩),
      tiDadeMap_eq_zero (fun y hy hyg => hex ⟨y, hy, hyg⟩)]

private noncomputable def extZero (L : Subgroup G) (f : L → ℂ) : G → ℂ :=
  Function.extend L.subtype f 0

private theorem extZero_of_mem (f : L → ℂ) {z : G} (hz : z ∈ L) :
    extZero L f z = f ⟨z, hz⟩ := L.subtype_injective.extend_apply f 0 ⟨z, hz⟩

private theorem extZero_of_notMem (f : L → ℂ) {z : G} (hz : z ∉ L) : extZero L f z = 0 := by
  refine Function.extend_apply' _ _ _ ?_
  rintro ⟨a, rfl⟩
  exact hz a.2

private theorem indClassFun_eq_sum_extZero [Fintype G] (f : L → ℂ) (g : G) :
    indClassFun L f g = (Nat.card L : ℂ)⁻¹ * ∑ t : G, extZero L f (t⁻¹ * g * t) := by
  classical
  rw [indClassFun_apply]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hz : t⁻¹ * g * t ∈ L
  · rw [dif_pos hz, extZero_of_mem f hz]
  · rw [dif_neg hz, extZero_of_notMem f hz]

private theorem card_filter_mem [Fintype G] (L : Subgroup G) [DecidablePred (· ∈ L)] :
    (Finset.univ.filter (· ∈ L)).card = Nat.card L := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem tiDadeMap_eq_indClassFun [Fintype G] (h : IsTIWithNormalizer A L) (hf : IsClassFun f)
    (hf0 : ∀ x : L, (x : G) ∉ A → f x = 0) :
    tiDadeMap A L f = indClassFun L f := by
  classical
  funext g
  rw [indClassFun_eq_sum_extZero]
  by_cases hg : ∃ x : L, (x : G) ∈ A ∧ IsConj (x : G) g
  ·
    obtain ⟨a, ha, hconj⟩ := hg
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    rw [tiDadeMap_apply_of_isConj h hf a ha hconj]
    have hre : (∑ t : G, extZero L f (t⁻¹ * g * t))
        = ∑ s : G, if s ∈ L then f a else 0 := by
      refine (Fintype.sum_equiv (Equiv.mulLeft c) _ _ fun s => ?_).symm
      simp only [Equiv.coe_mulLeft]
      rw [show (c * s)⁻¹ * g * (c * s) = s⁻¹ * (a : G) * s by rw [← hc]; group]
      by_cases hs : s ∈ L
      ·
        have hmem : s⁻¹ * (a : G) * s ∈ A := by
          have := h.conj_mem ha (inv_mem hs)
          simpa using this
        have hzL : s⁻¹ * (a : G) * s ∈ L := h.subset_coe hmem
        rw [if_pos hs, extZero_of_mem f hzL]
        exact hf.apply_eq (isConj_iff.2 ⟨⟨s, hs⟩⁻¹, Subtype.ext (by simp)⟩)
      ·
        rw [if_neg hs]
        by_cases hzL : s⁻¹ * (a : G) * s ∈ L
        · rw [extZero_of_mem f hzL]
          refine (hf0 _ fun hmem => hs ?_).symm
          have := h.mem_of_conj_mem ha (g := s⁻¹) (by simpa using hmem)
          simpa using this
        · rw [extZero_of_notMem f hzL]
    rw [hre, ← Finset.sum_filter, Finset.sum_const, card_filter_mem, nsmul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  ·
    rw [tiDadeMap_eq_zero (by intro x hx hxg; exact hg ⟨x, hx, hxg⟩)]
    have hz : ∀ t : G, extZero L f (t⁻¹ * g * t) = 0 := by
      intro t
      by_cases hz : t⁻¹ * g * t ∈ L
      · rw [extZero_of_mem f hz]
        refine hf0 _ fun hmem => hg ⟨⟨_, hz⟩, hmem, isConj_iff.2 ⟨t, by group⟩⟩
      · rw [extZero_of_notMem f hz]
    rw [Finset.sum_congr rfl fun t _ => hz t]
    simp

theorem tiDadeMap_eq_indClassFun_of_conj_image_eq_or_disjoint [Fintype G] (hne : A.Nonempty)
    (h1 : (1 : G) ∉ A)
    (hTI : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ∨ (fun x => g⁻¹ * x * g) '' A ∩ A = ∅)
    {f : Subgroup.normalizer A → ℂ} (hf : IsClassFun f)
    (hf0 : ∀ x : Subgroup.normalizer A, (x : G) ∉ A → f x = 0) :
    tiDadeMap A (Subgroup.normalizer A) f = indClassFun (Subgroup.normalizer A) f :=
  tiDadeMap_eq_indClassFun (isTIWithNormalizer_normalizer hne h1 hTI) hf hf0

end CFSG.FeitThompson
