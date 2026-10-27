module

public import CFSG.CharacterTheory.Wreathed.OddNormalQuotientInvolutions
public import CFSG.CharacterTheory.Wreathed.CentralSL2.CuspidalInduction
public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.OrderFormula

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.InvolutionInducedCharacters

open CFSG.Wreathed CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.OddNormalQuotientInvolutions

section Quotient

variable {N : Type} [Group N] [Finite N] (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R))
  {H : Type*} [Group H] (Φ : H ≃* N ⧸ R)

omit [Finite N] in
include hR in
theorem orderOf_mk_eq_two {t : N} (ht : orderOf t = 2) :
    orderOf (QuotientGroup.mk' R t) = 2 := by
  have hdvd : orderOf (QuotientGroup.mk' R t) ∣ 2 := by
    rw [← ht]
    exact orderOf_map_dvd _ t
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exfalso
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h := Subgroup.orderOf_dvd_natCard R h1
    rw [ht] at h
    exact (Nat.not_even_iff_odd.mpr hR) (even_iff_two_dvd.mpr h)
  · exact h2

include hR in
theorem isConj_of_isConj_mk {t t' : N} (ht : orderOf t = 2) (ht' : orderOf t' = 2)
    (hconj : IsConj (QuotientGroup.mk' R t) (QuotientGroup.mk' R t')) : IsConj t t' := by
  have hbij := (odd_normal_quotient_involution_classes_and_centralizers R hR).1
  have hmem : ∀ s : N, orderOf s = 2 → ConjClasses.mk s ∈ involutionClasses N := fun s hs =>
    ⟨s, hs, rfl⟩
  have h := hbij.injOn (hmem t ht) (hmem t' ht')
    (show ConjClasses.mk (QuotientGroup.mk' R t) = ConjClasses.mk (QuotientGroup.mk' R t') from
      ConjClasses.mk_eq_mk_iff_isConj.mpr hconj)
  exact ConjClasses.mk_eq_mk_iff_isConj.mp h

include hR in
theorem involutions_of_quotient_model {x₀ y₀ : H}
    (hH : ∀ h : H, orderOf h = 2 ↔ h = x₀ ∨ IsConj y₀ h) (hxy₀ : ¬ IsConj x₀ y₀)
    {x y : N} (hxc : x ∈ Subgroup.center N) (hx2 : orderOf x = 2)
    (hxΦ : QuotientGroup.mk' R x = Φ x₀) (hy2 : orderOf y = 2)
    (hyΦ : QuotientGroup.mk' R y = Φ y₀) :
    (∀ t : N, orderOf t = 2 ↔ t = x ∨ IsConj y t) ∧ ¬ IsConj x y := by
  have hQ := odd_normal_quotient_involution_classes_and_centralizers R hR
  have hfiber := ((hQ.2.2 (QuotientGroup.mk' R x) x hx2 rfl).2.2.2.2.2.2) hxc
  constructor
  · intro t
    constructor
    · intro ht
      have hord := orderOf_mk_eq_two R hR ht
      have hordH : orderOf (Φ.symm (QuotientGroup.mk' R t)) = 2 := by
        rw [MulEquiv.orderOf_eq]
        exact hord
      rcases (hH _).mp hordH with h | h
      · left
        have hmk : QuotientGroup.mk' R t = QuotientGroup.mk' R x := by
          rw [hxΦ, ← h, MulEquiv.apply_symm_apply]
        have hmem : t ∈ involutionFiber R (QuotientGroup.mk' R x) := ⟨ht, hmk⟩
        rw [hfiber] at hmem
        exact hmem
      · right
        apply isConj_of_isConj_mk R hR hy2 ht
        have h' := (MonoidHom.map_isConj Φ.toMonoidHom h)
        simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h'
        rw [hyΦ]
        exact h'
    · rintro (rfl | h)
      · exact hx2
      · rw [← hy2]
        obtain ⟨c, hc⟩ := isConj_iff.mp h
        rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  · intro h
    apply hxy₀
    have h' := MonoidHom.map_isConj (QuotientGroup.mk' R) h
    rw [hxΦ, hyΦ] at h'
    have h'' := MonoidHom.map_isConj Φ.symm.toMonoidHom h'
    simpa using h''

end Quotient

section Induced

variable {G : Type} [Group G] [Fintype G]

theorem sum_isConj_two_classes (N : Subgroup G) {x y : N}
    (hconj : ∀ h : N, IsConj (x : G) (h : G) ↔ h = x ∨ IsConj y h) (hxy : ¬ IsConj y x)
    (ψ : N → ℂ) (hψ : ∀ g h : N, ψ (g * h * g⁻¹) = ψ h) :
    ∑ h : N, (if IsConj (x : G) (h : G) then ψ h else 0) =
      ψ x + (Nat.card (ConjClasses.mk y).carrier : ℂ) * ψ y := by
  have hsplit : ∀ h : N, (if IsConj (x : G) (h : G) then ψ h else 0) =
      (if h = x then ψ h else 0) + (if IsConj y h then ψ y else 0) := by
    intro h
    by_cases hx : h = x
    · subst hx
      rw [ite_eq_left (IsConj.refl _), ite_eq_left rfl, ite_eq_right hxy, add_zero]
    · by_cases hy : IsConj y h
      · rw [ite_eq_left ((hconj h).mpr (Or.inr hy)), ite_eq_right hx, ite_eq_left hy, zero_add]
        obtain ⟨c, hc⟩ := isConj_iff.mp hy
        rw [← hc, hψ]
      · rw [ite_eq_right (fun h' => by rcases (hconj h).mp h' with h1 | h1 <;> contradiction),
          ite_eq_right hx, ite_eq_right hy, add_zero]
  rw [Finset.sum_congr rfl fun h _ => hsplit h, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  congr 1
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hcarrier : (ConjClasses.mk y).carrier = {h | IsConj y h} := by
    ext h
    simp only [ConjClasses.mem_carrier_iff_mk_eq, Set.mem_ofPred_eq]
    exact ⟨fun h' => ConjClasses.mk_eq_mk_iff_isConj.mp h'.symm,
      fun h' => (ConjClasses.mk_eq_mk_iff_isConj.mpr h').symm⟩
  rw [hcarrier]
  change _ = ((Nat.card {h // IsConj y h} : ℕ) : ℂ)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem inducedFunction_two_classes (N : Subgroup G) {x y : N}
    (hN : N = Subgroup.centralizer {(x : G)})
    (hconj : ∀ h : N, IsConj (x : G) (h : G) ↔ h = x ∨ IsConj y h) (hxy : ¬ IsConj y x)
    (ψ : N → ℂ) (hψ : ∀ g h : N, ψ (g * h * g⁻¹) = ψ h) :
    inducedFunction N ψ x = ψ x + (Nat.card (ConjClasses.mk y).carrier : ℂ) * ψ y := by
  rw [CFSG.Wreathed.CentralSL2.inducedFunction_eq_sum_isConj, sum_isConj_two_classes N hconj hxy ψ
    hψ, ← hN]
  have hpos : (Nat.card N : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  field_simp

theorem classWeight_two_classes (N : Subgroup G) {x y : N}
    (hconj : ∀ h : N, IsConj (x : G) (h : G) ↔ h = x ∨ IsConj y h) (hxy : ¬ IsConj y x)
    (ψ : N → ℂ) (hψ : ∀ g h : N, ψ (g * h * g⁻¹) = ψ h) :
    CFSG.LyonsUnitaryFour.classWeight N ψ x =
      (Nat.card N : ℂ)⁻¹ * (ψ x + (Nat.card (ConjClasses.mk y).carrier : ℂ) * ψ y) := by
  rw [CFSG.LyonsUnitaryFour.classWeight, ← sum_isConj_two_classes N hconj hxy ψ hψ]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  exact if_congr isConj_comm rfl rfl

end Induced

end CFSG.Wreathed.InvolutionInducedCharacters
