module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.BalanceConstancy

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

theorem isConj_of_mem_centralizer {t : X} (ht : orderOf t = 2)
    (hJ : IsTwoANine (EscapingQuotient t)) {u v : centralizer ({t} : Set X)}
    (hu : orderOf u = 2) (hv : orderOf v = 2) (hut : (u : X) ≠ t) (hvt : (v : X) ≠ t) :
    IsConj u v := by
  have hne : ∀ {w : centralizer ({t} : Set X)}, orderOf w = 2 → (w : X) ≠ t →
      escapingMk t w ≠ zbar (EscapingQuotient t) := fun hw hwt h =>
    hwt (hJ.eq_of_escapingMk_eq_zbar ht (by rw [← hw, pow_orderOf_eq_one]) h)
  exact escaping_isConj_of_isConj_mk t hu hv (hJ.isConj_of_orderOf_eq_two
    (escaping_orderOf_mk t hu) (escaping_orderOf_mk t hv) (hne hu hut) (hne hv hvt))

omit [Finite X] in
theorem orderOf_conj_eq (g a : X) : orderOf (g * a * g⁻¹) = orderOf a := by
  simpa only [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq a

theorem exists_conj_mem_sylow (S : Sylow 2 X) {a : X} (ha : orderOf a = 2) :
    ∃ x : X, x * a * x⁻¹ ∈ (S : Subgroup X) := by
  have hP : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X Q S
  refine ⟨x, ?_⟩
  have h := Subgroup.smul_mem_pointwise_smul a (MulAut.conj x) (Q : Subgroup X)
    (hQ (Subgroup.mem_zpowers a))
  rw [← Sylow.coe_subgroup_smul, hx] at h
  exact h

theorem isConj_of_orderOf_eq_two_of_conj_ne (S : Sylow 2 X) {t : X}
    (ht : IsCentralInvolution (S : Subgroup X) t) (hJ : IsTwoANine (EscapingQuotient t)) {g : X}
    (hgS : g⁻¹ * t * g ∈ (S : Subgroup X)) (hgt : g⁻¹ * t * g ≠ t) {a : X} (ha : orderOf a = 2) :
    IsConj t a := by
  have hSt := le_centralizer_of_isCentralInvolution ht
  obtain ⟨x, hx⟩ := exists_conj_mem_sylow S ha
  have hab : IsConj a (x * a * x⁻¹) := isConj_iff.mpr ⟨x, rfl⟩
  by_cases hxt : x * a * x⁻¹ = t
  · rw [← hxt]
    exact hab.symm
  have hu : orderOf (g⁻¹ * t * g) = 2 := by
    have h := orderOf_conj_eq g⁻¹ t
    rw [inv_inv] at h
    rw [h, ht.2.1]
  have hconj := isConj_of_mem_centralizer ht.2.1 hJ (u := ⟨g⁻¹ * t * g, hSt hgS⟩)
    (v := ⟨x * a * x⁻¹, hSt hx⟩) (by rw [Subgroup.orderOf_mk, hu])
    (by rw [Subgroup.orderOf_mk, orderOf_conj_eq, ha]) hgt hxt
  have h1 : IsConj t (g⁻¹ * t * g) := isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩
  exact h1.trans (((centralizer ({t} : Set X)).subtype.map_isConj hconj).trans hab.symm)

theorem isTwoANine_escapingQuotient_of_conj_ne (S : Sylow 2 X) {t : X}
    (ht : IsCentralInvolution (S : Subgroup X) t) (hJ : IsTwoANine (EscapingQuotient t)) {g : X}
    (hgS : g⁻¹ * t * g ∈ (S : Subgroup X)) (hgt : g⁻¹ * t * g ≠ t) {a : X} (ha : orderOf a = 2) :
    IsTwoANine (EscapingQuotient a) :=
  hJ.of_isConj_escapingQuotient (isConj_of_orderOf_eq_two_of_conj_ne S ht hJ hgS hgt ha)

theorem signalizerJoin_of_conj_ne (S : Sylow 2 X) {t : X}
    (ht : IsCentralInvolution (S : Subgroup X) t) (hJ : IsTwoANine (EscapingQuotient t)) {g : X}
    (hgS : g⁻¹ * t * g ∈ (S : Subgroup X)) (hgt : g⁻¹ * t * g ≠ t) {A : Subgroup X}
    (hAS : A ≤ S) (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA : Nat.card A = 16) :
    Odd (Nat.card (signalizerJoin A)) ∧
    (∀ a ∈ A, a ≠ 1 → signalizerJoin A ⊓ centralizer {a} = oddCentralizer a) ∧
    (∀ Y : Subgroup X, Odd (Nat.card Y) → A ≤ normalizer (Y : Set X) → Y ≤ signalizerJoin A) ∧
    (S : Subgroup X) ≤ normalizer (signalizerJoin A : Set X) ∧
    normalizer (A : Set X) ≤ normalizer (signalizerJoin A : Set X) := by
  have hall : ∀ c : X, orderOf c = 2 → IsTwoANine (EscapingQuotient c) := fun c hc =>
    isTwoANine_escapingQuotient_of_conj_ne S ht hJ hgS hgt hc
  have hallA : ∀ b ∈ A, b ≠ 1 → IsTwoANine (EscapingQuotient b) := fun b hb hb1 =>
    hall b (orderOf_eq_prime (hA2 b hb) hb1)
  have hA8 : 8 ≤ Nat.card A := by rw [hA]; norm_num
  exact ⟨odd_card_signalizerJoin hA2 hA8 hallA,
    fun a haA ha1 => signalizerJoin_inf_centralizer hA2 hA8 hallA haA ha1,
    fun Y hY hAY => le_signalizerJoin_of_odd hA2 hA hallA hY hAY,
    le_normalizer_signalizerJoin_of_le hall ht.2.1 hA2 hA S.isPGroup'
      (le_centralizer_of_isCentralInvolution ht) hAS,
    normalizer_le_normalizer_signalizerJoin A⟩

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
