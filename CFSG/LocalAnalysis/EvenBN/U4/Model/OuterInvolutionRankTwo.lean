module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.OuterInvolutionRank
public import CFSG.LocalAnalysis.EvenBN.U4.Fusion
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

section Lift

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_mul_self {x : G} (hx2 : x * x = 1) : IsPGroup 2 (zpowers x) := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hx2])
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])

omit [Finite G] in
theorem eq_one_of_mem_of_isPGroup_of_odd {P Z : Subgroup G} (hP : IsPGroup 2 P)
    (hZ : Odd (Nat.card Z)) {y : G} (hyP : y ∈ P) (hyZ : y ∈ Z) : y = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨y, hyP⟩
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    simpa using congrArg Subtype.val hk)
  have h2 : orderOf y ∣ Nat.card Z := by
    have := Subgroup.orderOf_dvd_natCard Z hyZ
    exact this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card Z) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hZ)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2)

theorem exists_elementaryAbelian_le_centralizer_of_odd {H Z : Subgroup G}
    (hZodd : Odd (Nat.card Z)) {n : ℕ} (hcard : Nat.card H = Nat.card Z * 2 ^ n)
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ Z) (hsq : ∀ a ∈ H, a * a ∈ Z)
    {x : G} (hx2 : x * x = 1) (hxH : x ∈ normalizer (H : Set G))
    (hxZ : ∀ a ∈ H, x * a * x⁻¹ * a⁻¹ ∈ Z) :
    ∃ E : Subgroup G, E ≤ H ∧ E ≤ centralizer ({x} : Set G) ∧ CFSG.IsElementaryAbelian 2 E ∧
      Nat.card E = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G := H ⊔ zpowers x with hK
  have hHK : H ≤ K := le_sup_left
  have hxK : x ∈ K := mem_sup_right (mem_zpowers x)
  have hKN : K ≤ normalizer (H : Set G) := sup_le le_normalizer ((zpowers_le).2 hxH)
  obtain ⟨Q, hQ⟩ := ((isPGroup_zpowers_of_mul_self hx2).comap_subtype (K := K)).exists_le_sylow
  set R : Subgroup G := (Q : Subgroup K).map K.subtype with hR
  have hRsyl : IsSylowOf 2 R K := ⟨Q, rfl⟩
  have hxR : x ∈ R := ⟨⟨x, hxK⟩, hQ (mem_subgroupOf.2 (mem_zpowers x)), rfl⟩
  set P : Subgroup G := R ⊓ H with hP
  have hPsyl : IsSylowOf 2 P H := hRsyl.inf_of_le_normalizer hHK hKN
  have hPcard : Nat.card P = 2 ^ n := by
    rw [hPsyl.card_eq, hcard, Nat.factorization_mul (by have := hZodd.pos; omega)
      (by positivity), Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
      (fun h2 => (Nat.not_even_iff_odd.2 hZodd) (even_iff_two_dvd.2 h2)),
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same, zero_add]
  have hPp : IsPGroup 2 P := hPsyl.isPGroup
  have hPZ : ∀ y ∈ P, y ∈ Z → y = 1 := fun y hyP hyZ =>
    eq_one_of_mem_of_isPGroup_of_odd hPp hZodd hyP hyZ
  have hxP : ∀ p ∈ P, x * p * x⁻¹ ∈ P := fun p hp =>
    mem_inf.2 ⟨mul_mem (mul_mem hxR (mem_inf.1 hp).1) (inv_mem hxR),
      (mem_normalizer_iff.1 hxH p).1 (mem_inf.1 hp).2⟩
  refine ⟨P, inf_le_right, fun p hp => ?_, isElementaryAbelian_two_of_forall
    (fun a ha b hb => ?_) (fun a ha => hPZ _ (mul_mem ha ha) (hsq a (mem_inf.1 ha).2)), hPcard⟩
  ·
    have h1 : x * p * x⁻¹ * p⁻¹ = 1 :=
      hPZ _ (mul_mem (hxP p hp) (inv_mem hp)) (hxZ p (mem_inf.1 hp).2)
    rw [mem_centralizer_singleton_iff]
    calc p * x = (x * p * x⁻¹ * p⁻¹)⁻¹ * (x * p) := by group
      _ = x * p := by rw [h1, inv_one, one_mul]
  ·
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 :=
      hPZ _ (mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))
        (hcomm a (mem_inf.1 ha).2 b (mem_inf.1 hb).2)
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]

end Lift

section Cover

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
@[expose] def quotientCenterConj {X : Subgroup G} (x : normalizer (X : Set G)) :
    MulAut (X ⧸ center X) :=
  QuotientGroup.congr (center X) (center X) (X.normalizerMonoidHom x)
    (characteristic_iff_map_eq.1 inferInstance _)

omit [Finite G] in
theorem quotientCenterConj_mk {X : Subgroup G} (x : normalizer (X : Set G)) (a : X) :
    quotientCenterConj x (a : X ⧸ center X) =
      ((X.normalizerMonoidHom x a : X) : X ⧸ center X) :=
  rfl

theorem exists_elementaryAbelian_le_centralizer_of_cover {X : Subgroup G}
    (ψ : X ⧸ center X ≃* gramSU h (miyamotoJ4 K)) (hZ : Odd (Nat.card (center X)))
    {x : G} (hxX : x ∈ normalizer (X : Set G)) (hx2 : x * x = 1) :
    ∃ E : Subgroup G, E ≤ X ∧ E ≤ centralizer ({x} : Set G) ∧ CFSG.IsElementaryAbelian 2 E ∧
      Nat.card E = (2 ^ f) ^ 3 := by
  set α := quotientCenterConj (⟨x, hxX⟩ : normalizer (X : Set G)) with hαdef
  have hconj : ∀ a : X, ((X.normalizerMonoidHom ⟨x, hxX⟩ a : X) : G) = x * a * x⁻¹ :=
    fun _ => rfl
  have hα : α * α = 1 := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [MulAut.mul_apply, hαdef, quotientCenterConj_mk, quotientCenterConj_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [hconj, hconj]
      calc x * (x * a * x⁻¹) * x⁻¹ = (x * x) * a * (x * x)⁻¹ := by group
        _ = a := by rw [hx2, inv_one, one_mul, mul_one]
  obtain ⟨E₀, hfix, hE₀e, hE₀c⟩ := exists_elementaryAbelian_fixed_of_mulEquiv h ψ hα
  set π : X →* X ⧸ center X := QuotientGroup.mk' (center X) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ a : X, π a = 1 ↔ a ∈ center X := fun a => QuotientGroup.eq_one_iff a
  set H : Subgroup G := (E₀.comap π).map X.subtype with hH
  set Z : Subgroup G := (center X).map X.subtype with hZdef
  have hmemH : ∀ a : X, (a : G) ∈ H ↔ π a ∈ E₀ := fun a =>
    ⟨fun ⟨b, hb, e⟩ => (Subtype.ext e : b = a) ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩
  have hmemZ : ∀ a : X, (a : G) ∈ Z ↔ a ∈ center X := fun a =>
    ⟨fun ⟨b, hb, e⟩ => (Subtype.ext e : b = a) ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩
  have hHX : H ≤ X := map_subtype_le _
  have hZX : Z ≤ X := map_subtype_le _
  have hlift : ∀ y ∈ H, ∃ a : X, (a : G) = y ∧ π a ∈ E₀ := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, rfl, ha⟩
  have hcardH : Nat.card H = Nat.card Z * 2 ^ (3 * f) := by
    rw [hH, hZdef, card_map_of_injective X.subtype_injective,
      card_map_of_injective X.subtype_injective]
    have h1 := Subgroup.card_mul_index (E₀.comap π)
    have h2 := Subgroup.card_mul_index E₀
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
    rw [index_comap_of_surjective _ hπs] at h1
    have hidx : 0 < E₀.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    have e : Nat.card (E₀.comap π) * E₀.index = Nat.card (center X) * 2 ^ (3 * f) * E₀.index := by
      rw [h1, h3, ← h2, hE₀c, ← pow_mul, mul_comm f 3]
      ring
    exact Nat.eq_of_mul_eq_mul_right hidx e
  have hE₀comm : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E₀) ⟨b, hb⟩)
  have hE₀sq : ∀ a ∈ E₀, a * a = 1 := fun a ha => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E₀) a ha
  obtain ⟨E, hEH, hEx, hEe, hEc⟩ := exists_elementaryAbelian_le_centralizer_of_odd
    (H := H) (Z := Z)
    (by rw [hZdef, card_map_of_injective X.subtype_injective]; exact hZ) hcardH
    (fun y hy z hz => by
      obtain ⟨a, rfl, ha⟩ := hlift y hy
      obtain ⟨b, rfl, hb⟩ := hlift z hz
      have e : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ = ((a * b * a⁻¹ * b⁻¹ : X) : G) := rfl
      rw [e, hmemZ, ← hker, map_mul, map_mul, map_mul, map_inv, map_inv, hE₀comm _ ha _ hb,
        mul_inv_cancel_right, mul_inv_cancel])
    (fun y hy => by
      obtain ⟨a, rfl, ha⟩ := hlift y hy
      have e : (a : G) * a = ((a * a : X) : G) := rfl
      rw [e, hmemZ, ← hker, map_mul]
      exact hE₀sq _ ha)
    hx2
    (mem_normalizer_fintype fun y hy => by
      obtain ⟨a, rfl, ha⟩ := hlift y hy
      rw [SetLike.mem_coe, ← hconj, hmemH]
      have := hfix _ ha
      rw [hπ, QuotientGroup.mk'_apply, hαdef, quotientCenterConj_mk] at this
      rw [hπ, QuotientGroup.mk'_apply, this]
      exact ha)
    (fun y hy => by
      obtain ⟨a, rfl, ha⟩ := hlift y hy
      have e : x * (a : G) * x⁻¹ * (a : G)⁻¹ =
          ((X.normalizerMonoidHom ⟨x, hxX⟩ a * a⁻¹ : X) : G) := by
        rw [Subgroup.coe_mul, hconj, Subgroup.coe_inv]
      have hfa := hfix _ ha
      rw [hπ, QuotientGroup.mk'_apply, hαdef, quotientCenterConj_mk] at hfa
      rw [e, hmemZ, ← hker, map_mul, map_inv, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, hfa, mul_inv_cancel])
  exact ⟨E, hEH.trans hHX, hEx, hEe, by rw [hEc, ← pow_mul, mul_comm]⟩

theorem exists_elementaryAbelian_le_centralizer_of_two_covers {G₁ G₂ : Subgroup G}
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (ψ₁ : G₁ ⧸ center G₁ ≃* gramSU h (miyamotoJ4 K))
    (ψ₂ : G₂ ⧸ center G₂ ≃* gramSU h (miyamotoJ4 K))
    (hZ₁ : Odd (Nat.card (center G₁))) (hZ₂ : Odd (Nat.card (center G₂))) {x : G}
    (hx2 : x * x = 1) (hx₁ : x ∈ normalizer (G₁ : Set G)) (hx₂ : x ∈ normalizer (G₂ : Set G)) :
    ∃ E : Subgroup G, E ≤ G₁ ⊔ G₂ ∧ E ≤ centralizer ({x} : Set G) ∧
      CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = (2 ^ f) ^ 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₁, hE₁, hE₁x, hE₁e, hE₁c⟩ :=
    exists_elementaryAbelian_le_centralizer_of_cover h ψ₁ hZ₁ hx₁ hx2
  obtain ⟨E₂, hE₂, hE₂x, hE₂e, hE₂c⟩ :=
    exists_elementaryAbelian_le_centralizer_of_cover h ψ₂ hZ₂ hx₂ hx2
  have hc12 : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb => hcomm a (hE₁ ha) b (hE₂ hb)
  have hsq : ∀ (E : Subgroup G) [CFSG.IsElementaryAbelian 2 E], ∀ a ∈ E, a * a = 1 :=
    fun E _ a ha => by rw [← sq]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) a ha
  have hcm : ∀ (E : Subgroup G) [CFSG.IsElementaryAbelian 2 E], ∀ a ∈ E, ∀ b ∈ E,
      a * b = b * a := fun E _ a ha b hb => congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hinf : E₁ ⊓ E₂ = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    have hyZ : (⟨y, hE₁ hy.1⟩ : G₁) ∈ center G₁ := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2 y (hE₂ hy.2))
    have hP : IsPGroup 2 (zpowers y) := isPGroup_zpowers_of_mul_self (hsq E₁ y hy.1)
    have hZ' : Odd (Nat.card ((center G₁).map G₁.subtype)) := by
      rw [card_map_of_injective G₁.subtype_injective]
      exact hZ₁
    exact mem_bot.2 (eq_one_of_mem_of_isPGroup_of_odd hP hZ' (mem_zpowers y) ⟨_, hyZ, rfl⟩)
  have hE₂N : E₂ ≤ normalizer (E₁ : Set G) := fun b hb =>
    mem_normalizer_fintype fun a ha => by rw [← hc12 a ha b hb, mul_inv_cancel_right]; exact ha
  have hcard := Common.card_sup_mul_card_inf_eq hE₂N
  rw [hinf, card_bot, mul_one, hE₁c, hE₂c] at hcard
  refine ⟨E₁ ⊔ E₂, sup_le_sup hE₁ hE₂, sup_le hE₁x hE₂x,
    isElementaryAbelian_two_of_forall (fun a ha b hb => ?_) (fun a ha => ?_), by
      rw [hcard]; ring⟩
  · obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hc12 ha
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hc12 hb
    rw [mul_assoc, ← mul_assoc a₂, ← hc12 b₁ hb₁ a₂ ha₂, mul_assoc b₁, hcm E₂ a₂ ha₂ b₂ hb₂,
      ← mul_assoc, hcm E₁ a₁ ha₁ b₁ hb₁, mul_assoc, mul_assoc, ← mul_assoc a₁,
      hc12 a₁ ha₁ b₂ hb₂, mul_assoc]
  · obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hc12 ha
    rw [mul_assoc, ← mul_assoc a₂, ← hc12 a₁ ha₁ a₂ ha₂, mul_assoc, hsq E₂ a₂ ha₂, mul_one,
      hsq E₁ a₁ ha₁]

theorem mem_normalizer_of_mem_normalizer_sup {G₁ G₂ : Subgroup G}
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hperf : ⁅G₂, G₂⁆ = G₂) {y : G}
    (hy : y ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) (hy₁ : y ∈ normalizer (G₁ : Set G)) :
    y ∈ normalizer (G₂ : Set G) := by
  set C : Subgroup G := (G₁ ⊔ G₂) ⊓ centralizer (G₁ : Set G) with hC
  have hG₂C : G₂ ≤ C := le_inf le_sup_right fun b hb =>
    mem_centralizer_iff.2 fun a ha => hcomm a ha b hb
  have hdec : ∀ c ∈ C, ∃ z ∈ G₁, (∀ g ∈ G₁ ⊔ G₂, z * g = g * z) ∧ ∃ b ∈ G₂, c = z * b := by
    intro c hc
    obtain ⟨z, hz, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hc.1
    have hzc : ∀ a ∈ G₁, a * z = z * a := by
      intro a ha
      have h1 := mem_centralizer_iff.1 hc.2 a ha
      have h2 := hcomm a ha b hb
      have : a * z * b = z * a * b := by
        calc a * z * b = a * (z * b) := mul_assoc _ _ _
          _ = z * b * a := h1
          _ = z * (b * a) := mul_assoc _ _ _
          _ = z * (a * b) := by rw [h2]
          _ = z * a * b := (mul_assoc _ _ _).symm
      exact mul_right_cancel this
    refine ⟨z, hz, fun g hg => ?_, b, hb, rfl⟩
    obtain ⟨a, ha, b', hb', rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hg
    rw [← mul_assoc, ← hzc a ha, mul_assoc, hcomm z hz b' hb', mul_assoc]
  have hCC : ⁅C, C⁆ = G₂ := by
    refine le_antisymm (commutator_le.2 fun c hc d hd => ?_) ?_
    · obtain ⟨z, hz, hzc, b, hb, rfl⟩ := hdec c hc
      obtain ⟨w, hw, hwc, b', hb', rfl⟩ := hdec d hd
      have hzb' : z * b' = b' * z := hzc b' (mem_sup_right hb')
      have hzw : z * w = w * z := hzc w (mem_sup_left hw)
      have hwb : w * b = b * w := hwc b (mem_sup_right hb)
      have e : ⁅z * b, w * b'⁆ = ⁅b, b'⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        have h1 : z * b * (w * b') * (z * b)⁻¹ * (w * b')⁻¹ =
            z * (b * w) * b' * b⁻¹ * z⁻¹ * b'⁻¹ * w⁻¹ := by group
        rw [h1, ← hwb, show z * (w * b) * b' * b⁻¹ * z⁻¹ * b'⁻¹ * w⁻¹ =
            (z * w) * (b * b' * b⁻¹) * z⁻¹ * b'⁻¹ * w⁻¹ by group, hzw]
        have hzb : z * b = b * z := hzc b (mem_sup_right hb)
        have hzbi : z * (b * b' * b⁻¹) = (b * b' * b⁻¹) * z := hzc _
          (mem_sup_right (mul_mem (mul_mem hb hb') (inv_mem hb)))
        rw [mul_assoc w z, hzbi, show w * (b * b' * b⁻¹ * z) * z⁻¹ * b'⁻¹ * w⁻¹ =
            w * (b * b' * b⁻¹ * b'⁻¹) * w⁻¹ by group]
        have hwc' : w * (b * b' * b⁻¹ * b'⁻¹) = (b * b' * b⁻¹ * b'⁻¹) * w := hwc _
          (mem_sup_right (mul_mem (mul_mem (mul_mem hb hb') (inv_mem hb)) (inv_mem hb')))
        rw [hwc', mul_inv_cancel_right]
      rw [e]
      exact hperf ▸ commutator_mem_commutator hb hb'
    · calc G₂ = ⁅G₂, G₂⁆ := hperf.symm
        _ ≤ ⁅C, C⁆ := commutator_mono hG₂C hG₂C
  have hyC : ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
    intro c hc
    refine ⟨(mem_normalizer_iff.1 hy c).1 hc.1, mem_centralizer_iff.2 fun a ha => ?_⟩
    have ha' : y⁻¹ * a * y ∈ G₁ := by
      have := (mem_normalizer_iff.1 (inv_mem hy₁) a).1 ha
      rwa [inv_inv] at this
    have := mem_centralizer_iff.1 hc.2 _ ha'
    calc a * (y * c * y⁻¹) = y * ((y⁻¹ * a * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * a * y)) * y⁻¹ := by rw [this]
      _ = y * c * y⁻¹ * a := by group
  have hyCn : y ∈ normalizer (C : Set G) := mem_normalizer_fintype hyC
  rw [← hCC]
  rw [mem_normalizer_iff_map_conj_eq] at hyCn ⊢
  rw [map_commutator, hyCn]

end Cover

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem false_of_conj_mem_normalizer_two_covers (hS : Setting h L η t Q T) {G₁ G₂ : Subgroup G}
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (ψ₁ : G₁ ⧸ center G₁ ≃* gramSU h (miyamotoJ4 K))
    (ψ₂ : G₂ ⧸ center G₂ ≃* gramSU h (miyamotoJ4 K))
    (hZ₁ : Odd (Nat.card (center G₁))) (hZ₂ : Odd (Nat.card (center G₂))) (g : G)
    (hg₁ : g * t * g⁻¹ ∈ normalizer (G₁ : Set G)) (hg₂ : g * t * g⁻¹ ∈ normalizer (G₂ : Set G)) :
    False := by
  have hx2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, hS.t_mul_t, mul_one,
      mul_inv_cancel]
  obtain ⟨E, -, hEx, hEe, hEc⟩ :=
    exists_elementaryAbelian_le_centralizer_of_two_covers h hcomm ψ₁ ψ₂ hZ₁ hZ₂ hx2 hg₁ hg₂
  set E' : Subgroup G := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hE'C : E' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    have hex := mem_centralizer_singleton_iff.1 (hEx he)
    rw [mem_centralizer_singleton_iff]
    change g⁻¹ * e * g⁻¹⁻¹ * t = t * (g⁻¹ * e * g⁻¹⁻¹)
    rw [inv_inv]
    calc g⁻¹ * e * g * t = g⁻¹ * (e * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * e) * g := by rw [hex]
      _ = t * (g⁻¹ * e * g) := by group
  have hE'e : CFSG.IsElementaryAbelian 2 E' := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.IsElementaryAbelian.map _
  have hle := hS.card_le_of_le_centralizer hE'C hE'e
  rw [hE', card_map_of_injective (MulAut.conj g⁻¹).injective, hEc] at hle
  have h4 : 4 ≤ 2 ^ f := hS.four_le
  have : 2 * (2 ^ f) ^ 4 < (2 ^ f) ^ 6 := by
    have h16 : 2 < (2 ^ f) ^ 2 := by nlinarith
    have hpos : 0 < (2 ^ f) ^ 4 := by positivity
    calc 2 * (2 ^ f) ^ 4 < (2 ^ f) ^ 2 * (2 ^ f) ^ 4 := by
          exact Nat.mul_lt_mul_of_pos_right h16 hpos
      _ = (2 ^ f) ^ 6 := by ring
  omega

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
