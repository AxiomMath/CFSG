module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma310
public import CFSG.LocalAnalysis.ComponentClassification.GMS78UnitaryLocal

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_le_card_centralizer_mul_card_commutator {H : Type*} [Group H] [Finite H] (x : H) :
    Nat.card H ≤ Nat.card (centralizer ({x} : Set H)) * Nat.card (commutator H) := by
  classical
  set C := centralizer ({x} : Set H) with hC
  have hmemC : ∀ c, c ∈ C ↔ c * x = x * c := fun c => mem_centralizer_singleton_iff
  have hmem : ∀ h : H, h * x * h⁻¹ * x⁻¹ ∈ commutator H := fun h => by
    rw [_root_.commutator_def, ← commutatorElement_def]
    exact commutator_mem_commutator (mem_top h) (mem_top x)
  have hwd : ∀ a b : H, a⁻¹ * b ∈ C → a * x * a⁻¹ = b * x * b⁻¹ := by
    intro a b hab
    rw [hmemC] at hab
    calc a * x * a⁻¹ = a * (x * (a⁻¹ * b)) * b⁻¹ := by group
      _ = a * ((a⁻¹ * b) * x) * b⁻¹ := by rw [hab]
      _ = b * x * b⁻¹ := by group
  let φ : H ⧸ C → commutator H := Quotient.lift (fun h => (⟨_, hmem h⟩ : commutator H))
    (fun a b hab => Subtype.ext (by
      show a * x * a⁻¹ * x⁻¹ = b * x * b⁻¹ * x⁻¹
      rw [hwd a b (QuotientGroup.leftRel_apply.mp hab)]))
  have hφ : Function.Injective φ := by
    intro u v huv
    induction u using QuotientGroup.induction_on with | H a => ?_
    induction v using QuotientGroup.induction_on with | H b => ?_
    apply QuotientGroup.eq.mpr
    have h1 : a * x * a⁻¹ * x⁻¹ = b * x * b⁻¹ * x⁻¹ := congrArg Subtype.val huv
    have h2 : a * x * a⁻¹ = b * x * b⁻¹ := mul_right_cancel h1
    rw [hmemC]
    calc a⁻¹ * b * x = a⁻¹ * (b * x * b⁻¹) * b := by group
      _ = a⁻¹ * (a * x * a⁻¹) * b := by rw [h2]
      _ = x * (a⁻¹ * b) := by group
  calc Nat.card H = Nat.card (H ⧸ C) * Nat.card C := C.card_eq_card_quotient_mul_card_subgroup
    _ ≤ Nat.card (commutator H) * Nat.card C :=
        Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective φ hφ)
    _ = _ := mul_comm _ _

omit [Finite G] in
theorem card_le_inf_centralizer_mul_card_commutator {W : Subgroup G} [Finite W] {u : G}
    (hu : u ∈ W) :
    Nat.card W ≤
      Nat.card (W ⊓ centralizer ({u} : Set G) : Subgroup G) * Nat.card (commutator W) := by
  have h := card_le_card_centralizer_mul_card_commutator (⟨u, hu⟩ : W)
  have hc : Nat.card (centralizer ({(⟨u, hu⟩ : W)} : Set W)) =
      Nat.card (W ⊓ centralizer ({u} : Set G) : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨c.1, c.1.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.2))⟩
        invFun := fun d => ⟨⟨d.1, d.2.1⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp d.2.2))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rwa [hc] at h

theorem card_le_two_mul_of_mul_mem {E H : Subgroup G}
    (h : ∀ x₁ ∈ E, ∀ x₂ ∈ E, x₁ ∉ H → x₂ ∉ H → x₁ * x₂ ∈ H) :
    Nat.card E ≤ 2 * Nat.card H := by
  classical
  by_cases hEH : E ≤ H
  · have := card_le_of_le hEH
    omega
  obtain ⟨x₁, hx₁E, hx₁H⟩ := IsConcreteLE.not_le_iff_exists.mp hEH
  let Φ : E → Bool × H := fun x =>
    if hx : (x : G) ∈ H then (true, ⟨x, hx⟩) else (false, ⟨x₁ * x, h x₁ hx₁E x x.2 hx₁H hx⟩)
  have hΦ : Function.Injective Φ := by
    intro x x' hxx'
    by_cases hx : (x : G) ∈ H <;> by_cases hx' : (x' : G) ∈ H <;>
      simp only [Φ, hx, hx', dite_true, dite_false, Prod.mk.injEq] at hxx'
    · have h2 := congrArg Subtype.val hxx'.2
      exact Subtype.ext h2
    · exact absurd hxx'.1 (by decide)
    · exact absurd hxx'.1 (by decide)
    · have h2 := congrArg Subtype.val hxx'.2
      exact Subtype.ext (mul_left_cancel h2)
  have h1 := Nat.card_le_card_of_injective Φ hΦ
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1

omit [Finite G] in
theorem le_normalizer_of_conj_mem {T X : Subgroup G} (h : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) :
    T ≤ normalizer (X : Set G) := fun t ht => mem_normalizer_iff.mpr fun x =>
  ⟨h t ht x, fun hx => by simpa [mul_assoc] using h t⁻¹ (inv_mem ht) _ hx⟩

namespace Sec3

variable {L T : Subgroup G}

theorem inf_eq_bot_of_odd (h : Sec3 G L T) (hZ : Odd (Nat.card (center L))) :
    (T ⊓ L) ⊓ (T ⊓ centralizer (L : Set G)) = ⊥ := by
  have hM : Odd (Nat.card ((center L).map L.subtype)) := by
    rwa [card_map_of_injective L.subtype_injective]
  refine two_subgroup_of_odd_eq_bot _ _ (h.sylow.isPGroup.to_le (inf_le_left.trans inf_le_left))
    hM ?_
  intro x hx
  have hxL : x ∈ L := (mem_inf.mp (mem_inf.mp hx).1).2
  have hxK : x ∈ centralizer (L : Set G) := (mem_inf.mp (mem_inf.mp hx).2).2
  refine ⟨⟨x, hxL⟩, ?_, rfl⟩
  show (⟨x, hxL⟩ : L) ∈ center L
  rw [mem_center_iff]
  intro z
  exact Subtype.ext (mem_centralizer_iff.mp hxK z z.2)

theorem conj_mem_T₀ (h : Sec3 G L T) {x : G} (hx : x ∈ T) {t : G}
    (ht : t ∈ T ⊓ centralizer (L : Set G)) : x * t * x⁻¹ ∈ T ⊓ centralizer (L : Set G) :=
  mem_inf.mpr ⟨mul_mem (mul_mem hx (mem_inf.mp ht).1) (inv_mem hx),
    (mem_normalizer_iff.mp (h.normalizer_le_normalizer_centralizer (h.sylow.le hx)) t).mp
      (mem_inf.mp ht).2⟩

theorem normalizer_le_of_psu3
    (h : Sec3 G L T) (hF : Foundation) {f : ℕ} (hf : 2 ≤ f) (e : rankTwoQuot L ≃* PSU3 2 f) :
    normalizer (T : Set G) ≤
      normalizer (((T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) := by
  intro y hy
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (L : Set G) with hKdef
  set T₁ := T ⊓ L with hT₁def
  set T₀ := T ⊓ K with hT₀def
  set W := T₁ ⊔ T₀ with hWdef
  set A₁ := T₁ ⊓ centralizer (T₁ : Set G) with hA₁def
  set V := A₁ ⊔ T₀ with hVdef
  have hq4 := four_le_two_pow hf
  have hLp : commutator L = ⊤ := h.hyp.standard.1.1
  have hZ := odd_card_center_of_psu3 hLp hf e
  have hT₁syl : IsSylowOf 2 T₁ L := h.isSylowOf_T₁
  obtain ⟨hT₁card, hA₁card, hA₁sq, hinvA, hsqA, hcomm⟩ := sylow_of_psu3 hZ hf e hT₁syl
  have hTcard : Nat.card T ≤
      (2 ^ f - 1) * Nat.card (T ⊓ centralizer (A₁ : Set G) : Subgroup G) :=
    card_le_of_psu3 hZ hf e hT₁syl h.sylow.isPGroup h.sylow.le fun x hx p hp =>
      (mem_normalizer_iff.mp (h.mem_normalizer_T₁ hx) p).mp hp
  set q := 2 ^ f with hqdef
  have hT₀el : IsElemAbelian 2 T₀ := h.isElemAbelian_T₀ hF
  have hinf : T₁ ⊓ T₀ = ⊥ := h.inf_eq_bot_of_odd hZ
  have hT₂ : IsPGroup 2 T := h.sylow.isPGroup
  have hTM : T ≤ normalizer (L : Set G) := h.sylow.le
  have hT₀C : T₀ ≤ centralizer (T₁ : Set G) := fun t ht => mem_centralizer_iff.mpr fun x hx =>
    mem_centralizer_iff.mp (mem_inf.mp ht).2 x (mem_inf.mp hx).2
  have hT₁N : T₁ ≤ normalizer (T₀ : Set G) :=
    (le_centralizer_iff.mp hT₀C).trans (Subgroup.centralizer_le_normalizer _)
  have hA₁T₁ : A₁ ≤ T₁ := inf_le_left
  have hT₁CA : T₁ ≤ centralizer (A₁ : Set G) := fun t ht => mem_centralizer_iff.mpr fun a ha =>
    (mem_centralizer_iff.mp (mem_inf.mp ha).2 t ht).symm
  have hT₀CA : T₀ ≤ centralizer (A₁ : Set G) := fun t ht => mem_centralizer_iff.mpr fun a ha =>
    mem_centralizer_iff.mp (hT₀C ht) a (hA₁T₁ ha)
  have hcT₁ : ∀ x ∈ T, ∀ p ∈ T₁, x * p * x⁻¹ ∈ T₁ := fun x hx p hp =>
    (mem_normalizer_iff.mp (h.mem_normalizer_T₁ hx) p).mp hp
  have hcT₀ : ∀ x ∈ T, ∀ p ∈ T₀, x * p * x⁻¹ ∈ T₀ := fun x hx p hp => h.conj_mem_T₀ hx hp
  have hdec : ∀ x ∈ W, ∃ x₁ ∈ T₁, ∃ x₀ ∈ T₀, x₁ * x₀ = x := fun x hx =>
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hT₁N hx
  have hcW : ∀ x ∈ T, ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
    intro x hx w hw
    obtain ⟨w₁, hw₁, w₀, hw₀, rfl⟩ := hdec w hw
    rw [show x * (w₁ * w₀) * x⁻¹ = (x * w₁ * x⁻¹) * (x * w₀ * x⁻¹) by group]
    exact mul_mem (mem_sup_left (hcT₁ x hx w₁ hw₁)) (mem_sup_right (hcT₀ x hx w₀ hw₀))
  have hWT : W ≤ T := sup_le inf_le_left inf_le_left
  have hWN : T ≤ normalizer (W : Set G) := le_normalizer_of_conj_mem hcW
  have hW_LK : ∀ x ∈ T, x ∈ L ⊔ K → x ∈ W := fun x hx hLK => by
    rw [hWdef, ← h.inf_sup_eq]
    exact mem_inf.mpr ⟨hx, hLK⟩
  have hT₀pos : 0 < Nat.card T₀ := Nat.card_pos
  have hWcard : Nat.card W = q ^ 3 * Nat.card T₀ := by
    have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hT₁N
    rw [show T₀ ⊓ T₁ = ⊥ by rw [inf_comm]; exact hinf, card_bot, mul_one, sup_comm,
      hT₁card] at h1
    rw [hWdef, h1, mul_comm]
  have hA₁N : A₁ ≤ normalizer (T₀ : Set G) := hA₁T₁.trans hT₁N
  have hVcard : Nat.card V = q * Nat.card T₀ := by
    have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hA₁N
    have hbot : T₀ ⊓ A₁ = ⊥ := le_bot_iff.mp (fun x hx => by
      rw [← hinf]
      exact mem_inf.mpr ⟨hA₁T₁ (mem_inf.mp hx).2, (mem_inf.mp hx).1⟩)
    rw [hbot, card_bot, mul_one, sup_comm, hA₁card] at h1
    rw [hVdef, h1, mul_comm]
  have hA₁el : IsElemAbelian 2 A₁ := ⟨⟨⟨fun a b => Subtype.ext
    (show (a : G) * b = b * a from mem_centralizer_iff.mp (mem_inf.mp b.2).2 a (hA₁T₁ a.2))⟩⟩,
    hA₁sq⟩
  have hVel : IsElemAbelian 2 V := isElemAbelian_sup hA₁el hT₀el hT₀CA
  have hVW : V ≤ W := sup_le (hA₁T₁.trans le_sup_left) le_sup_right
  have hVC : V ≤ centralizer (W : Set G) := by
    have hT₀T₀ : T₀ ≤ centralizer (T₀ : Set G) := le_centralizer_iff_isMulCommutative.mpr hT₀el.1
    have hWV : W ≤ centralizer (V : Set G) := sup_le
      (le_centralizer_iff.mp (sup_le inf_le_right hT₀C))
      (le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hT₀CA) hT₀T₀))
    exact le_centralizer_iff.mp hWV
  have hΩ : ∀ x ∈ W, x ^ 2 = 1 → x ∈ V := by
    intro x hx hx2
    obtain ⟨x₁, hx₁, x₀, hx₀, rfl⟩ := hdec x hx
    have hc : x₁ * x₀ = x₀ * x₁ := mem_centralizer_iff.mp (hT₀C hx₀) x₁ hx₁
    have hx₁2 : x₁ ^ 2 = 1 := by
      rw [Commute.mul_pow hc 2, hT₀el.2 x₀ hx₀, mul_one] at hx2
      exact hx2
    exact mul_mem (mem_sup_left (hinvA x₁ hx₁ hx₁2)) (mem_sup_right hx₀)
  have hCW : ∀ w ∈ T, (∀ x ∈ T₁, w * x = x * w → x ∈ A₁) →
      ∀ x ∈ W, w * x = x * w → x ∈ V := by
    intro w hw hfix x hx hwx
    obtain ⟨x₁, hx₁, x₀, hx₀, rfl⟩ := hdec x hx
    have h1 : w * x₁ * w⁻¹ ∈ T₁ := hcT₁ w hw x₁ hx₁
    have h0 : w * x₀ * w⁻¹ ∈ T₀ := hcT₀ w hw x₀ hx₀
    have h2 : (w * x₁ * w⁻¹) * (w * x₀ * w⁻¹) = x₁ * x₀ := by
      calc (w * x₁ * w⁻¹) * (w * x₀ * w⁻¹) = w * (x₁ * x₀) * w⁻¹ := by group
        _ = x₁ * x₀ := by rw [hwx, mul_inv_cancel_right]
    have h3 : x₁⁻¹ * (w * x₁ * w⁻¹) ∈ T₁ ⊓ T₀ := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem hx₁) h1, ?_⟩
      have h4 : x₁⁻¹ * (w * x₁ * w⁻¹) = x₀ * (w * x₀ * w⁻¹)⁻¹ := by
        calc x₁⁻¹ * (w * x₁ * w⁻¹)
            = x₁⁻¹ * ((w * x₁ * w⁻¹) * (w * x₀ * w⁻¹)) * (w * x₀ * w⁻¹)⁻¹ := by group
          _ = x₁⁻¹ * (x₁ * x₀) * (w * x₀ * w⁻¹)⁻¹ := by rw [h2]
          _ = x₀ * (w * x₀ * w⁻¹)⁻¹ := by group
      rw [h4]
      exact mul_mem hx₀ (inv_mem h0)
    rw [hinf, mem_bot] at h3
    have h5 : w * x₁ * w⁻¹ = x₁ := by
      calc w * x₁ * w⁻¹ = x₁ * (x₁⁻¹ * (w * x₁ * w⁻¹)) := by group
        _ = x₁ := by rw [h3, mul_one]
    have h6 : w * x₁ = x₁ * w := by
      calc w * x₁ = w * x₁ * w⁻¹ * w := by group
        _ = x₁ * w := by rw [h5]
    exact mul_mem (mem_sup_left (hfix x₁ hx₁ h6)) (mem_sup_right hx₀)
  set E := T ⊓ centralizer (A₁ : Set G) with hEdef
  have hEcard : Nat.card E ≤ 2 * Nat.card W := by
    have hpair : ∀ x₁ ∈ E, ∀ x₂ ∈ E, x₁ ∉ E ⊓ W → x₂ ∉ E ⊓ W → x₁ * x₂ ∈ E ⊓ W := by
      intro x₁ h₁ x₂ h₂ h₁W h₂W
      have h₁LK : x₁ ∉ L ⊔ K := fun hLK =>
        h₁W (mem_inf.mpr ⟨h₁, hW_LK x₁ (mem_inf.mp h₁).1 hLK⟩)
      have h₂LK : x₂ ∉ L ⊔ K := fun hLK =>
        h₂W (mem_inf.mpr ⟨h₂, hW_LK x₂ (mem_inf.mp h₂).1 hLK⟩)
      have hm := mul_mem_sup_of_psu3 hLp hZ hf e hT₁syl (hT₂.to_le inf_le_left)
        (inf_le_left.trans hTM) (fun x hx => hcT₁ x (mem_inf.mp hx).1)
        (fun x hx a ha => (mem_centralizer_iff.mp (mem_inf.mp hx).2 a ha).symm)
        (le_inf inf_le_left hT₁CA) h₁ h₂ h₁LK h₂LK
      exact mem_inf.mpr ⟨mul_mem h₁ h₂,
        hW_LK _ (mul_mem (mem_inf.mp h₁).1 (mem_inf.mp h₂).1) hm⟩
    exact (card_le_two_mul_of_mul_mem hpair).trans
      (Nat.mul_le_mul_left 2 (card_le_of_le inf_le_right))
  set c := (MulAut.conj y).toMonoidHom with hc
  have hcy : ∀ x ∈ T, y * x * y⁻¹ ∈ T := fun x hx => (mem_normalizer_iff.mp hy x).mp hx
  have hcyi : ∀ x ∈ T, y⁻¹ * x * y ∈ T := fun x hx => by
    simpa using (mem_normalizer_iff.mp (inv_mem hy) x).mp hx
  have hmapT : ∀ {X : Subgroup G}, X ≤ T → X.map c ≤ T := by
    intro X hX
    rintro _ ⟨x, hx, rfl⟩
    exact hcy x (hX hx)
  have hcard : ∀ X : Subgroup G, Nat.card (X.map c) = Nat.card X := fun X =>
    card_map_of_injective (MulAut.conj y).injective
  set Q := W.map c with hQdef
  have hQT : Q ≤ T := hmapT hWT
  have hQN : T ≤ normalizer (Q : Set G) := by
    apply le_normalizer_of_conj_mem
    rintro t ht _ ⟨w, hw, rfl⟩
    refine ⟨(y⁻¹ * t * y) * w * (y⁻¹ * t * y)⁻¹, hcW _ (hcyi t ht) w hw, ?_⟩
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hV'el : IsElemAbelian 2 (V.map c) := isElemAbelian_map c hVel
  have hV'C : V.map c ≤ centralizer (Q : Set G) := by
    rintro _ ⟨v, hv, rfl⟩
    refine mem_centralizer_iff.mpr ?_
    rintro _ ⟨w, hw, rfl⟩
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : w * v = v * w := mem_centralizer_iff.mp (hVC hv) w hw
    calc y * w * y⁻¹ * (y * v * y⁻¹) = y * (w * v) * y⁻¹ := by group
      _ = y * (v * w) * y⁻¹ := by rw [h1]
      _ = y * v * y⁻¹ * (y * w * y⁻¹) := by group
  have hQWcard := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer (hWT.trans hQN)
  rw [hcard] at hQWcard
  have hVV : V.map c = V := by
    by_contra hne
    have hnle : ¬ V.map c ≤ V := fun hle => hne (eq_of_le_of_card_ge hle (by rw [hcard]))
    obtain ⟨w, hwV', hwV⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    have hwT : w ∈ T := hmapT (hVW.trans hWT) hwV'
    have hww : w * w = 1 := by rw [← sq]; exact hV'el.2 w hwV'
    have hwW : w ∉ W := fun hwW => hwV (hΩ w hwW (by rw [sq]; exact hww))
    have hwLK : w ∉ L ⊔ K := fun hLK => hwW (hW_LK w hwT hLK)
    obtain ⟨-, hfixw⟩ :=
      outer_inv_of_psu3 hLp hZ hf e hT₁syl (hTM hwT) hww hwLK (hcT₁ w hwT)
    have hQW : Q ⊓ W ≤ V := fun x hx => hCW w hwT hfixw x (mem_inf.mp hx).2
      (mem_centralizer_iff.mp (hV'C hwV') x (mem_inf.mp hx).1).symm
    have h2 : Nat.card (Q ⊔ W : Subgroup G) ≤ Nat.card T := card_le_of_le (sup_le hQT hWT)
    have h3 : Nat.card (Q ⊓ W : Subgroup G) ≤ Nat.card V := card_le_of_le hQW
    obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    rw [hr, Nat.add_sub_cancel] at hTcard
    rw [hVcard] at h3
    rw [hWcard] at hQWcard hEcard
    rw [hr] at hQWcard h3 hEcard
    have h4 : (r + 1) ^ 3 * Nat.card T₀ * ((r + 1) ^ 3 * Nat.card T₀) ≤
        r * (2 * ((r + 1) ^ 3 * Nat.card T₀)) * ((r + 1) * Nat.card T₀) := by
      rw [← hQWcard]
      exact Nat.mul_le_mul (h2.trans (hTcard.trans (Nat.mul_le_mul_left r hEcard))) h3
    have hpos : 0 < (r + 1) ^ 3 * Nat.card T₀ := by positivity
    have h5 : (r + 1) ^ 3 * Nat.card T₀ ≤ 2 * r * ((r + 1) * Nat.card T₀) := by
      have : (r + 1) ^ 3 * Nat.card T₀ * ((r + 1) ^ 3 * Nat.card T₀) ≤
          2 * r * ((r + 1) * Nat.card T₀) * ((r + 1) ^ 3 * Nat.card T₀) := by
        calc _ ≤ r * (2 * ((r + 1) ^ 3 * Nat.card T₀)) * ((r + 1) * Nat.card T₀) := h4
          _ = _ := by ring
      exact Nat.le_of_mul_le_mul_right this hpos
    have h6 : (r + 1) ^ 2 ≤ 2 * r := by
      have hpos' : 0 < (r + 1) * Nat.card T₀ := by positivity
      have : (r + 1) ^ 2 * ((r + 1) * Nat.card T₀) ≤ 2 * r * ((r + 1) * Nat.card T₀) := by
        calc _ = (r + 1) ^ 3 * Nat.card T₀ := by ring
          _ ≤ _ := h5
      exact Nat.le_of_mul_le_mul_right this hpos'
    nlinarith
  have hQE : Q ≤ E := le_inf hQT fun x hx => mem_centralizer_iff.mpr fun a ha =>
    (mem_centralizer_iff.mp (hV'C (by rw [hVV]; exact mem_sup_left ha)) x hx).symm
  have hWE : W ≤ E := le_inf hWT (sup_le hT₁CA hT₀CA)
  have hidx : Nat.card Q ≤ 2 * Nat.card (Q ⊓ W : Subgroup G) := by
    have h1 : Nat.card (Q ⊔ W : Subgroup G) ≤ 2 * Nat.card W :=
      (card_le_of_le (sup_le hQE hWE)).trans hEcard
    have hWpos : 0 < Nat.card W := Nat.card_pos
    have h2 : Nat.card W * Nat.card W ≤ 2 * Nat.card W * Nat.card (Q ⊓ W : Subgroup G) := by
      rw [← hQWcard]
      exact Nat.mul_le_mul_right _ h1
    rw [hcard]
    have h3 : Nat.card W * Nat.card W ≤ 2 * Nat.card (Q ⊓ W : Subgroup G) * Nat.card W := by
      calc _ ≤ 2 * Nat.card W * Nat.card (Q ⊓ W : Subgroup G) := h2
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right h3 hWpos
  rw [mem_normalizer_iff_map_conj_eq]
  show Q = W
  by_contra hne
  have hnle : ¬ Q ≤ W := fun hle => hne (eq_of_le_of_card_ge hle (by rw [hcard]))
  obtain ⟨x, hxQ, hxW⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  obtain ⟨w, hwW, rfl⟩ := hxQ
  obtain ⟨w₁, hw₁, w₀, hw₀, rfl⟩ := hdec w hwW
  set u := y * w₁ * y⁻¹ with hudef
  have hu₀ : y * w₀ * y⁻¹ ∈ W := by
    have hmem : y * w₀ * y⁻¹ ∈ V.map c := ⟨w₀, mem_sup_right hw₀, rfl⟩
    rw [hVV] at hmem
    exact hVW hmem
  have hcxy : c (w₁ * w₀) = u * (y * w₀ * y⁻¹) := by
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hudef]
    group
  have huW : u ∉ W := fun huW => hxW (by rw [hcxy]; exact mul_mem huW hu₀)
  have huT₁' : u ∈ T₁.map c := ⟨w₁, hw₁, rfl⟩
  have huQ : u ∈ Q := ⟨w₁, mem_sup_left hw₁, rfl⟩
  have huT : u ∈ T := hQT huQ
  have huLK : u ∉ L ⊔ K := fun hLK => huW (hW_LK u huT hLK)
  have huA : ∀ a ∈ A₁, u * a = a * u := fun a ha =>
    (mem_centralizer_iff.mp (mem_inf.mp (hQE huQ)).2 a ha).symm
  have hu2 : ∃ a ∈ A₁, ∃ k ∈ K, u ^ 2 = a * k := by
    have h1 : u ^ 2 ∈ V := by
      rw [← hVV]
      refine ⟨w₁ ^ 2, mem_sup_left (hsqA w₁ hw₁), ?_⟩
      simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hudef]
      rw [sq, sq]
      group
    obtain ⟨a, ha, k, hk, hak⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hA₁N h1
    exact ⟨a, ha, k, (mem_inf.mp hk).2, hak.symm⟩
  obtain ⟨n, hn⟩ := hT₂ ⟨u, huT⟩
  have hun : u ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hfixu := centralizer_le_of_psu3 hLp hZ hf e hT₁syl (hTM huT) (hcT₁ u huT) hun huA huLK hu2
  have hCWu := hCW u huT hfixu
  set C₁ := T₁.map c ⊓ centralizer ({u} : Set G) with hC₁def
  have hC₁ := card_le_inf_centralizer_mul_card_commutator huT₁'
  have hcomm' : Nat.card (commutator (T₁.map c)) = q := by
    have h1 := card_commutator_congr (MulEquiv.subgroupMap (MulAut.conj y) T₁)
    rw [← hcomm]
    exact h1.symm
  rw [hcard, hT₁card, hcomm'] at hC₁
  have hT₀'C : T₀.map c ≤ centralizer (C₁ : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_centralizer_iff.mpr fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := (mem_inf.mp hx).1
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : p * t = t * p := mem_centralizer_iff.mp (hT₀C ht) p hp
    calc y * p * y⁻¹ * (y * t * y⁻¹) = y * (p * t) * y⁻¹ := by group
      _ = y * (t * p) * y⁻¹ := by rw [h1]
      _ = y * t * y⁻¹ * (y * p * y⁻¹) := by group
  have hC₁T₀ : C₁ ⊓ T₀.map c = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨⟨p, hp, rfl⟩, -⟩, ⟨t, ht, htp⟩⟩
    have hpt : p = t := (MulAut.conj y).injective htp.symm
    have h1 : p ∈ T₁ ⊓ T₀ := mem_inf.mpr ⟨hp, hpt ▸ ht⟩
    rw [hinf, mem_bot] at h1
    rw [mem_bot, h1, map_one]
  have hlow := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer
    (hT₀'C.trans (Subgroup.centralizer_le_normalizer _))
  rw [hC₁T₀, card_bot, mul_one, hcard] at hlow
  set D := Q ⊓ centralizer ({u} : Set G) with hDdef
  have hC₁D : C₁ ⊔ T₀.map c ≤ D := by
    refine sup_le (le_inf (inf_le_left.trans (map_mono le_sup_left)) inf_le_right) ?_
    refine le_inf (map_mono (le_sup_right.trans hVW)) ?_
    intro t ht
    have ht' : t ∈ V.map c := map_mono le_sup_right ht
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hV'C ht') u huQ).symm
  have hDN : D ≤ normalizer ((Q ⊓ W : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf (hQN (hQT (mem_inf.mp hx).1)) (hWN (hQT (mem_inf.mp hx).1))
  have hup := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hDN
  have hup1 : Nat.card ((Q ⊓ W) ⊔ D : Subgroup G) ≤ 2 * Nat.card (Q ⊓ W : Subgroup G) :=
    (card_le_of_le (sup_le inf_le_left inf_le_left)).trans hidx
  have hup2 : Nat.card ((Q ⊓ W) ⊓ D : Subgroup G) ≤ Nat.card V := by
    refine card_le_of_le fun x hx => hCWu x (mem_inf.mp (mem_inf.mp hx).1).2 ?_
    exact (mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp hx).2).2).symm
  have hQWpos : 0 < Nat.card (Q ⊓ W : Subgroup G) := Nat.card_pos
  have hD : Nat.card D ≤ 2 * Nat.card V := by
    have h1 : Nat.card (Q ⊓ W : Subgroup G) * Nat.card D ≤
        Nat.card (Q ⊓ W : Subgroup G) * (2 * Nat.card V) := by
      rw [← hup]
      calc _ ≤ 2 * Nat.card (Q ⊓ W : Subgroup G) * Nat.card V := Nat.mul_le_mul hup1 hup2
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left h1 hQWpos
  have hC₁D' := card_le_of_le hC₁D
  rw [hVcard] at hD
  have hqpos : 0 < q := by omega
  have h1 : Nat.card C₁ * Nat.card T₀ ≤ 2 * (q * Nat.card T₀) := by
    rw [← hlow]
    exact hC₁D'.trans hD
  have h2 : Nat.card C₁ ≤ 2 * q := by
    have : Nat.card C₁ * Nat.card T₀ ≤ 2 * q * Nat.card T₀ := by
      calc _ ≤ 2 * (q * Nat.card T₀) := h1
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this hT₀pos
  have h3 : q ^ 3 ≤ 2 * q * q := hC₁.trans (Nat.mul_le_mul_right q h2)
  nlinarith

theorem normalizer_le (h : Sec3 G L T)
    (hF : Foundation) :
    normalizer (T : Set G) ≤
      normalizer (((T ⊓ L) ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) := by
  rcases rankTwoBenderType_iff.mp h.hyp.bender with ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact h.normalizer_le_of_psl2 hF hm e
  · exact h.normalizer_le_of_psu3 hF hm e
  · exact h.normalizer_le_of_sz ha e

end Sec3

end CFSG.ComponentClassification.GMS78
