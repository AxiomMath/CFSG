module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Facts

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T : Subgroup G}

theorem u3Facts (h : Sec3 G L T)
    (hF : Foundation) {f : ℕ} (hf : 2 ≤ f) (e : rankTwoQuot L ≃* PSU3 2 f) :
    Nat.card (gmsW L T) = (2 ^ f) ^ 3 * Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) ∧
    Nat.card (gmsV L T) = 2 ^ f * Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) ∧
    IsElemAbelian 2 (gmsV L T) ∧ gmsV L T ≤ gmsW L T ∧
    gmsV L T ≤ centralizer (gmsW L T : Set G) ∧
    (∀ x ∈ gmsW L T, x ^ 2 = 1 → x ∈ gmsV L T) ∧
    (∀ w ∈ T, (∀ x ∈ T ⊓ L, w * x = x * w → x ∈ gmsA L T) →
      ∀ x ∈ gmsW L T, w * x = x * w → x ∈ gmsV L T) ∧
    Nat.card T ≤ (2 ^ f - 1) * (2 * Nat.card (gmsW L T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (L : Set G) with hKdef
  set T₁ := T ⊓ L with hT₁def
  set T₀ := T ⊓ K with hT₀def
  set W := T₁ ⊔ T₀ with hWdef
  set A₁ := T₁ ⊓ centralizer (T₁ : Set G) with hA₁def
  set V := A₁ ⊔ T₀ with hVdef
  have hLp : commutator L = ⊤ := h.hyp.standard.1.1
  have hZ := odd_card_center_of_psu3 hLp hf e
  have hT₁syl : IsSylowOf 2 T₁ L := h.isSylowOf_T₁
  obtain ⟨hT₁card, hA₁card, hA₁sq, hinvA, -, -⟩ := sylow_of_psu3 hZ hf e hT₁syl
  have hTcard : Nat.card T ≤
      (2 ^ f - 1) * Nat.card (T ⊓ centralizer (A₁ : Set G) : Subgroup G) :=
    card_le_of_psu3 hZ hf e hT₁syl h.sylow.isPGroup h.sylow.le fun x hx p hp =>
      (mem_normalizer_iff.mp (h.mem_normalizer_T₁ hx) p).mp hp
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
  have hW_LK : ∀ x ∈ T, x ∈ L ⊔ K → x ∈ W := fun x hx hLK => by
    rw [hWdef, ← h.inf_sup_eq]
    exact mem_inf.mpr ⟨hx, hLK⟩
  have hWcard : Nat.card W = (2 ^ f) ^ 3 * Nat.card T₀ := by
    have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hT₁N
    rw [show T₀ ⊓ T₁ = ⊥ by rw [inf_comm]; exact hinf, card_bot, mul_one, sup_comm,
      hT₁card] at h1
    rw [hWdef, h1, mul_comm]
  have hA₁N : A₁ ≤ normalizer (T₀ : Set G) := hA₁T₁.trans hT₁N
  have hVcard : Nat.card V = 2 ^ f * Nat.card T₀ := by
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
    have hT₀T₀ : T₀ ≤ centralizer (T₀ : Set G) :=
      le_centralizer_iff_isMulCommutative.mpr hT₀el.1
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
  exact ⟨hWcard, hVcard, hVel, hVW, hVC, hΩ, hCW,
    hTcard.trans (Nat.mul_le_mul_left _ hEcard)⟩

theorem map_eq_of_map_le_of_psu3
    (h : Sec3 G L T) (hF : Foundation) {f : ℕ} (hf : 2 ≤ f) (e : rankTwoQuot L ≃* PSU3 2 f)
    {z : G} (hz : (gmsW L T).map (MulAut.conj z).toMonoidHom ≤ T) :
    (gmsV L T).map (MulAut.conj z).toMonoidHom = gmsV L T := by
  obtain ⟨hWcard, hVcard, hVel, hVW, hVC, hΩ, hCW, hTcard⟩ := h.u3Facts hF hf e
  have hLp : commutator L = ⊤ := h.hyp.standard.1.1
  have hZ := odd_card_center_of_psu3 hLp hf e
  set c := (MulAut.conj z).toMonoidHom with hc
  have hcard : ∀ X : Subgroup G, Nat.card (X.map c) = Nat.card X := fun X =>
    card_map_of_injective (MulAut.conj z).injective
  have hWT : gmsW L T ≤ T := sup_le inf_le_left inf_le_left
  by_contra hne
  have hnle : ¬ (gmsV L T).map c ≤ gmsV L T := fun hle =>
    hne (eq_of_le_of_card_ge hle (by rw [hcard]))
  obtain ⟨w, hwV', hwV⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hwT : w ∈ T := hz (map_mono hVW hwV')
  have hww : w * w = 1 := by rw [← sq]; exact (isElemAbelian_map c hVel).2 w hwV'
  have hwW : w ∉ gmsW L T := fun hwW => hwV (hΩ w hwW (by rw [sq]; exact hww))
  have hwLK : w ∉ L ⊔ centralizer (L : Set G) := fun hLK => hwW (by
    rw [gmsW, ← h.inf_sup_eq]
    exact mem_inf.mpr ⟨hwT, hLK⟩)
  obtain ⟨-, hfixw⟩ := outer_inv_of_psu3 hLp hZ hf e h.isSylowOf_T₁ (h.sylow.le hwT) hww hwLK
    (fun p hp => (mem_normalizer_iff.mp (h.mem_normalizer_T₁ hwT) p).mp hp)
  have hwC : ∀ x ∈ (gmsW L T).map c, x * w = w * x := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hwV'
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : x * v = v * x := mem_centralizer_iff.mp (hVC hv) x hx
    calc z * x * z⁻¹ * (z * v * z⁻¹) = z * (x * v) * z⁻¹ := by group
      _ = z * (v * x) * z⁻¹ := by rw [h1]
      _ = z * v * z⁻¹ * (z * x * z⁻¹) := by group
  have hQW : (gmsW L T).map c ⊓ gmsW L T ≤ gmsV L T := fun x hx =>
    hCW w hwT hfixw x (mem_inf.mp hx).2 (hwC x (mem_inf.mp hx).1).symm
  have hidx := card_mul_card_le hz hWT
  rw [hcard, hWcard] at hidx
  have h3 := (card_le_of_le hQW).trans hVcard.le
  have hT₀pos : 0 < Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) := Nat.card_pos
  have hq4 := four_le_two_pow hf
  set q := 2 ^ f with hq
  set t := Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) with ht
  rw [hWcard] at hTcard
  obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rw [hr, Nat.add_sub_cancel] at hTcard
  rw [hr] at hidx h3
  have h4 : (r + 1) ^ 3 * t * ((r + 1) ^ 3 * t) ≤
      r * (2 * ((r + 1) ^ 3 * t)) * ((r + 1) * t) :=
    hidx.trans (Nat.mul_le_mul hTcard h3)
  have hpos : 0 < (r + 1) ^ 3 * t := by positivity
  have h5 : (r + 1) ^ 3 * t ≤ 2 * r * ((r + 1) * t) := by
    have : (r + 1) ^ 3 * t * ((r + 1) ^ 3 * t) ≤
        2 * r * ((r + 1) * t) * ((r + 1) ^ 3 * t) := by
      calc _ ≤ r * (2 * ((r + 1) ^ 3 * t)) * ((r + 1) * t) := h4
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have h6 : (r + 1) ^ 2 ≤ 2 * r := by
    have hpos' : 0 < (r + 1) * t := by positivity
    have : (r + 1) ^ 2 * ((r + 1) * t) ≤ 2 * r * ((r + 1) * t) := by
      calc _ = (r + 1) ^ 3 * t := by ring
        _ ≤ _ := h5
    exact Nat.le_of_mul_le_mul_right this hpos'
  nlinarith

theorem rightConjugate_eq_of_psu3
    (h : Sec3 G L T) (hF : Foundation) {f : ℕ} (hf : 2 ≤ f) (e : rankTwoQuot L ≃* PSU3 2 f)
    {z : G} (hz : rightConjugate (gmsW L T) z ≤ T) : rightConjugate (gmsV L T) z = gmsV L T :=
  h.map_eq_of_map_le_of_psu3 hF hf e hz

theorem facts_of_psu3
    (h : Sec3 G L T) (hF : Foundation) {f : ℕ} (hf : 2 ≤ f) (e : rankTwoQuot L ≃* PSU3 2 f) :
    Facts L T (2 ^ f) where
  four_le := four_le_two_pow hf
  oddCenter := odd_card_center_of_psu3 h.hyp.standard.1.1 hf e
  borel := ⟨3, Asc76X.fusionBenderBorel_of_mulEquiv_psu3 hf e⟩
  sq_mem := (sylow_of_psu3 (odd_card_center_of_psu3 h.hyp.standard.1.1 hf e) hf e
    h.isSylowOf_T₁).2.2.2.2.1
  weakClosure := fun _ hz => h.rightConjugate_eq_of_psu3 hF hf e hz

end Sec3

end CFSG.ComponentClassification.GMS78
