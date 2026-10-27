module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSOne
import CFSG.LocalAnalysis.SeitzReduction.Endgame

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem inf_le_of_not_mem_of_le {T₀ R₀ W₀ : Subgroup G} {t : G} (ht : t * t = 1)
    (htT₀ : t ∈ normalizer (T₀ : Set G)) (hT₀R₀ : T₀ ≤ R₀)
    (hCR₀ : centralizer (W₀ : Set G) ≤ R₀) (htR₀ : t ∉ R₀) :
    centralizer (W₀ : Set G) ⊓ (T₀ ⊔ zpowers t) ≤ T₀ := by
  intro z hz
  obtain ⟨hzC, hzT⟩ := Subgroup.mem_inf.1 hz
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht htT₀ hzT with h | h
  · exact h
  · exfalso
    apply htR₀
    have h1 : z⁻¹ * (z * t) ∈ R₀ := mul_mem (inv_mem (hCR₀ hzC)) (hT₀R₀ h)
    rwa [show z⁻¹ * (z * t) = t by group] at h1

theorem false_of_field_gen {W V S S₀ F W₀ R₀ T₀ : Subgroup G} {t : G} {k m : ℕ}
    (hW : ∀ w ∈ W, w * w = 1) (hWV : Nat.card W = Nat.card V ^ 2) (ht : t * t = 1)
    (hWS : W ≤ S) (hSN : S ≤ normalizer (W : Set G)) (htS : t ∈ S)
    (htcomm : ∀ s ∈ S, t * s * t⁻¹ * s⁻¹ ∈ V)
    (hB : ∀ B : Subgroup G, B ≤ S → B ≤ centralizer (V : Set G) → (∀ b ∈ B, b * b = 1) →
      (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) → Nat.card B = Nat.card W → B = W)
    (hmax : ∀ P : Subgroup G, IsPGroup 2 P → S ≤ P → P ≤ normalizer (W : Set G) → P = S)
    (hS2 : IsPGroup 2 S) (hS₀S : S₀ ≤ S) (hS₀C : S₀ ≤ centralizer (W₀ : Set G))
    (hSgen : S ≤ S₀ ⊔ F ⊔ zpowers t) (hScard : Nat.card S ≤ k * Nat.card S₀)
    (hCR₀ : centralizer (W₀ : Set G) ≤ R₀) (hFR₀ : F ≤ R₀)
    (htNR₀ : t ∈ normalizer (R₀ : Set G)) (htR₀ : t ∉ R₀)
    (hT₀2 : IsPGroup 2 T₀) (hT₀R₀ : T₀ ≤ R₀) (hT₀W₀ : T₀ ≤ normalizer (W₀ : Set G))
    (htW₀ : t ∈ normalizer (W₀ : Set G)) (htT₀ : t ∈ normalizer (T₀ : Set G))
    (hT₀m : m * Nat.card (T₀ ⊓ centralizer (W₀ : Set G) : Subgroup G) ≤ Nat.card T₀)
    (hk : k < 2 * m)
    (hkey : ∀ s ∈ S, s ∉ S₀ ⊔ F → s * s = 1 →
      Nat.card (W ⊓ centralizer ({s} : Set G) : Subgroup G) ≤ Nat.card V) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup G := R₀ ⊔ zpowers t with hR
  have hRN : R ≤ normalizer (R₀ : Set G) := sup_le le_normalizer ((zpowers_le).2 htNR₀)
  have hS₀FR₀ : S₀ ⊔ F ≤ R₀ := sup_le (hS₀C.trans hCR₀) hFR₀
  have hSR : S ≤ R := hSgen.trans (sup_le (hS₀FR₀.trans le_sup_left) le_sup_right)
  set T : Subgroup G := T₀ ⊔ zpowers t with hT
  have hT2 : IsPGroup 2 T := IsPGroup.to_sup_of_normal_left' hT₀2
    (isPGroup_zpowers_of_mul_self_eq_one ht) ((zpowers_le).2 htT₀)
  have hTR : T ≤ R := sup_le (hT₀R₀.trans le_sup_left) le_sup_right
  have hTW₀ : T ≤ normalizer (W₀ : Set G) := sup_le hT₀W₀ ((zpowers_le).2 htW₀)
  have hTC : T ≤ normalizer (centralizer (W₀ : Set G) : Set G) := fun z hz =>
    mem_normalizer_centralizer_sOne (hTW₀ hz)
  have hchain : 2 * m * Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G) ≤ Nat.card T := by
    have hCT : centralizer (W₀ : Set G) ⊓ T ≤ T₀ ⊓ centralizer (W₀ : Set G) := fun z hz =>
      Subgroup.mem_inf.2 ⟨inf_le_of_not_mem_of_le ht htT₀ hT₀R₀ hCR₀ htR₀ hz,
        (Subgroup.mem_inf.1 hz).1⟩
    have hlt : T₀ < T := by
      refine lt_of_le_of_ne le_sup_left fun h => htR₀ (hT₀R₀ ?_)
      rw [h]
      exact mem_sup_right (mem_zpowers t)
    have e1 := two_mul_card_le_of_lt hlt
    have e2 := Subgroup.card_le_of_le hCT
    calc 2 * m * Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G)
        ≤ 2 * (m * Nat.card (T₀ ⊓ centralizer (W₀ : Set G) : Subgroup G)) := by
          rw [mul_assoc]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e2)
      _ ≤ 2 * Nat.card T₀ := Nat.mul_le_mul_left _ hT₀m
      _ ≤ Nat.card T := e1
  obtain ⟨P, hP2, hPCT, hPcard⟩ := exists_isPGroup_sup_normalizer hT2 hTC (hS2.to_le hS₀S) hS₀C
  have hPR : P ≤ R := hPCT.trans (sup_le (hCR₀.trans le_sup_left) hTR)
  have hlt : Nat.card S < Nat.card P := by
    have hpos : 0 < Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G) := Nat.card_pos
    have hS₀pos : 0 < Nat.card S₀ := Nat.card_pos
    have h2 : (2 * m * Nat.card S₀) * Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G) ≤
        Nat.card P * Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G) := by
      calc (2 * m * Nat.card S₀) * Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G) =
          Nat.card S₀ * (2 * m * Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G)) := by
            ring
        _ ≤ Nat.card S₀ * Nat.card T := Nat.mul_le_mul_left _ hchain
        _ ≤ _ := hPcard
    have h8 := Nat.le_of_mul_le_mul_right h2 hpos
    have h9 : k * Nat.card S₀ < 2 * m * Nat.card S₀ := Nat.mul_lt_mul_of_pos_right hk hS₀pos
    omega
  obtain ⟨Q, hQ2, hSQ, hQR⟩ := exists_isPGroup_lt_of_card_lt hS2 hSR hP2 hPR hlt
  exact false_of_isPGroup_lt hW hWV ht hWS hSN htS htcomm hB hmax hQ2 hSQ
    (fun q hq r hr => (mem_normalizer_iff.1 (hRN (hQR hq)) r).1 hr) htR₀
    (fun s hs hsR hs2 => hkey s hs (fun h => hsR (hS₀FR₀ h)) hs2)

open CFSG.ComponentClassification.M12Cover.CyclicKernel
  (eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two) in
theorem exists_isPGroup_lt_card_of_field {W C S₀ F W₀ R₀ T₀ : Subgroup G} {t : G} {k m : ℕ}
    (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1) (htW : t ∈ normalizer (W : Set G))
    (htW' : t ∉ W)
    (hWV : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    (hV2 : 2 < Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G))
    (hC2 : IsPGroup 2 C) (hCW : C ≤ normalizer (W : Set G))
    (hCt : C ≤ centralizer ({t} : Set G))
    (hCV : C ⊓ centralizer ((W ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥)
    (hWS₀ : W ≤ S₀) (hS₀ : S₀ ≤ W ⊔ C) (hS₀C : S₀ ≤ centralizer (W₀ : Set G))
    (hCgen : C ≤ S₀ ⊔ F) (hScard : 2 * Nat.card W * Nat.card C ≤ k * Nat.card S₀)
    (hCR₀ : centralizer (W₀ : Set G) ≤ R₀) (hFR₀ : F ≤ R₀)
    (htNR₀ : t ∈ normalizer (R₀ : Set G)) (htR₀ : t ∉ R₀)
    (hT₀2 : IsPGroup 2 T₀) (hT₀R₀ : T₀ ≤ R₀) (hT₀W₀ : T₀ ≤ normalizer (W₀ : Set G))
    (htW₀ : t ∈ normalizer (W₀ : Set G)) (htT₀ : t ∈ normalizer (T₀ : Set G))
    (hT₀m : m * Nat.card (T₀ ⊓ centralizer (W₀ : Set G) : Subgroup G) ≤ Nat.card T₀)
    (hk : k < 2 * m)
    (hkey : ∀ c ∈ C, c * c = 1 → Nat.card (W ⊓ centralizer ({c * t} : Set G) : Subgroup G) ≤
      Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G)) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≤ normalizer (W : Set G) ∧
      2 * Nat.card W * Nat.card C < Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hcon' : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ normalizer (W : Set G) →
      Nat.card P ≤ 2 * Nat.card W * Nat.card C := fun P hP hPN =>
    not_lt.1 fun h => hcon ⟨P, hP, hPN, h⟩
  have hWc : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one hW hv hw
  set V : Subgroup G := W ⊓ centralizer ({t} : Set G) with hV
  have htNC : t ∈ normalizer (C : Set G) :=
    mem_normalizer_of_mul_self_of_conj_mem ht fun z hz => by
      rw [← mem_centralizer_singleton_iff.1 (hCt hz), mul_inv_cancel_right]
      exact hz
  have htWC : t ∈ normalizer ((W ⊔ C : Subgroup G) : Set G) := by
    refine mem_normalizer_of_mul_self_of_conj_mem ht fun x hx => ?_
    obtain ⟨w, hw, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer_sOne hCW hx
    rw [show t * (w * c) * t⁻¹ = (t * w * t⁻¹) * (t * c * t⁻¹) by group]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 htW w).1 hw))
      (mem_sup_right ((mem_normalizer_iff.1 htNC c).1 hc))
  have hWV' : W ≤ centralizer (V : Set G) := fun w hw =>
    mem_centralizer_iff.2 fun v hv => hWc v (Subgroup.mem_inf.1 hv).1 w hw
  have hc1 : ∀ w ∈ W, ∀ c ∈ C, w * c ∈ centralizer (V : Set G) → c = 1 := by
    intro w hw c hc hwc
    have h1 : c ∈ C ⊓ centralizer (V : Set G) := by
      refine Subgroup.mem_inf.2 ⟨hc, ?_⟩
      have h2 : c = w⁻¹ * (w * c) := by group
      rw [h2]
      exact mul_mem (inv_mem (hWV' hw)) hwc
    rwa [hCV, Subgroup.mem_bot] at h1
  have htCV : t ∈ centralizer (V : Set G) := mem_centralizer_iff.2 fun v hv =>
    (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hv).2)
  set S : Subgroup G := W ⊔ C ⊔ zpowers t with hS
  have hW2 : IsPGroup 2 W := isPGroup_of_forall_mul_self_eq_one hW
  have hWC2 : IsPGroup 2 (W ⊔ C : Subgroup G) := IsPGroup.to_sup_of_normal_left' hW2 hC2 hCW
  have hS2 : IsPGroup 2 S := IsPGroup.to_sup_of_normal_left' hWC2
    (isPGroup_zpowers_of_mul_self_eq_one ht) ((zpowers_le).2 htWC)
  have hSN : S ≤ normalizer (W : Set G) := sup_le (sup_le le_normalizer hCW) ((zpowers_le).2 htW)
  have htS : t ∈ S := mem_sup_right (mem_zpowers t)
  have hWS : W ≤ S := le_sup_left.trans le_sup_left
  have hWC0 : W ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h3 : z ∈ C ⊓ centralizer (V : Set G) := Subgroup.mem_inf.2 ⟨hz.2, hWV' hz.1⟩
    rwa [hCV] at h3
  have hWCcard : Nat.card (W ⊔ C : Subgroup G) = Nat.card W * Nat.card C := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer_sOne hCW
    rw [hWC0, Subgroup.card_bot, mul_one] at h1
    exact h1
  have htWC' : t ∉ W ⊔ C := by
    intro h
    obtain ⟨w, hw, c, hc, hwc⟩ := exists_mul_of_mem_sup_of_le_normalizer_sOne hCW h
    have hc' := hc1 w hw c hc (hwc ▸ htCV)
    rw [hc', mul_one] at hwc
    exact htW' (hwc ▸ hw)
  have hScard' : Nat.card S = 2 * Nat.card W * Nat.card C := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer_sOne ((zpowers_le).2 htWC)
    have hot : orderOf t = 2 := orderOf_eq_prime (by rw [sq, ht])
      (fun h1 => htW' (h1 ▸ one_mem W))
    have h2 : (W ⊔ C : Subgroup G) ⊓ zpowers t = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzWC, hzt⟩ := Subgroup.mem_inf.1 hz
      rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hot hzt with h | h
      · exact h ▸ one_mem _
      · exact absurd (h ▸ hzWC) htWC'
    rw [h2, Subgroup.card_bot, mul_one, hWCcard, Nat.card_zpowers, hot] at h1
    rw [h1]
    ring
  have hmax : ∀ P : Subgroup G, IsPGroup 2 P → S ≤ P → P ≤ normalizer (W : Set G) → P = S :=
    fun P hP hSP hPN => (Subgroup.eq_of_le_of_card_ge hSP (by
      rw [hScard']; exact hcon' P hP hPN)).symm
  have htcomm : ∀ s ∈ S, t * s * t⁻¹ * s⁻¹ ∈ V := tcomm_mem_of_mem_sup hW ht htW hCW hCt
  have hSV : S ⊓ centralizer (V : Set G) ≤ W ⊔ zpowers t := by
    intro s hs
    obtain ⟨hsS, hsV⟩ := Subgroup.mem_inf.1 hs
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht htWC hsS with h | h
    · obtain ⟨w, hw, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer_sOne hCW h
      rw [hc1 w hw c hc hsV, mul_one]
      exact mem_sup_left hw
    · obtain ⟨w, hw, c, hc, hwc⟩ := exists_mul_of_mem_sup_of_le_normalizer_sOne hCW h
      have hc' := hc1 w hw c hc (hwc ▸ mul_mem hsV htCV)
      rw [hc', mul_one] at hwc
      have h3 : s = w * t := by
        rw [← hwc, mul_assoc, ht, mul_one]
      rw [h3]
      exact mul_mem (mem_sup_left hw) (mem_sup_right (mem_zpowers t))
  have hB : ∀ B : Subgroup G, B ≤ S → B ≤ centralizer (V : Set G) → (∀ b ∈ B, b * b = 1) →
      (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) → Nat.card B = Nat.card W → B = W := by
    intro B hBS hBV hB2 hBc hBcard
    refine eq_of_le_sup_zpowers_of_mul_self hW ht htW ?_ (fun b hb => hSV
      (Subgroup.mem_inf.2 ⟨hBS hb, hBV hb⟩)) hB2 hBc hBcard
    rw [hWV, sq]
    exact Nat.mul_lt_mul_of_pos_right hV2 Nat.card_pos
  have hS₀S : S₀ ≤ S := hS₀.trans le_sup_left
  have hWCSF : W ⊔ C ≤ S₀ ⊔ F := sup_le (hWS₀.trans le_sup_left) hCgen
  have hSgen : S ≤ S₀ ⊔ F ⊔ zpowers t := sup_le (hWCSF.trans le_sup_left) le_sup_right
  have hkey' : ∀ s ∈ S, s ∉ S₀ ⊔ F → s * s = 1 →
      Nat.card (W ⊓ centralizer ({s} : Set G) : Subgroup G) ≤ Nat.card V := by
    intro s hs hsF hs2
    rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht htWC hs with h | h
    · exact absurd (hWCSF h) hsF
    obtain ⟨w, hw, c, hc, hwc⟩ := exists_mul_of_mem_sup_of_le_normalizer_sOne hCW h
    have hs' : s = w * (c * t) := by rw [← mul_assoc, ← hwc, mul_assoc, ht, mul_one]
    have hc2 : c * c = 1 := by
      have hct : c * t = t * c := mem_centralizer_singleton_iff.1 (hCt hc)
      have hwct : (c * t) * w * (c * t)⁻¹ ∈ W := by
        have h1 := (mem_normalizer_iff.1 (hCW hc) _).1 ((mem_normalizer_iff.1 htW w).1 hw)
        rwa [show c * (t * w * t⁻¹) * c⁻¹ = (c * t) * w * (c * t)⁻¹ by group] at h1
      have h1 : c * c = (w * ((c * t) * w * (c * t)⁻¹))⁻¹ * (s * s) := by
        rw [hs']
        calc c * c = (c * t) * (c * t) := by rw [mul_assoc, ← mul_assoc t, ← hct, mul_assoc,
              ht, mul_one]
          _ = (w * ((c * t) * w * (c * t)⁻¹))⁻¹ * (w * (c * t) * (w * (c * t))) := by group
      rw [hs2, mul_one] at h1
      have h2 : c * c ∈ W := h1 ▸ inv_mem (mul_mem hw hwct)
      have h3 : c * c ∈ W ⊓ C := Subgroup.mem_inf.2 ⟨h2, mul_mem hc hc⟩
      rwa [hWC0, Subgroup.mem_bot] at h3
    have heq : W ⊓ centralizer ({s} : Set G) = W ⊓ centralizer ({c * t} : Set G) := by
      ext z
      simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff]
      refine and_congr_right fun hz => ?_
      rw [hs']
      constructor
      · intro h1
        have h2 : w * (z * (c * t)) = w * ((c * t) * z) := by
          calc w * (z * (c * t)) = (w * z) * (c * t) := by group
            _ = (z * w) * (c * t) := by rw [hWc w hw z hz]
            _ = z * (w * (c * t)) := by group
            _ = w * (c * t) * z := h1
            _ = w * ((c * t) * z) := by group
        exact mul_left_cancel h2
      · intro h1
        calc z * (w * (c * t)) = (z * w) * (c * t) := by group
          _ = (w * z) * (c * t) := by rw [hWc w hw z hz]
          _ = w * (z * (c * t)) := by group
          _ = w * ((c * t) * z) := by rw [h1]
          _ = w * (c * t) * z := by group
    rw [heq]
    exact hkey c hc hc2
  exact false_of_field_gen hW hWV ht hWS hSN htS htcomm hB hmax hS2 hS₀S hS₀C hSgen
    (hScard'.symm ▸ hScard) hCR₀ hFR₀ htNR₀ htR₀ hT₀2 hT₀R₀ hT₀W₀ htW₀ htT₀ hT₀m hk hkey'

end CFSG.SeitzReduction.LinearPilot
