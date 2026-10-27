module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSGen
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSKey
import CFSG.LocalAnalysis.SeitzReduction.Endgame

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup
open scoped Pointwise
open CFSG.ComponentClassification.M12Cover.CyclicKernel
  (eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two)

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_le_normalizer_sOne {W C : Subgroup G}
    (hCW : C ≤ normalizer (W : Set G)) {x : G} (hx : x ∈ W ⊔ C) :
    ∃ w ∈ W, ∃ c ∈ C, x = w * c := by
  have hset : ((W ⊔ C : Subgroup G) : Set G) = (C : Set G) * (W : Set G) := by
    rw [sup_comm]
    exact coe_mul_of_left_le_normalizer_right C W hCW
  have hx' : x ∈ (C : Set G) * (W : Set G) := hset ▸ hx
  obtain ⟨c, hc, w, hw, rfl⟩ := hx'
  exact ⟨c * w * c⁻¹, (mem_normalizer_iff.1 (hCW hc) w).1 hw, c, hc, by group⟩

theorem isPGroup_of_forall_mul_self_eq_one {W : Subgroup G} (hW : ∀ w ∈ W, w * w = 1) :
    IsPGroup 2 W := by
  rintro ⟨w, hw⟩
  refine ⟨1, ?_⟩
  rw [pow_one, sq]
  exact Subtype.ext (hW w hw)

variable [Finite G]

theorem exists_isPGroup_lt_card_of_swap {W C S₀ F W₀ A X : Subgroup G} {t : G} {k : ℕ}
    (hW : ∀ w ∈ W, w * w = 1) (ht : t * t = 1) (htW : t ∈ normalizer (W : Set G))
    (htW' : t ∉ W)
    (hWV : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    (hV2 : 2 < Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G))
    (hC2 : IsPGroup 2 C) (hCW : C ≤ normalizer (W : Set G))
    (hCt : C ≤ centralizer ({t} : Set G))
    (hCV : C ⊓ centralizer ((W ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥)
    (hWS₀ : W ≤ S₀) (hS₀ : S₀ ≤ W ⊔ C) (hS₀C : S₀ ≤ centralizer (W₀ : Set G))
    (hCgen : C ≤ S₀ ⊔ F) (hScard : 2 * Nat.card W * Nat.card C ≤ k * Nat.card S₀)
    (hinf : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a)
    (htW₀ : t ∈ normalizer (W₀ : Set G)) (hE1 : W₀ ⊓ A ≠ ⊥)
    (hFA : F ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hFW₀ : F ≤ normalizer (W₀ : Set G))
    (hX2 : IsPGroup 2 X) (hXA : X ≤ A) (hXW₀ : X ≤ normalizer (W₀ : Set G))
    (hXE : X ⊓ centralizer ((W₀ ⊓ A : Subgroup G) : Set G) = ⊥) (hk : k < 2 * Nat.card X ^ 2)
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
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
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
  have hWCcard : Nat.card (W ⊔ C : Subgroup G) = Nat.card W * Nat.card C := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer_sOne hCW
    have h2 : W ⊓ C = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h3 : z ∈ C ⊓ centralizer (V : Set G) := Subgroup.mem_inf.2 ⟨hz.2, hWV' hz.1⟩
      rwa [hCV] at h3
    rw [h2, Subgroup.card_bot, mul_one] at h1
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
      have h4 : W ⊓ C = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        have h5 : z ∈ C ⊓ centralizer (V : Set G) := Subgroup.mem_inf.2 ⟨hz.2, hWV' hz.1⟩
        rwa [hCV] at h5
      rwa [h4, Subgroup.mem_bot] at h3
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
  exact false_of_swap_gen hW hWV ht hWS hSN htS htcomm hB hmax hS2 hS₀S hS₀C hSgen
    (hScard'.symm ▸ hScard) hinf hc htW₀ hE1 hFA hFW₀ hX2 hXA hXW₀ hXE hk hkey'

end CFSG.SeitzReduction.LinearPilot
