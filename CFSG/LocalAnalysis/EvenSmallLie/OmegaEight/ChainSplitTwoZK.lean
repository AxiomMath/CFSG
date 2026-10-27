module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitTwoZ
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainT0
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitTwoKill

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G]

theorem zCount_eq (ε : Eps) (n : ℕ) :
    zCount ε n = ((Finset.range 128).filter fun j => zTest ε (tilGet ε j) n = true).card +
      ((Finset.range 128).filter fun j => ((zAnn ε).all fun f =>
        dot4 f (mv4 (add4 one4 (tilGet ε j)) (dig4 n)) == 0) = true).card := by
  rw [zCount]
  congr 1

namespace Config

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} {W : Subgroup G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hC : Config t Q (P ⊔ zpowers x₀) 2 W) {Φ : (Fin 6 → ZMod 4) → G} (hΦ : Coord4 W ψ Φ)
  (hw : ∀ w, Rep Φ (wordElt p w) (prodW ε (c0Mat ε) w)) (hrept : Rep Φ t (-1))
  {ρ : G} (hρ : ρ = x₀ ∨ ρ = t * x₀) (hρX : Rep Φ ρ (toMat4 (xTil ε)))
  (hrepU : ∀ h ∈ U ⊔ zpowers ρ, ∃ i < 128, Rep Φ h (toMat4 (tilGet ε i)))
include hS hC hΦ hw hrept hρ hρX hrepU

theorem false_of_zX [Finite G]
    {g b h : G} (hb : b ∈ W) (hh : h ∈ U ⊔ zpowers ρ)
    (hh2 : h * h ∈ Q) (hbh : g * t * g⁻¹ = b * h)
    (hhz : Rep Φ h (toMat4 (tilGet ε (zTil ε))))
    (hodd : Odd ((W ⊔ (U ⊔ zpowers x₀ ⊔ zpowers t)).relIndex (centralizer {g * t * g⁻¹}))) :
    False := by
  have hR := hS.rad
  obtain ⟨-, hzc, hzfix, hzlt, hrlt, hrr, hann, hwit, hcov⟩ := zCheck_parts ε
  obtain ⟨X₂, hX₂U, hX₂E, hdec⟩ := hS.exists_levi hρ
  have hreal := hC.realizeX hS hΦ hw hρX
  set Tz := toMat4 (tilGet ε (zTil ε))
  have hTz2 : Tz * Tz = 1 := hΦ.rep_unique (Coord4.rep_mul hhz hhz)
    (hΦ.rep_of_mem_A hC.level.comm (hC.level.Q_le hh2))
  obtain ⟨h₀, hh₀, hh₀r⟩ := exists_rep_X₂ hS hC hΦ hρ hX₂U hreal hdec hzlt
  have hh₀2 : h₀ * h₀ = 1 := eq_of_rep_X₂ hS hΦ hρ hX₂U hX₂E (mul_mem hh₀ hh₀) (one_mem _)
    (hTz2 ▸ Coord4.rep_mul hh₀r hh₀r) Coord4.rep_one
  obtain ⟨q, hq, k, hk, hhk | hhk⟩ := hdec h (hS.Urho_le_TH hρ hh)
  swap
  · apply hS.t_not_mem_Urho hρ
    have : t = (q * k)⁻¹ * h := by rw [hhk]; group
    rw [this]
    exact mul_mem (inv_mem (mul_mem (mem_sup_left (hR.Q_le_U hq)) (hX₂U hk))) hh
  have hkz : Rep Φ k Tz := fun v => by
    have hq1 := hΦ.rep_of_mem_A hC.level.comm (hC.level.Q_le hq)
    have h1 := hhz v
    rw [hhk] at h1
    have h2 := hq1 (Tz *ᵥ v)
    rw [one_mulVec] at h2
    calc k * Φ v * k⁻¹ = q⁻¹ * (q * k * Φ v * (q * k)⁻¹) * q := by group
      _ = q⁻¹ * Φ (Tz *ᵥ v) * q := by rw [h1]
      _ = Φ (Tz *ᵥ v) := by
        calc q⁻¹ * Φ (Tz *ᵥ v) * q = q⁻¹ * (q * Φ (Tz *ᵥ v) * q⁻¹) * q := by rw [h2]
          _ = _ := by group
  have hkh₀ : k = h₀ := eq_of_rep_X₂ hS hΦ hρ hX₂U hX₂E hk hh₀ hkz hh₀r
  have hc₀ : b * q ∈ W := mul_mem hb (hC.level.Q_le hq)
  obtain ⟨x, hx⟩ := hΦ.surj _ hc₀
  have hu : g * t * g⁻¹ = Φ x * h₀ := by rw [hbh, hhk, hkh₀, hx, mul_assoc]
  have hxW : Φ x ∈ W := hΦ.mem x
  have hu2 : Φ x * h₀ * (Φ x * h₀) = 1 := by
    rw [← hu, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, hS.shape.mul_self]
    group
  have hx0 : (1 + Tz) *ᵥ x = 0 := by
    have e : Φ x * h₀ * (Φ x * h₀) = Φ (x + Tz *ᵥ x) := by
      rw [hΦ.add, ← hh₀r x]
      calc Φ x * h₀ * (Φ x * h₀) = Φ x * (h₀ * Φ x * h₀⁻¹) * (h₀ * h₀) := by group
        _ = Φ x * (h₀ * Φ x * h₀⁻¹) := by rw [hh₀2, mul_one]
    have := hΦ.inj _ (e ▸ hu2)
    rwa [add_mulVec, one_mulVec]
  set n := enc4 x
  have hn : n < 4096 := enc4_lt x
  have hxn : toVec4 (dig4 n) = x := toVec4_dig4_enc4 x
  have hzero : mv4 (add4 one4 (tilGet ε (zTil ε))) (dig4 n) = dig4 0 := by
    apply eq_of_toVec4_eq (f := fun i => ∑ k : Fin 6,
      m4Get (add4 one4 (tilGet ε (zTil ε))) i k * (dig4 n).getD k 0)
      (g := fun j => 0 / 4 ^ (j : ℕ))
    change toVec4 (mv4 (add4 one4 (tilGet ε (zTil ε))) (dig4 n)) = toVec4 (dig4 0)
    rw [toVec4_mv4, toMat4_add4, toMat4_one4, hxn, hx0, toVec4_dig4_zero]
  rcases hcov n hn hzero with ⟨w, hwW, hw1⟩ | hcnt
  ·
    obtain ⟨n', m, s⟩ := w
    simp only at hw1
    subst hw1
    have hwv := hwit _ hwW
    simp only at hwv
    set y := toVec4 (dig4 m)
    set Tr := toMat4 (tilGet ε (zRoot ε))
    obtain ⟨kr, hkr, hkrr⟩ := exists_rep_X₂ hS hC hΦ hρ hX₂U hreal hdec hrlt
    have hTr2 : Tr * Tr = Tz := by rw [← toMat4_mul4, hrr]
    have hkr2' : Rep Φ (kr * kr) Tz := hTr2 ▸ Coord4.rep_mul hkrr hkrr
    have hkr2 : kr * kr = h₀ := eq_of_rep_X₂ hS hΦ hρ hX₂U hX₂E (mul_mem hkr hkr) hh₀ hkr2' hh₀r
    have hkrt : kr * t = t * kr := hS.commute_of_mem_TH (hS.Urho_le_TH hρ (hX₂U hkr))
    obtain ⟨r, hr⟩ : ∃ r : G, r * r = g * t * g⁻¹ := by
      rw [hu]
      cases s
      ·
        have hyx : y - Tr *ᵥ y = x := by
          have := congrArg toVec4 hwv
          simp only [Bool.false_eq_true, ↓reduceIte, toVec4_mv4, toMat4_sub4, toMat4_one4,
            sub_mulVec, one_mulVec] at this
          rw [this, hxn]
        have hm : Rep Φ (kr * t) (Tr * -1) := Coord4.rep_mul hkrr hrept
        refine ⟨Φ y * (kr * t), ?_⟩
        calc Φ y * (kr * t) * (Φ y * (kr * t)) =
            Φ y * ((kr * t) * Φ y * (kr * t)⁻¹) * ((kr * t) * (kr * t)) := by group
          _ = Φ y * Φ ((Tr * -1) *ᵥ y) * (kr * kr) := by
            rw [hm y, show kr * t * (kr * t) = kr * kr * (t * t) by
              rw [mul_assoc kr t, ← mul_assoc t kr, ← hkrt]; group, hS.shape.mul_self, mul_one]
          _ = Φ x * h₀ := by
            rw [hkr2, ← hΦ.add, mul_neg_one, neg_mulVec, ← sub_eq_add_neg, hyx]
      ·
        have hyx : y + Tr *ᵥ y = x := by
          have := congrArg toVec4 hwv
          simp only [↓reduceIte, toVec4_mv4, toMat4_add4, toMat4_one4, add_mulVec,
            one_mulVec] at this
          rw [this, hxn]
        refine ⟨Φ y * kr, ?_⟩
        calc Φ y * kr * (Φ y * kr) = Φ y * (kr * Φ y * kr⁻¹) * (kr * kr) := by group
          _ = Φ x * h₀ := by rw [hkrr y, hkr2, ← hΦ.add, hyx]
    apply hS.shape.not_square (g⁻¹ * r * g)
    rw [show g⁻¹ * r * g * (g⁻¹ * r * g) = g⁻¹ * (r * r) * g by group, hr]
    group
  ·
    classical
    have hlow := hC.card_centralizer_geX hS hodd
    rw [hu] at hlow
    set F₁ := (Finset.range 128).filter fun j => zTest ε (tilGet ε j) n = true
    set F₂ := (Finset.range 128).filter fun j => ((zAnn ε).all fun f =>
      dot4 f (mv4 (add4 one4 (tilGet ε j)) (dig4 n)) == 0) = true
    set S := F₁.image (fun j => toMat4 (tilGet ε j)) ∪
      F₂.image (fun j => -toMat4 (tilGet ε j))
    have hScard : S.card ≤ 128 := by
      calc S.card ≤ (F₁.image _).card + (F₂.image _).card := Finset.card_union_le _ _
        _ ≤ F₁.card + F₂.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ = zCount ε n := (zCount_eq ε n).symm
        _ ≤ 128 := hcnt
    have hcommh₀ : ∀ k' ∈ X₂, k' * h₀ = h₀ * k' := by
      intro k' hk'
      obtain ⟨j, hj, hk'j⟩ := hrepU k' (hX₂U hk')
      have hjz := hzc j hj
      refine eq_of_rep_X₂ hS hΦ hρ hX₂U hX₂E (mul_mem hk' hh₀) (mul_mem hh₀ hk')
        (Coord4.rep_mul hk'j hh₀r) ?_
      have := Coord4.rep_mul hh₀r hk'j
      rwa [← toMat4_mul4, hjz, toMat4_mul4] at this
    have hh₀t : h₀ * t = t * h₀ := hS.commute_of_mem_TH (hS.Urho_le_TH hρ (hX₂U hh₀))
    have h1 := card_le_of_reps (C := (W ⊔ (U ⊔ zpowers x₀ ⊔ zpowers t)) ⊓
      centralizer {Φ x * h₀}) (W := W) S (fun c hc => ?_)
      (fun c hc hc1 => hC.mem_W_of_repX hS hΦ hrept hρ hc.1 hc1)
    · rw [hC.inf_centralizer_eqX hxW, card_fix_B hΦ hh₀r, card_fix4, hzfix] at h1
      have := h1.trans (Nat.mul_le_mul_left 64 hScard)
      omega
    · obtain ⟨hcT, hcC⟩ := Subgroup.mem_inf.1 hc
      have hcu := mem_centralizer_singleton_iff.1 hcC
      obtain ⟨w₀, hw₀, y, hy, hcy⟩ :=
        exists_mul_of_mem_sup_normalizer (hC.TH_le_normalizerX hS) hcT
      obtain ⟨q', hq', k', hk', hyk | hyk⟩ := hdec y hy
      all_goals
        obtain ⟨j, hj, hk'j⟩ := hrepU k' (hX₂U hk')
        have hw₁ : w₀ * q' ∈ W := mul_mem hw₀ (hC.level.Q_le hq')
        obtain ⟨wv, hwv⟩ := hΦ.surj _ hw₁
        have hwvn : toVec4 (dig4 (enc4 wv)) = wv := toVec4_dig4_enc4 wv
        have hT0 := hann
      ·
        have hmh : k' * h₀ * k'⁻¹ = h₀ := by rw [hcommh₀ k' hk', mul_inv_cancel_right]
        have hcw : Φ wv * k' = c := by rw [hwv, hcy, hyk]; group
        have hc' : Φ wv * k' * (Φ x * h₀) = Φ x * h₀ * (Φ wv * k') := by rw [hcw]; exact hcu
        have htest := test_of_commX hΦ hk'j hh₀r hmh hc'
        refine ⟨toMat4 (tilGet ε j), Finset.mem_union_left _ (Finset.mem_image_of_mem _
          (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ?_⟩)), ?_⟩
        · simp only [zTest, List.all_eq_true, beq_iff_eq]
          intro f hf
          have harr : mv4 (sub4 one4 (tilGet ε j)) (dig4 n) =
              mv4 (sub4 one4 (tilGet ε (zTil ε))) (dig4 (enc4 wv)) := by
            apply eq_of_toVec4_mv4
            rw [toMat4_sub4, toMat4_sub4, toMat4_one4, hxn, hwvn]
            exact htest.symm
          rw [harr]
          exact hann f hf _ (enc4_lt wv)
        · rw [← hcw]
          have := Coord4.rep_mul (hΦ.rep_of_mem_A hC.level.comm (hΦ.mem wv)) hk'j
          rwa [one_mul] at this
      ·
        have hk'tF : Rep Φ (k' * t) (toMat4 (tilGet ε j) * -1) := Coord4.rep_mul hk'j hrept
        have hmh : k' * t * h₀ * (k' * t)⁻¹ = h₀ := by
          calc k' * t * h₀ * (k' * t)⁻¹ = k' * (t * h₀ * t⁻¹) * k'⁻¹ := by group
            _ = k' * h₀ * k'⁻¹ := by rw [← hh₀t, mul_inv_cancel_right]
            _ = h₀ := by rw [hcommh₀ k' hk', mul_inv_cancel_right]
        have hcw : Φ wv * (k' * t) = c := by rw [hwv, hcy, hyk]; group
        have hc' : Φ wv * (k' * t) * (Φ x * h₀) = Φ x * h₀ * (Φ wv * (k' * t)) := by
          rw [hcw]; exact hcu
        have htest := test_of_commX hΦ hk'tF hh₀r hmh hc'
        refine ⟨-toMat4 (tilGet ε j), Finset.mem_union_right _ (Finset.mem_image_of_mem _
          (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ?_⟩)), ?_⟩
        · simp only [List.all_eq_true, beq_iff_eq]
          intro f hf
          have harr : mv4 (add4 one4 (tilGet ε j)) (dig4 n) =
              mv4 (sub4 one4 (tilGet ε (zTil ε))) (dig4 (enc4 wv)) := by
            apply eq_of_toVec4_mv4
            rw [toMat4_add4, toMat4_sub4, toMat4_one4, hxn, hwvn, htest, mul_neg_one,
              sub_neg_eq_add]
          rw [harr]
          exact hann f hf _ (enc4_lt wv)
        · rw [← hcw]
          have := Coord4.rep_mul (hΦ.rep_of_mem_A hC.level.comm (hΦ.mem wv)) hk'tF
          rwa [one_mul, mul_neg_one] at this

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain
