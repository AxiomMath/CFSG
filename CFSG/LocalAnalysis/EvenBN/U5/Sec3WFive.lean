module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3WFour

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem ElemAbMod.sup_of_le_normalizer {N B : Subgroup G} (hBN : B ≤ normalizer (N : Set G))
    (hB : ElemAbMod N B) : ElemAbMod N (N ⊔ B) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨n, hn, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN hx
    have e : n * b * (n * b) = n * (b * n * b⁻¹) * (b * b) := by group
    rw [e]
    exact mul_mem (mul_mem hn ((mem_normalizer_iff.1 (hBN hb) n).1 hn)) (hB.1 b hb)
  · obtain ⟨n, hn, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN hx
    obtain ⟨n', hn', b', hb', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN hy
    have e : ⁅n * b, n' * b'⁆ = n * (b * n' * b⁻¹) * ⁅b, b'⁆ * (n' * (b' * n * b'⁻¹))⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mul_mem (mul_mem hn ((mem_normalizer_iff.1 (hBN hb) n').1 hn'))
      (hB.2 b hb b' hb')) (inv_mem (mul_mem hn' ((mem_normalizer_iff.1 (hBN hb') n).1 hn)))

theorem ElemAbMod.of_le {N N' E : Subgroup G} (hE : ElemAbMod N E) (hNN : N ≤ N') :
    ElemAbMod N' E :=
  ⟨fun x hx => hNN (hE.1 x hx), fun x hx y hy => hNN (hE.2 x hx y hy)⟩

end Generic

section GenericFinite

variable {G : Type} [Group G] [Finite G]

theorem ElemAbMod.zpowers_sup_right {t : G} (ht : t * t = 1) {N E : Subgroup G}
    (hE : ElemAbMod N E) (hEt : ∀ e ∈ E, e * t = t * e) : ElemAbMod N (zpowers t ⊔ E) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨e, he, hxe | hxe⟩ := exists_of_mem_zpowers_sup_of_commute ht hEt hx
    · rw [hxe]
      exact hE.1 e he
    · rw [hxe, mul_self_t_mul ht (hEt e he)]
      exact hE.1 e he
  · obtain ⟨a, ha, hxa | hxa⟩ := exists_of_mem_zpowers_sup_of_commute ht hEt hx <;>
    obtain ⟨b, hb, hyb | hyb⟩ := exists_of_mem_zpowers_sup_of_commute ht hEt hy <;>
    rw [hxa, hyb]
    · exact hE.2 a ha b hb
    · rw [commutatorElement_t_mul_right ht (hEt a ha) (hEt b hb)]
      exact hE.2 a ha b hb
    · rw [commutatorElement_t_mul_left ht (hEt a ha) (hEt b hb)]
      exact hE.2 a ha b hb
    · rw [commutatorElement_t_mul_left ht (hEt a ha) (by rw [mul_assoc, hEt b hb]),
        commutatorElement_t_mul_right ht (hEt a ha) (hEt b hb)]
      exact hE.2 a ha b hb

end GenericFinite

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.elemAbMod_A₁_B₃ (hd : d.Hyp) : ElemAbMod d.A₁ d.B₃ :=
  ElemAbMod.zpowers_sup_right hd.t_mul_t d.elemAbMod_A₁_A₃ fun _ he =>
    hd.comm_t (d.A₃_le_P.trans d.P_le_L he)

theorem Hyp.elemAbMod_Zp_B₂ (hd : d.Hyp) : ElemAbMod d.Zp d.B₂ :=
  ElemAbMod.zpowers_sup_right hd.t_mul_t d.elemAbMod_Zp_A₂ fun _ he => hd.comm_t (d.A₂_le_L he)

theorem Hyp.card_FB₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card (d.F ⊔ d.B₃ : Subgroup G) = 2 * (2 ^ f) ^ 12 := by
  have hN : d.B₃ ≤ normalizer (d.F : Set G) :=
    (d.B₃_le_tP.trans hd.tP_le_T).trans (hd.T_le_normalizer_F hGMS)
  have h1 := Common.card_sup_mul_card_inf_eq hN
  rw [hd.F_inf_B₃ hGMS, hd.card_F hGMS, hd.card_B₃, d.card_A₁] at h1
  have hq : 0 < (2 ^ f) ^ 4 := by positivity
  refine Nat.eq_of_mul_eq_mul_right hq (h1.trans ?_)
  ring

theorem Hyp.F_sup_B₁_sup_A₂ (hd : d.Hyp) : d.F ⊔ (d.B₁ ⊔ d.A₂) = d.F ⊔ d.B₂ := by
  refine le_antisymm (sup_le le_sup_left (sup_le (sup_le (le_sup_left.trans le_sup_right)
    (hd.A₁_le_F.trans le_sup_left)) (le_sup_right.trans le_sup_right))) (sup_le le_sup_left ?_)
  exact sup_le ((le_sup_left.trans le_sup_left).trans le_sup_right) (le_sup_right.trans
    le_sup_right)

theorem Hyp.card_le_of_elemAbMod_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {E : Subgroup G} (hFE : d.F ≤ E) (hET : E ≤ d.F ⊔ d.T) (hE : ElemAbMod d.F E) :
    Nat.card E ≤ 2 * (2 ^ f) ^ 12 ∧
      (Nat.card E = 2 * (2 ^ f) ^ 12 → E = d.F ⊔ d.B₃ ∨ E = d.F ⊔ d.B₂) := by
  have hTF := hd.T_le_normalizer_F hGMS
  set Y := E ⊓ d.T with hY
  have hEeq : E = d.F ⊔ Y := by
    refine le_antisymm (fun e he => ?_) (sup_le hFE inf_le_left)
    obtain ⟨a, ha, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hTF (hET he)
    have hsE : s ∈ E := by
      have := mul_mem (inv_mem (hFE ha)) he
      rwa [inv_mul_cancel_left] at this
    exact mul_mem (mem_sup_left ha) (mem_sup_right (Subgroup.mem_inf.2 ⟨hsE, hs⟩))
  have hFY : d.F ⊓ Y = d.A₁ := by
    rw [hY, ← inf_assoc, inf_eq_left.2 hFE, hd.F_inf_T hGMS]
  have hYA : ElemAbMod d.A₁ Y := by
    rw [← hd.F_inf_T hGMS]
    refine ⟨fun x hx => Subgroup.mem_inf.2 ⟨hE.1 x hx.1, mul_mem hx.2 hx.2⟩,
      fun x hx y hy => Subgroup.mem_inf.2 ⟨hE.2 x hx.1 y hy.1, ?_⟩⟩
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx.2 hy.2) (inv_mem hx.2)) (inv_mem hy.2)
  have hYt : ∀ y ∈ Y, y * d.t = d.t * y := fun y hy =>
    mem_centralizer_singleton_iff.1 (hd.T_le_centralizer hy.2)
  have hY' : ElemAbMod d.B₁ (zpowers d.t ⊔ Y) := ElemAbMod.zpowers_sup hd.t_mul_t hYA hYt
  have hY'T : zpowers d.t ⊔ Y ≤ d.T := sup_le (zpowers_le.2 hd.t_mem_T) inf_le_right
  obtain ⟨hc, hc'⟩ := hd.card_le_of_elemAbMod_B₁ hY'T hY'
  have h1 := Common.card_sup_mul_card_inf_eq (show Y ≤ normalizer (d.F : Set G) from
    inf_le_right.trans hTF)
  rw [← hEeq, hFY, hd.card_F hGMS, d.card_A₁] at h1
  have hYY : Nat.card Y ≤ Nat.card (zpowers d.t ⊔ Y : Subgroup G) := card_le_of_le le_sup_right
  have hq : 0 < (2 ^ f) ^ 4 := by positivity
  have hcardE : Nat.card E = (2 ^ f) ^ 4 * Nat.card Y := by
    refine Nat.eq_of_mul_eq_mul_right hq (h1.trans ?_)
    ring
  refine ⟨?_, fun hE12 => ?_⟩
  · rw [hcardE]
    calc (2 ^ f) ^ 4 * Nat.card Y ≤ (2 ^ f) ^ 4 * (2 * (2 ^ f) ^ 8) :=
          Nat.mul_le_mul_left _ (hYY.trans hc)
      _ = 2 * (2 ^ f) ^ 12 := by ring
  · have hY8 : Nat.card Y = 2 * (2 ^ f) ^ 8 := by
      rw [hcardE] at hE12
      refine Nat.eq_of_mul_eq_mul_left hq (hE12.trans ?_)
      ring
    have hYeq : zpowers d.t ⊔ Y = Y := (Subgroup.eq_of_le_of_card_ge le_sup_right
      (by rw [hY8]; exact hc)).symm
    rcases hc' (le_antisymm hc (hY8 ▸ hYY)) with h3 | h3
    · left
      rw [hEeq, ← hYeq, h3]
    · right
      rw [hEeq, ← hYeq, h3, hd.F_sup_B₁_sup_A₂]

end Data

end CFSG.LocalAnalysis.EvenBN.U5
