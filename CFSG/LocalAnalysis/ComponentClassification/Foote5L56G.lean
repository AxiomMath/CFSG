module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56F
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56A
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56E

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mul_mem_of_card_eq_two_mul {A S : Subgroup G} (hAS : A ≤ S)
    (hcard : Nat.card S = 2 * Nat.card A) {y g : G} (hyS : y ∈ S) (hgS : g ∈ S)
    (hyA : y ∉ A) (hgA : g ∉ A) : y * g ∈ A := by
  have h1 := relIndex_mul_card A S
  rw [inf_of_le_left hAS, hcard] at h1
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h2 : A.relIndex S = 2 := by
    have h3 : A.relIndex S * Nat.card A = 2 * Nat.card A := h1
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  have h4 := (mul_mem_iff_of_index_two (H := A.subgroupOf S) h2
    (a := ⟨y, hyS⟩) (b := ⟨g, hgS⟩)).mpr
    ⟨fun h5 => absurd (mem_subgroupOf.mp h5) hyA, fun h5 => absurd (mem_subgroupOf.mp h5) hgA⟩
  exact mem_subgroupOf.mp h4

theorem gen4_of_three_involutions (hMW : MacWilliamsStatement) {T : Subgroup G}
    (hT : IsSylowOf 2 T ⊤) {e₁ e₂ e₃ : G} (h1T : e₁ ∈ T) (h2T : e₂ ∈ T) (h3T : e₃ ∈ T)
    (h11 : e₁ * e₁ = 1) (h22 : e₂ * e₂ = 1) (h33 : e₃ * e₃ = 1) (h12 : e₁ * e₂ = e₂ * e₁)
    (h13 : e₁ * e₃ = e₃ * e₁) (h23 : e₂ * e₃ = e₃ * e₂) (he₁ : e₁ ≠ 1) (he₂ : e₂ ≠ 1)
    (he₁₂ : e₁ ≠ e₂) (he₃ : ¬ (e₃ = e₁ * e₂ ∨ e₃ = e₁ ∨ e₃ = e₂ ∨ e₃ = 1))
    (hcent : ∀ y ∈ T, y * e₁ = e₁ * y → y * e₂ = e₂ * y → y * e₃ = e₃ * y →
      (y = e₁ * e₂ ∨ y = e₁ ∨ y = e₂ ∨ y = 1) ∨
        (y * e₃ = e₁ * e₂ ∨ y * e₃ = e₁ ∨ y * e₃ = e₂ ∨ y * e₃ = 1)) :
    GH74.Gen4 G := by
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions e₁ e₂ h11 h22 h12 with hV
  have hVmem : ∀ e, e ∈ V ↔ e = e₁ * e₂ ∨ e = e₁ ∨ e = e₂ ∨ e = 1 := fun e => by
    change e ∈ ({e₁ * e₂, e₁, e₂, 1} : Set G) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hV4 : Nat.card V = 4 := (GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    e₁ e₂ h11 h22 he₁ he₂ he₁₂ h12).card_four
  have hV3 : ∀ v ∈ V, v * e₃ = e₃ * v := by
    intro v hv
    rcases (hVmem v).mp hv with rfl | rfl | rfl | rfl
    · rw [mul_assoc, h23, ← mul_assoc, h13, mul_assoc]
    · exact h13
    · exact h23
    · rw [one_mul, mul_one]
  have hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val ((GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
      e₁ e₂ h11 h22 he₁ he₂ he₁₂ h12).isMulCommutative.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv =>
    congrArg Subtype.val ((GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
      e₁ e₂ h11 h22 he₁ he₂ he₁₂ h12).mul_self ⟨v, hv⟩)
  have hVT : V ≤ T := fun v hv => by
    rcases (hVmem v).mp hv with rfl | rfl | rfl | rfl
    · exact mul_mem h1T h2T
    · exact h1T
    · exact h2T
    · exact one_mem _
  have he₃1 : e₃ ≠ 1 := fun h1 => he₃ (Or.inr (Or.inr (Or.inr h1)))
  have hzp : ∀ w ∈ zpowers e₃, w = 1 ∨ w = e₃ := by
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [show m + m = 2 * m by ring, zpow_mul, zpow_two, h33, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, h33, one_zpow, one_mul, zpow_one]
  have hnorm : zpowers e₃ ≤ normalizer (V : Set G) := by
    refine le_normalizer_of_commute fun v hv w hw => ?_
    rcases hzp w hw with rfl | rfl
    · rw [mul_one, one_mul]
    · exact hV3 v hv
  have hdisj : Disjoint V (zpowers e₃) := by
    rw [disjoint_iff, eq_bot_iff]
    intro w hw
    rcases hzp w (mem_inf.mp hw).2 with rfl | rfl
    · exact one_mem _
    · exact absurd ((hVmem _).mp (mem_inf.mp hw).1) he₃
  set E := V ⊔ zpowers e₃ with hE
  have hEmem : ∀ y ∈ E, y ∈ V ∨ y * e₃ ∈ V := by
    intro y hy
    have h1 : y ∈ ((V : Set G) * (zpowers e₃ : Set G)) := by
      rw [← coe_mul_of_right_le_normalizer_left V (zpowers e₃) hnorm]
      exact hy
    obtain ⟨c, hc, w, hw, hcw⟩ := h1
    have hcw' : c * w = y := hcw
    rw [← hcw']
    rcases hzp w hw with hw1 | hw1 <;> rw [hw1]
    · left
      rw [mul_one]
      exact hc
    · right
      rw [mul_assoc, h33, mul_one]
      exact hc
  have hE8 : Nat.card E = 8 := by
    rw [hE, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer V (zpowers e₃) hnorm
      hdisj, hV4, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact h33) he₃1]
  have hEC : E ≤ centralizer (V : Set G) ⊓ centralizer ({e₃} : Set G) := by
    refine sup_le (le_inf (fun v hv => mem_centralizer_iff.mpr fun w hw => hVc w hw v hv)
      fun v hv => mem_centralizer_singleton_iff.mpr (hV3 v hv)) (zpowers_le.mpr ?_)
    exact mem_inf.mpr ⟨mem_centralizer_iff.mpr fun w hw => hV3 w hw,
      mem_centralizer_singleton_iff.mpr rfl⟩
  have hform : ∀ y ∈ E, ∃ v ∈ V, y = v ∨ y = v * e₃ := by
    intro y hy
    rcases hEmem y hy with h1 | h1
    · exact ⟨y, h1, Or.inl rfl⟩
    · exact ⟨y * e₃, h1, Or.inr (by rw [mul_assoc, h33, mul_one])⟩
  refine gen4_of_selfCentralizing_e8 hMW hT (E := E) (sup_le hVT (zpowers_le.mpr h3T))
    (fun y hy y' hy' => ?_) (fun y hy => ?_) hE8 (fun y hyT hy => ?_)
  · obtain ⟨v, hv, hyv | hyv⟩ := hform y hy <;> rw [hyv]
    · exact mem_centralizer_iff.mp (mem_inf.mp (hEC hy')).1 v hv
    · have h1 := mem_centralizer_iff.mp (mem_inf.mp (hEC hy')).1 v hv
      have h2 := mem_centralizer_singleton_iff.mp (mem_inf.mp (hEC hy')).2
      calc v * e₃ * y' = v * (e₃ * y') := mul_assoc _ _ _
        _ = v * (y' * e₃) := by rw [h2]
        _ = v * y' * e₃ := (mul_assoc _ _ _).symm
        _ = y' * v * e₃ := by rw [h1]
        _ = y' * (v * e₃) := mul_assoc _ _ _
  · obtain ⟨v, hv, hyv | hyv⟩ := hform y hy <;> rw [hyv]
    · exact hVsq v hv
    · rw [show v * e₃ * (v * e₃) = v * (e₃ * v) * e₃ by group, ← hV3 v hv,
        show v * (v * e₃) * e₃ = (v * v) * (e₃ * e₃) by group, hVsq v hv, h33, one_mul]
  · have hy1 := hy e₁ (mem_sup_left ((hVmem e₁).mpr (Or.inr (Or.inl rfl))))
    have hy2 := hy e₂ (mem_sup_left ((hVmem e₂).mpr (Or.inr (Or.inr (Or.inl rfl)))))
    have hy3 := hy e₃ (mem_sup_right (mem_zpowers e₃))
    rcases hcent y hyT hy1 hy2 hy3 with h1 | h1
    · exact mem_sup_left ((hVmem y).mpr h1)
    · rw [show y = y * e₃ * e₃ by rw [mul_assoc, h33, mul_one]]
      exact mul_mem (mem_sup_left ((hVmem _).mpr h1)) (mem_sup_right (mem_zpowers e₃))

namespace WreathCfg

variable {T X X' : Subgroup G} {x a s : G} (h : WreathCfg T X X' x a s)
include h

theorem gen4 (hMW : MacWilliamsStatement) (hT : IsSylowOf 2 T ⊤) : GH74.Gen4 G := by
  have hx'X' := h.sX x h.xX
  have ha'X' := h.sX a h.aX
  have hpS : x * (s * x * s) ∈ X ⊔ X' := mul_mem (mem_sup_left h.xX) (mem_sup_right hx'X')
  have hrS : a * (s * a * s) ∈ X ⊔ X' := mul_mem (mem_sup_left h.aX) (mem_sup_right ha'X')
  have ha1 : a ≠ 1 := fun h1 => by
    obtain ⟨d, -, hd⟩ := h.anc
    rw [h1, mul_one, one_mul] at hd
    exact hd rfl
  have hne1 : ∀ c ∈ X, c ≠ 1 → c * (s * c * s) ≠ 1 := by
    intro c hc hc1 h1
    have h2 : c ∈ X ⊓ X' := by
      refine mem_inf.mpr ⟨hc, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem (h.sX c hc)
    rw [h.bot, mem_bot] at h2
    exact hc1 h2
  have hpr : x * (s * x * s) ≠ a * (s * a * s) := by
    intro h1
    obtain ⟨h2, -⟩ := eq_of_mul_eq_mul_of_disjoint h.bot h.xX h.aX hx'X' ha'X' h1
    obtain ⟨d, hd, hda⟩ := h.anc
    rw [← h2] at hda
    exact hda (h.xZ d hd)
  have hsV : ¬ (s = x * (s * x * s) * (a * (s * a * s)) ∨ s = x * (s * x * s) ∨
      s = a * (s * a * s) ∨ s = 1) := by
    rintro (h1 | h1 | h1 | h1) <;> apply h.s_not_mem <;> rw [h1]
    · exact mul_mem hpS hrS
    · exact hpS
    · exact hrS
    · exact one_mem _
  refine gen4_of_three_involutions hMW hT (mul_mem (h.XT h.xX) (h.X'T hx'X'))
    (mul_mem (h.XT h.aX) (h.X'T ha'X')) h.sT (h.diag_sq h.xX h.x2) (h.diag_sq h.aX h.a2) h.s2
    (h.diag_comm h.xX h.aX (h.xZ a h.aX).symm) (h.s_comm_mul_conj h.xX).symm
    (h.s_comm_mul_conj h.aX).symm (hne1 x h.xX h.x1) (hne1 a h.aX ha1) hpr hsV ?_
  intro y hyT hyp hyr hys
  rcases h.mem_or_mul_mem_of_mem_N (h.mem_N_of_commute hyT hyp) with hyS | hyS
  · exact Or.inl (h.eq_of_commute_s_diag hyS hys hyr)
  · right
    have hsr := (h.s_comm_mul_conj h.aX).symm
    refine h.eq_of_commute_s_diag hyS (by
      calc y * s * s = y := by rw [mul_assoc, h.s2, mul_one]
        _ = s * (s * y) := by rw [← mul_assoc, h.s2, one_mul]
        _ = s * (y * s) := by rw [hys]) ?_
    calc y * s * (a * (s * a * s)) = y * (s * (a * (s * a * s))) := mul_assoc _ _ _
      _ = y * (a * (s * a * s) * s) := by rw [hsr]
      _ = y * (a * (s * a * s)) * s := (mul_assoc _ _ _).symm
      _ = a * (s * a * s) * y * s := by rw [hyr]
      _ = a * (s * a * s) * (y * s) := mul_assoc _ _ _

end WreathCfg

end CFSG.ComponentClassification.Foote5
