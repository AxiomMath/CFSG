module

public import CFSG.LargeExtraspecial.S14Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem isSimpleGroup_RmodN_of_occurs {t : S.O} {c : Config} (hocc : c.Occurs S g t) :
    IsSimpleGroup (RmodN S g t) := by
  have hΩ : ∀ d, 6 ≤ d → RNOmega S g t d → IsSimpleGroup (RmodN S g t) := by
    rintro d hd ⟨H, C, ht, ht1, hVQ, hΩ, hdim⟩
    exact ((S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ (by omega)).1
  have hSp : ∀ d, 6 ≤ d → RNSp S g t d → IsSimpleGroup (RmodN S g t) := by
    rintro d hd ⟨H, C, ht, ht1, hVQ, hSp, hdim⟩
    exact ((S45Q.hyp45Q H C).sp ht ht1 hVQ hSp (by omega)).1
  obtain ⟨hh, -, -⟩ := hocc
  cases c with
  | omegaMinus8 => exact hΩ 8 (by norm_num) hh.1
  | omegaMinus6 => exact hΩ 6 (by norm_num) hh.1
  | omegaPlus12 => exact hΩ 12 (by norm_num) hh.1
  | omegaPlus10 => exact hΩ 10 (by norm_num) hh.1
  | omegaPlus8a => exact hΩ 8 (by norm_num) hh.1
  | omegaPlus8b => exact hΩ 8 (by norm_num) hh.1
  | omegaPlus6 => exact hΩ 6 (by norm_num) hh.1
  | sp6 => exact hSp 6 (by norm_num) hh
  | sp8 => exact hSp 8 (by norm_num) hh

theorem false_of_sub_omega (hCorB : S8.TimmesfeldCorBInput) (hFacts : S8.CorBListFacts)
    (hCE : CentralExtInput.{0}) {t : S.O} (hSt : Stage S g t) {d : ℕ} (hΩ : RNOmega S g t d)
    (hd : 10 ≤ d ∨ (d = 8 ∧ ¬ RNPlus S g t))
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t) : False := by
  obtain ⟨H, C, ht, ht1, hVQ, hΩ, hdim⟩ := hΩ
  have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
  obtain ⟨D⟩ := S8.Std.nonempty hCE hNo hΩ
  have hpl := rnPlus_iff_not_isMinus D
  have hm := D.hdim
  have hm8 : 8 ≤ 2 * D.m := by rcases hd with hd | ⟨hd, -⟩ <;> omega
  rcases S8.timmesfeld_8_1 hCorB hFacts hCE (irr_of_not_isReducible hSt.irr) hNo hΩ D
      hSt.abar_ne (fun h => by have := h.1; omega) with ⟨x, hx, hL, hN⟩ | h | h | ⟨h4, hmin⟩
  · exact hN (hsub x hx hL)
  · have := h.1
    omega
  · omega
  · rcases hd with hd | ⟨hd8, hplus⟩
    · omega
    · exact hplus (hpl.mpr hmin)

theorem config_of_sub (hCorB : S8.TimmesfeldCorBInput) (hFacts : S8.CorBListFacts)
    (hCE : CentralExtInput.{0}) (h83 : S8_3Stmt) [IsSimpleGroup G] {t : S.O} {c : Config}
    (hSt : Stage S g t) (hocc : c.Occurs S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t) :
    c = .omegaMinus6 ∨ c = .omegaPlus8a ∨ c = .omegaPlus6 := by
  have hnw : ¬ ∃ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g ∧ x * t * x⁻¹ ∉ Nbar S g t :=
    fun ⟨x, hx, hL, hN⟩ => hN (hsub x hx hL)
  have hSp : ∀ d, 6 ≤ d → RNSp S g t d → False := by
    rintro d hd ⟨H, C, ht, ht1, hVQ, hSp, hdim⟩
    have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
    rcases S9.timmesfeld_9_1 hCorB hFacts hCE (irr_of_not_isReducible hSt.irr) H hNo C ht ht1
        hVQ hSp hSt.abar_ne with h | h
    · omega
    · exact hnw h
  obtain ⟨hh, hw, -⟩ := hocc
  cases c with
  | omegaMinus8 => exact (false_of_sub_omega hCorB hFacts hCE hSt hh.1 (Or.inr ⟨rfl, hh.2⟩)
      hsub).elim
  | omegaMinus6 => exact Or.inl rfl
  | omegaPlus12 => exact (false_of_sub_omega hCorB hFacts hCE hSt hh.1 (Or.inl (by norm_num))
      hsub).elim
  | omegaPlus10 => exact (false_of_sub_omega hCorB hFacts hCE hSt hh.1 (Or.inl le_rfl)
      hsub).elim
  | omegaPlus8a => exact Or.inr (Or.inl rfl)
  | omegaPlus8b =>
    exfalso
    have hw' : S.width = 16 := hw
    obtain ⟨-, -, -, -, -, -, h8⟩ := hh.1
    rcases h83 G S g t hSt (Or.inr (Or.inr hh)) with h | ⟨⟨-, -, -, -, -, -, h6⟩, -, -⟩ |
        ⟨-, -, h12⟩
    · exact hnw h
    · omega
    · omega
  | omegaPlus6 => exact Or.inr (Or.inr rfl)
  | sp6 => exact (hSp 6 le_rfl hh).elim
  | sp8 => exact (hSp 8 (by norm_num) hh).elim

end CFSG.LargeExtraspecial.S14
