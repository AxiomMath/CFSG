module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue76

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

namespace Cfg7

theorem z_mem_Pz (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) : z ∈ Pz S z := by
  rw [h.Pz_eq_sup hII]
  exact mem_sup_left (h.z_mem_P hII (Or.inl rfl))

theorem Pz_le_S1 (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) : Pz S z ≤ S1 S K₁ := by
  rw [h.Pz_eq_sup hII]
  exact h.P_le_S1 hII

theorem PQ_eq (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) (hc73 : Concl73 z S K₁ K₂)
    {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) : Pof S K ⊔ Qof S K = Pz S z := by
  rw [h.Pz_eq_sup hII]
  rcases hK with rfl | rfl
  · rw [hc73.2.1]
  · rw [hc73.2.2, sup_comm]

theorem concl72_of_props (hII : II4_4_4_center) (h12d : IVK_1_2d_lifted)
    (h : Cfg7 G z S K₁ K₂ t u q) (hc73 : Concl73 z S K₁ K₂)
    (hidx : (Pz S z).relIndex (S1 S K₁) = 2) {w : G} (hwS₁ : w ∈ S1 S K₁) (hwP : w ∉ Pz S z)
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwt : t * w = w * t) :
    Concl72abcf z S K₁ K₂ t q w := by
  have hwS : w ∈ S := hwS₁.1
  have hPS₁ : Pz S z ≤ S1 S K₁ := h.Pz_le_S1 hII
  have hPS : Pz S z ≤ S := hPS₁.trans S1_le_S
  have ht2 : t * t = 1 := h.t_sq
  have htP : t ∉ Pz S z := fun ht => h.t_nS1 (hPS₁ ht)
  have hwo : orderOf w = 2 := orderOf_eq_prime (by simpa [pow_two] using hw2) hw1
  have hYle : Ysub t w ≤ S := sup_le (zpowers_le.2 h.ch.t_mem) (zpowers_le.2 hwS)
  have hPnorm := h.S_normalizes_P hII
  refine ⟨hwS, Or.inr hwo, hwt, ⟨?_, ?_⟩, ?_, h.ch.t_swap, ?_⟩
  ·
    rw [eq_bot_iff]
    rintro x ⟨hxP, hxY⟩
    rw [Subgroup.mem_bot]
    rcases A.mem_sup_zpowers_two ht2 hw2 hwt hxY with h1 | h1 | h1 | h1
    · exact h1
    · rw [h1] at hxP; exact absurd hxP htP
    · rw [h1] at hxP; exact absurd hxP hwP
    · rw [h1] at hxP
      exfalso
      apply h.t_nS1
      have := (S1 S K₁).mul_mem (hPS₁ hxP) ((S1 S K₁).inv_mem hwS₁)
      simpa using this
  ·
    apply le_antisymm
    · intro s hs
      by_cases hsS₁ : s ∈ S1 S K₁
      · have hp := A.relIndex_two_pigeon hidx hwS₁ hsS₁
        rcases hp with h1 | h1 | h1
        · exact absurd h1 hwP
        · exact mem_sup_left h1
        · have e : s = w * (w⁻¹ * s) := by group
          rw [e]
          exact mul_mem (mem_sup_right (mem_sup_right (mem_zpowers w))) (mem_sup_left h1)
      · have hp := A.relIndex_two_pigeon h.S1_relIndex h.ch.t_mem hs
        rcases hp with h1 | h1 | h1
        · exact absurd h1 h.t_nS1
        · exact absurd h1 hsS₁
        · have hq : t⁻¹ * s ∈ Pz S z ⊔ Ysub t w := by
            have hq1 := A.relIndex_two_pigeon hidx hwS₁ h1
            rcases hq1 with k1 | k1 | k1
            · exact absurd k1 hwP
            · exact mem_sup_left k1
            · have e : t⁻¹ * s = w * (w⁻¹ * (t⁻¹ * s)) := by group
              rw [e]
              exact mul_mem (mem_sup_right (mem_sup_right (mem_zpowers w))) (mem_sup_left k1)
          have e : s = t * (t⁻¹ * s) := by group
          rw [e]
          exact mul_mem (mem_sup_right (mem_sup_left (mem_zpowers t))) hq
    · exact sup_le hPS hYle
  ·
    apply le_antisymm
    · intro s hs
      have hp := A.relIndex_two_pigeon hidx hwS₁ hs
      rcases hp with h1 | h1 | h1
      · exact absurd h1 hwP
      · exact mem_sup_left h1
      · have e : s = w * (w⁻¹ * s) := by group
        rw [e]
        exact mul_mem (mem_sup_right (mem_zpowers w)) (mem_sup_left h1)
    · exact sup_le hPS₁ (zpowers_le.2 hwS₁)
  ·
    intro _ K hK
    have hK' : K = K₁ ∨ K = K₂ := by simpa using hK
    have hKC : K ≤ centralizer ({z} : Set G) := h.K_le_C hII hK'
    have hnorm : w ∈ normalizer (K : Set G) := by
      rcases hK' with rfl | rfl
      · exact hwS₁.2
      · exact h.S1_norm₂ hII hwS₁
    have hSL2 : HatSL2 K q := by
      rcases hK' with rfl | rfl
      · exact h.ch.hq₁
      · exact h.ch.hq₂
    have hPQ := h.PQ_eq hII hc73 hK'
    have hnotinner : ¬ InducesInner w K := by
      rintro ⟨k, hkK, hk⟩
      apply hwP
      have hwX : w ∈ XK z K := by
        have e : w = (w * k⁻¹) * k := by group
        rw [e]
        exact mul_mem (mem_sup_right (Subgroup.mem_inf.2 ⟨hk,
          (centralizer ({z} : Set G)).mul_mem (h.S_le_C hII hwS)
            ((centralizer ({z} : Set G)).inv_mem (hKC hkK))⟩)) (mem_sup_left hkK)
      have := h.inf_XK_le hII hK' w hwS hwX
      rwa [hPQ] at this
    have hnotf : ¬ InducesFAut w K := by
      intro hf
      have hcond : Cond6a S K := by
        rcases hK' with rfl | rfl
        · exact h.std.a₁
        · exact h.std.a₂
      have hcs : w ∈ cSec K := hcond w hwS hf
      apply hwP
      have : w ∈ Pof S K ⊔ Qof S K := mem_sup_right ⟨hwS, hcs⟩
      rwa [hPQ] at this
    exact h12d G z S K₁ K₂ q h.std.std h.ch.q_odd K hK hSL2 w hwS hwo hnorm hnotinner hnotf

end Cfg7

theorem lemma_7_8 (hII : II4_4_4_center) (h12d : IVK_1_2d_lifted) : Lemma7_8 := by
  intro G _ _ z S K₁ K₂ t u q h hc73 hc74 hidx D hD hdih y hyD hyP hyo w hw
  have hyS₁ : y ∈ S1 S K₁ := hD.le hyD
  have hDE : D ≤ S ⊓ centralizer ({t} : Set G) := le_sup_right.trans hD.prod.1.le
  have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.1 (hDE hyD).2
  have hyS : y ∈ S := hyS₁.1
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_C hII hyS)
  have hzP : z ∈ Pz S z := h.z_mem_Pz hII
  have hy2 : y * y = 1 := mul_self_eq_one_of_orderOf_eq_two hyo
  have hy1 : y ≠ 1 := ne_one_of_orderOf_eq_two hyo
  have htz : t * z = z * t := h.t_mul_z hII
  rcases hw with rfl | hw
  · exact h.concl72_of_props hII h12d hc73 hidx hyS₁ hyP hy2 hy1 hyt.symm
  · have hw' : w = y * z := hw
    subst hw'
    have hyzS₁ : y * z ∈ S1 S K₁ := mul_mem hyS₁ (h.Pz_le_S1 hII hzP)
    have hyzP : y * z ∉ Pz S z := by
      intro hh
      apply hyP
      have := (Pz S z).mul_mem hh ((Pz S z).inv_mem hzP)
      simpa using this
    have hyz2 : (y * z) * (y * z) = 1 := by
      calc y * z * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [hyz]
        _ = (y * y) * (z * z) := by group
        _ = 1 := by rw [hy2, h.z_sq, mul_one]
    have hyz1 : y * z ≠ 1 := by
      intro hh
      apply hyzP
      rw [hh]; exact one_mem _
    have hyzt : t * (y * z) = (y * z) * t := by
      calc t * (y * z) = (t * y) * z := by group
        _ = (y * t) * z := by rw [hyt.symm]
        _ = y * (t * z) := by group
        _ = y * (z * t) := by rw [htz]
        _ = (y * z) * t := by group
    exact h.concl72_of_props hII h12d hc73 hidx hyzS₁ hyzP hyz2 hyz1 hyzt

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
