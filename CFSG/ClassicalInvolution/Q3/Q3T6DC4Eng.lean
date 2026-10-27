module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLateCfgEng
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1b
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D


open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem _root_.CFSG.ClassicalInvolution.Asc77.T3CII.Std20F.concl20_4_of_98
    (d : Std20F K K' J S R R' W V z t)
    (hcc : ∀ {a w : G}, a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K') → w ∈ W ⊓ K →
      a * w = w * a)
    (hzc : z ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K'))
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hex : Hex20 (CoreAssembly.conjClass K) K J W)
    (h98 : (∀ x ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K'), ∀ w ∈ W ⊓ K, x * w = w * x) →
      ∃ A' : Subgroup G,
        ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ centralizerModOdd (S : Subgroup G) (K ⊔ K') =
            ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ A' ∧
          ((W ⊓ J) ⊔ (W ⊓ K)) ⊓ A' = ⊥ ∧
          (∀ a ∈ A', ∀ y ∈ (W ⊓ J) ⊔ (W ⊓ K), a * y = y * a) ∧
          A' ≤ centralizerModOdd ⊤ (K ⊔ K') ∧ A' ≤ centralizerModOdd ⊤ J)
    (htor : ∃ r ∈ R, ∃ r' ∈ R', (∀ x ∈ W, (r * r') * x * (r * r')⁻¹ = x⁻¹) ∧
      r * t * r⁻¹ = z * t) :
    Concl20_4 S K K' J z := by
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hJΩ : J ∈ CoreAssembly.conjClass K := d.viol.mem
  have hzK := d.viol.hzK
  have hzJ := d.viol.hzJ
  set A := centralizerModOdd (S : Subgroup G) (K ⊔ K') with hA
  have hY : (W ⊓ J) ⊔ (W ⊓ K) = W := by rw [sup_comm, ← hex.hW]
  obtain ⟨A', hWA, hWA', hcomm', hA'M, hA'J⟩ := h98 (fun x hx w hw => hcc hx hw)
  rw [hY] at hWA hWA' hcomm'
  have hAS : A ≤ (S : Subgroup G) := fun x hx => hx.1
  have hA'S : A' ≤ (S : Subgroup G) :=
    (show A' ≤ W ⊔ A from hWA ▸ le_sup_right).trans (sup_le d.hWS hAS)
  have hA'W : A' ≤ Subgroup.normalizer (W : Set G) := le_normalizer_of_commutes hcomm'
  have hJWK : W ⊓ J ≤ Subgroup.normalizer ((W ⊓ K : Subgroup G) : Set G) :=
    le_normalizer_of_commutes fun x hx y hy => hWc x hx.1 y hy.1
  have hzA : z ∈ A := hzc
  have hzpA : Subgroup.zpowers z ≤ A := Subgroup.zpowers_le.mpr hzA
  have hle : A ≤ centralizerModOdd A J ⊔ Subgroup.zpowers z := by
    intro a ha
    have haWA' : a ∈ W ⊔ A' := hWA ▸ Subgroup.mem_sup_right ha
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left W A' hA'W] at haWA'
    obtain ⟨w, hw, a', ha', rfl⟩ := haWA'
    have ha'M : a' ∈ centModOddCore (K ⊔ K') := (hA'M ha').2.2.2
    have hw_cent : w ∈ centModOddCore (K ⊔ K') := by
      have := (centModOddCore (K ⊔ K')).mul_mem
        (mem_centModOddCore_of_mem_centralizerModOdd ha)
        ((centModOddCore (K ⊔ K')).inv_mem ha'M)
      simpa using this
    have hwS : w ∈ (S : Subgroup G) := d.hWS hw
    have hwR : ∀ r ∈ R, w * r = r * w := fun r hr =>
      commutes_of_mem_centModOddCore S.isPGroup' hw_cent hwS
        (Subgroup.mem_sup_left (d.hR.1 hr)) (d.hRS hr)
    have hwR' : ∀ r ∈ R', w * r = r * w := fun r hr =>
      commutes_of_mem_centModOddCore S.isPGroup' hw_cent hwS
        (Subgroup.mem_sup_right (d.hR'.1 hr)) (d.hR'S hr)
    obtain ⟨r, hr, r', hr', hinv, hrt⟩ := htor
    have hsq : w * w = 1 := by
      have h1 : (r * r') * w * (r * r')⁻¹ = w := by
        have e1 : r' * w * r'⁻¹ = w := mul_inv_eq_iff_eq_mul.mpr (hwR' r' hr').symm
        have e2 : r * w * r⁻¹ = w := mul_inv_eq_iff_eq_mul.mpr (hwR r hr).symm
        calc (r * r') * w * (r * r')⁻¹ = r * (r' * w * r'⁻¹) * r⁻¹ := by group
          _ = w := by rw [e1, e2]
      have h2 := hinv w hw
      rw [h1] at h2
      calc w * w = w * w⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel w
    have hw' : w ∈ (W ⊓ K) ⊔ (W ⊓ J) := hex.hW ▸ hw
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (W ⊓ K) (W ⊓ J) hJWK]
      at hw'
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hw'
    have hab : b₁ * a₁ = a₁ * b₁ := hWc b₁ hb₁.1 a₁ ha₁.1
    have hsq' : (a₁ * a₁) * (b₁ * b₁) = 1 := by
      calc (a₁ * a₁) * (b₁ * b₁) = a₁ * (a₁ * b₁) * b₁ := by group
        _ = a₁ * (b₁ * a₁) * b₁ := by rw [hab]
        _ = (a₁ * b₁) * (a₁ * b₁) := by group
        _ = 1 := hsq
    have hx1 : a₁ * a₁ = (b₁ * b₁)⁻¹ := eq_inv_of_mul_eq_one_left hsq'
    have hxK : a₁ * a₁ ∈ K := K.mul_mem ha₁.2 ha₁.2
    have hxJ : a₁ * a₁ ∈ J := by rw [hx1]; exact J.inv_mem (J.mul_mem hb₁.2 hb₁.2)
    have hxS : a₁ * a₁ ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem (d.hWS ha₁.1) (d.hWS ha₁.1)
    have hKJ : K ≠ J := fun h => d.viol.ne h.symm
    have hxsq : (a₁ * a₁) * (a₁ * a₁) = 1 := by
      refine mul_self_eq_one_of_card_zpowers_le_two ?_
      exact Sec6Gen.card_le_two_of_le_inf d.late_hΩ hKΩ hJΩ hKJ (S.isPGroup'.to_le
        (Subgroup.zpowers_le.mpr hxS)) (Subgroup.zpowers_le.mpr hxK) (Subgroup.zpowers_le.mpr hxJ)
    have hxone : a₁ * a₁ = 1 := by
      rcases hzK.unique _ hxK hxsq with h1 | h1
      · exact h1
      · rcases hzJ.unique _ hxJ hxsq with h2 | h2
        · exact h2
        · exact absurd (h2.symm.trans h1) d.late_ne_inv
    have hbone : b₁ * b₁ = 1 := by
      have := hx1
      rw [hxone] at this
      exact inv_eq_one.mp this.symm
    have ha₁z : a₁ = 1 ∨ a₁ = z := hzK.unique a₁ ha₁.2 hxone
    have hb₁t : b₁ = 1 ∨ b₁ = t := hzJ.unique b₁ hb₁.2 hbone
    have hb₁1 : b₁ = 1 := by
      rcases hb₁t with h | h
      · exact h
      · exfalso
        subst h
        have hrw : r * (a₁ * b₁) * r⁻¹ = a₁ * b₁ := mul_inv_eq_iff_eq_mul.mpr (hwR r hr).symm
        have hra : r * a₁ * r⁻¹ = a₁ := by
          rcases ha₁z with h1 | h1
          · rw [h1]; group
          · rw [h1]
            exact mul_inv_eq_iff_eq_mul.mpr (hzK.commute_of_mem (d.hR.1 hr)).symm
        have h5 : r * (a₁ * b₁) * r⁻¹ = a₁ * (z * b₁) := by
          calc r * (a₁ * b₁) * r⁻¹ = (r * a₁ * r⁻¹) * (r * b₁ * r⁻¹) := by group
            _ = a₁ * (z * b₁) := by rw [hra, hrt]
        rw [h5] at hrw
        have h6 := mul_left_cancel hrw
        exact hzK.ne_one (mul_eq_right.mp h6)
    subst hb₁1
    have hwz : a₁ * 1 ∈ Subgroup.zpowers z := by
      rw [mul_one]
      rcases ha₁z with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.mem_zpowers z
    have hwA : a₁ * 1 ∈ A := hzpA hwz
    have ha'A : a' ∈ A := by
      have := A.mul_mem (A.inv_mem hwA) ha
      simpa using this
    have ha'J : a' ∈ centralizerModOdd A J := ⟨ha'A, (hA'J ha').2.1, (hA'J ha').2.2.1,
      (hA'J ha').2.2.2⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hwz) (Subgroup.mem_sup_left ha'J)
  refine ⟨le_antisymm hle (sup_le (fun x hx => hx.1) hzpA), ?_⟩
  rw [Subgroup.disjoint_def]
  intro x hxJ hxz
  rcases eq_one_or_eq_of_mem_zpowers hzK.sq hxz with h | h
  · exact h
  · exfalso
    subst h
    have hzJ' : x ∈ centralizerModOdd A J := hxJ
    have htq : x ∈ Balance.Bootstrap.trivialOnQuot J := ⟨hzJ'.2.1, hzJ'.2.2.2⟩
    exact d.viol.not_nbr (mem_omegaNbr_of_trivialOnQuotGen d.late_hΩ hKΩ hzK hJΩ d.viol.ne htq)

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
