module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57J
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57H
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57I

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers_sq {v x : G} (hv2 : v * v = 1) (hx : x ∈ zpowers v) :
    x = 1 ∨ x = v := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have hvo : v ^ (2 : ℤ) = 1 := by rw [zpow_two, hv2]
  rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
  · left
    rw [zpow_mul, hvo, one_zpow]
  · right
    rw [zpow_add, zpow_mul, hvo, one_zpow, one_mul, zpow_one]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem lin_of_mem_conjugate_Q (hFC : Foote5FieldCentralizer) (h𝕊 : FooteSimpleType 𝕊)
    (hD : Foote5AutData 𝕊 Lin) (hQ4 : Nat.card Q = 4) (hQsq : ∀ q ∈ Q, q * q = 1) {s : G}
    (hsN : s ∈ normalizer (S : Set G)) (hbot : Q ⊓ conjugate Q s = ⊥)
    (hcomm : ∀ c ∈ Q, ∀ d ∈ conjugate Q s, c * d = d * c) :
    ∀ v ∈ conjugate Q s, actG L ε v ∈ Lin := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro v hv
  by_contra hβ
  have hvS : v ∈ S := h.conjugate_Q_le hsN hv
  have hvN := h.S_le hvS
  have hv2 : v * v = 1 := conjugate_sq_eq_one hQsq hv
  have hv1 : v ≠ 1 := fun h1 => hβ (by rw [h1, actG_one]; exact one_mem _)
  have hvQ : ∀ q ∈ Q, q * v = v * q := fun q hq => hcomm q hq v hv
  have hvL : v ∉ L := fun h1 => hβ (hD.inn_le (by
    rw [actG_of_mem_self ε h1]
    exact ⟨_, rfl⟩))
  obtain ⟨X, hXfix, ⟨φ⟩⟩ := h.exists_a4_fixed ε hFC h𝕊 hD hvS hv2 hβ
  obtain ⟨c₀, hc₀K, u₁, hu₁M, u₂, hu₂M, hc₀L, hu₁L, hu₂L, hu₁2, hu₂2, hu₁₂, ha₁, ha₂, hne,
    -, hc1, hc2⟩ := h.exists_involution_lifts_a4 ε hvS hvQ hXfix φ
  set K := liftCent5 L Q v with hKdef
  obtain ⟨y₁, hy₁K, hy₁N, hy₁fix⟩ := exists_normalizing_of_fourgroup ε (K := K) hc₀K hu₁M hu₂M
    hc₀L hu₁L hu₂L hu₁2 hu₂2 hu₁₂ ha₁ ha₂ hne hc1 hc2
  set W₁ := kleinFourOfCommutingInvolutions u₁ u₂ hu₁2 hu₂2 hu₁₂ with hW₁def
  have hu₁1 : u₁ ≠ 1 := fun h1 => ha₁ (by
    rw [show (⟨u₁, hu₁L⟩ : L) = 1 from Subtype.ext h1, map_one])
  have hu₂1 : u₂ ≠ 1 := fun h1 => ha₂ (by
    rw [show (⟨u₂, hu₂L⟩ : L) = 1 from Subtype.ext h1, map_one])
  have hu₁u₂ : u₁ ≠ u₂ := fun h1 => hne (by
    congr 1
    exact Subtype.ext h1)
  have hW₁4 : Nat.card W₁ = 4 :=
    (isKleinFour_kleinFourOfCommutingInvolutions u₁ u₂ hu₁2 hu₂2 hu₁1 hu₂1 hu₁u₂ hu₁₂).card_four
  have hW₁sq : ∀ w ∈ W₁, w * w = 1 := by
    intro w hw
    rcases (mem_kleinFour_iff hu₁2 hu₂2 hu₁₂).mp hw with rfl | rfl | rfl | rfl
    · rw [show u₁ * u₂ * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ by group, ← hu₁₂,
        show u₁ * (u₁ * u₂) * u₂ = (u₁ * u₁) * (u₂ * u₂) by group, hu₁2, hu₂2, one_mul]
    · exact hu₁2
    · exact hu₂2
    · exact one_mul 1
  have hKK : ⁅K, K⁆ ≤ K := commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
  have hW₁M : W₁ ≤ ⁅K, K⁆ := by
    intro w hw
    rcases (mem_kleinFour_iff hu₁2 hu₂2 hu₁₂).mp hw with rfl | rfl | rfl | rfl
    · exact mul_mem hu₁M hu₂M
    · exact hu₁M
    · exact hu₂M
    · exact one_mem _
  have hW₁K : W₁ ≤ K := hW₁M.trans hKK
  have hKcent : ∀ k ∈ K, ∀ p ∈ Q ⊔ zpowers v, p * k = k * p := fun k hk p hp =>
    mem_centralizer_iff.mp (mem_inf.mp hk).2 p hp
  have hKv : ∀ k ∈ K, k * v = v * k := fun k hk =>
    (hKcent k hk v (mem_sup_right (mem_zpowers v))).symm
  have hKQ : ∀ k ∈ K, ∀ q ∈ Q, q * k = k * q := fun k hk q hq =>
    hKcent k hk q (mem_sup_left hq)
  obtain ⟨hL₁, hL₁F, hQsC, hQsSyl⟩ := h.footeF_conjugate_data hQ4 hQsq hv hv1
  set L₁ := footeF L₀ v with hL₁def
  have hCvN : centralizer ({v} : Set G) ≤ normalizer (L₁ : Set G) :=
    le_normalizer_of_mem_footeFamilyOf h.sec4.huniq hL₁ hL₁F
  have hKN : K ≤ normalizer (L₁ : Set G) := fun k hk =>
    hCvN (mem_centralizer_singleton_iff.mpr (hKv k hk))
  have hQN : Q ≤ normalizer (L₁ : Set G) := fun q hq =>
    hCvN (mem_centralizer_singleton_iff.mpr (hvQ q hq))
  obtain ⟨-, ⟨e₁⟩⟩ := isSimpleGroup_quotient_of_mem_footeFamilyOf h.sec4.hGA h.sec4.hGC
    h.sec4.hSA h.sec4.footeFamilyType h.sec4.hrank2 hL₁ hL₁F
  obtain ⟨e₀⟩ := h.quotient_simple.2
  set ε₁ : L₁ ⧸ pPrimeCore 2 L₁ ≃* 𝕊 := e₁.trans (e₀.symm.trans ε) with hε₁
  have hvC : v ∈ coreActionKernel L₁ := hQsC hv
  have hQC : Q ⊓ coreActionKernel L₁ = ⊥ := by
    by_contra hne'
    obtain ⟨⟨q, hqm⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
    have hq1' : q ≠ 1 := fun h1 => hq1 (Subtype.ext h1)
    have hqQ := (mem_inf.mp hqm).1
    have hcq : ∀ c ∈ conjugate Q s, ∀ d ∈ zpowers q, c * d = d * c := by
      intro c hc d hd
      rcases eq_one_or_eq_of_mem_zpowers_sq (hQsq q hqQ) hd with rfl | rfl
      · rw [mul_one, one_mul]
      · exact (hcomm d hqQ c hc).symm
    have hdisj : conjugate Q s ⊓ zpowers q = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases eq_one_or_eq_of_mem_zpowers_sq (hQsq q hqQ) (mem_inf.mp hx).2 with rfl | rfl
      · exact one_mem _
      · have h1 : x ∈ Q ⊓ conjugate Q s := mem_inf.mpr ⟨hqQ, (mem_inf.mp hx).1⟩
        rwa [hbot] at h1
    have hq2 : orderOf q = 2 := orderOf_eq_prime (by rw [sq]; exact hQsq q hqQ) hq1'
    have hF8 : Nat.card ↥(conjugate Q s ⊔ zpowers q) = 8 := by
      rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (conjugate Q s)
        (zpowers q) (le_normalizer_of_commute hcq) (disjoint_iff.mpr hdisj),
        card_conjugate_eq_card, hQ4, Nat.card_zpowers, hq2]
    have hFS : conjugate Q s ⊔ zpowers q ≤ S :=
      sup_le (h.conjugate_Q_le hsN) (zpowers_le.mpr (h.QS hqQ))
    have h1 := card_le_twoPart (h.isPGroup_S.to_le hFS)
      (sup_le hQsC (zpowers_le.mpr (mem_inf.mp hqm).2))
    rw [hF8, twoPart, ← hQsSyl.card_eq, card_conjugate_eq_card, hQ4] at h1
    omega
  have hQt : IsKleinFour (actImage L₁ ε₁ Q) := by
    have h1 := card_eq_card_inf_mul_card_actImage ε₁ hQN
    rw [hQC, card_bot, one_mul, hQ4] at h1
    refine isKleinFour_of_card_four_sq h1.symm fun α hα => ?_
    obtain ⟨q, hq, rfl⟩ := (mem_actImage ε₁ hQN).mp hα
    rw [← actG_mul ε₁ (hQN hq) (hQN hq), hQsq q hq, actG_one]
  have hW₁C : ∀ w ∈ W₁, w ∈ coreActionKernel L₁ → w = 1 := by
    intro w hw hwC
    by_contra hw1
    have hw' : y₁ * w * y₁⁻¹ ∈ W₁ := hy₁N w hw
    have hw'C : y₁ * w * y₁⁻¹ ∈ coreActionKernel L₁ :=
      (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel L₁ (hKN hy₁K)) w).mp
        hwC
    have hww' : w ≠ y₁ * w * y₁⁻¹ := fun h1 => hw1 (hy₁fix w hw h1.symm)
    have hw'1 : y₁ * w * y₁⁻¹ ≠ 1 := fun h1 => hw1 (by
      calc w = y₁⁻¹ * (y₁ * w * y₁⁻¹) * y₁ := by group
        _ = 1 := by rw [h1]; group)
    have hW₁C' : W₁ ≤ coreActionKernel L₁ := by
      intro x hx
      rcases eq_of_mem_four hW₁4 hW₁sq hw hw' hw1 hw'1 hww' hx with rfl | rfl | rfl | rfl
      · exact mul_mem hwC hw'C
      · exact hwC
      · exact hw'C
      · exact one_mem _
    have hcv : ∀ c ∈ W₁, ∀ d ∈ zpowers v, c * d = d * c := by
      intro c hc d hd
      rcases eq_one_or_eq_of_mem_zpowers_sq hv2 hd with rfl | rfl
      · rw [mul_one, one_mul]
      · exact hKv c (hW₁K hc)
    have hdisj : W₁ ⊓ zpowers v = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases eq_one_or_eq_of_mem_zpowers_sq hv2 (mem_inf.mp hx).2 with rfl | rfl
      · exact one_mem _
      · exact absurd (mem_inf.mp (hW₁K (mem_inf.mp hx).1)).1 hvL
    have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
    have hF8 : Nat.card ↥(W₁ ⊔ zpowers v) = 8 := by
      rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer W₁ (zpowers v)
        (le_normalizer_of_commute hcv) (disjoint_iff.mpr hdisj), hW₁4, Nat.card_zpowers, hvo]
    have hFsq : ∀ x ∈ W₁ ⊔ zpowers v, x ^ 2 = 1 := by
      intro x hx
      obtain ⟨c, hc, d, hd, rfl⟩ := exists_mul_of_mem_sup_commute hcv hx
      rcases eq_one_or_eq_of_mem_zpowers_sq hv2 hd with rfl | rfl
      · rw [mul_one, sq]
        exact hW₁sq c hc
      · rw [sq, show c * d * (c * d) = c * (d * c) * d by group, ← hcv c hc d hd,
          show c * (c * d) * d = (c * c) * (d * d) by group, hW₁sq c hc, hv2, one_mul]
    have h3 := Foote47.three_le_pRank_of_card_eight (sup_le hW₁C' (zpowers_le.mpr hvC)) hFsq hF8
    have h4 := h.rankC _ hL₁F
    omega
  have hZ := h.center_eq_bot ε
  have hinj : Function.Injective (MulAut.conj : 𝕊 →* MulAut 𝕊) := by
    intro a b hab
    have h1 : b⁻¹ * a ∈ center 𝕊 := by
      rw [mem_center_iff]
      intro g
      have h2 := congrArg (fun φ : MulAut 𝕊 => φ g) hab
      simp only [MulAut.conj_apply] at h2
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
        _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h2]
        _ = b⁻¹ * a * g := by group
    rw [hZ, mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  have hW₁N : W₁ ≤ normalizer (L₁ : Set G) := hW₁K.trans hKN
  set Wt := actImage L₁ ε₁ W₁ with hWt
  have hWtinn : Wt ≤ (MulAut.conj : 𝕊 →* MulAut 𝕊).range := by
    intro α hα
    obtain ⟨w, hw, rfl⟩ := (mem_actImage ε₁ hW₁N).mp hα
    exact mem_innAut_of_mem_commutator hD ε₁ hKN (hW₁M hw)
  set W₀ := Wt.comap (MulAut.conj : 𝕊 →* MulAut 𝕊) with hW₀
  have hWt4 : Nat.card Wt = 4 := by
    have h1 := card_eq_card_inf_mul_card_actImage ε₁ hW₁N
    have h2 : W₁ ⊓ coreActionKernel L₁ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact hW₁C x (mem_inf.mp hx).1 (mem_inf.mp hx).2
    rw [h2, card_bot, one_mul, hW₁4] at h1
    exact h1.symm
  have hW₀4 : Nat.card W₀ = 4 := by
    rw [← hWt4, Nat.card_congr (W₀.equivMapOfInjective _ hinj).toEquiv, hW₀,
      map_comap_eq_self hWtinn]
  have hconjW : ∀ x ∈ W₀, ∃ w ∈ W₁, MulAut.conj x = actG L₁ ε₁ w := by
    intro x hx
    obtain ⟨w, hw, hwx⟩ := (mem_actImage ε₁ hW₁N).mp (show MulAut.conj x ∈ Wt from hx)
    exact ⟨w, hw, hwx.symm⟩
  have hW₀sq : ∀ x ∈ W₀, x * x = 1 := by
    intro x hx
    obtain ⟨w, hw, hwx⟩ := hconjW x hx
    apply hinj
    rw [map_mul, hwx, ← actG_mul ε₁ (hW₁N hw) (hW₁N hw), hW₁sq w hw, actG_one, map_one]
  have hW₀K : IsKleinFour W₀ := isKleinFour_of_card_four_sq hW₀4 hW₀sq
  set γ := actG L₁ ε₁ y₁ with hγ
  have hy₁N1 := hKN hy₁K
  have hγW : ∀ x ∈ W₀, γ x ∈ W₀ := by
    intro x hx
    obtain ⟨w, hw, hwx⟩ := hconjW x hx
    show MulAut.conj (γ x) ∈ Wt
    rw [← mulAut_mul_conj_mul_inv, hwx, hγ, ← actG_inv ε₁ hy₁N1, ← actG_mul ε₁ hy₁N1 (hW₁N hw),
      ← actG_mul ε₁ (mul_mem hy₁N1 (hW₁N hw)) (inv_mem hy₁N1)]
    exact actG_mem_actImage ε₁ hW₁N (hy₁N w hw)
  have hγfix : ∀ x ∈ W₀, γ x = x → x = 1 := by
    intro x hx hγx
    obtain ⟨w, hw, hwx⟩ := hconjW x hx
    have h1 : actG L₁ ε₁ (y₁ * w * y₁⁻¹) = actG L₁ ε₁ w := by
      rw [actG_mul ε₁ (mul_mem hy₁N1 (hW₁N hw)) (inv_mem hy₁N1), actG_mul ε₁ hy₁N1 (hW₁N hw),
        actG_inv ε₁ hy₁N1, ← hγ, ← hwx, mulAut_mul_conj_mul_inv, hγx]
    have h2 : actG L₁ ε₁ (y₁ * w * y₁⁻¹ * w⁻¹) = 1 := by
      rw [actG_mul ε₁ (mul_mem (mul_mem hy₁N1 (hW₁N hw)) (inv_mem hy₁N1)) (inv_mem (hW₁N hw)),
        h1, actG_inv ε₁ (hW₁N hw), mul_inv_cancel]
    have h3 := (actG_eq_one_iff ε₁ (mul_mem (mul_mem (mul_mem hy₁N1 (hW₁N hw))
      (inv_mem hy₁N1)) (inv_mem (hW₁N hw)))).mp h2
    have h4 := hW₁C _ (mul_mem (hy₁N w hw) (inv_mem hw)) h3
    rw [mul_inv_eq_one] at h4
    have h5 := hy₁fix w hw h4
    apply hinj
    rw [hwx, h5, actG_one, map_one]
  have hE : ∀ α ∈ actImage L₁ ε₁ Q, α * γ = γ * α ∧ ∀ x ∈ W₀, α x = x := by
    intro α hα
    obtain ⟨q, hq, rfl⟩ := (mem_actImage ε₁ hQN).mp hα
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hγ, ← actG_mul ε₁ (hQN hq) hy₁N1, ← actG_mul ε₁ hy₁N1 (hQN hq), hKQ y₁ hy₁K q hq]
    · obtain ⟨w, hw, hwx⟩ := hconjW x hx
      apply hinj
      rw [← mulAut_mul_conj_mul_inv, hwx, ← actG_inv ε₁ (hQN hq),
        ← actG_mul ε₁ (hQN hq) (hW₁N hw), ← actG_mul ε₁ (mul_mem (hQN hq) (hW₁N hw))
          (inv_mem (hQN hq)), hKQ w (hW₁K hw) q hq, mul_inv_cancel_right]
  exact (hFC 𝕊 h𝕊).2 W₀ hW₀K γ hγW hγfix _ hE hQt

end Sec5

end CFSG.ComponentClassification.Foote5
