module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterSwapTOut

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterSwapTwo

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapTwo G L f t T R₂ D d V U U₁ w s P)
include hW

theorem exists_sylow : ∃ S : Sylow 2 G, (S : Subgroup G) = swapS₂ P U T := by
  by_contra hns
  obtain ⟨z, hzN, hzS, P', hP'2, hSP', hzP'⟩ :=
    exists_normalizer_not_mem_of_not_isSylow hW.isPGroup_S₂ hns
  have hS := hW.step
  have hL := hW.level
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  have hcT : ∀ τ ∈ T, z * τ * z⁻¹ ∈ swapS₂ P U T := fun τ hτ =>
    (mem_normalizer_iff.mp hzN τ).mp (hW.le_S₂ (mem_sup_right hτ))
  have hSUP' : U ⊔ T ≤ P' := hW.le_S₂.trans hSP'
  rcases hW.conj_mem_cases hcT with h1 | h1
  · exact hzS (hW.le_S₂ (hL.muOne_mem_sup_of_conj hS hc hW.mu hK hμ hP'2 hSUP' hzP' h1))
  ·
    have hzTS : ∀ τ ∈ T, z * τ * z⁻¹ ∈ U ⊔ T := by
      intro τ hτ
      by_contra hh
      have hhS₂ := hcT τ hτ
      obtain ⟨-, hhw⟩ := hW.conj_of_not_mem hhS₂ hh
      have hhx : (z * τ * z⁻¹) * (z * t * z⁻¹) = (z * t * z⁻¹) * (z * τ * z⁻¹) :=
        hW.commute_of_mem_map ⟨τ, hτ, by simp⟩
      have h2 : (z * τ * z⁻¹) * (z * t * z⁻¹) * (z * τ * z⁻¹)⁻¹ * t⁻¹ ∈ U₁ := by
        rw [show (z * τ * z⁻¹) * (z * t * z⁻¹) * (z * τ * z⁻¹)⁻¹ * t⁻¹ =
          ((z * τ * z⁻¹) * (z * t * z⁻¹ * w⁻¹) * (z * τ * z⁻¹)⁻¹) *
            ((z * τ * z⁻¹) * w * (z * τ * z⁻¹)⁻¹ * t⁻¹) by group]
        exact mul_mem (hW.conj_U₁ hhS₂ h1) hhw
      have hconj : (z * τ * z⁻¹) * (z * t * z⁻¹) * (z * τ * z⁻¹)⁻¹ = z * t * z⁻¹ := by
        rw [hhx]; group
      rw [hconj] at h2
      apply hW.not_mem_U₁_of_mem_T (mul_mem hW.t_mem (inv_mem hW.w_mem))
        hW.t_mul_w_inv_not_mem_T₁
      rw [show t * w⁻¹ = (z * t * z⁻¹ * t⁻¹)⁻¹ * (z * t * z⁻¹ * w⁻¹) by group]
      exact mul_mem (inv_mem h2) h1
    obtain ⟨c₁, hc₁T, hc₁⟩ := hL.muOneCent_exists_conj_eq hS hc hW.mu hK hμ hW.w_mem hW.w_sq
      hW.w_not_mem hW.w_cent hzTS h1
    have hc₁S : c₁ ∈ swapS₂ P U T := hW.le_S₂ (mem_sup_left (hL.U₁_le (hW.T₁_le_U₁ hc₁T)))
    have hy : s⁻¹ * c₁ * z ∈ T := by
      refine U3C1OuterLevelData.norm_mem_T_of_commute hS hP'2
        ((le_sup_right : T ≤ U ⊔ T).trans hSUP')
        (mul_mem (mul_mem (inv_mem (hSP' hW.s_mem_S₂)) (hSP' hc₁S)) hzP') ?_
      have e : (s⁻¹ * c₁ * z) * t * (s⁻¹ * c₁ * z)⁻¹ = t := by
        rw [show (s⁻¹ * c₁ * z) * t * (s⁻¹ * c₁ * z)⁻¹ =
          s⁻¹ * (c₁ * (z * t * z⁻¹) * c₁⁻¹) * s by group, hc₁, ← hW.conj_t]
        group
      calc (s⁻¹ * c₁ * z) * t =
            (s⁻¹ * c₁ * z) * t * (s⁻¹ * c₁ * z)⁻¹ * (s⁻¹ * c₁ * z) := by group
        _ = t * (s⁻¹ * c₁ * z) := by rw [e]
    apply hzS
    rw [show z = c₁⁻¹ * s * (s⁻¹ * c₁ * z) by group]
    exact mul_mem (mul_mem (inv_mem hc₁S) hW.s_mem_S₂) (hW.le_S₂ (mem_sup_right hy))

theorem false : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hW.step
  have hL := hW.level
  obtain ⟨hsS, hs2, hstw, -⟩ := hW.swap_facts
  obtain ⟨S, hSeq⟩ := hW.exists_sylow
  set S₂ := swapS₂ P U T with hS₂def
  have hP2 : IsPGroup 2 S₂ := hSeq ▸ S.isPGroup'
  have hPidx : ¬ 2 ∣ S₂.index := hSeq ▸ S.not_dvd_index
  have htt : t * t = 1 := by rw [← sq, hS.start.sq_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htwT : t * w ∈ T := mul_mem hW.t_mem hW.w_mem
  have htwN : t * w ∈ normalizer (U₁ : Set G) := hL.T_le htwT
  have htwU : t * w ∉ U₁ := hW.not_mem_U₁_of_mem_T htwT hW.tw_not_mem_T₁
  have htw2 : t * w * (t * w) = 1 := by
    rw [← sq, Commute.mul_pow hW.wt_comm.symm 2, hS.start.sq_eq_one, hW.w_sq, one_mul]
  set H₀ := U₁ ⊔ zpowers (t * w) with hH₀def
  set Q := H₀ ⊔ zpowers s with hQdef
  have hU₁Q : U₁ ≤ Q := le_sup_left.trans le_sup_left
  have htwQ : t * w ∈ Q := mem_sup_left (mem_sup_right (mem_zpowers _))
  have hsQ : s ∈ Q := mem_sup_right (mem_zpowers s)
  have htS₂ : t ∈ S₂ := hW.le_S₂ (mem_sup_right hW.t_mem)
  have htw' : t⁻¹ * w ∈ Q := by rw [htinv]; exact htwQ
  have htN : ∀ u ∈ U₁, t⁻¹ * u * t ∈ U₁ := fun u hu => by
    have := (mem_normalizer_iff.mp (hL.T_le (inv_mem hW.t_mem)) u).mp hu
    simpa using this
  have hcovSU : ∀ σ ∈ U ⊔ T, σ ∈ Q ∨ t⁻¹ * σ ∈ Q := by
    intro σ hσ
    rcases hW.mem_U₁_cases hσ with h1 | h1 | h1 | h1
    · exact Or.inl (hU₁Q h1)
    · right
      rw [show t⁻¹ * σ = t⁻¹ * (σ * t⁻¹) * t by group]
      exact hU₁Q (htN _ h1)
    · right
      rw [show t⁻¹ * σ = (t⁻¹ * (σ * w⁻¹) * t) * (t⁻¹ * w) by group]
      exact mul_mem (hU₁Q (htN _ h1)) htw'
    · left
      rw [show σ = (σ * (t * w)⁻¹) * (t * w) by group]
      exact mul_mem (hU₁Q h1) htwQ
  have hcov : ∀ y ∈ S₂, y ∈ Q ∨ t⁻¹ * y ∈ Q := by
    intro y hy
    rcases hW.mem_or hy with h1 | h1
    · exact hcovSU y h1
    · rcases hcovSU _ h1 with h2 | h2
      · left
        rw [show y = (y * s⁻¹) * s by group]
        exact mul_mem h2 hsQ
      · right
        rw [show t⁻¹ * y = (t⁻¹ * (y * s⁻¹)) * s by group]
        exact mul_mem h2 hsQ
  have hS₂card : Nat.card S₂ = 8 * (2 ^ f) ^ 5 := by
    have h1 := relIndex_mul_card (H := U ⊔ T) (K := S₂)
    rw [hW.relIndex_SU_S₂, inf_of_le_left hW.le_S₂, hW.card_SU] at h1
    omega
  have hH₀card : Nat.card H₀ = 2 * (2 ^ f) ^ 5 := by
    have h2 := RankOne.Endings.relIndex_sup_zpowers_eq_two htwU htwN htw2
    have h3 := relIndex_mul_card (H := U₁) (K := H₀)
    rw [h2, inf_of_le_left le_sup_left, hL.muOne_card_U₁ hS] at h3
    omega
  have hH₀S : H₀ ≤ U ⊔ T :=
    sup_le (hL.U₁_le.trans le_sup_left) (zpowers_le.mpr (mem_sup_right htwT))
  have hsH₀ : s ∉ H₀ := fun h' => hsS (hH₀S h')
  have hsN : s ∈ normalizer (H₀ : Set G) := by
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => ?_
    rw [hH₀def, sup_comm] at hy
    obtain ⟨a, ha, u, hu, rfl⟩ := ncyc_exists_mul_of_mem_sup (zpowers_le.mpr htwN) hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    have e1 : s⁻¹ * (t * w) * s = t * w := by
      calc s⁻¹ * (t * w) * s = s⁻¹ * (s * (t * w) * s⁻¹) * s := by rw [hstw]
        _ = t * w := by group
    have e2 : s⁻¹ * (t * w) ^ k * s = (t * w) ^ k := by
      rw [show s⁻¹ * (t * w) ^ k * s = s⁻¹ * (t * w) ^ k * s⁻¹⁻¹ by rw [inv_inv], ← conj_zpow,
        inv_inv, e1]
    have hu' : s⁻¹ * u * s ∈ U₁ := by
      have := hW.conj_U₁ (inv_mem hW.s_mem_S₂) hu
      rwa [inv_inv] at this
    rw [show s⁻¹ * ((t * w) ^ k * u) * s = (s⁻¹ * (t * w) ^ k * s) * (s⁻¹ * u * s) by group, e2]
    exact mul_mem (mem_sup_right (zpow_mem (mem_zpowers _) k)) (mem_sup_left hu')
  have hss : s * s ∈ H₀ := by
    have htw₀ : t * w⁻¹ ∉ U₁ := hW.not_mem_U₁_of_mem_T (mul_mem hW.t_mem (inv_mem hW.w_mem))
      hW.t_mul_w_inv_not_mem_T₁
    have hs2' : s * s ∈ U ⊔ T := by rw [← sq]; exact mem_sup_right hs2
    have hst' : s * t⁻¹ * s⁻¹ = w⁻¹ := by rw [← hW.conj_t]; group
    have hsw' : s * w⁻¹ * s⁻¹ = t⁻¹ := by rw [← hW.conj_w]; group
    rcases hW.mem_U₁_cases hs2' with h1 | h1 | h1 | h1
    · exact mem_sup_left h1
    · exfalso
      have h2 : s * s * w⁻¹ ∈ U₁ := by
        have := hW.conj_s_U₁ _ h1
        rwa [show s * (s * s * t⁻¹) * s⁻¹ = s * s * (s * t⁻¹ * s⁻¹) by group, hst'] at this
      apply htw₀
      rw [show t * w⁻¹ = (s * s * t⁻¹)⁻¹ * (s * s * w⁻¹) by group]
      exact mul_mem (inv_mem h1) h2
    · exfalso
      have h2 : s * s * t⁻¹ ∈ U₁ := by
        have := hW.conj_s_U₁ _ h1
        rwa [show s * (s * s * w⁻¹) * s⁻¹ = s * s * (s * w⁻¹ * s⁻¹) by group, hsw'] at this
      apply htw₀
      rw [show t * w⁻¹ = (s * s * t⁻¹)⁻¹ * (s * s * w⁻¹) by group]
      exact mul_mem (inv_mem h2) h1
    · rw [show s * s = (s * s * (t * w)⁻¹) * (t * w) by group]
      exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers _))
  have hQcard : Nat.card Q = 4 * (2 ^ f) ^ 5 := by
    have h2 := relIndex_sup_zpowers_eq_two_of_mul_self_mem hsH₀ hsN hss
    have h3 := relIndex_mul_card (H := H₀) (K := Q)
    rw [h2, inf_of_le_left le_sup_left, hH₀card] at h3
    omega
  have htQ : t ∉ Q := by
    intro htQ
    have hS₂Q : S₂ ≤ Q := fun y hy => by
      rcases hcov y hy with h1 | h1
      · exact h1
      · rw [show y = t * (t⁻¹ * y) by group]
        exact mul_mem htQ h1
    have h1 := Subgroup.card_le_of_le hS₂Q
    rw [hS₂card, hQcard] at h1
    have hq5 : 0 < (2 ^ f) ^ 5 := pow_pos (pow_pos (by norm_num) f) 5
    omega
  have htQt : ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro q hq
    have hqS : q ∈ S₂ := (sup_le (sup_le (hL.U₁_le.trans le_sup_left |>.trans hW.le_S₂)
      (zpowers_le.mpr (hW.le_S₂ (mem_sup_right htwT)))) (zpowers_le.mpr hW.s_mem_S₂)) hq
    rcases hcov _ (mul_mem (mul_mem htS₂ hqS) (inv_mem htS₂)) with h1 | h1
    · exact h1
    · exfalso
      apply htQ
      have h2 : q⁻¹ * (t⁻¹ * (t * q * t⁻¹)) ∈ Q := mul_mem (inv_mem hq) h1
      rw [show q⁻¹ * (t⁻¹ * (t * q * t⁻¹)) = t⁻¹ by group] at h2
      simpa using inv_mem h2
  have hQn : ∀ a ∈ S₂, ∀ q ∈ Q, a * q * a⁻¹ ∈ Q := by
    intro a ha q hq
    rcases hcov a ha with h1 | h1
    · exact mul_mem (mul_mem h1 hq) (inv_mem h1)
    · rw [show a * q * a⁻¹ = t * ((t⁻¹ * a) * q * (t⁻¹ * a)⁻¹) * t⁻¹ by group]
      exact htQt _ (mul_mem (mul_mem h1 hq) (inv_mem h1))
  rcases CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) (P := S₂) (Q := Q) (u := t)
      hP2 hPidx hQn
      ⟨t, htS₂, fun y hy => by
        rcases hcov y hy with h1 | h1
        · exact ⟨0, by simpa using h1⟩
        · exact ⟨1, by simpa using h1⟩⟩
      htS₂ htQ
      (fun g k _ => by
        rw [pow_mul, hS.start.sq_eq_one, one_pow, mul_one, inv_mul_cancel]
        exact one_mem _)
      (fun g hgP _ => hcov _ hgP)
    with ⟨N, hN, hNcyc, -, htN'⟩ | ⟨g, hgM, hgext, -⟩
  · have hG : IsSimpleGroup G := hS.start.setting.1
    obtain ⟨a₀, b₀, hab⟩ : ∃ a b : G, a * b ≠ b * a := hS.start.setting.2.1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := N) with hN1 | hN1
    · apply hab
      have : IsCyclic (G ⧸ N) := hNcyc
      have hcomm := (QuotientGroup.mk' N).isMulCommutative_of_isCyclic_of_ker_le_center (by
        rw [QuotientGroup.ker_mk', hN1]
        exact bot_le)
      exact hcomm.is_comm.comm a₀ b₀
    · exact htN' (hN1 ▸ mem_top t)
  · obtain ⟨c, hct, hcT⟩ := hS.start.muOne_exists_conj_of_isExtremalIn hgext
    have hxQ : c * t * c⁻¹ ∈ Q := by rw [hct]; exact hgM
    rcases hW.conj_mem_cases hcT with h1 | h1
    · have h2 : (c * t * c⁻¹ * t⁻¹)⁻¹ * (c * t * c⁻¹) ∈ Q := mul_mem (inv_mem (hU₁Q h1)) hxQ
      rw [show (c * t * c⁻¹ * t⁻¹)⁻¹ * (c * t * c⁻¹) = t by group] at h2
      exact htQ h2
    · have h2 : (c * t * c⁻¹ * w⁻¹)⁻¹ * (c * t * c⁻¹) ∈ Q := mul_mem (inv_mem (hU₁Q h1)) hxQ
      rw [show (c * t * c⁻¹ * w⁻¹)⁻¹ * (c * t * c⁻¹) = w by group] at h2
      have h3 : t * w * w⁻¹ ∈ Q := mul_mem htwQ (inv_mem h2)
      rw [mul_inv_cancel_right] at h3
      exact htQ h3

end U3C1OuterSwapTwo

@[expose] def U3C1OuterSwapNormInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G), U3C1OuterStepHyp G L f t T R₂ D d V 1 →
    U3C1OuterLevelData G L f t T D V U U₁ 1 → ¬ U₁ ≤ centralizer (V : Set G) →
    (∀ s ∈ T, ∀ s' ∈ T, s ∉ szT₁ L T ⊔ zpowers t → s' ∉ szT₁ L T ⊔ zpowers t →
      s * s'⁻¹ ∈ szT₁ L T ⊔ zpowers t) →
    ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t → (∀ r ∈ V, w * r * w⁻¹ = r) →
      ∀ s ∈ normalizer ((U ⊔ T : Subgroup G) : Set G), s * t * s⁻¹ = w → s * w * s⁻¹ = t →
        ∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁

@[expose] def U3C1OuterSwapHighInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G), U3C1OuterStepHyp G L f t T R₂ D d V 1 →
    U3C1OuterLevelData G L f t T D V U U₁ 1 → ¬ U₁ ≤ centralizer (V : Set G) →
    (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U ⊔ T) →
    (∃ b ∈ T, ∃ b' ∈ T, b ∉ szT₁ L T ⊔ zpowers t ∧ b' ∉ szT₁ L T ⊔ zpowers t ∧
      b * b'⁻¹ ∉ szT₁ L T ⊔ zpowers t) →
    ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t → (∀ r ∈ V, w * r * w⁻¹ = r) →
      (∀ s : G, s ^ 2 ≠ w) → ∀ s ∈ normalizer ((U ⊔ T : Subgroup G) : Set G),
        (∃ P : Subgroup G, IsPGroup 2 P ∧ U ⊔ T ≤ P ∧ s ∈ P) → s * t * s⁻¹ = w →
          s * w * s⁻¹ ≠ t

theorem u3C1OuterMuOneSwapInput_of_high
    (hN : U3C1OuterSwapNormInput) (hH : U3C1OuterSwapHighInput) : U3C1OuterMuOneSwapInput := by
  intro G _ _ L f t T R₂ D d V U U₁ hS hL hμV hnS w hwT hw2 hwS hwV hsq s hsN hP hst hsw
  by_cases hidx : ∀ s ∈ T, ∀ s' ∈ T, s ∉ szT₁ L T ⊔ zpowers t → s' ∉ szT₁ L T ⊔ zpowers t →
      s * s'⁻¹ ∈ szT₁ L T ⊔ zpowers t
  · obtain ⟨P, hP2, hSP, hsP⟩ := hP
    exact (U3C1OuterSwapTwo.false (G := G) (L := L) (f := f) (t := t) (T := T) (R₂ := R₂)
      (D := D) (d := d) (V := V) (U := U) (U₁ := U₁) (w := w) (s := s) (P := P)
      ⟨hS, hL, hμV, hidx, hwT, hw2, hwS, hwV, hP2, hSP, hsN, hsP, hst, hsw,
        hN G L f t T R₂ D d V U U₁ hS hL hμV hidx w hwT hw2 hwS hwV s hsN hst hsw⟩)
  · refine hH G L f t T R₂ D d V U U₁ hS hL hμV hnS ?_ w hwT hw2 hwS hwV hsq s hsN hP hst hsw
    by_contra hcon
    apply hidx
    intro b hb b' hb' hbS hb'S
    by_contra hbb
    exact hcon ⟨b, hb, b', hb', hbS, hb'S, hbb⟩

end CFSG.SeitzReduction.RankOne
