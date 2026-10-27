module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoRootOut

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal

section Twist

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem section_swap_of_near_partner (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {S₀ : Finset (Fin n)} (hkn : S₀.card + 7 ≤ n)
    (hII : CaseIIAt e z S₀) {a g : G} (ha : a ∈ centralizer ({z} : Set G))
    (hg : g * z * g⁻¹ = a) (haz : a ≠ z)
    (hf : 5 ≤ (fixFin (permOf h d e ha)).card ∧ (fixFin (permOf h d e ha)).card ≠ 6)
    {S : Finset (Fin n)} (hSF : S ⊆ fixFin (permOf h d e ha)) (hS : S.card = S₀.card)
    (haR : a ∈ centralizer (corr (X := G) e (altSub S) : Set G))
    (ε : Perm (Fin (n - S.card + 2)) ≃* Sec G (corr (X := G) e (altSub S))) :
    (ε.symm (QuotientGroup.mk ⟨a, haR⟩)).IsSwap := by
  obtain ⟨S₁, hS₁card, hz₁, haR', Φ, hΦ⟩ := exists_partner_root_at h d T e ha hg haz hf hSF
  have hE : ExactShape z L n := exactShape_of_setting h d T.card
  have hSc : 2 ≤ S₀ᶜ.card := by rw [card_compl_fin]; omega
  obtain ⟨hz₁', hs₁⟩ := caseIIAt_transport hE e (show S₀.card = S₁.card by omega) hSc hII
  have hsa : SymOutcome (QuotientGroup.mk ⟨a, haR⟩ : Sec G (corr (X := G) e (altSub S)))
      (n - S.card) := by
    have := SymOutcome.map' Φ hs₁
    rw [hΦ, hS₁card] at this
    exact this
  obtain ⟨ε', hε'⟩ := hsa
  have := isSwap_map_of_mulEquiv (ε'.trans ε.symm) rfl
    (by simp only [Fintype.card_fin]; omega) hε'
  simpa using this

theorem not_isSwap_mul_of_comm {α : Type*} [DecidableEq α] [Fintype α] {σ₁ σ₂ : Perm α}
    (h₁ : σ₁.IsSwap) (h₂ : σ₂.IsSwap) (hc : σ₁ * σ₂ = σ₂ * σ₁) (hne : σ₁ ≠ σ₂) :
    ¬ (σ₁ * σ₂).IsSwap := by
  intro h3
  have hd : σ₁.Disjoint σ₂ := by
    intro i
    by_cases hi : σ₂ i = i
    · exact Or.inr hi
    · left
      exact fixes_of_comm_swap h₂ h₁ hc hne hi
  have hcard := hd.card_support_mul
  rw [Perm.card_support_eq_two.2 h₁, Perm.card_support_eq_two.2 h₂,
    Perm.card_support_eq_two.2 h3] at hcard
  omega

theorem not_isConj_both (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4)
    (hkn : S₀.card + 7 ≤ n) (hII : CaseIIAt e z S₀) {τ : Perm (Fin n)} (hτ : τ.IsSwap) :
    ¬ (IsConj z (swapIota h d T e τ : G) ∧ IsConj z (z * (swapIota h d T e τ : G))) := by
  classical
  rintro ⟨h₁, h₂⟩
  set s : G := (swapIota h d T e τ : G) with hs
  have hz2 : z * z = 1 := d.mul_self
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hsC : s ∈ centralizer ({z} : Set G) := swapIota_mem_centralizer h d T e τ
  have hzsC : z * s ∈ centralizer ({z} : Set G) := mul_mem hzC hsC
  have hps : permOf h d e hsC = τ := permOf_swapIota h d T e τ
  have hpzs : permOf h d e hzsC = τ := by
    rw [permOf_mul h d e hzC hsC hzsC, permOf_self h d e hzC, one_mul, hps]
  have hfix : (fixFin τ).card = n - 2 := card_fixFin_of_isSwap hτ
  obtain ⟨S, hSF, hScard⟩ := Finset.exists_subset_card_eq
    (show S₀.card ≤ (fixFin τ).card by omega)
  have hE : ExactShape z L n := exactShape_of_setting h d T.card
  have hSc : 2 ≤ S₀ᶜ.card := by rw [card_compl_fin]; omega
  obtain ⟨hzS, ε, hε⟩ := caseIIAt_transport hE e (show S₀.card = S.card by omega) hSc hII
  have hsz : s ≠ z := fun h' => z_notMem_swapComplement h d T.cent T.outer T.sq
    (h' ▸ (swapIota h d T e τ).2)
  have hzsz : z * s ≠ z := by
    intro h'
    have : s = 1 := by
      calc s = z⁻¹ * (z * s) := by group
        _ = 1 := by rw [h', inv_mul_cancel]
    have h1 := hps
    rw [permOf_congr' this hsC (one_mem _) h d e] at h1
    have : permOf h d e (one_mem (centralizer ({z} : Set G))) = 1 := by
      show rho e h.hn 1 = 1; exact map_one _
    rw [this] at h1
    obtain ⟨p, q, hpq, hτe⟩ := hτ
    rw [← h1] at hτe
    have := congrArg (fun f : Perm (Fin n) => f p) hτe
    simp only [Perm.one_apply, swap_apply_left] at this
    exact hpq this
  have hsR : s ∈ centralizer (corr (X := G) e (altSub S) : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact (comm_of_mem_corr_of_permOf_fix h d e hsC
      (fun i hi => by rw [hps]; exact mem_fixFin.1 (hSF hi)) hw).symm
  have hzsR : z * s ∈ centralizer (corr (X := G) e (altSub S) : Set G) := mul_mem hzS hsR
  have hfτ : 5 ≤ (fixFin τ).card ∧ (fixFin τ).card ≠ 6 := ⟨by omega, by omega⟩
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 h₁
  obtain ⟨g₂, hg₂⟩ := isConj_iff.1 h₂
  have hsw₁ := section_swap_of_near_partner h d T e hkn hII hsC hg₁ hsz
    (by rw [hps]; exact hfτ) (by rw [hps]; exact hSF) (by omega) hsR ε
  have hsw₂ := section_swap_of_near_partner h d T e hkn hII hzsC hg₂ hzsz
    (by rw [hpzs]; exact hfτ) (by rw [hpzs]; exact hSF) (by omega) hzsR ε
  have hprod : ε.symm (QuotientGroup.mk ⟨z * s, hzsR⟩) =
      ε.symm (QuotientGroup.mk ⟨z, hzS⟩) * ε.symm (QuotientGroup.mk ⟨s, hsR⟩) := by
    rw [← map_mul, ← QuotientGroup.mk_mul]
    rfl
  have hcomm : ε.symm (QuotientGroup.mk ⟨z, hzS⟩) * ε.symm (QuotientGroup.mk ⟨s, hsR⟩) =
      ε.symm (QuotientGroup.mk ⟨s, hsR⟩) * ε.symm (QuotientGroup.mk ⟨z, hzS⟩) := by
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hsC).symm
  have hss : s * s = 1 := by
    have : swapIota h d T e τ * swapIota h d T e τ = 1 := by
      rw [← map_mul]
      obtain ⟨p, q, _, hτe⟩ := hτ
      rw [hτe, swap_mul_self, map_one]
    exact congrArg Subtype.val this
  have hne : ε.symm (QuotientGroup.mk ⟨z, hzS⟩) ≠ ε.symm (QuotientGroup.mk ⟨s, hsR⟩) :=
    fun h' => mk_ne_of_partner d hsC hsz hss hzS hsR (ε.symm.injective h').symm
  exact not_isSwap_mul_of_comm hε hsw₁ hcomm hne (hprod ▸ hsw₂)

theorem exists_swap_partner (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {S₀ : Finset (Fin n)} (hkn : S₀.card + 7 ≤ n)
    (hII : CaseIIAt e z S₀) :
    ∃ τ : Perm (Fin n), τ.IsSwap ∧
      (IsConj z (swapIota h d T e τ : G) ∨ IsConj z (z * (swapIota h d T e τ : G))) := by
  classical
  obtain ⟨hzS, ε, hε⟩ := hII
  set R := corr (X := G) e (altSub S₀) with hR
  set zb : Sec G R := QuotientGroup.mk ⟨z, hzS⟩ with hzb
  have hz2 : z * z = 1 := d.mul_self
  have hzb2 : zb * zb = 1 := by
    rw [hzb, ← QuotientGroup.mk_mul]
    have : (⟨z, hzS⟩ : ↥(centralizer (R : Set G))) * ⟨z, hzS⟩ = 1 := Subtype.ext hz2
    rw [this]; rfl
  have hSc5 : 5 ≤ S₀ᶜ.card := by rw [card_compl_fin]; omega
  have hScn : S₀ᶜ.card = n - S₀.card := card_compl_fin S₀
  set Ψ : Perm ↥S₀ᶜ →* Perm (Fin (n - S₀.card + 2)) :=
    ε.symm.toMonoidHom.comp (thetaHom h d T e S₀) with hΨ
  have hinj : Function.Injective Ψ :=
    ε.symm.injective.comp (thetaHom_injective h d T e hSc5)
  have hθz : ∀ π : Perm ↥S₀ᶜ, thetaHom h d T e S₀ π * zb = zb * thetaHom h d T e S₀ π := by
    intro π
    rw [thetaHom_apply, hzb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (kappa_mem_centralizer h d T e S₀ π))
  have hcomm : ∀ π, Ψ π * ε.symm zb = ε.symm zb * Ψ π := by
    intro π
    simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hθz]
  have hneΨ : ∀ π, Ψ π ≠ ε.symm zb := by
    intro π hπ
    simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at hπ
    exact thetaHom_ne_z h d T e S₀ hzS π (ε.symm.injective hπ)
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 (show 1 < S₀ᶜ.card by omega)
  set σ₀ : Perm ↥S₀ᶜ := swap ⟨i, hi⟩ ⟨j, hj⟩ with hσ₀
  have hσ₀s : σ₀.IsSwap := ⟨⟨i, hi⟩, ⟨j, hj⟩, fun h' => hij (congrArg Subtype.val h'), rfl⟩
  obtain ⟨τ', hτ's, -, hτ'ne, hΨσ⟩ := embedding_swap_cases (α := ↥S₀ᶜ)
    (β := Fin (n - S₀.card + 2)) (by simp only [Fintype.card_fin, Fintype.card_coe]; omega)
    (by simp only [Fintype.card_coe]; omega) Ψ hinj hε hcomm hneΨ hσ₀s
  obtain ⟨p₀, q₀, hpq₀, hτ₀e⟩ := hε
  obtain ⟨r₀, s₀, hrs₀, hτ'e⟩ := hτ's
  obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hpq₀ hrs₀)
  have hετ' : ε τ' = ε c * zb * (ε c)⁻¹ := by
    rw [hτ'e, ← hc, ← hτ₀e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  set κ : G := kappa h d T e S₀ σ₀ with hκ
  have hκR : κ ∈ centralizer (R : Set G) := kappa_mem_centralizer_root h d T e S₀ σ₀
  have hzκR : z * κ ∈ centralizer (R : Set G) := mul_mem hzS hκR
  have hκC : κ ∈ centralizer ({z} : Set G) := kappa_mem_centralizer h d T e S₀ σ₀
  have hκ2 : κ * κ = 1 := by
    have : swapIota h d T e (Perm.ofSubtype σ₀) * swapIota h d T e (Perm.ofSubtype σ₀) = 1 := by
      rw [← map_mul, ← map_mul, hσ₀, swap_mul_self, map_one, map_one]
    exact congrArg Subtype.val this
  have hzκ : z * κ = κ * z := (mem_centralizer_singleton_iff.1 hκC).symm
  obtain ⟨b, hbR, hb2, hbmk, hbcases⟩ : ∃ (b : G) (hbR : b ∈ centralizer (R : Set G)), b * b = 1 ∧
      (QuotientGroup.mk ⟨b, hbR⟩ : Sec G R) = ε τ' ∧ (b = κ ∨ b = z * κ) := by
    rcases hΨσ with h1 | h1
    · refine ⟨κ, hκR, hκ2, ?_, Or.inl rfl⟩
      have h2 : ε (Ψ σ₀) = ε τ' := by rw [h1]
      simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply] at h2
      rw [← h2, thetaHom_apply]
    · refine ⟨z * κ, hzκR, ?_, ?_, Or.inr rfl⟩
      · calc z * κ * (z * κ) = (z * z) * (κ * κ) := by
              rw [mul_assoc, ← mul_assoc κ z κ, ← hzκ]; group
          _ = 1 := by rw [hz2, hκ2, one_mul]
      · have h2 : ε (Ψ σ₀) = ε (ε.symm zb * τ') := by rw [h1]
        simp only [hΨ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.apply_symm_apply, map_mul] at h2
        have h3 : (QuotientGroup.mk ⟨z * κ, hzκR⟩ : Sec G R) =
            zb * thetaHom h d T e S₀ σ₀ := by
          rw [thetaHom_apply, hzb, ← QuotientGroup.mk_mul]; rfl
        rw [h3, h2, ← mul_assoc, hzb2, one_mul]
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (ε c)
  set u₀ : ↥(centralizer (R : Set G)) := y * ⟨z, hzS⟩ * y⁻¹ with hu₀
  have hu₀2 : u₀ * u₀ = 1 := by
    rw [hu₀]
    have : (⟨z, hzS⟩ : ↥(centralizer (R : Set G))) * ⟨z, hzS⟩ = 1 := Subtype.ext hz2
    calc y * ⟨z, hzS⟩ * y⁻¹ * (y * ⟨z, hzS⟩ * y⁻¹) =
        y * ((⟨z, hzS⟩ : ↥(centralizer (R : Set G))) * ⟨z, hzS⟩) * y⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hb2' : (⟨b, hbR⟩ : ↥(centralizer (R : Set G))) * ⟨b, hbR⟩ = 1 := Subtype.ext hb2
  have hmk : (QuotientGroup.mk u₀ : Sec G R) = QuotientGroup.mk ⟨b, hbR⟩ := by
    rw [hbmk, hετ', hu₀, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy]
  have hmem : (⟨b, hbR⟩ : ↥(centralizer (R : Set G))) * u₀ ∈
      CFSG.oddCore ↥(centralizer (R : Set G)) := by
    have h1 := QuotientGroup.eq.1 hmk.symm
    have hbinv : (⟨b, hbR⟩ : ↥(centralizer (R : Set G)))⁻¹ = ⟨b, hbR⟩ :=
      inv_eq_of_mul_eq_one_right hb2'
    rwa [hbinv] at h1
  obtain ⟨r, -, hr⟩ := exists_conj_of_involutions_of_mul_mem
    (fun x hx => orderOf_odd_of_mem_oddCore hx) hu₀2 hb2' hmem
  have hconj : IsConj z b := by
    refine isConj_iff.2 ⟨((r * y : ↥(centralizer (R : Set G))) : G), ?_⟩
    have := congrArg Subtype.val hr
    simp only [hu₀, Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this]
    simp [mul_assoc]
  refine ⟨Perm.ofSubtype σ₀, hσ₀s.of_subtype_isSwap, ?_⟩
  rcases hbcases with rfl | rfl
  · exact Or.inl (by rw [hκ, kappa_apply] at hconj; exact hconj)
  · exact Or.inr (by rw [hκ, kappa_apply] at hconj; exact hconj)

theorem caseII_twist (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4)
    (hkn : S₀.card + 7 ≤ n) (hII : CaseIIAt e z S₀) :
    ∃ c : G, (c = 1 ∨ c = z) ∧ ∀ τ : Perm (Fin n), τ.IsSwap →
      IsConj z (c * (swapIota h d T e τ : G)) ∧ ¬ IsConj z (z * c * (swapIota h d T e τ : G)) := by
  classical
  have hz2 : z * z = 1 := d.mul_self
  obtain ⟨τ₀, hτ₀, hc₀⟩ := exists_swap_partner h d T e hkn hII
  have key : ∀ c : G, (c = 1 ∨ c = z) → IsConj z (c * (swapIota h d T e τ₀ : G)) →
      ∀ τ : Perm (Fin n), τ.IsSwap → IsConj z (c * (swapIota h d T e τ : G)) := by
    intro c hc h0 τ hτ
    obtain ⟨p, q, hpq, hτ₀e⟩ := hτ₀
    obtain ⟨r, t, hrt, hτe⟩ := hτ
    obtain ⟨π, hπ⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hpq hrt)
    have hιτ : (swapIota h d T e τ : G) = (swapIota h d T e π : G) *
        (swapIota h d T e τ₀ : G) * (swapIota h d T e π : G)⁻¹ := by
      rw [hτe, ← hπ, ← hτ₀e, map_mul, map_mul, map_inv]; rfl
    have hcπ : c * (swapIota h d T e π : G) = (swapIota h d T e π : G) * c := by
      rcases hc with rfl | rfl
      · simp
      · exact (mem_centralizer_singleton_iff.1 (swapIota_mem_centralizer h d T e π)).symm
    refine h0.trans (isConj_iff.2 ⟨(swapIota h d T e π : G), ?_⟩)
    rw [hιτ]
    calc (swapIota h d T e π : G) * (c * (swapIota h d T e τ₀ : G)) *
          (swapIota h d T e π : G)⁻¹ =
        ((swapIota h d T e π : G) * c) * (swapIota h d T e τ₀ : G) *
          (swapIota h d T e π : G)⁻¹ := by group
      _ = (c * (swapIota h d T e π : G)) * (swapIota h d T e τ₀ : G) *
          (swapIota h d T e π : G)⁻¹ := by rw [hcπ]
      _ = c * ((swapIota h d T e π : G) * (swapIota h d T e τ₀ : G) *
          (swapIota h d T e π : G)⁻¹) := by group
  have hnot : ∀ τ : Perm (Fin n), τ.IsSwap →
      ¬ (IsConj z (swapIota h d T e τ : G) ∧ IsConj z (z * (swapIota h d T e τ : G))) :=
    fun τ hτ => not_isConj_both h d T e hk hkn hII hτ
  rcases hc₀ with h0 | h0
  · have h0' : IsConj z (1 * (swapIota h d T e τ₀ : G)) := by rw [one_mul]; exact h0
    refine ⟨1, Or.inl rfl, fun τ hτ => ⟨key 1 (Or.inl rfl) h0' τ hτ, ?_⟩⟩
    intro h1
    rw [mul_one] at h1
    have h2 := key 1 (Or.inl rfl) h0' τ hτ
    rw [one_mul] at h2
    exact hnot τ hτ ⟨h2, h1⟩
  · refine ⟨z, Or.inr rfl, fun τ hτ => ⟨key z (Or.inr rfl) h0 τ hτ, ?_⟩⟩
    intro h1
    rw [hz2, one_mul] at h1
    exact hnot τ hτ ⟨h1, key z (Or.inr rfl) h0 τ hτ⟩

omit [Finite G] in
theorem mem_or_mul_mem_of_mem_sup_zpowers {u : G} (hu : u ∈ normalizer (L : Set G))
    (hu2 : u ^ 2 = 1) {c : G} (hc : c ∈ L ⊔ zpowers u) : c ∈ L ∨ c * u ∈ L := by
  obtain ⟨l, hl, w, hw, rfl⟩ := (mem_sup_zpowers_iff_of_mem_normalizer hu).1 hc
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul]
    simpa [hu2] using hl
  · right
    rw [zpow_add, zpow_mul, zpow_one]
    have hu1 : u * u = 1 := by rw [← pow_two, hu2]
    simpa [hu2, mul_assoc, hu1] using hl

theorem mem_of_mem_sup_zpowers_both (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    {x : G} (hx : x ∈ L ⊔ zpowers u) (hx' : x ∈ L ⊔ zpowers (u * z)) : x ∈ L := by
  obtain ⟨e⟩ := h.iso
  obtain ⟨hcent', -, hsq'⟩ := shapeTwo_mul_z d T.cent T.outer T.sq
  have huN : u ∈ normalizer (L : Set G) := AltStdBal.centralizer_le_normalizer h d T.cent
  have huzN : u * z ∈ normalizer (L : Set G) := AltStdBal.centralizer_le_normalizer h d hcent'
  rcases mem_or_mul_mem_of_mem_sup_zpowers huN T.sq hx with h1 | h1
  · exact h1
  rcases mem_or_mul_mem_of_mem_sup_zpowers huzN hsq' hx' with h2 | h2
  · exact h2
  exfalso
  have hzL : z ∈ L := by
    have := mul_mem (inv_mem h1) h2
    simpa [mul_assoc] using this
  have hz1 := eq_one_of_mem_of_mem_centralizer e (by have := h.hn; omega) hzL (d.le d.mem)
  have := d.order
  rw [hz1, orderOf_one] at this
  omega

theorem swapIota_mul_z_ne (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (T' : ShapeTwo L Q z (u * z)) (e : L ≃* alternatingGroup (Fin n)) {τ : Perm (Fin n)}
    (hτ : Perm.sign τ = -1) : (swapIota h d T' e τ : G) ≠ (swapIota h d T e τ : G) := by
  intro heq
  have hxL : (swapIota h d T e τ : G) ∈ L :=
    mem_of_mem_sup_zpowers_both h d T (swapIota h d T e τ).2 (heq ▸ (swapIota h d T' e τ).2)
  have hp := permOf_swapIota h d T e τ
  rw [permOf_of_mem h d e (swapIota_mem_centralizer h d T e τ) hxL] at hp
  have hs := mem_alternatingGroup.1 (e ⟨_, hxL⟩).2
  rw [hp, hτ] at hs
  exact absurd hs (by decide)

theorem swapIota_rhoSwap (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (s : ↥(L ⊔ zpowers u)) :
    swapIota h d T e (rhoSwap h d T.cent e s) = s :=
  (MulEquiv.ofBijective (rhoSwap h d T.cent e)
    (rhoSwap_bijective h d T.card T.cent T.outer T.sq e)).symm_apply_apply s

theorem caseII_of_untwisted (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n))
    (hsw : ∀ (a : G) (ha : a ∈ centralizer ({z} : Set G)), a ∈ Partners z →
      (permOf h d e ha).IsSwap)
    (htw : ∀ τ : Perm (Fin n), τ.IsSwap →
      IsConj z (swapIota h d T e τ : G) ∧ ¬ IsConj z (z * (swapIota h d T e τ : G))) :
    CaseII e h.hn (L ⊔ zpowers u) z := by
  intro a
  constructor
  · intro hP
    have ha : a ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hP.2.2
    have hs := hsw a ha hP
    rcases eq_swapIota_or h d T e ha with h1 | h1
    · refine ⟨h1 ▸ (swapIota h d T e (permOf h d e ha)).2,
        AltStdBal.centralizer_le_normalizer h d ha, hs⟩
    · exact absurd (h1 ▸ hP.1) (htw _ hs).2
  · rintro ⟨haS, haN, hsw'⟩
    have ha : a ∈ centralizer ({z} : Set G) :=
      (sup_le (le_centralizer_single h d) (zpowers_le.2 T.cent)) haS
    have hp : permOf h d e ha = rhoSwap h d T.cent e ⟨a, haS⟩ := rfl
    have hs : (permOf h d e ha).IsSwap := hsw'
    have haι : (swapIota h d T e (permOf h d e ha) : G) = a := by
      rw [hp, swapIota_rhoSwap]
    refine ⟨?_, ?_, ?_⟩
    · have := (htw _ hs).1
      rwa [haι] at this
    · intro haz
      exact z_notMem_swapComplement h d T.cent T.outer T.sq (haz ▸ haS)
    · exact mem_centralizer_singleton_iff.1 ha

end Twist

end CFSG.OddStandard.AltStdSec
