module

public import CFSG.Goldschmidt75.Sec41c
public import CFSG.CharacterTheory.Semidihedral.OddCoreQuotient
public import CFSG.Goldschmidt75.Sec41a

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {S₁ S₂ : Subgroup G}

theorem MinCE.exists_central (h : MinCE G T S₁ S₂) {n : G} (hnc : n ∈ center G)
    (hn2 : orderOf n = 2) :
    ∃ Z : Subgroup G, Z ≤ center G ∧ IsPGroup 2 Z ∧ n ∈ Z ∧
      ∀ s₁ ∈ S₁, ∀ s₂ ∈ S₂, s₂⁻¹ * s₁ ∈ Z → s₁ ∈ Z := by
  have hO := h.oddCore_eq_bot
  have hnT := mem_sylow_of_mem_center T hnc hn2
  have hnn : n * n = 1 := by rw [← pow_two, ← hn2, pow_orderOf_eq_one]
  have hcomm : ∀ x : G, x * n = n * x := fun x => mem_center_iff.mp hnc x
  have hdisj : ∀ x ∈ S₁, x ∈ S₂ → x = 1 := fun x h₁ h₂ => by
    have hx : x ∈ S₁ ⊓ S₂ := ⟨h₁, h₂⟩
    rwa [h.disj, mem_bot] at hx
  by_cases hcase : ∃ a ∈ S₂, a ≠ 1 ∧ a * n ∈ S₁
  · obtain ⟨a, ha, ha1, han⟩ := hcase
    have huniq : ∀ y ∈ S₂, y * n ∈ S₁ → y = a := by
      intro y hy hyn
      have h1 : (y * n) * (a * n)⁻¹ ∈ S₁ := mul_mem hyn (inv_mem han)
      have e : (y * n) * (a * n)⁻¹ = y * a⁻¹ := by
        rw [mul_inv_rev, ← mul_assoc, mul_assoc y, mul_inv_cancel, mul_one]
      rw [e] at h1
      have h2 := hdisj _ h1 (mul_mem hy (inv_mem ha))
      exact mul_inv_eq_one.mp h2
    have ha2 : orderOf a = 2 := by
      have h1 : (a * n) * (a * n) ∈ S₁ := mul_mem han han
      have e : (a * n) * (a * n) = a * a := by
        rw [mul_assoc, ← mul_assoc n, ← hcomm a, mul_assoc, hnn, mul_one]
      rw [e] at h1
      have h2 := hdisj _ h1 (mul_mem ha ha)
      exact orderOf_eq_prime (by rw [pow_two]; exact h2) ha1
    have hcl : fusionStronglyClosed ((zpowers a : Subgroup G) : Set G) T := by
      intro x hx g hg
      rcases eq_one_or_eq_of_mem_zpowers ha2 hx with rfl | rfl
      · simp
      · have hy₂ : g⁻¹ * x * g ∈ S₂ := h.sc₂ x ha g hg
        have e : g⁻¹ * (x * n) * g = (g⁻¹ * x * g) * n := by
          calc g⁻¹ * (x * n) * g = g⁻¹ * x * (n * g) := by group
            _ = g⁻¹ * x * (g * n) := by rw [← hcomm g]
            _ = g⁻¹ * x * g * n := by group
        have hyn : g⁻¹ * (x * n) * g ∈ (T : Subgroup G) := by
          rw [e]
          exact mul_mem hg hnT
        have hy₁ := h.sc₁ _ han g hyn
        rw [e] at hy₁
        rw [SetLike.mem_coe, huniq _ hy₂ hy₁]
        exact mem_zpowers _
    have hac := mem_center_of_stronglyClosed_zpowers T ha2 hcl hO
    have hNn : (zpowers n).Normal := normal_of_le_center (zpowers_le.mpr hnc)
    refine ⟨zpowers n ⊔ zpowers a, sup_le (zpowers_le.mpr hnc) (zpowers_le.mpr hac),
      (isPGroup_zpowers hn2).to_sup_of_normal_left (isPGroup_zpowers ha2),
      mem_sup_left (mem_zpowers n), fun s₁ hs₁ s₂ hs₂ hmem => ?_⟩
    obtain ⟨u, hu, w, hw, huw⟩ := mem_sup_of_normal_left.mp hmem
    have hwS : s₂ * w ∈ S₂ := mul_mem hs₂ ((zpowers_le.mpr ha) hw)
    have hcw : u * w = w * u := (mem_center_iff.mp (zpowers_le.mpr hnc hu) w).symm
    have hs : s₁ = (s₂ * w) * u := by
      calc s₁ = s₂ * (u * w) := by rw [huw]; group
        _ = s₂ * (w * u) := by rw [hcw]
        _ = s₂ * w * u := by group
    rcases eq_one_or_eq_of_mem_zpowers hn2 hu with rfl | rfl
    · rw [mul_one] at hs
      rw [hs, hdisj _ (hs ▸ hs₁) hwS]
      exact one_mem _
    · rw [hs] at hs₁ ⊢
      rw [huniq _ hwS hs₁]
      exact mul_mem (mem_sup_right (mem_zpowers a)) (mem_sup_left (mem_zpowers _))
  · push Not at hcase
    refine ⟨zpowers n, zpowers_le.mpr hnc, isPGroup_zpowers hn2, mem_zpowers n,
      fun s₁ hs₁ s₂ hs₂ hmem => ?_⟩
    rcases eq_one_or_eq_of_mem_zpowers hn2 hmem with h1 | h1
    · have e : s₂ = s₁ := inv_mul_eq_one.mp h1
      rw [hdisj _ hs₁ (e ▸ hs₂)]
      exact one_mem _
    · have e : s₁ = s₂ * n := by rw [← h1]; group
      by_cases hs₂1 : s₂ = 1
      · rw [e, hs₂1, one_mul]
        exact mem_zpowers n
      · exact absurd (e ▸ hs₁) (hcase s₂ hs₂ hs₂1)

theorem MinCE.not_le_centralizer (h : MinCE G T S₁ S₂) {N : Subgroup G} (hNn : N.Normal)
    (hN : N ≠ ⊥) : ¬ N ≤ centralizer (S₁ : Set G) := by
  intro hNS
  have hO := h.oddCore_eq_bot
  obtain ⟨N₀, hN₀n, hN₀1, hN₀N, hmin⟩ := exists_minimal_normal hNn hN
  have hH₁C : normalClosure (S₁ : Set G) ≤ centralizer (N₀ : Set G) := by
    have := hN₀n
    exact normalClosure_le_normal (le_centralizer_iff.mp (hN₀N.trans hNS))
  have hG : centralizer (N₀ : Set G) ⊔ S₂ = ⊤ :=
    top_le_iff.mp (h.sup_eq_top.symm.le.trans (sup_le_sup_right hH₁C _))
  obtain ⟨hN₀Z, hN₀2⟩ := minimal_normal_central hO hN₀n hN₀1 hmin (T.isPGroup'.to_le h.le₂) hG
  obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := N₀) 2 (by rw [hN₀2])
  have hn2 : orderOf (n : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hn
  obtain ⟨Z, hZc, hZp, hnZ, hZd⟩ := h.exists_central (hN₀Z n.2) hn2
  have hZn : Z.Normal := normal_of_le_center hZc
  have hZ1 : Z ≠ ⊥ := fun h0 => by
    rw [h0, mem_bot] at hnZ
    rw [hnZ, orderOf_one] at hn2
    exact absurd hn2 (by norm_num)
  have hcomm := thmA_quotient (h.ihG _ (card_quotient_lt hZ1)) T h.le₁ h.le₂ h.sc₁ h.sc₂
    h.comm hZd
  have hOZ : goldschmidtOddCore (G ⧸ Z) = ⊥ := by
    rw [goldschmidtOddCore_eq_pPrimeCore]
    exact CFSG.Semidihedral.OddCoreQuotient.pPrimeCore_quotient_eq_bot_of_central 2 Z hZc hZp
      (by rwa [← goldschmidtOddCore_eq_pPrimeCore])
  rw [hOZ, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hcomm
  set H₁ := normalClosure (S₁ : Set G)
  set H₂ := normalClosure (S₂ : Set G)
  have hD : IsPGroup 2 (H₁ ⊓ H₂ : Subgroup G) := by
    refine CFSG.isPGroup_of_nilpotent_normal _ (Subgroup.normal_inf_normal _ _)
      (isNilpotent_of_commutator_le_center ?_) (by rwa [← goldschmidtOddCore_eq_pPrimeCore])
    exact (commutator_mono inf_le_left inf_le_right).trans (hcomm.trans hZc)
  have hG2 : ∀ g : G, ∃ k : ℕ, g ^ (2 ^ k) = 1 := by
    intro g
    obtain ⟨k, hk⟩ := exists_two_pow_mem (T.isPGroup'.to_le h.le₂) h.sup_eq_top g
    obtain ⟨l, hl⟩ := exists_two_pow_mem (T.isPGroup'.to_le h.le₁) h.symm.sup_eq_top g
    have hmem : g ^ (2 ^ (k + l)) ∈ H₁ ⊓ H₂ := by
      refine ⟨?_, ?_⟩
      · rw [pow_add, pow_mul]
        exact pow_mem hk _
      · rw [pow_add, mul_comm, pow_mul]
        exact pow_mem hl _
    obtain ⟨m, hm⟩ := hD ⟨_, hmem⟩
    refine ⟨k + l + m, ?_⟩
    rw [pow_add, pow_mul]
    exact congrArg Subtype.val hm
  have hT : (T : Subgroup G) = ⊤ :=
    (T.is_maximal' (fun g => by obtain ⟨k, hk⟩ := hG2 g; exact ⟨k, Subtype.ext hk⟩)
      le_top).symm
  have hnorm : ∀ {S : Subgroup G}, fusionStronglyClosed (S : Set G) T →
      normalClosure (S : Set G) = S := by
    intro S hS
    have : S.Normal := ⟨fun s hs g => by
      have h1 := hS s hs g⁻¹ (by rw [hT]; exact mem_top _)
      rwa [inv_inv] at h1⟩
    exact normalClosure_eq_self S
  apply h.fail
  rw [hnorm h.sc₁, hnorm h.sc₂, commutator_eq_bot_iff_le_centralizer.mpr h.comm]
  exact bot_le

end CFSG.Goldschmidt75
