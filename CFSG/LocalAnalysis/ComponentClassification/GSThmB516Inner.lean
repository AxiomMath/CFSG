module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516Over

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def Row516CentralizerStatement : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H), h.Row516 →
    h.a ∈ h.K ⊔ coreActionKernel h.K → IsCyclic h.B → ∀ b ∈ h.B, orderOf b = 2 →
      h.a * b ∈ h.K → centralizer ({b} : Set H) ≠ ⊤ →
      ∃ L : Subgroup H, h.K ≤ L ∧ L ≤ h.K ⊔ oddCoreIn (centralizer ({b} : Set H)) ∧
        L ≤ centralizer ({b} : Set H) ∧ IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set H)))

theorem exists_pow_twoPower_map_eq {G Q : Type*} [Group G] [Finite G] [Group Q] (π : G →* Q)
    (g : G) (hg : π g ^ 2 = 1) : ∃ k : ℕ, (∃ n : ℕ, (g ^ k) ^ 2 ^ n = 1) ∧ π (g ^ k) = π g := by
  obtain ⟨v, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨m, ⟨v, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  · obtain ⟨j, rfl⟩ := hm
    rw [map_pow, pow_succ, pow_mul, hg, one_pow, one_mul]

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem false_of_row516_inner (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hStab : CFAutL2Stab) (hZ : CFRow516InnerCenter)
    (hFus : CFRow516InnerFusion) (hTK : CFRow516InnerT) (hOut : CFRow516InnerOut)
    (hPSp : CFRow516InnerPSp) (hNoPSp : CFRow516NoPSp) (hInv : CFL2InvPair)
    (hOS5 : Row516CentralizerStatement) (hrow : h.Row516)
    (hin : h.a ∈ h.K ⊔ coreActionKernel h.K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, f, hp, hp2, hf, hJlie, hKa, -⟩ := id hrow
  have hZJ := h.toHyp52.center_eq_bot hB1 hB6 hCF23 hCF24
  have hDP := h.toHyp52.D_inf_P_eq_bot hZJ
  have hCaN := h.toHyp52.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc
  have hZK := hZ H h.toHyp52 hrow hin
  obtain ⟨hTKB, hTKc⟩ := hTK H h.toHyp52 hrow hin
  have hKCB : h.K ≤ centralizer (h.B : Set H) :=
    h.toHyp52.K_le_layer_W.trans h.toHyp52.V_le_centralizer_B
  have hKW : h.K ≤ h.W := h.toHyp52.K_le_layer_W.trans (map_subtype_le _)
  have hWK : h.W ≤ normalizer (h.K : Set H) := by
    intro w hw
    rw [← h.toHyp52.V_eq_K hKa]
    exact mem_normalizer_layerIn hw
  have ha2 : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  have hKB1 : ∀ {y : H}, y ∈ h.K → y ∈ h.B → y = 1 := by
    intro y hyK hyB
    have hBC : h.B ≤ coreActionKernel h.K := by
      have := (hB6 H h.toHyp52).1
      rwa [h.toHyp52.V_eq_K hKa] at this
    have hyZ : y ∈ (Open.fusionZStar ↥h.K).map h.K.subtype := by
      rw [map_fusionZStar_eq]
      exact mem_inf.mpr ⟨hyK, hBC hyB⟩
    rw [fusionZStar_eq_of_center_eq_bot hZK] at hyZ
    have hle : zpowers y ≤ (pPrimeCore 2 ↥h.K).map h.K.subtype := zpowers_le.mpr hyZ
    have hodd : Odd (Nat.card ↥((pPrimeCore 2 ↥h.K).map h.K.subtype)) := by
      rw [card_map_of_injective h.K.subtype_injective]
      exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2))
    have h1 := eq_bot_of_le_two_group_of_le_odd h.toHyp52.isPGroup_B hodd
      (zpowers_le.mpr hyB) hle
    exact mem_bot.mp (h1 ▸ mem_zpowers y)
  have hKBn : h.K ≤ normalizer (h.B : Set H) := fun k hk =>
    centralizer_le_normalizer _ (hKCB hk)
  have hdec : ∀ {t : H}, t ∈ h.T → ∃ k ∈ h.K, ∃ β ∈ h.B, k * β = t := by
    intro t ht
    have h1 : t ∈ ((h.K ⊔ h.B : Subgroup H) : Set H) := hTKB ht
    rw [coe_mul_of_left_le_normalizer_right _ _ hKBn] at h1
    obtain ⟨k, hk, β, hβ, rfl⟩ := Set.mem_mul.mp h1
    exact ⟨k, hk, β, hβ, rfl⟩
  have hcommKB : ∀ {k β : H}, k ∈ h.K → β ∈ h.B → k * β = β * k := fun hk hβ =>
    (mem_centralizer_iff.mp (hKCB hk) _ hβ).symm
  have hinv : ∀ {k β : H}, k ∈ h.K → β ∈ h.B → (k * β) ^ 2 = 1 → k ^ 2 = 1 ∧ β ^ 2 = 1 := by
    intro k β hk hβ h2
    have hc := hcommKB hk hβ
    have hk2 : k ^ 2 = β⁻¹ ^ 2 := by
      have : k ^ 2 * β ^ 2 = 1 := by
        rw [pow_two, pow_two, ← h2, pow_two]
        calc k * k * (β * β) = k * (k * β) * β := by group
          _ = k * (β * k) * β := by rw [hc]
          _ = k * β * (k * β) := by group
      rw [inv_pow, eq_inv_iff_mul_eq_one]
      exact this
    have hkB : k ^ 2 = 1 := hKB1 (pow_mem hk 2) (hk2 ▸ pow_mem (inv_mem hβ) 2)
    refine ⟨hkB, ?_⟩
    rw [hkB, inv_pow, eq_comm, inv_eq_one] at hk2
    exact hk2
  obtain ⟨z, hzD, hzS, hz2⟩ := h.toHyp52.exists_involution_D_center
  have hzJ : z ∈ h.J := h.toHyp52.D_le_J hzD
  have hzS' : z ∈ h.S := h.toHyp52.D_le_S hzD
  have hza : z * h.a = h.a * z := h.toHyp52.comm_a hzS'
  have hzP : z ∉ h.P := fun hzP => by
    have := hDP ▸ mem_inf.mpr ⟨hzD, hzP⟩
    rw [mem_bot.mp this, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzx : z ∈ centralizer ({h.x} : Set H) :=
    mem_centralizer_singleton_iff.mpr (hzS h.x h.x_mem).symm
  have hfus5 : ∀ {g : H}, g ∈ h.W → g⁻¹ * h.a * g ≠ z := by
    intro g hgW hg
    obtain ⟨-, h2⟩ := hB1 H h.toHyp52 g hgW (hg ▸ hzS') (hg ▸ hzP)
    exact h2 (hg ▸ mem_inf.mpr ⟨subset_closure (Set.mem_union_left _ (SetLike.mem_coe.mpr hzD)),
      hzx⟩)
  have haK : h.a ∉ h.K := by
    intro haK
    obtain ⟨g, hgK, hg⟩ := hFus H h.toHyp52 hrow hin z hzD hzS hz2 h.a
      (mem_inf.mpr ⟨h.toHyp52.a_mem_P, haK⟩) h.orderOf_a
    exact hfus5 (hKW hgK) hg
  have haJ : h.a ∉ h.J := by
    intro haJ
    have : h.a ∈ h.D ⊓ h.P := mem_inf.mpr ⟨mem_inf.mpr ⟨h.toHyp52.a_mem_S, haJ⟩,
      h.toHyp52.a_mem_P⟩
    rw [hDP, mem_bot] at this
    have h2 := h.orderOf_a
    rw [this, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have haT : h.a ∈ h.T :=
    mem_inf.mpr ⟨mem_inf.mpr ⟨h.toHyp52.a_mem_S, h.toHyp52.a_mem_normalizer⟩,
      h.toHyp52.a_mem_P⟩
  have hBc : IsCyclic h.B := by
    have hTBc : IsCyclic (↥h.T ⧸ h.B.subgroupOf h.T) := by
      have : IsCyclic ↥(h.T ⊓ h.K) := hTKc
      set φ : ↥(h.T ⊓ h.K) →* ↥h.T ⧸ h.B.subgroupOf h.T :=
        (QuotientGroup.mk' (h.B.subgroupOf h.T)).comp (inclusion inf_le_left) with hφ
      refine isCyclic_of_surjective φ fun q => ?_
      obtain ⟨⟨t, ht⟩, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk, β, hβ, rfl⟩ := hdec ht
      have hkT : k ∈ h.T := by
        have := mul_mem ht (inv_mem (h.toHyp52.B_le_T hβ))
        rwa [mul_inv_cancel_right] at this
      refine ⟨⟨k, mem_inf.mpr ⟨hkT, hk⟩⟩, ?_⟩
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      show (⟨k, hkT⟩ : ↥h.T)⁻¹ * ⟨k * β, ht⟩ ∈ h.B.subgroupOf h.T
      rw [mem_subgroupOf]
      simp only [coe_mul, coe_inv, inv_mul_cancel_left]
      exact hβ
    obtain ⟨φ, hφ⟩ := hB7 H h
    exact isCyclic_of_surjective _ (MonoidHom.ofInjective hφ).symm.surjective
  obtain ⟨k₀, hk₀K, b, hbB, hk₀b⟩ := hdec haT
  have hab2 := hinv hk₀K hbB (by rw [hk₀b, ← h.orderOf_a, pow_orderOf_eq_one])
  have hb1 : b ≠ 1 := fun hb => haK (by rw [← hk₀b, hb, mul_one]; exact hk₀K)
  have hb2 : orderOf b = 2 := orderOf_eq_prime hab2.2 hb1
  have hbb : b * b = 1 := by rw [← pow_two]; exact hab2.2
  have hk₀ : k₀ = h.a * b := by
    rw [← hk₀b, mul_assoc, hbb, mul_one]
  have habK : h.a * b ∈ h.K := hk₀ ▸ hk₀K
  have hbS : b ∈ h.S := h.toHyp52.B_le_S hbB
  have hbT : b ∈ h.T := h.toHyp52.B_le_T hbB
  have hbP : b ∈ h.P := h.toHyp52.B_le_P hbB
  have haB : h.a * b = b * h.a := (h.toHyp52.comm_a hbS).symm
  have habT : h.a * b ∈ h.T := mul_mem haT hbT
  have habP : h.a * b ∈ h.P := mul_mem h.toHyp52.a_mem_P hbP
  have hab1 : h.a * b ≠ 1 := fun he => by
    have : h.a = b⁻¹ := eq_inv_of_mul_eq_one_left he
    rw [inv_eq_of_mul_eq_one_right hbb] at this
    exact h.toHyp52.a_not_mem_B (this ▸ hbB)
  have hab2' : (h.a * b) ^ 2 = 1 := by rw [← hk₀]; exact hab2.1
  have haborder : orderOf (h.a * b) = 2 := orderOf_eq_prime hab2' hab1
  have hxb : h.x⁻¹ * b * h.x = h.a * b := by
    set y := h.x⁻¹ * b * h.x with hy
    have hyT : y ∈ h.T := by
      have := (mem_normalizer_iff.mp (inv_mem h.x_mem_normalizer_T) b).mp hbT
      rwa [inv_inv] at this
    have hy2 : y ^ 2 = 1 := by
      rw [hy, pow_two]
      calc h.x⁻¹ * b * h.x * (h.x⁻¹ * b * h.x) = h.x⁻¹ * (b * b) * h.x := by group
        _ = 1 := by rw [hbb]; group
    have hy1 : y ≠ 1 := fun he => hb1 (by
      calc b = h.x * y * h.x⁻¹ := by rw [hy]; group
        _ = 1 := by rw [he]; group)
    have hyB : y ∉ h.B := fun hyB => by
      have hyx : y ∈ conjugate h.B h.x := by
        rw [mem_conjugate_iff, hy]
        convert hbB using 1
        group
      exact hy1 (mem_bot.mp (h.inf_conjugate_x ▸ mem_inf.mpr ⟨hyB, hyx⟩))
    have hya : y ≠ h.a := fun he => h.toHyp52.a_not_mem_B (by
      have : b = h.a := by
        calc b = h.x * y * h.x⁻¹ := by rw [hy]; group
          _ = h.x * h.a * h.x⁻¹ := by rw [he]
          _ = h.a := by rw [h.toHyp52.x_comm_a, mul_inv_cancel_right]
      exact this ▸ hbB)
    obtain ⟨k₁, hk₁K, β₁, hβ₁B, hk₁β₁⟩ := hdec hyT
    obtain ⟨hk₁2, hβ₁2⟩ := hinv hk₁K hβ₁B (by rw [hk₁β₁]; exact hy2)
    have hk₁T : k₁ ∈ h.T := by
      have := mul_mem hyT (inv_mem (h.toHyp52.B_le_T hβ₁B))
      rwa [← hk₁β₁, mul_inv_cancel_right] at this
    by_cases hk₁1 : k₁ = 1
    · exact absurd (by rw [← hk₁β₁, hk₁1, one_mul]; exact hβ₁B) hyB
    · have hk₁ab : k₁ = h.a * b := eq_of_sq_eq_one_of_isCyclic hTKc (mem_inf.mpr ⟨hk₁T, hk₁K⟩)
        (mem_inf.mpr ⟨habT, habK⟩) hk₁2 hab2' hk₁1 hab1
      by_cases hβ₁1 : β₁ = 1
      · rw [← hk₁β₁, hβ₁1, mul_one, hk₁ab]
      · have hβ₁b : β₁ = b := eq_of_sq_eq_one_of_isCyclic hBc hβ₁B hbB hβ₁2 hab2.2 hβ₁1 hb1
        exfalso
        apply hya
        rw [← hk₁β₁, hk₁ab, hβ₁b, mul_assoc, hbb, mul_one]
  obtain ⟨g, hgK, hgz⟩ := hFus H h.toHyp52 hrow hin z hzD hzS hz2 (h.a * b)
    (mem_inf.mpr ⟨habP, habK⟩) haborder
  have hgb : g * b = b * g := hcommKB hgK hbB
  set c := h.x * g with hc
  have hcb : c⁻¹ * b * c = z := by
    have hgb' : g⁻¹ * b * g = b := by rw [mul_assoc, ← hgb, ← mul_assoc, inv_mul_cancel, one_mul]
    calc c⁻¹ * b * c = g⁻¹ * (h.x⁻¹ * b * h.x) * g := by rw [hc]; group
      _ = z := by rw [hxb, hgz]
  have hbc : c * z * c⁻¹ = b := by rw [← hcb]; group
  have hBK : h.B ≤ coreActionKernel h.K := by
    have := (hB6 H h.toHyp52).1
    rwa [h.toHyp52.V_eq_K hKa] at this
  have hBsyl : ∃ R : Sylow 2 ↥(coreActionKernel h.K),
      (R : Subgroup _) = h.B.subgroupOf (coreActionKernel h.K) := by
    have := (hB6 H h.toHyp52).2
    rwa [h.toHyp52.V_eq_K hKa] at this
  have hKC : h.K ≤ centralizer ({b} : Set H) := fun k hk =>
    mem_centralizer_singleton_iff.mpr (hcommKB hk hbB)
  have habb : h.a * b ≠ b := fun he => by
    have h1 : h.a = 1 := by
      calc h.a = h.a * b * b⁻¹ := by group
        _ = 1 := by rw [he, mul_inv_cancel]
    have h2a := h.orderOf_a
    rw [h1, orderOf_one] at h2a
    exact absurd h2a (by norm_num)
  have hXne : centralizer ({b} : Set H) ≠ ⊤ := fun htop => hzP (by
    have hcX : c * b = b * c := mem_centralizer_singleton_iff.mp (htop ▸ mem_top c)
    have hcb' : c⁻¹ * b * c = b := by
      rw [mul_assoc, ← hcX, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [← hcb, hcb']
    exact hbP)
  obtain ⟨L, hKL, hLKO, hLC, hLp⟩ := hOS5 H h hrow hin hBc b hbB hb2 habK hXne
  set Cb := centralizer ({b} : Set H) with hCb
  have hdec : ∀ l ∈ L, ∃ k ∈ h.K, k⁻¹ * l ∈ oddCoreIn L := by
    intro l hl
    have hKN : h.K ≤ normalizer (oddCoreIn Cb : Set H) := fun k hk =>
      Over516.normalizer_le_normalizer_oddCoreIn Cb (le_normalizer (hKC hk))
    have hl' : l ∈ ((h.K ⊔ oddCoreIn Cb : Subgroup H) : Set H) := hLKO hl
    rw [coe_mul_of_left_le_normalizer_right _ _ hKN] at hl'
    obtain ⟨k, hk, o, ho, rfl⟩ := Set.mem_mul.mp hl'
    have hoL : o ∈ L := by
      have := mul_mem (inv_mem (hKL hk)) hl
      rwa [inv_mul_cancel_left] at this
    refine ⟨k, hk, ?_⟩
    rw [inv_mul_cancel_left]
    exact Over516.inf_oddCoreIn_le hLC ⟨hoL, ho⟩
  obtain ⟨ι, hι⟩ := Over516.exists_oddBar_equiv hKL hdec
  have hKperf : ⁅h.K, h.K⁆ = h.K := Subgroup.isPerfect_iff.mp
    (B5a.isPerfect_of_isPComponent_subgroupOf h.isPComponent_K.1 h.isPComponent_K.2)
  have hKO : ¬ h.K ≤ oddCoreIn L := fun hle => hab1 (by
    have h1 := eq_bot_of_le_two_group_of_le_odd (isPGroup_zpowers_of_sq_eq_one hab2')
      (Nat.coprime_two_left.mp (Over516.coprime_card_oddCoreIn L)) le_rfl
      (zpowers_le.mpr (hle habK))
    exact mem_bot.mp (h1 ▸ mem_zpowers _))
  have hNL : ∀ g ∈ Cb, g ∈ normalizer (h.K : Set H) → g ∈ normalizer (L : Set H) :=
    fun g hg hgK => Over516.mem_normalizer_of_isPComponent_of_le hLC hLp hKL hKperf hKO hg hgK
  have hBX : h.B ≤ Cb := fun β hβ =>
    mem_centralizer_singleton_iff.mpr (commute_of_mem_isCyclic hBc hβ hbB)
  have hBL : h.B ≤ coreActionKernel L := by
    intro β hβ
    have hβL := hNL β (hBX hβ) (hWK (le_normalizer hβ))
    refine mem_coreActionKernel.mpr ⟨hβL, fun l hl => ?_⟩
    obtain ⟨k, hk, ho⟩ := hdec l hl
    have hkβ : k⁻¹ * β⁻¹ * k = β⁻¹ := by
      have h1 := hcommKB hk hβ
      calc k⁻¹ * β⁻¹ * k = k⁻¹ * β⁻¹ * (k * β) * β⁻¹ := by group
        _ = k⁻¹ * β⁻¹ * (β * k) * β⁻¹ := by rw [h1]
        _ = β⁻¹ := by group
    have h1 : l⁻¹ * β⁻¹ * l * β = (k⁻¹ * l)⁻¹ * (β⁻¹ * (k⁻¹ * l) * β) := by
      calc l⁻¹ * β⁻¹ * l * β = (k⁻¹ * l)⁻¹ * (k⁻¹ * β⁻¹ * k) * (k⁻¹ * l) * β := by group
        _ = (k⁻¹ * l)⁻¹ * (β⁻¹ * (k⁻¹ * l) * β) := by rw [hkβ]; group
    have hβO := Over516.normalizer_le_normalizer_oddCoreIn L (inv_mem hβL)
    have h2 := (mem_normalizer_iff.mp hβO _).mp ho
    rw [inv_inv] at h2
    rw [h1]
    exact mul_mem (inv_mem ho) h2
  have hBA : h.B ≤ Cb ⊓ coreActionKernel L := le_inf hBX hBL
  have hBsylL : ∃ R : Sylow 2 ↥(Cb ⊓ coreActionKernel L),
      (R : Subgroup _) = h.B.subgroupOf (Cb ⊓ coreActionKernel L) := by
    refine Over516.exists_sylow_of_normalizer hBA h.toHyp52.isPGroup_B
      fun E hE hBE hEA hEN => ?_
    have hEK : E ≤ coreActionKernel h.K := by
      intro e he
      have heK : e ∈ normalizer (h.K : Set H) := hWK (hEN he)
      refine mem_coreActionKernel.mpr ⟨heK, fun k hk => ?_⟩
      have h1 := (mem_coreActionKernel.mp (mem_inf.mp (hEA he)).2).2 k (hKL hk)
      have h2 : k⁻¹ * e⁻¹ * k * e ∈ h.K := by
        have h3 := (mem_normalizer_iff.mp (inv_mem heK) k).mp hk
        rw [inv_inv] at h3
        rw [show k⁻¹ * e⁻¹ * k * e = k⁻¹ * (e⁻¹ * k * e) by group]
        exact mul_mem (inv_mem hk) h3
      exact Over516.inf_oddCoreIn_le hKL ⟨h2, h1⟩
    exact (Subgroup.eq_of_le_of_card_ge hBE
      (card_le_of_isPGroup_of_sylow hBK hBsyl hEK hE)).symm
  have hBinv : ∀ w ∈ Cb, w ∈ coreActionKernel L → w ^ 2 = 1 → w ≠ 1 → w = b :=
    fun w hwC hwK hw2 hw1 => eq_of_involution_of_isCyclic_sylow hBA hBsylL hBc hbB hab2.2 hb1
      (mem_inf.mpr ⟨hwC, hwK⟩) (mem_centralizer_singleton_iff.mp hwC) hw2 hw1
  have hCbN : Cb ≤ normalizer (L : Set H) :=
    centralizer_le_normalizer_of_isPComponent hLC hLp hBinv (hKL habK) hab2' hab1 habb
  have hZL : center (OddBar L) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy' : ι.symm y ∈ center (OddBar h.K) := by
      rw [Subgroup.mem_center_iff] at hy ⊢
      intro g
      apply ι.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy (ι g)
    rw [hZK, mem_bot] at hy'
    rw [mem_bot, ← ι.apply_symm_apply y, hy', map_one]
  have hlift : ∀ {w : H}, w * z = z * w → c * w * c⁻¹ ∈ centralizer ({b} : Set H) := by
    intro w hw
    rw [mem_centralizer_singleton_iff, ← hbc]
    calc c * w * c⁻¹ * (c * z * c⁻¹) = c * (w * z) * c⁻¹ := by group
      _ = c * (z * w) * c⁻¹ := by rw [hw]
      _ = c * z * c⁻¹ * (c * w * c⁻¹) := by group
  have hconj : ∀ {u v : H}, u * v = v * u →
      (c * u * c⁻¹) * (c * v * c⁻¹) = (c * v * c⁻¹) * (c * u * c⁻¹) := fun {u v} huv => by
    calc (c * u * c⁻¹) * (c * v * c⁻¹) = c * (u * v) * c⁻¹ := by group
      _ = c * (v * u) * c⁻¹ := by rw [huv]
      _ = (c * v * c⁻¹) * (c * u * c⁻¹) := by group
  set a' := c * h.a * c⁻¹ with ha'
  have ha'C : a' ∈ centralizer ({b} : Set H) := hlift hza.symm
  have ha'N : a' ∈ normalizer (L : Set H) := hCbN ha'C
  have ha'2 : a' * a' = 1 := by
    rw [ha']
    calc c * h.a * c⁻¹ * (c * h.a * c⁻¹) = c * (h.a * h.a) * c⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  set ta : ↥(normalizer (L : Set H)) := ⟨a', ha'N⟩ with hta
  set α := oddBarConj L ta with hα
  have hxz : h.x⁻¹ * z = z * h.x⁻¹ := by
    have := hzS h.x h.x_mem
    calc h.x⁻¹ * z = h.x⁻¹ * (z * h.x) * h.x⁻¹ := by group
      _ = h.x⁻¹ * (h.x * z) * h.x⁻¹ := by rw [this]
      _ = z * h.x⁻¹ := by group
  have hbz : b * z = z * b := by
    have := hzS b hbS
    exact this
  have hcomm_a : h.a = ⁅b⁻¹, h.x⁻¹⁆ := by
    have h1 : b⁻¹ * h.x⁻¹ * b * h.x = h.a := by
      calc b⁻¹ * h.x⁻¹ * b * h.x = b⁻¹ * (h.x⁻¹ * b * h.x) := by group
        _ = b⁻¹ * (h.a * b) := by rw [hxb]
        _ = b * (h.a * b) := by rw [inv_eq_of_mul_eq_one_right hbb]
        _ = h.a * (b * b) := by rw [← mul_assoc, ← haB, mul_assoc]
        _ = h.a := by rw [hbb, mul_one]
    rw [commutatorElement_def, inv_inv, inv_inv]
    exact h1.symm
  have hu : c * b⁻¹ * c⁻¹ ∈ centralizer ({b} : Set H) := hlift (by
    rw [inv_eq_of_mul_eq_one_right hbb]; exact hbz)
  have hv : c * h.x⁻¹ * c⁻¹ ∈ centralizer ({b} : Set H) := hlift hxz
  have hαinn : α ∈ (MulAut.conj : OddBar L →* MulAut (OddBar L)).range := by
    have hta' : ta = ⁅(⟨c * b⁻¹ * c⁻¹, hCbN hu⟩ : ↥(normalizer (L : Set H))),
        ⟨c * h.x⁻¹ * c⁻¹, hCbN hv⟩⁆ := by
      apply Subtype.ext
      simp only [hta, commutatorElement_def, coe_mul, coe_inv]
      rw [ha', hcomm_a, commutatorElement_def]
      group
    rw [hα, hta', map_commutatorElement]
    obtain ⟨m, hm⟩ := hOut H h.toHyp52 hrow hin
      ((MulAut.congr ι).symm (oddBarConj L ⟨c * b⁻¹ * c⁻¹, hCbN hu⟩))
      ((MulAut.congr ι).symm (oddBarConj L ⟨c * h.x⁻¹ * c⁻¹, hCbN hv⟩))
    refine ⟨ι m, ?_⟩
    rw [← Over516.congr_conj ι m, hm, map_commutatorElement, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
  obtain ⟨ℓ, hℓ⟩ := hαinn
  have hℓ2 : ℓ ^ 2 = 1 := by
    have h1 : MulAut.conj (ℓ ^ 2) = 1 := by
      rw [map_pow, hℓ, hα, ← map_pow, pow_two, show ta * ta = 1 from Subtype.ext ha'2,
        map_one]
    have hc : ℓ ^ 2 ∈ center (OddBar L) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h2 := congrArg (fun φ : MulAut (OddBar L) => φ w) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc w * ℓ ^ 2 = (ℓ ^ 2 * w * (ℓ ^ 2)⁻¹) * ℓ ^ 2 := by rw [h2]
        _ = ℓ ^ 2 * w := by group
    rw [hZL] at hc
    exact mem_bot.mp hc
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  set πJ := QuotientGroup.mk' (pPrimeCore 2 ↥h.J) with hπJ
  have hzN : z ∈ normalizer (h.J : Set H) := le_normalizer hzJ
  have hz2' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  obtain ⟨e, he2, hez, heJ, hez'⟩ : ∃ e : H, orderOf e = 2 ∧ e ≠ z ∧ e ∈ h.J ∧ e * z = z * e := by
    set zbar : OddBar h.J := πJ ⟨z, hzJ⟩ with hzbar
    have hzbar2 : orderOf zbar = 2 := by
      apply orderOf_eq_prime
      · rw [← map_pow]
        have : (⟨z, hzJ⟩ : h.J) ^ 2 = 1 := Subtype.ext (by
          rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hz2, pow_orderOf_eq_one])
        rw [this, map_one]
      · intro he
        rw [hzbar, hπJ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at he
        have hdvd : orderOf (⟨z, hzJ⟩ : h.J) ∣ Nat.card (pPrimeCore 2 ↥h.J) := by
          have := orderOf_dvd_natCard (⟨⟨z, hzJ⟩, he⟩ : pPrimeCore 2 ↥h.J)
          rwa [Subgroup.orderOf_mk] at this
        rw [Subgroup.orderOf_mk, hz2] at hdvd
        exact absurd (Nat.Coprime.coprime_dvd_right hdvd
          (CFSG.pPrimeCore_coprime_card (p := 2))) (by norm_num)
    obtain ⟨ubar, hu2, huz, huc⟩ := hInv (OddBar h.J) p f hp hp2 hf hJlie zbar hzbar2
    obtain ⟨u₀, rfl⟩ := QuotientGroup.mk_surjective ubar
    have hfix : oddBarConj h.J ⟨z, hzN⟩ (u₀ : OddBar h.J) = u₀ := by
      rw [oddBarConj_apply_mk]
      have : ((⟨z * u₀ * z⁻¹, (mem_normalizer_iff.mp hzN u₀).mp u₀.2⟩ : h.J) : OddBar h.J) =
          zbar * (u₀ : OddBar h.J) * zbar⁻¹ := by
        rw [hzbar, hπJ, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
          ← QuotientGroup.mk_mul]
        rfl
      rw [this, ← huc, mul_inv_cancel_right]
    obtain ⟨u', hu', hu'z⟩ := exists_fixed_lift hz2' hfix
    obtain ⟨k, ⟨n, hn⟩, hk⟩ := exists_pow_twoPower_map_eq πJ u' (by
      rw [hπJ, QuotientGroup.mk'_apply, hu', ← orderOf_dvd_iff_pow_eq_one, hu2])
    set e₀ : h.J := u' ^ k with he₀
    have he₀u : πJ e₀ = (u₀ : OddBar h.J) := by rw [he₀, hk, hπJ, QuotientGroup.mk'_apply, hu']
    have he₀1 : e₀ ≠ 1 := fun he => by
      rw [he, map_one] at he₀u
      rw [← he₀u, orderOf_one] at hu2
      exact absurd hu2 (by norm_num)
    have he₀2 : e₀ ^ 2 = 1 := by
      have hker : e₀ ^ 2 ∈ pPrimeCore 2 ↥h.J := by
        rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπJ, map_pow, he₀u,
          ← orderOf_dvd_iff_pow_eq_one, hu2]
      have hdvd1 : orderOf (e₀ ^ 2) ∣ Nat.card (pPrimeCore 2 ↥h.J) := by
        have := orderOf_dvd_natCard (⟨e₀ ^ 2, hker⟩ : pPrimeCore 2 ↥h.J)
        rwa [Subgroup.orderOf_mk] at this
      have hdvd2 : orderOf (e₀ ^ 2) ∣ 2 ^ n := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← pow_mul, mul_comm, pow_mul, hn, one_pow]
      have hcop : Nat.Coprime (2 ^ n) (Nat.card (pPrimeCore 2 ↥h.J)) :=
        Nat.Coprime.pow_left n (CFSG.pPrimeCore_coprime_card (p := 2))
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvd1)
    refine ⟨(e₀ : H), ?_, ?_, e₀.2, ?_⟩
    · rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime he₀2 he₀1
    · intro he
      apply huz
      rw [← he₀u, hzbar]
      congr 1
      exact Subtype.ext he
    · rw [he₀, SubgroupClass.coe_pow]
      exact ((Commute.pow_left (show Commute (u' : H) z from
        (show (z : H) * u' = u' * z from hu'z).symm) k).eq)
  have hea : e * h.a = h.a * e :=
    (mem_centralizer_singleton_iff.mp (h.J_le heJ))
  have hee : e * e = 1 := by rw [← pow_two, ← he2, pow_orderOf_eq_one]
  set e' := c * e * c⁻¹ with he'
  have he'C : e' ∈ centralizer ({b} : Set H) := hlift hez'
  have he'N : e' ∈ normalizer (L : Set H) := hCbN he'C
  have he'2 : e' * e' = 1 := by
    rw [he']
    calc c * e * c⁻¹ * (c * e * c⁻¹) = c * (e * e) * c⁻¹ := by group
      _ = 1 := by rw [hee]; group
  set te : ↥(normalizer (L : Set H)) := ⟨e', he'N⟩ with hte
  set ε := oddBarConj L te with hε
  have hε2 : ε ^ 2 = 1 := by
    rw [hε, ← map_pow, pow_two, show te * te = 1 from Subtype.ext he'2, map_one]
  have hα2 : α ^ 2 = 1 := by
    rw [hα, ← map_pow, pow_two, show ta * ta = 1 from Subtype.ext ha'2, map_one]
  have hea' : e' * a' = a' * e' := hconj hea
  have hεα : ε * α = α * ε := by
    rw [hε, hα, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hea'
  have hε1 : ε ≠ 1 := by
    intro hε1
    have he'K : e' ∈ coreActionKernel L := mem_coreActionKernel_of_oddBarConj_eq_one hε1
    have he'1 : e' ≠ 1 := fun he => by
      have : e = 1 := by
        calc e = c⁻¹ * e' * c := by rw [he']; group
          _ = 1 := by rw [he]; group
      rw [this, orderOf_one] at he2
      exact absurd he2 (by norm_num)
    have he'b := hBinv e' he'C he'K (by rw [pow_two]; exact he'2) he'1
    apply hez
    calc e = c⁻¹ * e' * c := by rw [he']; group
      _ = z := by rw [he'b, hcb]
  have hεα' : ε ≠ MulAut.conj ℓ := by
    rw [hℓ]
    intro hεeq
    set w := a' * e' with hw
    have hwC : w ∈ centralizer ({b} : Set H) := mul_mem ha'C he'C
    have hw1 : oddBarConj L ⟨w, hCbN hwC⟩ = 1 := by
      have : (⟨w, hCbN hwC⟩ : ↥(normalizer (L : Set H))) = ta * te := Subtype.ext rfl
      rw [this, map_mul, ← hα, ← hε, hεeq, ← pow_two, hα2]
    have hwK := mem_coreActionKernel_of_oddBarConj_eq_one hw1
    have hw2 : w * w = 1 := by
      rw [hw]
      calc a' * e' * (a' * e') = a' * (e' * a') * e' := by group
        _ = a' * (a' * e') * e' := by rw [hea']
        _ = (a' * a') * (e' * e') := by group
        _ = 1 := by rw [ha'2, he'2, one_mul]
    have hw1' : w ≠ 1 := fun he => by
      apply haJ
      have : h.a = e := by
        have h1 : a' = e' := by
          calc a' = a' * (e' * e') := by rw [he'2, mul_one]
            _ = (a' * e') * e' := by group
            _ = e' := by rw [← hw, he, one_mul]
        calc h.a = c⁻¹ * a' * c := by rw [ha']; group
          _ = c⁻¹ * e' * c := by rw [h1]
          _ = e := by rw [he']; group
      exact this ▸ heJ
    have hwb := hBinv w hwC hwK (by rw [pow_two]; exact hw2) hw1'
    apply haJ
    have hae : h.a * e = z := by
      calc h.a * e = c⁻¹ * w * c := by rw [hw, ha', he']; group
        _ = z := by rw [hwb, hcb]
    have : h.a = z * e := by
      calc h.a = h.a * e * e := by rw [mul_assoc, hee, mul_one]
        _ = z * e := by rw [hae]
    exact this ▸ mul_mem hzJ heJ
  set CK : Subgroup ↥L := (centralizer ({a'} : Set H)).subgroupOf L with hCK
  have hCKmap : CK.map π = centralizer ({ℓ} : Set (OddBar L)) := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hfixk : α (π k) = π k := by
        rw [hα, hπ, QuotientGroup.mk'_apply, oddBarConj_apply_mk]
        congr 1
        apply Subtype.ext
        show a' * k * a'⁻¹ = k
        have := mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp hk)
        rw [← this, mul_inv_cancel_right]
      rw [← hℓ, MulAut.conj_apply] at hfixk
      calc π k * ℓ = (ℓ * π k * ℓ⁻¹) * ℓ := by rw [hfixk]
        _ = ℓ * π k := by group
    · intro w hw
      obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective w
      have hfix : oddBarConj L ta (y₀ : OddBar L) = y₀ := by
        rw [← hα, ← hℓ, MulAut.conj_apply]
        have := mem_centralizer_singleton_iff.mp hw
        rw [← this, mul_inv_cancel_right]
      obtain ⟨y', hy', hyt⟩ := exists_fixed_lift ha'2 hfix
      exact ⟨y', mem_subgroupOf.mpr (mem_centralizer_singleton_iff.mpr hyt.symm), hy'⟩
  have hτa : ∀ k ∈ CK, (c⁻¹ * (k : H) * c) * h.a = h.a * (c⁻¹ * (k : H) * c) := by
    intro k hk
    have h1 : (k : H) * a' = a' * k := mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp hk)
    calc c⁻¹ * k * c * h.a = c⁻¹ * ((k : H) * (c * h.a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * h.a * c⁻¹) * k) * c := by rw [← ha', h1]
      _ = h.a * (c⁻¹ * k * c) := by group
  have hτz : ∀ k : ↥L, (c⁻¹ * (k : H) * c) * z = z * (c⁻¹ * (k : H) * c) := by
    intro k
    have h1 : (k : H) * b = b * k := mem_centralizer_singleton_iff.mp (hLC k.2)
    calc c⁻¹ * k * c * z = c⁻¹ * ((k : H) * (c * z * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * z * c⁻¹) * k) * c := by rw [hbc, h1]
      _ = z * (c⁻¹ * k * c) := by group
  have hτN : ∀ k ∈ CK, c⁻¹ * (k : H) * c ∈ normalizer (h.J : Set H) := fun k hk =>
    hCaN (mem_centralizer_singleton_iff.mpr (hτa k hk))
  have hconjK : ∀ {k : H}, k ∈ L → e' * k * e'⁻¹ ∈ L := fun {k} hk =>
    (mem_normalizer_iff.mp he'N k).mp hk
  set N := centralizerCore516 (p ^ f) ℓ with hN
  have hℓ2' : (ι.symm ℓ) ^ 2 = 1 := by rw [← map_pow, hℓ2, map_one]
  obtain ⟨hON₀, hPSpε₀⟩ := hPSp H h.toHyp52 hrow hin p f hp hp2 hf hJlie (ι.symm ℓ) hℓ2'
  have hNmap : (centralizerCore516 (p ^ f) (ι.symm ℓ)).map ι.toMonoidHom = N := by
    rw [Over516.map_centralizerCore516, MulEquiv.apply_symm_apply]
  have hON : pPrimeCore 2 ↥N = ⊥ := by
    rw [← hNmap, ← pPrimeCore_map_iso 2 ((centralizerCore516 (p ^ f) (ι.symm ℓ)).equivMapOfInjective
      ι.toMonoidHom ι.injective), hON₀, Subgroup.map_bot]
  have hPSpε : ∀ ε₁ : MulAut (OddBar L), ε₁ ^ 2 = 1 → ε₁ ≠ 1 → ε₁ ≠ MulAut.conj ℓ →
      ε₁ * MulAut.conj ℓ = MulAut.conj ℓ * ε₁ → (∀ y ∈ N, ε₁ y = y) →
      ∃ M : Subgroup (OddBar L), (∀ y ∈ M, ε₁ y = y) ∧ Blueprint.LieModel ↥M .PSp 2 p f := by
    intro ε₁ h2 h1 hℓε hcε hNε
    set ε₀ := (MulAut.congr ι).symm ε₁ with hε₀def
    have hε₀ : MulAut.congr ι ε₀ = ε₁ := MulEquiv.apply_symm_apply _ _
    have hε₀y : ∀ y : OddBar h.K, ι (ε₀ y) = ε₁ (ι y) := fun y => by
      rw [← hε₀, MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have hcℓ : MulAut.congr ι (MulAut.conj (ι.symm ℓ)) = MulAut.conj ℓ := by
      rw [Over516.congr_conj, MulEquiv.apply_symm_apply]
    obtain ⟨M₀, hM₀fix, hM₀lie⟩ := hPSpε₀ ε₀
      ((MulAut.congr ι).injective (by rw [map_pow, hε₀, h2, map_one]))
      (fun he => h1 (by rw [← hε₀, he, map_one]))
      (fun he => hℓε (by rw [← hε₀, he, hcℓ]))
      ((MulAut.congr ι).injective (by rw [map_mul, map_mul, hε₀, hcℓ, hcε]))
      (fun y hy => by
        apply ι.injective
        have hιy : ι y ∈ N := hNmap ▸ mem_map_of_mem ι.toMonoidHom hy
        rw [hε₀y, hNε (ι y) hιy])
    refine ⟨M₀.map ι.toMonoidHom, ?_, lieModel_of_mulEquiv_ne_zero
      (M₀.equivMapOfInjective ι.toMonoidHom ι.injective) (by norm_num) hM₀lie⟩
    rintro _ ⟨m, hm, rfl⟩
    show ε₁ (ι m) = ι m
    rw [← hε₀y, hM₀fix m hm]
  obtain ⟨hzbar2, hsolv, h2grp⟩ : ∃ _ : orderOf (πJ ⟨z, hzJ⟩) = 2,
      Group.IsSolvable ↥(MulAction.stabilizer (MulAut (OddBar h.J)) (πJ ⟨z, hzJ⟩)) ∧
      (p ^ f = 3 → IsPGroup 2 ↥(MulAction.stabilizer (MulAut (OddBar h.J)) (πJ ⟨z, hzJ⟩))) := by
    have hzbar2 : orderOf (πJ ⟨z, hzJ⟩) = 2 := by
      apply orderOf_eq_prime
      · rw [← map_pow]
        have : (⟨z, hzJ⟩ : h.J) ^ 2 = 1 := Subtype.ext (by
          rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hz2, pow_orderOf_eq_one])
        rw [this, map_one]
      · intro he
        rw [hπJ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at he
        have hdvd : orderOf (⟨z, hzJ⟩ : h.J) ∣ Nat.card (pPrimeCore 2 ↥h.J) := by
          have := orderOf_dvd_natCard (⟨⟨z, hzJ⟩, he⟩ : pPrimeCore 2 ↥h.J)
          rwa [Subgroup.orderOf_mk] at this
        rw [Subgroup.orderOf_mk, hz2] at hdvd
        exact absurd (Nat.Coprime.coprime_dvd_right hdvd
          (CFSG.pPrimeCore_coprime_card (p := 2))) (by norm_num)
    exact ⟨hzbar2, hStab (OddBar h.J) p f hp hp2 hf hJlie _ hzbar2⟩
  obtain ⟨Ñ, hÑC, hNÑ, hÑJ, hÑe⟩ : ∃ Ñ : Subgroup ↥L, Ñ ≤ CK ∧ Ñ.map π = N ∧
      (∀ k ∈ Ñ, c⁻¹ * (k : H) * c ∈ coreActionKernel h.J) ∧
      ∀ k ∈ Ñ, ∃ k' ∈ Ñ, (k' : H) = e' * k * e'⁻¹ := by
    by_cases hq3 : p ^ f = 3
    ·
      set Ñ : Subgroup ↥L := closure {k : ↥L | k ∈ CK ∧ Odd (orderOf k)} with hÑ
      refine ⟨Ñ, (closure_le _).mpr fun k hk => hk.1, ?_, ?_, ?_⟩
      · rw [hN, centralizerCore516, ite_eq_left hq3, hÑ, MonoidHom.map_closure]
        congr 1
        ext w
        constructor
        · rintro ⟨k, ⟨hk, hkodd⟩, rfl⟩
          refine ⟨hCKmap ▸ mem_map_of_mem π hk, ?_⟩
          exact hkodd.of_dvd_nat (orderOf_map_dvd π k)
        · rintro ⟨hw, hwodd⟩
          rw [← hCKmap] at hw
          obtain ⟨k, hk, rfl⟩ := hw
          obtain ⟨n, hnodd, hne⟩ := exists_pow_odd_orderOf_map_eq π k hwodd
          exact ⟨k ^ n, ⟨pow_mem hk n, hnodd⟩, hne⟩
      · set S' : Subgroup ↥L := ((coreActionKernel h.J).comap
          (MulAut.conj c⁻¹).toMonoidHom).comap L.subtype with hS'
        have hmemS' : ∀ {k : ↥L}, k ∈ S' ↔ c⁻¹ * (k : H) * c ∈ coreActionKernel h.J := by
          intro k
          simp only [hS', mem_comap, subtype_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            inv_inv]
        have hle : Ñ ≤ S' := by
          rw [hÑ, closure_le]
          rintro k ⟨hk, hkodd⟩
          rw [SetLike.mem_coe, hmemS']
          have hodd' : Odd (orderOf (c⁻¹ * (k : H) * c)) := by
            have h1 : c⁻¹ * (k : H) * c = (MulAut.conj c⁻¹).toMonoidHom (k : H) := by
              simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
            rw [h1, orderOf_injective _ (MulAut.conj c⁻¹).injective, Subgroup.orderOf_coe]
            exact hkodd
          exact mem_coreActionKernel_of_odd hzJ (hτN k hk) (hτz k) (h2grp hq3) hodd'
        exact fun k hk => hmemS'.mp (hle hk)
      ·
        set ψ : ↥L →* ↥L :=
          { toFun := fun k => ⟨e' * k * e'⁻¹, hconjK k.2⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun k₁ k₂ => Subtype.ext (by simp only [coe_mul]; group) } with hψ
        have hψinj : Function.Injective ψ := fun k₁ k₂ hk => by
          have h1 : e' * (k₁ : H) * e'⁻¹ = e' * k₂ * e'⁻¹ := congrArg Subtype.val hk
          apply Subtype.ext
          calc (k₁ : H) = e'⁻¹ * (e' * k₁ * e'⁻¹) * e' := by group
            _ = e'⁻¹ * (e' * k₂ * e'⁻¹) * e' := by rw [h1]
            _ = k₂ := by group
        have hle : Ñ ≤ Ñ.comap ψ := by
          rw [hÑ, closure_le]
          rintro k ⟨hk, hkodd⟩
          rw [SetLike.mem_coe, mem_comap]
          apply Subgroup.subset_closure
          refine ⟨?_, ?_⟩
          · rw [hCK, mem_subgroupOf, mem_centralizer_singleton_iff]
            show e' * k * e'⁻¹ * a' = a' * (e' * k * e'⁻¹)
            have h1 : (k : H) * a' = a' * k :=
              mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp hk)
            calc e' * k * e'⁻¹ * a' = e' * ((k : H) * (e'⁻¹ * a' * e')) * e'⁻¹ := by group
              _ = e' * ((k : H) * a') * e'⁻¹ := by
                rw [show e'⁻¹ * a' * e' = a' by
                  rw [mul_assoc, ← hea', ← mul_assoc, inv_mul_cancel, one_mul]]
              _ = e' * (a' * k) * e'⁻¹ := by rw [h1]
              _ = (e' * a' * e'⁻¹) * (e' * k * e'⁻¹) := by group
              _ = a' * (e' * k * e'⁻¹) := by rw [hea', mul_inv_cancel_right]
          · rw [orderOf_injective ψ hψinj k]
            exact hkodd
        exact fun k hk => ⟨ψ k, hle hk, rfl⟩
    ·
      refine ⟨Quasithin.perfectCore CK, Quasithin.perfectCore_le CK, ?_, ?_, ?_⟩
      · rw [Quasithin.map_perfectCore, hCKmap, hN, centralizerCore516, ite_eq_right hq3]
      · set X : Subgroup H := ((Quasithin.perfectCore CK).map L.subtype).map
          (MulAut.conj c⁻¹).toMonoidHom with hX
        have hmemX : ∀ {k : ↥L}, k ∈ Quasithin.perfectCore CK → c⁻¹ * (k : H) * c ∈ X :=
          fun {k} hk => ⟨k, ⟨k, hk, rfl⟩, by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
        have hXC : ∀ x ∈ X, ∃ k ∈ CK, x = c⁻¹ * (k : H) * c := by
          rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
          refine ⟨k, Quasithin.perfectCore_le CK hk, ?_⟩
          simp only [subtype_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        have hXN : X ≤ normalizer (h.J : Set H) := fun x hx => by
          obtain ⟨k, hk, rfl⟩ := hXC x hx
          exact hτN k hk
        have hXz : ∀ x ∈ X, x * z = z * x := fun x hx => by
          obtain ⟨k, -, rfl⟩ := hXC x hx
          exact hτz k
        have hXperf : ⁅X, X⁆ = X := by
          rw [hX, ← map_commutator, ← map_commutator, Quasithin.perfectCore_perfect]
        have hXle := le_coreActionKernel_of_perfect hzJ hXN hXz hsolv hXperf
        exact fun k hk => hXle (hmemX hk)
      ·
        set ψ : ↥L →* ↥L :=
          { toFun := fun k => ⟨e' * k * e'⁻¹, hconjK k.2⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun k₁ k₂ => Subtype.ext (by simp only [coe_mul]; group) } with hψ
        have hCKψ : CK.map ψ ≤ CK := by
          rintro _ ⟨k, hk, rfl⟩
          rw [hCK, mem_subgroupOf, mem_centralizer_singleton_iff]
          show e' * k * e'⁻¹ * a' = a' * (e' * k * e'⁻¹)
          have h1 : (k : H) * a' = a' * k :=
            mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp hk)
          calc e' * k * e'⁻¹ * a' = e' * ((k : H) * (e'⁻¹ * a' * e')) * e'⁻¹ := by group
            _ = e' * ((k : H) * a') * e'⁻¹ := by
              rw [show e'⁻¹ * a' * e' = a' by
                rw [mul_assoc, ← hea', ← mul_assoc, inv_mul_cancel, one_mul]]
            _ = e' * (a' * k) * e'⁻¹ := by rw [h1]
            _ = (e' * a' * e'⁻¹) * (e' * k * e'⁻¹) := by group
            _ = a' * (e' * k * e'⁻¹) := by rw [hea', mul_inv_cancel_right]
        have hle : (Quasithin.perfectCore CK).map ψ ≤ Quasithin.perfectCore CK := by
          rw [Quasithin.map_perfectCore]
          exact Quasithin.perfectCore_mono hCKψ
        exact fun k hk => ⟨ψ k, hle ⟨k, hk, rfl⟩, rfl⟩
  set OJ : Subgroup H := conjugate ((pPrimeCore 2 ↥h.J).map h.J.subtype) c⁻¹ with hOJ
  have hOJodd : Nat.Coprime 2 (Nat.card OJ) := by
    rw [hOJ, conjugate, card_map_of_injective (MulAut.conj c⁻¹⁻¹).injective,
      card_map_of_injective h.J.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card (p := 2)
  set Z₀ : Subgroup ↥L := Ñ ⊓ OJ.comap L.subtype with hZ₀
  have hZ₀map : Z₀.map π = ⊥ := by
    have hZ₀N : Z₀.map π ≤ N := by rw [← hNÑ]; exact map_mono inf_le_left
    have hnorm : ((Z₀.map π).subgroupOf N).Normal := by
      constructor
      intro y hy n
      rw [mem_subgroupOf] at hy ⊢
      obtain ⟨t, ht, hte⟩ := mem_map.mp hy
      have hn : (n : OddBar L) ∈ Ñ.map π := by rw [hNÑ]; exact n.2
      obtain ⟨k₀, hk₀, hk₀e⟩ := mem_map.mp hn
      refine ⟨k₀ * t * k₀⁻¹, mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact mul_mem (mul_mem hk₀ (mem_inf.mp ht).1) (inv_mem hk₀)
      · have htO : (t : H) ∈ OJ := (mem_inf.mp ht).2
        rw [hOJ, mem_conjugate_iff] at htO
        show ((k₀ * t * k₀⁻¹ : ↥L) : H) ∈ OJ
        rw [hOJ, mem_conjugate_iff]
        have hk₀N : c⁻¹ * (k₀ : H) * c ∈ normalizer (h.J : Set H) := hτN k₀ (hÑC hk₀)
        have hON := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic h.J
          (pPrimeCore 2 ↥h.J) hk₀N
        have := (mem_normalizer_iff.mp hON _).mp htO
        convert this using 1
        simp only [coe_mul, coe_inv, inv_inv]
        group
      · rw [map_mul, map_mul, map_inv, hk₀e, hte]
        rfl
    have hcop : Nat.Coprime 2 (Nat.card ((Z₀.map π).subgroupOf N)) := by
      have h1 : Nat.card ((Z₀.map π).subgroupOf N) = Nat.card (Z₀.map π) := by
        rw [← Subgroup.card_map_of_injective N.subtype_injective, subgroupOf_map_subtype,
          inf_of_le_left hZ₀N]
      have h2 : Nat.card (Z₀.map π) ∣ Nat.card Z₀ := Subgroup.card_map_dvd Z₀ π
      have h3 : Nat.card Z₀ ∣ Nat.card OJ := by
        have hle : Z₀.map L.subtype ≤ OJ := by
          rintro _ ⟨t, ht, rfl⟩
          exact (mem_inf.mp ht).2
        rw [← Subgroup.card_map_of_injective L.subtype_injective]
        exact Subgroup.card_dvd_of_le hle
      rw [h1]
      exact Nat.Coprime.coprime_dvd_right (h2.trans h3) hOJodd
    have hle := LocalAnalysis.ComponentInitial.le_pPrimeCore hnorm hcop
    rw [hON] at hle
    rw [eq_bot_iff]
    intro y hy
    have := hle (mem_subgroupOf.mpr (show ((⟨y, hZ₀N hy⟩ : N) : OddBar L) ∈ Z₀.map π from hy))
    rw [mem_bot] at this ⊢
    exact congrArg Subtype.val this
  have hεN : ∀ y ∈ N, ε y = y := by
    intro y hy
    rw [← hNÑ] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    obtain ⟨k', hk'Ñ, hk'e⟩ := hÑe k hk
    have hd : k⁻¹ * k' ∈ Z₀ := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem hk) hk'Ñ, ?_⟩
      rw [mem_comap, subtype_apply, coe_mul, coe_inv, hk'e, hOJ, mem_conjugate_iff]
      have hwK := hÑJ k hk
      obtain ⟨-, hc⟩ := mem_coreActionKernel.mp hwK
      have h1 := hc e heJ
      have heN : e ∈ normalizer (((pPrimeCore 2 ↥h.J).map h.J.subtype : Subgroup H) : Set H) :=
        UnbalancedGS.normalizer_le_normalizer_map_of_characteristic h.J (pPrimeCore 2 ↥h.J)
          (le_normalizer heJ)
      have h2 := (mem_normalizer_iff.mp heN _).mp h1
      convert h2 using 1
      rw [he', inv_inv]
      group
    have hπd : π (k⁻¹ * k') = 1 := by
      have : π (k⁻¹ * k') ∈ Z₀.map π := mem_map_of_mem π hd
      rw [hZ₀map, mem_bot] at this
      exact this
    have hkk' : π k' = π k := by
      rw [map_mul, map_inv, inv_mul_eq_one] at hπd
      exact hπd.symm
    show oddBarConj L te ((k : ↥L) : OddBar L) = ((k : ↥L) : OddBar L)
    rw [oddBarConj_apply_mk]
    have hkk'' : (⟨(te : H) * k * (te : H)⁻¹, (mem_normalizer_iff.mp te.2 k).mp k.2⟩ : ↥L) =
        k' := Subtype.ext hk'e.symm
    rw [hkk'']
    exact hkk'
  obtain ⟨M, hMfix, hMlie⟩ := hPSpε ε hε2 hε1 hεα' (by rw [hℓ]; exact hεα) hεN
  have hYA : ∀ y ∈ Cb, ∀ g ∈ Cb ⊓ coreActionKernel L, y * g * y⁻¹ ∈ Cb ⊓ coreActionKernel L := by
    intro y hy g hg
    refine mem_inf.mpr ⟨mul_mem (mul_mem hy (mem_inf.mp hg).1) (inv_mem hy), ?_⟩
    have h1 := GSLit.conj_mem_coreActionKernel_conjugate (mem_inf.mp hg).2 y⁻¹
    rwa [inv_inv, conjugate_eq_of_mem_normalizer (inv_mem (hCbN hy))] at h1
  obtain ⟨y, hyY, hyW⟩ := exists_conj_mem_normalizer_of_sylow hBX hBA hBsylL hYA he'C
    (by rw [pow_two]; exact he'2)
  have hyN : y ∈ normalizer (L : Set H) := hCbN hyY
  set w₀ := y * e' * y⁻¹ with hw₀
  have hw₀C : w₀ ∈ Cb := mul_mem (mul_mem hyY he'C) (inv_mem hyY)
  have hw₀N : w₀ ∈ normalizer (L : Set H) := hCbN hw₀C
  have hw₀K : w₀ ∈ normalizer (h.K : Set H) := hWK hyW
  have hw₀2 : w₀ * w₀ = 1 := by
    rw [hw₀]
    calc y * e' * y⁻¹ * (y * e' * y⁻¹) = y * (e' * e') * y⁻¹ := by group
      _ = 1 := by rw [he'2]; group
  set ty : ↥(normalizer (L : Set H)) := ⟨y, hyN⟩ with hty
  set φ := oddBarConj L ty with hφ
  have hw₀φ : oddBarConj L ⟨w₀, hw₀N⟩ = φ * ε * φ⁻¹ := by
    have : (⟨w₀, hw₀N⟩ : ↥(normalizer (L : Set H))) = ty * te * ty⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv]
  have hw₀ι : ∀ y' : OddBar h.K,
      ι (oddBarConj h.K ⟨w₀, hw₀K⟩ y') = oddBarConj L ⟨w₀, hw₀N⟩ (ι y') :=
    Over516.oddBar_equiv_conj hKL hι hw₀K hw₀N
  have hw₀1 : oddBarConj h.K ⟨w₀, hw₀K⟩ ≠ 1 := by
    intro h1
    apply hε1
    have h2 : oddBarConj L ⟨w₀, hw₀N⟩ = 1 := by
      ext y'
      obtain ⟨y₀, rfl⟩ := ι.surjective y'
      rw [← hw₀ι, h1, MulAut.one_apply, MulAut.one_apply]
    rw [hw₀φ] at h2
    calc ε = φ⁻¹ * (φ * ε * φ⁻¹) * φ := by group
      _ = 1 := by rw [h2]; group
  set M' : Subgroup (OddBar h.K) := (M.map φ.toMonoidHom).map ι.symm.toMonoidHom with hM'
  have hM'fix : ∀ y' ∈ M', oddBarConj h.K ⟨w₀, hw₀K⟩ y' = y' := by
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    apply ι.injective
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hw₀ι, MulEquiv.apply_symm_apply, hw₀φ, MulAut.mul_apply, MulAut.mul_apply,
      MulAut.inv_apply, MulEquiv.symm_apply_apply, hMfix m hm]
  have hM'lie : Blueprint.LieModel ↥M' .PSp 2 p f :=
    lieModel_of_mulEquiv_ne_zero ((M.equivMapOfInjective φ.toMonoidHom φ.injective).trans
      ((M.map φ.toMonoidHom).equivMapOfInjective ι.symm.toMonoidHom ι.symm.injective))
      (by norm_num) hMlie
  exact hNoPSp H h.toHyp52 hrow hin p f hp hp2 hf hJlie w₀ hw₀K hyW hw₀2 hw₀1
    ⟨M', hM'fix, hM'lie⟩

end Hyp59

theorem row516Inner_of_inputs (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hStab : CFAutL2Stab) (hZ : CFRow516InnerCenter)
    (hFus : CFRow516InnerFusion) (hTK : CFRow516InnerT) (hOut : CFRow516InnerOut)
    (hPSp : CFRow516InnerPSp) (hNoPSp : CFRow516NoPSp) (hInv : CFL2InvPair)
    (hOS5 : Row516CentralizerStatement) : Row516InnerStatement :=
  fun _ _ _ h hrow hin => h.false_of_row516_inner hB1 hB6 hB7 hCF23 hCF24 hCFc hStab hZ hFus
    hTK hOut hPSp hNoPSp hInv hOS5 hrow hin

theorem elim516_of_catalogue (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCFi : CFProp23IndexElim) (hST : SuzukiTausskyInput)
    (hFus : CFProp23Row516) (hStab : CFAutL2Stab) (hCent : CF516Cent)
    (hZ : CFRow516InnerCenter) (hFusI : CFRow516InnerFusion) (hTK : CFRow516InnerT)
    (hOut : CFRow516InnerOut) (hPSp : CFRow516InnerPSp) (hNoPSp : CFRow516NoPSp)
    (hInv : CFL2InvPair) (hOS5 : Row516CentralizerStatement) (hsec : SectionStatement) :
    Elim516Statement :=
  elim516_of_inputs hB1 hB6 hB7 hCF23 hCF24 hCFc hCFi hST hFus hStab hCent
    (row516Inner_of_inputs hB1 hB6 hB7 hCF23 hCF24 hCFc hStab hZ hFusI hTK hOut hPSp hNoPSp
      hInv hOS5) hsec

end CFSG.ComponentClassification.GSThmB
