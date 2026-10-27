module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterLocalPlus

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Semidihedral.UnitaryBranch
  CFSG.Semidihedral.Principal
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card exists_isSylowOf)

theorem conj_eq_inv_of_swap {K : Type} [Field K] {x y : Omega K} (hxy : x ≠ y)
    {n w : Equiv.Perm (Omega K)} (hnD : n ∈ coordinateD K) (hnx : n x = y) (hny : n y = x)
    (hwD : w ∈ coordinateD K) (hwx : w x = x) (hwy : w y = y) : n * w * n⁻¹ = w⁻¹ := by
  obtain ⟨g, hg, hgx, hgy⟩ := exists_coordinateG_infinity_zero (F := K) hxy
  have hgD := coordinateG_le_D K hg
  have hginv : ∀ z, g⁻¹ (g z) = z := fun z => by
    rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  have hn'D : g⁻¹ * n * g ∈ coordinateD K :=
    (coordinateD K).mul_mem ((coordinateD K).mul_mem ((coordinateD K).inv_mem hgD) hnD) hgD
  have hw'D : g⁻¹ * w * g ∈ coordinateD K :=
    (coordinateD K).mul_mem ((coordinateD K).mul_mem ((coordinateD K).inv_mem hgD) hwD) hgD
  have hn'1 : (g⁻¹ * n * g) none = some 0 := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgx, hnx, ← hgy, hginv]
  have hn'2 : (g⁻¹ * n * g) (some 0) = none := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgy, hny, ← hgx, hginv]
  have hw'1 : (g⁻¹ * w * g) none = none := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgx, hwx, ← hgx, hginv]
  have hw'2 : (g⁻¹ * w * g) (some 0) = some 0 := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgy, hwy, ← hgy, hginv]
  obtain ⟨c, hc⟩ := eq_multiplier_of_fixes_infty_zero hw'D hw'1 hw'2
  rcases eq_multiplier_or_of_preserves K hn'D (Or.inr ⟨hn'1, hn'2⟩) with ⟨μ, hμ⟩ | ⟨μ, hμ⟩
  · exfalso
    rw [hμ, multiplier_none] at hn'1
    exact Option.some_ne_none _ hn'1.symm
  · have hcomm : multiplier K μ * multiplier K c⁻¹ = multiplier K c⁻¹ * multiplier K μ := by
      rw [← multiplierHom_apply, ← multiplierHom_apply, ← map_mul, ← map_mul, mul_comm]
    have hinv : (multiplier K c)⁻¹ = multiplier K c⁻¹ := by
      rw [← multiplierHom_apply, ← multiplierHom_apply, map_inv]
    have key : (g⁻¹ * n * g) * (g⁻¹ * w * g) * (g⁻¹ * n * g)⁻¹ = (g⁻¹ * w * g)⁻¹ := by
      rw [hμ, hc, show multiplier K μ * inversion K * multiplier K c *
          (multiplier K μ * inversion K)⁻¹ = multiplier K μ *
          (inversion K * multiplier K c * (inversion K)⁻¹) * (multiplier K μ)⁻¹ by group,
        inversion_conj_multiplier, hcomm, mul_inv_cancel_right, hinv]
    calc n * w * n⁻¹ = g * ((g⁻¹ * n * g) * (g⁻¹ * w * g) * (g⁻¹ * n * g)⁻¹) * g⁻¹ := by
          group
      _ = g * (g⁻¹ * w * g)⁻¹ * g⁻¹ := by rw [key]
      _ = w⁻¹ := by group

namespace EqualParameterData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

theorem exists_two_point_of_mod_four_eq_three
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 3) :
    ∃ x y : Omega F, x ≠ y ∧
      (∀ c : C t, (c : G) ∈ torusW G t s₀ → κ c x = x ∧ κ c y = y) ∧
      κ ⟨s₀, h.localData.s_mem_C⟩ x = x ∧ κ ⟨s₀, h.localData.s_mem_C⟩ y = y ∧
      ∃ c : C t, (c : G) ∈ torusW G t s₀ ∧ κ c ≠ 1 := by
  have hL := h.localData
  have hWC : torusW G t s₀ ≤ C t := hL.W_le_J.trans hL.J_le
  obtain ⟨hW2, -⟩ := (h.card_W_B).2.1 he
  have hW1 : Nat.card (torusW G t s₀) ≠ 1 := by
    have := h.q_gt
    omega
  obtain ⟨r, hr, hrW⟩ := Nat.exists_prime_and_dvd hW1
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := torusW G t s₀) r hrW
  set wC : C t := ⟨w, hWC w.2⟩ with hwC
  have hwCW : (wC : G) ∈ torusW G t s₀ := w.2
  have hwCord : orderOf wC = r := by
    rw [hwC, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hw]
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact absurd (h.odd_card_W.of_dvd_nat hrW) (by decide)
  have hrq : r ∣ p ^ f - 1 := by
    rw [← hW2]
    exact hrW.mul_left 2
  have hwC1 : wC ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hwCord
    exact hr.one_lt.ne hwCord
  have hκw1 := h.κ_ne_one_of_mem_W hwCW hwC1
  have hκw : orderOf (κ wC) = r := by
    rcases (Nat.dvd_prime hr).mp (hwCord ▸ orderOf_map_dvd κ wC) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hκw1
    · exact h1
  have hwD : κ wC ∈ coordinateD F := h.range_κ ▸ ⟨wC, rfl⟩
  obtain ⟨x, y, hxy, hx, hy⟩ := fixes_two_of_prime_dvd h.card_F hwD hr hr2 hκw hrq
  have hED : Subgroup.zpowers (κ wC) ≤ coordinateD F := Subgroup.zpowers_le.mpr hwD
  have hEx : ∀ e ∈ Subgroup.zpowers (κ wC), e x = x := by
    intro e he'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he'
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx k
  have hEy : ∀ e ∈ Subgroup.zpowers (κ wC), e y = y := by
    intro e he'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he'
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hy k
  have hE1 : Subgroup.zpowers (κ wC) ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hκw1
  have hpair : ∀ c : C t, c * wC = wC * c →
      (κ c x = x ∧ κ c y = y) ∨ (κ c x = y ∧ κ c y = x) := by
    intro c hc
    apply mem_pair_of_mem_normalizer hxy hED hEx hEy hE1
    apply mem_normalizer_of_conj_mem
    intro e he'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he'
    have hcomm : Commute (κ c) (κ wC) := by
      change κ c * κ wC = κ wC * κ c
      rw [← map_mul, ← map_mul, hc]
    rw [(hcomm.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  have hWfix : ∀ c : C t, (c : G) ∈ torusW G t s₀ → κ c x = x ∧ κ c y = y := by
    intro c hc
    have hcw : c * wC = wC * c := Subtype.ext (hL.W_comm _ hc _ hwCW)
    have hodd : Odd (orderOf (κ c)) := by
      refine Odd.of_dvd_nat ?_ (orderOf_map_dvd κ c)
      rw [← Subgroup.orderOf_coe]
      exact hL.W_odd _ hc
    exact fixes_of_odd_of_pair hxy hodd (hpair c hcw)
  have hsw : (⟨s₀, hL.s_mem_C⟩ : C t) * wC = wC * ⟨s₀, hL.s_mem_C⟩ :=
    Subtype.ext (hL.W_comm_s _ hwCW).symm
  have hsfix : κ ⟨s₀, hL.s_mem_C⟩ x = x ∧ κ ⟨s₀, hL.s_mem_C⟩ y = y := by
    rcases hpair _ hsw with h1 | ⟨h1, h2⟩
    · exact h1
    · exfalso
      have hinv := conj_eq_inv_of_swap hxy (h.range_κ ▸ ⟨_, rfl⟩) h1 h2 hwD hx hy
      have hcomm : κ ⟨s₀, hL.s_mem_C⟩ * κ wC = κ wC * κ ⟨s₀, hL.s_mem_C⟩ := by
        rw [← map_mul, ← map_mul, hsw]
      rw [hcomm, mul_inv_cancel_right] at hinv
      have h2' : κ wC ^ 2 = 1 := by
        rw [pow_two]
        exact (congrArg (· * κ wC) hinv).trans (inv_mul_cancel _)
      have h3 := orderOf_dvd_of_pow_eq_one h2'
      rw [hκw] at h3
      have := Nat.le_of_dvd (by norm_num) h3
      have := hr.two_le
      omega
  exact ⟨x, y, hxy, hWfix, hsfix.1, hsfix.2, wC, hwCW, hκw1⟩

theorem exists_invariant_sylow_C (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
    (he : p ^ f % 4 = 3) :
    (∃ Q₁ : Subgroup G, IsSylowOf p Q₁ (C t) ∧
      Subgroup.zpowers s₀ ⊔ torusW G t s₀ ≤ Subgroup.normalizer (Q₁ : Set G) ∧
      C t ⊓ Subgroup.normalizer (Q₁ : Set G) = Q₁ ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype ⊔
        (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀)) ∧
    ∀ X : Subgroup G, X ≤ C t → IsPGroup p X → X ≠ ⊥ →
      torusW G t s₀ ≤ Subgroup.normalizer (X : Set G) → Nat.card X = p ^ f := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hL := h.localData
  have hf := h.one_le
  have hWC : torusW G t s₀ ≤ C t := hL.W_le_J.trans hL.J_le
  obtain ⟨hW2, -⟩ := (h.card_W_B).2.1 he
  obtain ⟨x, y, hxy, hWfix, hsx, -, wC, hwCW, hκw1⟩ := h.exists_two_point_of_mod_four_eq_three he
  have hκW : Nat.card (((torusW G t s₀).subgroupOf (C t)).map κ) = Nat.card (torusW G t s₀) :=
    h.card_map_κ_of_coprime hWC h.coprime_card_W
  refine ⟨?_, ?_⟩
  · set St : Subgroup (Equiv.Perm (Omega F)) :=
      coordinateD F ⊓ MulAction.stabilizer (Equiv.Perm (Omega F)) x with hSt
    set MG : Subgroup G := (St.comap κ).map (C t).subtype with hMG
    have hMGC : MG ≤ C t := Subgroup.map_subtype_le _
    have hMGcard : Nat.card MG =
        p ^ f * ((p ^ f - 1) * (Nat.card ((N t).map (C t).subtype) * 2)) := by
      rw [hMG, Subgroup.card_map_of_injective (C t).subtype_injective,
        h.card_comap_κ St inf_le_left, hSt, card_coordinateD_inf_stabilizer, h.card_F]
      ring
    have hfac : (Nat.card MG).factorization p = f := by
      rw [hMGcard]
      apply UnitaryBranch.factorization_prime_pow_mul hp
      intro hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
      · have h3 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
        have h2 : p ∣ p ^ f := dvd_pow_self p (by omega)
        exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_sub_iff_right h3 h2).mp h1))
      · have := h.coprime_card_ker
        rw [h.card_B_sup_t] at this
        exact (Nat.Prime.coprime_iff_not_dvd hp).mp this h1
    obtain ⟨Q₁, hQ₁M⟩ := exists_isSylowOf p MG
    have hQ₁ : IsSylowOf p Q₁ (C t) :=
      isSylowOf_of_card (hQ₁M.le.trans hMGC) (by rw [hQ₁M.card_eq, hfac, h.factorization_card_C])
    have hQC : Q₁ ≤ C t := hQ₁.le
    have hmemMG : ∀ c : C t, (c : G) ∈ MG → κ c ∈ St := fun c hc =>
      (Subgroup.mem_map_iff_mem (C t).subtype_injective).mp hc
    have hx₀ : ∀ g ∈ (Q₁.subgroupOf (C t)).map κ, g x = x := by
      rintro _ ⟨u, hu, rfl⟩
      exact (hmemMG u (hQ₁M.le hu)).2
    have hnorm := h.mem_normalizer_sylow_iff hQ₁ hx₀
    obtain ⟨hQcard, hQJ, -, -, -⟩ := h.sylow_C_facts hQ₁
    have hsN : s₀ ∈ Subgroup.normalizer (Q₁ : Set G) := (hnorm ⟨s₀, hL.s_mem_C⟩).mpr hsx
    have hWN : torusW G t s₀ ≤ Subgroup.normalizer (Q₁ : Set G) := fun w hw =>
      (hnorm ⟨w, hWC hw⟩).mpr (hWfix ⟨w, hWC hw⟩ hw).1
    set R : Subgroup G := Q₁ ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype ⊔
      (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀) with hR
    have hQR : Q₁ ≤ R := le_sup_left.trans (le_sup_left.trans le_sup_left)
    have hWR : torusW G t s₀ ≤ R := le_sup_right.trans (le_sup_left.trans le_sup_left)
    have hBR : (N t).map (C t).subtype ≤ R := le_sup_right.trans le_sup_left
    have htR : t ∈ R := le_sup_right (b := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
    have hsR : s₀ ∈ R := le_sup_right (b := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀))
    have hRle : R ≤ C t ⊓ Subgroup.normalizer (Q₁ : Set G) := by
      have htC : t ∈ C t := Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have htN : t ∈ Subgroup.normalizer (Q₁ : Set G) := by
        refine mem_normalizer_of_conj_mem fun u hu => ?_
        rw [(Subgroup.mem_centralizer_singleton_iff.mp (hQC hu)).symm, mul_inv_cancel_right]
        exact hu
      have hBN : (N t).map (C t).subtype ≤ Subgroup.normalizer (Q₁ : Set G) := fun b hb =>
        mem_normalizer_of_conj_mem fun u hu => by
          rw [← hL.JB_comm u (hQJ hu) b hb, mul_inv_cancel_right]
          exact hu
      refine le_inf (sup_le (sup_le (sup_le hQC hWC) hL.B_le)
        (sup_le (Subgroup.zpowers_le.mpr htC) (Subgroup.zpowers_le.mpr hL.s_mem_C)))
        (sup_le (sup_le (sup_le Subgroup.le_normalizer hWN) hBN)
          (sup_le (Subgroup.zpowers_le.mpr htN) (Subgroup.zpowers_le.mpr hsN)))
    have hker : (N t).map (C t).subtype ⊔ Subgroup.zpowers t ≤ R :=
      sup_le hBR (Subgroup.zpowers_le.mpr htR)
    have hRimg : (R.subgroupOf (C t)).map κ = St := by
      have hle : (R.subgroupOf (C t)).map κ ≤ St := by
        rintro _ ⟨c, hc, rfl⟩
        exact ⟨h.range_κ ▸ ⟨c, rfl⟩, (hnorm c).mp (hRle hc).2⟩
      apply Subgroup.eq_of_le_of_card_ge hle
      have hdvdQ : p ^ f ∣ Nat.card ((R.subgroupOf (C t)).map κ) := by
        have h1 : (Q₁.subgroupOf (C t)).map κ ≤ (R.subgroupOf (C t)).map κ := by
          rintro _ ⟨c, hc, rfl⟩
          exact ⟨c, hQR hc, rfl⟩
        have h2 := Subgroup.card_dvd_of_le h1
        rwa [h.card_map_κ_of_coprime hQC (h.coprime_of_isPGroup hQ₁.isPGroup), hQcard] at h2
      have hdvdW : Nat.card (torusW G t s₀) ∣ Nat.card ((R.subgroupOf (C t)).map κ) := by
        have h1 : ((torusW G t s₀).subgroupOf (C t)).map κ ≤ (R.subgroupOf (C t)).map κ := by
          rintro _ ⟨c, hc, rfl⟩
          exact ⟨c, hWR hc, rfl⟩
        have h2 := Subgroup.card_dvd_of_le h1
        rwa [hκW] at h2
      have hdvd2 : 2 ∣ Nat.card ((R.subgroupOf (C t)).map κ) := by
        have hs : κ ⟨s₀, hL.s_mem_C⟩ ∈ (R.subgroupOf (C t)).map κ := ⟨_, hsR, rfl⟩
        have := Subgroup.orderOf_dvd_natCard _ hs
        rwa [h.κ_s₀.2] at this
      have hcop1 : Nat.Coprime (Nat.card (torusW G t s₀)) 2 :=
        Nat.coprime_two_right.mpr h.odd_card_W
      have hcop2 : Nat.Coprime (p ^ f) (Nat.card (torusW G t s₀) * 2) := by
        apply Nat.Coprime.pow_left
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hdvd
        rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
        · exact h.card_W_B_arith.1 h1
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1
          subst this
          exact absurd h.odd (by decide)
      have hdvd := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop2 hdvdQ
        (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop1 hdvdW hdvd2)
      rw [hSt, card_coordinateD_inf_stabilizer, h.card_F,
        show p ^ f - 1 = Nat.card (torusW G t s₀) * 2 by omega]
      exact Nat.le_of_dvd Nat.card_pos hdvd
    refine ⟨Q₁, hQ₁, sup_le (Subgroup.zpowers_le.mpr hsN) hWN, le_antisymm ?_ hRle⟩
    rintro c ⟨hcC, hcN⟩
    have hκc : κ ⟨c, hcC⟩ ∈ (R.subgroupOf (C t)).map κ := by
      rw [hRimg]
      exact ⟨h.range_κ ▸ ⟨_, rfl⟩, (hnorm ⟨c, hcC⟩).mp hcN⟩
    exact h.mem_of_κ_mem_map hker hκc
  · intro X hXC hXp hX1 hWX
    have hcop := h.coprime_of_isPGroup hXp
    set X₁ := (X.subgroupOf (C t)).map κ with hX₁
    have hX₁D : X₁ ≤ coordinateD F := h.range_κ ▸ Subgroup.map_le_range κ _
    have hX₁p : IsPGroup p X₁ := (hXp.comap_subtype (K := C t)).map κ
    have hX₁card : Nat.card X₁ = Nat.card X := h.card_map_κ_of_coprime hXC hcop
    have hX₁1 : X₁ ≠ ⊥ := by
      intro hb
      apply hX1
      rw [hb, Subgroup.card_bot] at hX₁card
      exact Subgroup.card_eq_one.mp hX₁card.symm
    obtain ⟨z, hz, -⟩ := existsUnique_fixed_of_isPGroup hp h.odd h.card_F hX₁D hX₁p hX₁1
    set W₁ := ((torusW G t s₀).subgroupOf (C t)).map κ with hW₁
    have hWX₁ : W₁ ≤ Subgroup.normalizer (X₁ : Set (Equiv.Perm (Omega F))) :=
      map_subgroupOf_le_normalizer κ hWX
    have hW₁z : ∀ a ∈ W₁, a z = z := fun a ha =>
      fixed_of_mem_normalizer_of_isPGroup hp h.odd h.card_F hX₁D hX₁p hX₁1 hz (hWX₁ ha)
    have hW₁D : W₁ ≤ coordinateD F := h.range_κ ▸ Subgroup.map_le_range κ _
    have hW₁x : ∀ a ∈ W₁, a x = x := by
      rintro _ ⟨c, hc, rfl⟩
      exact (hWfix c hc).1
    have hW₁y : ∀ a ∈ W₁, a y = y := by
      rintro _ ⟨c, hc, rfl⟩
      exact (hWfix c hc).2
    have hzxy : z = x ∨ z = y := by
      by_contra hc
      push Not at hc
      exact hκw1 (eq_one_of_three_fixed_points F (h.range_κ ▸ ⟨wC, rfl⟩) hxy (Ne.symm hc.1)
        (Ne.symm hc.2) (hWfix wC hwCW).1 (hWfix wC hwCW).2 (hW₁z _ ⟨wC, hwCW, rfl⟩))
    have hle : Nat.card (torusW G t s₀) + 1 ≤ Nat.card X := by
      rw [← hκW, ← hX₁card]
      rcases hzxy with rfl | rfl
      · exact card_add_one_le_of_two_point hp h.card_F hxy hW₁D hW₁x hW₁y hX₁D hX₁p hz hX₁1
          hWX₁
      · exact card_add_one_le_of_two_point hp h.card_F hxy.symm hW₁D hW₁y hW₁x hX₁D hX₁p hz
          hX₁1 hWX₁
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXp
    have hkf : k ≤ f := by
      have h1 : p ^ k ∣ Nat.card (C t) := by
        rw [← hk]
        exact Subgroup.card_dvd_of_le hXC
      have := (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp h1
      rwa [h.factorization_card_C] at this
    rw [hk]
    rcases Nat.lt_or_ge k f with hlt | hge
    · exfalso
      have h1 : p ^ k ≤ p ^ (f - 1) := Nat.pow_le_pow_right hp.pos (by omega)
      have h2 : p ^ f = p * p ^ (f - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have h3 : 3 ≤ p := by
        obtain ⟨j, hj⟩ := h.odd
        have := hp.two_le
        omega
      have h4 : 2 * Nat.card (torusW G t s₀) + 1 = p ^ f := by
        have : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
        omega
      rw [hk] at hle
      nlinarith [Nat.mul_le_mul_right (p ^ (f - 1)) h3]
    · rw [le_antisymm hkf hge]

end EqualParameterData

end CFSG.Semidihedral.FixedCoreNontrivial
