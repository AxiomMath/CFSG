module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32E

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped Pointwise

variable {X : Type} [Group X]

private theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {u v : X} (hu : u * u = 1)
    (hv : v ∈ zpowers u) : v = 1 ∨ v = u := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
  have h2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two, hu]
  have hk : u ^ k = u ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, zpow_zero]
  · right
    rw [hk, h, zpow_one]

theorem exists_sylow_two_normalized_of_mul_self [Finite X] {L : Subgroup X} {t : X}
    (ht2 : t * t = 1) (htN : t ∈ normalizer (L : Set X)) :
    ∃ P : Sylow 2 ↥L, ∀ y : ↥L, y ∈ (P : Subgroup ↥L) →
      t * (y : X) * t⁻¹ ∈ (P : Subgroup ↥L).map L.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥(zpowers t) →* MulAut ↥L :=
    L.normalizerMonoidHom.comp (Subgroup.inclusion (zpowers_le.mpr htN))
  let _ : MulDistribMulAction ↥(zpowers t) ↥L := MulDistribMulAction.compHom ↥L φ
  have h2 : IsPGroup 2 (zpowers t) := isPGroup_zpowers_of_mul_self ht2
  obtain ⟨P, hP⟩ := h2.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥L)
    (not_dvd_card_sylow (p := 2) (G := ↥L))
  refine ⟨P, fun y hy => ?_⟩
  have hfix : (⟨t, mem_zpowers t⟩ : ↥(zpowers t)) • P = P := MulAction.mem_fixedPoints.mp hP _
  have h1 : (⟨t, mem_zpowers t⟩ : ↥(zpowers t)) • y ∈ (P : Subgroup ↥L) := by
    have h3 := Subgroup.smul_mem_pointwise_smul y (⟨t, mem_zpowers t⟩ : ↥(zpowers t))
      (P : Subgroup ↥L) hy
    rw [← Sylow.pointwise_smul_def, hfix] at h3
    exact h3
  exact ⟨_, h1, rfl⟩

theorem false_of_isPComponent_of_uniqueInvolution [Finite X] {C L K : Subgroup X} {t : X}
    (hLC : L ≤ C) (hLpc : IsPComponent 2 (L.subgroupOf C)) (hLK : L ≤ K) (htK : t ∈ K)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htN : t ∈ normalizer (L : Set X))
    (huniq : ∀ P : Subgroup X, P ≤ K → IsPGroup 2 P → t ∈ P →
      ∀ y ∈ P, y ≠ 1 → y * y = 1 → y = t)
    (hcov : (pPrimeCore 2 ↥C).map C.subtype ⊔ L =
      (pPrimeCore 2 ↥C).map C.subtype ⊔ ⁅L, zpowers t⁆) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set OC := (pPrimeCore 2 ↥C).map C.subtype with hOCdef
  have hOL : (pPrimeCore 2 ↥L).map L.subtype ≤ OC := pPrimeCore_le_of_isPComponent hLC hLpc
  have hLO : ¬ L ≤ OC := by
    intro hle
    obtain ⟨K₀, hK₀, -, hLK₀, -⟩ := hLpc
    have hbot : (L.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C)) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨y, hy, hyx⟩ := hle (mem_subgroupOf.mp hx)
      have h1 : y = x := Subtype.ext hyx
      rw [← h1]
      exact hy
    rw [hbot] at hLK₀
    subst hLK₀
    obtain ⟨a, b, hab⟩ := hK₀.1.2.2
    apply hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have ha : a = 1 := Subtype.ext (mem_bot.mp a.2)
    have hb : b = 1 := Subtype.ext (mem_bot.mp b.2)
    rw [ha, hb]
  have hev : 2 ∣ Nat.card L := by
    by_contra hodd
    apply hLO
    have htop : pPrimeCore 2 ↥L = ⊤ := eq_top_iff.mpr (le_sSup ⟨inferInstance, by
      rw [Subgroup.card_top]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd⟩)
    intro x hx
    apply hOL
    rw [htop]
    exact ⟨⟨x, hx⟩, mem_top _, rfl⟩
  obtain ⟨P, hPt⟩ := exists_sylow_two_normalized_of_mul_self ht2 htN
  set PX := (P : Subgroup ↥L).map L.subtype with hPXdef
  have hPXL : PX ≤ L := map_subtype_le _
  have hPX2 : IsPGroup 2 PX := P.isPGroup'.map L.subtype
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htPX : zpowers t ≤ normalizer (PX : Set X) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hPt y hy
    · rintro ⟨y, hy, hyx⟩
      have hxe : x = t * (y : X) * t⁻¹ := by
        have h1 : (y : X) = t * x * t⁻¹ := hyx
        rw [h1, htinv]
        calc x = t * t * x * (t * t) := by rw [ht2, one_mul, mul_one]
          _ = t * (t * x * t) * t := by simp only [mul_assoc]
      rw [hxe]
      exact hPt y hy
  set T : Subgroup X := zpowers t ⊔ PX with hTdef
  have hT2 : IsPGroup 2 T :=
    (isPGroup_zpowers_of_mul_self ht2).to_sup_of_normal_right' hPX2 htPX
  have hTK : T ≤ K := sup_le (zpowers_le.mpr htK) (hPXL.trans hLK)
  have hunT := huniq T hTK hT2 (mem_sup_left (mem_zpowers t))
  have hPne : (P : Subgroup ↥L) ≠ ⊥ := P.ne_bot_of_dvd_card hev
  have h2P : 2 ∣ Nat.card (P : Subgroup ↥L) := by
    rcases P.isPGroup'.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hPne
    · exact h
  obtain ⟨u, hu2⟩ := exists_prime_orderOf_dvd_card' 2 h2P
  have huu : ((u : ↥L) : X) * ((u : ↥L) : X) = 1 := by
    have h1 : u * u = 1 := by
      have h3 := pow_orderOf_eq_one u
      rw [hu2, sq] at h3
      exact h3
    have h2 := congrArg (fun z : ↥(P : Subgroup ↥L) => ((z : ↥L) : X)) h1
    simpa using h2
  have hu1 : ((u : ↥L) : X) ≠ 1 := by
    intro h
    have h1 : u = 1 := Subtype.ext (Subtype.ext h)
    rw [h1, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hut : ((u : ↥L) : X) = t := hunT _ (mem_sup_right ⟨u, u.2, rfl⟩) hu1 huu
  have htL : t ∈ L := hut ▸ (u : ↥L).2
  set t' : ↥L := ⟨t, htL⟩ with ht'def
  have ht'P : t' ∈ (P : Subgroup ↥L) := by
    have h1 : (u : ↥L) = t' := Subtype.ext hut
    rw [← h1]
    exact u.2
  have hperf : commutator ↥L = ⊤ :=
    Group.isPerfect_def.mp (GSThmB.B5a.isPerfect_of_isPComponent_subgroupOf hLC hLpc)
  let _ : Fintype ↥L := Fintype.ofFinite _
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have ht'2 : t' * t' = 1 := Subtype.ext ht2
  obtain ⟨N, hNn, hNodd, hN⟩ :=
    ZStar.BrauerSuzukiShortcut.zStarConclusion_of_perfect_uniqueInvolution_brauerSuzuki ht'1
      ht'2 P ht'P (fun y hy hy1 hy2 => Subtype.ext (hunT (y : X) (mem_sup_right ⟨y, hy, rfl⟩)
        (fun h => hy1 (Subtype.ext h)) (by rw [← Subgroup.coe_mul, hy2]; rfl))) hperf
  have hNO : N ≤ pPrimeCore 2 ↥L := le_sSup ⟨hNn, Nat.coprime_two_left.mpr hNodd⟩
  have hcomm : ⁅L, zpowers t⁆ ≤ OC := by
    rw [commutator_le]
    intro l hl z hz
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self ht2 hz with rfl | rfl
    · rw [commutatorElement_one_right]
      exact one_mem _
    · apply hOL
      refine ⟨⟨l, hl⟩ * t' * ⟨l, hl⟩⁻¹ * t'⁻¹, hNO (hN ⟨l, hl⟩), ?_⟩
      simp [commutatorElement_def, ht'def]
  apply hLO
  calc L ≤ OC ⊔ L := le_sup_right
    _ = OC ⊔ ⁅L, zpowers t⁆ := hcov
    _ ≤ OC := sup_le le_rfl hcomm

end CFSG.ComponentClassification.SolMax
