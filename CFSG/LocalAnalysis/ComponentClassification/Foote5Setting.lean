module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFooteF
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSec4

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

abbrev twoPart (X : Subgroup G) : ℕ := 2 ^ (Nat.card X).factorization 2

theorem card_le_twoPart {P X : Subgroup G} (hP : IsPGroup 2 P) (hPX : P ≤ X) :
    Nat.card P ≤ twoPart X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, hB, hPB⟩ := exists_isSylowOf_ge_of_le hPX hP
  rw [twoPart, ← hB.card_eq]
  exact card_le_of_le hPB

theorem twoPart_mono {K H : Subgroup G} (hKH : K ≤ H) : twoPart K ≤ twoPart H := by
  unfold twoPart
  refine Nat.pow_le_pow_right (by norm_num) ?_
  exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
    (Subgroup.card_dvd_of_le hKH) 2

theorem isSylowOf_of_twoPart_le {P X : Subgroup G} (hP : IsPGroup 2 P) (hPX : P ≤ X)
    (hcard : twoPart X ≤ Nat.card P) : IsSylowOf 2 P X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isSylowOf_of_card hPX (le_antisymm (card_le_twoPart hP hPX) hcard)

theorem pRank_le_of_isSylowOf {P K : Subgroup G} (hP : IsSylowOf 2 P K) :
    CFSG.pRank 2 ↥K ≤ CFSG.pRank 2 ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top,
    ← SectionRank.pRank_eq_pRank_top_subgroup, ← SectionRank.pRank_eq_pRank_top_subgroup]
  obtain ⟨E, hEK, hE, hcard⟩ := SectionRank.exists_pRank one_lt_two K
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hP hEK (IsPGroup.of_card hcard)
  have hEk : E.map (MulAut.conj k⁻¹).toMonoidHom ≤ P := by
    rintro _ ⟨e, he, rfl⟩
    have h := hk e he
    rwa [show (MulAut.conj k⁻¹).toMonoidHom e = k⁻¹ * e * k by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]]
  refine SectionRank.le_pRank one_lt_two hEk (SectionRank.isElemAbelian_map hE _) ?_
  rw [card_map_of_injective (MulAut.conj k⁻¹).injective, hcard]

structure Sec5 (G : Type) [Group G] [Finite G] (L₀ L Q S T : Subgroup G) (z t : G) : Prop where
  sec4 : FooteSec4 G L₀
  rankC : ∀ A ∈ footeFamilyOf L₀, CFSG.pRank 2 ↥(coreActionKernel A) ≤ 2
  memF : L ∈ footeFamilyOf L₀
  pmax : FootePointedMaximal z L
  rankCL : CFSG.pRank 2 ↥(coreActionKernel L) = 2
  sylQ : IsSylowOf 2 Q (coreActionKernel L)
  maxQ : ∀ A ∈ footeFamilyOf L₀, CFSG.pRank 2 ↥(coreActionKernel A) = 2 →
    twoPart (coreActionKernel A) ≤ Nat.card Q
  sylS : IsSylowOf 2 S (normalizer (L : Set G))
  QS : Q ≤ S
  maxS : ∀ A ∈ footeFamilyOf L₀, CFSG.pRank 2 ↥(coreActionKernel A) = 2 →
    twoPart (coreActionKernel A) = Nat.card Q → twoPart (normalizer (A : Set G)) ≤ Nat.card S
  sylT : IsSylowOf 2 T ⊤
  ST : S ≤ T
  zQ : z ∈ Q
  zS : ∀ s ∈ S, s * z = z * s
  tS : t ∈ S
  tL : t ∈ L
  tZ : ∀ s ∈ S, s * t = t * s
  t2 : orderOf t = 2

theorem exists_sec5
    {L₀ : Subgroup G}
    (h4 : FooteSec4 G L₀)
    (hrankC : ∀ A ∈ footeFamilyOf L₀, CFSG.pRank 2 ↥(coreActionKernel A) ≤ 2)
    (hex : ∃ A ∈ footeFamilyOf L₀, 2 ≤ CFSG.pRank 2 ↥(coreActionKernel A)) :
    ∃ (L Q S T : Subgroup G) (z t : G), Sec5 G L₀ L Q S T z t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLfam := h4.footeFamilyType
  set 𝒮 : Set (Subgroup G) :=
    {A | A ∈ footeFamilyOf L₀ ∧ CFSG.pRank 2 ↥(coreActionKernel A) = 2} with h𝒮
  have h𝒮ne : Nonempty 𝒮 := by
    obtain ⟨A, hAF, hA⟩ := hex
    exact ⟨⟨A, hAF, le_antisymm (hrankC A hAF) hA⟩⟩
  obtain ⟨⟨A₁, hA₁⟩, hA₁max⟩ :=
    Finite.exists_max (fun A : 𝒮 => twoPart (coreActionKernel (A : Subgroup G)))
  set 𝒮₀ : Set (Subgroup G) :=
    {A | A ∈ 𝒮 ∧ twoPart (coreActionKernel A) = twoPart (coreActionKernel A₁)} with h𝒮₀
  have h𝒮₀ne : Nonempty 𝒮₀ := ⟨⟨A₁, hA₁, rfl⟩⟩
  obtain ⟨⟨A, ⟨hAF, hArk⟩, hAd⟩, hAmax⟩ :=
    Finite.exists_max (fun A : 𝒮₀ => twoPart (normalizer ((A : Subgroup G) : Set G)))
  obtain ⟨z₀, hz₀⟩ := hAF.1
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 (coreActionKernel A)
  have hCN : coreActionKernel A ≤ normalizer (A : Set G) := fun x hx => hx.1
  obtain ⟨S, hS, hQS⟩ := exists_isSylowOf_ge_of_le (hQ.le.trans hCN) hQ.isPGroup
  obtain ⟨T, hT, hST⟩ := exists_isSylowOf_ge_of_le (le_top : S ≤ ⊤) hS.isPGroup
  have hSN : S ≤ normalizer (A : Set G) := hS.le
  have hQcard : Nat.card Q = twoPart (coreActionKernel A) := hQ.card_eq
  have hSC : S ⊓ coreActionKernel A = Q :=
    hQ.eq_of_le (le_inf hQS hQ.le) inf_le_right (hS.isPGroup.to_le inf_le_left)
  have hQnormS : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q := by
    intro s hs q hq
    rw [← hSC] at hq ⊢
    exact mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hq).1) (inv_mem hs),
      (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel A (hSN hs)) q).mp
        (mem_inf.mp hq).2⟩
  have hQne : Q ≠ ⊥ := by
    intro h
    have h1 := pRank_le_of_isSylowOf hQ
    rw [hArk, h] at h1
    have h2 : CFSG.pRank 2 ↥(⊥ : Subgroup G) ≤ 1 :=
      pRank_le_one_of_card_le_two (by rw [card_bot]; norm_num)
    omega
  obtain ⟨z, hzQ, hzo, hzS⟩ : ∃ z ∈ Q, orderOf z = 2 ∧ ∀ s ∈ S, s * z = z * s := by
    have hP := hS.isPGroup
    have : Group.IsNilpotent S := hP.isNilpotent
    have hM : Q.subgroupOf S ≠ ⊥ := by
      intro h
      apply hQne
      rw [eq_bot_iff]
      intro x hx
      have hmem : (⟨x, hQS hx⟩ : S) ∈ Q.subgroupOf S := mem_subgroupOf.mpr hx
      rw [h, mem_bot] at hmem
      rw [mem_bot]
      exact congrArg Subtype.val hmem
    have hMn : (Q.subgroupOf S).Normal := ⟨fun x hx g => by
      rw [mem_subgroupOf] at hx ⊢
      simpa using hQnormS g g.2 x hx⟩
    have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hM
    have hZp : IsPGroup 2 ↥(Q.subgroupOf S ⊓ center S) := hP.to_subgroup _
    rcases hZp.card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.card_eq_one.mp h1) h
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
    refine ⟨((y : S) : G), mem_subgroupOf.mp (mem_inf.mp y.2).1, ?_, fun s hs => ?_⟩
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
    · exact congrArg Subtype.val (mem_center_iff.mp (mem_inf.mp y.2).2 ⟨s, hs⟩)
  have hA2 : CFSG.pRank 2 ↥A = 2 := h4.hrank2 A hAF
  obtain ⟨t, htS, htA, hto, htZ⟩ : ∃ t ∈ S, t ∈ A ∧ orderOf t = 2 ∧ ∀ s ∈ S, s * t = t * s := by
    have hP := hS.isPGroup
    have : Group.IsNilpotent S := hP.isNilpotent
    have hRsyl : IsSylowOf 2 (S ⊓ A) A := hS.inf_of_le_normalizer le_normalizer le_rfl
    have hRne : S ⊓ A ≠ ⊥ := by
      intro h
      have h1 := pRank_le_of_isSylowOf hRsyl
      rw [hA2, h] at h1
      have h2 : CFSG.pRank 2 ↥(⊥ : Subgroup G) ≤ 1 :=
        pRank_le_one_of_card_le_two (by rw [card_bot]; norm_num)
      omega
    have hM : A.subgroupOf S ≠ ⊥ := by
      intro h
      apply hRne
      rw [eq_bot_iff]
      intro x hx
      have hmem : (⟨x, (mem_inf.mp hx).1⟩ : S) ∈ A.subgroupOf S :=
        mem_subgroupOf.mpr (mem_inf.mp hx).2
      rw [h, mem_bot] at hmem
      rw [mem_bot]
      exact congrArg Subtype.val hmem
    have hMn : (A.subgroupOf S).Normal := ⟨fun x hx g => by
      rw [mem_subgroupOf] at hx ⊢
      exact (mem_normalizer_iff.mp (hSN g.2) x).mp hx⟩
    have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hM
    have hZp : IsPGroup 2 ↥(A.subgroupOf S ⊓ center S) := hP.to_subgroup _
    rcases hZp.card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.card_eq_one.mp h1) h
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
    refine ⟨((y : S) : G), (y : S).2, mem_subgroupOf.mp (mem_inf.mp y.2).1, ?_, fun s hs => ?_⟩
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
    · exact congrArg Subtype.val (mem_center_iff.mp (mem_inf.mp y.2).2 ⟨s, hs⟩)
  have hzA : z ∈ coreActionKernel A := hQ.le hzQ
  obtain ⟨hfix, hLz, hLF⟩ := footeFixed_eq_footeF h4.hLB h4.hGA h4.hGC h4.hSA hLfam h4.huniq
    h4.hrank2 hz₀ hAF hzo hzA
  obtain ⟨B, hB, hBmax, hBF, -⟩ :=
    exists_mem_footeFamilyOf_of_mem_coreActionKernel h4.hLB h4.huniq hz₀ hAF hzo hzA
  have hBL : B = footeF L₀ z := (eq_footeF h4.huniq hB hBF).symm
  set L := footeF L₀ z with hLdef
  have hLmax : FootePointedMaximal z L := hBL ▸ hBmax
  have hLz' : IsTwoComponentAt z (footeFixed A z) := hfix ▸ hLz
  have hQL : Q ≤ coreActionKernel L := by
    intro q hq
    rw [← hfix]
    exact mem_coreActionKernel_footeFixed (hzS q (hQS hq)).symm (hQ.le hq) hLz'
  have hrkL : CFSG.pRank 2 ↥(coreActionKernel L) = 2 := by
    refine le_antisymm (hrankC L hLF) ?_
    have h1 := (pRank_le_of_isSylowOf hQ).trans (pRank_subgroup_mono hQL)
    rwa [hArk] at h1
  have hLin : L ∈ 𝒮 := ⟨hLF, hrkL⟩
  have hdL : twoPart (coreActionKernel L) ≤ Nat.card Q := by
    rw [hQcard, hAd]
    exact hA₁max ⟨L, hLin⟩
  have hQsyl : IsSylowOf 2 Q (coreActionKernel L) :=
    isSylowOf_of_twoPart_le hQ.isPGroup hQL hdL
  have hSL : S ≤ normalizer (L : Set G) :=
    fun s hs => le_normalizer_of_mem_footeFamilyOf h4.huniq hLz hLF
      (mem_centralizer_singleton_iff.mpr (hzS s hs))
  have hLdQ : twoPart (coreActionKernel L) = twoPart (coreActionKernel A₁) := by
    refine le_antisymm (hA₁max ⟨L, hLin⟩) ?_
    rw [← hAd, ← hQcard]
    exact card_le_twoPart hQ.isPGroup hQL
  have hSsyl : IsSylowOf 2 S (normalizer (L : Set G)) := by
    refine isSylowOf_of_twoPart_le hS.isPGroup hSL ?_
    rw [hS.card_eq]
    exact hAmax ⟨L, hLin, hLdQ⟩
  have htL : t ∈ L := by
    rw [← hfix, footeFixed]
    refine subset_closure ⟨mem_sup_left (mem_inf.mpr ⟨htA, ?_⟩), 1, ?_⟩
    · exact mem_centralizer_singleton_iff.mpr (htZ z (hQS hzQ)).symm
    · rw [pow_one, hto]
  have hmaxQ : ∀ A' ∈ footeFamilyOf L₀, CFSG.pRank 2 ↥(coreActionKernel A') = 2 →
      twoPart (coreActionKernel A') ≤ Nat.card Q := by
    intro A' hA'F hA'rk
    rw [hQcard, hAd]
    exact hA₁max ⟨A', hA'F, hA'rk⟩
  have hmaxS : ∀ A' ∈ footeFamilyOf L₀, CFSG.pRank 2 ↥(coreActionKernel A') = 2 →
      twoPart (coreActionKernel A') = Nat.card Q →
        twoPart (normalizer (A' : Set G)) ≤ Nat.card S := by
    intro A' hA'F hA'rk hA'd
    rw [hS.card_eq]
    exact hAmax ⟨A', ⟨hA'F, hA'rk⟩, by rw [hA'd, hQcard, hAd]⟩
  exact ⟨L, Q, S, T, z, t, h4, hrankC, hLF, hLmax, hrkL, hQsyl, hmaxQ, hSsyl, hQS, hmaxS,
    hT, hST, hzQ, hzS, htS, htL, htZ, hto⟩

@[expose] def eligibleSolomonClass (X : Subgroup G) : Set (Subgroup G) :=
  {K | K ∈ solomonKStar G ∧ SolomonEquiv X K ∧ ∃ v : G, IsTwoComponentAt v K}

theorem eligible_kernel_sylow_isElemAbelian_card_four_l216
    {X : Subgroup G}
    (hU2 : ∀ K ∈ eligibleSolomonClass X,
      CFSG.pRank 2 (coreActionKernel K) = 2)
    (hD : ∀ K ∈ eligibleSolomonClass X,
      twoPart (coreActionKernel K) ≤ 4) :
    ∀ K ∈ eligibleSolomonClass X, ∀ Q : Subgroup G,
      IsSylowOf 2 Q (coreActionKernel K) →
      CFSG.Open.IsElemAbelian 2 Q ∧ Nat.card Q = 4 := by
  intro K hK Q hQ
  have hQcard : Nat.card Q ≤ 4 := by
    rw [hQ.card_eq]
    exact hD K hK
  have hQrank : 2 ≤ CFSG.pRank 2 Q := by
    calc
      2 = CFSG.pRank 2 (coreActionKernel K) := (hU2 K hK).symm
      _ ≤ CFSG.pRank 2 Q := pRank_le_of_isSylowOf hQ
  have hrankO : 2 ≤ CFSG.Open.pRank 2 Q := by
    rw [SectionRank.pRank_eq_pRank_top_subgroup,
      ← SectionRank.pRank_eq_open_pRank_top]
    exact hQrank
  obtain ⟨E, hEQ, hE, hEc⟩ := SectionRank.exists_pRank one_lt_two Q
  have hEge : 4 ≤ Nat.card E := by
    rw [hEc]
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hrankO
  have hcard : Nat.card Q = 4 :=
    le_antisymm hQcard (hEge.trans (Subgroup.card_le_of_le hEQ))
  have hEq : E = Q :=
    Subgroup.eq_of_le_of_card_ge hEQ (by rw [hcard]; exact hEge)
  exact ⟨hEq ▸ hE, hcard⟩

theorem exists_eligibleSolomonClass_optimizer {X : Subgroup G} {v : G}
    (hX : X ∈ solomonKStar G) (hXv : IsTwoComponentAt v X) :
    ∃ L P S T : Subgroup G,
      L ∈ eligibleSolomonClass X ∧
      IsSylowOf 2 P (coreActionKernel L) ∧ P ≤ S ∧
      IsSylowOf 2 S (normalizer (L : Set G)) ∧ S ≤ T ∧ IsSylowOf 2 T ⊤ ∧
      (∀ K ∈ eligibleSolomonClass X, twoPart (coreActionKernel K) ≤ Nat.card P) ∧
      (∀ K ∈ eligibleSolomonClass X,
        twoPart (coreActionKernel K) = Nat.card P →
          twoPart (normalizer (K : Set G)) ≤ Nat.card S) := by
  classical
  have hXelig : X ∈ eligibleSolomonClass X :=
    ⟨hX, ⟨hX.1.1, Relation.ReflTransGen.refl⟩, ⟨v, hXv⟩⟩
  set 𝒮 : Set (Subgroup G) := eligibleSolomonClass X with h𝒮
  have h𝒮ne : Nonempty 𝒮 := ⟨⟨X, hXelig⟩⟩
  have := h𝒮ne
  obtain ⟨⟨L₁, hL₁⟩, hL₁max⟩ :=
    Finite.exists_max (fun K : 𝒮 => twoPart (coreActionKernel (K : Subgroup G)))
  set 𝒮₀ : Set (Subgroup G) :=
    {K | K ∈ 𝒮 ∧ twoPart (coreActionKernel K) = twoPart (coreActionKernel L₁)} with h𝒮₀
  have h𝒮₀ne : Nonempty 𝒮₀ := ⟨⟨L₁, hL₁, rfl⟩⟩
  have := h𝒮₀ne
  obtain ⟨⟨L, ⟨hL𝒮, hLd⟩⟩, hLmax⟩ :=
    Finite.exists_max (fun K : 𝒮₀ => twoPart (normalizer ((K : Subgroup G) : Set G)))
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (coreActionKernel L)
  have hCN : coreActionKernel L ≤ normalizer (L : Set G) := fun x hx => hx.1
  obtain ⟨S, hS, hPS⟩ := exists_isSylowOf_ge_of_le (hP.le.trans hCN) hP.isPGroup
  obtain ⟨T, hT, hST⟩ := exists_isSylowOf_ge_of_le (le_top : S ≤ ⊤) hS.isPGroup
  have hmaxP : ∀ K ∈ eligibleSolomonClass X, twoPart (coreActionKernel K) ≤ Nat.card P := by
    intro K hK
    have h1 : twoPart (coreActionKernel K) ≤ twoPart (coreActionKernel L₁) :=
      hL₁max ⟨K, hK⟩
    calc
      twoPart (coreActionKernel K) ≤ twoPart (coreActionKernel L₁) := h1
      _ = twoPart (coreActionKernel L) := hLd.symm
      _ = Nat.card P := hP.card_eq.symm
  have hmaxS : ∀ K ∈ eligibleSolomonClass X,
      twoPart (coreActionKernel K) = Nat.card P →
        twoPart (normalizer (K : Set G)) ≤ Nat.card S := by
    intro K hK hKcard
    have hK₀ : K ∈ 𝒮₀ := ⟨hK, by
      calc
        twoPart (coreActionKernel K) = Nat.card P := hKcard
        _ = twoPart (coreActionKernel L) := hP.card_eq
        _ = twoPart (coreActionKernel L₁) := hLd⟩
    have h1 : twoPart (normalizer (K : Set G)) ≤ twoPart (normalizer (L : Set G)) :=
      hLmax ⟨K, hK₀⟩
    calc
      twoPart (normalizer (K : Set G)) ≤ twoPart (normalizer (L : Set G)) := h1
      _ = Nat.card S := hS.card_eq.symm
  exact ⟨L, P, S, T, hL𝒮, hP, hPS, hS, hST, hT, hmaxP, hmaxS⟩

end CFSG.ComponentClassification.Foote5
