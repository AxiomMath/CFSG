module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNTwo
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516Tools
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNResidue
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FWEq
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwFusIEnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwSwitch
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_conjugate_ne_bot {W K : Subgroup G} (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G)))) {T : Subgroup G}
    (hTsyl : IsSylowTwoIn T (normalizer (W : Set G))) {m : G}
    (hm : m ∈ normalizer (W : Set G)) : T ⊓ conjugate K m ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := normalizer (W : Set G) with hM
  set J : Subgroup G := ⨆ (g : G) (_ : g ∈ M), conjugate K g with hJ
  have hJM : J ≤ M := iSup₂_le fun g hg => conjugate_le_of_mem hKM hg
  have hMJ : M ≤ normalizer (J : Set G) := by
    intro g hg
    refine GrS4.mem_normalizer_of_map_le_self ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun g' hg' x hx => ?_
    have hmem : g * x * g⁻¹ ∈ conjugate K (g' * g⁻¹) := by
      rw [mem_conjugate_iff] at hx ⊢
      rwa [show g' * g⁻¹ * (g * x * g⁻¹) * (g' * g⁻¹)⁻¹ = g' * x * g'⁻¹ by group]
    simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (le_iSup₂_of_le (f := fun (g : G) (_ : g ∈ M) => conjugate K g) (g' * g⁻¹)
      (mul_mem hg' (inv_mem hg)) le_rfl) hmem
  have hK₃J : conjugate K m ≤ J := le_iSup₂_of_le m hm le_rfl
  have hJK₃ : J ≤ normalizer (conjugate K m : Set G) := by
    refine iSup₂_le fun g hg => ?_
    by_cases he : conjugate K g = conjugate K m
    · rw [he]
      exact le_normalizer
    · exact (GrS5.commutator_le_of_ne (conjugate_le_of_mem hKM hm) (conjugate_le_of_mem hKM hg)
        (isPComponent_conjugate_subgroupOf hm hKc) (isPComponent_conjugate_subgroupOf hg hKc)
        (Ne.symm he)).2
  obtain ⟨R, hR⟩ := RankProjectiveAction.exists_sylow_inf_of_le_normalizer hTsyl.1 hTsyl.2 hJM hMJ
  obtain ⟨R', hR'⟩ := RankProjectiveAction.exists_sylow_inf_of_le_normalizer
    (inf_le_right : T ⊓ J ≤ J) ⟨R, hR⟩ hK₃J hJK₃
  rw [inf_assoc, inf_of_le_right hK₃J] at hR'
  intro hbot
  have hev : 2 ∣ Nat.card ↥(conjugate K m) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp (GrS4.not_odd_card_of_isPComponent
      (conjugate_le_of_mem hKM hm) (isPComponent_conjugate_subgroupOf hm hKc)))
  apply R'.ne_bot_of_dvd_card hev
  rw [hR', hbot]
  exact (bot_subgroupOf _)

theorem inf_coreKernel_eq_bot (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog) (hbase : L34BaseSetting G) {a : G} {J W K : Subgroup G}
    (hs : SingleComponentSetting G a J W K) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hTM : T ≤ normalizer (W : Set G)) (haT : a ∈ T)
    (hTK : ¬ T ≤ normalizer (K : Set G)) :
    T ⊓ HeSN.coreKernel (normalizer (W : Set G)) K = ⊥ := by
  by_contra hne
  have hTn : T ≤ normalizer ((T ⊓ HeSN.coreKernel (normalizer (W : Set G)) K : Subgroup G) :
      Set G) := by
    intro t ht
    refine GrS4.mem_normalizer_of_map_le_self ?_
    rintro _ ⟨x, hx, rfl⟩
    exact mem_inf.mpr ⟨mul_mem (mul_mem ht (mem_inf.mp hx).1) (inv_mem ht),
      HeSN.conj_mem_coreKernel (hTM ht) (mem_inf.mp hx).2⟩
  obtain ⟨z, hzQ, hz2, hzc⟩ := GrS4.exists_center_involution_of_normal hT2 inf_le_left hTn hne
  have hzK := HeSN.mem_coreActionKernel_of_mem_coreKernel (mem_inf.mp hzQ).2
  exact hTK fun t ht =>
    mem_normalizer_of_commute hMax hS hbase hs hL34 hz2 (hzc a haT) hzK (hTM ht) (hzc t ht)

theorem commute_conj_one {W K : Subgroup G} (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G)))) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTM : T ≤ normalizer (W : Set G)) {x y k : G} (hx : x ∈ T ⊓ K)
    (hy : y ∈ T ⊓ K) (hk : k ∈ T) (hne : conjugate K k ≠ K) : Commute x (k⁻¹ * y * k) := by
  have hkK := conj_mem_conjugate (mem_inf.mp hy).2 k
  have hc := GrS5.commutator_le_inf_oddIn hKM (conjugate_le_of_mem hKM (hTM hk)) hKc
    (isPComponent_conjugate_subgroupOf (hTM hk) hKc) (Ne.symm hne)
  have h1 := (mem_inf.mp (hc (commutator_mem_commutator (mem_inf.mp hx).2 hkK))).1
  have hkT : k⁻¹ * y * k ∈ T := mul_mem (mul_mem (inv_mem hk) (mem_inf.mp hy).1) hk
  have h2 : ⁅x, k⁻¹ * y * k⁆ ∈ T := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (mem_inf.mp hx).1 hkT) (inv_mem (mem_inf.mp hx).1))
      (inv_mem hkT)
  exact commutatorElement_eq_one_iff_mul_comm.mp (HeDiag.eq_one_of_mem_oddIn hT2 h2 h1)

theorem conj_mem_coreActionKernel_of_ne {W K : Subgroup G} (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G)))) {x k : G} (hx : x ∈ K)
    (hk : k ∈ normalizer (W : Set G)) (hne : conjugate K k ≠ K) :
    k⁻¹ * x * k ∈ coreActionKernel K :=
  HeSN.le_coreActionKernel_of_ne hKM (conjugate_le_of_mem hKM hk) hKc
    (isPComponent_conjugate_subgroupOf hk hKc) (Ne.symm hne) (conj_mem_conjugate hx k)

theorem eq_or_eq_of_mem (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog) (hbase : L34BaseSetting G) {a : G} {J W K : Subgroup G}
    (hs : SingleComponentSetting G a J W K) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    {T : Subgroup G} (hTsyl : IsSylowTwoIn T (normalizer (W : Set G))) (haT : a ∈ T)
    (hTK : ¬ T ≤ normalizer (K : Set G)) :
    ∃ t ∈ T, t ∉ normalizer (K : Set G) ∧ t * t ∈ normalizer (K : Set G) ∧
      ∀ m ∈ normalizer (W : Set G), conjugate K m = K ∨ conjugate K m = conjugate K t := by
  have hT2 := GrS4.isPGroup_of_isSylowTwoIn hTsyl
  obtain ⟨t, htT, htT₁, htt, htN⟩ := HeSN.exists_mem_normalizer_sq hT2
    (inf_le_left : T ⊓ normalizer (K : Set G) ≤ T) fun hle => hTK (hle.trans inf_le_right)
  have htK : t ∉ normalizer (K : Set G) := fun ht => htT₁ (mem_inf.mpr ⟨htT, ht⟩)
  have httK : t * t ∈ normalizer (K : Set G) := (mem_inf.mp htt).2
  refine ⟨t, htT, htK, httK, fun m hm => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  have htM := hTsyl.1 htT
  set T₂ : Subgroup G := T ⊓ normalizer (K : Set G) ⊔ zpowers t with hT₂
  set R : Subgroup G := T₂ ⊓ coreActionKernel K ⊓ coreActionKernel (conjugate K t) with hR
  have hT₂T : T₂ ≤ T := sup_le inf_le_left (zpowers_le.mpr htT)
  have hT₂2 : IsPGroup 2 T₂ := hT2.to_le hT₂T
  have hRT₂ : R ≤ T₂ := inf_le_left.trans inf_le_left
  have hcK : ∀ {g x : G}, g ∈ normalizer (K : Set G) → x ∈ coreActionKernel K →
      g * x * g⁻¹ ∈ coreActionKernel K := fun hg hx =>
    UnbalancedLayer.conj_mem_coreActionKernel hg hx
  have hT₂n : T₂ ≤ normalizer (R : Set G) := by
    refine sup_le (fun g hg => ?_) (zpowers_le.mpr ?_)
    · refine GrS4.mem_normalizer_of_map_le_self ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨⟨hxT₂, hxK⟩, hxKt⟩ := And.intro (mem_inf.mp (mem_inf.mp hx).1) (mem_inf.mp hx).2
      have hgT₂ : g ∈ T₂ := mem_sup_left hg
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨mul_mem (mul_mem hgT₂ hxT₂) (inv_mem hgT₂),
        hcK (mem_inf.mp hg).2 hxK⟩, FooteLit.mem_coreActionKernel_conjugate_iff.mpr ?_⟩
      have h1 := FooteLit.mem_coreActionKernel_conjugate_iff.mp hxKt
      have h2 := hcK (htN g hg |> fun h' => (mem_inf.mp h').2) h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show t * g * t⁻¹ * (t * x * t⁻¹) * (t * g * t⁻¹)⁻¹ = t * (g * x * g⁻¹) * t⁻¹ by
        group] at h2
    · refine GrS4.mem_normalizer_of_map_le_self ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨⟨hxT₂, hxK⟩, hxKt⟩ := And.intro (mem_inf.mp (mem_inf.mp hx).1) (mem_inf.mp hx).2
      have htT₂ : t ∈ T₂ := mem_sup_right (mem_zpowers t)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨mul_mem (mul_mem htT₂ hxT₂) (inv_mem htT₂),
        FooteLit.mem_coreActionKernel_conjugate_iff.mp hxKt⟩,
        FooteLit.mem_coreActionKernel_conjugate_iff.mpr ?_⟩
      have h1 := hcK httK hxK
      rwa [show t * t * x * (t * t)⁻¹ = t * (t * x * t⁻¹) * t⁻¹ by group] at h1
  have hK₃M := conjugate_le_of_mem hs.le_normalizer hm
  have hK₃c := isPComponent_conjugate_subgroupOf hm hs.isPComponent_K
  have hKtc := isPComponent_conjugate_subgroupOf htM hs.isPComponent_K
  have hle : T ⊓ conjugate K m ≤ R := by
    intro x hx
    obtain ⟨hxT, hxK₃⟩ := mem_inf.mp hx
    have hxN : x ∈ normalizer (K : Set G) :=
      (GrS5.commutator_le_of_ne hs.le_normalizer hK₃M hs.isPComponent_K hK₃c
        (Ne.symm hne1)).2 hxK₃
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨mem_sup_left (mem_inf.mpr ⟨hxT, hxN⟩),
      HeSN.le_coreActionKernel_of_ne hs.le_normalizer hK₃M hs.isPComponent_K hK₃c (Ne.symm hne1)
        hxK₃⟩,
      HeSN.le_coreActionKernel_of_ne (conjugate_le_of_mem hs.le_normalizer htM) hK₃M hKtc hK₃c
        (Ne.symm hne2) hxK₃⟩
  have hRne : R ≠ ⊥ := fun hb => inf_conjugate_ne_bot hs.le_normalizer hs.isPComponent_K hTsyl
    hm (eq_bot_iff.mpr (hb ▸ hle))
  obtain ⟨s, hsR, hs2, hsc⟩ := GrS4.exists_center_involution_of_normal hT₂2 hRT₂ hT₂n hRne
  have haT₂ : a ∈ T₂ := mem_sup_left (mem_inf.mpr ⟨haT,
    (mem_coreActionKernel.mp (GrS4.mem_coreActionKernel_of_singleComponentSetting hMax hs)).1⟩)
  exact htK (mem_normalizer_of_commute hMax hS hbase hs hL34 hs2 (hsc a haT₂)
    (mem_inf.mp (mem_inf.mp hsR).1).2 htM (hsc t (mem_sup_right (mem_zpowers t))))

theorem inf_zStarIn_eq_bot_of_zOne {a : G} {J W K S : Subgroup G}
    (hs : SingleComponentSetting G a J W K) (hSsyl : IsSylowTwoIn S (normalizer (J : Set G)))
    (hZ1 : S ⊓ zStarIn J = ⊥) {T : Subgroup G} (hT2 : IsPGroup 2 T) : T ⊓ zStarIn K = ⊥ :=
  inf_zStarIn_eq_bot_of_sup hT2 (GrS4.le_of_singleComponentSetting hs)
    (GrS4.eq_sup_oddIn_of_singleComponentSetting hs).symm le_rfl
    (sup_eq_left.mpr (map_subtype_le _)) (odd_card_zStarIn_of_inf_eq_bot hSsyl hZ1)

theorem odd_card_inf_coreActionKernel {a : G} {J W K S : Subgroup G}
    (hs : SingleComponentSetting G a J W K) (hSsyl : IsSylowTwoIn S (normalizer (J : Set G)))
    (hZ1 : S ⊓ zStarIn J = ⊥) : Odd (Nat.card ↥(K ⊓ coreActionKernel K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(K ⊓ coreActionKernel K) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(K ⊓ coreActionKernel K)) 2 h2
  have hy2 : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hyZ : (y : G) ∈ zStarIn K := GrS5.inf_coreActionKernel_le_zStarIn K y.2
  have hP : IsPGroup 2 (zpowers (y : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
  have h1 := inf_zStarIn_eq_bot_of_zOne hs hSsyl hZ1 hP
  have h3 : (y : G) ∈ zpowers (y : G) ⊓ zStarIn K := mem_inf.mpr ⟨mem_zpowers _, hyZ⟩
  rw [h1, mem_bot] at h3
  rw [h3, orderOf_one] at hy2
  exact absurd hy2 (by norm_num)

theorem exists_mul_of_mem_sup_kernel {K D : Subgroup G} (hD2 : IsPGroup 2 D)
    (hDN : D ≤ normalizer (K : Set G)) (hDK : IsSylowTwoIn (D ⊓ K) K)
    (hKC : Odd (Nat.card ↥(K ⊓ coreActionKernel K))) {x : G} (hxD : x ∈ D)
    (hx : x ∈ K ⊔ coreActionKernel K) :
    ∃ k ∈ D ⊓ K, ∃ p ∈ D ⊓ coreActionKernel K, x = k * p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := normalizer (K : Set G) with hN
  set φ := GSThmB.oddBarConj K with hφ
  have hCN : coreActionKernel K ≤ N := fun c hc => (mem_coreActionKernel.mp hc).1
  have hKN : K ≤ N := le_normalizer
  have hx' : x ∈ (K : Set G) * (coreActionKernel K : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left K (coreActionKernel K) hCN]
    exact hx
  obtain ⟨k₀, hk₀, c₀, hc₀, hkc⟩ := hx'
  have hkc : k₀ * c₀ = x := hkc
  set P : Subgroup G := D ⊓ K with hP
  have hPN : P ≤ N := inf_le_left.trans hDN
  set ψ : ↥(P.subgroupOf N) →* MulAut (↥K ⧸ pPrimeCore 2 ↥K) := φ.comp (P.subgroupOf N).subtype
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyC : ((y : N) : G) ∈ coreActionKernel K :=
      GSThmB.mem_coreActionKernel_of_oddBarConj_eq_one hy
    have hyP : ((y : N) : G) ∈ P := mem_subgroupOf.mp y.2
    have hb := eq_bot_of_le_two_group_of_le_odd hD2 hKC
      (zpowers_le.mpr (mem_inf.mp hyP).1) (zpowers_le.mpr (mem_inf.mpr ⟨(mem_inf.mp hyP).2, hyC⟩))
    have h1 : ((y : N) : G) ∈ zpowers ((y : N) : G) := mem_zpowers _
    rw [hb, mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hrange : ψ.range = (P.subgroupOf N).map φ := by
    rw [MonoidHom.range_comp, range_subtype]
  have hcard₁ : Nat.card ↥((P.subgroupOf N).map φ) = Nat.card P := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
    exact Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv
  set Q₂ : Subgroup (MulAut (↥K ⧸ pPrimeCore 2 ↥K)) :=
    (D.subgroupOf N).map φ ⊓ (K.subgroupOf N).map φ with hQ₂
  have hD2' : IsPGroup 2 ↥(D.subgroupOf N) := hD2.of_equiv (subgroupOfEquivOfLe hDN).symm
  have hQ₂2 : IsPGroup 2 Q₂ := (hD2'.map φ).to_le inf_le_left
  obtain ⟨n, hn⟩ := hQ₂2.exists_card_eq
  have hdvdK : Nat.card Q₂ ∣ Nat.card K := by
    have h1 := card_dvd_of_le (inf_le_right : Q₂ ≤ (K.subgroupOf N).map φ)
    have h2 := card_map_dvd (K.subgroupOf N) φ
    rw [Nat.card_congr (subgroupOfEquivOfLe hKN).toEquiv] at h2
    exact h1.trans h2
  obtain ⟨hPK, Q, hQ⟩ := hDK
  have hidx : ¬ 2 ∣ (Q : Subgroup ↥K).index := Q.not_dvd_index
  have hKcard : Nat.card P * (Q : Subgroup ↥K).index = Nat.card K := by
    rw [← Subgroup.card_mul_index (Q : Subgroup ↥K), hQ,
      Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv]
  have hle : Nat.card Q₂ ≤ Nat.card P := by
    have hcop : Nat.Coprime (2 ^ n) (Q : Subgroup ↥K).index :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx)
    have h1 : 2 ^ n ∣ Nat.card P * (Q : Subgroup ↥K).index := by rw [hKcard, ← hn]; exact hdvdK
    rw [hn]
    exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right h1)
  have hQ₁₂ : (P.subgroupOf N).map φ ≤ Q₂ := by
    refine le_inf (map_mono fun y hy => ?_) (map_mono fun y hy => ?_)
    · exact mem_subgroupOf.mpr (mem_inf.mp (mem_subgroupOf.mp hy)).1
    · exact mem_subgroupOf.mpr (mem_inf.mp (mem_subgroupOf.mp hy)).2
  have heq : (P.subgroupOf N).map φ = Q₂ := eq_of_le_of_card_ge hQ₁₂ (by rw [hcard₁]; exact hle)
  set x' : ↥N := ⟨x, hDN hxD⟩
  set k₀' : ↥N := ⟨k₀, hKN hk₀⟩
  have hc₀' : φ ⟨c₀, hCN hc₀⟩ = 1 := GSThmB.oddBarConj_eq_one_of_mem_coreActionKernel hc₀
  have hxk : φ x' = φ k₀' := by
    have h1 : x' = k₀' * ⟨c₀, hCN hc₀⟩ := Subtype.ext hkc.symm
    rw [h1, map_mul, hc₀', mul_one]
  have hxQ : φ x' ∈ Q₂ :=
    mem_inf.mpr ⟨⟨x', mem_subgroupOf.mpr hxD, rfl⟩, ⟨k₀', mem_subgroupOf.mpr hk₀, hxk.symm⟩⟩
  rw [← heq] at hxQ
  obtain ⟨p', hp', hpx⟩ := hxQ
  have hpP : ((p' : N) : G) ∈ P := mem_subgroupOf.mp hp'
  have h1 : φ (p'⁻¹ * x') = 1 := by rw [map_mul, map_inv, hpx, inv_mul_cancel]
  have h2 := GSThmB.mem_coreActionKernel_of_oddBarConj_eq_one h1
  refine ⟨(p' : G), hpP, (p' : G)⁻¹ * x, mem_inf.mpr ⟨mul_mem (inv_mem (mem_inf.mp hpP).1) hxD,
    h2⟩, by group⟩

end CFSG.ComponentClassification.GrSLit.KSw
