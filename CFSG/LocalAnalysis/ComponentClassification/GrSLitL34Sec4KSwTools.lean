module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools59
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Cover59
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_subtype_subgroupOf_self {L : Subgroup G} (H : Subgroup L) :
    (H.map L.subtype).subgroupOf L = H := by
  rw [← comap_subtype, comap_map_eq_self_of_injective L.subtype_injective]

omit [Finite G] in
theorem mem_of_inv_mul_mem_of_odd {H : Type*} [Group H] {N : Subgroup H} [N.Normal] {y w : H}
    (hyw : y⁻¹ * w ∈ N) (hw : Odd (orderOf w)) {k : ℕ} (hy : orderOf y = 2 ^ k) : y ∈ N := by
  have hq : (y : H ⧸ N) = (w : H ⧸ N) := QuotientGroup.eq.mpr hyw
  have h1 : orderOf (y : H ⧸ N) ∣ 2 ^ k := hy ▸ orderOf_map_dvd (QuotientGroup.mk' N) y
  have h2 : orderOf (y : H ⧸ N) ∣ orderOf w := hq ▸ orderOf_map_dvd (QuotientGroup.mk' N) w
  have hcop : Nat.Coprime (2 ^ k) (orderOf w) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hw)
  have h3 : orderOf (y : H ⧸ N) = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2)
  rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3

theorem mem_coreActionKernel_of_mem_kernel {X : Type} [Group X] [Finite X] {a : X}
    {J W K : Subgroup X} (hs : SingleComponentSetting X a J W K) {c : X}
    (hcK : c ∈ coreActionKernel K) (hcN : c ∈ normalizer (J : Set X)) :
    c ∈ coreActionKernel J := by
  have hJK : J ≤ K := GrS4.le_of_singleComponentSetting hs
  have hOK : oddIn K ≤ oddIn (normalizer (W : Set X)) :=
    GSLit.map_pPrimeCore_le_of_isPComponent hs.le_normalizer hs.isPComponent_K
  refine mem_coreActionKernel.mpr ⟨hcN, fun j hj => ?_⟩
  have h1 : j⁻¹ * c⁻¹ * j * c ∈ oddIn K := (mem_coreActionKernel.mp hcK).2 j (hJK hj)
  have h3 : c⁻¹ * j * c ∈ J := by
    have := (mem_normalizer_iff.mp (inv_mem hcN) j).mp hj
    rwa [inv_inv] at this
  have h2 : j⁻¹ * c⁻¹ * j * c ∈ J := by
    have := mul_mem (inv_mem hj) h3
    rwa [← mul_assoc, ← mul_assoc] at this
  have h4 : j⁻¹ * c⁻¹ * j * c ∈ oddIn J := by
    rw [GrS4.oddIn_eq_inf_of_singleComponentSetting hs]
    exact mem_inf.mpr ⟨h2, hOK h1⟩
  exact h4

theorem le_gsFixedLayer_of_isPGroup {J P : Subgroup G} {z : G}
    (hTset : (gsFixedLayer J z : Set G) * (oddIn J : Set G) = J) (hP : IsPGroup 2 P)
    (hPJ : P ≤ J ⊓ centralizer ({z} : Set G)) : P ≤ gsFixedLayer J z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := J ⊓ centralizer ({z} : Set G) with hH
  have : (pLayer ↥H 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  intro p hp
  have hpH : p ∈ H := hPJ hp
  have hpJ : p ∈ ((gsFixedLayer J z : Set G) * (oddIn J : Set G)) := by
    rw [hTset]
    exact (mem_inf.mp hpH).1
  obtain ⟨t, ht, o, ho, hto⟩ := hpJ
  have hto : t * o = p := hto
  have htH : t ∈ H := gsFixedLayer_le_inf J z ht
  have hoH : o ∈ H := by
    have h1 := mul_mem (inv_mem htH) hpH
    rwa [← hto, inv_mul_cancel_left] at h1
  obtain ⟨t', ht', rfl⟩ := ht
  have hpe : (⟨p, hpH⟩ : H) = t' * ⟨o, hoH⟩ := Subtype.ext (by simp [← hto])
  have hmem : (⟨p, hpH⟩ : H)⁻¹ * ⟨o, hoH⟩ ∈ pLayer ↥H 2 := by
    rw [hpe, mul_inv_rev]
    have h1 := (inferInstance : (pLayer ↥H 2).Normal).conj_mem _ (inv_mem ht') (⟨o, hoH⟩ : H)⁻¹
    rwa [inv_inv] at h1
  have hoodd : Odd (orderOf (⟨o, hoH⟩ : H)) := by
    rw [Subgroup.orderOf_mk]
    have h1 : orderOf (⟨o, ho⟩ : ↥(oddIn J)) ∣ Nat.card ↥(oddIn J) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact (UnbalancedCorr.odd_card_map_pPrimeCore J).of_dvd_nat h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨p, hp⟩
  have hpk : orderOf (⟨p, hpH⟩ : H) = 2 ^ k := by
    rw [Subgroup.orderOf_mk, ← hk, Subgroup.orderOf_mk]
  exact ⟨⟨p, hpH⟩, mem_of_inv_mul_mem_of_odd hmem hoodd hpk, rfl⟩

theorem odd_card_zStarIn_of_inf_eq_bot {S J : Subgroup G}
    (hS : IsSylowTwoIn S (normalizer (J : Set G))) (hZ : S ⊓ zStarIn J = ⊥) :
    Odd (Nat.card ↥(zStarIn J)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(zStarIn J) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(zStarIn J)) 2 h2
  have hy2 : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hyJ : (y : G) ∈ J := (map_subtype_le _ : zStarIn J ≤ J) y.2
  have hyN : (y : G) ∈ normalizer (J : Set G) := le_normalizer hyJ
  obtain ⟨c, hcN, hcS⟩ := hS.exists_conj_le (zpowers_le.mpr hyN)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one]))
  have hcy : c * (y : G) * c⁻¹ ∈ zStarIn J := by
    have : (Open.fusionZStar ↥J).Characteristic := inferInstance
    exact (mem_normalizer_iff.mp
      (normalizer_le_normalizer_map_of_characteristic J (Open.fusionZStar ↥J) hcN) _).mp y.2
  have h1 : c * (y : G) * c⁻¹ ∈ S ⊓ zStarIn J := mem_inf.mpr ⟨hcS _ (mem_zpowers _), hcy⟩
  rw [hZ, mem_bot, mul_inv_eq_one, mul_eq_left] at h1
  rw [h1, orderOf_one] at hy2
  exact absurd hy2 (by norm_num)

theorem inf_zStarIn_eq_bot_of_sup {T J L P : Subgroup G} (hP : IsPGroup 2 P) (hTL : T ≤ L)
    (hTLs : T ⊔ oddIn L = L) (hTJ : T ≤ J) (hTJs : T ⊔ oddIn J = J)
    (hJ : Odd (Nat.card ↥(zStarIn J))) : P ⊓ zStarIn L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_bot_iff.mpr fun y hy => ?_
  obtain ⟨hyP, hyZ⟩ := mem_inf.mp hy
  have hyL : y ∈ L := (map_subtype_le _ : zStarIn L ≤ L) hyZ
  have hsub : T.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ := by
    have h1 : (T ⊔ oddIn L).subgroupOf L = ⊤ := by rw [hTLs, subgroupOf_self]
    unfold oddIn at h1
    rwa [subgroupOf_sup hTL (map_subtype_le _), map_subtype_subgroupOf_self] at h1
  have hyy : (⟨y, hyL⟩ : L) ∈ ((T.subgroupOf L ⊔ pPrimeCore 2 ↥L : Subgroup L) : Set L) := by
    rw [hsub]
    exact mem_top _
  rw [mul_normal] at hyy
  obtain ⟨t, ht, o, ho, hto⟩ := hyy
  have hto : t * o = ⟨y, hyL⟩ := hto
  have htT : (t : G) ∈ T := ht
  have hoL : (o : G) ∈ oddIn L := ⟨o, ho, rfl⟩
  have htZ : (t : G) ∈ zStarIn L := by
    have hto' : (t : G) * (o : G) = y := by
      have := congrArg Subtype.val hto
      simpa using this
    rw [eq_mul_inv_of_mul_eq hto']
    exact mul_mem hyZ (inv_mem (GrS4.oddIn_le_zStarIn L hoL))
  have htJ : (t : G) ∈ zStarIn J :=
    GrS5.mem_zStarIn_of_sup_oddIn hTJ hTJs
      (GrS5.inf_zStarIn_le_zStarIn_of_le hTL (mem_inf.mpr ⟨htT, htZ⟩))
  have htodd : Odd (orderOf t) := by
    rw [← Subgroup.orderOf_coe]
    have h1 : orderOf (⟨(t : G), htJ⟩ : ↥(zStarIn J)) ∣ Nat.card ↥(zStarIn J) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hJ.of_dvd_nat h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨y, hyP⟩
  have hyk : orderOf (⟨y, hyL⟩ : L) = 2 ^ k := by
    rw [Subgroup.orderOf_mk, ← hk, Subgroup.orderOf_mk]
  have hmem : (⟨y, hyL⟩ : L)⁻¹ * t ∈ pPrimeCore 2 ↥L := by
    rw [← hto, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact inv_mem ho
  have hyO := mem_of_inv_mul_mem_of_odd hmem htodd hyk
  have hyodd : Odd (2 ^ k) := by
    rw [← hyk]
    have h1 : orderOf (⟨⟨y, hyL⟩, hyO⟩ : ↥(pPrimeCore 2 ↥L)) ∣ Nat.card ↥(pPrimeCore 2 ↥L) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h1
  have hk0 : k = 0 := by
    by_contra hk0
    exact Nat.not_odd_iff_even.mpr even_two ((Nat.odd_pow_iff hk0).mp hyodd)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hyk
  have := congrArg Subtype.val hyk
  simpa using this

theorem le_of_sup_oddIn_eq_of_normalizer {L T K' : Subgroup G} (hLper : ⁅L, L⁆ = L)
    (hTL : T ≤ L) (hsupL : T ⊔ oddIn L = L) (hTK : T ≤ K')
    (hLN : L ≤ normalizer (K' : Set G)) : L ≤ K' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Odd (Nat.card (pPrimeCore 2 ↥L)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hRK : pPrimeCore 2 ↥L ≤ normalizer ((K'.subgroupOf L : Subgroup L) : Set L) := by
    intro r _
    refine mem_normalizer_iff.mpr fun y => ?_
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hLN r.2) y
  have hsub : L.subgroupOf L ≤ K'.subgroupOf L ⊔ pPrimeCore 2 ↥L := by
    intro y _
    have h1 : y ∈ (T ⊔ oddIn L).subgroupOf L := by
      rw [mem_subgroupOf, hsupL]
      exact y.2
    unfold oddIn at h1
    rw [subgroupOf_sup hTL (map_subtype_le _), map_subtype_subgroupOf_self] at h1
    have hTK' : T.subgroupOf L ≤ K'.subgroupOf L := fun t ht =>
      mem_subgroupOf.mpr (hTK (mem_subgroupOf.mp ht))
    exact sup_le_sup_right hTK' _ h1
  have hle := le_of_perfect_le_sup_of_odd hR hRK (GrS4.isPerfect_subgroupOf le_rfl hLper) hsub
  intro l hl
  exact mem_subgroupOf.mp (hle (show (⟨l, hl⟩ : L) ∈ L.subgroupOf L from hl))

theorem normalizer_le_of_wData (hPar : L34ParabolicGenerationFact) {J P S₁ D W E₁ : Subgroup G}
    (hJper : ⁅J, J⁆ = J) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (hP : IsSylowTwoIn P J)
    (hPS₁ : P ≤ S₁) (hS₁J : S₁ ≤ withKernel J)
    (hWB : ∀ B : Subgroup G, B ≤ S₁ → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hDS : D ≤ S₁) (hD : IsElemTwo D) (hD16 : 16 ≤ Nat.card D) (hE₁P : E₁ ≤ P)
    (hE₁ : IsEightGroup E₁) : normalizer (J : Set G) ≤ normalizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hOM : oddIn J ≤ M := by
    have hDN : D ≤ normalizer ((oddIn J : Subgroup G) : Set G) := fun d hd =>
      normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 J)
        (GrS4.withKernel_le_normalizer J (hS₁J (hDS hd)))
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 3
      Nat.prime_two D (oddIn J) hD.isElemAbelian (by norm_num; omega) hDN
      (by rw [oddIn, card_map_of_injective J.subtype_injective]; exact pPrimeCore_coprime_card)
    rw [← hgen]
    refine iSup₂_le fun F hF => ?_
    have hFD : F ≤ D := hF.1
    have hFc : Nat.card F = 8 := by rw [hF.2]; norm_num
    refine inf_le_right.trans fun y hy => ?_
    refine GrS4.mem_normalizer_wGroup_of_eight hWB (hFD.trans hDS) ⟨hD.mono hFD, hFc⟩ ?_
    rintro _ ⟨f, hf, rfl⟩
    have hfy := (mem_centralizer_iff.mp hy) f hf
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hfy, mul_inv_cancel_right]
    exact hDS (hFD hf)
  obtain ⟨T₁, T₂, hT₁P, hT₂P, ⟨F₁, hF₁T, hF₁⟩, ⟨F₂, hF₂T, hF₂⟩, hJgen⟩ :=
    hPar G J P hJper hL34 hP
  have hNT : ∀ T F : Subgroup G, T ≤ P → F ≤ T → IsEightGroup F →
      J ⊓ normalizer (T : Set G) ≤ M := by
    intro T F hTP hFT hF g hg
    refine GrS4.mem_normalizer_wGroup_of_eight hWB ((hFT.trans hTP).trans hPS₁) hF ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hPS₁ (hTP ((mem_normalizer_iff.mp (mem_inf.mp hg).2 f).mp (hFT hf)))
  have hJM : J ≤ M := hJgen.trans
    (sup_le (sup_le hOM (hNT T₁ F₁ hT₁P hF₁T hF₁)) (hNT T₂ F₂ hT₂P hF₂T hF₂))
  intro n hn
  obtain ⟨m, hmJ, k, hkN, rfl⟩ := GrS4.exists_mul_mem_normalizer_of_isSylowTwoIn hP hn
  refine mul_mem (hJM hmJ) (GrS4.mem_normalizer_wGroup_of_eight hWB (hE₁P.trans hPS₁) hE₁ ?_)
  rintro _ ⟨f, hf, rfl⟩
  exact hPS₁ ((mem_normalizer_iff.mp hkN f).mp (hE₁P hf))

end CFSG.ComponentClassification.GrSLit.KSw
