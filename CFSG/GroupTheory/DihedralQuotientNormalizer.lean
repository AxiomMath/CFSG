module

public import CFSG.GroupTheory.SylowNormalizerRelIndex
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGroup
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentPQ
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Cyclic
public import CFSG.GroupTheory.SteinbergCBFTSCN
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import TauCeti.GroupTheory.ExponentPrime
import CFSG.Timmesfeld.Bridge.Asc72WreathStruct
import CFSG.GroupTheory.TwoReflections

public section

namespace CFSG.GroupTheory

open scoped Pointwise commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ}

theorem le_relPPrimeCore_of_normal_coprime (hp : p.Prime) {N H : Subgroup Γ}
    (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hcop : Nat.Coprime p (Nat.card N)) : N ≤ CFSG.Open.relPPrimeCore p H := by
  have hcop' : Nat.Coprime p (Nat.card (N.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
  have h := CFSG.le_pPrimeCore_of_normal_coprime (p := p) hN hcop'
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
    hp H, ← Subgroup.map_subgroupOf_eq_of_le hNH]
  exact Subgroup.map_mono h

theorem pPrimeCore_quotient_image_eq_bot (hp : p.Prime) {U H : Subgroup Γ} [hU : U.Normal]
    (hUH : U ≤ H) (hUeq : U = CFSG.Open.relPPrimeCore p H) :
    CFSG.pPrimeCore p (H.map (QuotientGroup.mk' U)) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let q : Γ →* Γ ⧸ U := QuotientGroup.mk' U
  let Hbar : Subgroup (Γ ⧸ U) := H.map q
  let f : H →* Hbar := (q.comp H.subtype).codRestrict Hbar fun x =>
    Subgroup.mem_map_of_mem q x.2
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨h, hh, hhy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨h, hh⟩, Subtype.ext hhy⟩
  have hker : f.ker = CFSG.pPrimeCore p ↥H := by
    have hker' : f.ker = U.subgroupOf H := by
      ext x
      constructor
      · intro hx
        have h1 : f x = 1 := hx
        have h2 : q (x : Γ) = 1 := congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff (N := U) (x : Γ)).mp h2
      · intro hx
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff (N := U) (x : Γ)).mpr hx
    rw [hker', hUeq,
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
        hp H]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  let eHom : (↥H ⧸ CFSG.pPrimeCore p ↥H) →* Hbar :=
    QuotientGroup.lift (CFSG.pPrimeCore p ↥H) f (by rw [← hker])
  have hsurj : Function.Surjective eHom :=
    QuotientGroup.lift_surjective_of_surjective (CFSG.pPrimeCore p ↥H) f hf (by rw [← hker])
  have hinj : Function.Injective eHom := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift]
    rw [hker, QuotientGroup.map_mk'_self]
  let e : (↥H ⧸ CFSG.pPrimeCore p ↥H) ≃* Hbar :=
    MulEquiv.ofBijective eHom ⟨hinj, hsurj⟩
  have hsource : CFSG.pPrimeCore p (↥H ⧸ CFSG.pPrimeCore p ↥H) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  have hmap := CFSG.pPrimeCore_map_iso
    (G := ↥H ⧸ CFSG.pPrimeCore p ↥H) (G' := Hbar) p e
  rw [hsource, Subgroup.map_bot] at hmap
  exact hmap.symm

theorem exists_orderOf_eq_prime_mem_normalizer_of_pPrimeCore_quotient
    (hp : p.Prime) (hp2 : p ≠ 2) {U H : Subgroup Γ} [hU : U.Normal] (hUH : U ≤ H)
    (hpU : Nat.Coprime p (Nat.card U))
    {Q : Subgroup Γ} (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q H)
    {gbar : Γ ⧸ U} (hgbar : orderOf gbar = p)
    (hgbarH : gbar ∉ H.map (QuotientGroup.mk' U))
    (hgbarN : gbar ∈ Subgroup.normalizer
      ((Q.map (QuotientGroup.mk' U) : Subgroup (Γ ⧸ U)) : Set (Γ ⧸ U))) :
    ∃ b : Γ, b ∉ H ∧ orderOf b = p ∧
      ∃ R : Subgroup Γ, CFSG.ABGLocalTools.IsSylowOf 2 R H ∧
        b ∈ Subgroup.normalizer (R : Set Γ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Γ ⧸ U) :=
    Finite.of_surjective (QuotientGroup.mk' U) (QuotientGroup.mk'_surjective U)
  let q : Γ →* Γ ⧸ U := QuotientGroup.mk' U
  let Hbar : Subgroup (Γ ⧸ U) := H.map q
  let Qbar : Subgroup (Γ ⧸ U) := Q.map q
  have hQbar : CFSG.ABGLocalTools.IsSylowOf 2 Qbar Hbar := by
    obtain ⟨QH, hQH⟩ := hQ
    have hQleH : Q ≤ H := by
      rw [← hQH]
      exact Subgroup.map_subtype_le (QH : Subgroup H)
    let qH : H →* Hbar :=
      (q.comp H.subtype).codRestrict Hbar fun x => Subgroup.mem_map_of_mem q x.2
    have hqH : Function.Surjective qH := by
      intro z
      obtain ⟨h, hh, hhz⟩ := Subgroup.mem_map.mp z.2
      exact ⟨⟨h, hh⟩, Subtype.ext hhz⟩
    let QbarH : Sylow 2 Hbar := QH.mapSurjective hqH
    have hmap_cod : (QH : Subgroup H).map qH =
        ((QH : Subgroup H).map (q.comp H.subtype)).subgroupOf Hbar := by
      ext x
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨h, hh, rfl⟩
      · rintro ⟨h, hh, hx⟩
        exact ⟨h, hh, Subtype.ext hx⟩
    have hQbarH : (QbarH : Subgroup Hbar) = (Q.map q).subgroupOf Hbar := by
      rw [Sylow.coe_mapSurjective hqH QH, hmap_cod]
      rw [← Subgroup.map_map (K := (QH : Subgroup H)) q H.subtype, hQH]
    refine ⟨QbarH, ?_⟩
    rw [hQbarH]
    exact Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_mono hQleH)
  let W : Subgroup Γ := Qbar.comap q
  let Zbar : Subgroup (Γ ⧸ U) := Subgroup.zpowers gbar ⊔ Qbar
  let Z : Subgroup Γ := Zbar.comap q
  have hUW : U ≤ W := by
    intro u hu
    have hqu : q u = 1 := (QuotientGroup.eq_one_iff (N := U) u).mpr hu
    show q u ∈ Qbar
    rw [hqu]
    exact Qbar.one_mem
  have hWH : W ≤ H := by
    intro x hx
    obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp hx
    have hxU : x * h⁻¹ ∈ U := by
      refine (QuotientGroup.eq_one_iff (N := U) (x * h⁻¹)).mp ?_
      show q (x * h⁻¹) = 1
      rw [map_mul, map_inv, hhx, mul_inv_cancel]
    rw [show x = (x * h⁻¹) * h by group]
    exact H.mul_mem (hUH hxU) (hQ.le hh)
  have hWZ : W ≤ Z := Subgroup.comap_mono le_sup_right
  have hWbar_normal : Zbar ≤ Subgroup.normalizer (Qbar : Set (Γ ⧸ U)) := by
    change Subgroup.zpowers gbar ⊔ Qbar ≤ _
    exact sup_le (Subgroup.zpowers_le.mpr hgbarN) Subgroup.le_normalizer
  have hWnorm : (W.subgroupOf Z).Normal := by
    have : (Qbar.subgroupOf Zbar).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right : Qbar ≤ Zbar)).mpr
        hWbar_normal
    let ψ : Z →* Zbar := (q.comp Z.subtype).codRestrict Zbar fun z => z.2
    have hEq : (Qbar.subgroupOf Zbar).comap ψ = W.subgroupOf Z := by
      ext x
      change q (x : Γ) ∈ Qbar ↔ q (x : Γ) ∈ Qbar
      exact Iff.rfl
    rw [← hEq]
    exact Subgroup.Normal.comap inferInstance ψ
  have hUnorm : (U.subgroupOf Z).Normal := Subgroup.normal_subgroupOf
  have hZbar_card : Nat.card Zbar = p * Nat.card Qbar := by
    have hHnorm : Subgroup.zpowers gbar ≤
        Subgroup.normalizer (Qbar : Set (Γ ⧸ U)) := Subgroup.zpowers_le.mpr hgbarN
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := Subgroup.zpowers gbar) (K := Qbar) hHnorm
    have hinf : Subgroup.zpowers gbar ⊓ Qbar = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      by_contra hx1
      have hxbar : gbar ∈ Qbar := by
        have hcyc : Subgroup.zpowers x = Subgroup.zpowers gbar :=
          TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp
            (by simpa [hgbar] using pow_orderOf_eq_one gbar) hx1 hx.1
        exact (Subgroup.zpowers_le.mpr hx.2) (by rw [hcyc]; exact Subgroup.mem_zpowers gbar)
      exact hgbarH (hQbar.le hxbar)
    rw [show Subgroup.zpowers gbar ⊔ Qbar = Zbar from rfl, hinf, Subgroup.card_bot, mul_one,
      Nat.card_zpowers, hgbar] at h
    exact h
  have hZ_card : Nat.card Z = Nat.card U * Nat.card Zbar :=
    QuotientGroup.card_preimage_mk U (Zbar : Set (Γ ⧸ U))
  have hW_card : Nat.card W = Nat.card U * Nat.card Qbar :=
    QuotientGroup.card_preimage_mk U (Qbar : Set (Γ ⧸ U))
  have hidx : W.relIndex Z = p := by
    have h := Subgroup.relIndex_mul_card (G := Γ) W Z
    rw [inf_eq_left.mpr hWZ] at h
    rw [hZ_card, hW_card, hZbar_card] at h
    have hpos : 0 < Nat.card U * Nat.card Qbar := Nat.mul_pos Nat.card_pos Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h]
    ring
  have h2 : ∀ w ∈ W, ∃ k : ℕ, w ^ (2 ^ k) ∈ U := by
    intro w hw
    obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp hQbar.isPGroup ⟨q w, hw⟩
    refine ⟨k, ?_⟩
    have hq1 : q (w ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    exact (QuotientGroup.eq_one_iff (N := U) _).mp hq1
  obtain ⟨R₀, hR₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 U
  have hNU : ¬ p ∣ Nat.card ↥(U ⊓ Subgroup.normalizer (R₀ : Set Γ)) := by
    have hdvd : Nat.card ↥(U ⊓ Subgroup.normalizer (R₀ : Set Γ)) ∣ Nat.card U :=
      Subgroup.card_dvd_of_le inf_le_left
    exact fun h => (Nat.Prime.coprime_iff_not_dvd hp).mp (hpU.coprime_dvd_right hdvd) h
  obtain ⟨R, hR, b, hbZ, hbW, hbord, hbR⟩ :=
    CFSG.GroupTheory.exists_orderOf_eq_prime_mem_normalizer_sylow_of_relIndex
      (G := Γ) hp hp2 hUW hWZ hWnorm hUnorm hidx h2 hR₀ hNU
  have hH_card : Nat.card H = Nat.card U * Nat.card Hbar := by
    have h1 : Nat.card ↥(Hbar.comap q) = Nat.card U * Nat.card Hbar :=
      QuotientGroup.card_preimage_mk U (Hbar : Set (Γ ⧸ U))
    have h2 : Hbar.comap q = H := by
      rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hUH]
    rwa [h2] at h1
  have hWeq : W.relIndex H = Qbar.relIndex Hbar := by
    have hrelW : W.relIndex H * Nat.card W = Nat.card H := by
      have h := Subgroup.relIndex_mul_card (G := Γ) W H
      rwa [inf_eq_left.mpr hWH] at h
    have hrelQ : Qbar.relIndex Hbar * Nat.card Qbar = Nat.card Hbar := by
      have h := Subgroup.relIndex_mul_card (G := Γ ⧸ U) Qbar Hbar
      rwa [inf_eq_left.mpr hQbar.le] at h
    have h1 : W.relIndex H * (Nat.card U * Nat.card Qbar) = Nat.card U * Nat.card Hbar := by
      rw [← hW_card, ← hH_card]
      exact hrelW
    have h2 : Qbar.relIndex Hbar * (Nat.card U * Nat.card Qbar) = Nat.card U * Nat.card Hbar := by
      calc Qbar.relIndex Hbar * (Nat.card U * Nat.card Qbar)
          = Nat.card U * (Qbar.relIndex Hbar * Nat.card Qbar) := by ring
        _ = Nat.card U * Nat.card Hbar := by rw [hrelQ]
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos Nat.card_pos Nat.card_pos) (h1.trans h2.symm)
  have hWodd : ¬ 2 ∣ W.relIndex H := by
    rw [hWeq]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hQbar).2.2
  have hRH : CFSG.ABGLocalTools.IsSylowOf 2 R H := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hR.le.trans hWH, hR.isPGroup, ?_⟩
    have hprod : R.relIndex W * W.relIndex H = R.relIndex H :=
      Subgroup.relIndex_mul_relIndex (G := Γ) R W H hR.le hWH
    rw [← hprod]
    exact fun h => (Nat.prime_two.dvd_mul.mp h).elim
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hR).2.2 hWodd
  have hZbar_inf : Zbar ⊓ Hbar = Qbar := by
    have hQle : Qbar ≤ Zbar ⊓ Hbar := le_inf le_sup_right hQbar.le
    have hle : Zbar ⊓ Hbar ≤ Zbar := inf_le_left
    have hrel := Subgroup.relIndex_mul_relIndex (G := Γ ⧸ U) Qbar (Zbar ⊓ Hbar) Zbar hQle hle
    have hrelp : Qbar.relIndex Zbar = p := by
      have h := Subgroup.relIndex_mul_card (G := Γ ⧸ U) Qbar Zbar
      rw [inf_eq_left.mpr (le_sup_right : Qbar ≤ Zbar)] at h
      have hpos : 0 < Nat.card ↥Qbar := Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      rw [← hZbar_card]
      exact h
    have hne1 : (Zbar ⊓ Hbar).relIndex Zbar ≠ 1 := by
      intro h1
      have htop : Zbar ≤ Zbar ⊓ Hbar := Subgroup.relIndex_eq_one.mp h1
      have hgZ : gbar ∈ Zbar := Subgroup.mem_sup_left (Subgroup.mem_zpowers gbar)
      exact hgbarH (htop hgZ).2
    have hdvd : (Zbar ⊓ Hbar).relIndex Zbar ∣ Qbar.relIndex Zbar := by
      rw [← hrel]
      exact dvd_mul_left _ _
    have hval : (Zbar ⊓ Hbar).relIndex Zbar = p := by
      rw [hrelp] at hdvd
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hone : Qbar.relIndex (Zbar ⊓ Hbar) = 1 := by
      have h2 : Qbar.relIndex (Zbar ⊓ Hbar) * (Zbar ⊓ Hbar).relIndex Zbar =
          Qbar.relIndex Zbar := hrel
      rw [hrelp, hval] at h2
      refine Nat.eq_of_mul_eq_mul_right hp.pos ?_
      calc Qbar.relIndex (Zbar ⊓ Hbar) * p = p := h2
        _ = 1 * p := by rw [one_mul]
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hQle
  have hbH : b ∉ H := by
    intro hbH'
    have hqb_H : q b ∈ Hbar := Subgroup.mem_map_of_mem q hbH'
    have hqb_Q : q b ∈ Qbar := by
      have : q b ∈ Zbar ⊓ Hbar := ⟨hbZ, hqb_H⟩
      rwa [hZbar_inf] at this
    exact hbW hqb_Q
  exact ⟨b, hbH, hbord, R, hRH, hbR⟩

theorem orderOf_eq_prime_mem_pCoreOf_of_cyclic_sylow {H : Subgroup Γ} (hH : H.Normal)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hcyc : ∀ P : Subgroup Γ, P ≤ H → IsPGroup p P → IsCyclic P)
    (hY : CFSG.Open.pCoreOf p H ≠ ⊥) {x : Γ} (hxH : x ∈ H) (hxord : orderOf x = p) :
    x ∈ CFSG.Open.pCoreOf p H := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let Y : Subgroup Γ := CFSG.Open.pCoreOf p H
  have hYp : IsPGroup p Y := CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf p H
  have hYle : Y ≤ H := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le p H
  obtain ⟨k, hk⟩ := hYp.exists_card_eq
  have hkpos : 0 < k := by
    rcases k with _ | k
    · exfalso
      exact hY (Subgroup.card_eq_one.mp hk)
    · omega
  have hpdvd : p ∣ Nat.card Y := by
    rw [hk]
    exact dvd_pow_self p hkpos.ne'
  haveI : Fintype Y := Fintype.ofFinite Y
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card (G := Y) p (by
    simpa [Nat.card_eq_fintype_card] using hpdvd)
  let yΓ : Γ := (y : Γ)
  have hyY : yΓ ∈ Y := y.2
  have hyH : yΓ ∈ H := hYle hyY
  have hyordΓ : orderOf yΓ = p := by
    simpa [yΓ] using hyord
  let xH : H := ⟨x, hxH⟩
  have hxHord : orderOf xH = p := by
    rw [Subgroup.orderOf_mk, hxord]
  have hxHp : IsPGroup p (Subgroup.zpowers xH) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hxHord, pow_one]
  obtain ⟨P, hxP⟩ := hxHp.exists_le_sylow
  let YH : Subgroup H := CFSG.pCore p H
  have hYH_eq : YH = Y.subgroupOf H := by
    change CFSG.pCore p H = Subgroup.comap H.subtype ((CFSG.pCore p H).map H.subtype)
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hYH_P : YH ≤ (P : Subgroup H) := CFSG.pCore_isPGroup.le_sylow_of_normal P
  have hyP : (⟨yΓ, hyH⟩ : H) ∈ (P : Subgroup H) := by
    apply hYH_P
    rw [hYH_eq]
    exact hyY
  have hPcyc : IsCyclic (P : Subgroup H) := by
    let PΓ : Subgroup Γ := (P : Subgroup H).map H.subtype
    have hPΓcyc : IsCyclic PΓ := hcyc PΓ (by rintro _ ⟨z, -, rfl⟩; exact z.2)
      (P.isPGroup'.map H.subtype)
    have e : (P : Subgroup H) ≃* PΓ :=
      Subgroup.equivMapOfInjective (f := H.subtype) (P : Subgroup H) H.subtype_injective
    exact e.isCyclic.mpr hPΓcyc
  have hxcard : Nat.card (Subgroup.zpowers xH) = p := by
    rw [Nat.card_zpowers, hxHord]
  have hycard : Nat.card (Subgroup.zpowers (⟨yΓ, hyH⟩ : H)) = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hyordΓ]
  have hxP' : Subgroup.zpowers xH ≤ (P : Subgroup H) := hxP
  have hyP' : Subgroup.zpowers (⟨yΓ, hyH⟩ : H) ≤ (P : Subgroup H) :=
    Subgroup.zpowers_le.mpr hyP
  have : IsCyclic (P : Subgroup H) := hPcyc
  have hxPcard : Nat.card ((Subgroup.zpowers xH).subgroupOf (P : Subgroup H)) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxP').toEquiv, hxcard]
  have hyPcard : Nat.card
      ((Subgroup.zpowers (⟨yΓ, hyH⟩ : H)).subgroupOf (P : Subgroup H)) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyP').toEquiv, hycard]
  have heqP : (Subgroup.zpowers xH).subgroupOf (P : Subgroup H) =
      (Subgroup.zpowers (⟨yΓ, hyH⟩ : H)).subgroupOf (P : Subgroup H) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq]
    rw [hxPcard, hyPcard]
  have heq : Subgroup.zpowers xH = Subgroup.zpowers (⟨yΓ, hyH⟩ : H) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hxP',
      ← Subgroup.map_subgroupOf_eq_of_le hyP', heqP]
  have hyYH : (⟨yΓ, hyH⟩ : H) ∈ Y.subgroupOf H := hyY
  have hxY : xH ∈ YH := by
    rw [hYH_eq]
    have hxmem : xH ∈ Subgroup.zpowers xH := Subgroup.mem_zpowers xH
    rw [heq] at hxmem
    exact Subgroup.zpowers_le.mpr hyYH hxmem
  exact Subgroup.mem_map.mpr ⟨xH, hxY, rfl⟩

theorem centralizer_pCoreOf_eq_pCoreOf_of_cyclic_sylow {H : Subgroup Γ} (hH : H.Normal)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hcyc : ∀ P : Subgroup Γ, P ≤ H → IsPGroup p P → IsCyclic P)
    (hOp' : CFSG.Open.relPPrimeCore p H = ⊥)
    (hYne : CFSG.Open.pCoreOf p H ≠ ⊥) :
    H ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf p H : Set Γ) =
      CFSG.Open.pCoreOf p H := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let Y : Subgroup Γ := CFSG.Open.pCoreOf p H
  let C : Subgroup Γ := H ⊓ Subgroup.centralizer (Y : Set Γ)
  have hYp : IsPGroup p Y := CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf p H
  have hYle : Y ≤ H := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le p H
  have hYcyc : IsCyclic Y := hcyc Y hYle hYp
  have hYleC : Y ≤ C := by
    refine le_inf hYle ?_
    have : IsMulCommutative Y := hYcyc.isMulCommutative
    exact Subgroup.le_centralizer (H := Y)
  have hCleH : C ≤ H := inf_le_left
  have hYnormalH : (Y.subgroupOf H).Normal := by
    have hEq : Y.subgroupOf H = CFSG.pCore p H := by
      change Subgroup.comap H.subtype ((CFSG.pCore p H).map H.subtype) = CFSG.pCore p H
      rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [hEq]
    infer_instance
  have hHnormY : H ≤ Subgroup.normalizer (Y : Set Γ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYle).mp hYnormalH
  have hHnormCen : H ≤ Subgroup.normalizer
      (Subgroup.centralizer (Y : Set Γ) : Set Γ) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_centralizer hHnormY
  have hHnormC : H ≤ Subgroup.normalizer (C : Set Γ) := by
    have hHle : H ≤ Subgroup.normalizer (H : Set Γ) ⊓
        Subgroup.normalizer (Subgroup.centralizer (Y : Set Γ) : Set Γ) :=
      le_inf Subgroup.le_normalizer hHnormCen
    exact hHle.trans (by
      simpa [C] using (Subgroup.inf_normalizer_le_normalizer_inf
        (H := H) (K := Subgroup.centralizer (Y : Set Γ))))
  have hCnormalH : (C.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCleH).mpr hHnormC
  have hcycC : ∀ P : Sylow p C, IsCyclic P := by
    intro P
    let PΓ : Subgroup Γ := (P : Subgroup C).map C.subtype
    have hPΓcyc : IsCyclic PΓ :=
      hcyc PΓ (by rintro _ ⟨z, -, rfl⟩; exact hCleH z.2) (P.isPGroup'.map C.subtype)
    have e : (P : Subgroup C) ≃* PΓ :=
      Subgroup.equivMapOfInjective (f := C.subtype) (P : Subgroup C) C.subtype_injective
    exact e.isCyclic.mpr hPΓcyc
  have hcenC : ∀ x : C, orderOf x = p → x ∈ Subgroup.center C := by
    intro x hxord
    have hxH : (x : Γ) ∈ H := x.2.1
    have hxordΓ : orderOf (x : Γ) = p := by
      simpa using (orderOf_injective C.subtype C.subtype_injective x).trans hxord
    have hxY : (x : Γ) ∈ Y :=
      orderOf_eq_prime_mem_pCoreOf_of_cyclic_sylow hH hp hp2 hcyc hYne hxH hxordΓ
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    have hcCen : (c : Γ) ∈ Subgroup.centralizer (Y : Set Γ) := c.2.2
    exact (Subgroup.mem_centralizer_iff.mp hcCen (x : Γ) hxY).symm
  have hcomp : CFSG.HasNormalPComplement p C :=
    CFSG.LocalAnalysis.RankThreeTheoremC.hasNormalPComplement_of_cyclic_sylow_central
      hcycC hcenC
  have hCquotp : IsPGroup p (C ⧸ CFSG.pPrimeCore p C) :=
    CFSG.isPGroup_quotient_pPrimeCore_of_hasNormalPComplement p C hcomp
  have hCcore : CFSG.pPrimeCore p C = ⊥ := by
    have hgle : CFSG.Open.GLAPPrimeCoreOf p C ≤ CFSG.Open.GLAPPrimeCoreOf p H :=
      CFSG.gLAPPrimeCoreOf_le_of_normal hCleH hCnormalH
    have hle : CFSG.Open.relPPrimeCore p C ≤ CFSG.Open.relPPrimeCore p H := by
      rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
          hp C,
        CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
          hp H]
      exact hgle
    have hrelC : CFSG.Open.relPPrimeCore p C = ⊥ :=
      le_bot_iff.mp (hle.trans hOp'.le)
    have hmap : (CFSG.pPrimeCore p C).map C.subtype = ⊥ := by
     rw [← CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
       hp C]
     exact hrelC
    exact (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pPrimeCore p C)
      C.subtype_injective).mp hmap
  have hCp : IsPGroup p C := by
    let e : (C ⧸ CFSG.pPrimeCore p C) ≃* (C ⧸ (⊥ : Subgroup C)) :=
      QuotientGroup.quotientMulEquivOfEq hCcore
    have hCq : IsPGroup p (C ⧸ (⊥ : Subgroup C)) :=
      IsPGroup.of_equiv hCquotp e
    exact IsPGroup.of_equiv hCq (QuotientGroup.quotientBot)
  have hCn : ∀ x ∈ H, ∀ y ∈ C, x * y * x⁻¹ ∈ C := by
    intro x hx y hy
    let yH : C.subgroupOf H := ⟨⟨y, hCleH hy⟩, hy⟩
    let xH : H := ⟨x, hx⟩
    refine ⟨?_, ?_⟩
    · exact H.mul_mem (H.mul_mem hx (hCleH hy)) (H.inv_mem hx)
    · exact (hCnormalH.conj_mem yH yH.2 xH).2
  have hCleY : C ≤ Y := CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hCleH hCn hCp
  exact le_antisymm hCleY hYleC

theorem exists_orderOf_eq_prime_of_normal_pPrime_index_prime
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {K : Subgroup X} [hK : K.Normal] (hKp : Nat.Coprime p (Nat.card K))
    (hidx : K.index = p) :
    ∃ e : X, e ∉ K ∧ orderOf e = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime (N := K) (by
    rw [hidx]
    exact hKp.symm)
  have hCcard : Nat.card C = p := by
    have h1 : Nat.card K * Nat.card C = Nat.card X := hC.card_mul_card
    have h2 : Nat.card K * p = Nat.card X := by
      rw [← Subgroup.card_mul_index K, hidx]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  haveI : Fintype C := Fintype.ofFinite C
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card (G := C) p (by
    rw [← Nat.card_eq_fintype_card, hCcard])
  have hcXord : orderOf (c : X) = p := by
    simpa using (orderOf_injective C.subtype C.subtype_injective c).trans hc
  refine ⟨(c : X), ?_, hcXord⟩
  intro hcK
  have hcbot : (c : X) ∈ (⊥ : Subgroup X) := by
    rw [← hC.disjoint.eq_bot]
    exact ⟨hcK, c.2⟩
  have hc1 : (c : X) = 1 := by simpa using hcbot
  have h1 : orderOf (c : X) = 1 := by rw [hc1]; simp
  rw [hcXord] at h1
  exact hp.ne_one h1

theorem exists_orderOf_eq_prime_mem_normalizer_of_pCore_ne_bot
    (hp : p.Prime) (hp2 : p ≠ 2)
    (π : Γ →* DihedralGroup p) (hπ : Function.Surjective π)
    (hcyc : ∀ P : Subgroup Γ, P ≤ π.ker → IsPGroup p P → IsCyclic P)
    (hK : CFSG.Open.IsKGroup Γ)
    (hOp' : CFSG.Open.relPPrimeCore p π.ker = ⊥)
    {Q : Subgroup Γ} (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q π.ker) (hQne : Q ≠ ⊥)
    (hYne : CFSG.Open.pCoreOf p π.ker ≠ ⊥) :
    ∃ e : Γ, π e ≠ 1 ∧ orderOf e = p ∧ e ∈ Subgroup.normalizer (Q : Set Γ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup Γ := π.ker
  have hH : H.Normal := MonoidHom.normal_ker π
  let Y : Subgroup Γ := CFSG.Open.pCoreOf p H
  let N : Subgroup Γ := Subgroup.normalizer (Q : Set Γ)
  let K : Subgroup Γ := H ⊓ N
  have hYp : IsPGroup p Y := CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf p H
  have hYle : Y ≤ H := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le p H
  have hYcyc : IsCyclic Y := hcyc Y hYle hYp
  have hCeq : H ⊓ Subgroup.centralizer (Y : Set Γ) = Y :=
    centralizer_pCoreOf_eq_pCoreOf_of_cyclic_sylow hH hp hp2 hcyc hOp' hYne
  have hYQbot : Y ⊓ Q = ⊥ :=
    (IsPGroup.disjoint_of_ne p 2 hp2 Y Q hYp hQ.isPGroup).eq_bot
  have hYnormalH : (Y.subgroupOf H).Normal := by
    have hEq : Y.subgroupOf H = CFSG.pCore p H := by
      change Subgroup.comap H.subtype ((CFSG.pCore p H).map H.subtype) = CFSG.pCore p H
      rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [hEq]
    infer_instance
  have hHnormY : H ≤ Subgroup.normalizer (Y : Set Γ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYle).mp hYnormalH
  have hKp : Nat.Coprime p (Nat.card K) := by
    rw [hp.coprime_iff_not_dvd]
    intro hpdvd
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨v, hvord⟩ := exists_prime_orderOf_dvd_card (G := K) p (by
      rwa [← Nat.card_eq_fintype_card])
    let u : Γ := (v : Γ)
    have huH : u ∈ H := v.2.1
    have huN : u ∈ N := v.2.2
    have huord : orderOf u = p := by
      simpa [u] using (orderOf_injective K.subtype K.subtype_injective v).trans hvord
    have huY : u ∈ Y :=
      orderOf_eq_prime_mem_pCoreOf_of_cyclic_sylow hH hp hp2 hcyc hYne huH huord
    have hcentral : ∀ q ∈ Q, q * u * q⁻¹ = u := by
      intro q hq
      have hqH : q ∈ H := hQ.le hq
      have huqQ : u * q * u⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp huN q).mp hq
      have huqY : u * q * u⁻¹ * q⁻¹ ∈ Y := by
        have hqinvY : q * u⁻¹ * q⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp (hHnormY hqH) (u⁻¹)).mp (Y.inv_mem huY)
        have h := Y.mul_mem huY hqinvY
        simpa [mul_assoc] using h
      have huqQ' : u * q * u⁻¹ * q⁻¹ ∈ Q :=
        Q.mul_mem huqQ (Q.inv_mem hq)
      have hbot : u * q * u⁻¹ * q⁻¹ ∈ (⊥ : Subgroup Γ) := by
        rw [← hYQbot]
        exact ⟨huqY, huqQ'⟩
      have h1 : u * q * u⁻¹ * q⁻¹ = 1 := by simpa using hbot
      have huq : u * q = q * u := by
        calc u * q = (u * q * u⁻¹ * q⁻¹) * (q * u) := by group
          _ = 1 * (q * u) := by rw [h1]
          _ = q * u := by rw [one_mul]
      calc q * u * q⁻¹ = (u * q) * q⁻¹ := by rw [huq.symm]
        _ = u := by group
    have hQcenY : ∀ q ∈ Q, ∀ d ∈ Y, q * d * q⁻¹ = d := by
      intro q hq d hd
      have hqH : q ∈ H := hQ.le hq
      have hYp' : ∀ d ∈ Y, ∃ k : ℕ, d ^ p ^ k = 1 := by
        intro d hd
        obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp hYp ⟨d, hd⟩
        exact ⟨k, by simpa using hk⟩
      have hqY : ∀ d ∈ Y, q * d * q⁻¹ ∈ Y := by
        intro d hd
        exact (Subgroup.mem_normalizer_iff.mp (hHnormY hqH) d).mp hd
      have hqu : q * u * q⁻¹ = u := hcentral q hq
      have hs : Nat.Coprime p (orderOf q) := by
        rw [hp.coprime_iff_not_dvd]
        intro hpq
        obtain ⟨k, hk⟩ := hQ.isPGroup.exists_orderOf_dvd_pow (⟨q, hq⟩ : Q)
        have hk' : orderOf q ∣ 2 ^ k := by
          simpa using hk
        have hpdvd2 : p ∣ 2 := hp.dvd_of_dvd_pow (hpq.trans hk')
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdvd2)
      have hgs : ∀ d ∈ Y, (q ^ orderOf q) * d * (q ^ orderOf q)⁻¹ = d := by
        intro d hd
        rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one]
      exact CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.cyclic_coprime_aut_trivial
        hp (D := Y) (x := u) hYp' huY huord hqY hqu hs hgs d hd
    have hQleY : Q ≤ Y := by
      intro q hq
      have hqH : q ∈ H := hQ.le hq
      have hqC : q ∈ H ⊓ Subgroup.centralizer (Y : Set Γ) := by
        refine ⟨hqH, ?_⟩
        change q ∈ Subgroup.centralizer (Y : Set Γ)
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        have h := hQcenY q hq d hd
        have hqd : q * d = d * q := by
          calc q * d = (q * d * q⁻¹) * q := by group
            _ = d * q := by rw [h]
        exact hqd.symm
      rwa [hCeq] at hqC
    have hQbot : Q = ⊥ := by
      have hle : Q ≤ Y ⊓ Q := le_inf hQleY le_rfl
      rw [hYQbot] at hle
      exact le_bot_iff.mp hle
    exact hQne hQbot
  have hfratt : H ⊔ N = ⊤ := by
    have htop : (⊤ : Subgroup Γ) ≤ H ⊔ N :=
      CFSG.LocalAnalysis.RankThreeTheoremC.le_sup_normalizer_of_isSylowOf
        (by rw [Subgroup.normalizer_eq_top (H := H)]) hQ
    exact top_le_iff.mp htop
  have hmapN : N.map π = ⊤ := by
    have h := congrArg (Subgroup.map π) hfratt
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective π hπ] at h
    have hHmap : H.map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
    rwa [hHmap, bot_sup_eq] at h
  let πN : N →* DihedralGroup p := π.comp N.subtype
  have hπN : Function.Surjective πN := by
    intro y
    have hy : y ∈ N.map π := by rw [hmapN]; exact Subgroup.mem_top y
    obtain ⟨n, hnN, hny⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨n, hnN⟩, hny⟩
  let R : Subgroup (DihedralGroup p) := Subgroup.zpowers (DihedralGroup.r 1)
  have hRcard : Nat.card R = p := by
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  let L : Subgroup N := R.comap πN
  have hHL : H.subgroupOf N ≤ L := by
    intro x hx
    change πN x ∈ R
    have hxH : (x : Γ) ∈ H := hx
    rw [show πN x = 1 by
      change π (x : Γ) = 1
      exact (MonoidHom.mem_ker).mp hxH]
    exact Subgroup.one_mem _
  let KN : Subgroup N := H.subgroupOf N
  let KNL : Subgroup L := KN.subgroupOf L
  have hKNLnormal : KNL.Normal := Subgroup.normal_subgroupOf
  have hKNcard : Nat.card KN = Nat.card K := by
    have hEq : KN = K.subgroupOf N := by
      ext x
      simp [KN, K]
    rw [hEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : K ≤ N)).toEquiv
  have hKNcop : Nat.Coprime p (Nat.card KNL) := by
    have e : KN ≃* KNL := (Subgroup.subgroupOfEquivOfLe hHL).symm
    rw [← Nat.card_congr e.toEquiv, hKNcard]
    exact hKp
  have hKNLindex : KNL.index = p := by
    let φ : L →* R := (πN.comp L.subtype).codRestrict R fun x => x.2
    have hφsurj : Function.Surjective φ := by
      intro r
      obtain ⟨n, hn⟩ := hπN (r : DihedralGroup p)
      refine ⟨⟨n, ?_⟩, ?_⟩
      · change πN n ∈ R
        rw [hn]
        exact r.2
      · apply Subtype.ext
        exact hn
    have hφker : φ.ker = KNL := by
      ext x
      constructor
      · intro hx
        have h1 : φ x = 1 := hx
        have h2 : πN (x : L) = 1 := congrArg Subtype.val h1
        exact h2
      · intro hx
        apply Subtype.ext
        exact hx
    have h1 : Nat.card KNL * Nat.card R = Nat.card ↥L := by
      have h := Subgroup.card_ker_mul_card_range φ
      rw [hφker, MonoidHom.range_eq_top.mpr hφsurj, Subgroup.card_top] at h
      exact h
    have h2 : Nat.card KNL * KNL.index = Nat.card ↥L := Subgroup.card_mul_index KNL
    have h3 : Nat.card KNL * KNL.index = Nat.card KNL * p := by
      rw [h2, ← h1, hRcard]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
  obtain ⟨c, hcK, hcord⟩ :=
    exists_orderOf_eq_prime_of_normal_pPrime_index_prime hp hKNcop hKNLindex
  let e : Γ := N.subtype (L.subtype c)
  have heN : e ∈ N := (L.subtype c).2
  have heH : e ∉ H := by
    intro heH
    apply hcK
    change (c : N) ∈ H.subgroupOf N
    exact heH
  have heord : orderOf e = p := by
    have hinj : Function.Injective (N.subtype.comp L.subtype) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext hxy)
    simpa [e] using (orderOf_injective (N.subtype.comp L.subtype) hinj c).trans hcord
  refine ⟨e, ?_, heord, heN⟩
  intro hπe
  exact heH ((MonoidHom.mem_ker).mpr hπe)

theorem abelian_minimal_normal_contradiction {H V : Subgroup Γ} (hH : H.Normal)
    (hp : p.Prime) (hOp' : CFSG.Open.relPPrimeCore p H = ⊥)
    (hYbot : CFSG.Open.pCoreOf p H = ⊥) (hVnormal : V.Normal) (hVleH : V ≤ H)
    (hVne : V ≠ ⊥) (hVmin : ∀ M : Subgroup Γ, M.Normal → M ≤ V → M = ⊥ ∨ M = V)
    (hVcomm : IsMulCommutative V) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : V.Normal := hVnormal
  have : IsMulCommutative V := hVcomm
  have : Group.IsSolvable V := inferInstance
  have : CFSG.IsMinimalNormal V :=
    CFSG.IsMinimalNormal.mk (fun K hK hle => hVmin K hK hle)
  obtain ⟨r, hrprime, hVele⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian V
  have : CFSG.IsElementaryAbelian r V := hVele
  have : Fact r.Prime := ⟨hrprime⟩
  have hVp : IsPGroup r V := CFSG.IsElementaryAbelian.isPGroup r V
  obtain ⟨k, hk⟩ := hVp.exists_card_eq
  have hn : ∀ x ∈ H, ∀ y ∈ V, x * y * x⁻¹ ∈ V := by
    intro x hx y hy
    exact hVnormal.conj_mem y hy x
  by_cases hrp : r = p
  · subst r
    have hVleY : V ≤ CFSG.Open.pCoreOf p H :=
      CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hVleH hn hVp
    rw [hYbot] at hVleY
    exact hVne (le_bot_iff.mp hVleY)
  · have hpr : Nat.Coprime p r := by
      rw [Nat.coprime_comm, hrprime.coprime_iff_not_dvd]
      intro h
      exact hrp ((Nat.prime_dvd_prime_iff_eq hrprime hp).mp h)
    have hcop : Nat.Coprime p (Nat.card V) := by
      rw [hk]
      exact hpr.pow_right k
    have hVleP : V ≤ CFSG.Open.relPPrimeCore p H :=
      le_relPPrimeCore_of_normal_coprime hp hVleH Subgroup.normal_subgroupOf hcop
    rw [hOp'] at hVleP
    exact hVne (le_bot_iff.mp hVleP)

theorem minimal_normal_factors_p_dvd_and_unique {H V : Subgroup Γ} {r : ℕ}
    {S : Fin r → Subgroup Γ} (hp : p.Prime) (hVnormal : V.Normal) (hVleH : V ≤ H)
    (hVne : V ≠ ⊥) (hOp' : CFSG.Open.relPPrimeCore p H = ⊥)
    (hcyc : ∀ P : Subgroup Γ, P ≤ H → IsPGroup p P → IsCyclic P)
    (hr : 1 ≤ r) (hSV : ∀ i, S i ≤ V)
    (hSconj : ∀ i j, ∃ g : Γ, S j = CFSG.conjugate (S i) g)
    (e : ((i : Fin r) → S i) ≃* V)
    (he : ∀ (i : Fin r) (x : (j : Fin r) → S j), (∀ j, j ≠ i → x j = 1) →
      (e x : Γ) = x i) :
    r = 1 ∧ ∀ i, p ∣ Nat.card (S i) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpdiv : ∀ i, p ∣ Nat.card (S i) := by
    by_contra h
    have hex : ∃ i, ¬ p ∣ Nat.card (S i) := by
      by_contra hcon
      apply h
      intro i
      by_contra hi
      exact hcon ⟨i, hi⟩
    obtain ⟨i0, hi0⟩ := hex
    have hcard0 : ∀ i, Nat.card (S i) = Nat.card (S i0) := by
      intro i
      obtain ⟨g, hg⟩ := hSconj i0 i
      rw [hg, CFSG.conjugate]
      exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have hcopS : ∀ i, Nat.Coprime p (Nat.card (S i)) := by
      intro i
      rw [hp.coprime_iff_not_dvd, hcard0 i]
      exact hi0
    have hcopProd : Nat.Coprime p (Nat.card ((i : Fin r) → S i)) := by
      rw [Nat.card_pi]
      exact Nat.Coprime.prod_right (fun i _ => hcopS i)
    have hcopV : Nat.Coprime p (Nat.card V) := by
      rw [← Nat.card_congr e.toEquiv]
      exact hcopProd
    have hVleP : V ≤ CFSG.Open.relPPrimeCore p H :=
      le_relPPrimeCore_of_normal_coprime hp hVleH Subgroup.normal_subgroupOf hcopV
    rw [hOp'] at hVleP
    exact hVne (le_bot_iff.mp hVleP)
  have hcard : ∀ i j, Nat.card (S j) = Nat.card (S i) := by
    intro i j
    obtain ⟨g, hg⟩ := hSconj i j
    rw [hg, CFSG.conjugate]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  refine ⟨?_, hpdiv⟩
  by_contra hr1
  have hr2 : 2 ≤ r := by omega
  let i0 : Fin r := ⟨0, by omega⟩
  let j0 : Fin r := ⟨1, by omega⟩
  have hij : i0 ≠ j0 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, j0] at this
  haveI : Fintype (S i0) := Fintype.ofFinite _
  obtain ⟨a, haord⟩ := exists_prime_orderOf_dvd_card (G := S i0) p (by
    rw [← Nat.card_eq_fintype_card]
    exact hpdiv i0)
  haveI : Fintype (S j0) := Fintype.ofFinite _
  obtain ⟨b, hbord⟩ := exists_prime_orderOf_dvd_card (G := S j0) p (by
    rw [← Nat.card_eq_fintype_card]
    exact hpdiv j0)
  let aΓ : Γ := (a : Γ)
  let bΓ : Γ := (b : Γ)
  have ha_mem : aΓ ∈ S i0 := a.2
  have hb_mem : bΓ ∈ S j0 := b.2
  have ha_ord : orderOf aΓ = p := by
    simpa [aΓ] using (orderOf_injective (S i0).subtype (S i0).subtype_injective a).trans haord
  have hb_ord : orderOf bΓ = p := by
    simpa [bΓ] using (orderOf_injective (S j0).subtype (S j0).subtype_injective b).trans hbord
  have hcomm : aΓ * bΓ = bΓ * aΓ :=
    (CFSG.Timmesfeld.Bridge.Asc72.WreathStruct.commute_of_mem_of_ne he hij ha_mem hb_mem).eq
  have hAp : IsPGroup p (Subgroup.zpowers aΓ) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ha_ord, pow_one]
  have hBp : IsPGroup p (Subgroup.zpowers bΓ) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hb_ord, pow_one]
  have hnorm : Subgroup.zpowers aΓ ≤
      Subgroup.normalizer (Subgroup.zpowers bΓ : Set Γ) :=
    Subgroup.zpowers_le.mpr
      (mem_normalizer_zpowers_of_conj_eq (mul_inv_eq_of_eq_mul hcomm))
  have hPp : IsPGroup p ↥(Subgroup.zpowers aΓ ⊔ Subgroup.zpowers bΓ) :=
    IsPGroup.to_sup_of_normal_right' hAp hBp hnorm
  have hPleH : Subgroup.zpowers aΓ ⊔ Subgroup.zpowers bΓ ≤ H := by
    refine sup_le ?_ ?_
    · exact Subgroup.zpowers_le.mpr (hVleH (hSV i0 ha_mem))
    · exact Subgroup.zpowers_le.mpr (hVleH (hSV j0 hb_mem))
  have hPcyc : IsCyclic ↥(Subgroup.zpowers aΓ ⊔ Subgroup.zpowers bΓ) :=
    hcyc _ hPleH hPp
  have := hPcyc
  have hAcard : Nat.card ((Subgroup.zpowers aΓ).subgroupOf
      (Subgroup.zpowers aΓ ⊔ Subgroup.zpowers bΓ)) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
      Nat.card_zpowers, ha_ord]
  have hBcard : Nat.card ((Subgroup.zpowers bΓ).subgroupOf
      (Subgroup.zpowers aΓ ⊔ Subgroup.zpowers bΓ)) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv,
      Nat.card_zpowers, hb_ord]
  have hEqP : (Subgroup.zpowers aΓ).subgroupOf
      (Subgroup.zpowers aΓ ⊔ Subgroup.zpowers bΓ) =
      (Subgroup.zpowers bΓ).subgroupOf
        (Subgroup.zpowers aΓ ⊔ Subgroup.zpowers bΓ) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq]
    rw [hAcard, hBcard]
  have hEq : Subgroup.zpowers aΓ = Subgroup.zpowers bΓ := by
    have hmap := congrArg
      (Subgroup.map (Subgroup.zpowers aΓ ⊔ Subgroup.zpowers bΓ).subtype) hEqP
    simpa [Subgroup.map_subgroupOf_eq_of_le le_sup_left,
      Subgroup.map_subgroupOf_eq_of_le le_sup_right] using hmap
  have ha_inf : aΓ ∈ S i0 ⊓ S j0 := by
    refine ⟨ha_mem, ?_⟩
    have ha_zp : aΓ ∈ Subgroup.zpowers aΓ := Subgroup.mem_zpowers aΓ
    rw [hEq] at ha_zp
    exact (Subgroup.zpowers_le.mpr hb_mem) ha_zp
  have hInf : S i0 ⊓ S j0 = ⊥ :=
    eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr
      (CFSG.Timmesfeld.Bridge.Asc72.WreathStruct.eq_one_of_mem_of_mem he hij ha.1 ha.2)
  rw [hInf] at ha_inf
  have ha1 : aΓ = 1 := by simpa using ha_inf
  have h1 : orderOf aΓ = 1 := by rw [ha1]; simp
  rw [ha_ord] at h1
  exact hp.ne_one h1

theorem centralizer_eq_bot_of_minimal_normal_nonabelian {H V : Subgroup Γ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hcyc : ∀ P : Subgroup Γ, P ≤ H → IsPGroup p P → IsCyclic P)
    (hVnormal : V.Normal) (hVleH : V ≤ H) (hVne : V ≠ ⊥)
    (hVsimple : IsSimpleGroup V)
    (hnonab : ∃ a ∈ V, ∃ b ∈ V, a * b ≠ b * a)
    (hpdvd : p ∣ Nat.card V)
    (hOp' : CFSG.Open.relPPrimeCore p H = ⊥) :
    H ⊓ Subgroup.centralizer (V : Set Γ) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : V.Normal := hVnormal
  let C : Subgroup Γ := H ⊓ Subgroup.centralizer (V : Set Γ)
  have hcenterV : Subgroup.center V = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center V) with h | h
    · exact h
    · exfalso
      have : IsMulCommutative V := Subgroup.center_eq_top_iff.mp h
      obtain ⟨a, ha, b, hb, hab⟩ := hnonab
      apply hab
      exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : V) (⟨b, hb⟩ : V))
  have hCV : C ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxV : x ∈ V := hx.2
    have hxC : x ∈ C := hx.1
    have hxcen : x ∈ Subgroup.centralizer (V : Set Γ) := hxC.2
    have hxcenter : (⟨x, hxV⟩ : V) ∈ Subgroup.center V := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxcen (y : Γ) y.2
    have hx1 : (⟨x, hxV⟩ : V) = 1 := by
      rw [← Subgroup.mem_bot, ← hcenterV]
      exact hxcenter
    simpa using congrArg Subtype.val hx1
  have hCnotp : ¬ p ∣ Nat.card C := by
    intro hpdvdC
    haveI : Fintype C := Fintype.ofFinite C
    obtain ⟨u, huord⟩ := exists_prime_orderOf_dvd_card (G := C) p (by
      rw [← Nat.card_eq_fintype_card]
      exact hpdvdC)
    haveI : Fintype V := Fintype.ofFinite V
    obtain ⟨v, hvord⟩ := exists_prime_orderOf_dvd_card (G := V) p (by
      rw [← Nat.card_eq_fintype_card]
      exact hpdvd)
    let uΓ : Γ := (u : Γ)
    let vΓ : Γ := (v : Γ)
    have huC : uΓ ∈ C := u.2
    have huH : uΓ ∈ H := huC.1
    have huCen : uΓ ∈ Subgroup.centralizer (V : Set Γ) := huC.2
    have hvV : vΓ ∈ V := v.2
    have hvH : vΓ ∈ H := hVleH hvV
    have huordΓ : orderOf uΓ = p := by
      simpa [uΓ] using (orderOf_injective C.subtype C.subtype_injective u).trans huord
    have hvordΓ : orderOf vΓ = p := by
      simpa [vΓ] using (orderOf_injective V.subtype V.subtype_injective v).trans hvord
    have hu_notV : uΓ ∉ V := by
      intro huV
      have hbot : uΓ ∈ (⊥ : Subgroup Γ) := by
        rw [← hCV]
        exact ⟨huC, huV⟩
      have hu1 : uΓ = 1 := by simpa using hbot
      have h1 : orderOf uΓ = 1 := by rw [hu1]; simp
      rw [huordΓ] at h1
      exact hp.ne_one h1
    have hv_notC : vΓ ∉ C := by
      intro hvC
      have hbot : vΓ ∈ (⊥ : Subgroup Γ) := by
        rw [← hCV]
        exact ⟨hvC, hvV⟩
      have hv1 : vΓ = 1 := by simpa using hbot
      have h1 : orderOf vΓ = 1 := by rw [hv1]; simp
      rw [hvordΓ] at h1
      exact hp.ne_one h1
    have hcomm : vΓ * uΓ = uΓ * vΓ :=
      Subgroup.mem_centralizer_iff.mp huCen vΓ hvV
    have hVp : IsPGroup p (Subgroup.zpowers vΓ) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hvordΓ, pow_one]
    have hUp : IsPGroup p (Subgroup.zpowers uΓ) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, huordΓ, pow_one]
    have hnorm : Subgroup.zpowers vΓ ≤
        Subgroup.normalizer (Subgroup.zpowers uΓ : Set Γ) :=
      Subgroup.zpowers_le.mpr
      (mem_normalizer_zpowers_of_conj_eq (mul_inv_eq_of_eq_mul hcomm))
    have hPp : IsPGroup p ↥(Subgroup.zpowers vΓ ⊔ Subgroup.zpowers uΓ) :=
      IsPGroup.to_sup_of_normal_right' hVp hUp hnorm
    have hPleH : Subgroup.zpowers vΓ ⊔ Subgroup.zpowers uΓ ≤ H := by
      refine sup_le ?_ ?_
      · exact Subgroup.zpowers_le.mpr hvH
      · exact Subgroup.zpowers_le.mpr huH
    have hPcyc : IsCyclic ↥(Subgroup.zpowers vΓ ⊔ Subgroup.zpowers uΓ) :=
      hcyc _ hPleH hPp
    have := hPcyc
    have hVcard : Nat.card ((Subgroup.zpowers vΓ).subgroupOf
        (Subgroup.zpowers vΓ ⊔ Subgroup.zpowers uΓ)) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
        Nat.card_zpowers, hvordΓ]
    have hUcard : Nat.card ((Subgroup.zpowers uΓ).subgroupOf
        (Subgroup.zpowers vΓ ⊔ Subgroup.zpowers uΓ)) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv,
        Nat.card_zpowers, huordΓ]
    have hEqP : (Subgroup.zpowers vΓ).subgroupOf
        (Subgroup.zpowers vΓ ⊔ Subgroup.zpowers uΓ) =
        (Subgroup.zpowers uΓ).subgroupOf
          (Subgroup.zpowers vΓ ⊔ Subgroup.zpowers uΓ) := by
      rw [IsCyclic.subgroup_eq_iff_card_eq]
      rw [hVcard, hUcard]
    have hEq : Subgroup.zpowers vΓ = Subgroup.zpowers uΓ := by
      have hmap := congrArg
        (Subgroup.map (Subgroup.zpowers vΓ ⊔ Subgroup.zpowers uΓ).subtype) hEqP
      simpa [Subgroup.map_subgroupOf_eq_of_le le_sup_left,
        Subgroup.map_subgroupOf_eq_of_le le_sup_right] using hmap
    have hu_zp : uΓ ∈ Subgroup.zpowers vΓ := by
      rw [hEq]
      exact Subgroup.mem_zpowers uΓ
    exact hu_notV ((Subgroup.zpowers_le.mpr hvV) hu_zp)
  have hCnormal : (C.subgroupOf H).Normal := by
    have : (Subgroup.centralizer (V : Set Γ)).Normal := inferInstance
    have hEq : C.subgroupOf H =
        (Subgroup.centralizer (V : Set Γ)).subgroupOf H := by
      ext x
      simp [C]
    rw [hEq]
    infer_instance
  have hcop : Nat.Coprime p (Nat.card C) := hp.coprime_iff_not_dvd.mpr hCnotp
  have hCleP : C ≤ CFSG.Open.relPPrimeCore p H :=
    le_relPPrimeCore_of_normal_coprime hp inf_le_left hCnormal hcop
  rw [hOp'] at hCleP
  exact le_bot_iff.mp hCleP

theorem exists_orderOf_eq_prime_mem_normalizer_of_kfact
    {H J : Subgroup Γ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hH : H.Normal) (hJleH : J ≤ H) (hJnormal : J.Normal) (hJsimple : IsSimpleGroup J)
    (hJnonab : ∃ a ∈ J, ∃ b ∈ J, a * b ≠ b * a)
    (hpdvd : p ∣ Nat.card J)
    (hcyc : ∀ P : Subgroup Γ, P ≤ H → IsPGroup p P → IsCyclic P)
    (hK : CFSG.Open.IsKGroup Γ)
    (hKF : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (hHcentral : H ⊓ Subgroup.centralizer (J : Set Γ) = ⊥)
    (π : Γ →* DihedralGroup p) (hπ : Function.Surjective π) (hJker : J ≤ π.ker)
    (hkerH : π.ker ≤ H) :
    ∃ d : Γ, π d ≠ 1 ∧ orderOf d = p ∧ d ∈ Subgroup.centralizer (H : Set Γ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : J.Normal := hJnormal
  haveI : Fintype J := Fintype.ofFinite J
  obtain ⟨v, hvord⟩ := exists_prime_orderOf_dvd_card (G := J) p (by
    rw [← Nat.card_eq_fintype_card]
    exact hpdvd)
  have hvp : IsPGroup p (Subgroup.zpowers v) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hvord, pow_one]
  obtain ⟨P, hvP⟩ := hvp.exists_le_sylow
  have hPne : (P : Subgroup J) ≠ ⊥ := by
    intro hbot
    have hvbot : v ∈ (⊥ : Subgroup J) := by
      rw [← hbot]
      exact hvP (Subgroup.mem_zpowers v)
    have hv1 : v = 1 := by simpa using hvbot
    have h1 : orderOf v = 1 := by rw [hv1]; simp
    rw [hvord] at h1
    exact hp.ne_one h1
  let PJΓ : Subgroup Γ := (P : Subgroup J).map J.subtype
  have hPJΓcyc : IsCyclic PJΓ :=
    hcyc PJΓ (by rintro _ ⟨x, -, rfl⟩; exact hJleH x.2) (P.isPGroup'.map J.subtype)
  have hPJcyc : IsCyclic (P : Subgroup J) :=
    (Subgroup.equivMapOfInjective (f := J.subtype) (P : Subgroup J)
      J.subtype_injective).isCyclic.mpr hPJΓcyc
  have : IsCyclic PJΓ := hPJΓcyc
  have hPcomm : IsMulCommutative (P : Subgroup J) := hPJcyc.isMulCommutative
  have hfratt : J ⊔ Subgroup.normalizer (PJΓ : Set Γ) = ⊤ := by
    have h := CFSG.LocalAnalysis.RankThreeTheoremC.le_sup_normalizer_of_isSylowOf
      (H := ⊤) (Y := J) (S := PJΓ)
      (by rw [Subgroup.normalizer_eq_top (H := J)]) ⟨P, rfl⟩
    exact top_le_iff.mp h
  let N : Subgroup Γ := Subgroup.normalizer (PJΓ : Set Γ)
  have hmapN : N.map π = ⊤ := by
    have h := congrArg (Subgroup.map π) hfratt
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective π hπ] at h
    have hJmap : J.map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      exact hJker
    rwa [hJmap, bot_sup_eq] at h
  let πN : N →* DihedralGroup p := π.comp N.subtype
  have hπN : Function.Surjective πN := by
    intro y
    have hy : y ∈ N.map π := by rw [hmapN]; exact Subgroup.mem_top y
    obtain ⟨n, hnN, hny⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨n, hnN⟩, hny⟩
  obtain ⟨x1, hx1⟩ := hπN (DihedralGroup.r 1 : DihedralGroup p)
  obtain ⟨x2, hx2⟩ := hπN (DihedralGroup.sr 0 : DihedralGroup p)
  have : IsMulCommutative (MulAut PJΓ) := by
    refine ⟨⟨fun f g => ?_⟩⟩
    apply (IsCyclic.mulAutMulEquiv PJΓ).injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  let ψ : N →* MulAut PJΓ := Subgroup.normalizerMonoidHom PJΓ
  let xN : N := ⁅x1, x2⁆
  have hxNcomm : xN ∈ ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x1) (Subgroup.mem_top x2)
  have hxker : xN ∈ ψ.ker :=
    Abelianization.commutator_subset_ker ψ hxNcomm
  rw [Subgroup.normalizerMonoidHom_ker] at hxker
  have hxcen : (xN : Γ) ∈ Subgroup.centralizer (PJΓ : Set Γ) :=
    Subgroup.mem_subgroupOf.mp hxker
  have hπx : π (xN : Γ) = (DihedralGroup.r 2 : DihedralGroup p) := by
    have h1 : π (x1 : Γ) = (DihedralGroup.r 1 : DihedralGroup p) := hx1
    have h2 : π (x2 : Γ) = (DihedralGroup.sr 0 : DihedralGroup p) := hx2
    change π (⁅(x1 : Γ), (x2 : Γ)⁆) = _
    simp [commutatorElement_def, map_mul, map_inv, h1, h2]
    ring_nf
  obtain ⟨k, m, hm, hordx⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (xN : Γ)).ne' p hp.ne_one
  let c : Γ := (xN : Γ) ^ m
  have hc_pow : c ^ (p ^ k) = 1 := by
    dsimp [c]
    rw [← pow_mul, Nat.mul_comm, ← hordx, pow_orderOf_eq_one]
  have hc_central : c ∈ Subgroup.centralizer (PJΓ : Set Γ) :=
    Subgroup.pow_mem _ hxcen m
  have hr2ord : orderOf (DihedralGroup.r 2 : DihedralGroup p) = p := by
    rw [DihedralGroup.orderOf_r]
    have hcop : Nat.Coprime p 2 := by
      rw [hp.coprime_iff_not_dvd]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    have hgcd : Nat.gcd p 2 = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
    have hp2le : 2 ≤ p := hp.two_le
    have hp2lt : 2 < p := by omega
    have hval : ZMod.val (2 : ZMod p) = 2 := by
      rw [ZMod.val_ofNat]
      exact Nat.mod_eq_of_lt hp2lt
    rw [hval, hgcd, Nat.div_one]
  have hπc_eq : π c = (DihedralGroup.r 2 : DihedralGroup p) ^ m := by
    simp [c, map_pow, hπx]
  have hπc : π c ≠ 1 := by
    rw [hπc_eq]
    intro h
    have hpdvdm : p ∣ m := by
      rw [← hr2ord]
      exact orderOf_dvd_iff_pow_eq_one.mpr h
    exact hm hpdvdm
  let φ : MulAut J := MulAut.conjNormal c
  have hφpow : ∃ n : ℕ, φ ^ (p ^ n) = 1 := by
    refine ⟨k, ?_⟩
    dsimp [φ]
    rw [← map_pow, hc_pow, map_one]
  have hφcomm : ∀ g ∈ (P : Subgroup J), φ * MulAut.conj g = MulAut.conj g * φ := by
    intro g hg
    ext h
    have hcg : c * (g : Γ) = (g : Γ) * c := by
      have hmem : (g : Γ) ∈ PJΓ := Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp hc_central (g : Γ) hmem).symm
    change c * ((g : Γ) * (h : Γ) * (g : Γ)⁻¹) * c⁻¹ =
      (g : Γ) * (c * (h : Γ) * c⁻¹) * (g : Γ)⁻¹
    calc c * ((g : Γ) * (h : Γ) * (g : Γ)⁻¹) * c⁻¹
        = (c * (g : Γ)) * (h : Γ) * ((c * (g : Γ))⁻¹) := by group
      _ = ((g : Γ) * c) * (h : Γ) * (((g : Γ) * c)⁻¹) := by rw [hcg]
      _ = (g : Γ) * (c * (h : Γ) * c⁻¹) * (g : Γ)⁻¹ := by group
  have hJnonabSub : ∃ a b : J, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hJnonab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hJcat : CFSG.Open.IsCatalogGroup J :=
    hK.isCatalogGroup_of_surjective J hJnonabSub (MonoidHom.id J) Function.surjective_id
  obtain ⟨g0, hg0P, hg0eq⟩ :=
    hKF p hp hp2 J hJsimple hJnonabSub hJcat P hPne hPcomm
      φ hφpow hφcomm
  let d : Γ := c * ((g0 : J) : Γ)⁻¹
  have hdcenJ : d ∈ Subgroup.centralizer (J : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    let y : J := ⟨((g0 : J) : Γ)⁻¹ * j * ((g0 : J) : Γ), by
      exact J.mul_mem (J.mul_mem (J.inv_mem (g0 : J).2) hj) (g0 : J).2⟩
    have hy : (y : Γ) = ((g0 : J) : Γ)⁻¹ * j * ((g0 : J) : Γ) := rfl
    have hφy : c * (y : Γ) * c⁻¹ =
        ((g0 : J) : Γ) * (y : Γ) * ((g0 : J) : Γ)⁻¹ := by
      have h := congrArg (fun z : J => (z : Γ))
        (congrArg (fun f : MulAut J => f y) hg0eq)
      simpa [φ, MulAut.conjNormal_apply, MulAut.conj_apply] using h
    have hconj : d * j * d⁻¹ = j := by
      calc d * j * d⁻¹ = c * (y : Γ) * c⁻¹ := by
            simp [d, y]
            group
        _ = ((g0 : J) : Γ) * (y : Γ) * ((g0 : J) : Γ)⁻¹ := hφy
        _ = j := by
            simp [y]
            group
    calc j * d = (d * j * d⁻¹) * d := by rw [hconj]
      _ = d * j := by group
  have hdπ : π d ≠ 1 := by
    have hg0ker : π ((g0 : J) : Γ) = 1 :=
      MonoidHom.mem_ker.mp (hJker (g0 : J).2)
    have hπd : π d = π c := by
      simp [d, map_mul, map_inv, hg0ker]
    rwa [hπd]
  have hdord : orderOf d = p := by
    have hg0ker : π ((g0 : J) : Γ) = 1 :=
      MonoidHom.mem_ker.mp (hJker (g0 : J).2)
    have hπd : π d = π c := by
      simp [d, map_mul, map_inv, hg0ker]
    have hπd_ord : orderOf (π d) = p := by
      rw [hπd, hπc_eq, orderOf_pow, hr2ord]
      have hcop : Nat.Coprime p m := (hp.coprime_iff_not_dvd).mpr hm
      rw [Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.div_one]
    have hdp1 : d ^ p = 1 := by
      have hmemH : d ^ p ∈ H := by
        apply hkerH
        rw [MonoidHom.mem_ker, map_pow]
        have h := pow_orderOf_eq_one (π d)
        rwa [hπd_ord] at h
      have hmemC : d ^ p ∈ Subgroup.centralizer (J : Set Γ) :=
        Subgroup.pow_mem _ hdcenJ p
      have hmem : d ^ p ∈ H ⊓ Subgroup.centralizer (J : Set Γ) := ⟨hmemH, hmemC⟩
      rw [hHcentral] at hmem
      simpa using hmem
    have hdvd : orderOf d ∣ p := orderOf_dvd_of_pow_eq_one hdp1
    have hdne : d ≠ 1 := by
      intro h1
      apply hdπ
      rw [h1]
      simp
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      exact hdne h
    · exact h
  have hdH : d ∈ Subgroup.centralizer (H : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hmemH : d * h * d⁻¹ * h⁻¹ ∈ H :=
      H.mul_mem (hH.conj_mem h hh d) (H.inv_mem hh)
    have hmemC : d * h * d⁻¹ * h⁻¹ ∈ Subgroup.centralizer (J : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hdj : d * j * d⁻¹ = j := by
        have hcomm := Subgroup.mem_centralizer_iff.mp hdcenJ j hj
        calc d * j * d⁻¹ = (j * d) * d⁻¹ := by rw [hcomm]
          _ = j := by group
      have hj' : h⁻¹ * j * h ∈ J := by
        simpa using hJnormal.conj_mem j hj h⁻¹
      have hdj' : d * (h⁻¹ * j * h) * d⁻¹ = h⁻¹ * j * h := by
        have hcomm := Subgroup.mem_centralizer_iff.mp hdcenJ (h⁻¹ * j * h) hj'
        calc d * (h⁻¹ * j * h) * d⁻¹ = ((h⁻¹ * j * h) * d) * d⁻¹ := by rw [hcomm]
          _ = h⁻¹ * j * h := by group
      have hdj'' : d⁻¹ * (h⁻¹ * j * h) * d = h⁻¹ * j * h := by
        calc d⁻¹ * (h⁻¹ * j * h) * d
            = d⁻¹ * (d * (h⁻¹ * j * h) * d⁻¹) * d := by rw [hdj']
          _ = h⁻¹ * j * h := by group
      have hconj : (d * h * d⁻¹ * h⁻¹) * j * (d * h * d⁻¹ * h⁻¹)⁻¹ = j := by
        calc (d * h * d⁻¹ * h⁻¹) * j * (d * h * d⁻¹ * h⁻¹)⁻¹
            = d * (h * (d⁻¹ * (h⁻¹ * j * h) * d) * h⁻¹) * d⁻¹ := by group
          _ = d * (h * (h⁻¹ * j * h) * h⁻¹) * d⁻¹ := by rw [hdj'']
          _ = d * j * d⁻¹ := by group
          _ = j := hdj
      calc j * (d * h * d⁻¹ * h⁻¹)
          = ((d * h * d⁻¹ * h⁻¹) * j * (d * h * d⁻¹ * h⁻¹)⁻¹)
              * (d * h * d⁻¹ * h⁻¹) := by rw [hconj]
        _ = (d * h * d⁻¹ * h⁻¹) * j := by group
    have hmem : d * h * d⁻¹ * h⁻¹ ∈ H ⊓ Subgroup.centralizer (J : Set Γ) := ⟨hmemH, hmemC⟩
    rw [hHcentral] at hmem
    have h1 : d * h * d⁻¹ * h⁻¹ = 1 := by simpa using hmem
    have h3 : d * h * d⁻¹ = h := by
      calc d * h * d⁻¹ = (d * h * d⁻¹ * h⁻¹) * h := by group
        _ = 1 * h := by rw [h1]
        _ = h := one_mul _
    have h2 : d * h = h * d := by
      calc d * h = (d * h * d⁻¹) * d := by group
        _ = h * d := by rw [h3]
    exact h2.symm
  exact ⟨d, hdπ, hdord, hdH⟩

theorem exists_orderOf_eq_prime_mem_normalizer_of_pCore_eq_bot
    (hp : p.Prime) (hp2 : p ≠ 2)
    (π : Γ →* DihedralGroup p) (hπ : Function.Surjective π)
    (hcyc : ∀ P : Subgroup Γ, P ≤ π.ker → IsPGroup p P → IsCyclic P)
    (hy : ∃ y : Γ, π y ≠ 1 ∧ orderOf y = p)
    (hK : CFSG.Open.IsKGroup Γ)
    (hKF : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (hOp' : CFSG.Open.relPPrimeCore p π.ker = ⊥)
    {Q : Subgroup Γ} (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q π.ker) (hQne : Q ≠ ⊥)
    (hYbot : CFSG.Open.pCoreOf p π.ker = ⊥) :
    ∃ e : Γ, π e ≠ 1 ∧ orderOf e = p ∧ e ∈ Subgroup.normalizer (Q : Set Γ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup Γ := π.ker
  have hH : H.Normal := MonoidHom.normal_ker π
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hQle : Q ≤ H := hQ.le
    rw [hbot] at hQle
    exact hQne (le_bot_iff.mp hQle)
  obtain ⟨V, hVnorm, hVleH, hVne, hVmin0⟩ := CFSG.exists_minimal_normal_le H hH hHne
  have : V.Normal := hVnorm
  have hVmin : ∀ M : Subgroup Γ, M.Normal → M ≤ V → M = ⊥ ∨ M = V := by
    intro M hM hle
    by_cases hMbot : M = ⊥
    · exact Or.inl hMbot
    · exact Or.inr (hVmin0 M hM hle hMbot)
  have hpV : p ∣ Nat.card V := by
    by_contra hpd
    have hcop : Nat.Coprime p (Nat.card V) := (hp.coprime_iff_not_dvd).mpr hpd
    have hle : V ≤ CFSG.Open.relPPrimeCore p H :=
      le_relPPrimeCore_of_normal_coprime hp hVleH Subgroup.normal_subgroupOf hcop
    rw [hOp'] at hle
    exact hVne (le_bot_iff.mp hle)
  by_cases hVcomm : IsMulCommutative V
  · exact (abelian_minimal_normal_contradiction hH hp hOp' hYbot hVnorm hVleH hVne hVmin
      hVcomm).elim
  have hVnonab : ∃ a b : V, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hVcomm { is_comm := Std.Commutative.mk (fun a b => h a b) }
  obtain ⟨r, S, hr, hSV, hSsimple, hSconj, hSnormV, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hVnorm hVne hVmin
  obtain ⟨hr1, hpS⟩ := minimal_normal_factors_p_dvd_and_unique hp hVnorm hVleH hVne hOp'
    (fun P hPH hPp => hcyc P hPH hPp) hr hSV hSconj e he
  have hrpos : 0 < r := by omega
  let i0 : Fin r := ⟨0, hrpos⟩
  have hVeqS : V = S i0 := by
    apply le_antisymm
    · intro v hv
      let x : (j : Fin r) → ↥(S j) := e.symm ⟨v, hv⟩
      have hx : e x = ⟨v, hv⟩ := e.apply_symm_apply ⟨v, hv⟩
      have hxfun : x = Pi.mulSingle i0 (x i0) := by
        funext j
        have hj : j = i0 := by
          apply Fin.ext
          have h1 := j.isLt
          have h2 := i0.isLt
          simp [i0] at h2 ⊢
          omega
        rw [hj]
        exact (Pi.mulSingle_eq_same (M := fun k => ↥(S k)) i0 (x i0)).symm
      have h := he i0 (Pi.mulSingle i0 (x i0))
        (fun j hj => Pi.mulSingle_eq_of_ne (M := fun k => ↥(S k)) hj (x i0))
      rw [← hxfun, hx] at h
      have h' : v = (x i0 : Γ) := h
      rw [h']
      exact (x i0).2
    · intro v hv
      exact hSV i0 hv
  have hVsimple : IsSimpleGroup V := hVeqS.symm ▸ hSsimple i0
  have hpV' : p ∣ Nat.card V := by
    rw [hVeqS]
    exact hpS i0
  have hnonabV : ∃ a ∈ V, ∃ b ∈ V, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hVnonab
    exact ⟨(a : Γ), a.2, (b : Γ), b.2, fun h => hab (Subtype.ext h)⟩
  have hCHV : H ⊓ Subgroup.centralizer (V : Set Γ) = ⊥ :=
    centralizer_eq_bot_of_minimal_normal_nonabelian hp hp2
      (fun P hPH hPp => hcyc P hPH hPp) hVnorm hVleH hVne hVsimple hnonabV hpV' hOp'

  obtain ⟨d, hdπ, hdord, hdH⟩ :=
    exists_orderOf_eq_prime_mem_normalizer_of_kfact hp hp2 hH hVleH hVnorm hVsimple
      hnonabV hpV' hcyc hK hKF hCHV π hπ hVleH le_rfl
  refine ⟨d, hdπ, hdord, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hxH : x ∈ H := hQ.le hx
    have hcomm : x * d = d * x := Subgroup.mem_centralizer_iff.mp hdH x hxH
    have hx' : d * x * d⁻¹ = x := by
      calc d * x * d⁻¹ = x * d * d⁻¹ := by rw [hcomm]
        _ = x := by group
    rwa [hx']
  · intro hx
    have hxH : x ∈ H := by
      have hyH : d * x * d⁻¹ ∈ H := hQ.le hx
      have := hH.conj_mem (d * x * d⁻¹) hyH d⁻¹
      simpa [mul_assoc] using this
    have hcomm : x * d = d * x := Subgroup.mem_centralizer_iff.mp hdH x hxH
    have hx' : d * x * d⁻¹ = x := by
      calc d * x * d⁻¹ = x * d * d⁻¹ := by rw [hcomm]
        _ = x := by group
    rwa [hx'] at hx

theorem exists_orderOf_eq_prime_mem_normalizer_of_dihedral_core
    (hp : p.Prime) (hp2 : p ≠ 2)
    (π : Γ →* DihedralGroup p) (hπ : Function.Surjective π)
    (hcyc : ∀ P : Subgroup Γ, P ≤ π.ker → IsPGroup p P → IsCyclic P)
    (hy : ∃ y : Γ, π y ≠ 1 ∧ orderOf y = p)
    (hK : CFSG.Open.IsKGroup Γ)
    (hKF : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (hOp' : CFSG.Open.relPPrimeCore p π.ker = ⊥)
    {Q : Subgroup Γ} (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q π.ker) :
    ∃ e : Γ, π e ≠ 1 ∧ orderOf e = p ∧
      e ∈ Subgroup.normalizer (Q : Set Γ) := by
  classical
  by_cases hQbot : Q = ⊥
  · obtain ⟨y, hyπ, hyord⟩ := hy
    refine ⟨y, hyπ, hyord, ?_⟩
    rw [hQbot]
    have htop : Subgroup.normalizer ((⊥ : Subgroup Γ) : Set Γ) = ⊤ :=
      Subgroup.normalizer_eq_top (H := (⊥ : Subgroup Γ))
    exact htop ▸ Subgroup.mem_top y
  · have hHne : π.ker ≠ ⊥ := by
      intro h
      exact hQbot (le_bot_iff.mp (hQ.le.trans h.le))
    by_cases hYbot : CFSG.Open.pCoreOf p π.ker = ⊥
    · exact exists_orderOf_eq_prime_mem_normalizer_of_pCore_eq_bot
        hp hp2 π hπ hcyc hy hK hKF hOp' hQ hQbot hYbot
    · exact exists_orderOf_eq_prime_mem_normalizer_of_pCore_ne_bot
        hp hp2 π hπ hcyc hK hOp' hQ hQbot hYbot

theorem exists_orderOf_eq_prime_mem_normalizer_of_dihedral
    {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (π : Γ →* DihedralGroup p) (hπ : Function.Surjective π)
    (hcyc : ∀ P : Subgroup Γ, P ≤ π.ker → IsPGroup p P → IsCyclic P)
    (hy : ∃ y : Γ, π y ≠ 1 ∧ orderOf y = p)
    (hK : CFSG.Open.IsKGroup Γ)
    (hKF : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    {Q : Subgroup Γ} (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q π.ker) :
    ∃ e : Γ, π e ≠ 1 ∧ orderOf e = p ∧ e ∈ Subgroup.normalizer (Q : Set Γ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let H : Subgroup Γ := π.ker
  let U : Subgroup Γ := CFSG.Open.relPPrimeCore p H
  have hUH : U ≤ H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le H
  have hUeq : U = CFSG.Open.relPPrimeCore p H := rfl
  have hUnormal : U.Normal := by
    change (CFSG.Open.relPPrimeCore p H).Normal
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      hp H]
    have : H.Normal := MonoidHom.normal_ker π
    exact ConjAct.normal_of_characteristic_of_normal
      (H := H) (K := CFSG.pPrimeCore p H)
  have hpU : Nat.Coprime p (Nat.card U) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      hp H
  let q : Γ →* Γ ⧸ U := QuotientGroup.mk' U
  let πbar : Γ ⧸ U →* DihedralGroup p :=
    QuotientGroup.lift U π (by
      change U ≤ π.ker
      exact hUH)
  have hπbar : Function.Surjective πbar := by
    exact QuotientGroup.lift_surjective_of_surjective U π hπ (by
      change U ≤ π.ker
      exact hUH)
  have hker : πbar.ker = H.map q := by
    rw [show πbar = QuotientGroup.lift U π (by
      change U ≤ π.ker
      exact hUH) from rfl, QuotientGroup.ker_lift]
  have hOpbar : CFSG.Open.relPPrimeCore p πbar.ker = ⊥ := by
    rw [hker]
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      hp (H.map q)]
    rw [pPrimeCore_quotient_image_eq_bot hp hUH hUeq]
    exact Subgroup.map_bot (Subgroup.subtype (H.map q))
  have hcycbar : ∀ P : Subgroup (Γ ⧸ U), P ≤ πbar.ker → IsPGroup p P → IsCyclic P := by
    intro P hP hPp
    exact CFSG.AGLEmbedding.isCyclic_of_le_map q hcyc
      (by rwa [hker] at hP) hPp
  obtain ⟨y, hyπ, hyord⟩ := hy
  let ybar : Γ ⧸ U := q y
  have hybarπ : πbar ybar ≠ 1 := by
    change π y ≠ 1
    simpa [ybar, πbar] using hyπ
  have hybarord : orderOf ybar = p := by
    have hdvd : orderOf ybar ∣ p := by
      rw [orderOf_dvd_iff_pow_eq_one]
      have : ybar ^ p = 1 := by
        rw [show ybar ^ p = q (y ^ p) by rw [map_pow]]
        rw [← hyord, pow_orderOf_eq_one, map_one]
      exact this
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exfalso
      have hybar1 : ybar = 1 := orderOf_eq_one_iff.mp h
      exact hybarπ (by rw [hybar1]; exact map_one πbar)
    · exact h
  have hybarH : ybar ∉ H.map q := by
    intro h
    apply hybarπ
    change πbar ybar = 1
    rw [show πbar ybar = 1 ↔ ybar ∈ πbar.ker from MonoidHom.mem_ker.symm]
    rwa [hker]
  have hQbar : CFSG.ABGLocalTools.IsSylowOf 2 (Q.map q) πbar.ker := by
    obtain ⟨QH, hQH⟩ := hQ
    have hQleH : Q ≤ H := by
      rw [← hQH]
      exact Subgroup.map_subtype_le (QH : Subgroup H)
    let qH : H →* H.map q :=
      (q.comp H.subtype).codRestrict (H.map q) fun x =>
        Subgroup.mem_map_of_mem q x.2
    have hqH : Function.Surjective qH := by
      intro z
      obtain ⟨h, hh, hhz⟩ := Subgroup.mem_map.mp z.2
      exact ⟨⟨h, hh⟩, Subtype.ext hhz⟩
    let QbarH : Sylow 2 (H.map q) := QH.mapSurjective hqH
    have hmap_cod : (QH : Subgroup H).map qH =
        ((QH : Subgroup H).map (q.comp H.subtype)).subgroupOf (H.map q) := by
      ext x
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨h, hh, rfl⟩
      · rintro ⟨h, hh, hx⟩
        exact ⟨h, hh, Subtype.ext hx⟩
    have hQbarH : (QbarH : Subgroup (H.map q)) =
        (Q.map q).subgroupOf (H.map q) := by
      rw [Sylow.coe_mapSurjective hqH QH, hmap_cod]
      rw [← Subgroup.map_map (K := (QH : Subgroup H)) q H.subtype, hQH]
    rw [hker]
    refine ⟨QbarH, ?_⟩
    rw [hQbarH]
    exact Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_mono hQleH)
  obtain ⟨ebar, hebarπ, hebarord, hebarN⟩ :=
    exists_orderOf_eq_prime_mem_normalizer_of_dihedral_core
      hp hp2 πbar hπbar hcycbar ⟨ybar, hybarπ, hybarord⟩
      (hK.quotient U) hKF hOpbar hQbar
  have hebarH : ebar ∉ H.map q := by
    intro h
    apply hebarπ
    change πbar ebar = 1
    rw [show πbar ebar = 1 ↔ ebar ∈ πbar.ker from MonoidHom.mem_ker.symm]
    rwa [hker]
  obtain ⟨b, hbH, hbord, R, hRsyl, hbR⟩ :=
    exists_orderOf_eq_prime_mem_normalizer_of_pPrimeCore_quotient
      hp hp2 hUH hpU hQ hebarord hebarH hebarN
  obtain ⟨k, hkH, hk⟩ := hRsyl.exists_mem_conj hQ
  let c : Γ := MulAut.conj k b
  have hRmap : (R : Subgroup Γ).map (MulAut.conj k).toMonoidHom = Q := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : k⁻¹ * (k * r * k⁻¹) * k ∈ R := by
        rwa [show k⁻¹ * (k * r * k⁻¹) * k = r by group]
      exact (hk (k * r * k⁻¹)).mpr hr'
    · intro hx
      have hxR : k⁻¹ * x * k ∈ R := (hk x).mp hx
      refine ⟨k⁻¹ * x * k, hxR, ?_⟩
      change k * (k⁻¹ * x * k) * k⁻¹ = x
      group
  have hcN : c ∈ Subgroup.normalizer (Q : Set Γ) := by
    have hmem : c ∈ (Subgroup.normalizer (R : Set Γ)).map
        (MulAut.conj k).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨b, hbR, rfl⟩
    rw [Subgroup.map_equiv_normalizer_eq R (MulAut.conj k), hRmap] at hmem
    exact hmem
  have hcH : c ∉ H := by
    intro hcH
    apply hbH
    have : b = k⁻¹ * c * k := by
      simp only [c, MulAut.conj_apply]
      group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hkH) hcH) hkH
  have hcπ : π c ≠ 1 := by
    have hk1 : π k = 1 := MonoidHom.mem_ker.mp hkH
    have hbπ : π b ≠ 1 := fun h => hbH (MonoidHom.mem_ker.mpr h)
    have hceq : π c = π b := by
      simp [c, MulAut.conj_apply, hk1]
    intro h
    exact hbπ (by rwa [hceq] at h)
  refine ⟨c, hcπ, ?_, hcN⟩
  rw [show c = MulAut.conj k b from rfl, MulEquiv.orderOf_eq, hbord]

end CFSG.GroupTheory
