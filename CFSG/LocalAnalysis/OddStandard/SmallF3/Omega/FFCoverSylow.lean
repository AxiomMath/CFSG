module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G H : Type} [Group G] [Group H] {L : Subgroup G}

private theorem ff_key {φ : ↥L →* H} (hφ : OddCentralCover φ) {a : ℕ} {x z : ↥L}
    (hz : z ∈ φ.ker) (hx : x ^ 2 ^ a = 1) (hxz : (x * z) ^ 2 ^ a = 1) : z = 1 := by
  have hc : z ∈ Subgroup.center ↥L := hφ.ker_le_center hz
  have hcomm : Commute x z := Subgroup.mem_center_iff.mp hc x
  have hz2 : z ^ 2 ^ a = 1 := by
    have h1 : (x * z) ^ 2 ^ a = x ^ 2 ^ a * z ^ 2 ^ a := hcomm.mul_pow _
    rw [h1, hx, one_mul] at hxz
    exact hxz
  have hdvd : orderOf z ∣ 2 ^ a := orderOf_dvd_iff_pow_eq_one.mpr hz2
  have hk : orderOf z ∣ Nat.card φ.ker := Subgroup.orderOf_dvd_natCard φ.ker hz
  have hcop : Nat.Coprime (2 ^ a) (Nat.card φ.ker) :=
    (Nat.coprime_two_left.mpr hφ.odd_card_ker).pow_left a
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd hk)

private theorem ff_twoPow_of_mem {B : Subgroup G} (hB : IsPGroup 2 B) {x : ↥L}
    (hx : (x : G) ∈ B) : ∃ a, x ^ 2 ^ a = 1 := by
  obtain ⟨k, hk⟩ := hB ⟨(x : G), hx⟩
  exact ⟨k, Subtype.ext (by simpa using congrArg (Subtype.val) hk)⟩

private theorem ff_twoPow_conj_of_mem {B : Subgroup G} (hB : IsPGroup 2 B) (x : ↥L)
    {y : ↥L} (hy : (y : G) ∈ B) : ∃ a, (x * y * x⁻¹) ^ 2 ^ a = 1 := by
  obtain ⟨k, hk⟩ := ff_twoPow_of_mem hB hy
  exact ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩

private theorem ff_key_order {φ : ↥L →* H} (hφ : OddCentralCover φ) {x y : ↥L}
    (hz : x⁻¹ * y ∈ φ.ker) (hx : ∃ a, x ^ 2 ^ a = 1) (hy : ∃ a, y ^ 2 ^ a = 1) : x = y := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have ha' : x ^ 2 ^ max a b = 1 := by
    obtain ⟨m, hm⟩ := pow_dvd_pow 2 (le_max_left a b)
    rw [hm, pow_mul, ha, one_pow]
  have hb' : y ^ 2 ^ max a b = 1 := by
    obtain ⟨m, hm⟩ := pow_dvd_pow 2 (le_max_right a b)
    rw [hm, pow_mul, hb, one_pow]
  have hz1 : x⁻¹ * y = 1 := by
    apply ff_key hφ hz ha'
    show (x * (x⁻¹ * y)) ^ 2 ^ max a b = 1
    rw [mul_inv_cancel_left]
    exact hb'
  rwa [inv_mul_eq_one] at hz1

@[expose] def ffImg (φ : ↥L →* H) (B : Subgroup G) : Subgroup H :=
  (B.subgroupOf L).map φ

theorem mem_ffImg_iff {φ : ↥L →* H} {B : Subgroup G} {h : H} :
    h ∈ ffImg φ B ↔ ∃ l : ↥L, (l : G) ∈ B ∧ φ l = h := by
  unfold ffImg
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Subgroup.mem_subgroupOf.mp hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩

theorem ffImg_mono {φ : ↥L →* H} {B B' : Subgroup G} (h : B ≤ B') : ffImg φ B ≤ ffImg φ B' := by
  intro x hx
  rw [mem_ffImg_iff] at hx ⊢
  obtain ⟨l, hl, rfl⟩ := hx
  exact ⟨l, h hl, rfl⟩

theorem ff_cover_eq_of_pGroup {φ : ↥L →* H} (hφ : OddCentralCover φ) {B : Subgroup G}
    (hB : IsPGroup 2 B) {l l' : ↥L} (hl : (l : G) ∈ B) (hl' : (l' : G) ∈ B) (h : φ l = φ l') :
    l = l' := by
  have hxker : l⁻¹ * l' ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hxB : ((l⁻¹ * l' : ↥L) : G) ∈ B := by
    show (l : G)⁻¹ * (l' : G) ∈ B
    exact B.mul_mem (B.inv_mem hl) hl'
  obtain ⟨k, hk⟩ := ff_twoPow_of_mem hB hxB
  have hdvd : orderOf (l⁻¹ * l') ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  have hk' : orderOf (l⁻¹ * l') ∣ Nat.card φ.ker := Subgroup.orderOf_dvd_natCard φ.ker hxker
  have hcop : Nat.Coprime (2 ^ k) (Nat.card φ.ker) :=
    (Nat.coprime_two_left.mpr hφ.odd_card_ker).pow_left k
  have h1 : l⁻¹ * l' = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes hcop hdvd hk'
  rwa [inv_mul_eq_one] at h1

@[expose] noncomputable def ffImgEquiv {φ : ↥L →* H} (hφ : OddCentralCover φ) {B : Subgroup G}
    (hBL : B ≤ L) (hB : IsPGroup 2 B) : ↥B ≃* ↥(ffImg φ B) := by
  let f : ↥B →* ↥(ffImg φ B) :=
    MonoidHom.mk'
      (fun b : ↥B => ⟨φ ⟨(b : G), hBL b.2⟩,
        by rw [mem_ffImg_iff]; exact ⟨⟨(b : G), hBL b.2⟩, b.2, rfl⟩⟩)
      (fun a b => by
        apply Subtype.ext
        exact map_mul φ ⟨(a : G), hBL a.2⟩ ⟨(b : G), hBL b.2⟩)
  exact MulEquiv.ofBijective f (by
    refine ⟨?_, ?_⟩
    · intro a b hab
      have hφab : φ ⟨(a : G), hBL a.2⟩ = φ ⟨(b : G), hBL b.2⟩ :=
        congrArg (Subgroup.subtype (ffImg φ B)) hab
      have heq := ff_cover_eq_of_pGroup (B := B) hφ hB
        (l := ⟨(a : G), hBL a.2⟩) (l' := ⟨(b : G), hBL b.2⟩) a.2 b.2 hφab
      have heqG : (a : G) = (b : G) := congrArg (fun x : ↥L => (x : G)) heq
      exact Subtype.ext heqG
    · intro y
      obtain ⟨l, hl, hly⟩ := mem_ffImg_iff.mp y.2
      refine ⟨⟨(l : G), hl⟩, ?_⟩
      apply Subtype.ext
      show φ ⟨(l : G), hBL hl⟩ = (y : H)
      rw [show (⟨(l : G), hBL hl⟩ : ↥L) = l from Subtype.ext rfl, hly])

theorem coe_ffImgEquiv {φ : ↥L →* H} (hφ : OddCentralCover φ) {B : Subgroup G} (hBL : B ≤ L)
    (hB : IsPGroup 2 B) (b : ↥B) :
    ((ffImgEquiv hφ hBL hB b : ↥(ffImg φ B)) : H) = φ ⟨(b : G), hBL b.2⟩ := rfl

theorem ff_cover_isPGroup_img {φ : ↥L →* H} {B : Subgroup G} (hBL : B ≤ L)
    (hB : IsPGroup 2 B) : IsPGroup 2 (ffImg φ B) := by
  unfold ffImg
  exact (hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBL).symm).map φ

theorem ff_cover_elemAb2_iff {φ : ↥L →* H} (hφ : OddCentralCover φ) {B : Subgroup G}
    (hBL : B ≤ L) (hB : IsPGroup 2 B) (k : ℕ) : IsElemAb2 B k ↔ IsElemAb2 (ffImg φ B) k := by
  unfold IsElemAb2 CFSG.Open.IsElemAbelian
  constructor
  · rintro ⟨⟨hcomm, hpow⟩, hcard⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · haveI : IsMulCommutative ↥B := hcomm
      exact Subgroup.map_isMulCommutative (H := B.subgroupOf L) φ
    · intro y hy
      obtain ⟨b, hb⟩ := (ffImgEquiv hφ hBL hB).surjective ⟨y, hy⟩
      have hyb : ((ffImgEquiv hφ hBL hB b : ↥(ffImg φ B)) : H) = y :=
        congrArg (Subtype.val) hb
      rw [← hyb]
      have hb2 : b ^ 2 = 1 := by
        apply Subtype.ext
        simpa using hpow (b : G) b.2
      calc ((ffImgEquiv hφ hBL hB b : ↥(ffImg φ B)) : H) ^ 2
          = ((ffImgEquiv hφ hBL hB b ^ 2 : ↥(ffImg φ B)) : H) := rfl
        _ = ((ffImgEquiv hφ hBL hB (b ^ 2) : ↥(ffImg φ B)) : H) := by rw [map_pow]
        _ = ((ffImgEquiv hφ hBL hB 1 : ↥(ffImg φ B)) : H) := by rw [hb2]
        _ = 1 := by rw [map_one, Subgroup.coe_one]
    · exact (Nat.card_congr (ffImgEquiv hφ hBL hB).toEquiv).symm.trans hcard
  · rintro ⟨⟨hcomm, hpow⟩, hcard⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hsurj : Function.Surjective (ffImgEquiv hφ hBL hB).symm.toMonoidHom :=
        (ffImgEquiv hφ hBL hB).symm.surjective
      exact Function.Surjective.isMulCommutative hsurj hcomm
    · intro x hx
      have hxφ : φ ⟨x, hBL hx⟩ ∈ ffImg φ B := by
        rw [mem_ffImg_iff]; exact ⟨⟨x, hBL hx⟩, hx, rfl⟩
      have hx2φ : (φ ⟨x, hBL hx⟩) ^ 2 = 1 := hpow _ hxφ
      have hxl : (⟨x, hBL hx⟩ : ↥L) ^ 2 = 1 := by
        apply ff_cover_eq_of_pGroup hφ hB
        · have : ((⟨x, hBL hx⟩ : ↥L) : G) ^ 2 ∈ B := by
            rw [pow_two]
            exact B.mul_mem hx hx
          simpa using this
        · exact B.one_mem
        · rw [map_pow, map_one]
          exact hx2φ
      simpa using congrArg (Subtype.val) hxl
    · exact (Nat.card_congr (ffImgEquiv hφ hBL hB).toEquiv).trans hcard

theorem ff_cover_isSylow2Of [Finite G] {φ : ↥L →* H} (hφ : OddCentralCover φ) {P : Subgroup G}
    (hP : IsSylow2Of P L) : IsSylow2Of (ffImg φ P) (⊤ : Subgroup H) := by
  refine ⟨le_top, ff_cover_isPGroup_img hP.1 hP.2.1, ?_⟩
  rw [Subgroup.relIndex_top_right]
  intro h2
  have hdvd : (ffImg φ P).index ∣ P.relIndex L := by
    unfold ffImg
    exact Subgroup.index_map_dvd (P.subgroupOf L) hφ.surjective
  exact hP.2.2 (dvd_trans h2 hdvd)

theorem ff_cover_img_injective {φ : ↥L →* H} (hφ : OddCentralCover φ) {P : Subgroup G}
    (hPL : P ≤ L) (hP : IsPGroup 2 P) {B₁ B₂ : Subgroup G} (h₁ : B₁ ≤ P) (h₂ : B₂ ≤ P)
    (h : ffImg φ B₁ = ffImg φ B₂) : B₁ = B₂ := by
  have key : ∀ {B B' : Subgroup G}, B ≤ P → B' ≤ P → ffImg φ B = ffImg φ B' → B ≤ B' := by
    intro B B' hB hB' heq x hx
    have hxL : x ∈ L := hPL (hB hx)
    have hmem : φ ⟨x, hxL⟩ ∈ ffImg φ B := by
      rw [mem_ffImg_iff]; exact ⟨⟨x, hxL⟩, hx, rfl⟩
    rw [heq] at hmem
    obtain ⟨l, hlB', hlφ⟩ := mem_ffImg_iff.mp hmem
    have heq' : (⟨x, hxL⟩ : ↥L) = l :=
      ff_cover_eq_of_pGroup (B := P) hφ hP (l := ⟨x, hxL⟩) (l' := l)
        (hB hx) (hB' hlB') hlφ.symm
    rw [show x = (l : G) from congrArg (Subtype.val) heq']
    exact hlB'
  exact le_antisymm (key h₁ h₂ h) (key h₂ h₁ h.symm)

theorem ff_cover_exists_of_le_img {φ : ↥L →* H} (hφ : OddCentralCover φ) {P : Subgroup G}
    (hPL : P ≤ L) (hP : IsPGroup 2 P) {B' : Subgroup H} (h : B' ≤ ffImg φ P) :
    ∃ B : Subgroup G, B ≤ P ∧ ffImg φ B = B' := by
  refine ⟨((B'.comap φ) ⊓ (P.subgroupOf L)).map L.subtype, ?_, ?_⟩
  · rintro x ⟨l, hl, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hl.2
  · apply le_antisymm
    · intro y hy
      obtain ⟨l', hl'B, rfl⟩ := mem_ffImg_iff.mp hy
      rw [Subgroup.mem_map] at hl'B
      obtain ⟨l, hl, hl_eq⟩ := hl'B
      have hll' : l = l' := Subtype.ext hl_eq
      rw [← hll']
      exact Subgroup.mem_comap.mp hl.1
    · intro y hy
      rw [mem_ffImg_iff]
      obtain ⟨l, hlP, hlφ⟩ := mem_ffImg_iff.mp (h hy)
      refine ⟨l, ?_, hlφ⟩
      rw [Subgroup.mem_map]
      exact ⟨l, ⟨Subgroup.mem_comap.mpr (hlφ.symm ▸ hy), Subgroup.mem_subgroupOf.mpr hlP⟩, rfl⟩

private theorem ff_cover_conj_mem_of_mem_normalizer {φ : ↥L →* H} (hφ : OddCentralCover φ)
    {B : Subgroup G} (hB : IsPGroup 2 B) (l : ↥L)
    (hl : φ l ∈ Subgroup.normalizer (ffImg φ B : Set H)) {b : ↥L} (hb : (b : G) ∈ B) :
    ((l * b * l⁻¹ : ↥L) : G) ∈ B := by
  have hbl : φ b ∈ ffImg φ B := by rw [mem_ffImg_iff]; exact ⟨b, hb, rfl⟩
  have hconj : φ (l * b * l⁻¹) ∈ ffImg φ B := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hl (φ b)).mp hbl
  obtain ⟨b', hb'B, hb'φ⟩ := mem_ffImg_iff.mp hconj
  have hz : b'⁻¹ * (l * b * l⁻¹) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hb'φ, inv_mul_cancel]
  have heq : b' = l * b * l⁻¹ :=
    ff_key_order hφ hz (ff_twoPow_of_mem hB hb'B) (ff_twoPow_conj_of_mem hB l hb)
  rw [← heq]
  exact hb'B

theorem ff_cover_mem_normalizer_iff {φ : ↥L →* H} (hφ : OddCentralCover φ) {B : Subgroup G}
    (hBL : B ≤ L) (hB : IsPGroup 2 B) (l : ↥L) :
    (l : G) ∈ Subgroup.normalizer (B : Set G) ↔
      φ l ∈ Subgroup.normalizer (ffImg φ B : Set H) := by
  constructor
  · intro hl
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨b, hb, rfl⟩ := mem_ffImg_iff.mp hh
      have hmap : φ (l * b * l⁻¹) = φ l * φ b * (φ l)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [← hmap]
      rw [mem_ffImg_iff]
      exact ⟨l * b * l⁻¹,
        (Subgroup.mem_normalizer_iff.mp hl (b : G)).mp hb, rfl⟩
    · intro hh
      obtain ⟨b', hb'B, hb'φ⟩ := mem_ffImg_iff.mp hh
      rw [mem_ffImg_iff]
      refine ⟨l⁻¹ * b' * l, ?_, ?_⟩
      · have hb'l : (l : G)⁻¹ * (b' : G) * (l : G) ∈ B := by
          simpa using (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (B : Set G)).inv_mem hl) (b' : G)).mp hb'B
        simpa using hb'l
      · rw [map_mul, map_mul, map_inv, hb'φ]
        group
  · intro hl
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      exact ff_cover_conj_mem_of_mem_normalizer hφ hB l hl (b := ⟨b, hBL hb⟩) hb
    · intro hb
      have hl' : φ l⁻¹ ∈ Subgroup.normalizer (ffImg φ B : Set H) := by
        rw [map_inv]
        exact (Subgroup.normalizer (ffImg φ B : Set H)).inv_mem hl
      have hz := ff_cover_conj_mem_of_mem_normalizer hφ hB l⁻¹ hl'
        (b := ⟨(l : G) * b * (l : G)⁻¹, hBL hb⟩) hb
      have hz' : ((l⁻¹ * ⟨(l : G) * b * (l : G)⁻¹, hBL hb⟩ * (l⁻¹)⁻¹ : ↥L) : G) = b := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hz'] at hz
      exact hz

theorem ff_cover_normalE16_iff {φ : ↥L →* H} (hφ : OddCentralCover φ) {P B : Subgroup G}
    (hPL : P ≤ L) (hP : IsPGroup 2 P) (hBP : B ≤ P) :
    IsNormalE16In P B ↔ IsNormalE16In (ffImg φ P) (ffImg φ B) := by
  have hBL : B ≤ L := le_trans hBP hPL
  have hB : IsPGroup 2 B := hP.to_le hBP
  unfold IsNormalE16In
  constructor
  · rintro ⟨_, hE, hN⟩
    refine ⟨ffImg_mono hBP, (ff_cover_elemAb2_iff hφ hBL hB 4).mp hE, ?_⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (ffImg_mono hBP)]
    have hPnorm : P ≤ Subgroup.normalizer (B : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mp hN
    have h2 : (P.subgroupOf L).map φ ≤
        ((Subgroup.normalizer (B : Set G)).subgroupOf L).map φ :=
      Subgroup.map_mono (Subgroup.comap_mono hPnorm)
    rw [Subgroup.subgroupOf_normalizer_eq hBL] at h2
    exact h2.trans (Subgroup.le_normalizer_map φ)
  · rintro ⟨hB'le, hE, hN⟩
    refine ⟨hBP, (ff_cover_elemAb2_iff hφ hBL hB 4).mpr hE, ?_⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBP]
    have hNnorm : ffImg φ P ≤ Subgroup.normalizer (ffImg φ B : Set H) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hB'le).mp hN
    intro p hp
    exact (ff_cover_mem_normalizer_iff hφ hBL hB ⟨p, hPL hp⟩).mpr
      (hNnorm (by rw [mem_ffImg_iff]; exact ⟨⟨p, hPL hp⟩, hp, rfl⟩))

theorem ff_cover_commute_iff {φ : ↥L →* H} (hφ : OddCentralCover φ) {B : Subgroup G}
    (hBL : B ≤ L) (hB : IsPGroup 2 B) (l : ↥L) :
    (∀ b ∈ B, (l : G) * b = b * (l : G)) ↔ ∀ b' ∈ ffImg φ B, φ l * b' = b' * φ l := by
  constructor
  · intro hcomm b' hb'
    obtain ⟨b, hb, rfl⟩ := mem_ffImg_iff.mp hb'
    have hlb : l * b = b * l := Subtype.ext (hcomm b hb)
    rw [← map_mul, ← map_mul, hlb]
  · intro hcomm b hb
    let bl : ↥L := ⟨b, hBL hb⟩
    have hbl : φ bl ∈ ffImg φ B := by rw [mem_ffImg_iff]; exact ⟨bl, hb, rfl⟩
    have h' : φ l * φ bl = φ bl * φ l := hcomm (φ bl) hbl
    have hconj : φ (l * bl * l⁻¹) = φ bl := by
      rw [map_mul, map_mul, map_inv]
      rw [h']
      group
    have hz : bl⁻¹ * (l * bl * l⁻¹) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hconj, inv_mul_cancel]
    have heq : bl = l * bl * l⁻¹ :=
      ff_key_order hφ hz (ff_twoPow_of_mem hB hb) (ff_twoPow_conj_of_mem hB l hb)
    have h : bl * l = l * bl := by
      nth_rewrite 1 [heq]
      group
    have hlr : l * bl = bl * l := h.symm
    simpa using congrArg (Subtype.val) hlr

end CFSG.OddStandard.SmallF3.Omega
