module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3BRBar
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step14
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint
open scoped Pointwise

namespace Sec3

section Generic

variable {H G' : Type} [Group H] [Group G']

theorem map_rightConjugate (f : H →* G') (X : Subgroup H) (k : H) :
    (rightConjugate X k).map f = rightConjugate (X.map f) (f k) := by
  unfold rightConjugate
  rw [map_map, map_map]
  congr 1
  ext y
  simp

variable [Finite H] {N : Subgroup H} [N.Normal]
  (hNc : N ≤ center H) (hNo : Odd (Nat.card N))
include hNc hNo

theorem le_centralizer_of_map {X Y : Subgroup H} (hX : IsPGroup 2 X) (hY : IsPGroup 2 Y)
    (h : X.map (QuotientGroup.mk' N) ≤
      centralizer ((Y.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N))) :
    X ≤ centralizer (Y : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N
  have hW : IsPGroup 2 ↥(X.map π ⊔ Y.map π) :=
    (hX.map π).to_sup_of_normal_right' (hY.map π)
      (h.trans (centralizer_le_normalizer _))
  have hXW : X ≤ twoLift N (X.map π ⊔ Y.map π) := le_twoLift hX (le_sup_left)
  have hYW : Y ≤ twoLift N (X.map π ⊔ Y.map π) := le_twoLift hY (le_sup_right)
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  apply injOn_twoLift hNc hNo hW (mul_mem (hYW hb) (hXW ha)) (mul_mem (hXW ha) (hYW hb))
  rw [map_mul, map_mul]
  exact mem_centralizer_iff.mp (h ⟨a, ha, rfl⟩) (π b) ⟨b, hb, rfl⟩

theorem isSylowOf_twoLift_comap {W M : Subgroup (H ⧸ N)} (hWM : IsSylowOf 2 W M) :
    IsSylowOf 2 (twoLift N W) (M.comap (QuotientGroup.mk' N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N
  have hW := hWM.isPGroup
  have hle : twoLift N W ≤ M.comap π :=
    (isSylowOf_twoLift hNc hNo hW).le.trans (comap_mono hWM.le)
  obtain ⟨S, hS⟩ := ((isPGroup_twoLift hNc hNo hW).comap_subtype :
    IsPGroup 2 ((twoLift N W).subgroupOf (M.comap π))).exists_le_sylow
  have hS' : IsSylowOf 2 ((S : Subgroup ↥(M.comap π)).map (M.comap π).subtype) (M.comap π) :=
    ⟨S, rfl⟩
  have hle' : twoLift N W ≤ (S : Subgroup ↥(M.comap π)).map (M.comap π).subtype :=
    fun a ha => ⟨⟨a, hle ha⟩, hS ha, rfl⟩
  have hmapS : ((S : Subgroup ↥(M.comap π)).map (M.comap π).subtype).map π = W := by
    refine (hWM.eq_of_le ?_ ?_ (hS'.isPGroup.map π)).symm.symm
    · rw [← map_twoLift hNc hNo hW]
      exact map_mono hle'
    · rintro _ ⟨a, ha, rfl⟩
      exact hS'.le ha
  have heq : (S : Subgroup ↥(M.comap π)).map (M.comap π).subtype = twoLift N W :=
    le_antisymm (le_twoLift hS'.isPGroup hmapS.le) hle'
  rw [← heq]
  exact hS'

end Generic

theorem isElemAbelian_map {H G' : Type} [Group H] [Group G'] (f : H →* G') {X : Subgroup H}
    (hX : IsElemAbelian 2 X) : IsElemAbelian 2 (X.map f) := CFSG.SectionRank.isElemAbelian_map hX _

section Center

variable {H : Type} [Group H] [Finite H]

theorem exists_centerIn_eq_zpowers {T Z : Subgroup H} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hZ2 : (Subgroup.upperCentralSeries ↥T 2).map T.subtype = Z) (hne : centerIn T ≠ Z)
    (hZ4 : Nat.card Z = 4) :
    ∃ z : H, centerIn T = zpowers z ∧ orderOf z = 2 ∧ z ∈ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : centerIn T ≤ Z := by
    rw [← map_center_eq_centerIn, ← hZ2, ← Subgroup.upperCentralSeries_one]
    exact map_mono (Subgroup.upperCentralSeries_mono _ (by norm_num))
  have hnt : Nontrivial ↥T := by
    rw [nontrivial_iff_ne_bot]
    exact hT1
  have hc := hT.center_nontrivial
  have hcard : Nat.card (centerIn T) = 2 := by
    have hd : Nat.card (centerIn T) ∣ 4 := hZ4 ▸ Subgroup.card_dvd_of_le hle
    have h1 : Nat.card (centerIn T) ≠ 1 := by
      rw [card_centerIn]
      exact (Finite.one_lt_card_iff_nontrivial.mpr hc).ne'
    have h4 : Nat.card (centerIn T) ≠ 4 := fun h =>
      hne (eq_of_le_of_card_ge hle (by rw [h, hZ4]))
    have : Nat.card (centerIn T) ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have : IsCyclic ↥(centerIn T) := isCyclic_of_prime_card hcard
  obtain ⟨⟨z, hz⟩, hzgen⟩ := IsCyclic.exists_generator (α := ↥(centerIn T))
  refine ⟨z, ?_, ?_, hle hz⟩
  · refine (eq_of_le_of_card_ge (zpowers_le.mpr hz) ?_).symm
    rw [Nat.card_zpowers, hcard, ← Subgroup.orderOf_mk z hz, orderOf_eq_card_of_forall_mem_zpowers
      hzgen, hcard]
  · rw [← Subgroup.orderOf_mk z hz, orderOf_eq_card_of_forall_mem_zpowers hzgen, hcard]

theorem centerIn_eq_of_normal {T Q : Subgroup H} {z : H} (hT : IsPGroup 2 T)
    (hQT : Q ≤ T) (hTQ : T ≤ normalizer (Q : Set H)) (hQ : CFSG.IsExtraspecialPGroup 2 Q)
    (hz : centerIn T = zpowers z) (hz2 : orderOf z = 2) : centerIn Q = zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hQn : (Q.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hQT).mpr hTQ
  have hQ1 : Q.subgroupOf T ≠ ⊥ := by
    intro h
    have hc : Nat.card (centerIn Q) = 2 := by rw [card_centerIn]; exact hQ.2.2.2
    have hQb : Q = ⊥ := by
      rw [eq_bot_iff]
      intro q hq
      have : (⟨q, hQT hq⟩ : ↥T) ∈ Q.subgroupOf T := hq
      rw [h, mem_bot] at this
      exact congrArg Subtype.val this
    rw [hQb] at hc
    have : Nat.card (centerIn (⊥ : Subgroup H)) ≤ 1 := by
      rw [← Subgroup.card_bot (G := H)]
      exact Subgroup.card_le_of_le inf_le_left
    omega
  have hm := Group.IsNilpotent.inf_center_ne_bot_of_normal hQ1
  obtain ⟨⟨⟨w, hwT⟩, hwQ, hwc⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hm
  have hwZ : w ∈ centerIn T := by
    rw [← map_center_eq_centerIn]
    exact ⟨⟨w, hwT⟩, hwc, rfl⟩
  rw [hz] at hwZ
  have hwz : w = z := eq_of_mem_zpowers hz2 hwZ (fun h => hw1 (Subtype.ext (Subtype.ext h)))
  have hzQ : z ∈ Q := hwz ▸ hwQ
  refine centerIn_eq_zpowers hQ ⟨hzQ, mem_centralizer_iff.mpr fun q hq => ?_⟩ ?_
  · have hzc : z ∈ centerIn T := by rw [hz]; exact mem_zpowers z
    exact (mem_centralizer_iff.mp hzc.2 q (hQT hq))
  · intro h1
    rw [h1, orderOf_one] at hz2
    omega

end Center


theorem isElemAbelian_subgroupOf' {H : Type} [Group H] {V X : Subgroup H}
    (hV : IsElemAbelian 2 V) : IsElemAbelian 2 (V.subgroupOf X) :=
  CFSG.Open.IsElemAbelian.subgroupOf hV X

theorem isPGroup_sec2P {H : Type} [Group H] [Finite H] (E : Subgroup H) : IsPGroup 2 (sec2P E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.pCore_isPGroup.map _

theorem sec2P_le_normalizer {H : Type} [Group H] (E : Subgroup H) :
    sec2P E ≤ normalizer (E : Set H) :=
  ABGTheoremB.pCoreIn_le 2 _

theorem normalizer_le_normalizer_sec2P {H : Type} [Group H] (E : Subgroup H) :
    normalizer (E : Set H) ≤ normalizer (sec2P E : Set H) := by
  have := CFSG.pCore_normal (p := 2) (G := ↥(normalizer (E : Set H)))
  exact ABGTheoremB.le_normalizer_map_subtype _ _

theorem exists_sec2P_mem_rightConjugate
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h21 : Step21) {H : Type} [Group H]
    [Finite H] {A R : Subgroup H} {g : H} {E F : Subgroup H} (hS2 : Sec2Setting H A R g E F)
    {e : H} (he : e ∈ E) (heA : e ∉ A) : ∃ a ∈ sec2P E, e ∈ rightConjugate R a := by
  obtain ⟨hcover, -, -, P₀, -, hP₀N, -, -, -, -, hP₀t, -⟩ :=
    step15_of_frame h11 hE16 hS2.frame hS2.type hS2.odd
  obtain ⟨Q, hQ, heQ⟩ := hcover e he heA
  obtain ⟨n, hn, rfl⟩ := hP₀t Q hQ
  obtain ⟨-, -, hOP, -, -, hNS, hNeq, -⟩ := h21 _ _ _ _ _ _ hS2
  set O := AS76b.oddCoreIn (centralizer (E : Set H)) with hO
  have hnN : n⁻¹ ∈ normalizer (E : Set H) := inv_mem (hP₀N hn)
  have hMN : normalizer (E : Set H) ⊓ normalizer (R : Set H) ≤
      normalizer ((sec2P E ⊔ O : Subgroup H) : Set H) := inf_le_left.trans hNS
  have hnN' : n⁻¹ ∈ ((sec2P E ⊔ O : Subgroup H) : Set H) *
      ((normalizer (E : Set H) ⊓ normalizer (R : Set H) : Subgroup H) : Set H) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hMN, ← hNeq]
    exact hnN
  obtain ⟨s, hs, m, hm, hsm⟩ := hnN'
  have hsm : s * m = n⁻¹ := hsm
  have hON : O ≤ normalizer (sec2P E : Set H) := hOP.trans (centralizer_le_normalizer _)
  have hs' : s⁻¹ ∈ (sec2P E : Set H) * (O : Set H) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hON]
    exact inv_mem hs
  obtain ⟨a, ha, o, ho, hao⟩ := hs'
  have hao : a * o = s⁻¹ := hao
  refine ⟨a, ha, ?_⟩
  have hn' : n = m⁻¹ * (a * o) := by
    rw [hao, ← mul_inv_rev, hsm, inv_inv]
  have hRa : rightConjugate R a ≤ E := by
    intro w hw
    rw [mem_rightConjugate_iff] at hw
    have h1 := (mem_normalizer_iff.mp (inv_mem (sec2P_le_normalizer E ha)) _).mp
      (hS2.frame.R_le_E hw)
    simpa [mul_assoc] using h1
  rw [hn', ← rightConjugate_mul, ← rightConjugate_mul,
    (rightConjugate_eq_self_iff R m⁻¹).mpr (inv_mem hm.2)] at heQ
  rw [mem_rightConjugate_iff] at heQ
  have hoe : o * e * o⁻¹ = e := by
    have h1 := mem_centralizer_iff.mp
      ((AS76b.oddCoreIn_le (centralizer (E : Set H))) ho) e he
    rw [← h1, mul_inv_cancel_right]
  rwa [hoe] at heQ

theorem sec2P_le_centralizer (h211 : Step211) {H : Type} [Group H] [Finite H] {A R : Subgroup H}
    {g : H} {E F : Subgroup H} (hS2 : Sec2Setting H A R g E F) :
    sec2P E ≤ centralizer ((E ⊓ A : Subgroup H) : Set H) := by
  obtain ⟨hPK, -, -, -, -, -, -, ⟨φ, hφs, hφk⟩, -⟩ := h211 _ _ _ _ _ _ hS2
  have hPK' : sec2P E ≤ sec2K E := le_sup_left.trans hPK
  have hKN : sec2K E ≤ normalizer (sec2P E : Set H) := by
    unfold sec2K AS81.oUpperTwo
    exact (closure_le _).mpr fun _ hx => hx.1
  have hP'N : ((sec2P E).subgroupOf (sec2K E)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hPK').mpr hKN
  have hφP : (((sec2P E).subgroupOf (sec2K E)).map φ).Normal := hP'N.map φ hφs
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((sec2P E).subgroupOf (sec2K E)).map φ) with
    h | h
  · intro p hp
    have h1 : (⟨p, hPK' hp⟩ : ↥(sec2K E)) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, ← mem_bot, ← h]
      exact ⟨_, mem_subgroupOf.mpr hp, rfl⟩
    rw [hφk, mem_subgroupOf] at h1
    exact (mem_inf.mp h1).2
  · exfalso
    have h2 : IsPGroup 2 ↥(((sec2P E).subgroupOf (sec2K E)).map φ) :=
      ((isPGroup_sec2P E).comap_subtype).map φ
    rw [h] at h2
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
    have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      have h1 := two_mul_nat_card_alternatingGroup (α := Fin 6)
      have h2 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin]
        rfl
      omega
    rw [Subgroup.card_top, h360] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 360)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at this

theorem mem_normalizer_oUpperTwo {H : Type} [Group H] {X : Subgroup H} {n : H} (hn : n ∈ X) :
    n ∈ normalizer (oUpperTwo X : Set H) := by
  rw [mem_normalizer_iff_map_conj_eq, oUpperTwo, MonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨u, ⟨huX, hu⟩, rfl⟩
    refine ⟨X.mul_mem (X.mul_mem hn huX) (X.inv_mem hn), ?_⟩
    have h := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective u
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    change Odd (orderOf (n * u * n⁻¹))
    rwa [h]
  · rintro ⟨hwX, hw⟩
    refine ⟨n⁻¹ * w * n, ⟨by simpa [mul_assoc] using X.mul_mem (X.mul_mem (X.inv_mem hn) hwX) hn,
      ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
    have h : orderOf (n⁻¹ * w * n) = orderOf w := by
      have h1 := orderOf_injective (MulAut.conj n⁻¹).toMonoidHom (MulAut.conj n⁻¹).injective w
      simpa [MulAut.conj_apply] using h1
    rwa [h]

section Frame

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {x : G}

theorem oddCore_le_A₁ (hS : Sec3Pre G A A₁ R x)
    (hBc : centerIn (sec3B A₁ x) = zpowers x) (hBp : commutator ↥(sec3B A₁ x) = ⊤)
    (hBs : NativeSporadic.IsSporadic (↥(sec3B A₁ x) ⧸ center ↥(sec3B A₁ x)) .Suz) :
    standardComponentOddCore ↥(sec3K A₁ R x) ≤ A₁.subgroupOf (sec3K A₁ R x) := fun k hk =>
  mem_subgroupOf.mpr (zpowers_le.mpr (mem_centerIn_A₁ hS).1
    (oddCore_sec3K_le_zpowers hS hBc hBp hBs ⟨k, hk, rfl⟩))

theorem frame_lift (hS : Sec3Pre G A A₁ R x) {K : Subgroup G} {N : Subgroup ↥K}
    [N.Normal] (hNc : N ≤ center ↥K) (hNo : Odd (Nat.card N)) (hNA : N ≤ A₁.subgroupOf K)
    (hA₁K : A₁ ≤ K) (hRK : R ≤ K) (hKx : K ≤ centralizer ({x} : Set G))
    {gb : ↥K ⧸ N} {Eb Fb : Subgroup (↥K ⧸ N)}
    (hFr : Frame (↥K ⧸ N) ((A₁.subgroupOf K).map (QuotientGroup.mk' N))
      ((A₁.subgroupOf K).map (QuotientGroup.mk' N)) ((R.subgroupOf K).map (QuotientGroup.mk' N))
      gb Eb Fb)
    (k : ↥K) (hk : QuotientGroup.mk' N k = gb) :
    Frame G A A₁ R k ((twoLift N Eb).map K.subtype) ((twoLift N Fb).map K.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (R.subgroupOf K) := (isPGroup_R hS).comap_subtype
  have hA₁map : (A₁.subgroupOf K).map K.subtype = A₁ := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hA₁K]
  have hRmap : (R.subgroupOf K).map K.subtype = R := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hRK]
  have hRlift : twoLift N ((R.subgroupOf K).map (QuotientGroup.mk' N)) = R.subgroupOf K :=
    twoLift_map hNc hNo hR2
  have hcomap : ((A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊔
      (R.subgroupOf K).map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) =
      A₁.subgroupOf K ⊔ R.subgroupOf K := by
    rw [← Subgroup.map_sup, comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr (hNA.trans le_sup_left)
  have hD2 : IsPGroup 2 ↥(Eb ⊔ Fb) := hFr.sylow.isPGroup
  have hE2 : IsPGroup 2 Eb := hD2.to_le le_sup_left
  have hF2 : IsPGroup 2 Fb := hD2.to_le le_sup_right
  have hRg2 : IsPGroup 2 (rightConjugate (R.subgroupOf K) k) := by
    unfold rightConjugate
    exact hR2.map _
  have hRgmap : (rightConjugate (R.subgroupOf K) k).map (QuotientGroup.mk' N) =
      rightConjugate ((R.subgroupOf K).map (QuotientGroup.mk' N)) gb := by
    rw [map_rightConjugate, hk]
  have hRgG : rightConjugate R (k : G) =
      (rightConjugate (R.subgroupOf K) k).map K.subtype := by
    rw [map_rightConjugate, hRmap]
    rfl
  have hRglift : twoLift N (rightConjugate ((R.subgroupOf K).map (QuotientGroup.mk' N)) gb) =
      rightConjugate (R.subgroupOf K) k := by
    rw [← hRgmap]
    exact twoLift_map hNc hNo hRg2
  have hEFsup : twoLift N (Eb ⊔ Fb) = twoLift N Eb ⊔ twoLift N Fb := twoLift_sup hNc hNo hD2
  have hEFinf : twoLift N (Eb ⊓ Fb) = twoLift N Eb ⊓ twoLift N Fb :=
    twoLift_inf hNc hNo hD2 le_sup_left le_sup_right
  have hlift_le : ∀ {W : Subgroup (↥K ⧸ N)}, IsPGroup 2 W →
      W ≤ (A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊔
        (R.subgroupOf K).map (QuotientGroup.mk' N) →
      twoLift N W ≤ A₁.subgroupOf K ⊔ R.subgroupOf K := fun hW hWle => by
    rw [← hcomap]
    exact (isSylowOf_twoLift hNc hNo hW).le.trans (comap_mono hWle)
  have hsupG : A₁ ⊔ R = (A₁.subgroupOf K ⊔ R.subgroupOf K).map K.subtype := by
    rw [Subgroup.map_sup, hA₁map, hRmap]
  have hinj := K.subtype_injective
  refine ⟨hS.base, hS.le, hS.quasisimple, hS.typeA₁, hS.sylowR, hS.elemR, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [← Nat.card_congr (subgroupOfEquivOfLe hRK).toEquiv,
      ← AS81.card_map_mk'_of_le hR2 hNo le_rfl]
    exact hFr.cardR
  ·
    intro hkA
    apply hFr.not_mem
    have hkx : (k : G) ∈ centralizer ((zpowers x : Subgroup G) : Set G) := by
      rw [centralizer_zpowers]
      exact hKx k.2
    have h1 := AS76b.normalizer_inf_le_normalizer_layerCentralizer A (zpowers x)
      (mem_inf.mpr ⟨hkA, hkx⟩)
    rw [hS.layer] at h1
    have h2 : k ∈ normalizer ((A₁.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
      rw [mem_normalizer_iff]
      intro a
      rw [mem_subgroupOf, mem_subgroupOf]
      simpa using mem_normalizer_iff.mp h1 a
    rw [← hk]
    exact le_normalizer_map _ ⟨k, h2, rfl⟩
  ·
    have h1 := le_centralizer_of_map hNc hNo hRg2 hR2 (by rw [hRgmap]; exact hFr.comm)
    rw [hRgG]
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    intro r hr
    have hr' : (⟨r, hRK hr⟩ : ↥K) ∈ R.subgroupOf K := hr
    exact congrArg Subtype.val (mem_centralizer_iff.mp (h1 ha) _ hr')
  ·
    rw [hRgG, hsupG]
    refine map_mono ?_
    rw [← hRglift]
    exact hlift_le (by rw [← hRgmap]; exact hRg2.map _) hFr.conj_le
  ·
    rw [hsupG]
    exact map_mono (hlift_le hE2 hFr.E_le)
  ·
    rw [hsupG]
    exact map_mono (hlift_le hF2 hFr.F_le)
  ·
    rw [← hRmap, ← hRlift]
    exact map_mono (twoLift_mono hNc hNo (hR2.map _) hFr.R_le_E)
  ·
    rw [← hRmap, ← hRlift]
    exact map_mono (twoLift_mono hNc hNo (hR2.map _) hFr.R_le_F)
  · exact isElemAbelian_map _ (isElemAbelian_twoLift hNc hNo hFr.elemE)
  · exact isElemAbelian_map _ (isElemAbelian_twoLift hNc hNo hFr.elemF)
  · rw [card_map_of_injective hinj, card_twoLift hNc hNo hE2, hFr.cardE]
  · rw [card_map_of_injective hinj, card_twoLift hNc hNo hF2, hFr.cardF]
  ·
    intro h
    apply hFr.ne
    have h1 := (map_injective hinj) h
    rw [← map_twoLift hNc hNo hE2, ← map_twoLift hNc hNo hF2, h1]
  ·
    rw [← map_inf_eq _ _ _ hinj, ← hEFinf, hFr.inf_eq, twoLift_sup hNc hNo (by
      rw [← hFr.inf_eq]; exact hD2.to_le (inf_le_left.trans le_sup_left)), hRlift, hRglift,
      Subgroup.map_sup, hRmap, ← hRgG]
  ·
    rw [← map_inf_eq _ _ _ hinj, ← Subgroup.map_sup, centerIn_map_of_injective _ hinj,
      ← hEFinf, ← hEFsup, hFr.inf_eq_center, centerIn_twoLift hNc hNo hD2]
  ·
    rw [← Subgroup.map_sup, hsupG, isSylowOf_map_subtype_iff, ← hEFsup, ← hcomap]
    exact isSylowOf_twoLift_comap hNc hNo hFr.sylow

theorem isQ8Cube_twoLift {K : Subgroup G} {N : Subgroup ↥K} [N.Normal]
    (hNc : N ≤ center ↥K) (hNo : Odd (Nat.card N)) {Qb : Subgroup (↥K ⧸ N)} (hQ : IsQ8Cube Qb) :
    IsQ8Cube ((twoLift N Qb).map K.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 Qb := hQ.1.1
  let e : ↥((twoLift N Qb).map K.subtype) ≃* ↥Qb :=
    ((twoLift N Qb).equivMapOfInjective _ K.subtype_injective).symm.trans
      (twoLiftEquiv hNc hNo hQ2)
  refine ⟨LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv e.symm hQ.1, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, hQ.2.1]
  · rintro ⟨U, hUQ, hU, hU16⟩
    apply hQ.2.2
    have hUK : U ≤ K := hUQ.trans (map_subtype_le _)
    have hUQ' : U.subgroupOf K ≤ twoLift N Qb := fun u hu => by
      obtain ⟨v, hv, hvu⟩ := hUQ (mem_subgroupOf.mp hu)
      rwa [show v = u from Subtype.ext hvu] at hv
    refine ⟨(U.subgroupOf K).map (QuotientGroup.mk' N), ?_, isElemAbelian_map _
      (isElemAbelian_subgroupOf' hU), ?_⟩
    · rw [← map_twoLift hNc hNo hQ2]
      exact map_mono hUQ'
    · rw [AS81.card_map_mk'_of_le (isPGroup_twoLift hNc hNo hQ2) hNo hUQ',
        Nat.card_congr (subgroupOfEquivOfLe hUK).toEquiv, hU16]

theorem twoLift_zpowers {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    (hNc : N ≤ center H) (hNo : Odd (Nat.card N)) {z : H} (hz : IsPGroup 2 (zpowers z)) :
    twoLift N (zpowers (QuotientGroup.mk' N z)) = zpowers z := by
  rw [← MonoidHom.map_zpowers]
  exact twoLift_map hNc hNo hz

theorem isQ8Cube_map_of_le {K : Subgroup G} {N : Subgroup ↥K} [N.Normal]
    (hNc : N ≤ center ↥K) (hNo : Odd (Nat.card N)) {W : Subgroup (↥K ⧸ N)} (hW : IsPGroup 2 W)
    {X : Subgroup ↥K} (hXW : X ≤ twoLift N W) (hX : IsQ8Cube (X.map K.subtype)) :
    IsQ8Cube (X.map (QuotientGroup.mk' N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp X.subtype) := fun a b h =>
    Subtype.ext (injOn_twoLift hNc hNo hW (hXW a.2) (hXW b.2) h)
  let e₁ : ↥(X.map K.subtype) ≃* ↥X :=
    (X.equivMapOfInjective _ K.subtype_injective).symm
  let e₂ : ↥X ≃* ↥(X.map (QuotientGroup.mk' N)) :=
    (MulEquiv.ofBijective (((QuotientGroup.mk' N).comp X.subtype).rangeRestrict)
      ⟨fun a b h => hinj (congrArg Subtype.val h), MonoidHom.rangeRestrict_surjective _⟩).trans
      (MulEquiv.subgroupCongr (by
        rw [MonoidHom.range_eq_map, ← map_map, ← MonoidHom.range_eq_map, range_subtype]))
  refine ⟨LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv (e₁.trans e₂) hX.1, ?_, ?_⟩
  · rw [← Nat.card_congr (e₁.trans e₂).toEquiv, hX.2.1]
  · rintro ⟨U, hUX, hU, hU16⟩
    apply hX.2.2
    have hU2 : IsPGroup 2 U := fun u => ⟨1, Subtype.ext (by simpa using hU.2 _ u.2)⟩
    have hUW : U ≤ W := hUX.trans ((map_mono hXW).trans (map_twoLift hNc hNo hW).le)
    have hlift : twoLift N U ≤ X := by
      have h1 : twoLift N U ≤ twoLift N (X.map (QuotientGroup.mk' N)) :=
        twoLift_mono hNc hNo hU2 hUX
      rwa [twoLift_map hNc hNo ((isPGroup_twoLift hNc hNo hW).to_le hXW)] at h1
    refine ⟨(twoLift N U).map K.subtype, map_mono hlift,
      isElemAbelian_map _ (isElemAbelian_twoLift hNc hNo hU), ?_⟩
    rw [card_map_of_injective K.subtype_injective, card_twoLift hNc hNo hU2, hU16]

theorem twoLift_inf_map {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    (hNc : N ≤ center H) (hNo : Odd (Nat.card N)) {L : Subgroup H} (hNL : N ≤ L)
    {C : Subgroup (H ⧸ N)} (hC : IsPGroup 2 C) :
    twoLift N (L.map (QuotientGroup.mk' N) ⊓ C) = L ⊓ twoLift N C := by
  have hLC : IsPGroup 2 ↥(L.map (QuotientGroup.mk' N) ⊓ C) := hC.to_le inf_le_right
  refine le_antisymm (le_inf ?_ (twoLift_mono hNc hNo hLC inf_le_right)) (le_twoLift
    ((isPGroup_twoLift hNc hNo hC).to_le inf_le_right) ?_)
  · refine (isSylowOf_twoLift hNc hNo hLC).le.trans ?_
    refine (comap_mono inf_le_left).trans ?_
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNL]
  · exact (map_inf_le _ _ _).trans (inf_le_inf_left _ (map_twoLift hNc hNo hC).le)

theorem sec3Suz_of_sec2 (hS : Sec3Pre G A A₁ R x) (h21 : Step21) (h24 : Step24)
    (h27 : Step27) (h211 : Step211) (h212 : Step212) (hLQ : Sec2LocalQ)
    {K : Subgroup G} {N : Subgroup ↥K} [N.Normal] (hNc : N ≤ center ↥K)
    (hNo : Odd (Nat.card N)) (hNA : N ≤ A₁.subgroupOf K) (hN3 : Nat.card N ∣ 3)
    (hKdef : K = sec3B A₁ x ⊔ R) (hKx : K ≤ centralizer ({x} : Set G))
    (hRB : R ≤ normalizer (sec3B A₁ x : Set G))
    {gb : ↥K ⧸ N} {Eb Fb : Subgroup (↥K ⧸ N)}
    (hS2 : Sec2Setting (↥K ⧸ N) ((A₁.subgroupOf K).map (QuotientGroup.mk' N))
      ((R.subgroupOf K).map (QuotientGroup.mk' N)) gb Eb Fb)
    (hcov : ∀ e ∈ Eb, e ∉ (A₁.subgroupOf K).map (QuotientGroup.mk' N) →
      ∃ a ∈ sec2P Eb, e ∈ rightConjugate ((R.subgroupOf K).map (QuotientGroup.mk' N)) a)
    (hBc : centerIn (sec3B A₁ x) = zpowers x) (hBp : commutator ↥(sec3B A₁ x) = ⊤)
    (hBs : NativeSporadic.IsSporadic (↥(sec3B A₁ x) ⧸ center ↥(sec3B A₁ x)) .Suz) :
    ∃ (g' : G) (E' F' Zs P T Q B₀ : Subgroup G) (z y : G),
      Sec3Suz G A A₁ R g' E' F' x Zs P T Q B₀ z y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBK : sec3B A₁ x ≤ K := hKdef ▸ le_sup_left
  have hRK : R ≤ K := hKdef ▸ le_sup_right
  have hA₁K : A₁ ≤ K := (le_sec3B (A₁_le_centralizer hS)).trans hBK
  obtain ⟨⟨T₀b, hPS, hT₀syl⟩, h212all⟩ := h212 _ _ _ _ _ _ hS2
  obtain ⟨hT₀all, hPST, -, hZ2, hZne, hT₀P⟩ := h212all T₀b hPS hT₀syl
  obtain ⟨⟨ub, yb, huy⟩, -⟩ := h27 _ _ _ _ _ _ hS2
  have hData : Sec2Data (↥K ⧸ N) _ _ gb Eb Fb T₀b ub yb := ⟨hS2, hPS, hT₀syl, huy⟩
  obtain ⟨Qb, hQ8, hQT, hyQ, hQuniq, -, hHTQ, hQidx⟩ := hLQ _ _ _ _ _ _ _ _ _ hData
  have htrans := (h211 _ _ _ _ _ _ hS2).2.2.2.2.1 ub yb huy
  have hZ4 := (h24 _ _ _ _ _ _ hS2).1
  have hEP : Eb ≤ sec2P Eb := (h21 _ _ _ _ _ _ hS2).2.1.1
  have hD2 : IsPGroup 2 ↥(Eb ⊔ Fb) := hS2.frame.sylow.isPGroup
  have hE2 : IsPGroup 2 Eb := hD2.to_le le_sup_left
  have hT2 : IsPGroup 2 (sec2T Eb T₀b) := hT₀syl.isPGroup.to_le inf_le_left
  have hET : Eb ≤ sec2T Eb T₀b := hEP.trans (le_sup_left.trans hPST)
  have hT1 : sec2T Eb T₀b ≠ ⊥ := by
    intro h
    have h64 := hS2.frame.cardE
    have h' : Eb ≤ ⊥ := by
      rw [← h]
      exact hET
    rw [le_bot_iff.mp h', Subgroup.card_bot] at h64
    omega
  obtain ⟨zb, hzT, hz2, hzZ⟩ := exists_centerIn_eq_zpowers hT2 hT1 hZ2 hZne hZ4
  have hTQ : sec2T Eb T₀b ≤ normalizer (Qb : Set (↥K ⧸ N)) := le_sup_right.trans hHTQ
  have hzQ : centerIn Qb = zpowers zb := centerIn_eq_of_normal hT2 hQT hTQ hQ8.1 hzT hz2
  have hQ2 : IsPGroup 2 Qb := hQ8.1.1
  have hZb2 : IsPGroup 2 (sec2Z ((A₁.subgroupOf K).map (QuotientGroup.mk' N)) Eb Fb) :=
    hD2.to_le (inf_le_right.trans inf_le_left)
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective N gb
  have hFr' := frame_lift hS hNc hNo hNA hA₁K hRK hKx hS2.frame k hk
  have hS' : Sec3Setting G A A₁ R k ((twoLift N Eb).map K.subtype)
      ((twoLift N Fb).map K.subtype) x := ⟨hS, hFr'⟩
  have hzbT : zb ∈ sec2T Eb T₀b := (hzT ▸ mem_zpowers zb : zb ∈ centerIn (sec2T Eb T₀b)).1
  obtain ⟨z₁, hz₁T, hz₁⟩ := exists_mem_twoLift hNc hNo hT2 hzbT
  have hz₁2 : IsPGroup 2 (zpowers z₁) :=
    (isPGroup_twoLift hNc hNo hT2).to_le (zpowers_le.mpr hz₁T)
  obtain ⟨y₁, hy₁⟩ := QuotientGroup.mk'_surjective N yb
  have hR2 : IsPGroup 2 (R.subgroupOf K) := (isPGroup_R hS).comap_subtype
  have hRlift : twoLift N ((R.subgroupOf K).map (QuotientGroup.mk' N)) = R.subgroupOf K :=
    twoLift_map hNc hNo hR2
  have hRB' : R ≤ sec3B A₁ x := by
    have hRbK : (R.subgroupOf K).map (QuotientGroup.mk' N) ≤ sec2K Eb :=
      hS2.frame.R_le_E.trans (hET.trans inf_le_right)
    have hKB : sec2K Eb ≤ ((sec3B A₁ x).subgroupOf K).map (QuotientGroup.mk' N) := by
      refine (closure_le _).mpr ?_
      rintro kb ⟨-, hkb⟩
      obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective N kb
      refine ⟨k', mem_subgroupOf.mpr ?_, rfl⟩
      refine mem_of_odd_of_mem_sup (isPGroup_R hS) hRB (hKdef ▸ k'.2) ?_
      rw [Subgroup.orderOf_coe]
      have h1 : k' ^ orderOf (QuotientGroup.mk' N k') ∈ (QuotientGroup.mk' N).ker := by
        rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
      rw [QuotientGroup.ker_mk'] at h1
      have h2 : (k' ^ orderOf (QuotientGroup.mk' N k')) ^ Nat.card N = 1 := by
        have h3 : (⟨_, h1⟩ : ↥N) ^ Nat.card N = 1 := pow_card_eq_one'
        exact congrArg Subtype.val h3
      rw [← pow_mul] at h2
      exact (hkb.mul hNo).of_dvd_nat (orderOf_dvd_of_pow_eq_one h2)
    intro r hr
    obtain ⟨b, hb, hbr⟩ := hKB (hRbK ⟨⟨r, hRK hr⟩, hr, rfl⟩)
    have h1 : b⁻¹ * ⟨r, hRK hr⟩ ∈ N := by
      rw [← QuotientGroup.eq]
      exact hbr
    have h2 := (sec3B A₁ x).mul_mem (mem_subgroupOf.mp hb)
      (le_sec3B (A₁_le_centralizer hS) (mem_subgroupOf.mp (hNA h1)))
    simpa using h2
  have hKB : K ≤ sec3B A₁ x := hKdef ▸ sup_le le_rfl hRB'
  have hinj := K.subtype_injective
  have hA₁map : (A₁.subgroupOf K).map K.subtype = A₁ := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hA₁K]
  have hRmap : (R.subgroupOf K).map K.subtype = R := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hRK]
  have hC2 : IsPGroup 2 (centerIn (Eb ⊔ Fb)) := hD2.to_le inf_le_left
  have hZs : sec2Z A₁ ((twoLift N Eb).map K.subtype) ((twoLift N Fb).map K.subtype) =
      (twoLift N (sec2Z ((A₁.subgroupOf K).map (QuotientGroup.mk' N)) Eb Fb)).map K.subtype := by
    unfold sec2Z
    rw [twoLift_inf_map hNc hNo hNA hC2, map_inf_eq _ _ _ hinj, hA₁map,
      ← centerIn_twoLift hNc hNo hD2, twoLift_sup hNc hNo hD2,
      ← centerIn_map_of_injective _ hinj, Subgroup.map_sup]
  have hz₁Z : z₁ ∈ twoLift N (sec2Z ((A₁.subgroupOf K).map (QuotientGroup.mk' N)) Eb Fb) := by
    refine le_twoLift hz₁2 ?_ (mem_zpowers z₁)
    rw [MonoidHom.map_zpowers, hz₁, zpowers_le]
    exact hzZ
  have hzlift : twoLift N (zpowers zb) = zpowers z₁ := by
    rw [← hz₁]
    exact twoLift_zpowers hNc hNo hz₁2
  have hTc : centerIn ((twoLift N (sec2T Eb T₀b)).map K.subtype) = zpowers (z₁ : G) := by
    rw [centerIn_map_of_injective _ hinj, centerIn_twoLift hNc hNo hT2, hzT, hzlift,
      MonoidHom.map_zpowers]
    rfl
  have hQc : centerIn ((twoLift N Qb).map K.subtype) = zpowers (z₁ : G) := by
    rw [centerIn_map_of_injective _ hinj, centerIn_twoLift hNc hNo hQ2, hzQ, hzlift,
      MonoidHom.map_zpowers]
    rfl
  have hyN : yb ∈ normalizer (((R.subgroupOf K).map (QuotientGroup.mk' N) : Subgroup _) :
      Set (↥K ⧸ N)) := huy.2.2.2.1.1.2
  have hy₁R : y₁ ∈ normalizer ((R.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [← hRlift]
    exact mem_normalizer_twoLift hNc hNo (hR2.map _) (hy₁ ▸ hyN)
  have hy₁Q : y₁ ∈ normalizer ((twoLift N Qb : Subgroup ↥K) : Set ↥K) :=
    mem_normalizer_twoLift hNc hNo hQ2 (hy₁ ▸ hyQ)
  have hP2b : IsPGroup 2 (sec2P Eb) := isPGroup_sec2P Eb
  have hPNb : sec2P Eb ≤ normalizer (Eb : Set (↥K ⧸ N)) := sec2P_le_normalizer Eb
  have hPlift : pCoreOf 2 (sec3B A₁ x ⊓ normalizer
      (((twoLift N Eb).map K.subtype : Subgroup G) : Set G)) ≤
      (twoLift N (sec2P Eb)).map K.subtype := by
    set P := pCoreOf 2 (sec3B A₁ x ⊓ normalizer
      (((twoLift N Eb).map K.subtype : Subgroup G) : Set G)) with hP
    have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hPK : P ≤ K := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_left.trans hBK)
    have hPK2 : IsPGroup 2 (P.subgroupOf K) := hP2.comap_subtype
    have hPN : (P.subgroupOf K).map (QuotientGroup.mk' N) ≤
        normalizer (Eb : Set (↥K ⧸ N)) := by
      rintro _ ⟨p, hp, rfl⟩
      have hpN : (p : G) ∈ normalizer (((twoLift N Eb).map K.subtype : Subgroup G) : Set G) :=
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _) (mem_subgroupOf.mp hp)).2
      have hpN' : p ∈ normalizer ((twoLift N Eb : Subgroup ↥K) : Set ↥K) := by
        rw [mem_normalizer_iff]
        intro a
        have h1 := mem_normalizer_iff.mp hpN a
        constructor
        · intro ha
          obtain ⟨b, hb, hba⟩ := h1.mp ⟨a, ha, rfl⟩
          rw [show b = p * a * p⁻¹ from Subtype.ext (by simpa using hba)] at hb
          exact hb
        · intro ha
          obtain ⟨b, hb, hba⟩ := h1.mpr ⟨_, ha, rfl⟩
          rwa [show b = a from Subtype.ext hba] at hb
      rw [← map_twoLift hNc hNo hE2]
      exact le_normalizer_map _ ⟨p, hpN', rfl⟩
    have hPnorm : (((P.subgroupOf K).map (QuotientGroup.mk' N)).subgroupOf
        (normalizer (Eb : Set (↥K ⧸ N)))).Normal := by
      refine (normal_subgroupOf_iff_le_normalizer hPN).mpr ?_
      intro nb hnb
      obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective N nb
      have hn : n ∈ normalizer ((twoLift N Eb : Subgroup ↥K) : Set ↥K) :=
        mem_normalizer_twoLift hNc hNo hE2 hnb
      have hnG : (n : G) ∈ sec3B A₁ x ⊓ normalizer
          (((twoLift N Eb).map K.subtype : Subgroup G) : Set G) := by
        refine ⟨hKB n.2, ?_⟩
        have := le_normalizer_map K.subtype ⟨n, hn, rfl⟩
        exact this
      have hnP := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hnG
      have hnPK : n ∈ normalizer ((P.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
        rw [mem_normalizer_iff]
        intro a
        rw [mem_subgroupOf, mem_subgroupOf]
        exact mem_normalizer_iff.mp hnP a
      exact le_normalizer_map _ ⟨n, hnPK, rfl⟩
    have hle : (P.subgroupOf K).map (QuotientGroup.mk' N) ≤ sec2P Eb := by
      intro a ha
      have h1 : ((P.subgroupOf K).map (QuotientGroup.mk' N)).subgroupOf
          (normalizer (Eb : Set (↥K ⧸ N))) ≤ CFSG.pCore 2 ↥(normalizer (Eb : Set (↥K ⧸ N))) :=
        le_sSup ⟨hPnorm, (hPK2.map _).comap_subtype⟩
      exact ⟨⟨a, hPN ha⟩, h1 (mem_subgroupOf.mpr ha), rfl⟩
    have h2 : P.subgroupOf K ≤ twoLift N (sec2P Eb) := le_twoLift hPK2 hle
    intro p hp
    exact ⟨⟨p, hPK hp⟩, h2 hp, rfl⟩
  have hPT : pCoreOf 2 (sec3B A₁ x ⊓ normalizer
      (((twoLift N Eb).map K.subtype : Subgroup G) : Set G)) ≤
      (twoLift N (sec2T Eb T₀b)).map K.subtype :=
    hPlift.trans (map_mono (twoLift_mono hNc hNo hP2b (le_sup_left.trans hPST)))
  have hNK : ∀ n : ↥K, (n : G) ∈ normalizer (((twoLift N Eb).map K.subtype : Subgroup G) : Set G) →
      n ∈ normalizer ((twoLift N Eb : Subgroup ↥K) : Set ↥K) := by
    intro n hn
    rw [mem_normalizer_iff]
    intro a
    have h1 := mem_normalizer_iff.mp hn a
    constructor
    · intro ha
      obtain ⟨b, hb, hba⟩ := h1.mp ⟨a, ha, rfl⟩
      rw [show b = n * a * n⁻¹ from Subtype.ext (by simpa using hba)] at hb
      exact hb
    · intro ha
      obtain ⟨b, hb, hba⟩ := h1.mpr ⟨_, ha, rfl⟩
      rwa [show b = a from Subtype.ext hba] at hb
  have hliftP : (twoLift N (sec2P Eb)).map K.subtype ≤ pCoreOf 2 (sec3B A₁ x ⊓
      normalizer (((twoLift N Eb).map K.subtype : Subgroup G) : Set G)) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
      ((isPGroup_twoLift hNc hNo hP2b).map _)
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨hKB a.2, le_normalizer_map K.subtype ⟨a, mem_normalizer_twoLift hNc hNo hE2
        (hPNb (mk_mem_of_mem_twoLift hNc hNo hP2b ha)), rfl⟩⟩
    · intro n hn
      have hnK : n ∈ K := hBK hn.1
      have hnEb : QuotientGroup.mk' N ⟨n, hnK⟩ ∈ normalizer (Eb : Set (↥K ⧸ N)) := by
        rw [← map_twoLift hNc hNo hE2]
        exact le_normalizer_map _ ⟨_, hNK ⟨n, hnK⟩ hn.2, rfl⟩
      have hnPb : QuotientGroup.mk' N ⟨n, hnK⟩ ∈ normalizer (sec2P Eb : Set (↥K ⧸ N)) :=
        normalizer_le_normalizer_sec2P Eb hnEb
      exact le_normalizer_map K.subtype ⟨⟨n, hnK⟩, mem_normalizer_twoLift hNc hNo hP2b hnPb, rfl⟩
  have hPeq : pCoreOf 2 (sec3B A₁ x ⊓ normalizer
      (((twoLift N Eb).map K.subtype : Subgroup G) : Set G)) =
      (twoLift N (sec2P Eb)).map K.subtype := le_antisymm hPlift hliftP
  refine ⟨k, (twoLift N Eb).map K.subtype, (twoLift N Fb).map K.subtype,
    sec2Z A₁ ((twoLift N Eb).map K.subtype) ((twoLift N Fb).map K.subtype),
    pCoreOf 2 (sec3B A₁ x ⊓ normalizer (((twoLift N Eb).map K.subtype : Subgroup G) : Set G)),
    (twoLift N (sec2T Eb T₀b)).map K.subtype, (twoLift N Qb).map K.subtype,
    ⁅sec3B A₁ x ⊓ centralizer ({(z₁ : G)} : Set G),
      sec3B A₁ x ⊓ centralizer ({(z₁ : G)} : Set G)⁆, z₁, y₁,
    ⟨hS', hRB', rfl, ?_, rfl, (map_subtype_le _).trans hKB,
      (isPGroup_twoLift hNc hNo hT2).map _, hPT,
      map_mono (twoLift_mono hNc hNo (hD2.to_le le_sup_right)
        (le_sup_left.trans (le_sup_right.trans hPST))),
      map_mono (twoLift_mono hNc hNo hQ2 hQT),
      isQ8Cube_twoLift hNc hNo hQ8, hQc, hTc, ?_, le_normalizer_map _ ⟨y₁, hy₁Q, rfl⟩, ?_, rfl,
      ⟨hKB y₁.2, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hBs, hBc, ?_, ?_, hBp⟩⟩
  · rw [hZs, card_map_of_injective hinj, card_twoLift hNc hNo hZb2, hZ4]
  · rw [hZs]
    exact ⟨z₁, hz₁Z, rfl⟩
  ·
    intro Q' hQ' hQ'T hyQ'
    have hQ'K : Q' ≤ K := hQ'T.trans (map_subtype_le _)
    have hXmap : (Q'.subgroupOf K).map K.subtype = Q' := by
      rw [subgroupOf_map_subtype, inf_eq_left.mpr hQ'K]
    have hXT : Q'.subgroupOf K ≤ twoLift N (sec2T Eb T₀b) := fun a ha => by
      obtain ⟨b, hb, hba⟩ := hQ'T (mem_subgroupOf.mp ha)
      rwa [show b = a from Subtype.ext hba] at hb
    have hX8 : IsQ8Cube ((Q'.subgroupOf K).map (QuotientGroup.mk' N)) :=
      isQ8Cube_map_of_le hNc hNo hT2 hXT (by rw [hXmap]; exact hQ')
    have hX2 : IsPGroup 2 (Q'.subgroupOf K) := (isPGroup_twoLift hNc hNo hT2).to_le hXT
    have hyX : y₁ ∈ normalizer ((Q'.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
      rw [mem_normalizer_iff]
      intro a
      rw [mem_subgroupOf, mem_subgroupOf]
      exact mem_normalizer_iff.mp hyQ' a
    have hyXb : yb ∈ normalizer (((Q'.subgroupOf K).map (QuotientGroup.mk' N) :
        Subgroup (↥K ⧸ N)) : Set (↥K ⧸ N)) := by
      rw [← hy₁]
      exact le_normalizer_map _ ⟨y₁, hyX, rfl⟩
    have hXTb : (Q'.subgroupOf K).map (QuotientGroup.mk' N) ≤ sec2T Eb T₀b :=
      (map_mono hXT).trans (map_twoLift hNc hNo hT2).le
    have h1 := hQuniq _ hX8 hXTb hyXb
    rw [← hXmap, ← twoLift_map hNc hNo hX2, h1]
  · rw [← hRmap]
    exact le_normalizer_map _ ⟨y₁, hy₁R, rfl⟩
  ·
    refine ⟨2, ?_⟩
    have h1 : y₁ ^ 3 ∈ (QuotientGroup.mk' N).ker := by
      rw [MonoidHom.mem_ker, map_pow, hy₁, ← huy.2.2.2.2, pow_orderOf_eq_one]
    rw [QuotientGroup.ker_mk'] at h1
    have h2 : (⟨_, h1⟩ : ↥N) ^ 3 = 1 := by
      obtain ⟨c, hc⟩ := hN3
      have h5 : (⟨_, h1⟩ : ↥N) ^ (Nat.card N * c) = 1 := by
        rw [pow_mul, pow_card_eq_one', one_pow]
      rwa [← hc] at h5
    have h3 : (y₁ ^ 3) ^ 3 = 1 := congrArg Subtype.val h2
    rw [← pow_mul] at h3
    have h4 := congrArg Subtype.val h3
    simpa using h4
  ·
    intro r hr hr1 h
    have hr' : (⟨r, hRK hr⟩ : ↥K) ∈ R.subgroupOf K := hr
    refine htrans _ ⟨_, hr', rfl⟩ (fun h1 => hr1 ?_) ?_
    · have h2 := AS81.mk'_injOn hR2 hNo hr' (one_mem _) (h1.trans (map_one _).symm)
      exact congrArg Subtype.val h2
    · rw [← hy₁, ← map_inv, ← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext h)
  ·
    rintro _ ⟨e', he', rfl⟩ heA
    have heb : QuotientGroup.mk' N e' ∈ Eb := mk_mem_of_mem_twoLift hNc hNo hE2 he'
    have hebA : QuotientGroup.mk' N e' ∉ (A₁.subgroupOf K).map (QuotientGroup.mk' N) := by
      rintro ⟨a, ha, hae⟩
      apply heA
      have h1 : a⁻¹ * e' ∈ N := by
        rw [← QuotientGroup.eq]
        exact hae
      have h2 := mul_mem (mem_subgroupOf.mp ha) (mem_subgroupOf.mp (hNA h1))
      simpa using h2
    obtain ⟨ab, hab, heab⟩ := hcov _ heb hebA
    obtain ⟨a, ha, rfl⟩ := exists_mem_twoLift hNc hNo hP2b hab
    refine ⟨a, hliftP ⟨a, ha, rfl⟩, ?_⟩
    have hRa2 : IsPGroup 2 (rightConjugate (R.subgroupOf K) a) := by
      unfold rightConjugate
      exact hR2.map _
    have hRaE : rightConjugate (R.subgroupOf K) a ≤ twoLift N Eb := by
      refine le_twoLift hRa2 ?_
      rw [map_rightConjugate]
      intro w hw
      rw [mem_rightConjugate_iff] at hw
      have h1 := (mem_normalizer_iff.mp (inv_mem (hPNb (mk_mem_of_mem_twoLift hNc hNo hP2b ha)))
        _).mp (hS2.frame.R_le_E hw)
      simpa [mul_assoc] using h1
    rw [← map_rightConjugate] at heab
    obtain ⟨r, hr, hre⟩ := heab
    have hr : r ∈ rightConjugate (R.subgroupOf K) a := hr
    have hre' := injOn_twoLift hNc hNo hE2 (hRaE hr) he' hre
    subst hre'
    rw [mem_rightConjugate_iff] at hr ⊢
    exact hr
  ·
    have hPc := sec2P_le_centralizer h211 hS2
    rintro _ hp
    obtain ⟨p', hp', rfl⟩ := hPeq ▸ hp
    rw [mem_centralizer_iff]
    rintro _ ⟨⟨e', he', rfl⟩, heA⟩
    have hp'N : p' ∈ normalizer ((twoLift N Eb : Subgroup ↥K) : Set ↥K) :=
      mem_normalizer_twoLift hNc hNo hE2 (hPNb (mk_mem_of_mem_twoLift hNc hNo hP2b hp'))
    have hc : p' * e' * p'⁻¹ * e'⁻¹ ∈ twoLift N Eb :=
      mul_mem ((mem_normalizer_iff.mp hp'N e').mp he') (inv_mem he')
    have hcb : QuotientGroup.mk' N (p' * e' * p'⁻¹ * e'⁻¹) = QuotientGroup.mk' N 1 := by
      have h1 := mem_centralizer_iff.mp (hPc (mk_mem_of_mem_twoLift hNc hNo hP2b hp'))
        (QuotientGroup.mk' N e') ⟨mk_mem_of_mem_twoLift hNc hNo hE2 he', ⟨e', heA, rfl⟩⟩
      simp only [map_mul, map_inv, map_one]
      rw [← h1]
      group
    have h1 := injOn_twoLift hNc hNo hE2 hc (one_mem _) hcb
    have h2 : e' * p' = p' * e' := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    exact congrArg Subtype.val h2
  ·
    obtain ⟨hPFE, ⟨hEPb, hrel, -⟩, -⟩ := h21 _ _ _ _ _ _ hS2
    have hEcomm : ∀ a ∈ Eb, ∀ b ∈ Eb, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hS2.frame.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    refine le_antisymm ?_ (le_inf ?_ ?_)
    · rintro _ ⟨hp, hpc⟩
      obtain ⟨p', hp', rfl⟩ := hPeq ▸ hp
      have hpb : QuotientGroup.mk' N p' ∈ (sec2P Eb ⊔ Fb) ⊓ centralizer (Eb : Set (↥K ⧸ N)) := by
        refine mem_inf.mpr ⟨mem_sup_left (mk_mem_of_mem_twoLift hNc hNo hP2b hp'), ?_⟩
        rw [mem_centralizer_iff]
        intro eb heb
        obtain ⟨e', he', rfl⟩ := exists_mem_twoLift hNc hNo hE2 heb
        have h1 := mem_centralizer_iff.mp hpc _ ⟨e', he', rfl⟩
        rw [← map_mul, ← map_mul]
        exact congrArg _ (Subtype.ext h1)
      rw [hPFE] at hpb
      obtain ⟨e', he', he'p⟩ := exists_mem_twoLift hNc hNo hE2 hpb
      have h1 := injOn_twoLift hNc hNo hP2b (twoLift_mono hNc hNo hE2 hEPb he') hp' he'p
      subst h1
      exact ⟨e', he', rfl⟩
    · rw [hPeq]
      exact map_mono (twoLift_mono hNc hNo hE2 hEPb)
    · rintro _ ⟨e', he', rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨e'', he'', rfl⟩
      exact congrArg Subtype.val ((hS'.frame.elemE.1.is_comm.comm ⟨_, ⟨e'', he'', rfl⟩⟩
        ⟨_, ⟨e', he', rfl⟩⟩))
  ·
    obtain ⟨-, ⟨hEPb, hrel, -⟩, -⟩ := h21 _ _ _ _ _ _ hS2
    have h1 := Subgroup.relIndex_mul_relIndex ⊥ Eb (sec2P Eb) bot_le hEPb
    rw [relIndex_bot_left, relIndex_bot_left, hrel, hS2.frame.cardE] at h1
    rw [hPeq, card_map_of_injective hinj, card_twoLift hNc hNo hP2b, ← h1]
    norm_num
  ·
    obtain ⟨-, -, -, -, -, hcm, -⟩ := h211 _ _ _ _ _ _ hS2
    have hEPb : Eb ≤ sec2P Eb := (h21 _ _ _ _ _ _ hS2).2.1.1
    rintro _ hp _ hq
    obtain ⟨p', hp', rfl⟩ := hPeq ▸ hp
    obtain ⟨q', hq', rfl⟩ := hPeq ▸ hq
    have hc : p' * q' * p'⁻¹ * q'⁻¹ ∈ twoLift N (sec2P Eb) :=
      mul_mem (mul_mem (mul_mem hp' hq') (inv_mem hp')) (inv_mem hq')
    have hcb : QuotientGroup.mk' N (p' * q' * p'⁻¹ * q'⁻¹) ∈
        Eb ⊓ (A₁.subgroupOf K).map (QuotientGroup.mk' N) := by
      have hpb := mk_mem_of_mem_twoLift hNc hNo hP2b hp'
      have hqb := mk_mem_of_mem_twoLift hNc hNo hP2b hq'
      have h1 := ((hcm.ge (mem_sup_left (inv_mem hqb))).2.2) _ (inv_mem hpb)
      simp only [inv_inv] at h1
      simpa only [map_mul, map_inv] using h1
    obtain ⟨e', he', he'c⟩ := exists_mem_twoLift hNc hNo hE2 hcb.1
    have h1 := injOn_twoLift hNc hNo hP2b (twoLift_mono hNc hNo hE2 hEPb he') hc he'c
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← h1]
    refine ⟨⟨e', he', rfl⟩, ?_⟩
    obtain ⟨a, ha, hae⟩ := hcb.2
    rw [← he'c] at hae
    have h2 : a⁻¹ * e' ∈ N := by
      rw [← QuotientGroup.eq]
      exact hae
    have h3 := mul_mem (mem_subgroupOf.mp ha) (mem_subgroupOf.mp (hNA h2))
    simpa using h3
  ·
    have hKN : sec2K Eb ≤ normalizer (sec2P Eb : Set (↥K ⧸ N)) := by
      unfold sec2K AS81.oUpperTwo
      exact (closure_le _).mpr fun _ hx => hx.1
    rw [hPeq]
    rintro _ ⟨t, ht, rfl⟩
    exact le_normalizer_map _ ⟨t, mem_normalizer_twoLift hNc hNo hP2b
      (hKN (mem_inf.mp (mk_mem_of_mem_twoLift hNc hNo hT2 ht)).2), rfl⟩
  ·
    have hPS' : sec2P Eb ⊔ sec2S ((A₁.subgroupOf K).map (QuotientGroup.mk' N))
        ((R.subgroupOf K).map (QuotientGroup.mk' N)) Eb Fb = sec2P Eb ⊔ Fb := by
      refine le_antisymm (sup_le le_sup_left (sup_le le_sup_right ?_))
        (sup_le_sup_left le_sup_left _)
      exact fun w hw => mem_sup_left (mem_centralizerMod.mp hw).1
    have hPF2 : IsPGroup 2 ↥(sec2P Eb ⊔ Fb) := hT2.to_le (hPS' ▸ hPST)
    have hNb : sec2T Eb T₀b ≤ normalizer ((sec2P Eb ⊔ Fb : Subgroup (↥K ⧸ N)) : Set (↥K ⧸ N)) := by
      rw [← hPS']
      exact fun t ht => mem_normalizer_sup (hT₀P (mem_inf.mp ht).1) (hT₀syl.le (mem_inf.mp ht).1)
    have hlift : (twoLift N (sec2P Eb ⊔ Fb)).map K.subtype = pCoreOf 2 (sec3B A₁ x ⊓
        normalizer (((twoLift N Eb).map K.subtype : Subgroup G) : Set G)) ⊔
          (twoLift N Fb).map K.subtype := by
      rw [twoLift_sup hNc hNo hPF2, Subgroup.map_sup, ← hPeq]
    rw [← hlift]
    rintro _ ⟨t, ht, rfl⟩
    exact le_normalizer_map _ ⟨t, mem_normalizer_twoLift hNc hNo hPF2
      (hNb (mk_mem_of_mem_twoLift hNc hNo hT2 ht)), rfl⟩
  ·
    rintro _ ⟨t, ht, rfl⟩
    exact le_normalizer_map _ ⟨t, mem_normalizer_twoLift hNc hNo hQ2
      (hHTQ (mem_sup_right (mk_mem_of_mem_twoLift hNc hNo hT2 ht))), rfl⟩
  ·
    obtain ⟨hPOK, hidx, -⟩ := h211 _ _ _ _ _ _ hS2
    have hKN : sec2K Eb ≤ normalizer (sec2P Eb : Set (↥K ⧸ N)) := by
      unfold sec2K AS81.oUpperTwo
      exact (closure_le _).mpr fun _ hx => hx.1
    have hNK : normalizer (sec2P Eb : Set (↥K ⧸ N)) ≤ normalizer (sec2K Eb : Set (↥K ⧸ N)) :=
      fun n hn => mem_normalizer_oUpperTwo hn
    have hTsyl : IsSylowOf 2 (sec2T Eb T₀b) (sec2K Eb) :=
      (hT₀all.of_le hT₀P le_top).inf_of_le_normalizer hKN hNK
    have hPcard : Nat.card (sec2P Eb) = 2 ^ 10 := by
      obtain ⟨-, ⟨hEPb, hrel, -⟩, -⟩ := h21 _ _ _ _ _ _ hS2
      have h1 := Subgroup.relIndex_mul_relIndex ⊥ Eb (sec2P Eb) bot_le hEPb
      rw [relIndex_bot_left, relIndex_bot_left, hrel, hS2.frame.cardE] at h1
      rw [← h1]
      norm_num
    have hOodd := AS76b.odd_card_oddCoreIn (sec2K Eb)
    have hOP : AS76b.oddCoreIn (sec2K Eb) ⊓ sec2P Eb = ⊥ :=
      disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by
        rw [hPcard]
        exact Nat.Coprime.pow_right 10 (Nat.coprime_two_right.mpr hOodd)))
    have hPON : sec2P Eb ≤ normalizer (AS76b.oddCoreIn (sec2K Eb) : Set (↥K ⧸ N)) :=
      (le_sup_left.trans hPOK).trans (AS76b.le_normalizer_oddCoreIn _)
    have hcardPO : Nat.card ↥(sec2P Eb ⊔ AS76b.oddCoreIn (sec2K Eb)) =
        Nat.card (AS76b.oddCoreIn (sec2K Eb)) * 2 ^ 10 := by
      rw [sup_comm, AschbacherTheorem3.card_sup_of_le_normalizer hPON hOP, hPcard]
    have hcardK : Nat.card (sec2K Eb) = 2 ^ 13 * (135 * Nat.card (AS76b.oddCoreIn (sec2K Eb))) := by
      have h1 := Subgroup.relIndex_mul_card (sec2P Eb ⊔ AS76b.oddCoreIn (sec2K Eb)) (sec2K Eb)
      rw [inf_eq_left.mpr hPOK, hidx, hcardPO] at h1
      rw [← h1]
      ring
    have hodd : ¬ 2 ∣ 135 * Nat.card (AS76b.oddCoreIn (sec2K Eb)) := by
      rw [Nat.Prime.dvd_mul Nat.prime_two]
      rintro (h | h)
      · norm_num at h
      · exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
    have hfac : (Nat.card (sec2K Eb)).factorization 2 = 13 := by
      rw [hcardK, Nat.factorization_mul (by positivity) (by
          intro h
          exact hodd (h ▸ dvd_zero 2)), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hodd]
    rw [card_map_of_injective hinj, card_twoLift hNc hNo hT2, hTsyl.card_eq, hfac]
  ·
    have hAE2 : IsPGroup 2 ↥((A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊓ Eb) :=
      hE2.to_le inf_le_right
    have hAEQ2 : IsPGroup 2 ↥((A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊓ Eb ⊓ Qb) :=
      hAE2.to_le inf_le_left
    have hEA : (twoLift N Eb).map K.subtype ⊓ A₁ =
        (twoLift N ((A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊓ Eb)).map K.subtype := by
      rw [twoLift_inf_map hNc hNo hNA hE2, inf_comm, map_inf_eq _ _ _ hinj, hA₁map]
    have hEAQ : (twoLift N Eb).map K.subtype ⊓ A₁ ⊓ (twoLift N Qb).map K.subtype =
        (twoLift N ((A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊓ Eb ⊓ Qb)).map K.subtype := by
      rw [hEA, ← map_inf_eq _ _ _ hinj, twoLift_inf hNc hNo hT2 (inf_le_right.trans hET) hQT]
    have hle : twoLift N ((A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊓ Eb ⊓ Qb) ≤
        twoLift N ((A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊓ Eb) :=
      twoLift_mono hNc hNo hAEQ2 inf_le_left
    have hQidx' : ((A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊓ Eb ⊓ Qb).relIndex
        ((A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊓ Eb) = 2 := by
      rw [inf_comm ((A₁.subgroupOf K).map (QuotientGroup.mk' N)) Eb]
      exact hQidx
    rw [hEAQ, hEA, relIndex_map_map_of_injective _ _ hinj]
    have h1 := relIndex_mul_card (twoLift N ((A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊓ Eb ⊓ Qb))
      (twoLift N ((A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊓ Eb))
    rw [inf_eq_left.mpr hle, card_twoLift hNc hNo hAEQ2, card_twoLift hNc hNo hAE2] at h1
    have h2 := relIndex_mul_card ((A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊓ Eb ⊓ Qb)
      ((A₁.subgroupOf K).map (QuotientGroup.mk' N) ⊓ Eb)
    rw [inf_eq_left.mpr inf_le_left, hQidx'] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

end Frame

end Sec3

open Sec3 in
theorem step3Suz_of
    (hstd : Step31Std) (hII : L34HypII) (h11 : Step11)
    (hL34 : L34General)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h21 : Step21)
    (h24 : Step24) (h27 : Step27) (h211 : Step211) (h212 : Step212) (hLQ : Sec2LocalQ) :
    Step3Suz := by
  intro G _ _ A A₁ R x hS hBc hBp hBs
  obtain ⟨gb, Eb, Fb, hS2⟩ :=
    exists_sec2Setting_sec3K hS hstd hII (step14_of h11 hE16) hL34 hBp hBs
  have hN3 : Nat.card (standardComponentOddCore ↥(sec3K A₁ R x)) ∣ 3 := by
    have h1 := Subgroup.card_dvd_of_le (oddCore_sec3K_le_zpowers hS hBc hBp hBs)
    rwa [card_map_of_injective (sec3K A₁ R x).subtype_injective, Nat.card_zpowers,
      hS.order_x] at h1
  exact sec3Suz_of_sec2 hS h21 h24 h27 h211 h212 hLQ (oddCore_sec3K_le_center hS hBc hBp hBs)
    RankTwoSporadic.odd_card_standardComponentOddCore (oddCore_le_A₁ hS hBc hBp hBs) hN3 rfl
    (sec3K_le_centralizer hS) (R_le_sec3K.trans (sec3K_le_normalizer hS)) hS2
    (fun e he heA => exists_sec2P_mem_rightConjugate h11 hE16 h21 hS2 he heA) hBc hBp hBs

end CFSG.ComponentClassification.AS81
