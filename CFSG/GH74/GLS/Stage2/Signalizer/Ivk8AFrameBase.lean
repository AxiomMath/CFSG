module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Abs
import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Quot
import CFSG.GH74.GLS.IVK.Lifted.TwoCoverRank
import CFSG.GH74.GLS.Stage1.Thm4.L97a
import CFSG.GH74.GLS.Stage2.Bender.Thm2.L121Cover

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Base

variable {G : Type} [Group G]

theorem aframe_core [Finite G] (H : Subgroup G) : pPrimeCore 2 (HBar H) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot ↥H 2

@[expose] def psiS {S H : Subgroup G} (hSH : S ≤ H) : ↥S →* HBar H :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥H)).comp (Subgroup.inclusion hSH)

theorem psiS_injective [Finite G] {S H : Subgroup G} (hSH : S ≤ H) (hS : IsPGroup 2 ↥S) :
    Function.Injective (psiS hSH) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have hmem : Subgroup.inclusion hSH s ∈ pPrimeCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp hs
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥H)) :=
    CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥H)
  have hdvd : orderOf (⟨Subgroup.inclusion hSH s, hmem⟩ : ↥(pPrimeCore 2 ↥H)) ∣
      Nat.card (pPrimeCore 2 ↥H) := orderOf_dvd_natCard _
  have hord : orderOf (⟨Subgroup.inclusion hSH s, hmem⟩ : ↥(pPrimeCore 2 ↥H)) = orderOf s := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_injective _ (Subgroup.inclusion_injective hSH) s
  rw [hord] at hdvd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS) s
  rw [hk] at hdvd
  have h1 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hcop) hdvd
  exact orderOf_eq_one_iff.mp (hk.trans h1)

theorem psiS_range {S H : Subgroup G} (hSH : S ≤ H) : (psiS hSH).range = barIn H S := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨Subgroup.inclusion hSH s, Subgroup.mem_subgroupOf.mpr s.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.1, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩


@[expose] def zbar (H : Subgroup G) (z : G) (hz : z ∈ H) : HBar H :=
  QuotientGroup.mk (⟨z, hz⟩ : ↥H)

theorem pRank_two_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) : pRank 2 X = pRank 2 Y := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top]
  exact SectionRank.pRank_top_eq_of_mulEquiv one_lt_two e

variable {z : G} {S H V : Subgroup G}

theorem aframe_card [Finite G] (ctx : Stage2Ctx G z Kind.ly S) (hSH : S ≤ H) :
    Nat.card ↥(barIn H S) = 2 ^ 8 := by
  rw [IVK812.card_barIn_two hSH ctx.sylow.isPGroup]
  exact L121.card_S_eq ctx

theorem aframe_sylow [Finite G] (ctx : Stage2Ctx G z Kind.ly S) (hSH : S ≤ H) :
    CFSG.ABGLocalTools.IsSylowOf 2 (barIn H S) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S H := ctx.sylow_top.of_le hSH le_top
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hSyl ⊢
  refine ⟨le_top, IVK812.isPGroup_barIn hSyl.2.1, ?_⟩
  rw [Subgroup.relIndex_top_right]
  intro hdvd
  exact hSyl.2.2
    (hdvd.trans (Subgroup.index_map_dvd (S.subgroupOf H) (QuotientGroup.mk'_surjective _)))

theorem aframe_zb_ord [Finite G] (ctx : Stage2Ctx G z Kind.ly S) (hSH : S ≤ H) :
    orderOf (zbar H z (hSH ctx.z_mem)) = 2 := by
  have h := orderOf_injective (psiS hSH) (psiS_injective hSH ctx.sylow.isPGroup)
    ⟨z, ctx.z_mem⟩
  rw [Subgroup.orderOf_mk, ctx.orderOf_z] at h
  exact h

theorem aframe_zb_mem [Finite G] (ctx : Stage2Ctx G z Kind.ly S) (hSH : S ≤ H) :
    zbar H z (hSH ctx.z_mem) ∈ barIn H S := by
  rw [← psiS_range hSH]
  exact ⟨⟨z, ctx.z_mem⟩, rfl⟩

theorem aframe_zcen [Finite G] (ctx : Stage2Ctx G z Kind.ly S) (hSH : S ≤ H) :
    ∀ u ∈ barIn H S, (∀ t ∈ barIn H S, t * u = u * t) → orderOf u = 2 →
      u = zbar H z (hSH ctx.z_mem) := by
  intro u hu hcomm hord
  rw [← psiS_range hSH] at hu
  obtain ⟨s, rfl⟩ := hu
  have hinj := psiS_injective hSH ctx.sylow.isPGroup
  have hsc : ∀ t : ↥S, t * s = s * t := by
    intro t
    apply hinj
    rw [map_mul, map_mul]
    exact hcomm _ (by rw [← psiS_range hSH]; exact ⟨t, rfl⟩)
  have hs2 : orderOf (s : G) = 2 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective _ hinj s]
    exact hord
  have hsz : (s : G) = z :=
    ctx.data.base.zcen (s : G) s.2 (fun t ht => congrArg Subtype.val (hsc ⟨t, ht⟩)) hs2
  have hsz' : s = ⟨z, ctx.z_mem⟩ := Subtype.ext hsz
  exact congrArg (psiS hSH) hsz'

theorem aframe_v3 (hV : MaxSInv 3 S H V) : IsPGroup 3 ↥(barIn H V) :=
  IVK812.isPGroup_barIn hV.2.1

theorem aframe_v_ne (hV : MaxSInv 3 S H V) (hn : ¬ V ≤ pPrimeCoreOf 2 H) : barIn H V ≠ ⊥ :=
  fun h => hn ((IVK812.barIn_eq_bot_iff hV.1).1 h)

theorem aframe_v_norm (hV : MaxSInv 3 S H V) :
    barIn H S ≤ normalizer ((barIn H V : Subgroup (HBar H)) : Set (HBar H)) :=
  IVK812.barIn_le_normalizer hV.2.2.1


theorem aframe_rank_hi [Finite G] (H : Subgroup G) (h4 : pRank 2 G ≤ 4) :
    pRank 2 (HBar H) ≤ 4 := by
  have hcop : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥H) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥H))
  have hq : pRank 2 (HBar H) = pRank 2 ↥H :=
    GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
      (pPrimeCore 2 ↥H) hcop
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hq]
  calc pRank 2 ↥H = CFSG.Open.pRank 2 (⊤ : Subgroup ↥H) :=
        SectionRank.pRank_eq_open_pRank_top 2 ↥H
    _ = CFSG.Open.pRank 2 H := (SectionRank.pRank_eq_pRank_top_subgroup H).symm
    _ ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) := SectionRank.pRank_mono one_lt_two le_top
    _ = pRank 2 G := (SectionRank.pRank_eq_open_pRank_top 2 G).symm
    _ ≤ 4 := h4

theorem four_le_pRank_S [Finite G] (ctx : Stage2Ctx G z Kind.ly S) : 4 ≤ pRank 2 ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := ctx.data
  cases hd with
  | ly hm =>
    obtain ⟨n, hn, hs⟩ := hm
    have h8 : 8 ≤ n := by omega
    obtain ⟨π, hπ, -⟩ := Stage1.Thm4.L97.exists_twoCover hs.cover
    have h4 : 4 ≤ pRank 2 (CentralizerBar z) := IVK.Lifted.four_le_pRank_of_twoCover hπ h8
    have hcop : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥(Cen z)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
        (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
    have h5 : pRank 2 (CentralizerBar z) = pRank 2 ↥(Cen z) :=
      GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
        (pPrimeCore 2 ↥(Cen z)) hcop
    obtain ⟨Q, hQ⟩ := ctx.sylow.exists_sylow_eq_subgroupOf
    have h6 : pRank 2 ↥(S.subgroupOf (Cen z)) = pRank 2 ↥(Cen z) := by
      have := (SectionRank.pRank_sylow Q).2
      rw [hQ] at this
      exact this
    have h7 : pRank 2 ↥S = pRank 2 ↥(S.subgroupOf (Cen z)) :=
      pRank_two_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe ctx.S_le_Cen).symm
    omega

theorem aframe_rank_lo [Finite G] (ctx : Stage2Ctx G z Kind.ly S) (hSH : S ≤ H) :
    4 ≤ pRank 2 ↥(barIn H S) := by
  have e : ↥S ≃* ↥(barIn H S) :=
    (MonoidHom.ofInjective (psiS_injective hSH ctx.sylow.isPGroup)).trans
      (MulEquiv.subgroupCongr (psiS_range hSH))
  rw [← pRank_two_eq_of_mulEquiv e]
  exact four_le_pRank_S ctx


theorem aframe_v_max [Finite G] (ctx : Stage2Ctx G z Kind.ly S) (hSH : S ≤ H)
    (hV : MaxSInv 3 S H V) :
    ∀ W : Subgroup (HBar H), IsPGroup 3 ↥W → barIn H S ≤ normalizer (W : Set (HBar H)) →
      barIn H V ≤ W → W = barIn H V := by
  intro W hW3 hSW hVW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hVH, hV3, hSV, hVmax⟩ := hV
  set π : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπ
  set W' : Subgroup ↥H := W.comap π with hW'
  set Wt : Subgroup G := W'.map H.subtype with hWt
  have hWtH : Wt ≤ H := Subgroup.map_subtype_le _
  have hVWt : V ≤ Wt := by
    intro v hv
    refine ⟨⟨v, hVH hv⟩, ?_, rfl⟩
    exact hVW (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hv))
  have hSWt : S ≤ normalizer (Wt : Set G) := by
    have h1 : S.subgroupOf H ≤ normalizer (W' : Set ↥H) := fun s hs =>
      Subgroup.le_normalizer_comap π (hSW (Subgroup.mem_map_of_mem π hs))
    intro s hs
    have hsH : s ∈ H := hSH hs
    have hs' : (⟨s, hsH⟩ : ↥H) ∈ S.subgroupOf H := Subgroup.mem_subgroupOf.mpr hs
    exact Subgroup.le_normalizer_map H.subtype ⟨⟨s, hsH⟩, h1 hs', rfl⟩
  have hcop : Nat.Coprime 2 (Nat.card Wt) := by
    rw [hWt, Subgroup.card_map_of_injective H.subtype_injective, hW',
      L121.card_comap_mk' (pPrimeCore 2 ↥H) W]
    obtain ⟨m, hm⟩ := hW3.exists_card_eq
    rw [hm]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right m (by norm_num))
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥H))
  obtain ⟨Q, hQsyl, hVQ, hQS⟩ := DihedralBlueprint.normalized_sylow_containing 2 3
    Nat.prime_two Nat.prime_three S Wt V ctx.sylow.isPGroup hSWt hcop hVWt hV3 hSV
  have hQV : Q = V := hVmax Q (hQsyl.1.trans hWtH) hQsyl.2.1 hQS hVQ
  rw [hQV] at hQsyl
  have hVsyl : CFSG.ABGLocalTools.IsSylowOf 3 V Wt :=
    (DihedralBlueprint.isSylowIn_iff_exists_sylow 3 V Wt).mp hQsyl
  have hndvd : ¬ 3 ∣ V.relIndex Wt := (CFSG.ABGLocalTools.isSylowOf_iff.mp hVsyl).2.2
  have hV' : (V.subgroupOf H).map H.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVH
  have hrel : V.relIndex Wt = (V.subgroupOf H).relIndex W' := by
    conv_lhs => rw [← hV']
    exact Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective
  have hker : π.ker ≤ W' := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    show π x ∈ W
    rw [hx]
    exact W.one_mem
  have hWeq : W'.map π = W := Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective _) W
  have hdvd : (barIn H V).relIndex W ∣ (V.subgroupOf H).relIndex W' := by
    have h1 : (barIn H V).relIndex W =
        ((V.subgroupOf H) ⊔ π.ker).relIndex (W' ⊔ π.ker) := by
      conv_lhs => rw [← hWeq]
      exact Subgroup.relIndex_map_map π (V.subgroupOf H) W'
    rw [h1, sup_of_le_left hker]
    exact Subgroup.relIndex_dvd_of_le_left W' le_sup_left
  have hVW' : barIn H V ≤ W := hVW
  have hpow : ∃ n, (barIn H V).relIndex W = 3 ^ n := by
    have hW3' : IsPGroup 3 ↥W := hW3
    exact hW3'.index ((barIn H V).subgroupOf W)
  obtain ⟨n, hn⟩ := hpow
  have hn0 : n = 0 := by
    by_contra hne
    apply hndvd
    rw [hrel]
    refine dvd_trans ?_ hdvd
    rw [hn]
    exact dvd_pow_self 3 hne
  rw [hn0, pow_zero] at hn
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hn) hVW


structure AFrameEasy (A : Type) [Group A] [Finite A] (zb : A) (Sb Vb : Subgroup A) : Prop where
  core : pPrimeCore 2 A = ⊥
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 Sb ⊤
  card : Nat.card ↥Sb = 2 ^ 8
  rank_lo : 4 ≤ pRank 2 ↥Sb
  rank_hi : pRank 2 A ≤ 4
  zb_ord : orderOf zb = 2
  zb_mem : zb ∈ Sb
  zcen : ∀ u ∈ Sb, (∀ s ∈ Sb, s * u = u * s) → orderOf u = 2 → u = zb
  v3 : IsPGroup 3 ↥Vb
  v_ne : Vb ≠ ⊥
  v_norm : Sb ≤ normalizer (Vb : Set A)
  v_max : ∀ W : Subgroup A, IsPGroup 3 ↥W → Sb ≤ normalizer (W : Set A) → Vb ≤ W → W = Vb

theorem aframe_easy [Finite G] (ctx : Stage2Ctx G z Kind.ly S) (hSH : S ≤ H)
    (hV : MaxSInv 3 S H V) (hn : ¬ V ≤ pPrimeCoreOf 2 H) :
    AFrameEasy (HBar H) (zbar H z (hSH ctx.z_mem)) (barIn H S) (barIn H V) where
  core := aframe_core H
  sylow := aframe_sylow ctx hSH
  card := aframe_card ctx hSH
  rank_lo := aframe_rank_lo ctx hSH
  rank_hi := aframe_rank_hi H ctx.std.rank.2
  zb_ord := aframe_zb_ord ctx hSH
  zb_mem := aframe_zb_mem ctx hSH
  zcen := aframe_zcen ctx hSH
  v3 := aframe_v3 hV
  v_ne := aframe_v_ne hV hn
  v_norm := aframe_v_norm hV
  v_max := aframe_v_max ctx hSH hV

theorem AFrameEasy.toAFrame {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}
    (he : AFrameEasy A zb Sb Vb)
    (invsec : ∀ x : A, orderOf x = 2 → ∀ (Y : Type) [Group Y] [IsSimpleGroup Y],
      ¬ Group.IsSolvable Y → IsSection Y ↥(centralizer ({x} : Set A)) → KindFactorAll Kind.ly Y)
    (four : ∀ U : Subgroup A, IVK.IsFourSubgroup U → ∀ r : ℕ, r.Prime → 5 ≤ r →
      ∀ x ∈ centralizer (U : Set A), orderOf x = r →
        x ∈ pPrimeCoreOf 2 (centralizer (U : Set A)))
    (cbar : ∀ t : A, orderOf t = 2 → ∀ R : Subgroup A, R ≤ centralizer ({t} : Set A) →
      ∃ (n : ℕ) (K : Type) (_ : Group K) (R' : Subgroup K), (n = 10 ∨ n = 11) ∧
        IsDoubleCoverOfAlt K n ∧ Nonempty ((↥R ⧸ pPrimeCore 2 ↥R) ≃* (↥R' ⧸ pPrimeCore 2 ↥R'))) :
    AFrame A zb Sb Vb where
  core := he.core
  sylow := he.sylow
  card := he.card
  rank_lo := he.rank_lo
  rank_hi := he.rank_hi
  zb_ord := he.zb_ord
  zb_mem := he.zb_mem
  zcen := he.zcen
  v3 := he.v3
  v_ne := he.v_ne
  v_norm := he.v_norm
  v_max := he.v_max
  invsec := invsec
  four := four
  cbar := cbar

end Base

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
