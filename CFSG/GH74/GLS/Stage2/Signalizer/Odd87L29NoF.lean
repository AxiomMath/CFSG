module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29PRank
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.GH74.GLS.Stage1.Main.BrG2AutC
public import CFSG.GH74.GLS.Stage1.Thm4.L98b
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafC1
public import CFSG.GH74.GLS.IVK.Lifted.FAutBasic
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Two
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12 CFSG.ComponentClassification
open scoped commutatorElement

section Lift0

theorem isTwoComponent_of_isComponent_bar {G : Type} [Group G] [Finite G] (z : G)
    {L : Subgroup (CentralizerBar z)} (hL : IsComponent L) :
    TwoComponents.IsTwoComponent L := by
  have hcore : pPrimeCore 2 (CentralizerBar z) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot Nat.prime_two
  have h1 : HarrisLit.IsTwoComponent L := (HarrisLit.isTwoComponent_iff_isComponent hcore L).mpr hL
  have h2 : IsPComponent 2 L := (HarrisLit.isTwoComponent_iff_isPComponent L).mp h1
  exact (CatalogueBAlternating.pComponent_two_iff L).mp h2

theorem exists_lift_component {G : Type} [Group G] [Finite G] (z : G)
    {L : Subgroup (CentralizerBar z)} (hL : IsComponent L) :
    ∃ K : Subgroup G, IsPCompIn 2 (Cen z) K ∧ barOf z K = L := by
  obtain ⟨K', hK', hmap⟩ := OddKernelTwoComponents.exists_lift (TwoThin.barMk ↥(Cen z))
    TwoThin.barMk_surjective TwoThin.odd_card_ker_barMk L (isTwoComponent_of_isComponent_bar z hL)
  have hsub : (K'.map (Cen z).subtype).subgroupOf (Cen z) = K' :=
    Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective K'
  refine ⟨K'.map (Cen z).subtype, ?_, ?_⟩
  · rw [TwoThin.isPCompIn_two_iff]
    exact ⟨Subgroup.map_subtype_le _, by rw [hsub]; exact hK'⟩
  · show ((K'.map (Cen z).subtype).subgroupOf (Cen z)).map (toBar z) = L
    rw [hsub]
    exact hmap

end Lift0

section Lift
variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] noncomputable def phiK' {K : Subgroup G} (hK : K ≤ Cen z) : ↥K →* ↥(barOf z K) where
  toFun x := ⟨toBar z ⟨(x : G), hK x.2⟩, ⟨⟨(x : G), hK x.2⟩, x.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (toBar z)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (toBar z) ⟨(x : G), hK x.2⟩ ⟨(y : G), hK y.2⟩

omit [Finite G] in
theorem phiK'_surjective {K : Subgroup G} (hK : K ≤ Cen z) : Function.Surjective (phiK' hK) := by
  rintro ⟨_, c, hc, rfl⟩
  exact ⟨⟨(c : G), hc⟩, rfl⟩

omit [Finite G] in
theorem phiK'_apply {K : Subgroup G} (hK : K ≤ Cen z) (k : ↥K) :
    (phiK' hK k : CentralizerBar z) = toBar z ⟨(k : G), hK k.2⟩ := rfl

theorem phiK'_ker {K : Subgroup G} (hK : IsPCompIn 2 (Cen z) K) :
    (phiK' hK.1).ker = pPrimeCore 2 ↥K := by
  ext x
  have hiff : x ∈ (phiK' hK.1).ker ↔ (x : G) ∈ Stage1.Thm3.Sec5.Oz z := by
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : toBar z ⟨(x : G), hK.1 x.2⟩ = 1 := by
        have := congrArg Subtype.val h
        exact this
      exact Stage1.Thm4.mem_Oz_iff.mpr ((QuotientGroup.eq_one_iff _).1 h1)
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).2 (Stage1.Thm4.mem_Oz_iff.mp h)
  rw [hiff]
  constructor
  · intro hx
    have : (x : G) ∈ pPrimeCoreOf 2 K := Stage1.Thm3.Sec7.Leaf.Oz_inf_le hK.1 ⟨x.2, hx⟩
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  · intro hx
    exact Stage1.Thm3.Sec5.pPrimeCoreOf_le_Oz hK ⟨x, hx, rfl⟩

@[expose] noncomputable def hatEquivBarOf {K : Subgroup G} (hK : IsPCompIn 2 (Cen z) K) :
    (↥K ⧸ pPrimeCore 2 ↥K) ≃* ↥(barOf z K) :=
  (QuotientGroup.quotientMulEquivOfEq (phiK'_ker hK).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (phiK' hK.1) (phiK'_surjective hK.1))

theorem hatEquivBarOf_mk {K : Subgroup G} (hK : IsPCompIn 2 (Cen z) K) (k : ↥K) :
    hatEquivBarOf hK (QuotientGroup.mk k) = phiK' hK.1 k := rfl

omit [Finite G] in
theorem map_conj_cen_eq {c : G} (hc : c ∈ Cen z) :
    (Cen z).map (MulAut.conj c).toMonoidHom = Cen z := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hx) (Subgroup.inv_mem _ hc)
  · intro hy
    refine ⟨c⁻¹ * y * c, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hy) hc, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem barOf_map_conj {K : Subgroup G} {c : G} (hc : c ∈ Cen z) :
    barOf z (K.map (MulAut.conj c).toMonoidHom) =
      (barOf z K).map (MulAut.conj (toBar z ⟨c, hc⟩)).toMonoidHom := by
  ext y
  rw [Stage1.Thm4.mem_barOf_iff]
  constructor
  · rintro ⟨x, ⟨k₀, hk₀, hkx⟩, rfl⟩
    have hkx' : c * k₀ * c⁻¹ = (x : G) := by simpa [MulAut.conj_apply] using hkx
    have hkC : k₀ ∈ Cen z := by
      have : k₀ = c⁻¹ * (x : G) * c := by rw [← hkx']; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) x.2) hc
    refine ⟨toBar z ⟨k₀, hkC⟩, ⟨⟨k₀, hkC⟩, hk₀, rfl⟩, ?_⟩
    show toBar z ⟨c, hc⟩ * toBar z ⟨k₀, hkC⟩ * (toBar z ⟨c, hc⟩)⁻¹ = toBar z x
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hkx'
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨k, hk, rfl⟩ := (Stage1.Thm4.mem_barOf_iff).1 hw
    refine ⟨⟨c * (k : G) * c⁻¹,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hc k.2) (Subgroup.inv_mem _ hc)⟩,
      ⟨(k : G), hk, by simp [MulAut.conj_apply]⟩, ?_⟩
    show toBar z _ = toBar z ⟨c, hc⟩ * toBar z k * (toBar z ⟨c, hc⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {K : Subgroup G} {c : G}
    (h : K.map (MulAut.conj c).toMonoidHom = K) : c ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨k, hk, hky⟩ := hy
    have : k = y := by
      have := congrArg (fun t => c⁻¹ * t * c) hky
      simpa [MulAut.conj_apply, mul_assoc] using this
    rwa [this] at hk

theorem mem_normalizer_of_toBar_mem {K : Subgroup G} (hK : IsPCompIn 2 (Cen z) K) {c : G}
    (hc : c ∈ Cen z)
    (hn : toBar z ⟨c, hc⟩ ∈
      normalizer ((barOf z K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z))) :
    c ∈ normalizer (K : Set G) := by
  have hK₂ : IsPCompIn 2 (Cen z) (K.map (MulAut.conj c).toMonoidHom) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hK c
    rwa [map_conj_cen_eq hc] at this
  have himg : barOf z (K.map (MulAut.conj c).toMonoidHom) = barOf z K := by
    rw [barOf_map_conj hc]
    exact map_conj_eq_of_mem_normalizer hn
  obtain ⟨hKC, hK2⟩ := TwoThin.isPCompIn_two_iff.mp hK
  obtain ⟨hK₂C, hK₂2⟩ := TwoThin.isPCompIn_two_iff.mp hK₂
  have hEq := OddKernelTwoComponents.lift_unique (TwoThin.barMk ↥(Cen z)) TwoThin.barMk_surjective
    TwoThin.odd_card_ker_barMk _ _ hK₂2 hK2 (by
      show ((K.map (MulAut.conj c).toMonoidHom).subgroupOf (Cen z)).map (toBar z) =
        (K.subgroupOf (Cen z)).map (toBar z)
      exact himg)
  have h := Subgroup.subgroupOf_inj.mp hEq
  rw [inf_eq_left.mpr hK₂C, inf_eq_left.mpr hKC] at h
  exact mem_normalizer_of_map_conj_eq h

omit [Finite G] in
theorem inducedQuotAut_mk_aux (K : Subgroup G) (N : Subgroup ↥K) [N.Characteristic]
    (x : normalizer (K : Set G)) (k : ↥K) :
    inducedQuotAut K N x (QuotientGroup.mk k) =
      QuotientGroup.mk ⟨(x : G) * k * (x : G)⁻¹, (mem_normalizer_iff.1 x.2 k).1 k.2⟩ :=
  rfl

theorem congr_inducedQuotAut {K : Subgroup G} (hK : IsPCompIn 2 (Cen z) K) {u : G}
    (hu : u ∈ Cen z) (hx : u ∈ normalizer (K : Set G))
    (hn : toBar z ⟨u, hu⟩ ∈
      normalizer ((barOf z K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z))) :
    MulAut.congr (hatEquivBarOf hK) (inducedQuotAut K (pPrimeCore 2 ↥K) ⟨u, hx⟩) =
      Stage1.Main.actOnK (barOf z K) (toBar z ⟨u, hu⟩) hn := by
  ext y
  obtain ⟨q, rfl⟩ := (hatEquivBarOf hK).surjective y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [inducedQuotAut_mk_aux, hatEquivBarOf_mk, hatEquivBarOf_mk]
  show (phiK' hK.1 _ : CentralizerBar z) = toBar z ⟨u, hu⟩ * (phiK' hK.1 k : CentralizerBar z) *
    (toBar z ⟨u, hu⟩)⁻¹
  rw [phiK'_apply, phiK'_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

end Lift

section Main
variable {G : Type} [Group G] [Finite G] {z : G}

theorem isKGroupNative_bar {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S) :
    IsKGroupNative (CentralizerBar z) := by
  have hz : orderOf z = 2 := ctx.central.1
  have hC : IsKGroupNative ↥(Cen z) :=
    ctx.std.kps.isKGroupNative_of_ne_top
      (centralizer_involution_ne_top ctx.std.kps.1 ctx.std.kps.2.1 hz)
  exact SectionRank.IsKGroupCat.quotient hC _

omit [Finite G] in
theorem actOnK_mul_self {X : Type} [Group X] {K : Subgroup X} {s : X}
    (hs : s ∈ normalizer (K : Set X))
    (h : s * s = 1) : Stage1.Main.actOnK K s hs * Stage1.Main.actOnK K s hs = 1 := by
  ext k
  simp only [MulAut.mul_apply, MulAut.one_apply]
  show s * (s * (k : X) * s⁻¹) * s⁻¹ = k
  have : s * s = 1 := h
  calc s * (s * (k : X) * s⁻¹) * s⁻¹ = (s * s) * (k : X) * (s * s)⁻¹ := by group
    _ = k := by rw [this]; simp

theorem not_fixedCond_actOnK {k : Kind} {S : Subgroup G} (ctx : Stage2Ctx G z k S) {q : ℕ}
    (hodd : Odd q) (h4 : 4 ≤ q) {L : Subgroup (CentralizerBar z)} (hL : IsComponent L)
    (hsl : HasSL2Model ↥L (fun r => r = q)) {u : G} (huS : u ∈ S) (hu : u ∈ Cen z)
    (hu2 : u * u = 1) (hn : toBar z ⟨u, hu⟩ ∈ normalizer (L : Set (CentralizerBar z)))
    (hne : Stage1.Main.actOnK L (toBar z ⟨u, hu⟩) hn ≠ 1) :
    ¬ IVK.Lifted.FixedCond ↥L (Stage1.Main.actOnK L (toBar z ⟨u, hu⟩) hn) := by
  intro hfc
  obtain ⟨K, hK, hbar⟩ := exists_lift_component z hL
  subst hbar
  have hx := mem_normalizer_of_toBar_mem hK hu hn
  set Φ := hatEquivBarOf hK with hΦ
  have hfcK : IVK.Lifted.FixedCond (↥K ⧸ pPrimeCore 2 ↥K)
      (inducedQuotAut K (pPrimeCore 2 ↥K) ⟨u, hx⟩) := by
    apply IVK.Lifted.fixedCond_of_congr Φ
    rw [congr_inducedQuotAut hK hu hx hn]
    exact hfc
  obtain ⟨hq, hZ, hinv⟩ := sl2_model_facts hodd h4 hsl
  have hLeven : Even (Nat.card ↥(barOf z K)) := by
    have h2 : Nat.card ↥(center ↥(barOf z K)) ∣ Nat.card ↥(barOf z K) :=
      Subgroup.card_subgroup_dvd_card _
    rw [hZ] at h2
    exact even_iff_two_dvd.mpr h2
  have hinv' : ∀ x y : ↥(barOf z K), orderOf x = 2 → orderOf y = 2 → x = y := by
    intro x y hx2 hy2
    exact Subtype.ext (hinv x x.2 y y.2 (by rw [Subgroup.orderOf_coe]; exact hx2)
      (by rw [Subgroup.orderOf_coe]; exact hy2))
  have hrK : CFSG.pRank 2 ↥K = 1 :=
    pRank_two_eq_one_of_odd_cover (phiK' hK.1) (phiK'_surjective hK.1)
      (by rw [phiK'_ker hK]; exact TwoThin.odd_card_pPrimeCore _) hLeven hinv'
  have hQr : CFSG.pRank 2 (↥K ⧸ pPrimeCore 2 ↥K) = 1 :=
    pRank_two_eq_one_of_odd_cover Φ.toMonoidHom Φ.surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr Φ.injective, Subgroup.card_bot]; exact odd_one)
      hLeven hinv'
  have hQq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    LocalCores.isQuasisimple_of_mulEquiv Φ.symm hq
  have hQk : IsKGroupNative (↥K ⧸ pPrimeCore 2 ↥K) :=
    SectionRank.IsKGroupCat.of_mulEquiv
      (SectionRank.IsKGroupCat.subgroup (isKGroupNative_bar ctx) _) Φ
  have hφsq : inducedQuotAut K (pPrimeCore 2 ↥K) ⟨u, hx⟩ *
      inducedQuotAut K (pPrimeCore 2 ↥K) ⟨u, hx⟩ = 1 := by
    apply (MulAut.congr Φ).injective
    rw [map_mul, congr_inducedQuotAut hK hu hx hn, map_one]
    exact actOnK_mul_self hn (by
      rw [← map_mul]
      have : (⟨u, hu⟩ * ⟨u, hu⟩ : ↥(Cen z)) = 1 := Subtype.ext hu2
      rw [this, map_one])
  have hind : InducesFAut u K :=
    ⟨hx, IVK.Lifted.isFAutomorphism_of_fixedCond hQq hQk hQr hφsq hfcK⟩
  have hcent := ctx.detail.no_fAut u huS K hK hrK hind
  apply hne
  ext y
  obtain ⟨c, hcK, hcy⟩ := Stage1.Thm4.mem_barOf_iff.mp y.2
  have hcomm : ⁅(c : G), u⁆ ∈ pPrimeCoreOf 2 K := hcent.2.2 (c : G) hcK
  have hOz : ⁅(c : G), u⁆ ∈ Stage1.Thm3.Sec5.Oz z :=
    Stage1.Thm3.Sec5.pPrimeCoreOf_le_Oz hK hcomm
  have hcx : ⁅(c : G), u⁆ ∈ Cen z := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem c.2 hu) (inv_mem c.2)) (inv_mem hu)
  have h1 : toBar z ⟨⁅(c : G), u⁆, hcx⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Stage1.Thm4.mem_Oz_iff.mp hOz)
  have e : (⟨⁅(c : G), u⁆, hcx⟩ : ↥(Cen z)) = ⁅c, (⟨u, hu⟩ : ↥(Cen z))⁆ := rfl
  rw [e, map_commutatorElement] at h1
  have h2 := commutatorElement_eq_one_iff_mul_comm.1 h1
  show toBar z ⟨u, hu⟩ * (y : CentralizerBar z) * (toBar z ⟨u, hu⟩)⁻¹ = y
  rw [← hcy, ← h2]
  simp

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
