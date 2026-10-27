module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStart
public import CFSG.LocalAnalysis.SteinbergBNGMSNormalRootData
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvBasic
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Adapters.LinearFieldTransport
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamilies

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis
open scoped MatrixGroups

section Quotient

variable {G : Type*} [Group G]

theorem gmsNormalizerQuotient_of_regular_complement {X U D : Subgroup G}
    (hUX : U ≤ X) (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hDX : D ≤ X) (hDN : D ≤ normalizer (U : Set G)) (hN : X ⊓ normalizer (U : Set G) ≤ U ⊔ D)
    (hDcyc : IsCyclic D)
    (hreg : ∀ x ∈ U, x ≠ 1 → ∀ y ∈ U, y ≠ 1 → ∃! d : D, (d : G) * x * (d : G)⁻¹ = y)
    (hU1 : ∃ x ∈ U, x ≠ 1) :
    IsCyclic (GMSNormalizerQuotient X U) ∧ Nat.card (GMSNormalizerQuotient X U) = Nat.card D ∧
      ∀ u v : U, u ≠ 1 → v ≠ 1 →
        ∃! c : GMSNormalizerQuotient X U, gmsQuotConjAct X U c u = v := by
  set N := X ⊓ normalizer (U : Set G) with hNdef
  set K := (X ⊓ centralizer (U : Set G)).subgroupOf N with hKdef
  have hDle : D ≤ N := le_inf hDX hDN
  let ι : D →* N := Subgroup.inclusion hDle
  let ψ : D →* GMSNormalizerQuotient X U := (QuotientGroup.mk' K).comp ι
  have hψact : ∀ (d : D) (u : U),
      ((gmsQuotConjAct X U (ψ d) u : U) : G) = d * u * (d : G)⁻¹ := fun _ _ => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro d hd
    obtain ⟨x, hx, hx1⟩ := hU1
    have hdK : ι d ∈ K := (QuotientGroup.eq_one_iff _).mp hd
    rw [hKdef, mem_subgroupOf] at hdK
    have hdC : (d : G) * x * (d : G)⁻¹ = x := by
      have h1 := mem_centralizer_iff.mp (mem_inf.mp hdK).2 x hx
      change x * (d : G) = (d : G) * x at h1
      rw [← h1, mul_inv_cancel_right]
    obtain ⟨d₀, -, huniq⟩ := hreg x hx hx1 x hx hx1
    exact (huniq d hdC).trans (huniq 1 (by simp)).symm
  have hsurj : Function.Surjective ψ := by
    intro c
    induction c using QuotientGroup.induction_on with
    | H n =>
      have hn : (n : G) ∈ ((U ⊔ D : Subgroup G) : Set G) := hN n.2
      rw [coe_mul_of_right_le_normalizer_left U D hDN] at hn
      obtain ⟨u, hu, d, hd, hud⟩ := hn
      refine ⟨⟨d, hd⟩, QuotientGroup.eq.mpr ?_⟩
      rw [hKdef, mem_subgroupOf]
      have hc : ((ι ⟨d, hd⟩)⁻¹ * n : N) = (d⁻¹ * u * d : G) := by
        change (d : G)⁻¹ * (n : G) = _
        rw [← hud]
        group
      rw [hc]
      have hdu : d⁻¹ * u * d ∈ U := by
        have h1 := (mem_normalizer_iff.mp (inv_mem (hDN hd)) u).mp hu
        rwa [inv_inv] at h1
      exact mem_inf.mpr ⟨hUX hdu, mem_centralizer_iff.mpr fun y hy => hUab y hy _ hdu⟩
  have := hDcyc
  refine ⟨isCyclic_of_surjective ψ hsurj,
    (Nat.card_congr (MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).toEquiv).symm, ?_⟩
  intro u v hu hv
  have hu' : (u : G) ≠ 1 := fun h => hu (Subtype.ext h)
  have hv' : (v : G) ≠ 1 := fun h => hv (Subtype.ext h)
  obtain ⟨d, hd, huniq⟩ := hreg u u.2 hu' v v.2 hv'
  refine ⟨ψ d, Subtype.ext (by rw [hψact]; exact hd), ?_⟩
  intro c hc
  obtain ⟨d', rfl⟩ := hsurj c
  rw [huniq d' (by show (d' : G) * u * (d' : G)⁻¹ = v; rw [← hψact, hc])]

end Quotient

section Model

open CFSG.Blueprint

theorem nonempty_mulEquiv_psl2_of_lieModel {X : Type} [Group X] {f : ℕ}
    (h : LieModel X .PSL 2 2 f) : Nonempty (X ≃* PSL(2, GaloisField 2 f)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with ⟨-, hc⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hc
    exact ⟨e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 f hadm.2.1 hK)⟩
  all_goals exact absurd hn (by decide)

variable {G : Type*} [Group G] [Finite G]

theorem exists_singer_torus_of_psl2 {L V : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* PSL(2, GaloisField 2 f)) (hVL : V ≤ L)
    (hV : ∃ U : Sylow 2 L, (U : Subgroup L) = V.subgroupOf L) :
    IsElementaryAbelian 2 V ∧ Nat.card V = 2 ^ f ∧
      ∃ D : Subgroup G, D ≤ L ∧ IsCyclic D ∧ Nat.card D = 2 ^ f - 1 ∧ V ⊓ D = ⊥ ∧
        L ⊓ normalizer (V : Set G) = V ⊔ D ∧
        ∀ x ∈ V, x ≠ 1 → ∀ y ∈ V, y ≠ 1 → ∃! d : D, (d : G) * x * (d : G)⁻¹ = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := hV
  set ι : PSL(2, GaloisField 2 f) →* G := L.subtype.comp e.symm.toMonoidHom with hιdef
  have hιinj : Function.Injective ι := L.subtype_injective.comp e.symm.injective
  have hιe : ∀ x : L, ι (e x) = x := fun x => by simp [hιdef]
  set U₀ : Sylow 2 PSL(2, GaloisField 2 f) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective U with hU₀def
  have hU₀coe : (U₀ : Subgroup PSL(2, GaloisField 2 f)) = (U : Subgroup L).map e.toMonoidHom :=
    rfl
  have hU₀ : (U₀ : Subgroup PSL(2, GaloisField 2 f)).map ι = V := by
    rw [hU₀coe, Subgroup.map_map]
    have : ι.comp e.toMonoidHom = L.subtype := by ext x; simp [hιdef]
    rw [this, hU, subgroupOf_map_subtype, inf_of_le_left hVL]
  obtain ⟨hU₀el, hU₀card⟩ := CFSG.Walter.psl2_even_sylow_two hf U₀
  obtain ⟨D₀, hD₀cyc, hD₀card, hU₀D₀, hsup, hreg₀⟩ :=
    CFSG.Walter.psl2_even_normalizer_sylow_two hf U₀
  have hD₀N : D₀ ≤ normalizer ((U₀ : Subgroup PSL(2, GaloisField 2 f)) :
      Set PSL(2, GaloisField 2 f)) := by
    rw [← hsup]
    exact le_sup_right
  set D : Subgroup G := D₀.map ι with hDdef
  have hVel : IsElementaryAbelian 2 V := by
    rw [← hU₀]
    exact IsElementaryAbelian.map ι
  have hVcard : Nat.card V = 2 ^ f := by
    rw [← hU₀, Subgroup.card_map_of_injective hιinj, hU₀card]
  have hDL : D ≤ L := by
    rintro _ ⟨y, -, rfl⟩
    exact (e.symm y).2
  have hDN : D ≤ normalizer (V : Set G) := by
    rw [hDdef, ← hU₀]
    exact (Subgroup.map_mono hD₀N).trans (le_normalizer_map ι)
  have hNLV : L ⊓ normalizer (V : Set G) = V ⊔ D := by
    refine le_antisymm (fun x hx => ?_) (sup_le (le_inf hVL le_normalizer) (le_inf hDL hDN))
    obtain ⟨hxL, hxN⟩ := mem_inf.mp hx
    have hyN : e ⟨x, hxL⟩ ∈ normalizer ((U₀ : Subgroup PSL(2, GaloisField 2 f)) :
        Set PSL(2, GaloisField 2 f)) := by
      rw [← comap_map_eq_self_of_injective hιinj (U₀ : Subgroup PSL(2, GaloisField 2 f)),
        ← comap_normalizer_eq_of_le_range (map_le_range ι _), mem_comap, hιe, hU₀]
      exact hxN
    rw [← hsup] at hyN
    have hx' : ι (e ⟨x, hxL⟩) = x := hιe ⟨x, hxL⟩
    rw [← hx', ← hU₀, hDdef, ← Subgroup.map_sup]
    exact mem_map_of_mem ι hyN
  have hDcyc : IsCyclic D := by
    have := hD₀cyc
    exact isCyclic_of_surjective (equivMapOfInjective D₀ ι hιinj)
      (equivMapOfInjective D₀ ι hιinj).surjective
  have hDcard : Nat.card D = 2 ^ f - 1 := by
    rw [hDdef, Subgroup.card_map_of_injective hιinj, hD₀card]
  have hVD : V ⊓ D = ⊥ := by
    rw [← hU₀, hDdef, ← map_inf_eq _ _ ι hιinj, hU₀D₀, Subgroup.map_bot]
  refine ⟨hVel, hVcard, D, hDL, hDcyc, hDcard, hVD, hNLV, ?_⟩
  intro x hx hx1 y hy hy1
  rw [← hU₀] at hx hy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  have hx₀1 : x₀ ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hy₀1 : y₀ ≠ 1 := fun h => hy1 (by rw [h, map_one])
  obtain ⟨d₀, hd₀, huniq⟩ := hreg₀ x₀ hx₀ hx₀1 y₀ hy₀ hy₀1
  refine ⟨⟨ι d₀, mem_map_of_mem ι d₀.2⟩, ?_, ?_⟩
  · change ι d₀ * ι x₀ * (ι d₀)⁻¹ = ι y₀
    rw [← hd₀, map_mul, map_mul, map_inv]
  · rintro ⟨_, ⟨d₁, hd₁, rfl⟩⟩ hd₁'
    have h1 : d₁ * x₀ * d₁⁻¹ = y₀ := hιinj (by
      change ι d₁ * ι x₀ * (ι d₁)⁻¹ = ι y₀ at hd₁'
      rw [map_mul, map_mul, map_inv, hd₁'])
    have h2 := huniq ⟨d₁, hd₁⟩ h1
    exact Subtype.ext (congrArg (fun d : D₀ => ι d) h2)

theorem gmsNormalizerQuotient_of_psl2 {L V : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* PSL(2, GaloisField 2 f)) (hVL : V ≤ L)
    (hV : ∃ U : Sylow 2 L, (U : Subgroup L) = V.subgroupOf L) :
    IsCyclic (GMSNormalizerQuotient L V) ∧ Nat.card (GMSNormalizerQuotient L V) = 2 ^ f - 1 ∧
      ∀ u v : V, u ≠ 1 → v ≠ 1 → ∃! c : GMSNormalizerQuotient L V, gmsQuotConjAct L V c u = v := by
  obtain ⟨hVel, hVcard, D, hDL, hDcyc, hDcard, -, hNLV, hreg⟩ :=
    exists_singer_torus_of_psl2 hf e hVL hV
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVel.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDN : D ≤ normalizer (V : Set G) :=
    le_sup_right.trans (hNLV.symm.le.trans inf_le_right)
  have hV1 : ∃ x ∈ V, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : V = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [hbot, Subgroup.card_bot] at hVcard
    have : 2 ^ 1 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨hQcyc, hQcard, hQreg⟩ :=
    gmsNormalizerQuotient_of_regular_complement hVL hVab hDL hDN hNLV.le hDcyc hreg hV1
  exact ⟨hQcyc, hQcard.trans hDcard, hQreg⟩

theorem exists_inner_of_centralizes_sylow_psl2 {L V : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* PSL(2, GaloisField 2 f)) (hVL : V ≤ L)
    (hV : ∃ U : Sylow 2 L, (U : Subgroup L) = V.subgroupOf L) {x : G}
    (hxN : x ∈ normalizer (L : Set G)) (hxC : x ∈ centralizer (V : Set G)) :
    ∃ r ∈ V, ∀ y ∈ L, x * y * x⁻¹ = r * y * r⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVel, -, -⟩ := exists_singer_torus_of_psl2 hf e hVL hV
  obtain ⟨U, hU⟩ := hV
  have hsimple : IsSimpleGroup L :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (Or.inl ⟨f, hf, ⟨e⟩⟩)
  have hB : CFSG.Open.fusionBenderBorel L (2 ^ f) 1 :=
    (CFSG.Open.bender_psl2_borel_full f hf).map_mulEquiv e.symm
  obtain ⟨hSE, -, -, -, hUcard⟩ := hB U
  have hcardSyl : Nat.card (Sylow 2 L) = Nat.card (U : Subgroup L) + 1 := by
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.card_sylow_eq_of_mulEquiv e 2,
      CFSG.Walter.psl2_even_card_sylow (by omega), hUcard, pow_one]
  have hmemU : ∀ y : L, y ∈ (U : Subgroup L) ↔ (y : G) ∈ V := fun y => by
    rw [hU, mem_subgroupOf]
  have hUab : ∀ a ∈ (U : Subgroup L), ∀ b ∈ (U : Subgroup L), a * b = b * a := by
    intro a ha b hb
    have h1 := congrArg Subtype.val
      (hVel.toIsMulCommutative.is_comm.comm ⟨a, (hmemU a).mp ha⟩ ⟨b, (hmemU b).mp hb⟩)
    exact Subtype.ext h1
  set α : MulAut L := L.normalizerMonoidHom ⟨x, hxN⟩ with hαdef
  have hαapp : ∀ y : L, (α y : G) = x * y * x⁻¹ := fun y =>
    L.normalizerMonoidHom_apply_apply_coe ⟨x, hxN⟩ y
  have hfix : ∀ r ∈ (U : Subgroup L), α r = r := by
    intro r hr
    apply Subtype.ext
    rw [hαapp, ← mem_centralizer_iff.mp hxC r ((hmemU r).mp hr), mul_inv_cancel_right]
  obtain ⟨r, hr, hαr⟩ :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.exists_eq_conj_of_abelian hSE
      hcardSyl hUab α hfix
  refine ⟨r, (hmemU r).mp hr, fun y hy => ?_⟩
  have h1 : (α ⟨y, hy⟩ : G) = ((MulAut.conj r ⟨y, hy⟩ : L) : G) := by rw [hαr]
  rw [hαapp] at h1
  rw [h1]
  rfl

theorem inf_centralizer_sylow_eq_of_psl2 {L V : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* PSL(2, GaloisField 2 f)) (hVL : V ≤ L)
    (hV : ∃ U : Sylow 2 L, (U : Subgroup L) = V.subgroupOf L) :
    L ⊓ centralizer (V : Set G) = V := by
  obtain ⟨hVel, -, -⟩ := exists_singer_torus_of_psl2 hf e hVL hV
  have hZ : center L = ⊥ := by
    let e' : L ≃* SL(2, GaloisField 2 f) := e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
    have h1 : (center L).map e'.toMonoidHom = ⊥ := by
      have h2 : (center L).map e'.toMonoidHom = center SL(2, GaloisField 2 f) :=
        map_center_eq e'
      rw [h2, CFSG.Walter.sl2_center_eq_bot_of_charTwo]
    exact (map_eq_bot_iff_of_injective _ e'.injective).mp h1
  refine le_antisymm (fun x hx => ?_) (le_inf hVL fun x hx =>
    mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hVel.toIsMulCommutative.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩))
  obtain ⟨hxL, hxC⟩ := mem_inf.mp hx
  obtain ⟨r, hr, hxr⟩ :=
    exists_inner_of_centralizes_sylow_psl2 hf e hVL hV (le_normalizer hxL) hxC
  have hrx : r⁻¹ * x ∈ L := mul_mem (inv_mem (hVL hr)) hxL
  have hcen : (⟨r⁻¹ * x, hrx⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : G) * (r⁻¹ * x) = r⁻¹ * x * y
    have h1 := hxr y y.2
    calc (y : G) * (r⁻¹ * x) = r⁻¹ * (r * y * r⁻¹) * x := by group
      _ = r⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = r⁻¹ * x * y := by group
  rw [hZ, mem_bot] at hcen
  have h2 : r⁻¹ * x = 1 := congrArg Subtype.val hcen
  rw [inv_mul_eq_one] at h2
  rw [← h2]
  exact hr

end Model

section Setting

open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem psl2_centralizer_root_of_card_sylow_eq_two {L : Subgroup G} (h : SeitzSetting G L)
    {f : ℕ} (hf : 3 ≤ f) (hL : LieModel L .PSL 2 2 f)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {t : G} (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G))
    {T : Subgroup G} (hTN : T ≤ normalizer (zpowers t : Set G))
    (hT : ∃ P : Sylow 2 (normalizer (zpowers t : Set G)),
      (P : Subgroup _) = T.subgroupOf (normalizer (zpowers t : Set G))) :
    normalizer (zpowers t : Set G) = centralizer ({t} : Set G) ∧
      (∃ U : Sylow 2 L, (U : Subgroup L) = (T ⊓ L).subgroupOf L) ∧
      L ⊓ centralizer ((T ⊓ L : Subgroup G) : Set G) = T ⊓ L ∧
      centralizer ({t} : Set G) ⊓ centralizer ((T ⊓ L : Subgroup G) : Set G) =
        T ⊓ L ⊔ zpowers t ∧
      T ⊓ centralizer ((T ⊓ L : Subgroup G) : Set G) = T ⊓ L ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf2 : 2 ≤ f := by omega
  have hst := h.standardSetting
  have hZ : center L = ⊥ := h.center_eq_bot
  have hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup L := hst.standard
  have hNC := normalizer_zpowers_eq_centralizer_of_involution ht
  have hTH : T ≤ centralizer ({t} : Set G) := hNC ▸ hTN
  have hT' : ∃ P : Sylow 2 (centralizer ({t} : Set G)),
      (P : Subgroup _) = T.subgroupOf (centralizer ({t} : Set G)) := by
    rw [← hNC]
    exact hT
  obtain ⟨-, htT, -, -, ⟨U, hU⟩, -, -, -, -⟩ :=
    sylow_centralizer_start_of_card_sylow_eq_two hstd hZ hS2 htC ht (hst.core t ht) hTH hT'
  obtain ⟨hHM, hLH, -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hstd htC ht
  have hCH := inf_centralizer_eq_zpowers_of_card_sylow_eq_two hstd hS2 htC ht (hst.core t ht)
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2_of_lieModel hL
  have hV : ∃ U : Sylow 2 L, (U : Subgroup L) = (T ⊓ L).subgroupOf L :=
    ⟨U, by rw [hU, inf_subgroupOf_right]⟩
  obtain ⟨hVel, -, -⟩ := exists_singer_torus_of_psl2 hf2 e inf_le_right hV
  have hUab : ∀ x ∈ T ⊓ L, ∀ y ∈ T ⊓ L, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVel.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hUC : T ⊓ L ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun y hy => hUab y hy x hx
  have htCU : zpowers t ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) :=
    zpowers_le.mpr (mem_centralizer_iff.mpr fun y hy =>
      mem_centralizer_iff.mp htC y (mem_inf.mp hy).2)
  have hHU : centralizer ({t} : Set G) ⊓ centralizer ((T ⊓ L : Subgroup G) : Set G) =
      T ⊓ L ⊔ zpowers t := by
    refine le_antisymm (fun x hx => ?_) (sup_le (le_inf (inf_le_right.trans hLH) hUC)
      (le_inf (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) htCU))
    obtain ⟨hxH, hxC⟩ := mem_inf.mp hx
    obtain ⟨r, hr, hxr⟩ :=
      exists_inner_of_centralizes_sylow_psl2 hf2 e inf_le_right hV (hHM hxH) hxC
    have hrx : r⁻¹ * x ∈ zpowers t := by
      rw [← hCH]
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun y hy => ?_,
        mul_mem (inv_mem (hLH (mem_inf.mp hr).2)) hxH⟩
      calc y * (r⁻¹ * x) = r⁻¹ * (r * y * r⁻¹) * x := by group
        _ = r⁻¹ * (x * y * x⁻¹) * x := by rw [hxr y hy]
        _ = r⁻¹ * x * y := by group
    have hx' : x = r * (r⁻¹ * x) := by group
    rw [hx']
    exact mul_mem (mem_sup_left hr) (mem_sup_right hrx)
  refine ⟨hNC, hV, inf_centralizer_sylow_eq_of_psl2 hf2 e inf_le_right hV, hHU, ?_⟩
  refine le_antisymm (fun x hx => ?_) (sup_le (le_inf inf_le_left hUC)
    (le_inf (zpowers_le.mpr htT) htCU))
  rw [← hHU]
  exact mem_inf.mpr ⟨hTH (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩

theorem gmsNormalRootData_of_psl2_of_card_sylow_eq_two {L : Subgroup G} (h : SeitzSetting G L)
    {f : ℕ} (hf : 3 ≤ f) (hL : LieModel L .PSL 2 2 f)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {t : G} (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G))
    {T : Subgroup G} (hTN : T ≤ normalizer (zpowers t : Set G))
    (hT : ∃ P : Sylow 2 (normalizer (zpowers t : Set G)),
      (P : Subgroup _) = T.subgroupOf (normalizer (zpowers t : Set G))) :
    GMSNormalRootData (centralizer (L : Set G)) (zpowers t) L (T ⊓ L) T f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf2 : 2 ≤ f := by omega
  have hst := h.standardSetting
  have hZ : center L = ⊥ := h.center_eq_bot
  have hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup L := hst.standard
  obtain ⟨hNC, hV, -, -, hCTU⟩ :=
    psl2_centralizer_root_of_card_sylow_eq_two h hf hL hS2 ht htC hTN hT
  have hTH : T ≤ centralizer ({t} : Set G) := hNC ▸ hTN
  have hT' : ∃ P : Sylow 2 (centralizer ({t} : Set G)),
      (P : Subgroup _) = T.subgroupOf (centralizer ({t} : Set G)) := by
    rw [← hNC]
    exact hT
  obtain ⟨-, htT, -, -, -, hTU, hUt, hUtn, -⟩ :=
    sylow_centralizer_start_of_card_sylow_eq_two hstd hZ hS2 htC ht (hst.core t ht) hTH hT'
  obtain ⟨-, hLH, hLn, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hstd htC ht
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2_of_lieModel hL
  obtain ⟨hUel, hUcard, -⟩ := exists_singer_torus_of_psl2 hf2 e inf_le_right hV
  refine ⟨hf, CFSG.Open.standardComponentIsStandard.tightlyEmbedded_centralizer hstd,
    ⟨IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← ht]; exact pow_orderOf_eq_one t),
      zpowers_le.mpr htC, exists_sylow_eq_zpowers_of_card_sylow_eq_two hS2 htC ht⟩,
    ⟨hNC ▸ hLH, by rw [hNC]; exact hLn, fun l hl => mem_centralizer_iff.mpr fun y hy => ?_⟩,
    ⟨hUel, inf_le_right, hV, hUcard⟩, gmsNormalizerQuotient_of_psl2 hf2 e inf_le_right hV,
    ⟨hTN, hT, inf_le_left, zpowers_le.mpr htT, hTU, hUt, hCTU, hUtn⟩⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  exact (Commute.zpow_left (mem_centralizer_iff.mp htC l hl).symm k).eq

end Setting

end CFSG.SeitzReduction.RankOne
