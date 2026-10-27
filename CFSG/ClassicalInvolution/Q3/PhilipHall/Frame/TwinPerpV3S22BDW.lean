module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf93Steps
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf93WO2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf16Orbit

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section LayerDW

theorem exists_sylow_ge_lift {G : Type} [Group G] [Finite G] {C : Subgroup G} {H : Subgroup ↥C}
    [H.Normal] {N : Subgroup ↥H} [N.Normal] (hN : N = ⊥) {V : Subgroup (↥H ⧸ N)}
    (hV2 : IsPGroup 2 ↥V) {W : Subgroup G} (hW2 : IsPGroup 2 ↥W) (hWC : W ≤ C)
    (hinv : ∀ w : ↥C, ∀ x y : ↥H, (y : ↥C) = w * (x : ↥C) * w⁻¹ →
      (QuotientGroup.mk x : ↥H ⧸ N) ∈ V → (QuotientGroup.mk y : ↥H ⧸ N) ∈ V) :
    ∃ S₁ : Sylow 2 G, W ≤ (S₁ : Subgroup G) ∧
      ∀ x : ↥H, (QuotientGroup.mk x : ↥H ⧸ N) ∈ V → ((x : ↥C) : G) ∈ (S₁ : Subgroup G) := by
  classical
  have hq : Function.Injective (QuotientGroup.mk' N) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN]
  let ψ : ↥H →* G := C.subtype.comp H.subtype
  let V' : Subgroup ↥H := V.comap (QuotientGroup.mk' N)
  have hV'2 : IsPGroup 2 ↥V' := hV2.comap_of_injective _ hq
  have hVl2 : IsPGroup 2 ↥(V'.map ψ) := hV'2.map ψ
  have key : ∀ w ∈ W, ∀ v ∈ V'.map ψ, w * v * w⁻¹ ∈ V'.map ψ := by
    intro w hw v hv
    obtain ⟨x, hx, rfl⟩ := hv
    let g : ↥C := ⟨w, hWC hw⟩
    let y : ↥H := ⟨g * (x : ↥C) * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ x.2 g⟩
    have hy : (y : ↥C) = g * (x : ↥C) * g⁻¹ := rfl
    refine ⟨y, hinv g x y hy hx, ?_⟩
    show ((y : ↥C) : G) = w * ((x : ↥C) : G) * w⁻¹
    rw [hy]
    rfl
  have hWN : W ≤ Subgroup.normalizer ((V'.map ψ : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · exact key w hw v
    · intro h
      have := key w⁻¹ (W.inv_mem hw) _ h
      simpa [mul_assoc] using this
  obtain ⟨S₁, hS₁⟩ := (hVl2.to_sup_of_normal_left' hW2 hWN).exists_le_sylow
  refine ⟨S₁, le_sup_right.trans hS₁, fun x hx => ?_⟩
  exact hS₁ (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem ψ (show x ∈ V' from hx)))

theorem card_map_inf_le {A B : Type} [Group A] [Group B] [Finite A] (q : A →* B) (K : Subgroup A)
    (V : Subgroup B) : Nat.card ↥(K.map q ⊓ V) ≤ Nat.card ↥(K ⊓ V.comap q) := by
  refine Nat.card_le_card_of_surjective
    (fun x : ↥(K ⊓ V.comap q) =>
      (⟨q x, Subgroup.mem_map_of_mem q x.2.1, x.2.2⟩ : ↥(K.map q ⊓ V))) ?_
  rintro ⟨y, ⟨x, hx, rfl⟩, hyV⟩
  exact ⟨⟨x, hx, hyV⟩, rfl⟩

theorem card_inf_le_sylow_lift {G : Type} [Group G] [Finite G] {C : Subgroup G} {H : Subgroup ↥C}
    {N : Subgroup ↥H} [N.Normal] {V : Subgroup (↥H ⧸ N)} {J S₁ : Subgroup G}
    (hS₁ : ∀ x : ↥H, (QuotientGroup.mk x : ↥H ⧸ N) ∈ V → ((x : ↥C) : G) ∈ S₁) :
    Nat.card ↥(((J.subgroupOf C).subgroupOf H).map (QuotientGroup.mk' N) ⊓ V) ≤
      Nat.card ↥(J ⊓ S₁) := by
  refine (card_map_inf_le _ _ _).trans ?_
  refine Nat.card_le_card_of_injective
    (fun x : ↥(((J.subgroupOf C).subgroupOf H) ⊓ V.comap (QuotientGroup.mk' N)) =>
      (⟨((x.1 : ↥H) : ↥C), x.2.1, hS₁ x.1 x.2.2⟩ : ↥(J ⊓ S₁))) ?_
  intro a b hab
  have h1 := congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext (Subtype.ext h1))

theorem layer_inf_W_mem_USet {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
    (hΩ : HypOmegaGen Ω) (h2g : ∀ J ∈ Ω, IsPGroup 2 ↥J)
    (hN : classicalInvolutionOddCore ↥(coreHull Ω c) = ⊥)
    {V : Subgroup (LSec Ω c)} (hV : WSet (TwinDisc.secFam Ω c) = {V})
    {W : Subgroup G} (hW : W ∈ WSet Ω) (hcW : c ∈ W)
    {J : Subgroup G} (hJ : J ∈ Ω) (hJc : J ≤ Subgroup.centralizer ({c} : Set G)) :
    J ⊓ W ∈ USet Ω := by
  classical
  have hW2 : IsPGroup 2 ↥W := Thompson.isPGroup_of_mem_WSet hW
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) := hW2.to_le (Subgroup.zpowers_le.mpr hcW)
  have hab := TwinThmEW.habel_of_WSet hΩ hW
  have hWC : W ≤ Subgroup.centralizer ({c} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hab w hw c hcW)
  haveI hHn : (coreHull Ω c).Normal := Pf93.normal_coreHull hΩ hc2
  have hΩ' : HypOmegaGen (TwinDisc.secFam Ω c) := TwinDisc.hypOmegaGen_secFam hΩ hc2
  have hVW : V ∈ WSet (TwinDisc.secFam Ω c) := by rw [hV]; exact Set.mem_singleton V
  have hV2 : IsPGroup 2 ↥V := Thompson.isPGroup_of_mem_WSet hVW
  haveI hVn : V.Normal := ⟨fun v hv q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective v
    exact Pf93.sec_invariant_of_unique hΩ hc2 hV (x : ↥(Subgroup.centralizer ({c} : Set G))) z
      (x * z * x⁻¹) rfl hv⟩
  have hinv : ∀ w : ↥(Subgroup.centralizer ({c} : Set G)), ∀ x y : ↥(coreHull Ω c),
      (y : ↥(Subgroup.centralizer ({c} : Set G))) =
        w * (x : ↥(Subgroup.centralizer ({c} : Set G))) * w⁻¹ →
      (QuotientGroup.mk x : LSec Ω c) ∈ V → (QuotientGroup.mk y : LSec Ω c) ∈ V :=
    fun w x y hy hx => Pf93.sec_invariant_of_unique hΩ hc2 hV w x y hy hx
  obtain ⟨S₁, hWS₁, hVS₁⟩ := exists_sylow_ge_lift (C := Subgroup.centralizer ({c} : Set G))
    (H := coreHull Ω c) (N := classicalInvolutionOddCore ↥(coreHull Ω c)) hN hV2 hW2 hWC hinv
  have hJtq : J ∈ tqMembers3 Ω c := mem_tqMembers3_of_le_centralizer hJ hJc
  have hcore : TwinADescent.coreAt c J = J := Sec.coreAt_eq_of_isPGroup (h2g J hJ) hJc
  have hJbar : TwinDisc.secImg Ω c J ∈ TwinDisc.secFam Ω c := TwinDisc.secImg_mem_secFam hJtq
  have hJbarEq : TwinDisc.secImg Ω c J =
      ((J.subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf (coreHull Ω c)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))) := by
    unfold TwinDisc.secImg
    rw [hcore]
  have hJ2 : IsPGroup 2 ↥((J.subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf
      (coreHull Ω c)) :=
    ((h2g J hJ).comap_subtype (K := Subgroup.centralizer ({c} : Set G))).comap_subtype
      (K := coreHull Ω c)
  have hJbar2 : IsPGroup 2 ↥(TwinDisc.secImg Ω c J) := by
    rw [hJbarEq]
    exact hJ2.map _
  have hVJ : IsPGroup 2 ↥(V ⊔ TwinDisc.secImg Ω c J) := hV2.to_sup_of_normal_left hJbar2
  obtain ⟨Sb, hSb⟩ := hVJ.exists_le_sylow
  have hRS : TwinDisc.secImg Ω c J ∈ RSet (TwinDisc.secFam Ω c) :=
    mem_RSet_iff.mpr ⟨_, hJbar, le_rfl, hJbar2, fun R' hR' _ hle => le_antisymm hR' hle⟩
  have h8 := hΩ'.eight_le_of_mem_RSet hRS
  have h2 : 2 < Nat.card ↥(TwinDisc.secImg Ω c J ⊓ (Sb : Subgroup (LSec Ω c))) := by
    rw [inf_eq_left.mpr (le_sup_right.trans hSb)]
    omega
  have hU := TwinThmEW.inf_W_mem_USet_of_card hΩ' hVW (le_sup_left.trans hSb) hJbar h2
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ'.exists_data_of_mem_USet hU
  refine TwinThmEW.inf_W_mem_USet_of_card hΩ hW hWS₁ hJ ?_
  have hcard := card_inf_le_sylow_lift (C := Subgroup.centralizer ({c} : Set G))
    (H := coreHull Ω c) (N := classicalInvolutionOddCore ↥(coreHull Ω c)) (V := V) (J := J)
    (S₁ := (S₁ : Subgroup G)) hVS₁
  rw [← hJbarEq] at hcard
  omega

theorem oddCore_coreHull_eq_bot {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
    (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hOC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G)) = ⊥) :
    classicalInvolutionOddCore ↥(coreHull Ω c) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun n hn => ?_
  have h := oddCore_coreHull_le hΩ hc2 hn
  have h0 : oddCoreOf (Subgroup.centralizer ({c} : Set G)) = ⊥ := by
    show (classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G))).map _ = ⊥
    rw [hOC, Subgroup.map_bot]
  rw [h0] at h
  exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp h))

theorem v3LayerDWO_proved (n : ℕ) :
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
      (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
        (∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) →
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y)) = ⊥ →
        ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
          K ⊓ W ∈ USet (CoreAssembly.conjClass (tightCore R)) → u₁ ∈ W → u₂ ∈ W →
        (∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
          WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V}) →
          ∀ J ∈ CoreAssembly.conjClass (tightCore R),
            J ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) →
              J ⊓ W ∈ USet (CoreAssembly.conjClass (tightCore R)) := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd h2g hOC W hW _ hu₁ hu₂ ⟨V, hV⟩ J hJ hJc
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) :=
    (CoreData.of_S hStd.perp.core).hyp
  have hcW : u₁ * u₂ ∈ W := W.mul_mem hu₁ hu₂
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    (Thompson.isPGroup_of_mem_WSet hW).to_le (Subgroup.zpowers_le.mpr hcW)
  exact layer_inf_W_mem_USet hΩ h2g (oddCore_coreHull_eq_bot hΩ hc2 hOC) hV hW hcW hJ hJc

theorem oddCent_prod_eq_bot {n : ℕ}
    (hSp : TwinCentRes.ModelFactSp62) (hD4 : TwinCentRes.ModelFactD42)
    (h4 : Thm4RTwinBelow 3 n) (hcit : CIT3Below n)
    (hPb : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) (hB : V3Hyp51B n)
    (h5 : V3Fourth n) (h7 : V3Alpha13 n) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hO : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y)) = ⊥ := by
  have hTri := v3Tri_of_thm4 hcit hPb h4
  obtain ⟨K₄, hF⟩ := h5 Y R S t K K' K₃ u₁ u₂ u₃ hStd
  have hα := h7 Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF (hTri Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF)
  have h2g := members_isPGroup_of_std hB hStd hα
  have heq := oddCent_eq_of_datum' hSp hD4 h4 hStd.perp hStd.datum hF.1 hF.2.1 hF.2.2.1
    hF.2.2.2.1 h2g hα
  exact TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn
    (heq.symm.trans (TwinConnT.oddCoreIn_eq_bot_of_classicalOddCore hO))

end LayerDW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
