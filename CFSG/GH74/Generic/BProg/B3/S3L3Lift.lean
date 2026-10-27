module

public import CFSG.GH74.Generic.BProg.B3.S3L3KGroup
public import CFSG.GH74.Generic.BProg.B3.FalseCtxS45Comp
public import CFSG.GH74.Generic.BProg.B3.Lemma212Aux
public import CFSG.GH74.Generic.BProg.B1.Lift0
public import CFSG.GH74.Generic.BProg.B3.S3FusionBar

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3L3Lift

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3.S3Fusion CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_le_cx {x y : G} {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G)) :
    K ⊓ centralizer ({y} : Set G) ≤ centralizer ({x} : Set G) :=
  inf_le_left.trans hKC

@[expose] noncomputable def phiY (x y : G) {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G)) :
    ↥(K ⊓ centralizer ({y} : Set G)) →* ↥(S3.imgBar x K) :=
  ((proj x).comp (Subgroup.inclusion (inf_le_cx (y := y) hKC))).codRestrict (S3.imgBar x K) fun w =>
    mem_imgBar.2 ⟨Subgroup.inclusion (inf_le_cx (y := y) hKC) w, (Subgroup.mem_inf.1 w.2).1, rfl⟩

omit [Finite G] in
theorem phiY_coe (x y : G) {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G))
    (w : ↥(K ⊓ centralizer ({y} : Set G))) :
    ((phiY x y hKC w : ↥(S3.imgBar x K)) : CentralizerBar x) = piC x (w : G) := by
  rw [piC_of_mem x (inf_le_cx hKC w.2)]
  rfl

@[expose] noncomputable def yK (x : G) {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G))
    {y : G} (hyK : y ∈ K) : ↥(S3.imgBar x K) :=
  ⟨piC x y, mem_imgBar.2 ⟨⟨y, hKC hyK⟩, hyK, (piC_of_mem x (hKC hyK)).symm⟩⟩

omit [Finite G] in
theorem yK_coe (x : G) {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G)) {y : G}
    (hyK : y ∈ K) : ((yK x hKC hyK : ↥(S3.imgBar x K)) : CentralizerBar x) = piC x y := rfl

theorem phiY_ker_odd (x y : G) {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G)) :
    Odd (Nat.card (phiY x y hKC).ker) := by
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(centralizer ({x} : Set G)))) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have h := B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion (inf_le_cx (y := y) hKC))
    (Subgroup.inclusion_injective _) (pPrimeCore 2 ↥(centralizer ({x} : Set G))) hodd
  have hker : (phiY x y hKC).ker =
      ((QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G)))).comp
        (Subgroup.inclusion (inf_le_cx (y := y) hKC))).ker := by
    unfold phiY
    exact MonoidHom.ker_codRestrict _ _ _
  rw [hker]
  exact Nat.odd_iff.2 (by omega)

theorem phiY_range (x : G) {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G)) {y : G}
    (hyK : y ∈ K) (hy : orderOf y = 2) :
    (phiY x y hKC).range = centralizer ({yK x hKC hyK} : Set ↥(S3.imgBar x K)) := by
  ext c
  constructor
  · rintro ⟨w, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hw : (w : G) * y = y * (w : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 w.2).2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, phiY_coe, yK_coe,
      ← piC_mul x (inf_le_cx hKC w.2) (hKC hyK), ← piC_mul x (hKC hyK) (inf_le_cx hKC w.2), hw]
  · intro hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    obtain ⟨g, hgK, hg⟩ := mem_imgBar.1 c.2
    set θ : ↥K →* CentralizerBar x := (proj x).comp (Subgroup.inclusion hKC) with hθ
    have hodd : Odd (Nat.card (pPrimeCore 2 ↥(centralizer ({x} : Set G)))) :=
      Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
    have hN : Odd (Nat.card θ.ker) := by
      have h : ¬ 2 ∣ Nat.card θ.ker :=
        B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hKC) (Subgroup.inclusion_injective hKC)
          (pPrimeCore 2 ↥(centralizer ({x} : Set G))) hodd
      exact Nat.odd_iff.2 (by omega)
    set k : ↥K := ⟨(g : G), hgK⟩ with hk
    set yh : ↥K := ⟨y, hyK⟩ with hyh
    have hθk : θ k = (c : CentralizerBar x) := hg
    have hθy : θ yh = (yK x hKC hyK : CentralizerBar x) := (piC_of_mem x (hKC hyK)).symm
    have hyh2 : orderOf yh = 2 := by rw [hyh, Subgroup.orderOf_mk]; exact hy
    have hcomm : θ yh * θ k = θ k * θ yh := by
      rw [hθk, hθy]
      exact (congrArg Subtype.val hc).symm
    have hc' : ∀ a ∈ Subgroup.zpowers yh,
        QuotientGroup.mk' θ.ker a * (QuotientGroup.mk k : ↥K ⧸ θ.ker) =
          (QuotientGroup.mk k : ↥K ⧸ θ.ker) * QuotientGroup.mk' θ.ker a := by
      intro a ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      show (QuotientGroup.mk (yh ^ n) : ↥K ⧸ θ.ker) * QuotientGroup.mk k =
        QuotientGroup.mk k * QuotientGroup.mk (yh ^ n)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, MonoidHom.mem_ker]
      have h1 : θ (yh ^ n) * θ k = θ k * θ (yh ^ n) := by
        rw [map_zpow]
        exact ((Commute.zpow_left (show Commute (θ yh) (θ k) from hcomm) n)).eq
      rw [map_mul, map_inv, map_mul, map_mul, h1]
      simp
    obtain ⟨g', hg'1, hg'2⟩ := B1.centralizer_quotient_of_pGroup θ.ker hN
      (B1.isPGroup_two_zpowers_of_orderOf hyh2) hc'
    have hθg' : θ g' = θ k := by
      have h1 : g'⁻¹ * k ∈ θ.ker := QuotientGroup.eq.1 hg'1
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
      exact h1
    have hg'y : (g' : G) * y = y * (g' : G) :=
      (congrArg Subtype.val (hg'2 yh (Subgroup.mem_zpowers yh))).symm
    refine ⟨⟨(g' : G), Subgroup.mem_inf.2
      ⟨g'.2, Subgroup.mem_centralizer_singleton_iff.2 hg'y⟩⟩, ?_⟩
    apply Subtype.ext
    rw [phiY_coe, piC_of_mem x (hKC g'.2)]
    exact hθg'.trans hθk

theorem eq_of_isPCompIn_centralizer {Kt : Type} [Group Kt] [Finite Kt] {u : Kt} {S M : Subgroup Kt}
    (hS : IsPCompIn 2 (centralizer ({u} : Set Kt)) S)
    (hcomm : ∀ a ∈ centralizer ({u} : Set Kt), ∀ b ∈ centralizer ({u} : Set Kt), ⁅a, b⁆ ∈ S)
    (hM : IsPCompIn 2 (centralizer ({u} : Set Kt)) M) : M = S := by
  set H : Subgroup Kt := centralizer ({u} : Set Kt) with hH
  have hperf : ⁅M.subgroupOf H, M.subgroupOf H⁆ = M.subgroupOf H :=
    Subgroup.isPerfect_iff.1
      (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hM.2)
  have h1 : M.subgroupOf H ≤ S.subgroupOf H := by
    have h2 : ⁅M.subgroupOf H, M.subgroupOf H⁆ ≤ S.subgroupOf H := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_subgroupOf]
      exact hcomm a a.2 b b.2
    rwa [hperf] at h2
  have hMS : M ≤ S := fun m hm => h1 (show (⟨m, hM.1 hm⟩ : ↥H) ∈ M.subgroupOf H from hm)
  exact FalseCtxS45Comp.eq_of_le hM hS hMS

structure LayerHyp (x : G) {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G)) {y : G}
    (hyK : y ∈ K) (S : Subgroup ↥(S3.imgBar x K)) (F : Type) [Field F] [Finite F] : Prop where
  odd : Odd (Nat.card F)
  big : 4 ≤ Nat.card F
  equiv : Nonempty (↥S ≃* SL(2, F))
  mem : yK x hKC hyK ∈ S
  comp : IsPCompIn 2 (centralizer ({yK x hKC hyK} : Set ↥(S3.imgBar x K))) S
  uniq : ∀ M : Subgroup ↥(S3.imgBar x K),
    IsPCompIn 2 (centralizer ({yK x hKC hyK} : Set ↥(S3.imgBar x K))) M → M = S

theorem orderOf_yK (x : G) {K : Subgroup G} (hKC : K ≤ centralizer ({x} : Set G)) {y : G}
    (hyK : y ∈ K) (hy : orderOf y = 2) : orderOf (yK x hKC hyK) = 2 := by
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  have hyC : y ∈ centralizer ({x} : Set G) := hKC hyK
  have h1 : yK x hKC hyK * yK x hKC hyK = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, yK_coe, ← piC_mul x hyC hyC, hy2, piC_one]
    rfl
  have h2 : yK x hKC hyK ≠ 1 := by
    intro h
    have h' : proj x ⟨y, hyC⟩ = 1 := by
      have := congrArg Subtype.val h
      rwa [yK_coe, piC_of_mem x hyC] at this
    have := proj_odd x ⟨y, hyC⟩ h'
    rw [Subgroup.orderOf_mk, hy] at this
    exact absurd this (by decide)
  exact orderOf_eq_prime (by rw [pow_two]; exact h1) h2

theorem exists_layerHyp {x : G} {K : Subgroup G} {y : G}
    (hK : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) K) (hyK : y ∈ K) (hy : orderOf y = 2)
    (hshape : BarShape (CentralizerBar x) (xbar x) (S3.imgBar x K)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (S : Subgroup ↥(S3.imgBar x K)),
      LayerHyp x hK.1 hyK S F ∧
      (∀ σ : MulAut ↥(S3.imgBar x K), σ * σ = 1 → (∀ s ∈ S, σ s = s) →
        σ = 1 ∨ σ = MulAut.conj (yK x hK.1 hyK)) := by
  obtain ⟨t, p, f, ht, hp, hp2, h5, hmod⟩ := hshape.model
  have hq3 : QShape3 ↥(S3.imgBar x K) := by
    refine ⟨p, f, hp, hp2, by omega, ?_⟩
    rcases ht with rfl | rfl
    · exact Or.inl hmod
    · exact Or.inr hmod
  have hZ : ∀ z : ↥(S3.imgBar x K), (∀ g : ↥(S3.imgBar x K), g * z = z * g) → z = 1 := by
    intro z hz
    have hmem : z ∈ center ↥(S3.imgBar x K) := Subgroup.mem_center_iff.2 fun g => hz g
    rw [hshape.centerless, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨F, hF, hFin, S, hodd, h5', e, huS, -, hcomm, hSc, hB4⟩ :=
    S3L3KGroup.exists_sl2_component hq3 hZ (orderOf_yK x hK.1 hyK hy)
  exact ⟨F, hF, hFin, S, ⟨hodd, by omega, e, huS, hSc, fun M hM =>
    eq_of_isPCompIn_centralizer hSc hcomm hM⟩, hB4⟩

section Lift

variable {x y : G} {K : Subgroup G} {hKC : K ≤ centralizer ({x} : Set G)} {hyK : y ∈ K}
  {S : Subgroup ↥(S3.imgBar x K)} {F : Type} [Field F] [Finite F]

theorem LayerHyp.exists_comp (hS : LayerHyp x hKC hyK S F) (hy : orderOf y = 2) :
    ∃ L : Subgroup G, IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) L ∧
      ((L.subgroupOf (K ⊓ centralizer ({y} : Set G))).map (phiY x y hKC)) = S := by
  have hker : ¬ 2 ∣ Nat.card (phiY x y hKC).ker :=
    Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 (phiY_ker_odd x y hKC))
  obtain ⟨h1, h2⟩ := B1.exists_isPCompIn_lift_of_odd_ker (phiY x y hKC) hker (Jb := S)
    (by rw [phiY_range x hKC hyK hy]; exact hS.comp)
  exact ⟨_, h1, h2⟩

theorem LayerHyp.image_eq (hS : LayerHyp x hKC hyK S F) (hy : orderOf y = 2) {L : Subgroup G}
    (hL : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) L) :
    (L.subgroupOf (K ⊓ centralizer ({y} : Set G))).map (phiY x y hKC) = S := by
  set W : Subgroup G := K ⊓ centralizer ({y} : Set G) with hW
  set φ : ↥W →* ↥(S3.imgBar x K) := phiY x y hKC with hφ
  have hfs : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hfk : Odd (Nat.card φ.rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact phiY_ker_odd x y hKC
  have hL2 := (TwoThin.isPCompIn_two_iff.mp hL).2
  have himg :=
    CFSG.ComponentClassification.OddKernelTwoComponents.image φ.rangeRestrict hfs hfk _ hL2
  set M : Subgroup ↥(S3.imgBar x K) := (L.subgroupOf W).map φ with hM
  have hMeq : M = ((L.subgroupOf W).map φ.rangeRestrict).map φ.range.subtype := by
    rw [Subgroup.map_map]
    rfl
  have hMsub : M.subgroupOf φ.range = (L.subgroupOf W).map φ.rangeRestrict := by
    rw [hMeq]
    exact Subgroup.comap_map_eq_self_of_injective φ.range.subtype_injective _
  have hMle : M ≤ φ.range := by
    rintro _ ⟨l, _, rfl⟩
    exact ⟨l, rfl⟩
  have hMc : IsPCompIn 2 (centralizer ({yK x hKC hyK} : Set ↥(S3.imgBar x K))) M := by
    rw [← phiY_range x hKC hyK hy]
    exact TwoThin.isPCompIn_two_iff.mpr ⟨hMle, by rw [hMsub]; exact himg⟩
  exact hS.uniq M hMc

theorem LayerHyp.unique_comp (hS : LayerHyp x hKC hyK S F) (hy : orderOf y = 2) {L₁ L₂ : Subgroup G}
    (h₁ : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) L₁)
    (h₂ : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) L₂) : L₁ = L₂ := by
  set W : Subgroup G := K ⊓ centralizer ({y} : Set G) with hW
  set φ : ↥W →* ↥(S3.imgBar x K) := phiY x y hKC with hφ
  have hfs : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hfk : Odd (Nat.card φ.rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact phiY_ker_odd x y hKC
  have e1 := hS.image_eq hy h₁
  have e2 := hS.image_eq hy h₂
  have hmap : ∀ L : Subgroup G, ((L.subgroupOf W).map φ.rangeRestrict).map φ.range.subtype =
      (L.subgroupOf W).map φ := fun L => by
    rw [Subgroup.map_map]
    rfl
  have hmaps : (L₁.subgroupOf W).map φ.rangeRestrict = (L₂.subgroupOf W).map φ.rangeRestrict := by
    apply Subgroup.map_injective φ.range.subtype_injective
    rw [hmap, hmap, e1, e2]
  have := CFSG.ComponentClassification.OddKernelTwoComponents.lift_unique φ.rangeRestrict hfs hfk
    (L₁.subgroupOf W) (L₂.subgroupOf W) (TwoThin.isPCompIn_two_iff.mp h₁).2
    (TwoThin.isPCompIn_two_iff.mp h₂).2 hmaps
  have h3 := Subgroup.subgroupOf_inj.1 this
  rwa [inf_of_le_left h₁.1, inf_of_le_left h₂.1] at h3

theorem LayerHyp.pLayerOf_eq (hS : LayerHyp x hKC hyK S F) (hy : orderOf y = 2) {L : Subgroup G}
    (hL : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) L) :
    pLayerOf 2 (K ⊓ centralizer ({y} : Set G)) = L :=
  le_antisymm (sSup_le fun _ hL' => (hS.unique_comp hy hL' hL).le) (le_sSup hL)

theorem LayerHyp.mem_layer (hS : LayerHyp x hKC hyK S F) (hy : orderOf y = 2) :
    y ∈ pLayerOf 2 (K ⊓ centralizer ({y} : Set G)) := by
  set W : Subgroup G := K ⊓ centralizer ({y} : Set G) with hW
  set φ : ↥W →* ↥(S3.imgBar x K) := phiY x y hKC with hφ
  have hfs : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hfk : Odd (Nat.card φ.rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact phiY_ker_odd x y hKC
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  have hyW : y ∈ W := Subgroup.mem_inf.2 ⟨hyK, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  set yW : ↥W := ⟨y, hyW⟩ with hyWdef
  have hyW2 : yW * yW = 1 := Subtype.ext hy2
  have hrange := phiY_range x hKC hyK hy
  have hSle : S ≤ pLayerOf 2 (centralizer ({yK x hKC hyK} : Set ↥(S3.imgBar x K))) :=
    le_sSup hS.comp
  have hmem : yK x hKC hyK ∈ pLayerOf 2 φ.range := by
    rw [hφ, hrange]
    exact hSle hS.mem
  rw [TwoThin.pLayerOf_two_eq_map] at hmem
  obtain ⟨t, ht, htv⟩ := hmem
  have hφy : φ yW = yK x hKC hyK := by
    apply Subtype.ext
    rw [hφ, phiY_coe]
    rfl
  have hft : φ.rangeRestrict yW = t := Subtype.ext (hφy.trans htv.symm)
  have h1 : φ.rangeRestrict yW ∈ CFSG.ComponentClassification.TwoLayer.subgroup ↥φ.range := hft ▸ ht
  have h2 := Lemma212Aux.mem_twoLayer_of_map_mem φ.rangeRestrict hfs hfk hyW2 h1
  rw [TwoThin.pLayerOf_two_eq_map]
  exact ⟨yW, h2, rfl⟩

theorem pPrimeCore_eq_bot_of_sl2 {Sg : Type} [Group Sg] [Finite Sg] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) (e : Sg ≃* SL(2, F)) : pPrimeCore 2 Sg = ⊥ := by
  have e' : ↥(⊤ : Subgroup Sg) ≃* SL(2, F) := Subgroup.topEquiv.trans e
  have h := B1.PilotS3.inf_pPrimeCore_eq_one (H := Sg) (M := ⊤)
    (B1.PilotS3.isQuasisimple_of_equiv_sl2 h4 e')
    (CFSG.ClassicalInvolution.natCard_center_of_equiv_sl2 hodd e')
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  exact h z trivial hz

theorem LayerHyp.psi_data (hS : LayerHyp x hKC hyK S F) (hy : orderOf y = 2) {L : Subgroup G}
    (hL : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) L) :
    ∃ ψ : ↥L →* ↥S, Function.Surjective ψ ∧ ψ.ker = pPrimeCore 2 ↥L ∧
      ∀ (l : G) (hl : l ∈ L), ((ψ ⟨l, hl⟩ : ↥S) : CentralizerBar x) = piC x l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup G := K ⊓ centralizer ({y} : Set G) with hW
  set φ : ↥W →* ↥(S3.imgBar x K) := phiY x y hKC with hφ
  have himg := hS.image_eq hy hL
  have hLW : L ≤ W := hL.1
  have hmem : ∀ z : ↥L, φ (Subgroup.inclusion hLW z) ∈ S := fun z => by
    rw [← himg]
    exact ⟨Subgroup.inclusion hLW z, z.2, rfl⟩
  set ψ : ↥L →* ↥S := (φ.comp (Subgroup.inclusion hLW)).codRestrict S hmem with hψ
  have hψc : ∀ z : ↥L, (ψ z : ↥(S3.imgBar x K)) = φ (Subgroup.inclusion hLW z) := fun z => rfl
  have hsurj : Function.Surjective ψ := by
    rintro ⟨s, hs⟩
    rw [← himg] at hs
    obtain ⟨w, hw, hws⟩ := hs
    refine ⟨⟨(w : G), hw⟩, Subtype.ext ?_⟩
    rw [hψc]
    exact hws
  have hker : ¬ 2 ∣ Nat.card ψ.ker := by
    have h1 : ψ.ker = φ.ker.comap (Subgroup.inclusion hLW) := by
      rw [hψ, MonoidHom.ker_codRestrict, MonoidHom.comap_ker]
    rw [h1]
    intro h2
    have h3 := Subgroup.card_comap_dvd_of_injective φ.ker (Subgroup.inclusion hLW)
      (Subgroup.inclusion_injective hLW)
    have h4 := phiY_ker_odd x y hKC
    exact (Nat.not_even_iff_odd.2 h4) (even_iff_two_dvd.2 (h2.trans h3))
  obtain ⟨e⟩ := hS.equiv
  have hbot : pPrimeCore 2 ↥S = ⊥ := pPrimeCore_eq_bot_of_sl2 hS.odd hS.big e
  have hcore := (prime_complement_kernel_core_preimage ψ hsurj hker).1
  rw [hbot, MonoidHom.comap_bot] at hcore
  exact ⟨ψ, hsurj, hcore, fun l hl => by
    rw [hψc]
    have := phiY_coe x y hKC (Subgroup.inclusion hLW ⟨l, hl⟩)
    rw [hφ, this]
    rfl⟩

end Lift

end S3L3Lift

end CFSG.GH74.Generic.BProg.B3
