module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22RestAut
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22RestPair
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SubnormalE2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnQuiet
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinFusion
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22Basic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecEdge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecFrame
public import CFSG.ClassicalInvolution.SmallCases.A7T22ZStar
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
  CFSG.CGT.PushingUpLit.SolKNA.R4
open scoped commutatorElement

section Pkg


variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {r n : ℕ}

theorem exists_secPkg (h : TwinStdR r n Y R S t) (hRc : tightCore R = R)
    (hZ : Subgroup.center Y = ⊥) {c : Y} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hcm : c ∈ centralizerModOdd ⊤ R) (htc : t ∈ Subgroup.centralizer ({c} : Set Y)) :
    ∃ (ht' : (⟨t, htc⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) ∈ secH R c)
      (S₀ : Sylow 2 ↥(tightCore (secR R c))),
      Q8TwinDatum (tightCore (secR R c)) S₀
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c)) ⟨⟨t, htc⟩, ht'⟩) ∧
      Nonempty (↥(S₀ : Subgroup ↥(tightCore (secR R c))) ≃* QuaternionGroup (2 ^ (r - 2))) ∧
      TightSelfGen (tightCore (secR R c)) ∧ TightOddFree (SecQ R c) ∧
      HypOmegaGen (CoreAssembly.conjClass (tightCore (tightCore (secR R c)))) ∧
      AEmpty (CoreAssembly.conjClass (tightCore (tightCore (secR R c))))
        (tightCore (tightCore (secR R c))) ∧
      Nat.card (SecQ R c) < n := by
  classical
  have hd := h.datum
  have hB2 : IsPGroup 2 ↥(Subgroup.zpowers c) := isPGroup_zpowers_of_mul_self_eq_one hc2 hc1
  have hBR : Subgroup.zpowers c ≤ centralizerModOdd ⊤ R := Subgroup.zpowers_le.mpr hcm
  obtain ⟨S', hS'⟩ := TwinEdge.exists_sylow_le_centralizer hd hB2 hBR
  have hdS := TwinEdge.ofSylow hd S'
  have hS'u : (S' : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({c} : Set Y) :=
    hS'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)))
  obtain ⟨S₁, hd₁, ⟨e₁⟩⟩ := TwinEdge.restrict hdS hS'u
  have hq8 : Nonempty (↥(S₁ : Subgroup (R.subgroupOf (Subgroup.centralizer ({c} : Set Y)))) ≃*
      QuaternionGroup (2 ^ (r - 2))) :=
    ⟨e₁.trans ((Sylow.equiv S' S).trans h.quat.some)⟩
  obtain ⟨ht', S'', hdH, hgenH, hq8H⟩ := exists_secK hd₁ hq8
  set H := subnormalClosure (tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))))
    with hH
  have hHodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hdq := TwinEdge.oddQuot hdH hHodd
  have hgenq := TwinEdge.oddQuot_selfGen (N := classicalInvolutionOddCore ↥H) hgenH
  obtain ⟨e⟩ := hq8H
  have hq8q := (TwinEdge.sylowEquiv hdH hHodd).symm.trans e
  have hOq : TightOddFree (SecQ R c) := CFSG.ABGLocalTools.oddCore_quotient_oddCore_eq_bot
  obtain ⟨S₀, hdc, ⟨e₀⟩⟩ := TwinEdge.toCore hdq
  have hidem := TwinEdge.tightCore_idem (secR R c)
  have hgenc : TightSelfGen (tightCore (secR R c)) := by
    unfold TightSelfGen
    rw [hidem]
    exact hgenq
  have hq8c : Nonempty (↥(S₀ : Subgroup ↥(tightCore (secR R c))) ≃*
      QuaternionGroup (2 ^ (r - 2))) := ⟨e₀.trans hq8q⟩
  have hΩ' := TwinVtx.twinSecHyp_cent hd hRc h.hyp hc2 hc1 hcm
  rw [← hidem] at hΩ'
  have hlt : Nat.card (SecQ R c) < n := by
    have h1 : Nat.card (SecQ R c) ≤ Nat.card ↥H :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2 : Nat.card ↥H ≤ Nat.card ↥(Subgroup.centralizer ({c} : Set Y)) :=
      Subgroup.card_le_card_group H
    have h3 := TwinEdge.card_centralizer_lt_of_center hZ hc1
    rw [← h.card]
    omega
  have hΩ : HypOmegaGen (CoreAssembly.conjClass R) := by
    have := h.hyp; rwa [hRc] at this
  have hA : ∀ M ∈ CoreAssembly.conjClass R, AEmpty (CoreAssembly.conjClass R) M := by
    have := h.aEmpty
    rw [hRc] at this
    rintro _ ⟨g, rfl⟩
    exact aEmpty_conj hΩ.conjInvariant this g
  have hcK : c ∈ Balance.Bootstrap.trivialOnQuot R := ⟨hcm.2.1, fun x hx => hcm.2.2.2 x hx⟩
  have hAE := TwinADescent2.aEmpty_section' hΩ (hA R (CoreAssembly.mem_conjClass_self R)) hB2 hcK
  have hAE' := hAE
  rw [← hidem] at hAE'
  exact ⟨ht', S₀, hdc, hq8c, hgenc, hOq, hΩ', hAE', hlt⟩

section NoTwin

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem not_hasTwin_section (hd : Q8TwinDatum R S t) (hRc : tightCore R = R)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) {c : Y} (hc2 : c * c = 1)
    (hc1 : c ≠ 1) (hcm : c ∈ centralizerModOdd ⊤ R) (htc : t ∈ Subgroup.centralizer ({c} : Set Y))
    (ht' : (⟨t, htc⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) ∈ secH R c)
    (hV : ∀ M ∈ twinSet (CoreAssembly.conjClass R) R,
      c ∈ Balance.Bootstrap.trivialOnQuot M → M = R) :
    ¬ HasTwin (tightCore (secR R c)) := by
  classical
  set C : Subgroup Y := Subgroup.centralizer ({c} : Set Y) with hC
  set H : Subgroup ↥C := secH R c with hHdef
  set KH : Subgroup ↥H := (tightCore (R.subgroupOf C)).subgroupOf H with hKH
  have hΩR : HypOmegaGen (CoreAssembly.conjClass R) := by
    have := hΩ; rwa [hRc] at this
  have hB2 : IsPGroup 2 ↥(Subgroup.zpowers c) := isPGroup_zpowers_of_mul_self_eq_one hc2 hc1
  have hBR : Subgroup.zpowers c ≤ centralizerModOdd ⊤ R := Subgroup.zpowers_le.mpr hcm
  obtain ⟨S', hS'⟩ := TwinEdge.exists_sylow_le_centralizer hd hB2 hBR
  have hS'u : (S' : Subgroup R).map R.subtype ≤ C :=
    hS'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)))
  have hP : ∃ P : Subgroup Y, IsSylow2In P R ∧ P ≤ C := ⟨_, isSylow2In_map_sylow R S', hS'u⟩
  have hF : HypOmegaGen (CoreAssembly.conjClass KH) :=
    TwinEdge.hypOmegaGen_sectionFamily hΩR hP (H := H) (le_subnormalClosure _)
  have hHodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) := hB2
  have hRΩ : R ∈ CoreAssembly.conjClass R := CoreAssembly.mem_conjClass_self R
  have hRtq : R ∈ tqMembers3 (CoreAssembly.conjClass R) c :=
    ⟨hRΩ, ⟨hcm.2.1, fun x hx => hcm.2.2.2 x hx⟩⟩
  have htR : IsUniqueInvolution R t := by
    have := Q8Datum.isUniqueInvolution_core hd; rwa [hRc] at this
  have hK₁eq : tightCore (R.subgroupOf C) = (TwinADescent.coreAt c R).subgroupOf C :=
    TwinExitPf2.tightCore_subgroupOf_cent R c
  have htR' : IsUniqueInvolution (TwinADescent.coreAt c R) t :=
    isUniqueInvolution_coreAt_of_tq hΩR hc2' hRtq htR
  have ht₁ : IsUniqueInvolution (tightCore (R.subgroupOf C)) (⟨t, htc⟩ : ↥C) := by
    rw [hK₁eq]
    exact isUniqueInvolution_subgroupOf htR' (TwinADescent.coreAt_le_centralizer c R)
  have hHle : tightCore (R.subgroupOf C) ≤ H := le_subnormalClosure _
  have ht₂ : IsUniqueInvolution KH (⟨⟨t, htc⟩, ht'⟩ : ↥H) := isUniqueInvolution_subgroupOf ht₁ hHle
  rintro ⟨Jb, hJb, hne⟩
  rw [TwinEdge.tightCore_idem, TwinEdge.tightCore_secR R c] at hJb hne
  have hfam : CoreAssembly.conjClass (KH.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥H))) =
      quotFamily (CoreAssembly.conjClass KH) (classicalInvolutionOddCore ↥H) :=
    (image_conjClass (N := classicalInvolutionOddCore ↥H) KH).symm
  have hJb' : Jb ∈ twinSet (quotFamily (CoreAssembly.conjClass KH) (classicalInvolutionOddCore ↥H))
      (KH.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥H))) := by
    rw [← hfam]; exact hJb
  obtain ⟨Kp, ⟨⟨g, hg⟩, z', hz'K, hz'Kp⟩, hKpne, -⟩ :=
    OddQuot.exists_twin_of_map hF hHodd (CoreAssembly.mem_conjClass_self KH) hJb' hne
  have hz'eq : z' = (⟨⟨t, htc⟩, ht'⟩ : ↥H) := (ht₂.eq hz'K).symm
  have hg' : conjSub g KH = Kp := hg
  rw [← hg'] at hz'Kp
  have hgt : g * (⟨⟨t, htc⟩, ht'⟩ : ↥H) * g⁻¹ = ⟨⟨t, htc⟩, ht'⟩ := by
    have := (ht₂.conj g).eq hz'Kp
    rw [hz'eq] at this
    exact this
  have hgtY : ((g : ↥C) : Y) * t * ((g : ↥C) : Y)⁻¹ = t := by
    have := congrArg (fun x : ↥H => (((x : ↥H) : ↥C) : Y)) hgt
    simpa using this
  have hgC : ((g : ↥C) : Y) * c * ((g : ↥C) : Y)⁻¹ = c := by
    have h1 := (Subgroup.mem_centralizer_singleton_iff.mp (g : ↥C).2)
    calc ((g : ↥C) : Y) * c * ((g : ↥C) : Y)⁻¹ = c * ((g : ↥C) : Y) * ((g : ↥C) : Y)⁻¹ := by
          rw [← h1]
      _ = c := by group
  have hcR : c ∈ Balance.Bootstrap.trivialOnQuot R := ⟨hcm.2.1, fun x hx => hcm.2.2.2 x hx⟩
  have hcRg : c ∈ Balance.Bootstrap.trivialOnQuot (conjSub ((g : ↥C) : Y) R) := by
    have := Balance.Bootstrap.trivialOnQuot_conjSub hcR ((g : ↥C) : Y)
    rwa [hgC] at this
  have hRg : conjSub ((g : ↥C) : Y) R ∈ twinSet (CoreAssembly.conjClass R) R :=
    ⟨⟨_, rfl⟩, t, htR, by
      have := htR.conj ((g : ↥C) : Y)
      rwa [hgtY] at this⟩
  have hRgR : conjSub ((g : ↥C) : Y) R = R := hV _ hRg hcRg
  have hcore : conjSub (g : ↥C) (tightCore (R.subgroupOf C)) = tightCore (R.subgroupOf C) := by
    rw [conjSub_tightCore, conjSub_subgroupOf C (g : ↥C) R, hRgR]
  apply hKpne
  rw [← hg', hKH, conjSub_subgroupOf H g, hcore]

end NoTwin

section Aux

variable {Y : Type} [Group Y] [Finite Y]

theorem tightDatum_of_not_hasTwin {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (hd : Q8TwinDatum R S t) (htc : tightCore R = R) (hno : ¬ HasTwin R) : TightDatum R S t := by
  have hzK : IsUniqueInvolution (tightCore R) t := Q8Datum.isUniqueInvolution_core hd
  have hsing : twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) = {tightCore R} := by
    ext K
    constructor
    · intro hK
      by_contra hne
      exact hno ⟨K, hK, hne⟩
    · intro hK
      rw [Set.mem_singleton_iff] at hK
      subst hK
      exact ⟨CoreAssembly.mem_conjClass_self _, t, hzK, hzK⟩
  have hnormal := (twinSet_eq_singleton_iff (Q3B.conjInvariant_conjClass _)
    (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) (CoreAssembly.mem_conjClass_self _) hzK).mp hsing
  rw [htc] at hnormal
  exact hd.toTightDatum hnormal

theorem twinE4_of_tightE4 {Q : Type} [Group Q] (h : TightE4 Q) : TwinE4 Q := by
  obtain ⟨P, _, f, hs, h2, -, hP⟩ := h
  exact ⟨P, inferInstance, f, hs, h2, hP⟩

theorem mem_normalizer_core {R : Subgroup Y} {c g : Y}
    (hgC : g ∈ Subgroup.centralizer ({c} : Set Y)) (hg : g ∈ Subgroup.normalizer (R : Set Y)) :
    (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) ∈
      Subgroup.normalizer ((tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))) :
        Subgroup ↥(Subgroup.centralizer ({c} : Set Y))) : Set ↥(Subgroup.centralizer ({c} : Set Y))) := by
  have h1 : conjSub (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({c} : Set Y)))
      (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))) =
      R.subgroupOf (Subgroup.centralizer ({c} : Set Y)) := by
    rw [conjSub_subgroupOf (Subgroup.centralizer ({c} : Set Y)) ⟨g, hgC⟩ R]
    exact congrArg (fun K : Subgroup Y => K.subgroupOf (Subgroup.centralizer ({c} : Set Y)))
      (mem_normalizer_iff_conjSub_eq.mp hg)
  exact mem_normalizer_iff_conjSub_eq.mpr (by rw [conjSub_tightCore, h1])

theorem mem_normalizer_secH {R : Subgroup Y} {c g : Y}
    (hgC : g ∈ Subgroup.centralizer ({c} : Set Y)) (hg : g ∈ Subgroup.normalizer (R : Set Y)) :
    (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) ∈
      Subgroup.normalizer ((secH R c : Subgroup ↥(Subgroup.centralizer ({c} : Set Y))) :
        Set ↥(Subgroup.centralizer ({c} : Set Y))) :=
  TwinExitPf2.mem_normalizer_subnormalClosure (mem_normalizer_core hgC hg)

theorem exists_sylow_centralized {R : Subgroup Y} {C : Subgroup Y} {v : ↥C}
    (hvN : v ∈ Subgroup.normalizer ((tightCore (R.subgroupOf C) : Subgroup ↥C) : Set ↥C))
    (hv2 : v * v = 1)
    (hvt : ∀ x ∈ tightCore (R.subgroupOf C), ⁅((v : ↥C) : Y), ((x : ↥C) : Y)⁆ ∈
      CFSG.ClassicalInvolution.Balance.oddCoreIn R) :
    ∃ P : Subgroup ↥C, IsSylow2In P (tightCore (R.subgroupOf C)) ∧ ∀ x ∈ P, v * x * v⁻¹ = x := by
  classical
  have hW2 : IsPGroup 2 ↥(Subgroup.zpowers v) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hv2
  have hWN : Subgroup.zpowers v ≤ Subgroup.normalizer ((tightCore (R.subgroupOf C) :
      Subgroup ↥C) : Set ↥C) := Subgroup.zpowers_le.mpr hvN
  obtain ⟨P, hP, hfix⟩ := AscQuot.exists_sylow_normalized' hW2 hWN
  refine ⟨P, hP, fun x hx => ?_⟩
  have hvP : conjSub v P = P := hfix v (Subgroup.mem_zpowers v)
  have hy : v * x * v⁻¹ * x⁻¹ ∈ P := by
    have h1 : v * x * v⁻¹ ∈ conjSub v P := conj_mem_conjSub hx
    rw [hvP] at h1
    exact P.mul_mem h1 (P.inv_mem hx)
  have hxK : x ∈ tightCore (R.subgroupOf C) := hP.1 hx
  have hcomm := hvt x hxK
  have hodd : Odd (Nat.card (CFSG.ClassicalInvolution.Balance.oddCoreIn R)) := by
    unfold CFSG.ClassicalInvolution.Balance.oddCoreIn
    rw [Subgroup.card_map_of_injective R.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card R
  have h2 : IsPGroup 2 (Subgroup.zpowers (((v * x * v⁻¹ * x⁻¹ : ↥C)) : Y)) := by
    have e : Subgroup.zpowers (((v * x * v⁻¹ * x⁻¹ : ↥C)) : Y) =
        (Subgroup.zpowers (v * x * v⁻¹ * x⁻¹)).map C.subtype :=
      (MonoidHom.map_zpowers C.subtype (v * x * v⁻¹ * x⁻¹)).symm
    rw [e]
    exact (hP.2.1.to_le (Subgroup.zpowers_le.mpr hy)).map _
  have h3 : (((v * x * v⁻¹ * x⁻¹ : ↥C)) : Y) = 1 := by
    refine CFSG.ClassicalInvolution.Asc77.eq_one_of_isPGroup_of_mem_odd hodd ?_ h2
    have : (((v * x * v⁻¹ * x⁻¹ : ↥C)) : Y) = ⁅((v : ↥C) : Y), ((x : ↥C) : Y)⁆ := by
      simp [commutatorElement_def]
    rw [this]
    exact hcomm
  have h4 : v * x * v⁻¹ * x⁻¹ = 1 := Subtype.ext h3
  calc v * x * v⁻¹ = (v * x * v⁻¹ * x⁻¹) * x := by group
    _ = x := by rw [h4, one_mul]

theorem isSylow2In_image_section {R : Subgroup Y} {c : Y}
    {P : Subgroup ↥(Subgroup.centralizer ({c} : Set Y))}
    (hP : IsSylow2In P (tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))))) :
    IsSylow2In ((P.subgroupOf (secH R c)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c)))) (tightCore (secR R c)) := by
  have hHle : tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))) ≤ secH R c :=
    le_subnormalClosure _
  have h1 := IsSylow2In.subgroupOf hP hHle
  let SH := TwinEdge.sylowOf h1
  have h2 := isSylow2In_map_sylow
    (((tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y)))).subgroupOf (secH R c)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))))
    (TwistQ.sylowMap (classicalInvolutionOddCore ↥(secH R c)) SH)
  rw [TwistQ.sylowMap_map_subtype] at h2
  have e : (SH : Subgroup ↥((tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y)))).subgroupOf
      (secH R c))).map ((tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y)))).subgroupOf
        (secH R c)).subtype = P.subgroupOf (secH R c) :=
    Subgroup.map_subgroupOf_eq_of_le h1.1
  rw [e] at h2
  rw [TwinEdge.tightCore_secR R c]
  exact h2

end Aux

section Datum

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem not_mem_tq_of_datum (d : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    u₁ * u₂ ∉ Balance.Bootstrap.trivialOnQuot K ∧ u₁ * u₂ ∉ Balance.Bootstrap.trivialOnQuot K' := by
  have hu₁1 : u₁ ≠ 1 := fun h => by
    have := d.sq₁; rw [h, one_mul] at this; exact d.hz.ne_one this.symm
  have hu₁z : u₁ ≠ z := fun h => by
    have := d.sq₁; rw [h] at this
    have h2 : z = 1 := mul_left_cancel (a := z) (by rw [this, mul_one])
    exact d.hz.ne_one h2
  have hu₂1 : u₂ ≠ 1 := fun h => by
    have := d.sq₂; rw [h, one_mul] at this; exact d.hz.ne_one this.symm
  have hu₂z : u₂ ≠ z := fun h => by
    have := d.sq₂; rw [h] at this
    have h2 : z = 1 := mul_left_cancel (a := z) (by rw [this, mul_one])
    exact d.hz.ne_one h2
  constructor
  · intro hc
    have hu₂t : u₂ ∈ Balance.Bootstrap.trivialOnQuot K :=
      A7T22.le_trivialOnQuot_of_twin d.hyp d.hK'.1 d.mem d.hne d.hzK' d.hz d.hu₂.1
    have hu₁t : u₁ ∈ Balance.Bootstrap.trivialOnQuot K := by
      have := (Balance.Bootstrap.trivialOnQuot K).mul_mem hc
        ((Balance.Bootstrap.trivialOnQuot K).inv_mem hu₂t)
      have e : u₁ * u₂ * u₂⁻¹ = u₁ := by group
      rwa [e] at this
    rcases Sec6Gen.center_two d.hyp d.mem d.hz u₁ d.hu₁.1
      (T7A.isPGroup_zpowers_of_orderOf_four d.hu₁.2) (fun y hy => hu₁t.2 y hy) with h | h
    · exact hu₁1 h
    · exact hu₁z h
  · intro hc
    have hu₁t : u₁ ∈ Balance.Bootstrap.trivialOnQuot K' :=
      A7T22.le_trivialOnQuot_of_twin d.hyp d.mem d.hK'.1 d.hne.symm d.hz d.hzK' d.hu₁.1
    have hu₂t : u₂ ∈ Balance.Bootstrap.trivialOnQuot K' := by
      have := (Balance.Bootstrap.trivialOnQuot K').mul_mem
        ((Balance.Bootstrap.trivialOnQuot K').inv_mem hu₁t) hc
      have e : u₁⁻¹ * (u₁ * u₂) = u₂ := by group
      rwa [e] at this
    rcases Sec6Gen.center_two d.hyp d.hK'.1 d.hzK' u₂ d.hu₂.1
      (T7A.isPGroup_zpowers_of_orderOf_four d.hu₂.2) (fun y hy => hu₂t.2 y hy) with h | h
    · exact hu₂1 h
    · exact hu₂z h

theorem eq_of_mem_twinSet_three (d : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    (hcard : (twinSet Ω K).ncard = 3) : ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃ := by
  have hsub : ({K, K', K₃} : Set (Subgroup G)) ⊆ twinSet Ω K := by
    intro M hM
    rcases hM with rfl | rfl | rfl
    · exact mem_twinSet_self d.mem d.hz
    · exact d.hK'
    · exact d.hK₃
  have h3 : ({K, K', K₃} : Set (Subgroup G)).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨K, K', K₃, d.hne.symm, d.hK₃K.symm, d.hK₃K'.symm, rfl⟩
  have hfin : (twinSet Ω K).Finite := Set.toFinite _
  have := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, h3]) hfin
  intro M hM
  rw [← this] at hM
  simpa using hM

theorem eq_of_mem_twinSet_tq (d : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    (hcard : (twinSet Ω K).ncard = 3) {M : Subgroup G} (hM : M ∈ twinSet Ω K₃)
    (hc : u₁ * u₂ ∈ Balance.Bootstrap.trivialOnQuot M) : M = K₃ := by
  have hM' : M ∈ twinSet Ω K := by
    rw [← twinSet_eq_of_mem_twinSet d.hz d.hK₃]; exact hM
  rcases eq_of_mem_twinSet_three d hcard M hM' with h | h | h
  · exact absurd (h ▸ hc) (not_mem_tq_of_datum d).1
  · exact absurd (h ▸ hc) (not_mem_tq_of_datum d).2
  · exact h

end Datum

end Pkg

section Main


variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {r n : ℕ}

theorem inO2_cent_of_three_twins (hr : 4 ≤ r) (hNo : NoQ16E4) (hList : SmallListR)
    (hO : NoDatumOtherR r) (h6 : ∀ m, TightLargeEdgeSR r m) (hM : Model163R r)
    (h : PerpHypR r n Y R S t)
    (hcard : (twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)).ncard = 3)
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y)) :
    TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y)))
      (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y)))) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := d.hyp
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  have hzK₃ : IsUniqueInvolution K₃ t := d.hzK₃
  have hstd : TwinStdR r n Y R S t :=
    ⟨h.core.card, h.core.simple, h.core.nonab, h.core.datum, h.core.quat, h.core.gen,
      h.core.oddFree, h.core.hyp, h.core.aEmpty, h.core.twin⟩
  obtain ⟨S₀, hstd₀⟩ := hstd.core
  have hRc₀ : tightCore (tightCore R) = tightCore R := TwinEdge.tightCore_idem R
  have hK₃Ω : K₃ ∈ CoreAssembly.conjClass (tightCore (tightCore R)) := by
    rw [hRc₀]; exact d.hK₃.1
  obtain ⟨S₃, hstd₃⟩ := exists_datum_atR hstd₀ hRc₀ hK₃Ω hzK₃
  have hRc₃ : tightCore K₃ = K₃ := TwinVtx.tightCore_eq_of_mem hRc₀ hK₃Ω
  have hcls : CoreAssembly.conjClass K₃ = Ω := TwinVtx.conjClass_eq_of_mem d.hK₃.1
  set c : Y := u₁ * u₂ with hcdef
  have hc2 : c * c = 1 := d.sq_12
  have hc1 : c ≠ 1 := by
    intro h1
    have hu₂ : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hu₂K : u₂ ∈ K := hu₂ ▸ K.inv_mem d.hu₁.1
    have h4dvd : 4 ∣ orderOf u₂ := by rw [d.hu₂.2]
    exact d.hne (eq_of_mem_inf_of_four_dvd hΩ d.hK'.1 d.mem d.hu₂.1 hu₂K h4dvd)
  have t13 : K ≤ Balance.Bootstrap.trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.mem d.hK₃.1 d.hK₃K.symm d.hz hzK₃
  have t23 : K' ≤ Balance.Bootstrap.trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 d.hK₃.1 d.hK₃K'.symm d.hzK' hzK₃
  have hcq3 : c ∈ Balance.Bootstrap.trivialOnQuot K₃ :=
    Subgroup.mul_mem _ (t13 d.hu₁.1) (t23 d.hu₂.1)
  have hcm : c ∈ centralizerModOdd ⊤ K₃ :=
    TwinEdge.mem_centralizerModOdd_of_commutator hc2 fun x hx => hcq3.2 x hx
  have hZ : Subgroup.center Y = ⊥ := h.center_eq_bot
  obtain ⟨ht', S₀', hdc, hq8c, hgenc, hOq, hΩ', hAE', hlt⟩ :=
    exists_secPkg hstd₃ hRc₃ hZ hc2 hc1 hcm htC
  suffices hE2 : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K₃ c))
      (⟨⟨t, htC⟩, ht'⟩ : ↥(secH K₃ c))) from
    tightInO2_oddQuot_of_subnormal (isSubnormal_subnormalClosure _) ht' hE2
  by_contra hnE2
  have hΩ₃ : HypOmegaGen (CoreAssembly.conjClass (tightCore K₃)) := by
    rw [hRc₃, hcls]; exact hΩ
  have hnotw : ¬ HasTwin (tightCore (secR K₃ c)) :=
    not_hasTwin_section hstd₃.datum hRc₃ hΩ₃ hc2 hc1 hcm htC ht' fun M hM hMc =>
      eq_of_mem_twinSet_tq d (by
        rw [twinSet_eq_of_mem_twinSet hU ⟨d.mem, t, hU, d.hz⟩]; exact hcard) (by
          rw [hcls] at hM; exact hM) hMc
  have hidem : tightCore (tightCore (secR K₃ c)) = tightCore (secR K₃ c) :=
    TwinEdge.tightCore_idem _
  obtain ⟨v, hvKK', hv2, hvc, hvu⟩ := exists_involution_of_datum d
  have hvtq : v ∈ Balance.Bootstrap.trivialOnQuot K₃ := (sup_le t13 t23) hvKK'
  have hvC : v ∈ Subgroup.centralizer ({c} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hvc
  have hu₁C : u₁ ∈ Subgroup.centralizer ({c} : Set Y) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc u₁ * c = u₁ * (u₂ * u₁) := by rw [hcdef, d.comm₁₂]
      _ = c * u₁ := by rw [hcdef]; group
  have hu₁tq : u₁ ∈ Balance.Bootstrap.trivialOnQuot K₃ := t13 d.hu₁.1
  have hv'N := mem_normalizer_secH hvC hvtq.1
  have hw'N := mem_normalizer_secH hu₁C hu₁tq.1
  have hv2' : (⟨v, hvC⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) * ⟨v, hvC⟩ = 1 :=
    Subtype.ext hv2
  obtain ⟨P, hP, hPfix⟩ := exists_sylow_centralized (mem_normalizer_core hvC hvtq.1) hv2'
    (fun x hx => hvtq.2 _ (Subgroup.mem_subgroupOf.mp ((tightCore_le _) hx)))
  have hSylV := isSylow2In_image_section hP
  let Sb : Sylow 2 ↥(tightCore (secR K₃ c)) := TwinEdge.sylowOf hSylV
  have hmapS : (Sb : Subgroup ↥(tightCore (secR K₃ c))).map (tightCore (secR K₃ c)).subtype =
      (P.subgroupOf (secH K₃ c)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K₃ c))) :=
    Subgroup.map_subgroupOf_eq_of_le hSylV.1
  have hdc' := TwinEdge.ofSylow hdc Sb
  have hq8c' : Nonempty (↥(Sb : Subgroup ↥(tightCore (secR K₃ c))) ≃*
      QuaternionGroup (2 ^ (r - 2))) := ⟨(Sylow.equiv Sb S₀').trans hq8c.some⟩
  have hdt := tightDatum_of_not_hasTwin hdc' hidem hnotw
  have hcls' : TightClsR r (SecQ K₃ c) (tightCore (secR K₃ c)) Sb
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K₃ c)) ⟨⟨t, htC⟩, ht'⟩) :=
    ⟨hq8c', hgenc, hOq⟩
  have hex := (h.core.tbelow (SecQ K₃ c) hlt _ Sb _ hdt hcls').resolve_right
    (not_goodThreeElement_of_four_le hr hdt hq8c')
  have hE : TightEdgeless (tightCore (secR K₃ c)) := by
    rcases hex with h2 | ⟨he, -⟩ | ⟨he, -⟩ | h4
    · exact absurd h2 hnE2
    · exact he
    · exact he
    · exact absurd (tightInO2_of_twinE4' hr hNo hdc' hq8c' (twinE4_of_tightE4 h4)) hnE2
  let Aq := Perp22.actQuot (secH K₃ c)
  let A₁ : ↥(Subgroup.normalizer ((secH K₃ c : Subgroup ↥(Subgroup.centralizer ({c} : Set Y))) :
      Set ↥(Subgroup.centralizer ({c} : Set Y)))) := ⟨⟨v, hvC⟩, hv'N⟩
  let A₂ : ↥(Subgroup.normalizer ((secH K₃ c : Subgroup ↥(Subgroup.centralizer ({c} : Set Y))) :
      Set ↥(Subgroup.centralizer ({c} : Set Y)))) := ⟨⟨u₁, hu₁C⟩, hw'N⟩
  let A₃ : ↥(Subgroup.normalizer ((secH K₃ c : Subgroup ↥(Subgroup.centralizer ({c} : Set Y))) :
      Set ↥(Subgroup.centralizer ({c} : Set Y)))) := ⟨⟨t, htC⟩, Subgroup.le_normalizer ht'⟩
  have hA₁₁ : A₁ * A₁ = 1 := Subtype.ext hv2'
  have hrel : A₁ * A₂ * A₁⁻¹ * A₂⁻¹ = A₃ := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hvu
  have hV2m : Aq A₁ * Aq A₁ = 1 := by rw [← map_mul, hA₁₁, map_one]
  have hV2 : ∀ x, Aq A₁ (Aq A₁ x) = x := fun x => by
    have := congrArg (fun φ : MulAut (SecQ K₃ c) => φ x) hV2m
    simpa using this
  have hA₃ : ∀ x : SecQ K₃ c,
      Aq A₃ x = QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K₃ c)) ⟨⟨t, htC⟩, ht'⟩ * x *
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K₃ c)) ⟨⟨t, htC⟩, ht'⟩)⁻¹ := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [Perp22.actQuot_apply_mk]
      rfl
  have hWz : Aq A₂ (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K₃ c))
      ⟨⟨t, htC⟩, ht'⟩) = QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K₃ c))
        ⟨⟨t, htC⟩, ht'⟩ := by
    rw [QuotientGroup.mk'_apply, Perp22.actQuot_apply_mk]
    refine congrArg QuotientGroup.mk (Subtype.ext (Subtype.ext ?_))
    show u₁ * t * u₁⁻¹ = t
    calc u₁ * t * u₁⁻¹ = t * u₁ * u₁⁻¹ := by rw [← d.comm_z₁]
      _ = t := by group
  have hcomm : ∀ x, Aq A₁ (Aq A₂ (Aq A₁ ((Aq A₂).symm x))) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K₃ c)) ⟨⟨t, htC⟩, ht'⟩ * x *
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH K₃ c)) ⟨⟨t, htC⟩, ht'⟩)⁻¹ := by
    intro x
    have h1 : Aq A₁ * Aq A₂ * (Aq A₁)⁻¹ * (Aq A₂)⁻¹ = Aq A₃ := by
      rw [← hrel, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hinv : (Aq A₁)⁻¹ = Aq A₁ := inv_eq_of_mul_eq_one_right hV2m
    rw [hinv] at h1
    have h2 := congrArg (fun φ : MulAut (SecQ K₃ c) => φ x) h1
    simp only [MulAut.mul_apply] at h2
    rw [hA₃] at h2
    exact h2
  have hVS : ∀ s ∈ (Sb : Subgroup ↥(tightCore (secR K₃ c))).map
      (tightCore (secR K₃ c)).subtype, Aq A₁ s = s := by
    intro s hs
    rw [hmapS] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    have hpP : ((p : ↥(secH K₃ c)) : ↥(Subgroup.centralizer ({c} : Set Y))) ∈ P :=
      Subgroup.mem_subgroupOf.mp hp
    show Aq A₁ (QuotientGroup.mk' _ p) = QuotientGroup.mk' _ p
    rw [QuotientGroup.mk'_apply, Perp22.actQuot_apply_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (hPfix _ hpP))
  exact false_of_layer_aut hr h.core.below h.core.tbelow hList hO h6 hM hlt hdt hcls' hnE2 hE
    (Aq A₁) (Aq A₂) hV2 hVS hWz hcomm

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest
