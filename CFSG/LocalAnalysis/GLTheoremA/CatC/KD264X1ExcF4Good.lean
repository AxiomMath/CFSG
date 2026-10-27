module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264X1ExcF4Red
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpMain
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsEndNode
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsSylow
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplit
public import CFSG.Assembly.Subnormal
public import CFSG.GroupTheory.PLayer.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.Holt.Centralizer
public import CFSG.LargeExtraspecial.S4CEA6Basic
public import CFSG.LargeExtraspecial.S4CESmallThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightSep
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockCensus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SLModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLie
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SpModel
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec19.Step1914E
public import CFSG.RankThree.PartTwo.Sec19.Steps195
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
public import Certificates.Certificate19800

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open

namespace X1F4

theorem centralizer_sup_eq {G : Type*} [Group G] (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun g hg => h g (Subgroup.mem_sup_left hg), fun g hg => h g (Subgroup.mem_sup_right hg)⟩
  · rintro ⟨hA, hB⟩ g hg
    have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) :=
      sup_le (fun g hg => Subgroup.mem_centralizer_singleton_iff.2 (hA g hg))
        (fun g hg => Subgroup.mem_centralizer_singleton_iff.2 (hB g hg))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

theorem map_subtype_centralizer {G : Type*} [Group G] (H : Subgroup G) (F : Subgroup H) :
    (Subgroup.centralizer (F : Set H)).map H.subtype =
      H ⊓ Subgroup.centralizer ((F.map H.subtype : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hy z hz)
  · rintro ⟨hxH, hx⟩
    refine ⟨⟨x, hxH⟩, Subgroup.mem_centralizer_iff.2 fun z hz => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 hx _ ⟨z, hz, rfl⟩

section One

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem sp_core_one (f : LinearMap.BilinForm (ZMod 2) W) (hfalt : f.IsAlt)
    (hfnd : f.Nondegenerate) (n : ℕ) (hn : 3 ≤ n) (hdim : Module.finrank (ZMod 2) W = 2 * n)
    (E' : Subgroup ↥(TauCeti.BilinForm.isometryGroup f)) [Fintype E']
    (hE' : IsElemAbelian 3 E') (hcard : Fintype.card E' = 3 ^ n) :
    ∃ F' : Subgroup ↥(TauCeti.BilinForm.isometryGroup f), F' ≤ E' ∧ F' ≠ ⊥ ∧
      ∃ L' : Subgroup ↥(TauCeti.BilinForm.isometryGroup f),
        CFSG.Open.IsSubnormal L'
          (Subgroup.centralizer (F' : Set ↥(TauCeti.BilinForm.isometryGroup f))) ∧
        Nonempty (↥L' ≃* alternatingGroup (Fin 6)) := by
  classical
  let EΓ : Subgroup (W ≃ₗ[ZMod 2] W) := E'.map (TauCeti.BilinForm.isometryGroup f).subtype
  haveI : Fintype EΓ := Fintype.ofFinite _
  have hEΓ : IsElemAbelian 3 EΓ :=
    X1Sp.isElemAbelian_map_hom 3 (TauCeti.BilinForm.isometryGroup f).subtype hE'
  have hcardΓ : Fintype.card EΓ = 3 ^ n := by
    rw [← hcard]
    exact (Fintype.card_congr (Subgroup.equivMapOfInjective E'
      (TauCeti.BilinForm.isometryGroup f).subtype Subtype.val_injective).toEquiv).symm
  have hGmem : ∀ g ∈ EΓ, g ∈ TauCeti.BilinForm.isometryGroup f := by
    intro g hg
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hg
    exact y.2
  have hEf : ∀ g ∈ EΓ, ∀ x y, f (g x) (g y) = f x y := by
    intro g hg x y
    exact (TauCeti.BilinForm.mem_isometryGroup_iff.1 (hGmem g hg)) x y
  obtain ⟨X, ρ, hdim2, hind, hsup, hinv, hmem, hcyc, hfix, hpow, hsep⟩ :=
    X1Sp.sp_struct EΓ hEΓ n hdim hcardΓ
  choose e heE hact using hsep
  let D : X1Sp.PlaneData EΓ n :=
    { X := X, ρ := ρ, e := e, dim2 := hdim2, indep := hind, sup_eq := hsup, inv := hinv,
      memE := hmem, cyc := hcyc, fixfree := hfix, pow := hpow, emem := heE, eact := hact }
  have hn2 : 2 ≤ n := by omega
  have hSub : CFSG.Open.IsSubnormal (D.Lg f hn2) (D.Cg f) :=
    D.isSubnormal_Lg_Cg f hEf hfalt hfnd hEΓ hn2
  have hIso := D.Lg_iso_alt f hEf hfalt hfnd hn2
  have hCG : D.Cg f ≤ TauCeti.BilinForm.isometryGroup f := inf_le_right
  have hLG : D.Lg f hn2 ≤ TauCeti.BilinForm.isometryGroup f :=
    le_trans (le_trans (Subgroup.map_le_range _ _) (D.Hg_le_Cg f hEf hfalt hn2)) hCG
  let F' : Subgroup ↥(TauCeti.BilinForm.isometryGroup f) :=
    D.fixU.subgroupOf (TauCeti.BilinForm.isometryGroup f)
  have hfixE : ∀ g ∈ D.fixU, g ∈ EΓ := fun g hg => hg.1
  have hF'E : F' ≤ E' := by
    intro x hx
    have hx' : (x : W ≃ₗ[ZMod 2] W) ∈ D.fixU := hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'.1
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  let i2 : Fin n := ⟨2, by omega⟩
  have hi2 : 2 ≤ i2.val := le_refl 2
  let a : ↥(TauCeti.BilinForm.isometryGroup f) := ⟨e i2, hGmem _ (heE i2)⟩
  have haF : a ∈ F' := Subgroup.mem_subgroupOf.2 (D.e_mem_fixU i2 hi2)
  have ha1 : a ≠ 1 := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := X i2) (by
      intro h0
      have := hdim2 i2
      rw [h0, finrank_bot] at this
      omega)
    have h1 : e i2 = 1 := congrArg Subtype.val h
    have h2 : e i2 x = ρ i2 x := by rw [hact i2 i2 x hx, if_pos rfl]
    have h3 : ρ i2 x = x := by
      rw [← h2, h1]
      rfl
    exact hx0 (hfix i2 x hx h3)
  have hF'ne : F' ≠ ⊥ := fun h => ha1 (Subgroup.mem_bot.1 (h ▸ haF))
  have hcent : Subgroup.centralizer (F' : Set ↥(TauCeti.BilinForm.isometryGroup f)) =
      (D.Cg f).subgroupOf (TauCeti.BilinForm.isometryGroup f) := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 (fun h hh => ?_), x.2⟩
      have hhG : h ∈ TauCeti.BilinForm.isometryGroup f := hGmem h (hfixE h hh)
      have hhF : (⟨h, hhG⟩ : ↥(TauCeti.BilinForm.isometryGroup f)) ∈ F' :=
        Subgroup.mem_subgroupOf.2 hh
      exact congrArg Subtype.val (hx _ hhF)
    · intro hx y hy
      apply Subtype.ext
      have hyΓ : (y : W ≃ₗ[ZMod 2] W) ∈ D.fixU := Subgroup.mem_subgroupOf.1 hy
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).1) _ hyΓ
  obtain ⟨ι⟩ := hIso
  refine ⟨F', hF'E, hF'ne, (D.Lg f hn2).subgroupOf (TauCeti.BilinForm.isometryGroup f), ?_, ?_⟩
  · rw [hcent]
    exact X1Sp.Gen.isSubnormal_subgroupOf _ hSub hCG
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hLG).trans ι⟩

end One

end X1F4

open CFSG.Blueprint.Chevalley CFSG.StandardType CFSG.StandardType.TableBF4TwoTB
  CFSG.SeitzReduction.F4Pilot

section Good


namespace X1F4

variable {K : Type} [Field K] [CharP K 2]

theorem tGen_eq_tE (i : Fin 4) : tGen K i = tE K (Multiplicative.ofAdd (Pi.single i 1)) := by
  rw [tE_single, tC_apply, toAdd_ofAdd, show (1 : ZMod 3).val = 1 from rfl, pow_one]

theorem tGen_mem_range (i : Fin 4) : tGen K i ∈ (tE K).range := by
  rw [tGen_eq_tE]
  exact ⟨_, rfl⟩

theorem nodeElt_mem_range [Finite K] : TableBF4TwoInputs.nodeElt K ∈ (tE K).range :=
  tGen_mem_range 3

theorem range_torus3_le_range_tE : (TableBF4Two.torus3 K).range ≤ (tE K).range := by
  rw [TableBF4Two.torus3, MonoidHom.noncommPiCoprod_range]
  refine iSup_le fun i => ?_
  rintro _ ⟨a, rfl⟩
  rw [TableBF4Two.torusCoord_apply, map_pow]
  exact Subgroup.pow_mem _ (tGen_mem_range i.castSucc) _

end X1F4

theorem x1F4FrameGood_holds : X1F4FrameGood := by
  intro K _ _ _ hK
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨ιs⟩ := X1Sp.exists_stdIso 3
  set D : Subgroup (adjointGroup .F4 K) := C3Levi K with hD
  obtain ⟨Θ, -⟩ : ∃ Θ : ↥D ≃* ↥(TauCeti.BilinForm.isometryGroup (X1Sp.stdForm 3)),
      Θ = (c3LeviEquivOfRingEquiv K (ZMod.ringEquiv K hKf).symm).trans ιs := ⟨_, rfl⟩
  have hE3D : (TableBF4Two.torus3 K).range ≤ D := TableBF4TwoInputs.range_torus3_le_C3Levi
  have hE3el : IsElemAbelian 3 (TableBF4Two.torus3 K).range :=
    X1F4.isElemAbelian_of_le X1F4.isElemAbelian_range_tE X1F4.range_torus3_le_range_tE
  obtain ⟨E', hE'def⟩ : ∃ E' : Subgroup ↥(TauCeti.BilinForm.isometryGroup (X1Sp.stdForm 3)),
      E' = ((TableBF4Two.torus3 K).range.subgroupOf D).map Θ.toMonoidHom := ⟨_, rfl⟩
  have hE'el : IsElemAbelian 3 E' := by
    rw [hE'def]
    exact X1Sp.isElemAbelian_map_hom 3 _
      (X1F4.isElemAbelian_comap Subtype.val_injective hE3el)
  haveI : Fintype E' := Fintype.ofFinite _
  have hE'card : Fintype.card E' = 3 ^ 3 := by
    rw [← Nat.card_eq_fintype_card, hE'def, Subgroup.card_map_of_injective Θ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE3D).toEquiv,
      TableBF4TwoInputs.card_range_torus3]
  obtain ⟨F', hF'E, hF'ne, L', hL'sub, ⟨χ0⟩⟩ :=
    X1F4.sp_core_one (X1Sp.stdForm 3) (X1Sp.stdForm_isAlt 3) (X1Sp.stdForm_nondeg 3) 3 le_rfl
      (X1Sp.stdForm_finrank 3) E' hE'el hE'card
  obtain ⟨FD, hFD⟩ : ∃ FD : Subgroup ↥D, FD = F'.map Θ.symm.toMonoidHom := ⟨_, rfl⟩
  obtain ⟨LD, hLD⟩ : ∃ LD : Subgroup ↥D, LD = L'.map Θ.symm.toMonoidHom := ⟨_, rfl⟩
  have hLDsub : IsSubnormal LD (Subgroup.centralizer (FD : Set ↥D)) := by
    have h := CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map Θ.symm hL'sub
    rw [centralizer_map_mulEquiv Θ.symm F'] at h
    rw [hLD, hFD]
    exact h
  have hFDE : FD ≤ (TableBF4Two.torus3 K).range.subgroupOf D := by
    rw [hFD]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 (hE'def ▸ hF'E hy)
    show Θ.symm (Θ z) ∈ _
    rw [MulEquiv.symm_apply_apply]
    exact hz
  have hFDne : FD ≠ ⊥ := by
    rw [hFD, Ne, Subgroup.map_eq_bot_iff_of_injective _ Θ.symm.injective]
    exact hF'ne
  obtain ⟨P, hP⟩ : ∃ P : Subgroup (adjointGroup .F4 K), P = FD.map D.subtype := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Subgroup (adjointGroup .F4 K), L = LD.map D.subtype := ⟨_, rfl⟩
  have hPD : P ≤ D := by
    rw [hP]
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hPT : P ≤ (tE K).range := by
    rw [hP]
    rintro _ ⟨y, hy, rfl⟩
    exact X1F4.range_torus3_le_range_tE (Subgroup.mem_subgroupOf.1 (hFDE hy))
  have hPne : P ≠ ⊥ := by
    rw [hP, Ne, Subgroup.map_eq_bot_iff_of_injective _ Subtype.val_injective]
    exact hFDne
  have hLsubD : IsSubnormal L (D ⊓ Subgroup.centralizer (P : Set (adjointGroup .F4 K))) := by
    have h := hLDsub.map D.subtype
    rw [X1F4.map_subtype_centralizer D FD] at h
    rw [hL, hP]
    exact h
  set x₀ := TableBF4TwoInputs.nodeElt K with hx₀
  have hDsub : IsSubnormal D (Subgroup.centralizer ({x₀} : Set (adjointGroup .F4 K))) :=
    CFSG.Assembly.isSubnormal_iff_open.1 (TableBF4TwoInputs.layer_centralizer_nodeElt hK).2.2.1
  obtain ⟨F, hF⟩ : ∃ F : Subgroup (adjointGroup .F4 K), F = Subgroup.zpowers x₀ ⊔ P :=
    ⟨_, rfl⟩
  have hCF : Subgroup.centralizer (F : Set (adjointGroup .F4 K)) =
      Subgroup.centralizer ({x₀} : Set (adjointGroup .F4 K)) ⊓
        Subgroup.centralizer (P : Set (adjointGroup .F4 K)) := by
    rw [hF, X1F4.centralizer_sup_eq, ← TableBF4TwoInputs.centralizer_singleton_eq_zpowers]
  have hLsub : IsSubnormal L (Subgroup.centralizer (F : Set (adjointGroup .F4 K))) := by
    rw [hCF]
    exact hLsubD.trans (hDsub.inf _)
  obtain ⟨χ⟩ : Nonempty (↥L ≃* alternatingGroup (Fin 6)) := by
    rw [hL, hLD]
    exact ⟨((Subgroup.equivMapOfInjective _ D.subtype Subtype.val_injective).symm.trans
      (MulEquiv.subgroupMap Θ.symm L').symm).trans χ0⟩
  have hq : CFSG.Open.IsQuasisimple ↥L :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv χ.symm
      X1Sp.isQuasisimple_alt6
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥L := χ.isSimpleGroup
  have hnc6 : ¬ IsMulCommutative (alternatingGroup (Fin 6)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
  obtain ⟨a6, b6, hab6⟩ := X1Sp.exists_noncomm_of_not_mulCommutative hnc6
  have hncL : ∃ a b : ↥L, a * b ≠ b * a :=
    ⟨χ.symm a6, χ.symm b6, fun h => hab6 (by
      have := congrArg χ h
      simpa using this)⟩
  have hcenL : Subgroup.center ↥L = ⊥ := center_eq_bot_of_simple_nonabelian hncL
  have h360 : Nat.card ↥L = 360 := by
    rw [Nat.card_congr χ.toEquiv]
    have h2 := two_mul_nat_card_alternatingGroup (α := Fin 6)
    have h3 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_perm]
      simp [Nat.factorial]
    rw [h3] at h2
    omega
  have hd : 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [hcenL, Nat.card_congr (QuotientGroup.quotientBot (G := ↥L)).toEquiv, h360]
    norm_num
  have hGood : IsSubnormal L
      (⨅ g ∈ F.map (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)),
        CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup g) := by
    rw [iInf_fixSubgroup_conj]
    exact hLsub
  have hFT : F ≤ (tE K).range := by
    rw [hF]
    exact sup_le (Subgroup.zpowers_le.2 X1F4.nodeElt_mem_range) hPT
  have hF9 : 9 ≤ Nat.card F := by
    have hdvd : Nat.card F ∣ 3 ^ 4 := by
      rw [← X1F4.card_range_tE (K := K)]
      exact Subgroup.card_dvd_of_le hFT
    obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hX : Subgroup.zpowers x₀ ≤ F := hF ▸ le_sup_left
    have h3 : Nat.card (Subgroup.zpowers x₀) = 3 := by
      rw [Nat.card_zpowers, TableBF4TwoInputs.orderOf_nodeElt]
    have h3F : 3 ∣ Nat.card F := h3 ▸ Subgroup.card_dvd_of_le hX
    have hne : Nat.card F ≠ 3 := by
      intro h
      have heq : Subgroup.zpowers x₀ = F :=
        Subgroup.eq_of_le_of_card_ge hX (by rw [h, h3])
      have hPX : P ≤ Subgroup.zpowers x₀ := heq ▸ (hF ▸ le_sup_right)
      have hdisj := (centralizer_nonsplit TableBF4TwoInputs.zpowers_nodeElt_le
        (Subgroup.isCyclic_zpowers _) (TableBF4TwoInputs.card_zpowers_nodeElt hK)).2.1
      exact hPne (eq_bot_iff.2 fun p hp =>
        Subgroup.mem_bot.2 (Subgroup.disjoint_def.1 hdisj (hPX hp) (hPD hp)))
    rw [hk] at h3F hne ⊢
    interval_cases k
    · norm_num at h3F
    · exact absurd (pow_one 3) hne
    all_goals norm_num
  exact ⟨F, hFT, hF9, isGood_of_subnormal_quasisimple Nat.prime_three hGood hq hd⟩

theorem kd264X1ExcF4_of_conj (hC : X1F4FrameConj) : KD264X1ExcF4 :=
  kd264X1ExcF4_of_frame hC x1F4FrameGood_holds

end Good

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
