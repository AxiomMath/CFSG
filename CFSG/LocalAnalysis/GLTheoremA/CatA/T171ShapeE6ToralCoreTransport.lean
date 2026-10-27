module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralLangOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.MIPComp
import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescProof
import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentral
import CFSG.Assembly.LargeEvenGLABridge
import CFSG.LieType.Automorphisms.SteinbergBLCompleteIndexTwo
import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport
import CFSG.Assembly.OpenBridges
import CFSG.HardMathSupport.Dickson.I271.ChevPBal
import CFSG.HardMathSupport.Dickson.I271.I202Full
import CFSG.HardMathSupport.Dickson.I271.Support.OuterStep
import CFSG.LieType.SteinbergBRBlockParabolicDInf
import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
import CFSG.Quasithin.Background.C1PackS15212C
import CFSG.Quasithin.Background.D2Cyclic
import CFSG.Quasithin.Background.F918H5
import CFSG.Quasithin.Background.GoldschmidtS146RBend1
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
import CFSG.Quasithin.EmptyFaithful.S14610Q1
import CFSG.Quasithin.EmptyFaithful.S14610Top
import CFSG.Quasithin.EmptyFaithful.S146F4
import CFSG.Quasithin.EmptyFaithful.S152N11
import CFSG.Quasithin.EmptyFaithful.S152UGen
import CFSG.Quasithin.EmptyFaithful.S152Y15
import CFSG.Quasithin.EmptyFaithful.S152Y19
import CFSG.Quasithin.EmptyFaithful.S153E59A
import CFSG.Quasithin.Recognition.ModelBridges
import CFSG.Quasithin.Vol2.Ch1EightFourChar2
import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.HardMathSupport.Solomon.Coordinator (glaPComponent_map_central)

theorem innDiagOn_of_psimple_iso {G K : Type} [Group G] [Finite G] [Group K]
    {p : ℕ} {X : Subgroup G} {J : Subgroup G} {L : Subgroup K} {b : G} {y : K}
    (hJ : GLAPComponent p X J)
    (e : PSimple p J ≃* PSimple p L)
    (hb : b ∈ Subgroup.normalizer (J : Set G))
    (hy : y ∈ Subgroup.normalizer (L : Set K))
    (key : MulAut.congr e (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hb) =
      CFSG.LocalAnalysis.GLTheoremA.MI.indAut p L y hy)
    (h : InnDiagOn p (Subgroup.zpowers y) L) :
    InnDiagOn p (Subgroup.zpowers b) J := by
  obtain ⟨-, hcomm, lab, hlab, hraw⟩ := h
  refine ⟨Subgroup.zpowers_le.2 hb, (CFSG.LocalAnalysis.GLTheoremA.MI.isQuasisimple_pQuot_any hJ).1,
    lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R' _ I F ⟨hs, hna, θ, hθ⟩
  refine ⟨hs, hna, e.trans θ, ?_⟩
  intro b' hb'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
  have hyk : y ^ k ∈ Subgroup.zpowers y := Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) k
  obtain ⟨φ, hφI, hφ⟩ := hθ (y ^ k) hyk
  refine ⟨φ, hφI, ?_⟩
  have indAut_zpow_eq : ∀ {X : Type} [Group X] {S : Subgroup X} {g : X}
      (hg : g ∈ Subgroup.normalizer (S : Set X)) (m : ℤ)
      (hm : g ^ m ∈ Subgroup.normalizer (S : Set X)),
      CFSG.LocalAnalysis.GLTheoremA.MI.indAut p S (g ^ m) hm =
        (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p S g hg) ^ m := by
    intro X _ S g hg m hm
    unfold CFSG.LocalAnalysis.GLTheoremA.MI.indAut
    rw [← map_zpow]
    congr 1
    apply Subtype.ext
    simp [zpow_neg, inv_zpow]
  have hbk : b ^ k ∈ Subgroup.normalizer (J : Set G) := Subgroup.zpow_mem _ hb k
  have hyK : y ^ k ∈ Subgroup.normalizer (L : Set K) := Subgroup.zpow_mem _ hy k
  have hkeyk : MulAut.congr e (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J (b ^ k) hbk) =
      CFSG.LocalAnalysis.GLTheoremA.MI.indAut p L (y ^ k) hyK := by
    calc MulAut.congr e (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J (b ^ k) hbk)
        = MulAut.congr e ((CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hb) ^ k) := by
          rw [indAut_zpow_eq hb k hbk]
      _ = (MulAut.congr e (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hb)) ^ k :=
          map_zpow (MulAut.congr e).toMonoidHom _ k
      _ = (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p L y hy) ^ k := by rw [key]
      _ = CFSG.LocalAnalysis.GLTheoremA.MI.indAut p L (y ^ k) hyK :=
          (indAut_zpow_eq hy k hyK).symm
  have hφ' := (CFSG.LocalAnalysis.GLTheoremA.MI.induces_indRel_iff hyK θ).1 hφ
  refine (CFSG.LocalAnalysis.GLTheoremA.MI.induces_indRel_iff hbk (e.trans θ)).2 ?_
  rw [hφ']
  calc MulAut.congr θ (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p L (y ^ k) hyK)
      = MulAut.congr θ (MulAut.congr e
          (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J (b ^ k) hbk)) := by rw [hkeyk]
    _ = MulAut.congr (e.trans θ) (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J (b ^ k) hbk) := by
        ext r
        simp [MulAut.congr_apply, MulEquiv.trans_apply]

theorem componentDescentIndAut_of_conjOn_map
    {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G)
    {R : Type} [Group R] [Finite R] {H : Type} [Group H] (ι : R →* H)
    (hι : Function.Injective ι) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (φ : MulAut R) (y : H) (hS : Setup p L J A d b)
    (hind : LargeEvenInduces θ (conjRel b) φ)
    (hN : y ∈ Subgroup.normalizer
      ((((J.subgroupOf L).map (piCenterQuot θ)).map ι) : Set H))
    (hconj : ∀ x ∈ (J.subgroupOf L).map (piCenterQuot θ), ι (φ x) = y * ι x * y⁻¹) :
    ∃ e : PSimple p J ≃* PSimple p (((J.subgroupOf L).map (piCenterQuot θ)).map ι),
      MulAut.congr e (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hS.b_norm) =
        CFSG.LocalAnalysis.GLTheoremA.MI.indAut p
          (((J.subgroupOf L).map (piCenterQuot θ)).map ι) y⁻¹ (Subgroup.inv_mem _ hN) := by
  classical
  have hp : p.Prime := hS.prime
  have hJL : J ≤ L := hS.comp.1.1.trans inf_le_left
  let π : ↥L →* R := piCenterQuot θ
  have hπker : π.ker ≤ Subgroup.center ↥L := by
    rw [show π.ker = Subgroup.center ↥L from by
      dsimp only [π, piCenterQuot]
      rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center ↥L))
        θ.toMonoidHom θ.injective, QuotientGroup.ker_mk']]
  have hbL : b ∈ Subgroup.normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag) hS.b_mem
  have hXle : L ⊓ Subgroup.centralizer ({d} : Set G) ≤ L := inf_le_left
  have hJ' : GLAPComponent p ((L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L)
      (J.subgroupOf L) :=
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf hp hXle hS.pcomp
  have hc : ∀ z ∈ (L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L ⊓ π.ker,
      ∀ x ∈ (L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L, x * z = z * x := by
    intro z hz x _hx
    have hzc : z ∈ Subgroup.center ↥L := hπker hz.2
    exact Subgroup.mem_center_iff.1 hzc x
  have hJbar : GLAPComponent p
      (((L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L).map π)
      ((J.subgroupOf L).map π) :=
    glaPComponent_map_central hp π hc hJ'
  let Jbar : Subgroup R := (J.subgroupOf L).map π
  have hJbar' : GLAPComponent p
      (((L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L).map π) Jbar := hJbar
  let Kbar : Subgroup H := Jbar.map ι
  have hN' : y⁻¹ ∈ Subgroup.normalizer (Kbar : Set H) := Subgroup.inv_mem _ hN
  let πJ : ↥J →* R := π.comp (Subgroup.inclusion hJL)
  let fJ : ↥J →* ↥Jbar :=
    πJ.codRestrict Jbar fun j =>
      Subgroup.mem_map.mpr ⟨⟨(j : G), hJL j.2⟩, j.2, rfl⟩
  have hfJ : Function.Surjective fJ := by
    intro z
    obtain ⟨l, hl, hz⟩ := Subgroup.mem_map.mp z.2
    have hlj : (l : G) ∈ J := Subgroup.mem_subgroupOf.mp hl
    refine ⟨⟨(l : G), hlj⟩, ?_⟩
    apply Subtype.ext
    exact hz
  let ιJ : ↥J →* H := ι.comp (Jbar.subtype.comp fJ)
  let ι' : ↥J →* ↥Kbar :=
    ιJ.codRestrict Kbar fun j =>
      Subgroup.mem_map.mpr ⟨fJ j, (fJ j).2, rfl⟩
  have hι' : Function.Surjective ι' := by
    intro z
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp z.2
    obtain ⟨j, hj⟩ := hfJ ⟨x, hx⟩
    refine ⟨j, Subtype.ext ?_⟩
    show ι (fJ j) = z
    rw [hj]
    exact hxz
  haveI : Finite ↥Kbar := Finite.of_surjective ι' hι'
  have hJbarQ : CFSG.Open.IsQuasisimple (PQuot p Jbar) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJbar'
  have hKbarQ : CFSG.Open.IsQuasisimple (PQuot p Kbar) := by
    have h := hJbarQ.of_mulEquiv ((CFSG.HardMathSupport.Dickson.I271.pQuotEquiv p
      (Subgroup.equivMapOfInjective Jbar ι hι)).symm)
    simpa [Kbar] using h
  let ψ : PSimple p J →* PSimple p Kbar :=
    CFSG.LocalAnalysis.GLTheoremA.pSimpleMapOfSurjective hp ι' hι'
  have hψsurj : Function.Surjective ψ :=
    CFSG.LocalAnalysis.GLTheoremA.pSimpleMapOfSurjective_surjective hp ι' hι'
  have hψmk : ∀ l : ↥J, ψ (QuotientGroup.mk (QuotientGroup.mk l)) =
      QuotientGroup.mk (QuotientGroup.mk (ι' l)) :=
    fun l => by
      simp [ψ, CFSG.LocalAnalysis.GLTheoremA.pSimpleMapOfSurjective,
        CFSG.LocalAnalysis.GLTheoremA.pQuotMapOfSurjective_mk]
  have hsimpleJ : IsSimpleGroup (PSimple p J) :=
    (CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian hp hS.pcomp).1
  have hnaBar : ∃ a b' : PSimple p Kbar, a * b' ≠ b' * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hKbarQ
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b', hab⟩ := hnaBar
      obtain ⟨a', rfl⟩ := hψsurj a
      obtain ⟨b'', rfl⟩ := hψsurj b'
      apply hab
      have h1 : ψ a' = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
      have h2 : ψ b'' = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
      rw [h1, h2]
  let e0 : PSimple p J ≃* PSimple p Kbar :=
    MulEquiv.ofBijective ψ ⟨hinj, hψsurj⟩
  have he0 : ∀ x, e0 x = ψ x := fun _ => rfl
  have hkey : ∀ l : ↥J,
      e0 (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hS.b_norm
          (QuotientGroup.mk (QuotientGroup.mk l))) =
        CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Kbar y⁻¹ hN'
          (e0 (QuotientGroup.mk (QuotientGroup.mk l))) := by
    intro l
    have hmem : b⁻¹ * (l : G) * b ∈ J := by
      have hbinv : b⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ hS.b_norm
      have := (Subgroup.mem_normalizer_iff.mp hbinv (l : G)).mp l.2
      simpa using this
    let l' : ↥J := ⟨b⁻¹ * (l : G) * b, hmem⟩
    have hrel : indRel p J b (QuotientGroup.mk l) (QuotientGroup.mk l') :=
      ⟨l, l', rfl, rfl, rfl⟩
    have hstep : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hS.b_norm
        (QuotientGroup.mk (QuotientGroup.mk l)) = QuotientGroup.mk (QuotientGroup.mk l') :=
      CFSG.LocalAnalysis.GLTheoremA.MI.indAut_apply_mk hS.b_norm hrel
    have hmemL : b⁻¹ * (l : G) * b ∈ L := hJL hmem
    let lL : ↥L := Subgroup.inclusion hJL l
    let lL' : ↥L := Subgroup.inclusion hJL l'
    have hrelL : (lL' : G) = b⁻¹ * (lL : G) * b := by
      simp [lL, lL', l']
    have hInd : φ (π lL) = π lL' := by
      change φ (θ (QuotientGroup.mk lL)) = θ (QuotientGroup.mk lL')
      exact hind lL lL' hrelL
    have hιl' : (ι' l' : H) = y * (ι' l : H) * y⁻¹ := by
      have h1 : (ι' l : H) = ι (π lL) := rfl
      have h2 : (ι' l' : H) = ι (π lL') := rfl
      calc (ι' l' : H) = ι (π lL') := h2
        _ = ι (φ (π lL)) := by rw [hInd]
        _ = y * ι (π lL) * y⁻¹ := hconj _ (fJ l).2
        _ = y * (ι' l : H) * y⁻¹ := by rw [h1]
    have hrelBar : indRel p Kbar y⁻¹ (QuotientGroup.mk (ι' l))
        (QuotientGroup.mk (ι' l')) := by
      refine ⟨ι' l, ι' l', rfl, rfl, ?_⟩
      show ((ι' l' : ↥Kbar) : H) = (y⁻¹)⁻¹ * ((ι' l : ↥Kbar) : H) * y⁻¹
      simpa using hιl'
    have hstepBar : CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Kbar y⁻¹ hN'
        (QuotientGroup.mk (QuotientGroup.mk (ι' l))) =
          QuotientGroup.mk (QuotientGroup.mk (ι' l')) :=
      CFSG.LocalAnalysis.GLTheoremA.MI.indAut_apply_mk hN' hrelBar
    calc e0 (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hS.b_norm
          (QuotientGroup.mk (QuotientGroup.mk l)))
        = e0 (QuotientGroup.mk (QuotientGroup.mk l')) := by rw [hstep]
      _ = QuotientGroup.mk (QuotientGroup.mk (ι' l')) := by rw [he0, hψmk]
      _ = CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Kbar y⁻¹ hN'
            (QuotientGroup.mk (QuotientGroup.mk (ι' l))) := hstepBar.symm
      _ = CFSG.LocalAnalysis.GLTheoremA.MI.indAut p Kbar y⁻¹ hN'
            (e0 (QuotientGroup.mk (QuotientGroup.mk l))) := by rw [he0, hψmk l]
  refine ⟨e0, ?_⟩
  ext x
  obtain ⟨y, hy⟩ := e0.surjective x
  rw [← hy]
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  simpa [MulAut.congr_apply, MulEquiv.trans_apply] using hkey l

theorem map_conjOn_image_of_normalizes
    {G R : Type} [Group G] [Group R] {L J : Subgroup G}
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {b : G}
    (hbL : b ∈ Subgroup.normalizer (L : Set G))
    (hbJ : b ∈ Subgroup.normalizer (J : Set G))
    {φ : MulAut R} (hind : LargeEvenInduces θ (conjRel b) φ) :
    ∀ x ∈ ((J.subgroupOf L).map (piCenterQuot θ)), φ x ∈
      ((J.subgroupOf L).map (piCenterQuot θ)) := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hx
  have hlJ : (l : G) ∈ J := Subgroup.mem_subgroupOf.1 hl
  have hmemJ : b⁻¹ * (l : G) * b ∈ J := by
    simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hbJ) (l : G)).1 hlJ
  have hmemL : b⁻¹ * (l : G) * b ∈ L := by
    simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hbL) (l : G)).1 l.2
  let l' : ↥L := ⟨b⁻¹ * (l : G) * b, hmemL⟩
  have hl' : l' ∈ J.subgroupOf L := Subgroup.mem_subgroupOf.2 hmemJ
  have hrel : (l' : G) = b⁻¹ * (l : G) * b := rfl
  have hInd := hind l l' hrel
  rw [show piCenterQuot θ l = θ (QuotientGroup.mk l) from rfl, hInd]
  exact Subgroup.mem_map.2 ⟨l', hl', rfl⟩

theorem componentCore_of_toralComponentAction
  (hcore : TwE6W0ToralComponentAction) : TwE6W0ComponentCore := by
  intro G _ _ L J A d b n K _ _ hn hK h3 hS σ hσ ε θ wd wb hd hb Fr hFr g hg hn0 htorus
  classical
  have hdL : d ∈ Subgroup.normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag) hS.d_mem
  haveI : Finite (TwE6Delta.RecipeR K n) := Finite.of_equiv _ θ.toEquiv
  have hcomp : CFSG.Assembly.IsComponentOf J
      (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    (CFSG.Assembly.isComponentOf_iff_open).2 hS.comp.1
  have hlayer : LargeEvenLayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J := by
    rw [CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer]
    exact hS.comp.2
  have hdesc := componentDescent_holds (G := G) (L := L) (R := TwE6Delta.RecipeR K n)
    hS.qs θ d hdL (TwE6Transport.recipeConj σ ε wd) hd J hcomp hlayer
  have hbL : b ∈ Subgroup.normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag) hS.b_mem
  have hnorm := map_conjOn_image_of_normalizes θ hbL hS.b_norm hb
  have hwd3 : wd ^ 3 = 1 := twwd_pow_three_eq_one hS hn hK hσ hd
  have hwd1 : wd ≠ 1 := twwd_ne_one hS hd
  have hwb3 : wb ^ 3 = 1 := twwb_pow_three_eq_one hS hn hK hσ hb
  exact hcore n K hn hK h3 σ hσ ε wd wb hwd3 hwd1 hwb3 Fr hFr g hg hn0 htorus _
    hdesc.1 hnorm

theorem twE6W0TorusExit_of_componentCore
  (hcore : TwE6W0ComponentCore) : TwE6W0TorusExit := by
  intro G _ _ L J A d b n K _ _ hn hK h3 hS σ hσ ε θ wd wb hd hb Fr hFr g hg hn0 htorus
  haveI : Finite (TwE6Delta.RecipeR K n) := Finite.of_equiv _ θ.toEquiv
  have hdiag : InnDiagOn 3
      (Subgroup.zpowers (TwE6Transport.recipeConj σ ε wb))
      (((J.subgroupOf L).map (piCenterQuot θ)).map (MulAut.conj :
        TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n))) :=
    hcore G L J A d b n K hn hK h3 hS σ hσ ε θ wd wb hd hb Fr hFr g hg hn0 htorus
  have hN : TwE6Transport.recipeConj σ ε wb ∈ Subgroup.normalizer
      ((((J.subgroupOf L).map (piCenterQuot θ)).map (MulAut.conj :
        TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n))) :
          Set (MulAut (TwE6Delta.RecipeR K n))) :=
    hdiag.1 (Subgroup.mem_zpowers _)
  haveI hsimpleL : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hS.qs.2
  haveI hsimpleR : IsSimpleGroup (TwE6Delta.RecipeR K n) :=
    (MulEquiv.isSimpleGroup_congr θ).mp hsimpleL
  have hnaR : ∃ x y : TwE6Delta.RecipeR K n, x * y ≠ y * x := by
    obtain ⟨a, b', hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hS.qs
    exact ⟨θ a, θ b', fun h => hab (θ.injective (by simpa [map_mul] using h))⟩
  have hcenter : Subgroup.center (TwE6Delta.RecipeR K n) = ⊥ :=
    CFSG.LieType.Automorphisms.center_eq_bot_of_simple hnaR
  have hι : Function.Injective (MulAut.conj :
      TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)) :=
    CFSG.LieType.Automorphisms.conj_injective_of_center_eq_bot hcenter
  have hnat : ∀ x ∈ (J.subgroupOf L).map (piCenterQuot θ),
      MulAut.conj (TwE6Transport.recipeConj σ ε wb x) =
        TwE6Transport.recipeConj σ ε wb * MulAut.conj x *
          (TwE6Transport.recipeConj σ ε wb)⁻¹ :=
    fun x _ => (CFSG.LieType.Automorphisms.mulAut_conj_conj _ x).symm
  obtain ⟨e, he⟩ := componentDescentIndAut_of_conjOn_map (p := 3) (L := L) (J := J)
    (A := A) (d := d) (b := b)
    (ι := (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)))
    hι θ (TwE6Transport.recipeConj σ ε wb) (TwE6Transport.recipeConj σ ε wb) hS hb hN hnat
  have hdiag' : InnDiagOn 3
      (Subgroup.zpowers (TwE6Transport.recipeConj σ ε wb)⁻¹)
      (((J.subgroupOf L).map (piCenterQuot θ)).map (MulAut.conj :
        TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n))) := by
    simpa only [Subgroup.zpowers_inv] using hdiag
  exact innDiagOn_of_psimple_iso hS.pcomp e hS.b_norm (Subgroup.inv_mem _ hN) he hdiag'

theorem twE6W0TorusExit_of_toralComponentAction
  (hcore : TwE6W0ToralComponentAction) : TwE6W0TorusExit :=
  twE6W0TorusExit_of_componentCore (componentCore_of_toralComponentAction hcore)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
