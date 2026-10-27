module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthFacts
public import CFSG.ClassicalInvolution.RouteD.TypeDAdapt
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Timmesfeld (edgeD)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_ctx_member {tY : StatedLieTag} {nY : ℕ} {K : Subgroup G} {z : G}
    (c : TCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 tY nY Ω z) {M : Subgroup G} (hM : M ∈ Ω) {x : G}
    (hx : IsClassicalMember p f M x) : Nonempty (TCtx p f tY nY Ω M x) := by
  obtain ⟨g, hg⟩ := hsingle M hM
  have hzx : IsClassicalMember p f M (g * z * g⁻¹) := by
    rw [hg]
    exact c.hz.conj g
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have hxe : x = g * z * g⁻¹ := unique_involution_of_isClassicalMember h2 (c.hex M hM) hx hzx
  subst hxe
  have hshape_x : LocalShapeT p f 2 tY nY Ω (g * z * g⁻¹) := hshape.conj c.hΩ.conjInvariant g
  have hP1_x : LocalOddCentral Ω {g * z * g⁻¹} :=
    localOddCentral_conj c.hΩ.conjInvariant g z c.hP1
  obtain ⟨dx⟩ := hshape_x.nonempty_dictT2 c.hY.ne_d4 c.hY.sc c.hΩ hM hzx
  obtain ⟨dx', hQx⟩ := exists_dictT2_of_member c.hY hM hzx dx
  let cx : TCtx p f tY nY Ω M (g * z * g⁻¹) :=
    { hp2 := c.hp2, hq := c.hq, hΩ := c.hΩ, hex := c.hex, hK := hM, hz := hzx, hP1 := hP1_x,
      d := dx', hQ₀ := hQx, hY := c.hY }
  exact ⟨cx⟩

section Nodes

variable {m : ℕ} {K : Subgroup G}

structure DNodes (p f m : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (K : Subgroup G) where
  J : Fin m → Subgroup G
  w : Fin m → G
  mem : ∀ a, J a ∈ Ω
  cl : ∀ a, IsClassicalMember p f (J a) (w a)
  commK : ∀ a, Commutes K (J a)
  comm : ∀ a b, a ≠ b → ¬ edgeD m a b → ¬ edgeD m b a → Commutes (J a) (J b)
  pair : ∀ a b, edgeD m a b → ∃ W, LinearBlockStandardPair (GaloisField p f) W (J a) (J b)

namespace DNodes

variable (nd : DNodes p f m Ω K)

@[expose] def Adj (a b : Fin m) : Prop := edgeD m a b ∨ edgeD m b a

theorem adj_def (a b : Fin m) : Adj a b ↔
    (((a.val + 1 = b.val ∧ b.val + 1 < m) ∨ (a.val + 3 = m ∧ b.val + 1 = m)) ∨
    ((b.val + 1 = a.val ∧ a.val + 1 < m) ∨ (b.val + 3 = m ∧ a.val + 1 = m))) := Iff.rfl

theorem Adj.ne {a b : Fin m} (h : Adj a b) : a ≠ b := by
  rintro rfl
  unfold Adj edgeD at h
  omega

theorem Adj.symm {a b : Fin m} (h : Adj a b) : Adj b a := Or.symm h

omit [Finite G] in
theorem pair_of_adj {a b : Fin m} (h : Adj a b) :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W (nd.J a) (nd.J b) := by
  rcases h with h | h
  · exact nd.pair a b h
  · obtain ⟨W, hW⟩ := nd.pair b a h
    exact ⟨W, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW⟩

omit [Finite G] in
theorem not_commutes_of_adj {a b : Fin m} (h : Adj a b) : ¬ Commutes (nd.J a) (nd.J b) := by
  obtain ⟨W, hW⟩ := nd.pair_of_adj h
  exact not_commutes_of_linearBlockStandardPair hW

omit [Finite G] in
theorem commutes_of_not_adj {a b : Fin m} (hab : a ≠ b) (h : ¬ Adj a b) :
    Commutes (nd.J a) (nd.J b) :=
  nd.comm a b hab (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'))

omit [Finite G] in
theorem ne_J (hΩ : InClass p f Ω) {a b : Fin m} (hab : a ≠ b) : nd.J a ≠ nd.J b := by
  intro h
  by_cases hadj : Adj a b
  · obtain ⟨W, hW⟩ := nd.pair_of_adj hadj
    exact ne_of_linearBlockStandardPair hW h
  · have := nd.commutes_of_not_adj hab hadj
    rw [← h] at this
    exact not_commutes_self_of_mem hΩ (nd.mem a) this

omit [Finite G] in
theorem commute_w (h2 : (2 : GaloisField p f) ≠ 0) (a b : Fin m) :
    Commute (nd.w a) (nd.w b) := by
  by_cases hab : a = b
  · subst hab; exact Commute.refl _
  by_cases hadj : Adj a b
  · obtain ⟨W, hW⟩ := nd.pair_of_adj hadj
    exact standardPair_involutions_commute h2 hW (nd.cl a).mem (nd.cl b).mem
      (nd.cl a).orderOf_eq_two (nd.cl b).orderOf_eq_two
  · exact (nd.commutes_of_not_adj hab hadj) _ (nd.cl a).mem _ (nd.cl b).mem

omit [Finite G] in
theorem conjSub_w (h2 : (2 : GaloisField p f) ≠ 0) {a b : Fin m} (h : Adj a b) :
    conjSub (nd.w b) (nd.J a) = nd.J a := by
  obtain ⟨W, hW⟩ := nd.pair_of_adj h
  exact conjSub_eq_of_standardPair h2 hW (nd.cl b).mem (nd.cl b).orderOf_eq_two

end DNodes

omit [Finite G] in
theorem DNodes.mem_loc (nd : DNodes p f m Ω K) (b : Fin m) {L : Subgroup G} (hL : L ∈ Ω)
    (hc : Commutes L (nd.J b)) : L ∈ centralizingMembers Ω {nd.w b} :=
  mem_centralizingMembers_of_commutes hL (nd.cl b).mem hc

end Nodes

section Scenarios

variable {m : ℕ} {K : Subgroup G} {z : G}

theorem scenario_A
    (hF : OrthGeom (Subgroup.center (modelUniv .POmegaPlus m p f Fact.out).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D) (GaloisField p f))
    (c : TCtx p f .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) (nd : DNodes p f m Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    {pp a₀ a₁ e b : Fin m} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp)
    (h0 : DNodes.Adj pp a₀) (h1 : DNodes.Adj pp a₁) (h01 : a₀ ≠ a₁) (h01' : ¬ DNodes.Adj a₀ a₁)
    (hea₀ : e ≠ a₀) (hea₁ : e ≠ a₁)
    (hdis : (DNodes.Adj e a₀ ∧ ¬ DNodes.Adj e a₁) ∨ (¬ DNodes.Adj e a₀ ∧ DNodes.Adj e a₁))
    (hbpp : b ≠ pp) (hb0 : b ≠ a₀) (hb1 : b ≠ a₁) (hbe : b ≠ e)
    (hbpp' : ¬ DNodes.Adj b pp) (hb0' : ¬ DNodes.Adj b a₀) (hb1' : ¬ DNodes.Adj b a₁)
    (hbe' : ¬ DNodes.Adj b e) : False := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape (nd.mem b) (nd.cl b)
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t := by
    have := standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two
      ht.orderOf_eq_two
    exact this
  have hKJ : ∀ a, K ≠ nd.J a := fun a h => by
    have := nd.commK a
    rw [← h] at this
    exact not_commutes_self_of_mem hΩ c.hK this
  have hβJ : ∀ a, β ≠ nd.J a := fun a h => by
    have := nd.commK a
    rw [← h] at this
    exact hnKβ this
  have hKw : ∀ a, Commute z (nd.w a) := fun a =>
    (nd.commK a) z c.hz.mem (nd.w a) (nd.cl a).mem
  have mxJ : ∀ a, a ≠ b → ¬ DNodes.Adj a b → nd.J a ∈ centralizingMembers Ω {nd.w b} :=
    fun a hab hadj => nd.mem_loc b (nd.mem a) (nd.commutes_of_not_adj hab hadj)
  have mxK : K ∈ centralizingMembers Ω {nd.w b} := nd.mem_loc b c.hK (nd.commK b)
  have mxβ : β ∈ centralizingMembers Ω {nd.w b} := nd.mem_loc b hβ (hfix b hbpp)
  have hppne : ∀ a, DNodes.Adj pp a → a ≠ pp := fun a h => (DNodes.Adj.ne h).symm
  have hfix0 : Commutes β (nd.J a₀) := hfix a₀ (hppne a₀ h0)
  have hfix1 : Commutes β (nd.J a₁) := hfix a₁ (hppne a₁ h1)
  have hcomm0β : Commutes (nd.J a₀) β := commutes_symm hfix0
  have hcomm1β : Commutes (nd.J a₁) β := commutes_symm hfix1
  refine star_config cx hF (c := nd.J pp) (wc := nd.w pp)
    (l := ![nd.J a₀, nd.J a₁, β]) (w := ![nd.w a₀, nd.w a₁, t]) ?_ (nd.cl pp) ?_ ?_ ?_ ?_ ?_
  · exact mxJ pp hbpp.symm (fun h => hbpp' h.symm)
  · intro i
    fin_cases i
    · exact mxJ a₀ hb0.symm (fun h => hb0' h.symm)
    · exact mxJ a₁ hb1.symm (fun h => hb1' h.symm)
    · exact mxβ
  · intro i
    fin_cases i
    · exact nd.cl a₀
    · exact nd.cl a₁
    · exact ht
  · intro i
    fin_cases i
    · exact ⟨nd.ne_J hΩ (DNodes.Adj.ne h0), nd.not_commutes_of_adj h0, nd.commute_w h2 _ _,
        nd.conjSub_w h2 h0⟩
    · exact ⟨nd.ne_J hΩ (DNodes.Adj.ne h1), nd.not_commutes_of_adj h1, nd.commute_w h2 _ _,
        nd.conjSub_w h2 h1⟩
    · exact ⟨(hβJ pp).symm, fun h => hmov (commutes_symm h),
        (commute_of_conjSub_eq' h2 (c.hex _ (nd.mem pp)) (nd.cl pp) hnorm).symm, hnorm⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact ⟨nd.ne_J hΩ h01, nd.commutes_of_not_adj h01 h01'⟩
    · exact ⟨(hβJ a₀).symm, hcomm0β⟩
    · exact ⟨nd.ne_J hΩ h01.symm, nd.commutes_of_not_adj h01.symm (fun h => h01' h.symm)⟩
    · exact absurd rfl hij
    · exact ⟨(hβJ a₁).symm, hcomm1β⟩
    · exact ⟨hβJ a₀, hfix0⟩
    · exact ⟨hβJ a₁, hfix1⟩
    · exact absurd rfl hij
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd hij (by decide) | skip
    ·
      refine ⟨nd.J e, nd.w e, mxJ e hbe.symm (fun h => hbe' h.symm), nd.cl e, nd.ne_J hΩ hea₀,
        nd.ne_J hΩ hea₁, nd.commute_w h2 _ _, nd.commute_w h2 _ _, ?_⟩
      rcases hdis with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
      · intro hiff
        exact nd.not_commutes_of_adj ha (hiff.mpr (nd.commutes_of_not_adj hea₁ hb'))
      · intro hiff
        exact nd.not_commutes_of_adj hb' (hiff.mp (nd.commutes_of_not_adj hea₀ ha))
    ·
      exact ⟨K, z, mxK, c.hz, hKJ a₀, hKne, hKw a₀, hzt,
        fun hiff => hnKβ (hiff.mp (nd.commK a₀))⟩
    ·
      exact ⟨K, z, mxK, c.hz, hKJ a₁, hKne, hKw a₁, hzt,
        fun hiff => hnKβ (hiff.mp (nd.commK a₁))⟩

theorem scenario_B
    (hF : OrthGeom (Subgroup.center (modelUniv .POmegaPlus m p f Fact.out).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D) (GaloisField p f))
    (c : TCtx p f .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) (nd : DNodes p f m Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    {pp q a₀ a₁ a₂ e b : Fin m} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp)
    (hpp : pp = a₁ ∨ pp = a₂)
    (hq0 : DNodes.Adj q a₀) (hq1 : DNodes.Adj q a₁) (hq2 : DNodes.Adj q a₂)
    (h01 : a₀ ≠ a₁) (h02 : a₀ ≠ a₂) (h12 : a₁ ≠ a₂)
    (h01' : ¬ DNodes.Adj a₀ a₁) (h02' : ¬ DNodes.Adj a₀ a₂) (h12' : ¬ DNodes.Adj a₁ a₂)
    (hea₀ : e ≠ a₀) (hea₁ : e ≠ a₁) (hea₂ : e ≠ a₂) (he0 : DNodes.Adj e a₀)
    (he1 : ¬ DNodes.Adj e a₁) (he2 : ¬ DNodes.Adj e a₂)
    (hbq : b ≠ q) (hb0 : b ≠ a₀) (hb1 : b ≠ a₁) (hb2 : b ≠ a₂) (hbe : b ≠ e)
    (hbq' : ¬ DNodes.Adj b q) (hb0' : ¬ DNodes.Adj b a₀) (hb1' : ¬ DNodes.Adj b a₁)
    (hb2' : ¬ DNodes.Adj b a₂) (hbe' : ¬ DNodes.Adj b e) : False := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape (nd.mem b) (nd.cl b)
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hKJ : ∀ a, K ≠ nd.J a := fun a h => by
    have := nd.commK a
    rw [← h] at this
    exact not_commutes_self_of_mem hΩ c.hK this
  have hβJ : ∀ a, β ≠ nd.J a := fun a h => by
    have := nd.commK a
    rw [← h] at this
    exact hnKβ this
  have hbpp : b ≠ pp := by rcases hpp with rfl | rfl <;> assumption
  have hTw : ∀ a, Commute t (nd.w a) := fun a => by
    by_cases hap : a = pp
    · subst hap
      exact commute_of_conjSub_eq' h2 (c.hex _ (nd.mem a)) (nd.cl a) hnorm
    · exact (hfix a hap) t ht.mem (nd.w a) (nd.cl a).mem
  have mxJ : ∀ a, a ≠ b → ¬ DNodes.Adj a b → nd.J a ∈ centralizingMembers Ω {nd.w b} :=
    fun a hab hadj => nd.mem_loc b (nd.mem a) (nd.commutes_of_not_adj hab hadj)
  have mxβ : β ∈ centralizingMembers Ω {nd.w b} := nd.mem_loc b hβ (hfix b hbpp)
  have hadjq : ∀ a, DNodes.Adj q a → a ≠ q := fun a h => (DNodes.Adj.ne h).symm
  refine star_config cx hF (c := nd.J q) (wc := nd.w q)
    (l := ![nd.J a₀, nd.J a₁, nd.J a₂]) (w := ![nd.w a₀, nd.w a₁, nd.w a₂])
    (mxJ q hbq.symm (fun h => hbq' h.symm)) (nd.cl q) ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact mxJ a₀ hb0.symm (fun h => hb0' h.symm)
    · exact mxJ a₁ hb1.symm (fun h => hb1' h.symm)
    · exact mxJ a₂ hb2.symm (fun h => hb2' h.symm)
  · intro i
    fin_cases i
    · exact nd.cl a₀
    · exact nd.cl a₁
    · exact nd.cl a₂
  · intro i
    fin_cases i
    · exact ⟨nd.ne_J hΩ (DNodes.Adj.ne hq0), nd.not_commutes_of_adj hq0, nd.commute_w h2 _ _,
        nd.conjSub_w h2 hq0⟩
    · exact ⟨nd.ne_J hΩ (DNodes.Adj.ne hq1), nd.not_commutes_of_adj hq1, nd.commute_w h2 _ _,
        nd.conjSub_w h2 hq1⟩
    · exact ⟨nd.ne_J hΩ (DNodes.Adj.ne hq2), nd.not_commutes_of_adj hq2, nd.commute_w h2 _ _,
        nd.conjSub_w h2 hq2⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact ⟨nd.ne_J hΩ h01, nd.commutes_of_not_adj h01 h01'⟩
    · exact ⟨nd.ne_J hΩ h02, nd.commutes_of_not_adj h02 h02'⟩
    · exact ⟨nd.ne_J hΩ h01.symm, nd.commutes_of_not_adj h01.symm (fun h => h01' h.symm)⟩
    · exact absurd rfl hij
    · exact ⟨nd.ne_J hΩ h12, nd.commutes_of_not_adj h12 h12'⟩
    · exact ⟨nd.ne_J hΩ h02.symm, nd.commutes_of_not_adj h02.symm (fun h => h02' h.symm)⟩
    · exact ⟨nd.ne_J hΩ h12.symm, nd.commutes_of_not_adj h12.symm (fun h => h12' h.symm)⟩
    · exact absurd rfl hij
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd hij (by decide) | skip
    · refine ⟨nd.J e, nd.w e, mxJ e hbe.symm (fun h => hbe' h.symm), nd.cl e, nd.ne_J hΩ hea₀,
        nd.ne_J hΩ hea₁, nd.commute_w h2 _ _, nd.commute_w h2 _ _, ?_⟩
      intro hiff
      exact nd.not_commutes_of_adj he0 (hiff.mpr (nd.commutes_of_not_adj hea₁ he1))
    · refine ⟨nd.J e, nd.w e, mxJ e hbe.symm (fun h => hbe' h.symm), nd.cl e, nd.ne_J hΩ hea₀,
        nd.ne_J hΩ hea₂, nd.commute_w h2 _ _, nd.commute_w h2 _ _, ?_⟩
      intro hiff
      exact nd.not_commutes_of_adj he0 (hiff.mpr (nd.commutes_of_not_adj hea₂ he2))
    · refine ⟨β, t, mxβ, ht, (hβJ a₁), (hβJ a₂), hTw a₁, hTw a₂, ?_⟩
      intro hiff
      rcases hpp with rfl | rfl
      · exact hmov (hiff.mpr (hfix a₂ h12.symm))
      · exact hmov (hiff.mp (hfix a₁ h12))

theorem scenario_C
    (hF : OrthFacts (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D)
      (GaloisField p f))
    (c : TCtx p f .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) (nd : DNodes p f m Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    {pp b : Fin m} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp)
    (hbpp : b ≠ pp) (hbpp' : ¬ DNodes.Adj b pp) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (nd.J pp) := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape (nd.mem b) (nd.cl b)
  obtain ⟨W, hW⟩ := hKβ
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hβJ : β ≠ nd.J pp := fun h => by
    have := nd.commK pp
    rw [← h] at this
    exact hnKβ this
  have hnormK : conjSub t K = K :=
    conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  exact sign_config cx hF (a := K) (b := β) (d := nd.J pp) (wa := z) (wb := t) (wd := nd.w pp)
    (nd.mem_loc b c.hK (nd.commK b)) (nd.mem_loc b hβ (hfix b hbpp))
    (nd.mem_loc b (nd.mem pp) (nd.commutes_of_not_adj hbpp.symm (fun h => hbpp' h.symm)))
    c.hz ht (nd.cl pp) hKne hβJ ⟨W, hW⟩ hmov (nd.commK pp) hzt
    (commute_of_conjSub_eq' h2 (c.hex _ (nd.mem pp)) (nd.cl pp) hnorm).symm hnormK hnorm

theorem fin_ne_of_val_ne {a b : Fin m} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

local macro "idx_tac" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (apply fin_ne_of_val_ne; simp only; omega)
    | (left; apply Fin.ext; simp only; omega)
    | (right; apply Fin.ext; simp only; omega))

theorem adapted_pattern_D (hm : 7 ≤ m)
    (hF : OrthFacts (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D)
      (GaloisField p f))
    (c : TCtx p f .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) (nd : DNodes p f m Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    {pp : Fin m} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp) :
    pp.val = 0 ∧ ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (nd.J pp) := by
  have hpt : pp.val < m := pp.isLt
  have hp0 : pp.val = 0 := by
    by_contra hne
    have hp1 : 1 ≤ pp.val := Nat.one_le_iff_ne_zero.mpr hne
    have hcases : pp.val = 1 ∨ (2 ≤ pp.val ∧ pp.val + 5 ≤ m) ∨ pp.val + 4 = m ∨ pp.val + 3 = m ∨
        pp.val + 2 = m ∨ pp.val + 1 = m := by omega
    rcases hcases with h | h | h | h | h | h
    ·
      refine scenario_A hF.toOrthGeom c hsingle hshape nd hβ ht hKβ (pp := pp) (a₀ := ⟨0, by omega⟩)
        (a₁ := ⟨2, by omega⟩) (e := ⟨3, by omega⟩) (b := ⟨m - 1, by omega⟩) hfix hmov hnorm
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      idx_tac
    ·
      by_cases hs : pp.val ≤ 3
      · refine scenario_A hF.toOrthGeom c hsingle hshape nd hβ ht hKβ (pp := pp)
          (a₀ := ⟨pp.val - 1, by omega⟩) (a₁ := ⟨pp.val + 1, by omega⟩)
          (e := ⟨pp.val - 2, by omega⟩) (b := ⟨m - 1, by omega⟩) hfix hmov hnorm
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        idx_tac
      · refine scenario_A hF.toOrthGeom c hsingle hshape nd hβ ht hKβ (pp := pp)
          (a₀ := ⟨pp.val - 1, by omega⟩) (a₁ := ⟨pp.val + 1, by omega⟩)
          (e := ⟨pp.val - 2, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        idx_tac
    ·
      refine scenario_A hF.toOrthGeom c hsingle hshape nd hβ ht hKβ (pp := pp)
        (a₀ := ⟨pp.val - 1, by omega⟩) (a₁ := ⟨pp.val + 1, by omega⟩)
        (e := ⟨m - 2, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      idx_tac
    ·
      refine scenario_A hF.toOrthGeom c hsingle hshape nd hβ ht hKβ (pp := pp)
        (a₀ := ⟨m - 4, by omega⟩) (a₁ := ⟨m - 2, by omega⟩)
        (e := ⟨m - 5, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      idx_tac
    ·
      refine scenario_B hF.toOrthGeom c hsingle hshape nd hβ ht hKβ (pp := pp) (q := ⟨m - 3, by omega⟩)
        (a₀ := ⟨m - 4, by omega⟩) (a₁ := ⟨m - 2, by omega⟩) (a₂ := ⟨m - 1, by omega⟩)
        (e := ⟨m - 5, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      idx_tac
    ·
      refine scenario_B hF.toOrthGeom c hsingle hshape nd hβ ht hKβ (pp := pp) (q := ⟨m - 3, by omega⟩)
        (a₀ := ⟨m - 4, by omega⟩) (a₁ := ⟨m - 2, by omega⟩) (a₂ := ⟨m - 1, by omega⟩)
        (e := ⟨m - 5, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      idx_tac
  refine ⟨hp0, ?_⟩
  refine scenario_C hF c hsingle hshape nd hβ ht hKβ (pp := pp) (b := ⟨2, by omega⟩) hfix hmov hnorm
    ?_ ?_ <;>
  idx_tac

end Scenarios

end CFSG.ClassicalInvolution.RouteD.Gaps
