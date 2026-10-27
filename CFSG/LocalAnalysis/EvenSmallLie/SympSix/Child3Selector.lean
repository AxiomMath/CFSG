module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrders
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelSector
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelDefs
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Lagrangian
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem card_GL_dvd_glOrd_twelve {N : ℕ} (hN : N ≤ 12) :
    Nat.card (GL (Fin N) (ZMod 2)) ∣ glOrd 12 := by
  rw [Matrix.card_GL_field, ZMod.card]
  interval_cases N <;> decide +kernel

theorem card_GL_nine : Nat.card (GL (Fin 9) (ZMod 2)) = glOrd 9 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide +kernel

theorem GL3Source.dvd_card {Y : Type} [Group Y] {D : Subgroup Y} {a : Y} {J : Subgroup Y}
    (h : GL3Source D a J) : 168 ∣ Nat.card D := by
  obtain ⟨ψ⟩ := h.gl3
  have h1 := Subgroup.card_dvd_of_le h.le
  rwa [Nat.card_congr ψ.toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits.card_GL_three_two] at h1

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
open LinearMap (BilinForm)
open Module

theorem card_sp6Dstar_dvd {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
    (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
    (he : SymplecticFlag.IsSymplecticBasis b e) (z : G) {V₁ : Subgroup G}
    (hconc : Sp6LagrangianLayerConclusion φ he z V₁) [IsElementaryAbelian 2 (sp6C₂ φ he z)]
    (hC₂ : Nat.card (sp6C₂ φ he z) = 4096) :
    Nat.card (sp6Dstar φ he z) ∣ Nat.card (GL (Fin 12) (ZMod 2)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨eQ, -⟩, -, hKR, -, -, -, -, ⟨κF, -, hκker, -⟩,
    -⟩ := hconc
  set Q := sp6Qstar φ he z
  let ψ : Q →* MulAut (sp6C₂ φ he z) := κF.comp Q.subtype
  have hle : ψ.ker ≤ (sp6Ro φ he z).subgroupOf Q := by
    intro q hq
    rw [MonoidHom.mem_ker] at hq
    have hq' : (q : Sp6F φ he z) ∈ κF.ker := hq
    rw [hκker] at hq'
    exact mem_subgroupOf.2 (hKR hq')
  let π : Q ⧸ ψ.ker →* Q ⧸ (sp6Ro φ he z).subgroupOf Q :=
    QuotientGroup.map _ _ (MonoidHom.id Q) fun x hx => hle hx
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk q, rfl⟩
  calc Nat.card (sp6Dstar φ he z) = Nat.card (Q ⧸ (sp6Ro φ he z).subgroupOf Q) :=
        (Nat.card_congr eQ.toEquiv).symm
    _ ∣ Nat.card (Q ⧸ ψ.ker) := Subgroup.card_dvd_of_surjective hπ
    _ = Nat.card ψ.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    _ ∣ Nat.card (MulAut (sp6C₂ φ he z)) := Subgroup.card_subgroup_dvd_card _
    _ = Nat.card (GL (Fin 12) (ZMod 2)) := card_mulAut_eq_card_GL (by rw [hC₂]; norm_num)

theorem gl3Source_of_layerConclusion {G : Type} [Group G] {L : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
    (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
    (he : SymplecticFlag.IsSymplecticBasis b e) (z : G) {V₁ : Subgroup G}
    (hconc : Sp6LagrangianLayerConclusion φ he z V₁) (hsimple : Sp6LayerSimple φ he z) :
    GL3Source (sp6Dstar φ he z) (sp6aBar φ he z) (sp6JLBar φ he z) ∧
      Catalog (sp6Dstar φ he z) := by
  obtain ⟨-, -, -, -, ⟨ι, -, hιinj, hιrange⟩, -, hYK, -, -, -, -, hθJL, -, -, -, -, -, -,
    haBar2, hJCa, hJinf, hCa, -, -, -, -, -, -, -, -, -, -, -, hCD, -⟩ := hconc
  obtain ⟨hDs, hDn, hJD, -⟩ := hsimple
  have hψinj : Function.Injective ((sp6θ φ he z).comp ι) := by
    intro g g' hgg
    apply hιinj
    refine hθJL ?_ ?_ hgg
    · rw [← hιrange]
      exact ⟨g, rfl⟩
    · rw [← hιrange]
      exact ⟨g', rfl⟩
  have hψrange : ((sp6θ φ he z).comp ι).range = sp6JLBar φ he z := by
    rw [MonoidHom.range_comp, hιrange]
    rfl
  refine ⟨⟨Subgroup.normalClosure_normal, hDs, hDn, hCD, haBar2, hJD.le, hJCa, hCa, hJinf,
    ⟨((MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange)).symm⟩⟩, ?_⟩
  exact CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hYK (sp6Dstar φ he z)
    (MonoidHom.id _) Function.surjective_id

section Selector


theorem layer_sector_of_GL3_source (hres : ResidualExclusions) {Y : Type} [Group Y] [Finite Y]
    {D : Subgroup Y} {a : Y} {J : Subgroup Y} (h : GL3Source D a J) (hcat : Catalog D)
    {N : ℕ} (hN : N ≤ 12) (hord : Nat.card D ∣ Nat.card (GL (Fin N) (ZMod 2))) : Sector D := by
  have := h.simple
  rcases filter_twelve hcat h.nonab (hord.trans (card_GL_dvd_glOrd_twelve hN)) h.dvd_card with
    halt | ⟨t, n, p, f, hp, hs, hm⟩ | ⟨x, hx, hm⟩ | ⟨s, hs, ⟨e⟩⟩
  · exact sector_of_alternating halt
  · exact sector_of_sectorTuple hp hs hm
  · exfalso
    simp only [residualTuples12, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact hres.charThree.psl39 Y D a J h hm
    · exact hres.charThree.psu33 Y D a J h hm
    · exact hres.charThree.psu43 Y D a J h hm
    · exact hres.classical.psu35 Y D a J h hm
    · exact hres.classical.psp47 Y D a J h hm
    · exact hres.orthogonal.plus4 Y D a J h hm
    · exact hres.orthogonal.plus5 Y D a J h hm
    · exact hres.orthogonal.plus6 Y D a J h hm
    · exact hres.orthogonal.plus7 Y D a J h hm
    · exact hres.orthogonal.minus4 Y D a J h hm
    · exact hres.orthogonal.minus5 Y D a J h hm
    · exact hres.orthogonal.minus6 Y D a J h hm
    · exact hres.exceptional.g2four Y D a J h hm
    · exact hres.exceptional.g2three Y D a J h hm
    · exact hres.exceptional.d4two Y D a J h hm
    · exact hres.exceptional.f4two Y D a J h hm
    · exact hres.exceptional.e6two Y D a J h hm
  · exfalso
    simp only [residualSporadic12, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hres.sporadic.M22 Y D a J h ⟨e⟩
    · exact hres.sporadic.M23 Y D a J h ⟨e⟩
    · exact hres.sporadic.M24 Y D a J h ⟨e⟩
    · exact hres.sporadic.J2 Y D a J h ⟨e⟩
    · exact hres.sporadic.HS Y D a J h ⟨e⟩
    · exact hres.sporadic.McL Y D a J h ⟨e⟩
    · exact hres.sporadic.He Y D a J h ⟨e⟩
    · exact hres.sporadic.Suz Y D a J h ⟨e⟩
    · exact hres.sporadic.Co3 Y D a J h ⟨e⟩
    · exact hres.sporadic.Co2 Y D a J h ⟨e⟩

theorem layer_sector_of_GL3_source_nine (hres : ResidualExclusionsNine) {Y : Type} [Group Y]
    [Finite Y] {D : Subgroup Y} {a : Y} {J : Subgroup Y} (h : GL3Source D a J)
    (hcat : Catalog D) (hord : Nat.card D ∣ Nat.card (GL (Fin 9) (ZMod 2))) : Sector D := by
  have := h.simple
  rcases filter_nine hcat h.nonab (card_GL_nine ▸ hord) h.dvd_card with
    halt | ⟨t, n, p, f, hp, hs, hm⟩ | ⟨x, hx, hm⟩ | ⟨s, hs, ⟨e⟩⟩
  · exact sector_of_alternating halt
  · exact sector_of_sectorTuple hp hs hm
  · exfalso
    simp only [residualTuples9, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hres.psu33 Y D a J h hm
    · exact hres.plus4 Y D a J h hm
    · exact hres.plus5 Y D a J h hm
    · exact hres.minus4 Y D a J h hm
  · exfalso
    simp only [residualSporadic9, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl
    · exact hres.J2 Y D a J h ⟨e⟩
    · exact hres.He Y D a J h ⟨e⟩

theorem gapLagrangianSelector_of (hF : Sp6LagrangianFullOddCoreStmt)
    (hres : ResidualExclusions) : GapLagrangianSelector := by
  intro G _ _ L T z hS V _ _ _ b hb hnd hV φ e he hfull hel hsimple
  have hQ : LieModel (L ⧸ center L) .PSp 3 2 1 :=
    lieModel_quot_of_center_eq_bot hS.center_eq hS.model
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hC₂card, hbranch⟩ :=
    SteinbergBM.sp6_even_linear_branch φ he z hF hS.simple hS.nonab hS.kProper hS.standard
      hS.core hS.center_eq hQ T hS.cyclic hS.mem hS.order hb hnd hV hfull
  have := hel
  obtain ⟨-, -, -, -, V₁, hconc⟩ := hbranch hel
  obtain ⟨hsrc, hcat⟩ := gl3Source_of_layerConclusion φ he z hconc hsimple
  exact layer_sector_of_GL3_source hres hsrc hcat le_rfl
    (card_sp6Dstar_dvd φ he z hconc hC₂card)

end Selector

section Gap


theorem gapLagrangianSelector (hres : ResidualExclusions) : GapLagrangianSelector :=
  gapLagrangianSelector_of (fullOddCore_of_schreier CFSG.RankThree.PartOne.SPOR.schreierFor_catalog)
    hres

end Gap

end CFSG.EvenSmallLie.Child3
