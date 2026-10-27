module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.FFTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Normalizer
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.Component

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin
open scoped commutatorElement

@[expose] def gomiBinaryRepresentation {W : Type} [CommGroup W] [Fact (∀ w : W, w * w = 1)]
    (Y : Subgroup (MulAut W)) : Representation (ZMod 2) ↥Y (Additive W) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((CFSG.QuasithinUnique.Setup.Family.binaryLin (W := W)).comp Y.subtype)

theorem gomiBinaryRepresentation_injective {W : Type} [CommGroup W]
    [Fact (∀ w : W, w * w = 1)] (Y : Subgroup (MulAut W)) :
    Function.Injective (gomiBinaryRepresentation Y) := by
  intro y y' h
  apply Subtype.ext
  apply CFSG.QuasithinUnique.Setup.Family.binaryLin_injective
  ext v
  exact congrArg (fun f : Additive W →ₗ[ZMod 2] Additive W => f v) h

theorem le_normalizer_of_offender_component {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {Y L A : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hcomp : CFSG.IsComponent (L.subgroupOf Y)) (hA : IsFFStarOffender Y A) :
    A ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  have hCo : CFSG.Open.IsComponentOf L Y :=
    CFSG.Quasithin.isComponentOf_iff_subgroupOf.mpr
      ⟨hLY, (CFSG.isComponent_iff_open (L.subgroupOf Y)).mp hcomp⟩
  exact CFSG.Quasithin.B15P4.asB15Part4 W (fun v => by rw [pow_two]; exact hW v) Y A hA L hCo

theorem commutator_eq_self_of_offender {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {Y L A : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hcomp : CFSG.IsComponent (L.subgroupOf Y)) (hA : IsFFStarOffender Y A)
    (hAnC : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W))) : ⁅L, A⁆ = L := by
  have hKq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY) hcomp.1
  refine CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.commutator_eq_of_ne_bot hKq
    (le_normalizer_of_offender_component hW hLY hcomp hA) ?_
  intro hbot
  rw [Subgroup.commutator_comm] at hbot
  exact hAnC (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)

theorem isElemBestOffender_subgroupOf {W : Type} [CommGroup W] [Finite W]
    [Fact (∀ w : W, w * w = 1)] {Y A : Subgroup (MulAut W)}
    (hA : IsFFStarOffender Y A) :
    CFSG.RankThree.FFModules.IsElemBestOffender (gomiBinaryRepresentation Y) (A.subgroupOf Y) := by
  have hmap : (A.subgroupOf Y).map
      (CFSG.Quasithin.FFModel.repMulAut (gomiBinaryRepresentation Y)) = A := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro ha
      exact ⟨⟨a, hA.1 ha⟩, ha, by ext w; rfl⟩
  have hle : (A.subgroupOf Y).map
      (CFSG.Quasithin.FFModel.repMulAut (gomiBinaryRepresentation Y)) ≤ Y := by
    rw [hmap]; exact hA.1
  exact ((CFSG.HardMathSupport.Meierfrankenfeld.Proving.FFTransport.isFFStarOffender_map_iff
    (gomiBinaryRepresentation_injective Y) hle).mp (by rw [hmap]; exact hA)).2

theorem le_normalizer_and_commutator_subgroupOf {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {Y L A : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hcomp : CFSG.IsComponent (L.subgroupOf Y)) (hA : IsFFStarOffender Y A)
    (hAnC : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W))) :
    A.subgroupOf Y ≤ Subgroup.normalizer ((L.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) ∧
      ⁅L.subgroupOf Y, A.subgroupOf Y⁆ = L.subgroupOf Y := by
  constructor
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro k
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp
      (le_normalizer_of_offender_component hW hLY hcomp hA ha) (k : MulAut W)
  · apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLY,
      Subgroup.map_subgroupOf_eq_of_le hA.1]
    exact commutator_eq_self_of_offender hW hLY hcomp hA hAnC

private theorem exists_irrSection_of_offender {W : Type} [CommGroup W] [Finite W]
    [fact : Fact (∀ w : W, w * w = 1)] (hW : ∀ w : W, w * w = 1)
    {Y L A : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hcomp : CFSG.IsComponent (L.subgroupOf Y)) (hA : IsFFStarOffender Y A)
    (hAnC : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W))) :
    ∃ (W' : Type) (_ : CommGroup W') (_ : Finite W') (Lb Eb : Subgroup (MulAut W')),
      (∀ w : W', w * w = 1) ∧ CFSG.QuasithinUnique.Setup.X1.IsIrrOn Lb ∧
      CFSG.IsQuasisimple ↥Lb ∧ Eb ≠ ⊥ ∧ IsElemAbelian2 Eb ∧
      Eb ≤ Subgroup.normalizer (Lb : Set (MulAut W')) ∧
      Nat.card W' ≤ Nat.card Eb * Nat.card (fixV Eb) ∧
      ∃ ψ : ↥(L.subgroupOf Y) →* ↥Lb, Function.Surjective ψ := by
  let K := L.subgroupOf Y
  let A' := A.subgroupOf Y
  let ρ := gomiBinaryRepresentation Y
  have hKq : CFSG.IsQuasisimple ↥K := hcomp.1
  have hbest := isElemBestOffender_subgroupOf hA
  have hρ := gomiBinaryRepresentation_injective Y
  have hfaith : ∀ a ∈ A', (∀ v : Additive W, ρ a v = v) → a = 1 := by
    intro a _ ha
    apply hρ
    rw [map_one]
    exact LinearMap.ext ha
  have hb : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsBestOffenderOn ρ A' ⊤ :=
    (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.isBestOffender_iff_on ρ A' hfaith).mp
      ⟨hbest.1, hbest.2⟩
  obtain ⟨hAK, hKA⟩ := le_normalizer_and_commutator_subgroupOf hW hLY hcomp hA hAnC
  have hKnt : ¬ K ≤ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.cenOn ρ K ⊤ := by
    intro hle
    have hbot : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.cenOn ρ K ⊤ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have hx1 : ρ x = 1 := LinearMap.ext fun u => hx.2 u Submodule.mem_top
      exact hρ (by rw [hx1, map_one])
    rw [hbot] at hle
    exact CFSG.QuasithinUnique.Setup.X1.ne_bot_of_isQuasisimple hKq (le_bot_iff.mp hle)
  obtain ⟨W', hW'c, hW'f, Lb, Eb, hW'2, hirr, hq, hE0, hEel, -, hEN, hoff, ψ, hψ⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.exists_irrSection ρ K A' hKq hbest.1
      hAK hKA hKnt hb
  exact ⟨W', hW'c, hW'f, Lb, Eb, hW'2, hirr, hq, hE0, hEel, hEN, hoff, ψ, hψ⟩

private theorem pCore_eq_bot_of_irr {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {Lb : Subgroup (MulAut W)}
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn Lb) : CFSG.pCore 2 ↥Lb = ⊥ := by
  unfold CFSG.pCore
  rw [sSup_eq_bot]
  rintro P ⟨hPn, hP2⟩
  have hPm2 : IsPGroup 2 ↥(P.map Lb.subtype) := hP2.map Lb.subtype
  have hfix : fixV (P.map Lb.subtype) ≠ ⊥ :=
    @CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.fixV_ne_bot_of_isPGroup'
      W _ _ (fun v => by rw [pow_two]; exact hW v) hirr.1 (P.map Lb.subtype) hPm2
  have hinv : ∀ g ∈ Lb, ∀ u ∈ fixV (P.map Lb.subtype), g u ∈ fixV (P.map Lb.subtype) := by
    intro g hg u hu
    rw [mem_fixV] at hu ⊢
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hq
    have hinvg : g⁻¹ ∈ Lb := Lb.inv_mem hg
    have hconj : (⟨g⁻¹, hinvg⟩ * p * ⟨g⁻¹, hinvg⟩⁻¹) ∈ P :=
      hPn.conj_mem p hp ⟨g⁻¹, hinvg⟩
    have hmem : ((g⁻¹ : MulAut W) * (p : MulAut W) * g) u = u :=
      hu _ (Subgroup.mem_map_of_mem Lb.subtype hconj)
    have h1 : (p : MulAut W) * g = g * ((g⁻¹ : MulAut W) * (p : MulAut W) * g) := by group
    calc (p : MulAut W) (g u) = ((p : MulAut W) * g) u := rfl
      _ = (g * ((g⁻¹ : MulAut W) * (p : MulAut W) * g)) u := by rw [h1]
      _ = g (((g⁻¹ : MulAut W) * (p : MulAut W) * g) u) := rfl
      _ = g u := by rw [hmem]
  rcases hirr.2 (fixV (P.map Lb.subtype)) hinv with hbot | htop
  · exact absurd hbot hfix
  · rw [eq_bot_iff]
    intro p hp
    rw [Subgroup.mem_bot]
    ext w
    have hw : w ∈ fixV (P.map Lb.subtype) := by rw [htop]; exact Subgroup.mem_top w
    exact mem_fixV.mp hw _ (Subgroup.mem_map_of_mem Lb.subtype hp)

private theorem centralizer_inf_eq_center {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {Lb Eb : Subgroup (MulAut W)}
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn Lb)
    (hEN : Eb ≤ Subgroup.normalizer (Lb : Set (MulAut W))) (hEel : IsElemAbelian2 Eb) :
    (Lb ⊔ Eb) ⊓ Subgroup.centralizer (Lb : Set (MulAut W)) =
      (Subgroup.center ↥Lb).map Lb.subtype := by
  refine le_antisymm ?_ ?_
  · intro c hc
    have hcL : c ∈ Lb := CFSG.QuasithinUnique.Setup.X1.centralizer_inf_le hW hirr hEN hEel hc
    refine Subgroup.mem_map.mpr ⟨⟨c, hcL⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc.2 l l.2
  · rintro c hc
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hc
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (by simp), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩)

theorem isGomiQuad_of_section {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {Lb Eb : Subgroup (MulAut W)}
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn Lb) (hq : CFSG.IsQuasisimple ↥Lb)
    (hE0 : Eb ≠ ⊥) (hEel : IsElemAbelian2 Eb)
    (hEN : Eb ≤ Subgroup.normalizer (Lb : Set (MulAut W)))
    (hoff : Nat.card W ≤ Nat.card Eb * Nat.card (fixV Eb)) :
    IsGomiQuad (Lb ⊔ Eb) Eb Lb := by
  refine ⟨⟨le_sup_right, hE0, hEel, hoff⟩, le_sup_left, ?_, hq, ?_,
    centralizer_inf_eq_center hW hirr hEN hEel, rfl⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hEN)
  · exact pCore_eq_bot_of_irr hW hirr

theorem gomiFact34_holds : GomiFact34 := by
  intro W _ _ hW Y L hLY hcomp _ hJ
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  let fact : Fact (∀ w : W, w * w = 1) := ⟨hW'⟩
  obtain ⟨A, hA, hAnC⟩ : ∃ A : Subgroup (MulAut W),
      IsFFStarOffender Y A ∧ ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    by_contra h
    refine hJ (iSup_le fun A => iSup_le fun hA => ?_)
    by_contra hAc
    exact h ⟨A, hA, hAc⟩
  obtain ⟨W', hW'c, hW'f, Lb, Eb, hW'2, hirr, hq, hE0, hEel, hEN, hoff, ψ, hψ⟩ :=
    exists_irrSection_of_offender (fact := fact) hW' hLY hcomp hA hAnC
  refine ⟨W', hW'c, hW'f, ?_⟩
  refine ⟨fun w => by rw [pow_two]; exact hW'2 w, Lb ⊔ Eb, Eb, Lb,
    isGomiQuad_of_section hW'2 hirr hq hE0 hEel hEN hoff, ?_⟩
  refine ⟨ψ.comp (Subgroup.subgroupOfEquivOfLe hLY).symm.toMonoidHom, ?_⟩
  exact hψ.comp (Subgroup.subgroupOfEquivOfLe hLY).symm.surjective

end CFSG.GroupTheory

end
