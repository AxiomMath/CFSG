module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAltLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Overgroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X35 CFSG.QuasithinUnique.Setup.X6
  CFSG.Quasithin CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem comm_central_left {G : Type*} [Group G] {z : G} (h : z ∈ Subgroup.center G)
    (a b : G) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : ⁅z, b⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp h b).symm
  have h2 : z * ⁅a, b⁆ * z⁻¹ = ⁅a, b⁆ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp h _).symm
  rw [h2, h1, mul_one]

theorem comm_central_right {G : Type*} [Group G] {z : G} (h : z ∈ Subgroup.center G)
    (a b : G) : ⁅a, z * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h1 : ⁅a, z⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp h a)
  have h2 : z * ⁅a, b⁆ * z⁻¹ = ⁅a, b⁆ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp h _).symm
  rw [h1, one_mul, h2]

theorem center_eq_bot_of_odd_central_extension_GL3
    {L : Type*} [Group L] [Finite L]
    (hperf : Group.IsPerfect L) (α : (L ⧸ Subgroup.center L) ≃* GL32)
    (hodd : Odd (Nat.card (Subgroup.center L))) : Subgroup.center L = ⊥ := by
  let π : L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    ((slEquivGL 3).symm.toMonoidHom.comp α.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π :=
    ((slEquivGL 3).symm.surjective.comp α.surjective).comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := by
    ext l
    rw [MonoidHom.mem_ker]
    show (slEquivGL 3).symm (α (QuotientGroup.mk' (Subgroup.center L) l)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff l
  obtain ⟨s, hs, -, -⟩ := CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting
    (K := ZMod 2) (n := 3) (by norm_num) hπ hker.le (by rw [hker]; exact hodd)
  have hdec : ∀ l : L, l * (s (π l))⁻¹ ∈ Subgroup.center L := by
    intro l
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]
  have hcomm : commutator L ≤ s.range := by
    show ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ ≤ s.range
    refine Subgroup.commutator_le.mpr (fun l₁ _ l₂ _ => ?_)
    have key : ⁅l₁, l₂⁆ = ⁅s (π l₁), s (π l₂)⁆ := by
      calc ⁅l₁, l₂⁆ = ⁅(l₁ * (s (π l₁))⁻¹) * s (π l₁), (l₂ * (s (π l₂))⁻¹) * s (π l₂)⁆ := by
            rw [inv_mul_cancel_right, inv_mul_cancel_right]
        _ = ⁅s (π l₁), (l₂ * (s (π l₂))⁻¹) * s (π l₂)⁆ :=
            comm_central_left (hdec l₁) _ _
        _ = ⁅s (π l₁), s (π l₂)⁆ := comm_central_right (hdec l₂) _ _
    rw [key, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  have hRtop : s.range = ⊤ := by
    rw [eq_top_iff, ← Group.isPerfect_def.mp hperf]
    exact hcomm
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hz1 : π z = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact hz
  have hzs : z ∈ s.range := by rw [hRtop]; exact Subgroup.mem_top z
  obtain ⟨g, rfl⟩ := hzs
  have hg : g = 1 := by rw [← hs g]; exact hz1
  rw [hg, map_one]

@[expose] def GL3GraphNormalizerExclusionProp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
    ∀ G L : Subgroup (MulAut V), IsComp L G → Nonempty (↥L ≃* GL32) →
      (∃ g ∈ G, g ∈ Subgroup.normalizer (L : Set (MulAut V)) ∧
        ∀ l ∈ L, ¬ ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹) →
      ∀ A : Subgroup (MulAut V), IsBestOffender G A → ⁅L, A⁆ = ⊥

theorem uniqueMax_covBy {G : Type*} [Group G] {R P D : Subgroup G} (h : IsUniqueMaxOver R P D) :
    R ≤ P ∧ P ⋖ D ∧ ∀ M, M ⋖ D → R ≤ M → M = P := by
  obtain ⟨hRP, hPD, hY⟩ := h
  refine ⟨hRP, ⟨hPD, fun c hPc hcD => ?_⟩, fun M hMD hRM => ?_⟩
  · exact absurd (hY c (hRP.trans hPc.le) hcD) (not_le_of_gt hPc)
  · have hMP : M ≤ P := hY M hRM hMD.lt
    by_contra hne
    exact hMD.2 (lt_of_le_of_ne hMP hne) hPD

theorem noGL3Component
    (hlayer : ActorLayerProp) (hT : ActorComponentTransfer)
    (hT1 : X1.ComponentTransferProp) (hd6 : GL3GraphNormalizerExclusionProp) :
    NoGL3ComponentProp := by
  intro V _ _ H T M E hFF hns L hL ⟨e⟩
  have hLay : ActorLayer V H T M := hlayer V H T M E hFF hns
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := hLay.odd_card_center hL
  have hqs : CFSG.IsQuasisimple ↥L := isQuasisimple_of_isComp hL
  have hperf : Group.IsPerfect ↥L := hqs.1
  have hZ : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_odd_central_extension_GL3 hperf e hZodd
  let e' : ↥L ≃* GL32 :=
    ((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e)
  obtain ⟨hSyl, -, P, hP⟩ := hT V H T M E hFF.toActorBase hns L (isComponentIn_of_isComp hL)
  obtain ⟨α, hαD, hαout⟩ := GL3_outer_of_unique_max e' (inner_le_autOn hL.1) hSyl
    (uniqueMax_covBy hP)
  obtain ⟨⟨g, hgN⟩, hgH, hgα⟩ := Subgroup.mem_map.1 hαD
  have hgH' : g ∈ H := hgH
  have hαg : ∀ y : ↥L, ((α y : ↥L) : MulAut V) = g * (y : MulAut V) * g⁻¹ := fun y => by
    rw [← hgα]
    show ((conjAct L ⟨g, hgN⟩ y : ↥L) : MulAut V) = _
    rw [conjAct]
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hout : ∀ l ∈ L, ¬ ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹ := fun l hl hcon => by
    apply hαout
    refine ⟨⟨l, hl⟩, ?_⟩
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [hαg y, hcon y y.2]
    simp [MulAut.conj_apply]
  obtain ⟨A, hAT, hAel, hAL, hAoff, hAstrict⟩ := (hT1 V H T M E hFF hns L hL).offender
  have hnt : Nontrivial GL32 := ⟨⟨unitriGL 1 0 0, 1, fun h => by
    have := congrArg (fun x : GL32 => (x : Mat3) 0 1) h
    simp [unitriGL, unitri] at this⟩⟩
  have hL1 : L ≠ ⊥ := fun h => by
    have : Nontrivial ↥L := (e'.toEquiv.nontrivial_congr).2 hnt
    exact (Subgroup.nontrivial_iff_ne_bot L).1 this h
  have hA0 : A ≠ ⊥ := fun h => hL1 (by rw [← hAL, h, Subgroup.commutator_bot_right])
  have hAH : A ≤ H := hAT.trans (inf_le_left.trans hFF.sylow.1)
  have hbest : IsBestOffender H A := ⟨hAH, hA0, hAel, hAoff, hAstrict⟩
  have h1 := hd6 V hFF.elementary H L hL ⟨e'⟩ ⟨g, hgH', hgN, hout⟩ A hbest
  exact hL1 (by rw [← hAL, h1])

end CFSG.QuasithinUnique.Setup.Family