module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.GroupTheory.SylowIntersectionControl.GomiSectionTools
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact34Holds
import CFSG.GroupTheory.SylowIntersectionControl.GomiQuadFF
import CFSG.Quasithin.Background.B1MoreElevenE
import CFSG.Quasithin.Background.B1More13B
import CFSG.HardMathSupport.Cooperstein.Coordinator.TripleA7
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem exists_center_generator {L : Subgroup (MulAut W)}
    (hZ : Nat.card (Subgroup.center ↥L) = 3) :
    ∃ zL : ↥L, orderOf zL = 3 ∧ Subgroup.center ↥L = Subgroup.zpowers zL ∧
      zL ∈ Subgroup.center ↥L := by
  have h3 : 3 ∣ Nat.card (Subgroup.center ↥L) := by rw [hZ]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨zc, hzc⟩ := exists_prime_orderOf_dvd_card' 3 h3
  set zL : ↥L := (zc : ↥L) with hzL
  have hzLo : orderOf zL = 3 := by rw [hzL, Subgroup.orderOf_coe, hzc]
  refine ⟨zL, hzLo, ?_, ?_⟩
  · symm
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.2 zc.2
    · rw [hZ, Nat.card_zpowers, hzLo]
  · exact zc.2

omit [Finite W] in
private theorem conj_mem_zpowers_of_normalizer {L A : Subgroup (MulAut W)} {zL : ↥L}
    (hzLc : zL ∈ Subgroup.center ↥L)
    (hcen : Subgroup.center ↥L = Subgroup.zpowers zL)
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    ∀ a ∈ A, a * (zL : MulAut W) * a⁻¹ ∈ Subgroup.zpowers (zL : MulAut W) := by
  intro a ha
  have hmemL : a * (zL : MulAut W) * a⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.1 (hAN ha) (zL : MulAut W)).1 zL.2
  have hc : (⟨a * (zL : MulAut W) * a⁻¹, hmemL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hg' : a⁻¹ * g * a ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (hAN (A.inv_mem ha)) g).1 g.2
      rwa [inv_inv] at this
    have hcomm' : (a⁻¹ * g * a) * (zL : MulAut W) = (zL : MulAut W) * (a⁻¹ * g * a) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hzLc ⟨a⁻¹ * g * a, hg'⟩)
    show (g : MulAut W) * (a * (zL : MulAut W) * a⁻¹) = a * (zL : MulAut W) * a⁻¹ * g
    calc (g : MulAut W) * (a * (zL : MulAut W) * a⁻¹)
        = a * ((a⁻¹ * g * a) * (zL : MulAut W)) * a⁻¹ := by group
      _ = a * ((zL : MulAut W) * (a⁻¹ * g * a)) * a⁻¹ := by rw [hcomm']
      _ = a * (zL : MulAut W) * a⁻¹ * g := by group
  rw [hcen] at hc
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hc
  exact Subgroup.mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩

omit [Finite W] in
private theorem not_le_centSub_commV {L : Subgroup (MulAut W)} {z : MulAut W} {zL : ↥L}
    (hz : (zL : MulAut W) = z) (hVne : commV (Subgroup.zpowers z) ≠ ⊥)
    (hfree : ∀ v ∈ commV (Subgroup.zpowers z), z v = v → v = 1) :
    ¬ L ≤ centSub (commV (Subgroup.zpowers z)) := by
  intro hle
  apply hVne
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  have hzfix : z v = v := by simpa [hz] using hle zL.2 v hv
  exact hfree v hv hzfix

omit [Finite W] in
private theorem commutator_autSub_eq {L A : Subgroup (MulAut W)} {V₁ : Subgroup W}
    (hLV₁ : ∀ l ∈ L, ∀ v ∈ V₁, l v ∈ V₁) (hAV₁ : ∀ a ∈ A, ∀ v ∈ V₁, a v ∈ V₁)
    (hLA : ⁅L, A⁆ = L) :
    ⁅autSub L V₁, autSub A V₁⁆ = autSub L V₁ := by
  have hLstab : L ≤ stabSub V₁ := B1.le_stabSub_of_invariant hLV₁
  have hAstab : A ≤ stabSub V₁ := B1.le_stabSub_of_invariant hAV₁
  have hHstab : L ⊔ A ≤ stabSub V₁ := sup_le hLstab hAstab
  let f : ↥(L ⊔ A) →* MulAut V₁ := (resHom V₁).comp (Subgroup.inclusion hHstab)
  have hLmap : (L.subgroupOf (L ⊔ A)).map f = autSub L V₁ := by
    rw [B1Red.autSub_eq_range hLstab]
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      exact ⟨⟨(l : MulAut W), Subgroup.mem_subgroupOf.mp hl⟩, rfl⟩
    · rintro _ ⟨⟨l, hl⟩, rfl⟩
      exact ⟨⟨l, Subgroup.mem_sup_left hl⟩, hl, rfl⟩
  have hAmap : (A.subgroupOf (L ⊔ A)).map f = autSub A V₁ := by
    rw [B1Red.autSub_eq_range hAstab]
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨⟨(a : MulAut W), Subgroup.mem_subgroupOf.mp ha⟩, rfl⟩
    · rintro _ ⟨⟨a, ha⟩, rfl⟩
      exact ⟨⟨a, Subgroup.mem_sup_right ha⟩, ha, rfl⟩
  have hcomm : ⁅L.subgroupOf (L ⊔ A), A.subgroupOf (L ⊔ A)⁆ = L.subgroupOf (L ⊔ A) := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (L ⊔ A))
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
      Subgroup.map_subgroupOf_eq_of_le le_sup_right, hLA]
  rw [← hLmap, ← hAmap, ← Subgroup.map_commutator, hcomm]

private structure OffenderData {W : Type} [CommGroup W] [Finite W] where
  hW : ∀ w : W, w ^ 2 = 1
  Y : Subgroup (MulAut W)
  L : Subgroup (MulAut W)
  hLY : L ≤ Y
  hcomp : CFSG.IsComponent (L.subgroupOf Y)
  hLq : CFSG.IsQuasisimple ↥L
  hZ : Nat.card (Subgroup.center ↥L) = 3
  hA7 : IsAlt (↥L ⧸ Subgroup.center ↥L) 7
  hJ : ¬ ffJ Y ≤ Subgroup.centralizer (L : Set (MulAut W))
  A : Subgroup (MulAut W)
  hA : IsFFStarOffender Y A
  hAnC : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W))
  hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W))
  hLA : ⁅L, A⁆ = L
  zL : ↥L
  hzLo : orderOf zL = 3
  hcen : Subgroup.center ↥L = Subgroup.zpowers zL
  hzLc : zL ∈ Subgroup.center ↥L
  hz3 : (zL : MulAut W) ^ 3 = 1
  hz1 : (zL : MulAut W) ≠ 1

private def OffenderData.z {W : Type} [CommGroup W] [Finite W]
    (D : OffenderData (W := W)) : MulAut W := (D.zL : MulAut W)

private theorem OffenderData.hzdef {W : Type} [CommGroup W] [Finite W]
    (D : OffenderData (W := W)) : D.z = (D.zL : MulAut W) := rfl

private noncomputable def buildOffenderData {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hcomp : CFSG.IsComponent (L.subgroupOf Y)) (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (hA7 : IsAlt (↥L ⧸ Subgroup.center ↥L) 7)
    (hJ : ¬ ffJ Y ≤ Subgroup.centralizer (L : Set (MulAut W))) :
    OffenderData (W := W) := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  have hX : ⁅L, ffJ Y⁆ ≠ ⊥ := by
    intro h
    apply hJ
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact h
  classical
  have hEx : ∃ A : Subgroup (MulAut W),
      IsFFStarOffender Y A ∧ ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    obtain ⟨A, hA, -, hAnC⟩ :=
      CFSG.Quasithin.B113.exists_offender_not_le_centralizer (G := Y) (T := Y) (X := L) le_rfl hX
    exact ⟨A, hA, hAnC⟩
  choose A hA hAnC using hEx
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    le_normalizer_of_offender_component hW' hLY hcomp hA
  have hLA : ⁅L, A⁆ = L := commutator_eq_self_of_offender hW' hLY hcomp hA hAnC
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY) hcomp.1
  choose zL hzLo hcen hzLc using exists_center_generator hZ
  have hzo : orderOf (zL : MulAut W) = 3 := by rw [Subgroup.orderOf_coe, hzLo]
  have hz3 : (zL : MulAut W) ^ 3 = 1 := hzo ▸ pow_orderOf_eq_one (zL : MulAut W)
  have hz1 : (zL : MulAut W) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzo
    omega
  exact ⟨hW, Y, L, hLY, hcomp, hLq, hZ, hA7, hJ, A, hA, hAnC, hAN, hLA,
    zL, hzLo, hcen, hzLc, hz3, hz1⟩

private structure CommVData {W : Type} [CommGroup W] [Finite W] extends OffenderData (W := W) where
  V₁ : Subgroup W
  hV₁def : V₁ = commV (Subgroup.zpowers (zL : MulAut W))
  hV₁ne : V₁ ≠ ⊥
  hV₁free : ∀ v ∈ V₁, (zL : MulAut W) v = v → v = 1
  hV₁sq : ∀ v : V₁, v * v = 1
  hLV₁ : ∀ l ∈ L, ∀ v ∈ V₁, l v ∈ V₁
  hAV₁ : ∀ a ∈ A, ∀ v ∈ V₁, a v ∈ V₁
  hHstab : L ⊔ A ≤ stabSub V₁

private noncomputable def buildCommVData {W : Type} [CommGroup W] [Finite W]
    (D : OffenderData (W := W)) : CommVData (W := W) := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact D.hW w
  set V₁ : Subgroup W := commV (Subgroup.zpowers D.z) with hV₁def
  have hV₁ne : V₁ ≠ ⊥ := by
    obtain ⟨u, hu, hu1⟩ :=
      CFSG.HardMathSupport.Cooperstein.Coordinator.TripleA7.exists_ne_one_mem_commV D.hz1
    exact fun h => hu1 (by
      have hu' : u ∈ V₁ := hu
      rw [h] at hu'
      exact Subgroup.mem_bot.mp hu')
  have hV₁free : ∀ v ∈ V₁, D.z v = v → v = 1 := fun v hv =>
    CFSG.HardMathSupport.Cooperstein.Coordinator.TripleA7.eq_one_of_mem_commV_of_apply_eq
      D.hW D.hz3 hv
  have hV₁sq : ∀ v : V₁, v * v = 1 := fun v => Subtype.ext (hW' v.1)
  have hLV₁ : ∀ l ∈ D.L, ∀ v ∈ V₁, l v ∈ V₁ := by
    intro l hl v hv
    have hk : l * D.z * l⁻¹ ∈ Subgroup.zpowers D.z := by
      have h1' : l * (D.zL : MulAut W) = (D.zL : MulAut W) * l :=
        congrArg Subtype.val (Subgroup.mem_center_iff.1 D.hzLc ⟨l, hl⟩)
      have h2 : l * (D.zL : MulAut W) * l⁻¹ = (D.zL : MulAut W) := by
        rw [h1']
        group
      rw [D.hzdef, h2]
      exact Subgroup.mem_zpowers (D.zL : MulAut W)
    exact CFSG.HardMathSupport.Cooperstein.Coordinator.TripleA7.apply_mem_commV_zpowers hk hv
  have hAV₁ : ∀ a ∈ D.A, ∀ v ∈ V₁, a v ∈ V₁ := by
    intro a ha v hv
    have hk : a * D.z * a⁻¹ ∈ Subgroup.zpowers D.z := by
      have h := conj_mem_zpowers_of_normalizer (L := D.L) (A := D.A) (zL := D.zL)
        D.hzLc D.hcen D.hAN a ha
      rwa [← D.hzdef] at h
    exact CFSG.HardMathSupport.Cooperstein.Coordinator.TripleA7.apply_mem_commV_zpowers hk hv
  have hHstab : D.L ⊔ D.A ≤ stabSub V₁ :=
    sup_le (B1.le_stabSub_of_invariant hLV₁) (B1.le_stabSub_of_invariant hAV₁)
  exact ⟨D, V₁, rfl, hV₁ne, hV₁free, hV₁sq, hLV₁, hAV₁, hHstab⟩

private structure AutSubOffenderData {W : Type} [CommGroup W] [Finite W]
    extends CommVData (W := W) where
  L₁ : Subgroup (MulAut V₁)
  A₁ : Subgroup (MulAut V₁)
  Y₁ : Subgroup (MulAut V₁)
  hL₁def : L₁ = autSub L V₁
  hA₁def : A₁ = autSub A V₁
  hY₁def : Y₁ = autSub (L ⊔ A) V₁
  hL₁Y₁ : L₁ ≤ Y₁
  hA₁le : A₁ ≤ Y₁
  hL₁qOpen : CFSG.Open.IsQuasisimple ↥L₁
  hL₁q : CFSG.IsQuasisimple ↥L₁
  hKA : ⁅L₁, A₁⁆ = L₁
  hA₁off : IsFFStarOffender Y₁ A₁

private noncomputable def buildAutSubOffenderData {W : Type} [CommGroup W] [Finite W]
    (D : CommVData (W := W)) : AutSubOffenderData (W := W) := by
  set L₁ : Subgroup (MulAut D.V₁) := autSub D.L D.V₁ with hL₁def
  set A₁ : Subgroup (MulAut D.V₁) := autSub D.A D.V₁ with hA₁def
  set Y₁ : Subgroup (MulAut D.V₁) := autSub (D.L ⊔ D.A) D.V₁ with hY₁def
  have hL₁Y₁ : L₁ ≤ Y₁ := autSub_mono le_sup_left D.V₁
  have hA₁le : A₁ ≤ Y₁ := autSub_mono le_sup_right D.V₁
  have hL₁qOpen : CFSG.Open.IsQuasisimple ↥L₁ :=
    CFSG.Quasithin.B1Red.isQuasisimple_autSub (B1.le_stabSub_of_invariant D.hLV₁)
      (CFSG.Quasithin.B1Red.isQuasisimple_to_open
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe D.hLY) D.hcomp.1))
      (D.hV₁def ▸ not_le_centSub_commV (z := D.z) (zL := D.zL) D.hzdef.symm
        (D.hV₁def ▸ D.hV₁ne) (D.hV₁def ▸ D.hV₁free))
  have hL₁q : CFSG.IsQuasisimple ↥L₁ := CFSG.Quasithin.B1Red.isQuasisimple_of_open hL₁qOpen
  have hKA : ⁅L₁, A₁⁆ = L₁ := by
    simpa [L₁, A₁] using commutator_autSub_eq D.hLV₁ D.hAV₁ D.hLA
  have hA₁off : IsFFStarOffender Y₁ A₁ := by
    have hAH : IsFFStarOffender (D.L ⊔ D.A) D.A := ⟨le_sup_right, D.hA.2⟩
    have hnt : ¬ D.A ≤ centSub D.V₁ := by
      intro hle
      have hA₁bot : A₁ = ⊥ := by
        rw [eq_bot_iff]
        intro a ha
        rw [Subgroup.mem_bot]
        obtain ⟨x, hx, rfl⟩ := mem_autSub.mp ha
        apply MulEquiv.ext
        intro v
        apply Subtype.ext
        have hxv : (x : MulAut W) (v : W) = v := hle hx v v.2
        simpa [CFSG.Quasithin.resHom_apply] using hxv
      rw [hA₁bot] at hKA
      have hbot : ⁅L₁, (⊥ : Subgroup (MulAut D.V₁))⁆ = ⊥ := by simp
      rw [hbot] at hKA
      exact CFSG.QuasithinUnique.Setup.X1.ne_bot_of_isQuasisimple hL₁q hKA.symm
    exact CFSG.Quasithin.B1Red.isFFStarOffender_autSub hAH D.hAV₁ hnt
  exact ⟨D, L₁, A₁, Y₁, rfl, rfl, rfl, hL₁Y₁, hA₁le, hL₁qOpen, hL₁q, hKA, hA₁off⟩

private theorem normal_subgroupOf_autSub {W : Type} [CommGroup W] [Finite W]
    (D : AutSubOffenderData (W := W)) : (D.L₁.subgroupOf D.Y₁).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer D.hL₁Y₁).2 ?_
  intro y hy
  rw [D.hY₁def] at hy
  obtain ⟨h, hh, rfl⟩ := mem_autSub.mp hy
  rw [Subgroup.mem_normalizer_iff]
  intro l₁
  constructor
  · intro hl₁
    rw [D.hL₁def] at hl₁
    obtain ⟨l, hl, rfl⟩ := mem_autSub.mp hl₁
    have hh' : (h : MulAut W) ∈ D.L ⊔ D.A := by simpa using hh
    have hl' : (l : MulAut W) ∈ D.L := by simpa using hl
    have hmem : (h : MulAut W) * (l : MulAut W) * (h : MulAut W)⁻¹ ∈ D.L :=
      (Subgroup.mem_normalizer_iff.1 (sup_le Subgroup.le_normalizer D.hAN hh')
        (l : MulAut W)).1 hl'
    have hstab : (h : MulAut W) * (l : MulAut W) * (h : MulAut W)⁻¹ ∈ stabSub D.V₁ :=
      (B1.le_stabSub_of_invariant D.hLV₁) hmem
    rw [D.hL₁def]
    refine mem_autSub.mpr ⟨⟨(h : MulAut W) * (l : MulAut W) * (h : MulAut W)⁻¹,
      hstab⟩, hmem, ?_⟩
    rw [← map_mul, ← map_inv]
    rfl
  · intro hl₁
    rw [D.hL₁def] at hl₁
    obtain ⟨l, hl, hl_eq⟩ := mem_autSub.mp hl₁
    have hh' : (h : MulAut W) ∈ D.L ⊔ D.A := by simpa using hh
    have hl' : (l : MulAut W) ∈ D.L := by simpa using hl
    have hmem : (h : MulAut W)⁻¹ * (l : MulAut W) * (h : MulAut W) ∈ D.L :=
      (Subgroup.mem_normalizer_iff.1 (sup_le Subgroup.le_normalizer D.hAN ((D.L ⊔ D.A).inv_mem hh'))
        (l : MulAut W)).1 hl'
    have hstab : (h : MulAut W)⁻¹ * (l : MulAut W) * (h : MulAut W) ∈ stabSub D.V₁ :=
      (B1.le_stabSub_of_invariant D.hLV₁) hmem
    rw [D.hL₁def]
    refine mem_autSub.mpr ⟨⟨(h : MulAut W)⁻¹ * (l : MulAut W) * (h : MulAut W),
      hstab⟩, hmem, ?_⟩
    have hres : (resHom D.V₁) ⟨(h : MulAut W)⁻¹ * (l : MulAut W) * (h : MulAut W), hstab⟩ =
        ((resHom D.V₁) h)⁻¹ * (resHom D.V₁) l * (resHom D.V₁) h := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hres, hl_eq]
    group

private structure AutSubNormalData {W : Type} [CommGroup W] [Finite W]
    extends AutSubOffenderData (W := W) where
  hL₁n : (L₁.subgroupOf Y₁).Normal
  hcomp' : CFSG.IsComponent (L₁.subgroupOf Y₁)

private noncomputable def buildAutSubNormalData {W : Type} [CommGroup W] [Finite W]
    (D : AutSubOffenderData (W := W)) : AutSubNormalData (W := W) := by
  have hL₁n : (D.L₁.subgroupOf D.Y₁).Normal := normal_subgroupOf_autSub D
  have hcomp' : CFSG.IsComponent (D.L₁.subgroupOf D.Y₁) := by
    have hCo₁ : CFSG.Open.IsComponentOf D.L₁ D.Y₁ :=
      ⟨D.hL₁Y₁, CFSG.Open.IsSubnormal.step D.hL₁Y₁ hL₁n (CFSG.Open.IsSubnormal.refl _),
        D.hL₁qOpen⟩
    exact (CFSG.isComponent_iff_open (D.L₁.subgroupOf D.Y₁)).mpr
      ((CFSG.Quasithin.isComponentOf_iff_subgroupOf.mp hCo₁).2)
  exact ⟨D, hL₁n, hcomp'⟩

private structure AutSubData {W : Type} [CommGroup W] [Finite W]
    extends AutSubNormalData (W := W) where
  hAK' : A₁.subgroupOf Y₁ ≤ Subgroup.normalizer
    ((L₁.subgroupOf Y₁ : Subgroup ↥Y₁) : Set ↥Y₁)
  hKA' : ⁅L₁.subgroupOf Y₁, A₁.subgroupOf Y₁⁆ = L₁.subgroupOf Y₁

private noncomputable def buildAutSubData {W : Type} [CommGroup W] [Finite W]
    (D : AutSubNormalData (W := W)) : AutSubData (W := W) := by
  have hAK' : D.A₁.subgroupOf D.Y₁ ≤ Subgroup.normalizer
      ((D.L₁.subgroupOf D.Y₁ : Subgroup ↥D.Y₁) : Set ↥D.Y₁) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      rw [Subgroup.mem_subgroupOf] at hl ⊢
      exact (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_of_offender_component D.hV₁sq D.hL₁Y₁ D.hcomp' D.hA₁off ha) l).1 hl
    · intro hl
      rw [Subgroup.mem_subgroupOf] at hl ⊢
      exact (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_of_offender_component D.hV₁sq D.hL₁Y₁ D.hcomp' D.hA₁off ha) l).2 hl
  have hKA' : ⁅D.L₁.subgroupOf D.Y₁, D.A₁.subgroupOf D.Y₁⁆ = D.L₁.subgroupOf D.Y₁ := by
    apply Subgroup.map_injective D.Y₁.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le D.hL₁Y₁,
      Subgroup.map_subgroupOf_eq_of_le D.hA₁le]
    exact D.hKA
  exact ⟨D, hAK', hKA'⟩

private structure SectionModuleData {W : Type} [CommGroup W] [Finite W]
    extends AutSubData (W := W) where
  fact : Fact (∀ v : V₁, v * v = 1)
  ρ : Representation (ZMod 2) ↥Y₁ (Additive V₁)
  hρ : Function.Injective ρ
  hρapply : ∀ (y : ↥Y₁) (v : Additive V₁),
    ρ y v = Additive.ofMul ((y : MulAut V₁) (Additive.toMul v))
  hbest : RankThree.FFModules.IsElemBestOffender ρ (A₁.subgroupOf Y₁)
  hfaith : ∀ a ∈ A₁.subgroupOf Y₁, (∀ v : Additive V₁, ρ a v = v) → a = 1
  hb : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsBestOffenderOn ρ
    (A₁.subgroupOf Y₁) ⊤
  hKnt : ¬ L₁.subgroupOf Y₁ ≤
    CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.cenOn ρ (L₁.subgroupOf Y₁) ⊤

private noncomputable def buildSectionModuleData {W : Type} [CommGroup W] [Finite W]
    (D : AutSubData (W := W)) : SectionModuleData (W := W) := by
  let fact : Fact (∀ v : D.V₁, v * v = 1) := ⟨D.hV₁sq⟩
  let ρ : Representation (ZMod 2) ↥D.Y₁ (Additive D.V₁) :=
    @gomiBinaryRepresentation D.V₁ _ fact D.Y₁
  have hρ : Function.Injective ρ := @gomiBinaryRepresentation_injective D.V₁ _ fact D.Y₁
  have hρapply : ∀ (y : ↥D.Y₁) (v : Additive D.V₁),
      ρ y v = Additive.ofMul ((y : MulAut D.V₁) (Additive.toMul v)) := by
    intro y v
    rfl
  have hbest : RankThree.FFModules.IsElemBestOffender ρ (D.A₁.subgroupOf D.Y₁) := by
    simpa [ρ] using @isElemBestOffender_subgroupOf D.V₁ _ _ fact D.Y₁ D.A₁ D.hA₁off
  have hfaith : ∀ a ∈ D.A₁.subgroupOf D.Y₁,
      (∀ v : Additive D.V₁, ρ a v = v) → a = 1 := by
    intro a _ ha
    apply hρ
    rw [map_one]
    exact LinearMap.ext ha
  have hb : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsBestOffenderOn ρ
      (D.A₁.subgroupOf D.Y₁) ⊤ :=
    (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.isBestOffender_iff_on ρ
      (D.A₁.subgroupOf D.Y₁) hfaith).mp ⟨hbest.1, hbest.2⟩
  have hKnt : ¬ D.L₁.subgroupOf D.Y₁ ≤
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.cenOn ρ
        (D.L₁.subgroupOf D.Y₁) ⊤ := by
    intro hle
    have hbot : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.cenOn ρ
        (D.L₁.subgroupOf D.Y₁) ⊤ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have hx1 : ρ x = 1 := LinearMap.ext fun u => hx.2 u Submodule.mem_top
      exact hρ (by rw [hx1, map_one])
    rw [hbot] at hle
    exact CFSG.QuasithinUnique.Setup.X1.ne_bot_of_isQuasisimple D.hcomp'.1
      (le_bot_iff.mp hle)
  exact ⟨D, fact, ρ, hρ, hρapply, hbest, hfaith, hb, hKnt⟩

private structure SectionElementData {W : Type} [CommGroup W] [Finite W]
    extends SectionModuleData (W := W) where
  z₁ : ↥L₁
  hzLstab : (zL : MulAut W) ∈ stabSub V₁
  hz₁def : (z₁ : MulAut V₁) = resHom V₁ ⟨(zL : MulAut W), hzLstab⟩
  k : ↥(L₁.subgroupOf Y₁)
  hkval : (k : MulAut V₁) = z₁
  hkfix : ∀ v : Additive V₁, ρ k v = v → v = 0

private noncomputable def buildSectionElementData {W : Type} [CommGroup W] [Finite W]
    (D : SectionModuleData (W := W)) : SectionElementData (W := W) := by
  have hzLstab : D.z ∈ stabSub D.V₁ := by
    have h : (D.zL : MulAut W) ∈ stabSub D.V₁ :=
      B1.le_stabSub_of_invariant D.hLV₁ D.zL.2
    rwa [← D.hzdef] at h
  have hz₁mem : resHom D.V₁ ⟨D.z, hzLstab⟩ ∈ D.L₁ := by
    have hzmem : (D.zL : MulAut W) ∈ D.L := D.zL.2
    have hzmem' : D.z ∈ D.L := by
      rwa [← D.hzdef] at hzmem
    have h : resHom D.V₁ ⟨D.z, hzLstab⟩ ∈ autSub D.L D.V₁ :=
      mem_autSub.mpr ⟨⟨D.z, hzLstab⟩, hzmem', rfl⟩
    rwa [← D.hL₁def] at h
  let z₁ : ↥D.L₁ := ⟨resHom D.V₁ ⟨D.z, hzLstab⟩, hz₁mem⟩
  let k : ↥(D.L₁.subgroupOf D.Y₁) := ⟨⟨z₁.1, D.hL₁Y₁ z₁.2⟩, z₁.2⟩
  have hkfix : ∀ v : Additive D.V₁, D.ρ k v = v → v = 0 := by
    intro v hv
    have hv' : (Additive.toMul v : D.V₁) = 1 := by
      apply Subtype.ext
      refine D.hV₁free (((Additive.toMul v : D.V₁)) : W)
        (Additive.toMul v).2 ?_
      have h1 : (D.z : MulAut W) (((Additive.toMul v : D.V₁)) : W) =
          (((Additive.toMul v : D.V₁)) : W) := by
        have := congrArg (fun x : Additive D.V₁ => ((Additive.toMul x : D.V₁) : W)) hv
        rw [D.hρapply k v] at this
        simpa [k, z₁, resHom, D.hzdef, CFSG.Quasithin.resAut] using this
      exact h1
    have := congrArg Additive.ofMul hv'
    simpa using this
  exact ⟨D, z₁, hzLstab, rfl, k, rfl, hkfix⟩

private structure SectionData {W : Type} [CommGroup W] [Finite W]
    extends SectionElementData (W := W) where
  W' : Type
  hW'c : CommGroup W'
  hW'f : Finite W'
  Lb : Subgroup (MulAut W')
  Eb : Subgroup (MulAut W')
  hW'2 : ∀ w : W', w * w = 1
  hirr : IsIrrOn Lb
  hq : CFSG.IsQuasisimple ↥Lb
  hE0 : Eb ≠ ⊥
  hEel : IsElemAbelian2 Eb
  hEq : IsQuadratic Eb
  hEN : Eb ≤ Subgroup.normalizer (Lb : Set (MulAut W'))
  hoff : Nat.card W' ≤ Nat.card Eb * Nat.card (fixV Eb)
  ψ : ↥(L₁.subgroupOf Y₁) →* ↥Lb
  hψ : Function.Surjective ψ
  hψk : ψ k ≠ 1

private noncomputable def buildSectionData {W : Type} [CommGroup W] [Finite W]
    (D : SectionElementData (W := W)) : SectionData (W := W) := by
  classical
  choose W' hW'c hW'f Lb Eb hW'2 hirr hq hE0 hEel hEq hEN hoff ψ hψ hψk using
    @exists_irrSection_fixedPointFree ↥D.Y₁ _ _ (Additive D.V₁) _
      (CFSG.QuasithinUnique.Setup.Family.binaryModule (W := D.V₁) (h := D.fact)) _
      D.ρ (D.L₁.subgroupOf D.Y₁) (D.A₁.subgroupOf D.Y₁) D.hcomp'.1 D.hbest.1
      D.hAK' D.hKA' D.hKnt D.hb D.k D.hkfix
  exact ⟨D, W', hW'c, hW'f, Lb, Eb, hW'2, hirr, hq, hE0, hEel, hEq, hEN, hoff, ψ, hψ, hψk⟩

private structure PhiData {W : Type} [CommGroup W] [Finite W]
    extends SectionData (W := W) where
  resL : ↥L →* ↥L₁
  hresL : Function.Surjective resL
  ψL : ↥L₁ →* ↥Lb
  φ : ↥L →* ↥Lb
  hφsurj : Function.Surjective φ
  hφz : φ zL ≠ 1

private noncomputable def buildPhiData {W : Type} [CommGroup W] [Finite W]
    (D : SectionData (W := W)) : PhiData (W := W) := by
  let resL : ↥D.L →* ↥D.L₁ :=
    ((resHom D.V₁).comp (Subgroup.inclusion (B1.le_stabSub_of_invariant D.hLV₁))).codRestrict
      D.L₁ fun l => by
        rw [D.hL₁def, B1Red.autSub_eq_range (B1.le_stabSub_of_invariant D.hLV₁)]
        exact ⟨l, rfl⟩
  have hresL : Function.Surjective resL := by
    intro y
    have hy : (y : MulAut D.V₁) ∈ ((resHom D.V₁).comp
        (Subgroup.inclusion (B1.le_stabSub_of_invariant D.hLV₁))).range := by
      have hy' : (y : MulAut D.V₁) ∈ autSub D.L D.V₁ := by
        rw [← D.hL₁def]
        exact y.2
      rwa [B1Red.autSub_eq_range (B1.le_stabSub_of_invariant D.hLV₁)] at hy'
    obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hy
    refine ⟨l, ?_⟩
    apply Subtype.ext
    exact hl
  let ψL : ↥D.L₁ →* ↥D.Lb :=
    D.ψ.comp (Subgroup.subgroupOfEquivOfLe D.hL₁Y₁).symm.toMonoidHom
  let φ : ↥D.L →* ↥D.Lb := ψL.comp resL
  have hφsurj : Function.Surjective φ :=
    (D.hψ.comp (Subgroup.subgroupOfEquivOfLe D.hL₁Y₁).symm.surjective).comp hresL
  have hφz : φ D.zL ≠ 1 := by
    intro h1
    apply D.hψk
    have hres : resL D.zL = D.z₁ := by
      apply Subtype.ext
      rw [D.hz₁def]
      rfl
    have hψL : ψL D.z₁ = D.ψ D.k := by
      apply congrArg D.ψ
      apply Subtype.ext
      apply Subtype.ext
      simpa only [MulEquiv.coe_toMonoidHom, D.hkval] using
        Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe D.hL₁Y₁ D.z₁
    have h1' : ψL D.z₁ = 1 := by
      rw [← hres]
      exact h1
    rwa [hψL] at h1'
  exact ⟨D, resL, hresL, ψL, φ, hφsurj, hφz⟩

private structure KernelData {W : Type} [CommGroup W] [Finite W]
    extends PhiData (W := W) where
  hker : φ.ker = ⊥
  hφinj : Function.Injective φ

private noncomputable def buildKernelData {W : Type} [CommGroup W] [Finite W]
    (D : PhiData (W := W)) : KernelData (W := W) := by
  have hker : D.φ.ker = ⊥ := by
    have hle := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple D.hLq
      (φ := D.φ) ⟨D.zL, D.hφz⟩
    have hdvd : Nat.card ↥D.φ.ker ∣ 3 := by
      have h1 : Nat.card ↥(D.φ.ker.subgroupOf (Subgroup.center ↥D.L)) ∣
          Nat.card (Subgroup.center ↥D.L) :=
        Subgroup.card_subgroup_dvd_card _
      rw [D.hZ] at h1
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
    have hne3 : Nat.card ↥D.φ.ker ≠ 3 := by
      intro h3
      have hcenter : D.φ.ker = Subgroup.center ↥D.L :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [h3, D.hZ])
      have hzcenter : D.zL ∈ Subgroup.center ↥D.L := by
        rw [D.hcen]
        exact Subgroup.mem_zpowers D.zL
      exact D.hφz ((MonoidHom.mem_ker).mp (hcenter.symm ▸ hzcenter))
    have hpos : 0 < Nat.card ↥D.φ.ker := Nat.card_pos
    have h1 : Nat.card ↥D.φ.ker = 1 := by
      rcases Nat.dvd_prime (by norm_num : Nat.Prime 3) |>.mp hdvd with h | h
      · exact h
      · exact absurd h hne3
    exact Subgroup.card_eq_one.mp h1
  have hφinj : Function.Injective D.φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxker : x ∈ D.φ.ker := MonoidHom.mem_ker.mpr hx
    rw [hker] at hxker
    exact Subgroup.mem_bot.mp hxker
  exact ⟨D, hker, hφinj⟩

private structure FinalData {W : Type} [CommGroup W] [Finite W]
    extends KernelData (W := W) where
  eL : ↥L ≃* ↥Lb
  hZLb : Nat.card (Subgroup.center ↥Lb) = 3
  hQ : IsGomiQuad (Lb ⊔ Eb) Eb Lb
  hquot : (↥L ⧸ Subgroup.center ↥L) ≃* (↥Lb ⧸ Subgroup.center ↥Lb)

private noncomputable def buildFinalData {W : Type} [CommGroup W] [Finite W]
    (D : KernelData (W := W)) : FinalData (W := W) := by
  let eL : ↥D.L ≃* ↥D.Lb := MulEquiv.ofBijective D.φ ⟨D.hφinj, D.hφsurj⟩
  have hZLb : Nat.card (Subgroup.center ↥D.Lb) = 3 := by
    have hmap := Subgroup.map_center_eq eL
    have hcard : Nat.card (Subgroup.center ↥D.Lb) =
        Nat.card (Subgroup.center ↥D.L) := by
      calc Nat.card (Subgroup.center ↥D.Lb)
          = Nat.card (Subgroup.map (eL : ↥D.L →* ↥D.Lb) (Subgroup.center ↥D.L)) := by
            rw [hmap]
        _ = Nat.card (Subgroup.center ↥D.L) :=
            Subgroup.card_map_of_injective eL.injective
    rw [hcard, D.hZ]
  have hQ := @isGomiQuad_of_section D.W' D.hW'c D.hW'f D.hW'2 D.Lb D.Eb
    D.hirr D.hq D.hE0 D.hEel D.hEN D.hoff
  have hquot : (↥D.L ⧸ Subgroup.center ↥D.L) ≃*
      (↥D.Lb ⧸ Subgroup.center ↥D.Lb) :=
    CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple D.hLq D.hφsurj
      (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple D.hLq (φ := D.φ) ⟨D.zL, D.hφz⟩)
  exact ⟨D, eL, hZLb, hQ, hquot⟩

private theorem final_contradiction {W : Type} [CommGroup W] [Finite W]
    (D : FinalData (W := W)) : False := by
  obtain ⟨eA7⟩ := D.hA7
  exact @IsGomiQuad.false_of_tripleA7 D.W' D.hW'c D.hW'f
    (D.Lb ⊔ D.Eb) D.Eb D.Lb D.hQ
    CFSG.HardMathSupport.Cooperstein.Coordinator.gf2NoFFTripleA7
    (fun w => by simpa [pow_two] using D.hW'2 w) D.hZLb (D.hquot.symm.trans eA7)

theorem ffJ_le_centralizer_of_tripleA7
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hcomp : CFSG.IsComponent (L.subgroupOf Y)) (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (hA7 : IsAlt (↥L ⧸ Subgroup.center ↥L) 7) :
    ffJ Y ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
  by_contra hJ
  let D1 : OffenderData (W := W) := buildOffenderData hW hLY hcomp hZ hA7 hJ
  let D2 : CommVData (W := W) := buildCommVData D1
  let D3 : AutSubOffenderData (W := W) := buildAutSubOffenderData D2
  let D4 : AutSubNormalData (W := W) := buildAutSubNormalData D3
  let D5 : AutSubData (W := W) := buildAutSubData D4
  let D6 : SectionModuleData (W := W) := buildSectionModuleData D5
  let D7 : SectionElementData (W := W) := buildSectionElementData D6
  let D8 : SectionData (W := W) := buildSectionData D7
  let D9 : PhiData (W := W) := buildPhiData D8
  let D10 : KernelData (W := W) := buildKernelData D9
  let D11 : FinalData (W := W) := buildFinalData D10
  exact final_contradiction D11

theorem not_tripleA7_of_gomiFact37Hyp
    (hW : ∀ w : W, w ^ 2 = 1) {Y S L : Subgroup (MulAut W)} (hH : GomiFact37Hyp Y S L)
    (hJ : ⁅L, ffJ Y⁆ ≠ ⊥) :
    ¬ (CFSG.IsQuasisimple ↥L ∧ Nat.card (Subgroup.center ↥L) = 3 ∧
        IsAlt (↥L ⧸ Subgroup.center ↥L) 7) := by
  rintro ⟨hLq, hZ, hA7⟩
  have hLY : L ≤ Y := hH.2.2.1
  have hsub : (L.subgroupOf Y).IsSubnormal := hH.2.2.2.1
  have hLq' : CFSG.IsQuasisimple ↥(L.subgroupOf Y) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm hLq
  have hcomp : CFSG.IsComponent (L.subgroupOf Y) := ⟨hLq', hsub⟩
  have hle := ffJ_le_centralizer_of_tripleA7 hW hLY hcomp hZ hA7
  have hJ' : ⁅ffJ Y, L⁆ ≠ ⊥ := by rwa [Subgroup.commutator_comm]
  exact hJ' (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle)

end CFSG.GroupTheory

end
