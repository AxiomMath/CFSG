module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalSuz
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Root
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDichotomy

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

section Central

variable {P Q : Type*} [Group P] [Group Q]

@[expose] def centralQuotEquivOfSurjective (hP : Group.IsPerfect P) (f : P →* Q)
    (hf : Function.Surjective f) (hker : f.ker ≤ center P) : P ⧸ center P ≃* Q ⧸ center Q :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
        LocalCores.comap_center_eq_of_perfect hP f hf hker] :
      center P = ((QuotientGroup.mk' (center Q)).comp f).ker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))

theorem open_isQuasisimple_of_surjective (hP : Group.IsPerfect P) (f : P →* Q)
    (hf : Function.Surjective f) (hker : f.ker ≤ center P) (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple P := by
  have := hQ.2
  exact ⟨hP.commutator_eq_top, (centralQuotEquivOfSurjective hP f hf hker).isSimpleGroup⟩

theorem isSimpleGroup_of_psl {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSL n p f) : IsSimpleGroup S :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ _ _ _ h).2

end Central

section Lift

variable {G : Type*} [Group G] {W : Type*} [Group W] {X : Subgroup W} {A : Subgroup G}
  {ψ : normalizer (A : Set G) →* W} {S : Subgroup W}

theorem psi_commutatorElement {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    ψ ⟨⁅x, y⁆, le_normalizer (RankTwoL3Even.commutatorElement_mem' hx hy)⟩ =
      ⁅ψ ⟨x, le_normalizer hx⟩, ψ ⟨y, le_normalizer hy⟩⁆ :=
  map_commutatorElement ψ ⟨x, le_normalizer hx⟩ ⟨y, le_normalizer hy⟩

theorem ker_leviLiftPsi_le_center (hψ : IsActionHom A X ψ) :
    (leviLiftPsi ψ S).ker ≤ center (leviLift ψ S) := by
  intro l h
  rw [MonoidHom.mem_ker] at h
  have hC : (l : G) ∈ centralizer (A : Set G) := by
    refine (hψ.eq_one_iff ⟨l, le_normalizer (leviLift_le l.2)⟩).1 ?_
    have := congrArg Subtype.val h
    rwa [leviLiftPsi_apply] at this
  rw [mem_center_iff]
  intro l'
  exact Subtype.ext (mem_centralizer_iff.1 hC l' (leviLift_le l'.2))

theorem isQuasisimple_leviLift_of_open (hψ : IsActionHom A X ψ) (hS : S ≤ X)
    (hperf : ⁅S, S⁆ = S) (hSq : CFSG.Open.IsQuasisimple ↥S) :
    CFSG.Open.IsQuasisimple ↥(leviLift ψ S) :=
  open_isQuasisimple_of_surjective ((Subgroup.isPerfect_iff).2 (commutator_leviLift hψ hS hperf))
    _ (leviLiftPsi_surjective hψ hS hperf) (ker_leviLiftPsi_le_center hψ) hSq

theorem layerCentralizer_eq_leviLift (hψ : IsActionHom A X ψ) {Q : Subgroup G} (hQA : Q ≤ A)
    (hQS : ∀ w (hw : w ∈ Q), ∀ s ∈ S,
      ψ ⟨w, le_normalizer (hQA hw)⟩ * s = s * ψ ⟨w, le_normalizer (hQA hw)⟩)
    (hN : ∀ x (hx : x ∈ A ⊓ centralizer (Q : Set G)),
      ψ ⟨x, le_normalizer (mem_inf.1 hx).1⟩ ∈ normalizer (S : Set W))
    (hcomm : ∀ x (hx : x ∈ A ⊓ centralizer (Q : Set G)) y (hy : y ∈ A ⊓ centralizer (Q : Set G)),
      ψ ⟨⁅x, y⁆, le_normalizer (RankTwoL3Even.commutatorElement_mem' (mem_inf.1 hx).1
        (mem_inf.1 hy).1)⟩ ∈ S)
    (hq : CFSG.Open.IsQuasisimple ↥(leviLift ψ S)) :
    layerCentralizer A Q = leviLift ψ S := by
  have hLC : leviLift ψ S ≤ A ⊓ centralizer (Q : Set G) :=
    le_inf leviLift_le fun l hl => mem_centralizer_iff.2 fun w hw =>
      (mem_centralizer_singleton_iff.1 (leviLift_le_centralizer hψ (le_normalizer (hQA hw))
        (hQS w hw) hl)).symm
  have hcommC : ⁅A ⊓ centralizer (Q : Set G), A ⊓ centralizer (Q : Set G)⁆ ≤ liftIn ψ S := by
    rw [commutator_le]
    intro x hx y hy
    exact mem_liftIn.2 ⟨RankTwoL3Even.commutatorElement_mem' (mem_inf.1 hx).1 (mem_inf.1 hy).1,
      hcomm x hx y hy⟩
  apply le_antisymm
  · have hE : layerCentralizer A Q = ⁅layerCentralizer A Q, layerCentralizer A Q⁆ := by
      rw [layerCentralizer, ← map_commutator, LocalCores.layer_perfect]
    have h1 : layerCentralizer A Q ≤ liftIn ψ S := by
      rw [hE]
      exact (commutator_mono (layerCentralizer_le A Q) (layerCentralizer_le A Q)).trans hcommC
    rw [hE]
    exact commutator_mono h1 h1
  · have hn : ((leviLift ψ S).subgroupOf (A ⊓ centralizer (Q : Set G))).Normal :=
      (normal_subgroupOf_iff_le_normalizer hLC).2 fun c hc =>
        mem_normalizer_leviLift (le_normalizer (mem_inf.1 hc).1) (hN c hc)
    have hq' : CFSG.IsQuasisimple ↥((leviLift ψ S).subgroupOf (A ⊓ centralizer (Q : Set G))) :=
      (AssemblyBPredicates.isQuasisimple_iff_native _).1
        (isQuasisimple_of_equiv (subgroupOfEquivOfLe hLC).symm hq)
    have hcomp : CFSG.IsComponent ((leviLift ψ S).subgroupOf (A ⊓ centralizer (Q : Set G))) :=
      ⟨hq', hn.isSubnormal⟩
    intro l hl
    exact ⟨⟨l, hLC hl⟩, LocalCores.component_le_layer hcomp (mem_subgroupOf.2 hl), rfl⟩

end Lift

section Inn

variable {K : Type} [Field K]

@[expose] def g2Inn (K : Type) [Field K] (S : Subgroup (ModGL .G2 K)) :
    Subgroup (MulAut ↥(adjointGroup .G2 K)) :=
  (S.subgroupOf (adjointGroup .G2 K)).map
    (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K))

theorem conj_mem_g2Inn {S : Subgroup (ModGL .G2 K)} {y : ↥(adjointGroup .G2 K)}
    (hy : (y : ModGL .G2 K) ∈ S) : MulAut.conj y ∈ g2Inn K S :=
  ⟨y, mem_subgroupOf.2 hy, rfl⟩

theorem mem_g2Inn {S : Subgroup (ModGL .G2 K)} {φ : MulAut ↥(adjointGroup .G2 K)} :
    φ ∈ g2Inn K S ↔ ∃ y : ↥(adjointGroup .G2 K), (y : ModGL .G2 K) ∈ S ∧ MulAut.conj y = φ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, mem_subgroupOf.1 hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact conj_mem_g2Inn hy

theorem g2Inn_le_range (S : Subgroup (ModGL .G2 K)) :
    g2Inn K S ≤ (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range :=
  map_le_range _ _

theorem commutator_g2Inn {S : Subgroup (ModGL .G2 K)} (hSC : S ≤ adjointGroup .G2 K)
    (hS : ⁅S, S⁆ = S) : ⁅g2Inn K S, g2Inn K S⁆ = g2Inn K S := by
  rw [g2Inn, ← map_commutator, commutator_subgroupOf_eq hSC hS]

variable [Finite K]

theorem coe_mem_of_conj_mem_g2Inn
    {S : Subgroup (ModGL .G2 K)}
    {y : ↥(adjointGroup .G2 K)} (h : MulAut.conj y ∈ g2Inn K S) : (y : ModGL .G2 K) ∈ S := by
  obtain ⟨y', hy', hyy'⟩ := h
  rw [RankTwoHypIIY.conj_injective_of_center_eq_bot
    LieType.Chevalley.center_adjointGroup_eq_bot hyy'] at hy'
  exact mem_subgroupOf.1 hy'

@[expose] def g2InnEquiv
    {S : Subgroup (ModGL .G2 K)}
    (hSC : S ≤ adjointGroup .G2 K) : ↥S ≃* ↥(g2Inn K S) :=
  (subgroupOfEquivOfLe hSC).symm.trans (equivMapOfInjective _ _
    (RankTwoHypIIY.conj_injective_of_center_eq_bot LieType.Chevalley.center_adjointGroup_eq_bot))

omit [Finite K] in
theorem conj_mem_normalizer_g2Inn {S : Subgroup (ModGL .G2 K)} {x : ↥(adjointGroup .G2 K)}
    (hx : (x : ModGL .G2 K) ∈ normalizer (S : Set (ModGL .G2 K))) :
    MulAut.conj x ∈ normalizer (g2Inn K S : Set (MulAut ↥(adjointGroup .G2 K))) := by
  rw [mem_normalizer_iff]
  intro φ
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨x * y * x⁻¹, mem_subgroupOf.2 ((mem_normalizer_iff.1 hx _).1 (mem_subgroupOf.1 hy)),
      ?_⟩
    rw [map_mul, map_mul, map_inv]
  · rintro ⟨y, hy, hφ⟩
    refine ⟨x⁻¹ * y * x, mem_subgroupOf.2 ?_, ?_⟩
    · have h := (mem_normalizer_iff.1 (inv_mem hx) (y : ModGL .G2 K)).1 (mem_subgroupOf.1 hy)
      simpa using h
    · rw [map_mul, map_mul, map_inv, hφ]
      group

end Inn

section G2Q

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem torus_r_c (t : Kˣ) (x : K) :
    torusElt .G2 K g2ir t * pinnedX .G2 K g2c x * (torusElt .G2 K g2ir t)⁻¹ =
      pinnedX .G2 K g2c x := by
  rw [root_torus_conjugation g2ir isRoot_g2c t x]
  have h : ∑ j, Tag.G2.cartan g2ir j * g2c j = 0 := by decide
  rw [h, zpow_zero, Units.val_one, one_mul]

omit [Finite K] in
theorem g2TorusR_le_g2LongCent
    : g2TorusR K ≤ g2LongCent K := by
  rintro _ ⟨t, rfl⟩
  refine mem_inf.2 ⟨torusElt_mem_adjointGroup g2ir t, mem_centralizer_singleton_iff.2 ?_⟩
  change torusElt .G2 K g2ir t * pinnedX .G2 K g2c 1 = pinnedX .G2 K g2c 1 * torusElt .G2 K g2ir t
  calc torusElt .G2 K g2ir t * pinnedX .G2 K g2c 1
      = torusElt .G2 K g2ir t * pinnedX .G2 K g2c 1 * (torusElt .G2 K g2ir t)⁻¹ *
          torusElt .G2 K g2ir t := by group
    _ = pinnedX .G2 K g2c 1 * torusElt .G2 K g2ir t := by rw [torus_r_c]

omit [Finite K] in
theorem g2TorusR_comm
    {h h' : ModGL .G2 K} (hh : h ∈ g2TorusR K)
    (hh' : h' ∈ g2TorusR K) : h * h' = h' * h := by
  obtain ⟨t, rfl⟩ := hh
  obtain ⟨t', rfl⟩ := hh'
  rw [← map_mul, ← map_mul, mul_comm]

@[expose] def g2Q
    (ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K))
    (T : Subgroup G) : Subgroup G :=
  CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) ⊓ liftIn ψ (g2Inn K (g2TorusR K))

variable {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

omit [Finite G] [Finite K] in
theorem g2Q_le : g2Q ψ T ≤ A :=
  fun _ hw => (mem_liftIn.1 (mem_inf.1 hw).2).1

omit [Finite G] [Finite K] in
theorem psi_mem_of_mem_g2Q
    {w : G} (hw : w ∈ g2Q ψ T) :
    ψ ⟨w, le_normalizer (g2Q_le hw)⟩ ∈ g2Inn K (g2TorusR K) :=
  (mem_liftIn.1 (mem_inf.1 hw).2).2

theorem leviLift_g2LongCent_le
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184 : G2Centr184) [CharP K 2] (hK4 : 4 ≤ Nat.card K) (hc : Sec3 A R T g)
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hT : ActsIn ψ T (rootSubgroup .G2 K g2c)) :
    leviLift ψ (g2Inn K (g2LongCent K)) ≤
      CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  obtain ⟨hperf, hcent⟩ := h184 K hK4
  have hTP : ∀ u ∈ T, ∀ huN : u ∈ normalizer (A : Set G), ∀ s ∈ g2Inn K (g2LongCent K),
      ψ ⟨u, huN⟩ * s = s * ψ ⟨u, huN⟩ := by
    intro u hu huN s hs
    obtain ⟨y, hy⟩ := exists_psi_eq_conj hc h32 h4 h34 hψ hu huN
    have hyC : (y : ModGL .G2 K) ∈ g2Centralizer K (g2LongCent K : Set (ModGL .G2 K)) := by
      rw [hcent]
      exact hT u hu huN y hy
    obtain ⟨d, hd, rfl⟩ := hs
    rw [hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.1 (mem_inf.1 hyC).2 d (mem_subgroupOf.1 hd)).symm
  exact CFSG.Quasithin.le_perfectCore_of_perfect
    (le_inf leviLift_le fun l hl => mem_centralizer_iff.2 fun u hu =>
      (mem_centralizer_singleton_iff.1 (leviLift_le_centralizer hψ (hc.le_normalizer hu)
        (hTP u hu _) hl)).symm)
    (commutator_leviLift hψ (g2Inn_le_range _) (commutator_g2Inn inf_le_left hperf))

theorem exists_mem_g2Q
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184 : G2Centr184) [CharP K 2] (hK4 : 4 ≤ Nat.card K) (hc : Sec3 A R T g)
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hT : ActsIn ψ T (rootSubgroup .G2 K g2c)) {y : ↥(adjointGroup .G2 K)}
    (hy : (y : ModGL .G2 K) ∈ g2TorusR K) :
    ∃ w, ∃ hw : w ∈ g2Q ψ T, ψ ⟨w, le_normalizer (g2Q_le hw)⟩ = MulAut.conj y := by
  obtain ⟨hperf, -⟩ := h184 K hK4
  obtain ⟨l, hl, hlψ⟩ := exists_mem_leviLift hψ (g2Inn_le_range _)
    (commutator_g2Inn inf_le_left hperf) (conj_mem_g2Inn (g2TorusR_le_g2LongCent hy))
  refine ⟨l, mem_inf.2 ⟨leviLift_g2LongCent_le h4 h32 h184 hK4 hc hψ hT hl,
    mem_liftIn.2 ⟨leviLift_le hl, ?_⟩⟩, hlψ⟩
  rw [hlψ]
  exact conj_mem_g2Inn hy

theorem coe_mem_g2Centralizer
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184 : G2Centr184) [CharP K 2] (hK4 : 4 ≤ Nat.card K) (hc : Sec3 A R T g)
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hT : ActsIn ψ T (rootSubgroup .G2 K g2c)) {x : G}
    (hx : x ∈ A ⊓ centralizer (g2Q ψ T : Set G)) {y : ↥(adjointGroup .G2 K)}
    (hy : ψ ⟨x, le_normalizer (mem_inf.1 hx).1⟩ = MulAut.conj y) :
    (y : ModGL .G2 K) ∈ g2Centralizer K (g2TorusR K : Set (ModGL .G2 K)) := by
  have hZ := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  refine mem_inf.2 ⟨y.2, mem_centralizer_iff.2 fun h hh => ?_⟩
  have hhC : h ∈ adjointGroup .G2 K := (g2TorusR_le_g2LongCent hh).1
  obtain ⟨w, hw, hwψ⟩ := exists_mem_g2Q h4 h32 h184 hK4 hc hψ hT (y := ⟨h, hhC⟩) hh
  have hwx : w * x = x * w := mem_centralizer_iff.1 (mem_inf.1 hx).2 w hw
  have hwN := le_normalizer (g2Q_le hw)
  have hxN := le_normalizer (mem_inf.1 hx).1
  have h1 := congrArg ψ (Subtype.ext hwx :
    (⟨w * x, mul_mem hwN hxN⟩ : normalizer (A : Set G)) = ⟨x * w, mul_mem hxN hwN⟩)
  rw [psi_mul hwN hxN, psi_mul hxN hwN, hwψ, hy, ← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (RankTwoHypIIY.conj_injective_of_center_eq_bot hZ h1)

end G2Q

section G2Levi

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)} {L : Subgroup (ModGL .G2 K)}

omit [Finite K] [CharP K 2] in
theorem exists_levi_mul
    (hLH : L ≤ centralizer (g2TorusR K : Set (ModGL .G2 K)))
    (hCdec : ∀ x ∈ g2Centralizer K (g2TorusR K : Set (ModGL .G2 K)), ∃ h ∈ g2TorusR K,
      h⁻¹ * x ∈ L) {x : ModGL .G2 K} (hx : x ∈ g2Centralizer K (g2TorusR K : Set (ModGL .G2 K))) :
    ∃ h ∈ g2TorusR K, ∃ l ∈ L, x = l * h ∧ h * l = l * h := by
  obtain ⟨h, hh, hl⟩ := hCdec x hx
  have hcomm : h * (h⁻¹ * x) = h⁻¹ * x * h := mem_centralizer_iff.1 (hLH hl) h hh
  exact ⟨h, hh, h⁻¹ * x, hl, by rw [← hcomm, mul_inv_cancel_left], hcomm⟩

omit [Finite K] [CharP K 2] in
theorem mem_normalizer_levi
    (hLH : L ≤ centralizer (g2TorusR K : Set (ModGL .G2 K)))
    (hCdec : ∀ x ∈ g2Centralizer K (g2TorusR K : Set (ModGL .G2 K)), ∃ h ∈ g2TorusR K,
      h⁻¹ * x ∈ L) {x : ModGL .G2 K} (hx : x ∈ g2Centralizer K (g2TorusR K : Set (ModGL .G2 K))) :
    x ∈ normalizer (L : Set (ModGL .G2 K)) := by
  obtain ⟨h, hh, l, hl, rfl, -⟩ := exists_levi_mul hLH hCdec hx
  refine mul_mem (le_normalizer hl) (centralizer_le_normalizer _ (mem_centralizer_iff.2 fun z hz =>
    (mem_centralizer_iff.1 (hLH hz) h hh).symm))

theorem g2_layerCentralizer_eq
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184 : G2Centr184) (hK4 : 4 ≤ Nat.card K) (hc : Sec3 A R T g)
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hT : ActsIn ψ T (rootSubgroup .G2 K g2c)) (hLC : L ≤ adjointGroup .G2 K) (hLperf : ⁅L, L⁆ = L)
    (hLH : L ≤ centralizer (g2TorusR K : Set (ModGL .G2 K)))
    (hCdec : ∀ x ∈ g2Centralizer K (g2TorusR K : Set (ModGL .G2 K)), ∃ h ∈ g2TorusR K,
      h⁻¹ * x ∈ L) (hLq : CFSG.Open.IsQuasisimple ↥L) :
    layerCentralizer A (g2Q ψ T) = leviLift ψ (g2Inn K L) := by
  refine layerCentralizer_eq_leviLift hψ g2Q_le ?_ ?_ ?_ ?_
  · intro w hw s hs
    obtain ⟨y, hy, hyw⟩ := mem_g2Inn.1 (psi_mem_of_mem_g2Q hw)
    obtain ⟨l, hl, rfl⟩ := mem_g2Inn.1 hs
    rw [← hyw, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.1 (hLH hl) _ hy)
  · intro x hx
    obtain ⟨y, hy⟩ := hψ.map_mem x (mem_inf.1 hx).1
    rw [← hy]
    exact conj_mem_normalizer_g2Inn (mem_normalizer_levi hLH hCdec
      (coe_mem_g2Centralizer h4 h32 h184 hK4 hc hψ hT hx hy.symm))
  · intro x hx z hz
    obtain ⟨y₁, hy₁⟩ := hψ.map_mem x (mem_inf.1 hx).1
    obtain ⟨y₂, hy₂⟩ := hψ.map_mem z (mem_inf.1 hz).1
    rw [psi_commutatorElement (mem_inf.1 hx).1 (mem_inf.1 hz).1, ← hy₁, ← hy₂,
      ← map_commutatorElement]
    refine conj_mem_g2Inn ?_
    obtain ⟨h₁, hh₁, l₁, hl₁, he₁, -⟩ :=
      exists_levi_mul hLH hCdec (coe_mem_g2Centralizer h4 h32 h184 hK4 hc hψ hT hx hy₁.symm)
    obtain ⟨h₂, hh₂, l₂, hl₂, he₂, -⟩ :=
      exists_levi_mul hLH hCdec (coe_mem_g2Centralizer h4 h32 h184 hK4 hc hψ hT hz hy₂.symm)
    show ⁅(y₁ : ModGL .G2 K), (y₂ : ModGL .G2 K)⁆ ∈ L
    rw [he₁, he₂, RankTwoL3Even.commutatorElement_mul_mul_of_commute
      (mem_centralizer_iff.1 (hLH hl₂) h₁ hh₁) (mem_centralizer_iff.1 (hLH hl₁) h₂ hh₂)
      (g2TorusR_comm hh₁ hh₂)]
    exact RankTwoL3Even.commutatorElement_mem' hl₁ hl₂
  · exact isQuasisimple_leviLift_of_open hψ (g2Inn_le_range L) (commutator_g2Inn hLC hLperf)
      (isQuasisimple_of_equiv (g2InnEquiv hLC) hLq)

omit [Finite K] [CharP K 2] in
theorem open_isQuasisimple_of_psl {n m : ℕ} (hLperf : ⁅L, L⁆ = L)
    (hLt : StatedClassicalModel (RankTwoStandard.rankTwoQuot L) .PSL n 2 m) :
    CFSG.Open.IsQuasisimple ↥L := by
  have : Group.IsPerfect ↥L := (Subgroup.isPerfect_iff).2 hLperf
  exact ⟨Group.IsPerfect.commutator_eq_top, isSimpleGroup_of_psl hLt⟩

omit [CharP K 2] in
theorem odd_card_center_leviLift_g2
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hZA : Odd (Nat.card (center A))) (hLC : L ≤ adjointGroup .G2 K) (hLperf : ⁅L, L⁆ = L)
    (hLZ : Odd (Nat.card (center ↥L))) :
    Odd (Nat.card (center ↥(leviLift ψ (g2Inn K L)))) := by
  have hZ := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZ
  have hZA' : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hS := g2Inn_le_range (K := K) L
  have hP := commutator_g2Inn hLC hLperf
  refine AS76b.Lemma22.odd_card_of_forall_orderOf_ne_two fun z hz h2 => ?_
  have hz2 : z ^ 2 = 1 := by rw [← h2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  obtain ⟨y, hyL, hy⟩ := mem_g2Inn.1 (psi_mem_of_mem_leviLift z.2)
  have hyZ : (⟨y, hyL⟩ : ↥L) ∈ center ↥L := by
    rw [mem_center_iff]
    intro l
    apply Subtype.ext
    have hlC : (l : ModGL .G2 K) ∈ adjointGroup .G2 K := hLC l.2
    obtain ⟨l', hl', hl'ψ⟩ := exists_mem_leviLift hψ hS hP
      (conj_mem_g2Inn (y := ⟨l, hlC⟩) l.2)
    have hc := mem_center_iff.1 hz ⟨l', hl'⟩
    have h := congrArg (fun x : ↥(leviLift ψ (g2Inn K L)) =>
      ψ ⟨x, le_normalizer (leviLift_le x.2)⟩) hc
    simp only [Subgroup.coe_mul] at h
    rw [psi_mul (le_normalizer (leviLift_le hl')) (le_normalizer (leviLift_le z.2)),
      psi_mul (le_normalizer (leviLift_le z.2)) (le_normalizer (leviLift_le hl')), hl'ψ, ← hy,
      ← map_mul, ← map_mul] at h
    have h' := congrArg Subtype.val (hinj h)
    exact h'
  have hyy : y ^ 2 = 1 := by
    have h := congrArg (fun x => x ^ 2) hy
    rw [← map_pow, ← psi_pow (le_normalizer (leviLift_le z.2))] at h
    have hz2' : (⟨(z : G) ^ 2, pow_mem (le_normalizer (leviLift_le z.2)) 2⟩ :
        normalizer (A : Set G)) = 1 := Subtype.ext (by
      have := congrArg Subtype.val hz2
      simpa using this)
    rw [hz2', map_one, ← map_one (MulAut.conj : ↥(adjointGroup .G2 K) →* _)] at h
    exact hinj h
  have hy2 : (⟨y, hyL⟩ : ↥L) ^ 2 ^ 1 = 1 := by
    apply Subtype.ext
    have h := congrArg Subtype.val hyy
    simpa using h
  have hy1 := RankTwoL3Even.eq_one_of_odd_of_pow_two (RankTwoL3Even.odd_orderOf_of_mem hLZ hyZ) hy2
  have hψz : ψ ⟨z, le_normalizer (leviLift_le z.2)⟩ = 1 := by
    rw [← hy]
    have h1 := congrArg Subtype.val hy1
    have : y = 1 := Subtype.ext h1
    rw [this, map_one]
  have hzK := (hψ.eq_one_iff _).1 hψz
  have hz' := RankTwoL3Even.eq_one_of_odd_of_pow_two
    (RankTwoL3Even.odd_orderOf_of_mem hZA' (mem_inf.2 ⟨leviLift_le z.2, hzK⟩)) (k := 1)
    (by rw [pow_one]; exact congrArg Subtype.val hz2)
  exact hz1 (Subtype.ext hz')

omit [Finite G] [CharP K 2] in
theorem levi_type_g2
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hLC : L ≤ adjointGroup .G2 K) (hLperf : ⁅L, L⁆ = L) {t : Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ}
    (hLt : StatedClassicalModel (RankTwoStandard.rankTwoQuot L) t n p f) :
    StatedClassicalModel (RankTwoStandard.rankTwoQuot (leviLift ψ (g2Inn K L))) t n p f := by
  have hS := g2Inn_le_range (K := K) L
  have hP := commutator_g2Inn hLC hLperf
  exact SectionRank.statedClassicalModel_of_mulEquiv
    ((centralQuotEquivOfSurjective ((Subgroup.isPerfect_iff).2 (commutator_leviLift hψ hS hP))
      _ (leviLiftPsi_surjective hψ hS hP) (ker_leviLiftPsi_le_center hψ)).trans
      (quotCenterCongr (g2InnEquiv hLC).symm)) hLt

omit [Finite K] [CharP K 2] in
theorem le_sup_leviLift_g2
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g)
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hT : ActsIn ψ T (rootSubgroup .G2 K g2c)) (hZA : Odd (Nat.card (center A)))
    (hLC : L ≤ adjointGroup .G2 K) (hLperf : ⁅L, L⁆ = L) (hXcL : rootSubgroup .G2 K g2c ≤ L) :
    T ≤ R ⊔ leviLift ψ (g2Inn K L) := by
  have hZA' : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  intro t ht
  have htN := hc.le_normalizer ht
  obtain ⟨p, hpA, hpR⟩ := hc.exists_aPart h32 h4 h34 ht
  obtain ⟨x, hx⟩ := exists_psi_eq_conj hc h32 h4 h34 hψ ht htN
  have hψp : ψ ⟨p, le_normalizer hpA⟩ = MulAut.conj x := by
    have h1 : ψ ⟨t⁻¹ * p, mul_mem (inv_mem htN) (le_normalizer hpA)⟩ = 1 :=
      (hψ.eq_one_iff _).2 (hc.sylowR.le hpR)
    rw [psi_mul (inv_mem htN) (le_normalizer hpA), psi_inv htN, inv_mul_eq_one] at h1
    rw [← h1, hx]
  have hp2 : p ^ 2 ^ 1 = 1 := by
    have hcomm : Commute t (t⁻¹ * p) := hc.commute_T_R ht hpR
    calc p ^ 2 ^ 1 = (t * (t⁻¹ * p)) ^ 2 := by rw [mul_inv_cancel_left, pow_one]
      _ = t ^ 2 * (t⁻¹ * p) ^ 2 := hcomm.mul_pow 2
      _ = 1 := by rw [(hc.elemT h32).2 t ht, (hc.elemR h32).2 _ hpR, one_mul]
  have hpL : p ∈ leviLift ψ (g2Inn K L) := by
    refine mem_leviLift_of_pow hψ (g2Inn_le_range L) (commutator_g2Inn hLC hLperf) hZA'
      (mem_liftIn.2 ⟨hpA, ?_⟩) hp2
    rw [hψp]
    exact conj_mem_g2Inn (hXcL (hT t ht htN x hx))
  have h1 : t = p * (t⁻¹ * p)⁻¹ := by group
  rw [h1]
  exact mul_mem (mem_sup_right hpL) (mem_sup_left (inv_mem hpR))

end G2Levi

end CFSG.ComponentClassification.RankTwoExceptional
