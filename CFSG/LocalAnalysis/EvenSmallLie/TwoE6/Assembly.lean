module

public import CFSG.LocalAnalysis.EvenSmallLie.Children
public import CFSG.LocalAnalysis.EvenSmallLie.Setup
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.IndexTwo
public import CFSG.Milestones.CL_LIT_Stroth_Leon_Sims_Baby_Monster_recognition
public import CFSG.Monster.B.GSide.RecognitionExists
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoCyclicKernel
public import CFSG.Monster.Existence.TwoPoint.StdE6Model

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Open CFSG.Blueprint CFSG.LieType.Chevalley.C2E6Std
  CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.GSide

theorem lieModel_twistedE6_two_iff
    (X : Type) [Group X] :
    LieModel X .twistedE6 0 2 1 ↔ Nonempty (X ≃* ↥stdGroup) := by
  constructor
  · rintro (⟨hc, -⟩ | ⟨-, -, hX⟩ | ⟨-, hr, -⟩ | ⟨-, hs, -⟩)
    · exact absurd hc (by decide)
    · obtain ⟨L, _, _, σ, hL, hσ, ⟨e⟩⟩ :=
        CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_E6 hX
      obtain ⟨e'⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_stdGroup_of_card_eq_four
        (by rw [hL]; norm_num) σ.toRingHom fun c => by simpa using hσ c
      exact ⟨e.trans e'⟩
    · exact absurd hr (by decide)
    · exact absurd hs (by decide)
  · rintro ⟨e⟩
    obtain ⟨e₀⟩ := CFSG.Monster.Existence.nonempty_mulEquiv_derivedCentralQuotient
      CFSG.Monster.Existence.commutator_stdFixedGroup CFSG.Monster.Existence.center_stdGroup_eq_bot
    exact CFSG.Monster.Existence.lieModel_twistedE6_of_mulEquiv CFSG.LieType.Chevalley.C2E6Overlap.K
      CFSG.Monster.B.E6.card_K CFSG.LieType.Chevalley.C2E6Overlap.barHom
      CFSG.Monster.B.E6.barHom_eq_pow ⟨e.trans e₀⟩

@[expose] def DoubleCoverUnique
    : Prop :=
  ∀ (A : Type) [Group A] [Finite A], CFSG.Open.IsQuasisimple A → Nat.card (center A) = 2 →
    Nonempty (A ⧸ center A ≃* ↥stdGroup) → Nonempty (A ≃* ↥(commutator ↥Eam))

@[expose] def CoverOuterLeTwo :
    Prop :=
  (MulAut.conj : ↥(commutator ↥Eam) →* MulAut ↥(commutator ↥Eam)).range.index ≤ 2

@[expose] def Stroth21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    Nat.card (center L) = 2 → LieModel (L ⧸ center L) .twistedE6 0 2 1 →
    centralizer (L : Set G) = (center L).map L.subtype

@[expose] def Stroth23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    Nat.card (center L) = 2 → LieModel (L ⧸ center L) .twistedE6 0 2 1 →
    centralizer (L : Set G) = (center L).map L.subtype →
    ∃ s ∈ normalizer (L : Set G), s ∉ L ∧ s * s = 1

theorem conj_eq_of_mem_normalizer {G : Type*} [Group G] {L : Subgroup G} {z : center L}
    (hzu : ∀ y : center L, y ≠ 1 → y = z) {h : G} (hh : h ∈ normalizer (L : Set G)) :
    h * ((z : L) : G) * h⁻¹ = ((z : L) : G) := by
  have hwL : h * ((z : L) : G) * h⁻¹ ∈ L := (mem_normalizer_iff.1 hh _).1 (z : L).2
  have hwZ : (⟨_, hwL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro l
    apply Subtype.ext
    have hl : h⁻¹ * (l : G) * h ∈ L := by
      have := (mem_normalizer_iff.1 (inv_mem hh) l).1 l.2
      rwa [inv_inv] at this
    have hc := congrArg Subtype.val ((mem_center_iff.1 z.2) ⟨_, hl⟩)
    rw [coe_mul, coe_mul] at hc
    show (l : G) * (h * ((z : L) : G) * h⁻¹) = h * ((z : L) : G) * h⁻¹ * l
    calc (l : G) * (h * ((z : L) : G) * h⁻¹) = h * ((h⁻¹ * l * h) * ((z : L) : G)) * h⁻¹ := by
          group
      _ = h * (((z : L) : G) * (h⁻¹ * l * h)) * h⁻¹ := by rw [hc]
      _ = h * ((z : L) : G) * h⁻¹ * l := by group
  by_cases hz : z = 1
  · rw [hz, OneMemClass.coe_one, OneMemClass.coe_one, mul_one, mul_inv_cancel]
  · have h1 : (⟨⟨_, hwL⟩, hwZ⟩ : center L) = z := by
      refine hzu _ fun h1 => hz ?_
      have h2 : h * ((z : L) : G) * h⁻¹ = 1 := congrArg (fun x : center L => ((x : L) : G)) h1
      have h3 : ((z : L) : G) = 1 := by
        calc ((z : L) : G) = h⁻¹ * (h * ((z : L) : G) * h⁻¹) * h := by group
          _ = 1 := by rw [h2]; group
      exact Subtype.ext (Subtype.ext h3)
    exact congrArg (fun x : center L => ((x : L) : G)) h1

theorem centralizer_eq_normalizer {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    (hL : standardComponentIsStandard L) {z : center L} (hzu : ∀ y : center L, y ≠ 1 → y = z)
    (hz : orderOf ((z : L) : G) = 2) :
    centralizer {((z : L) : G)} = normalizer (L : Set G) :=
  le_antisymm (centralizer_le_normalizer_of_standard hL (mem_centralizer_of_mem_center z.2) hz)
    fun h hh => mem_centralizer_singleton_iff.2 (by
      have := conj_eq_of_mem_normalizer hzu hh
      calc h * ((z : L) : G) = h * ((z : L) : G) * h⁻¹ * h := by group
        _ = ((z : L) : G) * h := by rw [this])

theorem nonempty_centralizer_labelB_of_mulEquiv
    {G : Type*} [Group G] {d : G}
    (e : centralizer {d} ≃* Eam) :
    Nonempty (centralizer {d} ≃* centralizer ({labelB} : Set NativeSporadic.B)) :=
  ⟨e.trans (vStabEam.symm.trans (centralizerVStabEquiv orderOf_labelB rank_labelB).symm)⟩

theorem nonempty_normalizer_mulEquiv_Eam
    (hO : CoverOuterLeTwo) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (ι : L ≃* ↥(commutator ↥Eam)) (hC : centralizer (L : Set G) ≤ L) {s : G}
    (hsN : s ∈ normalizer (L : Set G)) (hsL : s ∉ L) (hs2 : s * s = 1) :
    Nonempty (normalizer (L : Set G) ≃* Eam) := by
  set N := normalizer (L : Set G)
  have hC' : centralizer ((L.subgroupOf N : Subgroup N) : Set N) ≤ L.subgroupOf N := by
    intro x hx
    rw [mem_subgroupOf]
    refine hC (mem_centralizer_iff.2 fun l hl => ?_)
    exact congrArg Subtype.val ((mem_centralizer_iff.1 hx) ⟨l, le_normalizer hl⟩
      (by rw [SetLike.mem_coe, mem_subgroupOf]; exact hl))
  set ι' : L.subgroupOf N ≃* ↥(commutator ↥Eam) := (subgroupOfEquivOfLe le_normalizer).trans ι
  have hle : (L.subgroupOf N).index ≤ 2 := index_le_two_of_range_conj_index_le_two hO ι' hC'
  have hsL' : (⟨s, hsN⟩ : N) ∉ L.subgroupOf N := fun h => hsL (mem_subgroupOf.1 h)
  have hne1 : (L.subgroupOf N).index ≠ 1 := fun h => hsL' ((index_eq_one.1 h) ▸ mem_top _)
  have hne0 : (L.subgroupOf N).index ≠ 0 := FiniteIndex.index_ne_zero
  obtain ⟨e, -⟩ := nonempty_mulEquiv_Eam_of_outer_involution hO (L.subgroupOf N) (by omega) ι' hC'
    hsL' (Subtype.ext hs2)
  exact ⟨e⟩

theorem child2E6_of_inputs
    (hU : DoubleCoverUnique) (hO : CoverOuterLeTwo) (h21 : Stroth21)
    (h23 : Stroth23) : Child2E6 := by
  intro G _ _ L hset hc hB
  have : IsSimpleGroup G := hset.simple
  have hZ := h21 G L hset hc hB
  obtain ⟨s, hsN, hsL, hs2⟩ := h23 G L hset hc hB hZ
  obtain ⟨z, hz1, hzu⟩ := (Nat.card_eq_two_iff' (1 : center L)).1 hc
  have hzo : orderOf ((z : L) : G) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [← hc]; exact pow_card_eq_one') hz1
  obtain ⟨ι⟩ := hU L hset.standard.1 hc ((lieModel_twistedE6_two_iff _).1 hB)
  have hC : centralizer (L : Set G) ≤ L := by
    rw [hZ]
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  obtain ⟨e⟩ := nonempty_normalizer_mulEquiv_Eam hO ι hC hsN hsL hs2
  obtain ⟨φ⟩ := nonempty_centralizer_labelB_of_mulEquiv
    ((MulEquiv.subgroupCongr (centralizer_eq_normalizer hset.standard hzu hzo)).trans e)
  exact CFSG.Milestones.cl_lit_stroth_leon_sims_baby_monster_recognition_models labelB
    orderOf_labelB rank_labelB G _ hzo ⟨φ⟩

end CFSG.EvenSmallLie.TwoE6
