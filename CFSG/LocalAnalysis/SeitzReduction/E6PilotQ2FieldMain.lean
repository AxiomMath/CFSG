module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldFamily
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowFieldCover

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (F4Work QuadraticFrobenius centralizerPerfectCore)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.SeitzReduction.LinearPilot (CatSLmSporadicAt)

local instance e6PilotQ2FieldMainNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Sections

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

omit [Finite G] in
theorem map_conj_map_map_symm_E6 (e : L ≃* adjointGroup .E6 (fixSubfield σ))
    (A : Subgroup (adjointGroup .E6 (fixSubfield σ))) (n : adjointGroup .E6 (fixSubfield σ)) :
    ((A.map e.symm.toMonoidHom).map L.subtype).map (MulAut.conj ((e.symm n : L) : G)).toMonoidHom =
      ((A.map (MulAut.conj n).toMonoidHom).map e.symm.toMonoidHom).map L.subtype := by
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

@[expose] noncomputable def TwoCover.Section.congr {N : E6Neighbour} {E E' : Subgroup G}
    {h : TwoCover σ e N E} {H : Subgroup (adjointGroup .E6 K)} (t : h.Section H) (hE : E = E') :
    (h.congr hE).Section H where
  s := t.s
  mem y := hE ▸ t.mem y
  lift y := t.lift y

theorem coe_neighbourLeviEntrywiseEquiv_symm (ρ : K ≃+* K) (N : E6Neighbour) (z : N.levi K) :
    ((((neighbourLeviEntrywiseEquiv ρ N).symm z : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (ρ.symm : K →+* K) ((z : adjointGroup .E6 K) : ModGL .E6 K) := by
  obtain ⟨w, rfl⟩ := (neighbourLeviEntrywiseEquiv ρ N).surjective z
  rw [MulEquiv.symm_apply_apply, coe_neighbourLeviEntrywiseEquiv, F4Pilot.baseChangeGL_baseChangeGL,
    show (ρ.symm : K →+* K).comp (ρ : K →+* K) = RingHom.id K from
      RingHom.ext fun c => ρ.symm_apply_apply c, baseChangeGL_id]

@[expose] noncomputable def TwoCover.Section.twist {N : E6Neighbour} {E : Subgroup G}
    {h : TwoCover σ e N E} {J : Finset (Fin (Tag.rank .E6))}
    (t : h.Section (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J)) (ρ : K ≃+* K)
    (hρ : ∀ c : fixSubfield σ, ρ c = c) :
    (h.twist ρ hρ).Section (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J) where
  s := t.s.comp (leviEntrywise (ρ : K →+* K) J)
  mem y := t.mem _
  lift y := by
    apply Subtype.ext
    change ((((neighbourLeviEntrywiseEquiv ρ N).symm
      (h.p ⟨t.s (leviEntrywise (ρ : K →+* K) J y), t.mem _⟩) : N.levi K) :
        adjointGroup .E6 K) : ModGL .E6 K) = _
    rw [coe_neighbourLeviEntrywiseEquiv_symm, t.lift, coe_leviEntrywise,
      F4Pilot.baseChangeGL_baseChangeGL,
      show (ρ.symm : K →+* K).comp (ρ : K →+* K) = RingHom.id K from
        RingHom.ext fun c => ρ.symm_apply_apply c, baseChangeGL_id]

theorem exists_section_levi_congr {E₀ : Subgroup G} (P₀ : TwoCover σ e .high E₀)
    {EN : E6Neighbour → Subgroup G}
    (hE : ∀ N, E₀.map (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom = EN N)
    (N : E6Neighbour) {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2) :
    Nonempty (((P₀.toNeighbour N).congr (hE N)).Section
      (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J)) := by
  obtain ⟨s, hs⟩ := P₀.exists_section_levi N hJ hJ2
  exact ⟨(TwoCover.Section.ofHom _ s hs).congr (hE N)⟩

theorem exists_section_tripleRootSL2_congr {E₀ : Subgroup G} (P₀ : TwoCover σ e .high E₀)
    {EN : E6Neighbour → Subgroup G}
    (hE : ∀ N, E₀.map (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom = EN N)
    (N : E6Neighbour) :
    ∃ s : tripleRootSL2 K →* EN N,
      ∀ y, ((((P₀.toNeighbour N).congr (hE N)).p (s y) : N.levi K) : adjointGroup .E6 K) = y := by
  obtain ⟨s, hs⟩ := P₀.exists_section_tripleRootSL2 N
  refine ⟨(MulEquiv.subgroupCongr (hE N)).toMonoidHom.comp s, fun y => ?_⟩
  rw [TwoCover.congr_p_apply]
  exact hs y

omit [Finite K] [CharP K 2] [Finite G] in
theorem coe_q2LeviRootEltG {F : Type} [Field F] (N : E6Neighbour) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : γ ∈ orthRoots N.root) (a : F) :
    ((q2LeviRootElt N hγ a : N.levi F) : adjointGroup .E6 F) =
      ⟨pinnedX .E6 F γ a, pinnedX_mem_adjointGroup γ a⟩ :=
  rfl

theorem le_of_forall_isLift_mem {E : Subgroup G} (h : TwoCover σ e .high E) (hE : ⁅E, E⁆ = E)
    {G₀ : Subgroup G}
    (hgen : ∀ l (hl : l ∈ E6Neighbour.high.nodes) (a : K),
      (∃ g ∈ G₀, h.IsLift (q2LeviRootElt .high (single_mem_orthRoots_E6 hl) a) g) ∧
      (∃ g ∈ G₀, h.IsLift (q2LeviRootElt .high
        (neg_mem_orthRoots_E6 (single_mem_orthRoots_E6 hl)) a) g)) :
    E ≤ G₀ := by
  have hTop : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤ :=
    (Subgroup.isPerfect_iff.2 hE).commutator_eq_top
  have hmem : ∀ (u : E6Neighbour.high.levi K) (g : G), g ∈ G₀ → h.IsLift u g →
      (u : adjointGroup .E6 K) ∈ ((G₀.subgroupOf E).map h.p).map
        (E6Neighbour.high.levi K).subtype := by
    rintro u _ hg ⟨y, rfl, hpy, -⟩
    exact ⟨u, ⟨y, mem_subgroupOf.2 hg, hpy⟩, rfl⟩
  have hD : a5Levi K ≤ ((G₀.subgroupOf E).map h.p).map (E6Neighbour.high.levi K).subtype := by
    refine a5Levi_le_of_forall fun l hl c => ⟨?_, ?_⟩
    · obtain ⟨g, hg, hl'⟩ := (hgen l hl c).1
      have h1 := hmem _ g hg hl'
      rw [coe_q2LeviRootEltG] at h1
      exact h1
    · obtain ⟨g, hg, hl'⟩ := (hgen l hl c).2
      have h1 := hmem _ g hg hl'
      rw [coe_q2LeviRootEltG] at h1
      exact h1
  have hall : ∀ g : E, ∃ k ∈ G₀.subgroupOf E, h.p k = h.p g := by
    intro g
    have hpg : ((h.p g : E6Neighbour.high.levi K) : adjointGroup .E6 K) ∈
        ((G₀.subgroupOf E).map h.p).map (E6Neighbour.high.levi K).subtype := by
      refine hD ?_
      rw [← E6Neighbour.levi_high]
      exact (h.p g).2
    obtain ⟨_, ⟨k, hk, rfl⟩, hkg⟩ := hpg
    exact ⟨k, hk, Subtype.ext hkg⟩
  have hHtop := eq_top_of_forall_exists_map_eq_of_perfect hTop h.ker_le_center hall
  intro g hg
  have : (⟨g, hg⟩ : E) ∈ G₀.subgroupOf E := hHtop ▸ mem_top _
  exact mem_subgroupOf.1 this

theorem mem_inter_nodes_E6 (j : Fin (Tag.rank .E6)) :
    (j ∈ E6Neighbour.high.nodes → j ∈ E6Neighbour.six.nodes →
      j ∈ ({0, 2, 3} : Finset (Fin (Tag.rank .E6)))) ∧
    (j ∈ E6Neighbour.high.nodes → j ∈ E6Neighbour.three.nodes →
      j ∈ ({4, 5} : Finset (Fin (Tag.rank .E6)))) ∧
    (j ∈ E6Neighbour.six.nodes → j ∈ E6Neighbour.three.nodes →
      j ∈ ({1} : Finset (Fin (Tag.rank .E6)))) := by
  revert j
  decide

end Sections

section Main

@[expose] def q2CoverTriple {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G]
    {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)} {EN : E6Neighbour → Subgroup G}
    (h₁ : TwoCover σ e .high (EN .high)) (h₂ : TwoCover σ e .six (EN .six))
    (h₃ : TwoCover σ e .three (EN .three)) : ∀ N, TwoCover σ e N (EN N)
  | .high => h₁
  | .six => h₂
  | .three => h₃

theorem e6TwoFieldFamilyInput_holds : E6TwoFieldFamilyInput := by
  intro G _ _ L K _ _ _ σ hq e t hw A hAJ hA X hX htX D hD hk
  have hk2 : Nat.card (fixSubfield σ) = 2 := by rw [hw.card_eq, pow_one]
  have hK4 : Nat.card K = 2 ^ 2 := by rw [hq.card_eq]
  have : CharP (fixSubfield σ) 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  obtain ⟨p, hps, hpker, hpodd, hpfix⟩ :=
    exists_normalized_cover_nonsplit_E6_two hq e hw hAJ hA hX htX hD hk
  set EN : E6Neighbour → Subgroup G := fun N => centralizerPerfectCore (q2NeighbourGE6 e A N)
    with hEN
  let P₀ : TwoCover σ e .high (centralizerPerfectCore X) := ⟨p, hps, hpker.le, hpodd, hpfix⟩
  have hE : ∀ N, (centralizerPerfectCore X).map
      (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom = EN N := by
    intro N
    rw [F4Pilot.map_centralizerPerfectCore, hX, map_conj_map_map_symm_E6]
    rfl
  set PN : ∀ N, TwoCover σ e N (EN N) := fun N => (P₀.toNeighbour N).congr (hE N) with hPN
  choose sT hsT using exists_section_tripleRootSL2_congr P₀ hE
  have hrng : ∀ N, (sT N).range.map (EN N).subtype = tripleCoreG e A := fun N =>
    map_range_section_eq_tripleCoreG hk2 hK4 hAJ hA N rfl (PN N) (sT N) (hsT N)
  obtain ⟨ρhs, hρhs, h1p, h1n⟩ := (PN .high).exists_twistAt_tripleRoot (PN .six) (sT .high)
    (hsT .high) (sT .six) (hsT .six) ((hrng .high).trans (hrng .six).symm)
  obtain ⟨ρht, hρht, h2p, h2n⟩ := (PN .high).exists_twistAt_tripleRoot (PN .three) (sT .high)
    (hsT .high) (sT .three) (hsT .three) ((hrng .high).trans (hrng .three).symm)
  obtain ⟨ρst, -, h3p, h3n⟩ := (PN .six).exists_twistAt_tripleRoot (PN .three) (sT .six)
    (hsT .six) (sT .three) (hsT .three) ((hrng .six).trans (hrng .three).symm)
  obtain ⟨a1, a2, a3⟩ := exists_aligned_twoCover (PN .high) (PN .six) (PN .three) hρhs hρht
    ⟨h1p, h1n⟩ ⟨h2p, h2n⟩ ⟨h3p, h3n⟩
  set Q : ∀ N, TwoCover σ e N (EN N) :=
    q2CoverTriple (PN .high) ((PN .six).twist ρhs hρhs) ((PN .three).twist ρht hρht) with hQ
  have hal : TwoCoversAligned Q := by
    intro N N' j hj hj'
    obtain ⟨hHS, hHT, hST⟩ := mem_inter_nodes_E6 j
    cases N <;> cases N'
    · exact ⟨TwoCover.agree_self _ _, TwoCover.agree_self _ _⟩
    · exact ⟨(a1 j (hHS hj hj')).1.agree, (a1 j (hHS hj hj')).2.agree⟩
    · exact ⟨(a2 j (hHT hj hj')).1.agree, (a2 j (hHT hj hj')).2.agree⟩
    · exact ⟨(a1 j (hHS hj' hj)).1.agree.symm, (a1 j (hHS hj' hj)).2.agree.symm⟩
    · exact ⟨TwoCover.agree_self _ _, TwoCover.agree_self _ _⟩
    · exact ⟨(a3 j (hST hj hj')).1.agree, (a3 j (hST hj hj')).2.agree⟩
    · exact ⟨(a2 j (hHT hj' hj)).1.agree.symm, (a2 j (hHT hj' hj)).2.agree.symm⟩
    · exact ⟨(a3 j (hST hj' hj)).1.agree.symm, (a3 j (hST hj' hj)).2.agree.symm⟩
    · exact ⟨TwoCover.agree_self _ _, TwoCover.agree_self _ _⟩
  have hsecN : ∀ (N : E6Neighbour) (J : Finset (Fin (Tag.rank .E6))), J ⊆ N.nodes →
      J.card ≤ 2 → Nonempty ((Q N).Section (CFSG.LieType.CurtisTits.levi
        (adjDatumE6 K).rootGroup J)) := by
    intro N J hJ hJ2
    obtain ⟨t⟩ := exists_section_levi_congr P₀ hE N hJ hJ2
    cases N
    · exact ⟨t⟩
    · exact ⟨t.twist ρhs hρhs⟩
    · exact ⟨t.twist ρht hρht⟩
  set sec : ∀ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2},
      (Q (amalgamPlacement J.1)).Section
        (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J.1) :=
    fun J => (hsecN _ J.1 (subset_nodes_amalgamPlacement J.2) J.2).some with hsec
  have hφ := isTwoFieldFamilyE6_familyOfSections hal sec
  refine ⟨familyOfSections sec, hφ, le_antisymm ?_ ?_⟩
  ·
    refine iSup_le fun J => ?_
    rintro _ ⟨y, rfl⟩
    exact le_iSup EN (amalgamPlacement J.1) ((sec J).mem y)
  ·
    have hLG := le_twoFamilySupE6 hφ
    have hhigh : EN .high ≤ twoFamilySupE6 (familyOfSections sec) := by
      refine le_of_forall_isLift_mem (Q .high) (F4Pilot.commutator_centralizerPerfectCore _)
        fun l hl a => ⟨?_, ?_⟩
      · set J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2} := ⟨{l}, by simp⟩ with hJdef
        have hlJ : l ∈ J.1 := Finset.mem_singleton_self l
        have hγJ := mem_orthRoots_placement J.2 hlJ (Or.inl rfl)
        obtain ⟨g', hg'⟩ := (Q .high).exists_isLift
          (q2LeviRootElt_mul_self .high (single_mem_orthRoots_E6 hl) a)
        refine ⟨g', ?_, hg'⟩
        have h1 := isLift_familyOfSections sec J hlJ (Or.inl rfl) hγJ a
          ⟨xElement l a, xElement_mem_levi_adjDatumE6 l a⟩ (by
            change (xElement l a : ModGL .E6 K) = _
            rw [pinnedX_single]
            rfl)
        have h2 := (hal (amalgamPlacement J.1) .high l
          (subset_nodes_amalgamPlacement J.2 hlJ) hl).1 hγJ (single_mem_orthRoots_E6 hl) a _ _
          h1 hg'
        rw [← h2]
        exact mem_twoFamilySupE6 (familyOfSections sec) J _
      · set J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2} := ⟨{l}, by simp⟩ with hJdef
        have hlJ : l ∈ J.1 := Finset.mem_singleton_self l
        have hγJ := mem_orthRoots_placement J.2 hlJ (Or.inr rfl)
        obtain ⟨g', hg'⟩ := (Q .high).exists_isLift
          (q2LeviRootElt_mul_self .high (neg_mem_orthRoots_E6 (single_mem_orthRoots_E6 hl)) a)
        refine ⟨g', ?_, hg'⟩
        have h1 := isLift_familyOfSections sec J hlJ (Or.inr rfl) hγJ a
          ⟨yElement l a, yElement_mem_levi_adjDatumE6 l a⟩ (by
            change (yElement l a : ModGL .E6 K) = _
            rw [pinnedX_neg_single]
            rfl)
        have h2 := (hal (amalgamPlacement J.1) .high l
          (subset_nodes_amalgamPlacement J.2 hlJ) hl).2 hγJ
          (neg_mem_orthRoots_E6 (single_mem_orthRoots_E6 hl)) a _ _ h1 hg'
        rw [← h2]
        exact mem_twoFamilySupE6 (familyOfSections sec) J _
    have hXh : centralizerPerfectCore X = EN .high := by
      change centralizerPerfectCore X = centralizerPerfectCore (q2NeighbourGE6 e A .high)
      rw [q2NeighbourGE6_high, hX]
    refine iSup_le fun N => ?_
    rw [← hE N, hXh]
    rintro _ ⟨y, hy, rfl⟩
    have hn : ((e.symm (N.rep (fixSubfield σ)) : L) : G) ∈ twoFamilySupE6 (familyOfSections sec) :=
      hLG (e.symm _).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hn (hhigh hy)) (inv_mem hn)

theorem e6TwoFieldRowCTInput_holds : E6TwoFieldRowCTInput :=
  e6TwoFieldRowCTInput_of_family e6TwoFieldFamilyInput_holds

theorem seitzExclusion_highE6_of_gls3_sporadic (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor : CatSLmSporadicAt 6) : SeitzExclusion (HighExceptional .E6) :=
  seitzExclusion_highE6_of_q2CT hGLS hSpor e6TwoFieldRowCTInput_holds

end Main

end CFSG.SeitzReduction.E6Pilot
