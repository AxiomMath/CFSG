module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CoverCheck
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUniqueBound
public import CFSG.Certificates.Kernel.Misc.Coset.PGChain

public section

namespace CFSG.EvenSmallLie.OmegaEight.Cover

open Subgroup CFSG.CosetTable CFSG.LieType.Multipliers CFSG.RankThree.PerfectCover
  CFSG.Sporadic.Schreier CFSG.Monster.B.Co2

theorem cycPerm_genCycles
    (j : Fin 8) : cycPerm 360 (genCycles j) = gen j := by
  have h := gen_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact Rep.unique (fun x => h j x) (rep_gen (by omega))

theorem genList_mem
    : ∀ g ∈ genList, g ∈ omegaT := by
  intro g hg
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
  rw [cycPerm_genCycles]
  exact gen_mem_omegaT j.2

theorem gens_mem
    (i : Fin 4) : gens i ∈ omegaT := by
  rw [gens, tab_eq]
  exact evalCodes_mem _ genList_mem _

@[expose] def gensX
    (i : Fin 4) : omegaT := ⟨gens i, gens_mem i⟩

theorem model_facts
    : (∀ r ∈ rels, word r = 1) ∧ (∀ i, word (commWords (pairs i)) = gens i) ∧
    (∀ j, word (genWords j) = cycPerm 360 (genCycles j)) ∧ word uWord * word uWord = 1 ∧
    word tuWord = rhoT * word uWord * rhoT⁻¹ := by
  have h := model_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, fun i => h.1.1.1.2 i (List.mem_finRange i),
    fun j => h.1.1.2 j (List.mem_finRange j), h.1.2, h.2⟩

theorem lift_gens_mk (w : List (Fin 4 × Bool)) :
    FreeGroup.lift gens (FreeGroup.mk w) = word w :=
  FreeGroup.lift_mk

theorem coe_lift_gensX
    (x : FreeGroup (Fin 4)) :
    ((FreeGroup.lift gensX x : omegaT) : Equiv.Perm (Fin 360)) = FreeGroup.lift gens x := by
  have h : omegaT.subtype.comp (FreeGroup.lift gensX) = FreeGroup.lift gens :=
    FreeGroup.ext_hom _ _ fun i => by simp [gensX]
  exact DFunLike.congr_fun h x

theorem coe_lift_gensX_mk
    (w : List (Fin 4 × Bool)) :
    ((FreeGroup.lift gensX (FreeGroup.mk w) : omegaT) : Equiv.Perm (Fin 360)) = word w :=
  (coe_lift_gensX _).trans (lift_gens_mk w)

theorem closure_gensX
    : closure (Set.range gensX) = ⊤ := by
  have hmap : (closure (Set.range gensX)).map omegaT.subtype = closure (Set.range gens) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hle : omegaT ≤ (closure (Set.range gensX)).map omegaT.subtype := by
    rw [hmap, omegaT_eq, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have hw : gen j = word (genWords ⟨j, hj⟩) := by
      rw [model_facts.2.2.1, cycPerm_genCycles]
    rw [SetLike.mem_coe, hw, ← lift_gens_mk, ← FreeGroup.range_lift_eq_closure]
    exact ⟨_, rfl⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [show y = x from Subtype.ext hyx] at hy

theorem card_PG_rels
    : Finite (PG 4 rels) ∧ Nat.card (PG 4 rels) ≤ 174182400 := by
  obtain ⟨fY, cY⟩ := SympSix.card_PG_rels
  obtain ⟨f, c⟩ := CFSG.KC.MiscCoset.card_le_of_index_restrict rels (subsetOf 4 [0, 1, 2])
    pres_check ⟨fY, cY⟩
  exact ⟨f, c.trans (by norm_num)⟩

theorem isPresentation_omegaT :
    IsPresentation gensX (wordSet rels) := by
  obtain ⟨hfin, hcard⟩ := card_PG_rels
  refine IsPresentation.of_card_le ?_ closure_gensX ?_
  · intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact Subtype.ext ((coe_lift_gensX_mk w).trans (model_facts.1 w hw))
  · rw [card_omegaT]
    exact hcard

theorem card_cover_le
    : Finite (PG 4 coverWs) ∧ Nat.card (PG 4 coverWs) ≤ 4 * 174182400 := by
  obtain ⟨f₁, c₁⟩ := SympSix.card_cover_le
  obtain ⟨f, c⟩ := CFSG.KC.MiscCoset.card_le_of_index_restrict coverWs (subsetOf 4 [0, 1, 2])
    cover_check ⟨f₁, c₁⟩
  exact ⟨f, c.trans (by norm_num)⟩

theorem lift_commWords (i : Fin 4) :
    FreeGroup.lift gensX (FreeGroup.mk (commWords (pairs i))) = gensX i :=
  Subtype.ext ((coe_lift_gensX_mk _).trans (model_facts.2.1 i))

abbrev Cov : Type := PresentedCover (wordSet rels) fun i => FreeGroup.mk (commWords (pairs i))

theorem coverRelators_eq :
    coverRelators (wordSet rels) (fun i => FreeGroup.mk (commWords (pairs i))) =
      wordSet coverWs :=
  coverRelators_wordSet rels _

theorem finite_card_cov
    : Finite Cov ∧ Nat.card Cov ≤ 4 * 174182400 := by
  obtain ⟨hfin, hle⟩ := card_cover_le
  rw [Cov, PresentedCover, coverRelators_eq]
  exact ⟨hfin, hle⟩

theorem isPerfect_omegaT :
    Group.IsPerfect omegaT :=
  isPerfect_of_isPresentation isPresentation_omegaT (fun _ => mk_commWords_mem_commutator _)
    lift_commWords

noncomputable def coverEquiv :
    Cov ≃* HopfCover omegaT :=
  presentedCoverEquiv isPresentation_omegaT (fun _ => mk_commWords_mem_commutator _)
    lift_commWords

theorem hopfCoverMap_coverEquiv
    (x : Cov) :
    hopfCoverMap omegaT (coverEquiv x) = coverMap isPresentation_omegaT lift_commWords x :=
  hopfCoverMap_presentedCoverEquiv _ _ _ x

theorem card_hopfCover_le :
    Finite (HopfCover omegaT) ∧ Nat.card (HopfCover omegaT) ≤ 4 * Nat.card omegaT := by
  obtain ⟨hfin, hle⟩ := finite_card_cov
  rw [card_omegaT]
  exact ⟨Finite.of_equiv _ coverEquiv.toEquiv,
    (Nat.card_congr coverEquiv.toEquiv).symm.le.trans hle⟩

theorem card_hopfMultiplier_le :
    Finite (hopfMultiplier omegaT) ∧ Nat.card (hopfMultiplier omegaT) ≤ 4 := by
  have := isPerfect_omegaT
  obtain ⟨hfin, hle⟩ := card_hopfCover_le
  refine ⟨inferInstance, ?_⟩
  have h1 := (hopfMultiplier omegaT).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    hopfCoverMap_surjective).toEquiv, card_omegaT] at h1
  rw [card_omegaT] at hle
  omega

theorem lift_rhoGens_coverRelators :
    ∀ r ∈ coverRelators (wordSet rels) (fun i => FreeGroup.mk (commWords (pairs i))),
      FreeGroup.lift rhoGens r = 1 := by
  have h := rho_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  intro r hr
  rw [coverRelators_eq] at hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [FreeGroup.lift_mk]
  exact h.1.1 w hw

noncomputable def rhoHom : Cov →* Equiv.Perm (Fin 240) :=
  PresentedGroup.toGroup lift_rhoGens_coverRelators

theorem rhoHom_mk (w : List (Fin 4 × Bool)) :
    rhoHom (PresentedGroup.mk _ (FreeGroup.mk w)) = rhoWord w :=
  FreeGroup.lift_mk

end CFSG.EvenSmallLie.OmegaEight.Cover
