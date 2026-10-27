module

public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalSelfCentralizing
public import CFSG.LieType.Chevalley.OddPinnedComponents
public import CFSG.RankThree.PartOne.S11c.Sec66G2Sub
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Rig
public import CFSG.Timmesfeld.Orders.ExceptionalTorus

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.Sec66T CFSG.Timmesfeld.ExceptionalOrders

theorem two_elements_G2 : ∀ a x : Fin Tag.G2.rank, x ≠ a → ∀ y : Fin Tag.G2.rank,
    y = a ∨ y = x := by decide

section Lattice

variable (K : Type) [Field K]

abbrev inG2 (A : Subgroup (ModGL Tag.G2 K)) : Subgroup ↥(adjointGroup Tag.G2 K) :=
  A.subgroupOf (adjointGroup Tag.G2 K)

abbrev PG (J : Set (Fin Tag.G2.rank)) : Subgroup ↥(adjointGroup Tag.G2 K) :=
  inG2 K (parabolicSubgroup Tag.G2 K J)

abbrev QG (J : Set (Fin Tag.G2.rank)) : Subgroup ↥(adjointGroup Tag.G2 K) :=
  inG2 K (parabolicRadical Tag.G2 K J)

abbrev BG : Subgroup ↥(adjointGroup Tag.G2 K) := inG2 K (borelGroup Tag.G2 K)

theorem radical_le_C (J : Set (Fin Tag.G2.rank)) :
    parabolicRadical Tag.G2 K J ≤ adjointGroup Tag.G2 K :=
  (parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) J).trans
    (le_sup_right.trans g2Sub_borel_le_adjointGroup)

theorem PG_le_iff (J J' : Set (Fin Tag.G2.rank)) : PG K J ≤ PG K J' ↔ J ⊆ J' := by
  rw [subgroupOf_le_iff' (parabolicSubgroup_le_adjointGroup Tag.G2 K J)
    (parabolicSubgroup_le_adjointGroup Tag.G2 K J')]
  exact (standard_parabolic_cells Tag.G2 K).2.2.2.1 J J'

theorem PG_empty : PG K ∅ = BG K := by
  unfold PG BG inG2
  rw [(standard_parabolic_cells Tag.G2 K).2.2.2.2.1]

theorem PG_univ : PG K Set.univ = ⊤ := by
  unfold PG inG2
  rw [Subgroup.subgroupOf_eq_top, (standard_parabolic_cells Tag.G2 K).2.2.2.2.2.1]

theorem exists_PG_eq {A : Subgroup ↥(adjointGroup Tag.G2 K)} (hB : BG K ≤ A) :
    ∃ J, A = PG K J := by
  have hBC : borelGroup Tag.G2 K ≤ adjointGroup Tag.G2 K := g2Sub_borel_le_adjointGroup
  have hB1 : borelGroup Tag.G2 K ≤ A.map (adjointGroup Tag.G2 K).subtype := by
    intro x hx
    exact ⟨⟨x, hBC hx⟩, hB hx, rfl⟩
  have hAC : A.map (adjointGroup Tag.G2 K).subtype ≤ adjointGroup Tag.G2 K :=
    Subgroup.map_subtype_le A
  obtain ⟨⟨J, hJ, -⟩, -⟩ :=
    (Chevalley_Borel_overgroups_and_radical_normalizers Tag.G2 K).1 _ hB1 hAC
  refine ⟨J, ?_⟩
  unfold PG inG2
  rw [← hJ, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (adjointGroup Tag.G2 K).subtype_injective]

theorem PG_ne_top {J : Set (Fin Tag.G2.rank)} (hJ : J ≠ Set.univ) : PG K J ≠ ⊤ := by
  intro h
  rw [← PG_univ K] at h
  exact hJ (Set.eq_univ_of_univ_subset ((PG_le_iff K _ _).1 h.ge))

theorem PG_lt_of_ssubset {J J' : Set (Fin Tag.G2.rank)} (h : J ⊆ J') (hne : J ≠ J') :
    PG K J < PG K J' :=
  lt_of_le_of_ne ((PG_le_iff K _ _).2 h) fun h' =>
    hne (Set.Subset.antisymm h ((PG_le_iff K _ _).1 h'.ge))

theorem isCoatom_PG_singleton (a : Fin Tag.G2.rank) : IsCoatom (PG K {a}) := by
  have hex : ∃ x : Fin Tag.G2.rank, x ≠ a := by
    revert a
    decide
  obtain ⟨x, hx⟩ := hex
  have hne : ({a} : Set (Fin Tag.G2.rank)) ≠ Set.univ := by
    intro h
    have : x ∈ ({a} : Set (Fin Tag.G2.rank)) := h ▸ Set.mem_univ x
    exact hx this
  refine ⟨PG_ne_top K hne, fun A hA => ?_⟩
  have hBA : BG K ≤ A := by
    rw [← PG_empty K]
    exact ((PG_le_iff K ∅ {a}).2 (Set.empty_subset _)).trans hA.le
  obtain ⟨J, rfl⟩ := exists_PG_eq K hBA
  have hsub : ({a} : Set (Fin Tag.G2.rank)) ⊆ J := (PG_le_iff K _ _).1 hA.le
  by_contra hAtop
  have hJ : J ≠ Set.univ := fun h => hAtop (h ▸ PG_univ K)
  have hJa : J ⊆ {a} := by
    intro z hz
    by_contra hza
    apply hJ
    ext y
    simp only [Set.mem_univ, iff_true]
    rcases two_elements_G2 a z hza y with rfl | rfl
    · exact hsub rfl
    · exact hz
  exact hA.ne (le_antisymm hA.le ((PG_le_iff K _ _).2 hJa))

theorem coatom_eq_PG {A : Subgroup ↥(adjointGroup Tag.G2 K)} (hA : IsCoatom A) (hB : BG K ≤ A) :
    ∃ a, A = PG K {a} := by
  obtain ⟨J, rfl⟩ := exists_PG_eq K hB
  have hJ : J ≠ Set.univ := fun h => hA.1 (h ▸ PG_univ K)
  obtain ⟨a, haJ⟩ : J.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    have hlt := PG_lt_of_ssubset K (Set.empty_subset ({⟨0, by decide⟩} :
      Set (Fin Tag.G2.rank))) (Set.singleton_ne_empty _).symm
    exact (isCoatom_PG_singleton K ⟨0, by decide⟩).1 (hA.2 _ hlt)
  refine ⟨a, ?_⟩
  have hJa : J = {a} := by
    refine Set.Subset.antisymm (fun z hz => ?_) (Set.singleton_subset_iff.2 haJ)
    by_contra hza
    apply hJ
    ext y
    simp only [Set.mem_univ, iff_true]
    rcases two_elements_G2 a z (fun h => hza (h ▸ Set.mem_singleton a)) y with rfl | rfl
    · exact haJ
    · exact hz
  rw [hJa]

theorem QG_le_BG (J : Set (Fin Tag.G2.rank)) : QG K J ≤ BG K := by
  unfold QG BG inG2
  have hBC : borelGroup Tag.G2 K ≤ adjointGroup Tag.G2 K := g2Sub_borel_le_adjointGroup
  rw [subgroupOf_le_iff' (radical_le_C K J) hBC]
  exact (parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) J).trans le_sup_right

theorem QG_le_PG (J : Set (Fin Tag.G2.rank)) : QG K J ≤ PG K J := by
  unfold QG PG inG2
  rw [subgroupOf_le_iff' (radical_le_C K J)
    (parabolicSubgroup_le_adjointGroup Tag.G2 K J)]
  intro y hy
  rw [← (Chevalley_Borel_overgroups_and_radical_normalizers Tag.G2 K).2 J]
  exact Subgroup.mem_inf.2
    ⟨radical_le_C K J hy,
      Subgroup.le_normalizer hy⟩


theorem QG_ne_bot {J : Set (Fin Tag.G2.rank)} (hJ : J ≠ Set.univ) : QG K J ≠ ⊥ := by
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  intro h
  have hx := xUnit_mem_parabolicRadical (τ := Tag.G2) (K := K) hi (1 : K)
  have hxC := radical_le_C K J hx
  have hmem : (⟨_, hxC⟩ : ↥(adjointGroup Tag.G2 K)) ∈ QG K J := hx
  rw [h, Subgroup.mem_bot] at hmem
  have h1 : (xUnit Tag.G2 K i 1 : ModGL Tag.G2 K) = 1 := congrArg Subtype.val hmem
  have h2 : xOp Tag.G2 K i 1 = xOp Tag.G2 K i 0 := by
    have := congrArg (fun u : ModGL Tag.G2 K => (u : Module.End K (RootModule Tag.G2 K))) h1
    simpa [coe_xUnit, xOp_zero] using this
  exact one_ne_zero (xOp_injective _ h2)

theorem PG_normalizes {J : Set (Fin Tag.G2.rank)} :
    ∀ x ∈ PG K J, ∀ q ∈ QG K J, x * q * x⁻¹ ∈ QG K J := by
  intro x hx q hq
  have hN := (Chevalley_Borel_overgroups_and_radical_normalizers Tag.G2 K).2 J
  have hxN : (x : ModGL Tag.G2 K) ∈
      Subgroup.normalizer (parabolicRadical Tag.G2 K J : Set (ModGL Tag.G2 K)) := by
    have : (x : ModGL Tag.G2 K) ∈ adjointGroup Tag.G2 K ⊓
        Subgroup.normalizer (parabolicRadical Tag.G2 K J : Set (ModGL Tag.G2 K)) := by
      rw [hN]
      exact hx
    exact this.2
  exact (Subgroup.mem_normalizer_iff.1 hxN q).1 hq

theorem PG_selfCentralizing {J : Set (Fin Tag.G2.rank)} (hJ : J ≠ Set.univ) :
    ∀ x ∈ PG K J, (∀ q ∈ QG K J, x * q = q * x) → x ∈ QG K J := by
  intro x hx hc
  have hSC := (Chevalley_proper_parabolic_root_radical_self_centralizing Tag.G2 K hJ).2
  have hxC : (x : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K J ⊓
      Subgroup.centralizer (parabolicRadical Tag.G2 K J : Set (ModGL Tag.G2 K)) := by
    refine Subgroup.mem_inf.2 ⟨hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqC : q ∈ adjointGroup Tag.G2 K :=
      radical_le_C K J hq
    have := congrArg Subtype.val (hc ⟨q, hqC⟩ hq)
    exact this.symm
  exact hSC hxC

theorem QG_isPGroup (r : ℕ) [Fact r.Prime] [Finite K] [CharP K r] (J : Set (Fin Tag.G2.rank)) :
    IsPGroup r ↥(QG K J) := by
  have hBC : borelGroup Tag.G2 K ≤ adjointGroup Tag.G2 K := g2Sub_borel_le_adjointGroup
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := le_sup_right.trans hBC
  obtain ⟨hUp, -⟩ := isPGroup_and_not_dvd_index r hUC card_posUnipotent
  refine hUp.to_le ?_
  unfold QG inG2
  rw [subgroupOf_le_iff' (radical_le_C K J) hUC]
  exact parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) J

theorem no_normal_pGroup_G2 (r : ℕ) [Fact r.Prime] [Finite K] (hK : ringChar K ≠ 2) :
    ∀ R : Subgroup ↥(adjointGroup Tag.G2 K), R.Normal → IsPGroup r ↥R → R = ⊥ := by
  intro R hRn hRp
  obtain ⟨hsimp, ⟨x, y, hxy⟩, -⟩ := odd_pinned_Chevalley_p_components Tag.G2 K hK
  rcases hRn.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hG : IsPGroup r ↥(adjointGroup Tag.G2 K) := by
      intro g
      obtain ⟨k, hk⟩ := hRp ⟨g, h ▸ Subgroup.mem_top g⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have : Nontrivial ↥(adjointGroup Tag.G2 K) := ⟨⟨x, y, fun h' => hxy (by rw [h'])⟩⟩
    have hZ := hG.center_nontrivial
    have hcn : (Subgroup.center ↥(adjointGroup Tag.G2 K)).Normal := inferInstance
    rcases hcn.eq_bot_or_eq_top with hz | hz
    · exact (Subgroup.nontrivial_iff_ne_bot _).1 hZ hz
    · have hx : x ∈ Subgroup.center ↥(adjointGroup Tag.G2 K) := hz ▸ Subgroup.mem_top x
      exact hxy ((Subgroup.mem_center_iff.1 hx y).symm)

end Lattice

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
