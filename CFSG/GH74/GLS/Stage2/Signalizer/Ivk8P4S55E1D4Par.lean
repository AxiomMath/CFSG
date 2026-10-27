module

public import CFSG.LieType.Chevalley.GraphFixedParabolicNormalizer
public import CFSG.LieType.Chevalley.GraphFixedParabolicSelfCentralizing
public import CFSG.LieType.Chevalley.GraphFixedOddComponents
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Rig

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.Blueprint.Chevalley in
theorem two_elements : ∀ a x : Fin TwistTag.D4.foldedTag.rank, x ≠ a →
    ∀ y : Fin TwistTag.D4.foldedTag.rank, y = a ∨ y = x := by decide

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

abbrev inC₀ (K : Type) [Field K] (σ : K ≃+* K) (A : Subgroup (ModGL TwistTag.D4.tag K)) :
    Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  A.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

section Lattice

variable (K : Type) [Field K] (σ : K ≃+* K)

abbrev PJ (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  inC₀ K σ (graphFixedParabolic TwistTag.D4 K σ.toRingHom J)

abbrev QJ (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  inC₀ K σ (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J)

abbrev BB : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  inC₀ K σ (graphFixedRootBorel TwistTag.D4 K σ.toRingHom)

theorem PJ_le_iff (J J' : Set (Fin TwistTag.D4.foldedTag.rank)) :
    PJ K σ J ≤ PJ K σ J' ↔ J ⊆ J' := by
  rw [subgroupOf_le_iff' (graphFixedParabolic_le _ K σ.toRingHom J)
    (graphFixedParabolic_le _ K σ.toRingHom J')]
  exact (fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.1 J J'

theorem PJ_empty : PJ K σ ∅ = BB K σ := by
  unfold PJ BB inC₀
  rw [(fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.2.1]

theorem PJ_univ : PJ K σ Set.univ = ⊤ := by
  unfold PJ inC₀
  rw [Subgroup.subgroupOf_eq_top, (fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.2.2]


theorem exists_PJ_eq {A : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hB : BB K σ ≤ A) : ∃ J, A = PJ K σ J := by
  have hB1 : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤
      A.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype := by
    intro x hx
    have hxC : x ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      graphFixedRootBorel_le _ K σ.toRingHom hx
    exact ⟨⟨x, hxC⟩, hB hx, rfl⟩
  have hAC : A.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := Subgroup.map_subtype_le A
  obtain ⟨-, J, hJ, -⟩ := fixed_Borel_overgroup_classification TwistTag.D4 K σ _ hB1 hAC
  refine ⟨J, ?_⟩
  unfold PJ inC₀
  rw [← hJ, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective]

theorem PJ_ne_top {J : Set (Fin TwistTag.D4.foldedTag.rank)} (hJ : J ≠ Set.univ) :
    PJ K σ J ≠ ⊤ := by
  intro h
  rw [← PJ_univ K σ] at h
  exact hJ (Set.eq_univ_of_univ_subset ((PJ_le_iff K σ _ _).1 h.ge))

theorem PJ_lt_of_ssubset {J J' : Set (Fin TwistTag.D4.foldedTag.rank)} (h : J ⊆ J') (hne : J ≠ J') :
    PJ K σ J < PJ K σ J' :=
  lt_of_le_of_ne ((PJ_le_iff K σ _ _).2 h) fun h' =>
    hne (Set.Subset.antisymm h ((PJ_le_iff K σ _ _).1 h'.ge))

theorem isCoatom_PJ_singleton (a : Fin TwistTag.D4.foldedTag.rank) :
    IsCoatom (PJ K σ {a}) := by
  have hex : ∃ x : Fin TwistTag.D4.foldedTag.rank, x ≠ a := by
    revert a
    decide
  obtain ⟨x, hx⟩ := hex
  have hne : ({a} : Set (Fin TwistTag.D4.foldedTag.rank)) ≠ Set.univ := by
    intro h
    have : x ∈ ({a} : Set (Fin TwistTag.D4.foldedTag.rank)) := h ▸ Set.mem_univ x
    exact hx this
  refine ⟨PJ_ne_top K σ hne, fun A hA => ?_⟩
  have hBA : BB K σ ≤ A := by
    rw [← PJ_empty K σ]
    exact ((PJ_le_iff K σ ∅ {a}).2 (Set.empty_subset _)).trans hA.le
  obtain ⟨J, rfl⟩ := exists_PJ_eq K σ hBA
  have hsub : ({a} : Set (Fin TwistTag.D4.foldedTag.rank)) ⊆ J := (PJ_le_iff K σ _ _).1 hA.le
  by_contra hAtop
  have hJ : J ≠ Set.univ := fun h => hAtop (h ▸ PJ_univ K σ)
  have hJa : J ⊆ {a} := by
    intro z hz
    by_contra hza
    apply hJ
    ext y
    simp only [Set.mem_univ, iff_true]
    rcases two_elements a z hza y with rfl | rfl
    · exact hsub rfl
    · exact hz
  exact hA.ne (le_antisymm hA.le ((PJ_le_iff K σ _ _).2 hJa))

theorem coatom_eq_PJ {A : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hA : IsCoatom A) (hB : BB K σ ≤ A) : ∃ a, A = PJ K σ {a} := by
  obtain ⟨J, rfl⟩ := exists_PJ_eq K σ hB
  have hJ : J ≠ Set.univ := fun h => hA.1 (h ▸ PJ_univ K σ)
  obtain ⟨a, haJ⟩ : J.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    obtain ⟨i, hi⟩ : ∃ i : Fin TwistTag.D4.foldedTag.rank, True := ⟨⟨0, by decide⟩, trivial⟩
    have hlt := PJ_lt_of_ssubset K σ (Set.empty_subset ({i} : Set (Fin TwistTag.D4.foldedTag.rank)))
      (Set.singleton_ne_empty i).symm
    exact (isCoatom_PJ_singleton K σ i).1 (hA.2 _ hlt)
  refine ⟨a, ?_⟩
  have hJa : J = {a} := by
    refine Set.Subset.antisymm (fun z hz => ?_) (Set.singleton_subset_iff.2 haJ)
    by_contra hza
    apply hJ
    ext y
    simp only [Set.mem_univ, iff_true]
    rcases two_elements a z (fun h => hza (h ▸ Set.mem_singleton a)) y with rfl | rfl
    · exact haJ
    · exact hz
  rw [hJa]


theorem QJ_le_BB (J : Set (Fin TwistTag.D4.foldedTag.rank)) : QJ K σ J ≤ BB K σ := by
  unfold QJ BB inC₀
  rw [subgroupOf_le_iff' (graphFixedParabolicRadical_le_graphFixedRootGroup _ K σ.toRingHom J)
    (graphFixedRootBorel_le _ K σ.toRingHom)]
  exact fun x hx => graphFixedPosUnipotent_le_graphFixedRootBorel
    (graphFixedParabolicRadical_le_graphFixedPosUnipotent J hx)

theorem QJ_isPGroup (r : ℕ) [Fact r.Prime] [Finite K] [CharP K r]
    (J : Set (Fin TwistTag.D4.foldedTag.rank)) : IsPGroup r ↥(QJ K σ J) := by
  have hU := isPGroup_graphFixedPosUnipotent_subgroupOf r (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom)
  refine hU.to_le ?_
  unfold QJ inC₀
  rw [subgroupOf_le_iff' (graphFixedParabolicRadical_le_graphFixedRootGroup _ K σ.toRingHom J)
    (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ.toRingHom)]
  exact fun x hx => graphFixedParabolicRadical_le_graphFixedPosUnipotent J hx

theorem QJ_ne_bot {J : Set (Fin TwistTag.D4.foldedTag.rank)} (hJ : J ≠ Set.univ) :
    QJ K σ J ≠ ⊥ := by
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  intro h
  have hx := orbitX_mem_graphFixedParabolicRadical (σ := σ.toRingHom) ha 1
  have hxC : (orbitX TwistTag.D4 K σ.toRingHom a 1 : ModGL TwistTag.D4.tag K) ∈
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedRootGroup _ K σ.toRingHom J hx
  have hmem : (⟨_, hxC⟩ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈ QJ K σ J := hx
  rw [h, Subgroup.mem_bot] at hmem
  have h1 := congrArg Subtype.val hmem
  have h2 : orbitX TwistTag.D4 K σ.toRingHom a 1 = orbitX TwistTag.D4 K σ.toRingHom a 0 := by
    apply Subtype.ext
    rw [orbitX_zero]
    exact h1
  exact one_ne_zero (orbitX_injective σ.toRingHom a h2)

theorem PJ_normalizes {J : Set (Fin TwistTag.D4.foldedTag.rank)} :
    ∀ x ∈ PJ K σ J, ∀ q ∈ QJ K σ J, x * q * x⁻¹ ∈ QJ K σ J := by
  intro x hx q hq
  have hN := diagram_fixed_parabolic_root_radical_normalizers TwistTag.D4 K σ J
  have hxN : (x : ModGL TwistTag.D4.tag K) ∈
      Subgroup.normalizer (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J :
        Set (ModGL TwistTag.D4.tag K)) := by
    have : (x : ModGL TwistTag.D4.tag K) ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
        Subgroup.normalizer (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J :
          Set (ModGL TwistTag.D4.tag K)) := by
      rw [hN]
      exact hx
    exact this.2
  exact (Subgroup.mem_normalizer_iff.1 hxN q).1 hq

theorem PJ_selfCentralizing {J : Set (Fin TwistTag.D4.foldedTag.rank)} (hJ : J ≠ Set.univ) :
    ∀ x ∈ PJ K σ J, (∀ q ∈ QJ K σ J, x * q = q * x) → x ∈ QJ K σ J := by
  intro x hx hc
  have hSC := diagram_fixed_proper_parabolic_root_radical_self_centralizing TwistTag.D4 K σ hJ
  have hxC : (x : ModGL TwistTag.D4.tag K) ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J ⊓
      Subgroup.centralizer (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J :
        Set (ModGL TwistTag.D4.tag K)) := by
    refine Subgroup.mem_inf.2 ⟨hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqC : q ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      graphFixedParabolicRadical_le_graphFixedRootGroup _ K σ.toRingHom J hq
    have := congrArg Subtype.val (hc ⟨q, hqC⟩ hq)
    exact this.symm
  rw [hSC.1] at hxC
  obtain ⟨z, -, hz⟩ := hxC
  show (x : ModGL TwistTag.D4.tag K) ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J
  rw [← hz]
  exact z.2

theorem no_normal_pGroup (r : ℕ) [Fact r.Prime] [Finite K] (hK : ringChar K ≠ 2) :
    ∀ R : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), R.Normal → IsPGroup r ↥R →
      R = ⊥ := by
  intro R hRn hRp
  obtain ⟨hsimp, ⟨x, y, hxy⟩, -⟩ := odd_diagram_field_fixed_p_components TwistTag.D4 K hK σ
  rcases hRn.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hG : IsPGroup r ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
      intro g
      obtain ⟨k, hk⟩ := hRp ⟨g, h ▸ Subgroup.mem_top g⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have : Nontrivial ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      ⟨⟨x, y, fun h' => hxy (by rw [h'])⟩⟩
    have hZ := hG.center_nontrivial
    have hcn : (Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).Normal :=
      inferInstance
    rcases hcn.eq_bot_or_eq_top with hz | hz
    · exact (Subgroup.nontrivial_iff_ne_bot _).1 hZ hz
    · have hx : x ∈ Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
        hz ▸ Subgroup.mem_top x
      exact hxy ((Subgroup.mem_center_iff.1 hx y).symm)

theorem QJ_le_PJ (J : Set (Fin TwistTag.D4.foldedTag.rank)) : QJ K σ J ≤ PJ K σ J := by
  unfold QJ PJ inC₀
  rw [subgroupOf_le_iff' (graphFixedParabolicRadical_le_graphFixedRootGroup _ K σ.toRingHom J)
    (graphFixedParabolic_le _ K σ.toRingHom J)]
  intro y hy
  rw [← diagram_fixed_parabolic_root_radical_normalizers TwistTag.D4 K σ J]
  exact Subgroup.mem_inf.2
    ⟨graphFixedParabolicRadical_le_graphFixedRootGroup _ K σ.toRingHom J hy,
      Subgroup.le_normalizer hy⟩

end Lattice

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
