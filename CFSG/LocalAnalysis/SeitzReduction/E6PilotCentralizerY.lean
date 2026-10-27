module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYRoots
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUStd

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem commute_of_pair {G : Type*} [Group G] {X Y A B Z : G} (hXA : X * A = A * X)
    (hYB : Y * B = B * Y) (hXB : X * B = Z * B * X) (hYA : Y * A = Z * A * Y)
    (hZX : Z * X = X * Z) (hZA : Z * A = A * Z) (hZZ : Z * Z = 1) :
    X * Y * (A * B) = A * B * (X * Y) := by
  calc X * Y * (A * B) = X * (Y * A) * B := by group
    _ = X * (Z * A * Y) * B := by rw [hYA]
    _ = X * Z * A * (Y * B) := by group
    _ = X * Z * A * (B * Y) := by rw [hYB]
    _ = (Z * X) * A * B * Y := by rw [hZX]; group
    _ = Z * (X * A) * B * Y := by group
    _ = Z * (A * X) * B * Y := by rw [hXA]
    _ = Z * A * (X * B) * Y := by group
    _ = Z * A * (Z * B * X) * Y := by rw [hXB]
    _ = (Z * A * Z) * B * X * Y := by group
    _ = (Z * Z * A) * B * X * Y := by rw [mul_assoc Z A Z, ← hZA, ← mul_assoc]
    _ = A * B * (X * Y) := by rw [hZZ, one_mul]; group

section Defs


variable (K : Type) [Field K]

@[expose] def yLeviGens : Set (ModGL .E6 K) :=
  {g | ∃ γ ∈ yFixedRoots, ∃ c : K, g = pinnedX .E6 K γ c} ∪
    {g | ∃ δ ∈ yPairRoots, ∃ c : K, g = pinnedX .E6 K δ c * pinnedX .E6 K (yPartner δ) c}

@[expose] noncomputable def yLeviGL : Subgroup (ModGL .E6 K) :=
  closure (yLeviGens K)

@[expose] noncomputable def yLevi : Subgroup (adjointGroup .E6 K) :=
  (yLeviGL K).subgroupOf (adjointGroup .E6 K)

@[expose] noncomputable def yRadical : Subgroup (adjointGroup .E6 K) :=
  (rootSpan .E6 K yRadicalRoots).subgroupOf (adjointGroup .E6 K)

@[expose] noncomputable def yLeviD4 : Subgroup (adjointGroup .E6 K) :=
  (rootSpan .E6 K yLeviRoots).subgroupOf (adjointGroup .E6 K)

variable {K}

theorem mem_yLevi_iff {g : adjointGroup .E6 K} : g ∈ yLevi K ↔ (g : ModGL .E6 K) ∈ yLeviGL K :=
  mem_subgroupOf

theorem mem_yRadical_iff {g : adjointGroup .E6 K} :
    g ∈ yRadical K ↔ (g : ModGL .E6 K) ∈ rootSpan .E6 K yRadicalRoots :=
  mem_subgroupOf

theorem yLeviGens_subset_rootSpan : yLeviGens K ⊆ rootSpan .E6 K yLeviRoots := by
  rintro _ (⟨γ, hγ, c, rfl⟩ | ⟨δ, hδ, c, rfl⟩)
  · exact pinnedX_mem_rootSpan (yFixedRoots_subset_yLeviRoots hγ) c
  · obtain ⟨hr, h1, h4, -, -⟩ := yPartner_spec hδ
    have hp : yPartner δ ∈ yLeviRoots := ⟨hr, by rw [iform_yLam, h1, h4]; norm_num⟩
    exact mul_mem (pinnedX_mem_rootSpan (yPairRoots_subset_yLeviRoots hδ) c)
      (pinnedX_mem_rootSpan hp c)

theorem yLeviGL_le_rootSpan : yLeviGL K ≤ rootSpan .E6 K yLeviRoots :=
  (closure_le _).2 yLeviGens_subset_rootSpan

theorem yLeviGL_le_adjointGroup : yLeviGL K ≤ adjointGroup .E6 K :=
  yLeviGL_le_rootSpan.trans (rootSpan_le_adjointGroup K _)

theorem yLevi_le_yLeviD4 : yLevi K ≤ yLeviD4 K := fun _ hg =>
  mem_subgroupOf.2 (yLeviGL_le_rootSpan (mem_subgroupOf.1 hg))

end Defs

theorem e6_simplyLaced : Tag.E6 = .D4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 :=
  Or.inr (Or.inl rfl)

section Centralize


variable {K : Type} [Field K]

theorem commute_pinnedX_yD {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) (h1 : 0 ≤ iform γ yA1)
    (h4 : 0 ≤ iform γ yA4) (c : K) :
    Commute (pinnedX .E6 K γ c) (e6Rep K 1 : ModGL .E6 K) := by
  rw [coe_e6Rep_one]
  exact (classD4_commute_pinnedX e6_simplyLaced hγ (isRoot_single _ _) h1 c 1).mul_right
    (classD4_commute_pinnedX e6_simplyLaced hγ (isRoot_single _ _) h4 c 1)

theorem rootSpan_yRadicalRoots_le_centralizer :
    rootSpan .E6 K yRadicalRoots ≤ centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) := by
  refine iSup₂_le fun γ hγ => (closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  obtain ⟨h1, h4⟩ := iform_nonneg_of_mem_yRadicalRoots hγ
  exact (commute_pinnedX_yD hγ.1 h1 h4 c).eq

theorem commute_pair_yD [CharP K 2] {δ : Fin Tag.E6.rank → ℤ} (hδ : δ ∈ yPairRoots) (c : K) :
    Commute (pinnedX .E6 K δ c * pinnedX .E6 K (yPartner δ) c) (e6Rep K 1 : ModGL .E6 K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨-, h11, h44, h14, h41⟩ := yLam_eq
  obtain ⟨hδr, hδ1, hδ4⟩ := hδ
  obtain ⟨hpr, hp1, hp4, hzr, hsum⟩ := yPartner_spec ⟨hδr, hδ1, hδ4⟩
  have hA : IsRoot .E6 yA1 := isRoot_single _ _
  have hB : IsRoot .E6 yA4 := isRoot_single _ _
  have hδδ : iform δ δ = 2 := classD4_iform_self e6_simplyLaced hδr
  have hchk := oddDerivLacedCheck_of_simplyLaced e6_simplyLaced
  have hXA := (classD4_commute_pinnedX (R := K) e6_simplyLaced hδr hA
    (by rw [hδ1]; norm_num) c 1).eq
  have hYB := (classD4_commute_pinnedX (R := K) e6_simplyLaced hpr hB
    (by rw [hp4]; norm_num) c 1).eq
  have hXB : pinnedX .E6 K δ c * pinnedX .E6 K yA4 1 =
      pinnedX .E6 K (δ + yA4) c * pinnedX .E6 K yA4 1 * pinnedX .E6 K δ c := by
    obtain ⟨-, hne, hne'⟩ := classD4_isRoot_add e6_simplyLaced hδr hB hδ4
    have hc := commutatorElement_pinnedX_of_oddDerivLaced h2 hchk hδr hB hne hne' hzr c 1
    rw [commutatorElement_def, mul_one] at hc
    rw [← hc]
    group
  have hYA : pinnedX .E6 K (yPartner δ) c * pinnedX .E6 K yA1 1 =
      pinnedX .E6 K (δ + yA4) c * pinnedX .E6 K yA1 1 * pinnedX .E6 K (yPartner δ) c := by
    obtain ⟨-, hne, hne'⟩ := classD4_isRoot_add e6_simplyLaced hpr hA hp1
    have hr' : IsRoot .E6 (yPartner δ + yA1) := by rw [hsum]; exact hzr
    have hc := commutatorElement_pinnedX_of_oddDerivLaced h2 hchk hpr hA hne hne' hr' c 1
    rw [commutatorElement_def, mul_one, hsum] at hc
    rw [← hc]
    group
  have hZX := (classD4_commute_pinnedX (R := K) e6_simplyLaced hzr hδr
    (by rw [iform_add_left, hδδ, iform_comm, hδ4]; norm_num) c c).eq
  have hZA := (classD4_commute_pinnedX (R := K) e6_simplyLaced hzr hA
    (by rw [iform_add_left, hδ1, h41]; norm_num) c 1).eq
  have hZZ : pinnedX .E6 K (δ + yA4) c * pinnedX .E6 K (δ + yA4) c = 1 := by
    rw [← pinnedX_add, ← two_mul, h2, zero_mul, pinnedX_zero]
  rw [commute_iff_eq, coe_e6Rep_one]
  exact commute_of_pair hXA hYB hXB hYA hZX hZA hZZ

theorem yLeviGL_le_centralizer [CharP K 2] :
    yLeviGL K ≤ centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) := by
  refine (closure_le _).2 ?_
  rintro _ (⟨γ, hγ, c, rfl⟩ | ⟨δ, hδ, c, rfl⟩)
  · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (commute_pinnedX_yD hγ.1 hγ.2.1.ge hγ.2.2.ge c).eq
  · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (commute_pair_yD hδ c).eq

theorem mem_centralizer_e6Rep_iff (κ : Fin 3) {g : adjointGroup .E6 K} :
    g ∈ centralizer ({e6Rep K κ} : Set (adjointGroup .E6 K)) ↔
      (g : ModGL .E6 K) ∈ centralizer ({(e6Rep K κ : ModGL .E6 K)} : Set (ModGL .E6 K)) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem yRadical_sup_yLevi_le_centralizer [CharP K 2] :
    yRadical K ⊔ yLevi K ≤ centralizer ({e6Rep K 1} : Set (adjointGroup .E6 K)) :=
  sup_le (fun _ hg => (mem_centralizer_e6Rep_iff 1).2
      (rootSpan_yRadicalRoots_le_centralizer (mem_subgroupOf.1 hg)))
    (fun _ hg => (mem_centralizer_e6Rep_iff 1).2 (yLeviGL_le_centralizer (mem_subgroupOf.1 hg)))

end Centralize

section HighRoot


variable {K : Type} [Field K]

theorem rootSubgroup_le_yLeviGL {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ yFixedRoots) :
    rootSubgroup .E6 K γ ≤ yLeviGL K := by
  refine (closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  exact subset_closure (Or.inl ⟨γ, hγ, c, rfl⟩)

theorem highRootSL2_le_yLeviGL : EPilot.highRootSL2 .E6 K ≤ yLeviGL K :=
  sup_le (rootSubgroup_le_yLeviGL highRoot_mem_yFixedRoots.1)
    (rootSubgroup_le_yLeviGL highRoot_mem_yFixedRoots.2)

theorem highRootSL2_le_yLevi :
    (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) ≤ yLevi K := fun _ hg =>
  mem_subgroupOf.2 (highRootSL2_le_yLeviGL (mem_subgroupOf.1 hg))

end HighRoot

section Structure


variable {K : Type} [Field K]

theorem rootSpan_yRadicalRoots_eq_map :
    rootSpan .E6 K yRadicalRoots =
      (parabolicRadical .E6 K nodes16).map
        (MulAut.conj (e6RepConj K 1 : ModGL .E6 K)).toMonoidHom := by
  rw [parabolicRadical, map_conj_e6RepConj_rootSpan 1 (fun ρ hρ => hρ.1.1),
    image_e6RepWeyl_parabolicRadicalRoots_nodes16]

theorem rootSpan_yLeviRoots_eq_map :
    rootSpan .E6 K yLeviRoots =
      (rootSpan .E6 K (parabolicRoots .E6 nodes16)).map
        (MulAut.conj (e6RepConj K 1 : ModGL .E6 K)).toMonoidHom := by
  rw [map_conj_e6RepConj_rootSpan 1 (fun ρ hρ => hρ.1),
    image_e6RepWeyl_parabolicRoots_nodes16]

theorem isPGroup_rootSpan_yRadicalRoots [Finite K] [CharP K 2] :
    IsPGroup 2 (rootSpan .E6 K yRadicalRoots) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hQp, -⟩ := (parabolic_root_radical_Levi_factors .E6 K nodes16).2.2.2.2.2.2.2.2.2.2.2.2 2
  rw [rootSpan_yRadicalRoots_eq_map]
  exact hQp.map _

theorem rootSpan_yLeviRoots_le_normalizer :
    rootSpan .E6 K yLeviRoots ≤ normalizer (rootSpan .E6 K yRadicalRoots : Set (ModGL .E6 K)) := by
  rw [rootSpan_yLeviRoots_eq_map, rootSpan_yRadicalRoots_eq_map]
  change (rootSpan .E6 K (parabolicRoots .E6 nodes16)).map
      (MulAut.conj (e6RepConj K 1 : ModGL .E6 K)).toMonoidHom ≤
    normalizer ((parabolicRadical .E6 K nodes16).map
      (MulAut.conj (e6RepConj K 1 : ModGL .E6 K)).toMonoidHom : Set (ModGL .E6 K))
  rw [← map_equiv_normalizer_eq]
  exact map_mono (F4Pilot.rootSpan_parabolicRoots_le_normalizer nodes16)

theorem rootSpan_yRadicalRoots_inf_rootSpan_yLeviRoots :
    rootSpan .E6 K yRadicalRoots ⊓ rootSpan .E6 K yLeviRoots = ⊥ := by
  rw [rootSpan_yLeviRoots_eq_map, rootSpan_yRadicalRoots_eq_map,
    ← map_inf_eq _ _ _ (MulAut.conj (e6RepConj K 1 : ModGL .E6 K)).injective,
    F4Pilot.parabolicRadical_inf_rootSpan nodes16, Subgroup.map_bot]

theorem rootSpan_yRadicalRoots_le_adjointGroup :
    rootSpan .E6 K yRadicalRoots ≤ adjointGroup .E6 K :=
  rootSpan_le_adjointGroup K _

theorem isPGroup_yRadical [Finite K] [CharP K 2] : IsPGroup 2 (yRadical K) :=
  F4Pilot.isPGroup_subgroupOf_of_le rootSpan_yRadicalRoots_le_adjointGroup
    isPGroup_rootSpan_yRadicalRoots

theorem yLeviD4_le_normalizer_yRadical :
    yLeviD4 K ≤ normalizer (yRadical K : Set (adjointGroup .E6 K)) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro y
  have hmN := mem_normalizer_iff.1 (rootSpan_yLeviRoots_le_normalizer (mem_subgroupOf.1 hm))
    (y : ModGL .E6 K)
  simp only [yRadical, mem_subgroupOf, coe_mul, coe_inv]
  exact hmN

theorem yLevi_le_normalizer_yRadical :
    yLevi K ≤ normalizer (yRadical K : Set (adjointGroup .E6 K)) :=
  yLevi_le_yLeviD4.trans yLeviD4_le_normalizer_yRadical

theorem disjoint_yRadical_yLeviD4 : Disjoint (yRadical K) (yLeviD4 K) := by
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  obtain ⟨hxQ, hxL⟩ := mem_inf.1 hx
  have h := mem_inf.2 ⟨mem_subgroupOf.1 hxQ, mem_subgroupOf.1 hxL⟩
  rw [rootSpan_yRadicalRoots_inf_rootSpan_yLeviRoots, mem_bot] at h
  exact (mem_bot).2 (Subtype.ext h)

theorem disjoint_yRadical_yLevi : Disjoint (yRadical K) (yLevi K) :=
  disjoint_yRadical_yLeviD4.mono_right yLevi_le_yLeviD4

end Structure

end CFSG.SeitzReduction.E6Pilot
