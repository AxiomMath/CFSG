module

public import CFSG.LocalAnalysis.SeitzReduction.EnKLOrderSix
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerT
public import CFSG.RankThree.GF2n.Stroth80.Sec117ConfigBasic

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.GF2n.Stroth80

local instance twistedE6KLLeviNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩


variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem exists_mem_su6Levi_orderOf_eq_three [CharP K 2] (σ : K →+* K) :
    ∃ u ∈ (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), orderOf u = 3 ∧
      ∀ c : K, (u : ModGL TwistTag.E6.tag K) * pinnedX TwistTag.E6.tag K e6HighestRoot c =
        pinnedX TwistTag.E6.tag K e6HighestRoot c * (u : ModGL TwistTag.E6.tag K) := by
  have hr : IsRoot TwistTag.E6.tag (Pi.single 3 1) := isRoot_single _ 3
  have hr' : IsRoot TwistTag.E6.tag (-Pi.single 3 1) := CFSG.LieType.Chevalley.IsRoot.neg hr
  have h₁ : pinnedX TwistTag.E6.tag K (Pi.single 3 1) 1 ∈ su6Levi σ :=
    ⟨pinnedX_mem_subsystemGroup_setA hr (by decide) 1,
      pinnedX_mem_graphFixedRootGroup_of_fixed σ hr (by decide) (map_one σ)⟩
  have h₂ : pinnedX TwistTag.E6.tag K (-Pi.single 3 1) 1 ∈ su6Levi σ :=
    ⟨pinnedX_mem_subsystemGroup_setA hr' (by decide) 1,
      pinnedX_mem_graphFixedRootGroup_of_fixed σ hr' (by decide) (map_one σ)⟩
  refine ⟨⟨_, mul_mem (su6Levi_le_graphFixedRootGroup σ h₁)
    (su6Levi_le_graphFixedRootGroup σ h₂)⟩, mem_subgroupOf.2 (mul_mem h₁ h₂), ?_, fun c => ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact EPilot.orderOf_pinnedX_mul_pinnedX_neg_one hr
  · have c₁ := commute_pinnedX_of_oddDeriv hr isRoot_e6HighestRoot (by decide +kernel)
      (not_isRoot_of_oddDerivNotRootB (by decide +kernel)) (1 : K) c
    have c₂ := commute_pinnedX_of_oddDeriv hr' isRoot_e6HighestRoot (by decide +kernel)
      (not_isRoot_of_oddDerivNotRootB (by decide +kernel)) (1 : K) c
    exact (c₁.mul_left c₂).eq

private theorem su6Levi_subgroupOf_le_centralizer_stdRepC [CharP K 2] (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      Subgroup.centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
  rw [centralizer_stdRepC_zero_eq hf hk hK hσ]
  exact le_sup_right

private theorem isSimpleGroup_su6Levi_subgroupOf (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsSimpleGroup ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) :=
  (Subgroup.subgroupOfEquivOfLe (su6Levi_le_graphFixedRootGroup σ)).isSimpleGroup_congr.mpr
    (isSimpleGroup_su6Levi hf hk hK hσ)

private theorem pinnedX_e6RootA4_twistedE6PairX_ne_mul_comm [CharP K 2] (σ : K →+* K) :
    pinnedX TwistTag.E6.tag K e6RootA4 1 * twistedE6PairX σ e6RootA3 1 ≠
      twistedE6PairX σ e6RootA3 1 * pinnedX TwistTag.E6.tag K e6RootA4 1 := by
  intro h
  have h1 := commutatorElement_eq_one_iff_mul_comm.mpr h
  have hα3 : IsRoot TwistTag.E6.tag e6RootA3 := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have hα4 : IsRoot TwistTag.E6.tag e6RootA4 := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have hρ3 : permLattice TwistTag.E6.perm e6RootA3 = e6RootA5 := by decide
  have hρ4 : permLattice TwistTag.E6.perm e6RootA4 = e6RootA4 := by decide
  have hγ : IsRoot TwistTag.E6.tag (e6RootA4 + e6RootA3) := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have he : IsRoot TwistTag.E6.tag
      (e6RootA3 + (e6RootA4 + permLattice TwistTag.E6.perm e6RootA3)) := by
    rw [hρ3, isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have h4 : ¬IsRoot TwistTag.E6.tag
      (e6RootA3 + (e6RootA4 + permLattice TwistTag.E6.perm e6RootA3) +
        (e6RootA4 + permLattice TwistTag.E6.perm e6RootA3)) := by
    rw [hρ3, isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have h4' : e6RootA3 + (e6RootA4 + permLattice TwistTag.E6.perm e6RootA3) +
      (e6RootA4 + permLattice TwistTag.E6.perm e6RootA3) ≠ 0 := by
    rw [hρ3]; decide
  have hc := commutator_pinnedX_twistedE6PairX_of_fixed (σ := σ) (α := e6RootA4)
    (β := e6RootA3) hα4 hρ4 hα3 hγ he (by decide)
    (by rw [hρ3]; decide) (by rw [hρ3]; decide) h4 h4' (c := 1) (map_one σ) 1
  rw [hc, map_one, mul_one, one_mul, hρ3, twistedE6PairX,
    show permLattice TwistTag.E6.perm (e6RootA4 + e6RootA3) = e6RootA45 by decide, map_one,
    show e6RootA4 + e6RootA3 = e6RootA34 by decide,
    show e6RootA3 + (e6RootA4 + e6RootA5) = e6CascC by decide] at h1
  refine list_prod_pinnedX_one_ne_one (τ := TwistTag.E6.tag) (K := K) (m := 3) (by norm_num)
    (![e6RootA34, e6RootA45, e6CascC] : Fin 3 → Fin TwistTag.E6.tag.rank → ℤ)
    (by decide) (by
      intro i
      fin_cases i <;> exact ⟨by rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel, by decide⟩) ?_
  simpa [List.ofFn_succ, mul_assoc] using h1

private theorem pinnedX_e6RootA4_twistedE6PairX_mem_su6Levi_and_posUnipotent [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    pinnedX TwistTag.E6.tag K e6RootA4 1 ∈ su6Levi σ ∧
      twistedE6PairX σ e6RootA3 1 ∈ su6Levi σ ∧
        pinnedX TwistTag.E6.tag K e6RootA4 1 ∈ posUnipotent TwistTag.E6.tag K ∧
          twistedE6PairX σ e6RootA3 1 ∈ posUnipotent TwistTag.E6.tag K := by
  have hα3 : IsRoot TwistTag.E6.tag e6RootA3 := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have hα4 : IsRoot TwistTag.E6.tag e6RootA4 := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have hα5 : IsRoot TwistTag.E6.tag e6RootA5 := by
    rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
  have hρ3 : permLattice TwistTag.E6.perm e6RootA3 = e6RootA5 := by decide
  have hρ4 : permLattice TwistTag.E6.perm e6RootA4 = e6RootA4 := by decide
  have h3 : e6RootA3 ∈ {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α} := ⟨hα3, by decide⟩
  have h4 : e6RootA4 ∈ {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α} := ⟨hα4, by decide⟩
  have h5 : e6RootA5 ∈ {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α} := ⟨hα5, by decide⟩
  have hxL : pinnedX TwistTag.E6.tag K e6RootA4 1 ∈ su6Levi σ :=
    ⟨pinnedX_mem_subsystemGroup_setA hα4 (by decide) 1,
      pinnedX_mem_graphFixedRootGroup_of_fixed σ hα4 hρ4 (map_one σ)⟩
  have hyL : twistedE6PairX σ e6RootA3 1 ∈ su6Levi σ := by
    have hC : twistedE6PairX σ e6RootA3 1 ∈ graphFixedRootGroup TwistTag.E6 K σ :=
      twistedE6PairX_mem_graphFixedRootGroup (apply_apply_eq hK hσ) hα3 1
    refine ⟨?_, hC⟩
    rw [twistedE6PairX, hρ3, map_one]
    exact mul_mem (pinnedX_mem_subsystemGroup_setA hα3 (by decide) 1)
      (pinnedX_mem_subsystemGroup_setA hα5 (by decide) 1)
  exact ⟨hxL, hyL, pinnedX_mem_rootSpan h4 1, by
    rw [twistedE6PairX, hρ3, map_one]
    exact mul_mem (pinnedX_mem_rootSpan h3 1) (pinnedX_mem_rootSpan h5 1)⟩

private theorem closure_pair_le_su6Levi_and_isPGroup [CharP K 2] [Finite K]
    {σ : K →+* K} {x y : graphFixedRootGroup TwistTag.E6 K σ}
    (hxL : (x : ModGL TwistTag.E6.tag K) ∈ su6Levi σ)
    (hyL : (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ)
    (hxU : (x : ModGL TwistTag.E6.tag K) ∈ posUnipotent TwistTag.E6.tag K)
    (hyU : (y : ModGL TwistTag.E6.tag K) ∈ posUnipotent TwistTag.E6.tag K) :
    closure ({x, y} : Set (graphFixedRootGroup TwistTag.E6 K σ)) ≤
        (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ∧
      IsPGroup 2 (closure ({x, y} : Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have hSL : closure ({x, y} : Set (graphFixedRootGroup TwistTag.E6 K σ)) ≤
      (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_subgroupOf.2 hxL
    · exact Subgroup.mem_subgroupOf.2 hyL
  have hSU : closure ({x, y} : Set (graphFixedRootGroup TwistTag.E6 K σ)) ≤
      (posUnipotent TwistTag.E6.tag K).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_subgroupOf.2 hxU
    · exact Subgroup.mem_subgroupOf.2 hyU
  have hP : IsPGroup 2 ((posUnipotent TwistTag.E6.tag K).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)) :=
    (isPGroup_posUnipotent_of_charP (τ := TwistTag.E6.tag) (p := 2)).comap_subtype
  exact ⟨hSL, hP.to_le hSU⟩

private theorem exists_nonabelian_twoSubgroup_su6Levi [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ S : Subgroup (graphFixedRootGroup TwistTag.E6 K σ),
      S ≤ (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ∧
        IsPGroup 2 S ∧ ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x := by
  have hfin : Finite K := finite_of_card hK
  obtain ⟨hxL, hyL, hxU, hyU⟩ :=
    pinnedX_e6RootA4_twistedE6PairX_mem_su6Levi_and_posUnipotent hK hσ
  let x₀ : graphFixedRootGroup TwistTag.E6 K σ :=
    ⟨pinnedX TwistTag.E6.tag K e6RootA4 1, hxL.2⟩
  let y₀ : graphFixedRootGroup TwistTag.E6 K σ :=
    ⟨twistedE6PairX σ e6RootA3 1, hyL.2⟩
  obtain ⟨hSL, hS2⟩ := closure_pair_le_su6Levi_and_isPGroup (σ := σ) (x := x₀) (y := y₀)
    hxL hyL hxU hyU
  refine ⟨closure {x₀, y₀}, hSL, hS2, x₀, Subgroup.subset_closure (by simp),
    y₀, Subgroup.subset_closure (by simp), ?_⟩
  intro h
  exact pinnedX_e6RootA4_twistedE6PairX_ne_mul_comm σ (by simpa [x₀, y₀] using h)

private theorem le_centralizer_or_le_of_normal_subgroupOf_su6Levi
    (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {H : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (hHL : H ≤ (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
    (hHn : ∀ l ∈ (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ),
      ∀ h ∈ H, l * h * l⁻¹ ∈ H) :
    H ≤ Subgroup.centralizer
        ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) : Set _) ∨
      (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤ H := by
  have hsimple := isSimpleGroup_su6Levi_subgroupOf hf hk hK hσ
  have hN : (H.subgroupOf ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))).Normal :=
    ⟨fun h hh l => by
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      exact hHn l l.2 h hh⟩
  rcases (Subgroup.isSimpleGroup_iff (H := (su6Levi σ).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ))).mp hsimple |>.2 H hHL hN with h | h
  · exact Or.inl (h ▸ bot_le)
  · exact Or.inr (h ▸ le_rfl)

theorem su6Levi_subgroupOf_le_of_isA2PlaneKernel [CharP K 2] (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {a : ℕ} {N : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (hN : IsA2PlaneKernel (stdRepC (apply_apply_eq hK hσ) 0) a N) :
    (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤ N := by
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ
  set L := (su6Levi σ).subgroupOf C₀
  have hsimple := isSimpleGroup_su6Levi_subgroupOf hf hk hK hσ
  obtain ⟨S, hSL, hS2, x, hxS, y, hyS, hxy⟩ :=
    exists_nonabelian_twoSubgroup_su6Levi hK hσ
  let xL : L := ⟨x, hSL hxS⟩
  let yL : L := ⟨y, hSL hyS⟩
  have hxyL : xL * yL ≠ yL * xL := by
    intro h
    exact hxy (by simpa [xL, yL] using congrArg (fun z : L => (z : C₀)) h)
  have hcenter : Subgroup.center L = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top yL) xL) hxyL
  have hLz : ∀ z ∈ L, z ∈ Subgroup.centralizer (L : Set C₀) → Odd (orderOf z) := by
    intro z hzL hzc
    have hz1 : z = 1 := by
      have hzcenter : (⟨z, hzL⟩ : L) ∈ Subgroup.center L := by
        rw [Subgroup.mem_center_iff]
        intro w
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzc w w.2)
      rw [hcenter, Subgroup.mem_bot] at hzcenter
      simpa using congrArg (fun w : L => (w : C₀)) hzcenter
    rw [hz1, orderOf_one]
    exact odd_one
  refine IsA2PlaneKernel.le_of_forall_normal hN ?_ ?_ hLz hSL hS2 ⟨x, hxS, y, hyS, hxy⟩
  · exact su6Levi_subgroupOf_le_centralizer_stdRepC hf hk hK hσ
  · intro H hHL hHn
    exact le_centralizer_or_le_of_normal_subgroupOf_su6Levi hf hk hK hσ hHL hHn

theorem le_tRadical_of_isKLConfig [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {a : ℕ}
    {N A : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (h : IsKLConfig (stdRepC (apply_apply_eq hK hσ) 0) a N A)
    (hLN : (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤ N) :
    A ≤ (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ
  obtain ⟨-, hLQ, -⟩ := centralizer_stdRep_zero_inf_eq (k := k) hf hk hK hσ
  have hQ2 : IsPGroup 2 ((tRadical σ).subgroupOf C₀) := by
    obtain ⟨-, hT⟩ := even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
    obtain ⟨S, hS⟩ := hT.2.2.2.2.2.2.2.2.2.1
    refine S.isPGroup'.to_le ?_
    rw [hS]
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact mem_inf.2 ⟨parabolicRadical_le_posUnipotent _ (mem_inf.1 hx).1,
      graphFixedRootGroup_le _ _ _ x.2⟩
  refine h.le_of_sup_eq_centralizer hQ2 (centralizer_stdRepC_zero_eq hf hk hK hσ).symm
    (fun x hx => ?_) hLN (forall_normal_isPGroup_eq_bot_of_mulEquiv'
      (subgroupOfEquivOfLe (su6Levi_le_graphFixedRootGroup σ)).symm
      (forall_normal_isPGroup_eq_bot_su6Levi hf hk hK hσ))
  rw [mem_subgroupOf] at hx
  rw [mem_normalizer_iff]
  intro y
  simp only [mem_subgroupOf, coe_mul, coe_inv]
  exact mem_normalizer_iff.1 (hLQ hx) y

end CFSG.SeitzReduction.TwistedE6Pilot
