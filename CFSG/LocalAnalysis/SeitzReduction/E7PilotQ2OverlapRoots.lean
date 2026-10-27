module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2SwapMain

public section

namespace CFSG.SeitzReduction.E7Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD toStdD rootsD_eq boolSign)
open CFSG.LieType.RootSystem (roots weylAction coxeterMatrix reflection reflection_apply
  weylAction_simple weylAction_mul_apply)
open E7Neighbour

local instance e7PilotQ2OverlapRootsNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def d6HighRoot : Fin (Tag.rank .E7) → ℤ := ![0, 1, 1, 2, 2, 2, 1]

theorem thirdRoot_high_seven : E7Neighbour.thirdRoot .high .seven = d6HighRoot := rfl

theorem iform_d6HighRoot_single_check : ∀ j : Fin (Tag.rank .E7),
    iform d6HighRoot (Pi.single j 1) = (if j = 5 then 1 else 0) - (if j = 0 then 1 else 0) := by
  decide +kernel

theorem iform_d6HighRoot (v : Fin (Tag.rank .E7) → ℤ) : iform d6HighRoot v = v 5 - v 0 := by
  rw [F4Pilot.iform_eq_sum_mul_iform_single]
  simp only [iform_d6HighRoot_single_check, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem iform_d6HighRoot_self : iform d6HighRoot d6HighRoot = 2 := by
  rw [iform_d6HighRoot]
  rfl

theorem corootPair_d6HighRoot (v : Fin (Tag.rank .E7) → ℤ) :
    corootPair d6HighRoot v = v 5 - v 0 := by
  rw [corootPair, iform_d6HighRoot, iform_d6HighRoot_self]
  omega

theorem isRoot_d6HighRoot : IsRoot .E7 d6HighRoot :=
  mem_rootFinset.1 (by decide +kernel)

theorem height_d6HighRoot_pos : 0 < height d6HighRoot := by decide

theorem iform_highRoot_d6HighRoot : iform (highRoot .E7) d6HighRoot = 0 := by decide +kernel

theorem iform_highRoot_E7 (v : Fin (Tag.rank .E7) → ℤ) : iform (highRoot .E7) v = v 0 :=
  EPilot.iform_highRoot (Or.inr (Or.inl rfl)) v

set_option maxRecDepth 100000 in
theorem not_mem_rootFinset_add_d6HighRoot_check :
    ∀ α ∈ rootFinset .E7, α 0 = 0 → 0 < height α → α + d6HighRoot ∉ rootFinset .E7 := by
  decide +kernel

theorem not_isRoot_add_d6HighRoot {α : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (h0 : α 0 = 0) (hpos : 0 < height α) :
    ¬ IsRoot .E7 (α + d6HighRoot) := fun h =>
  not_mem_rootFinset_add_d6HighRoot_check α (mem_rootFinset.2 hα) h0 hpos (mem_rootFinset.2 h)

@[expose] def overlapNodes : Set (Fin (Tag.rank .E7)) := {j | j ≠ 0 ∧ j ≠ 5}

theorem zero_not_mem_overlapNodes : (0 : Fin (Tag.rank .E7)) ∉ overlapNodes :=
  fun h => h.1 rfl

theorem five_not_mem_overlapNodes : (5 : Fin (Tag.rank .E7)) ∉ overlapNodes :=
  fun h => h.2 rfl

theorem eq_zero_or_eq_five_of_not_mem_overlapNodes {i : Fin (Tag.rank .E7)}
    (hi : i ∉ overlapNodes) : i = 0 ∨ i = 5 := by
  by_contra h
  exact hi ⟨fun h0 => h (Or.inl h0), fun h5 => h (Or.inr h5)⟩

theorem mem_parabolicRoots_overlapNodes {α : Fin (Tag.rank .E7) → ℤ} :
    α ∈ parabolicRoots .E7 overlapNodes ↔ IsRoot .E7 α ∧ α 0 = 0 ∧ α 5 = 0 := by
  constructor
  · rintro ⟨hα, h⟩
    exact ⟨hα, h 0 zero_not_mem_overlapNodes, h 5 five_not_mem_overlapNodes⟩
  · rintro ⟨hα, h0, h5⟩
    refine ⟨hα, fun i hi => ?_⟩
    rcases eq_zero_or_eq_five_of_not_mem_overlapNodes hi with rfl | rfl
    exacts [h0, h5]

theorem parabolicRoots_overlapNodes :
    parabolicRoots .E7 overlapNodes = orthRoots (highRoot .E7) ∩ orthRoots d6HighRoot := by
  ext α
  rw [mem_parabolicRoots_overlapNodes]
  simp only [Set.mem_inter_iff, orthRoots, Set.mem_ofPred_eq, iform_highRoot_E7,
    iform_d6HighRoot]
  constructor
  · rintro ⟨hα, h0, h5⟩
    exact ⟨⟨hα, h0⟩, hα, by omega⟩
  · rintro ⟨⟨hα, h0⟩, -, h5⟩
    exact ⟨hα, h0, by omega⟩

theorem iform_highRoot_of_mem_parabolicRoots_overlapNodes {α : Fin (Tag.rank .E7) → ℤ}
    (hα : α ∈ parabolicRoots .E7 overlapNodes) : iform (highRoot .E7) α = 0 := by
  rw [parabolicRoots_overlapNodes] at hα
  exact hα.1.2

theorem iform_d6HighRoot_of_mem_parabolicRoots_overlapNodes {α : Fin (Tag.rank .E7) → ℤ}
    (hα : α ∈ parabolicRoots .E7 overlapNodes) : iform d6HighRoot α = 0 := by
  rw [parabolicRoots_overlapNodes] at hα
  exact hα.2.2

@[expose] def d4NodeE7 (i : Fin 4) : Fin (Tag.rank .E7) := (![1, 3, 2, 4] : Fin 4 → Fin 7) i

@[expose] def d4EmbedE7 (v : Fin 4 → ℤ) : Fin (Tag.rank .E7) → ℤ :=
  (![0, v 0, v 2, v 1, v 3, 0, 0] : Fin 7 → ℤ)

@[expose] def e7RestrictD4 (γ : Fin (Tag.rank .E7) → ℤ) : Fin 4 → ℤ := fun i => γ (d4NodeE7 i)

theorem d4EmbedE7_d4NodeE7 (v : Fin 4 → ℤ) (i : Fin 4) : d4EmbedE7 v (d4NodeE7 i) = v i := by
  fin_cases i <;> rfl

theorem d4EmbedE7_zero_apply (v : Fin 4 → ℤ) : d4EmbedE7 v 0 = 0 := rfl

theorem d4EmbedE7_five_apply (v : Fin 4 → ℤ) : d4EmbedE7 v 5 = 0 := rfl

theorem d4EmbedE7_six_apply (v : Fin 4 → ℤ) : d4EmbedE7 v 6 = 0 := rfl

theorem eq_d4NodeE7_or : ∀ j : Fin (Tag.rank .E7), j = 0 ∨ j = 5 ∨ j = 6 ∨ ∃ i, j = d4NodeE7 i := by
  decide

theorem ext_d4NodeE7 {γ δ : Fin (Tag.rank .E7) → ℤ} (h : ∀ i, γ (d4NodeE7 i) = δ (d4NodeE7 i))
    (h0 : γ 0 = δ 0) (h5 : γ 5 = δ 5) (h6 : γ 6 = δ 6) : γ = δ := by
  funext j
  rcases eq_d4NodeE7_or j with rfl | rfl | rfl | ⟨i, rfl⟩
  exacts [h0, h5, h6, h i]

theorem e7RestrictD4_d4EmbedE7 (v : Fin 4 → ℤ) : e7RestrictD4 (d4EmbedE7 v) = v :=
  funext (d4EmbedE7_d4NodeE7 v)

theorem d4EmbedE7_e7RestrictD4 {γ : Fin (Tag.rank .E7) → ℤ} (h0 : γ 0 = 0) (h5 : γ 5 = 0)
    (h6 : γ 6 = 0) : d4EmbedE7 (e7RestrictD4 γ) = γ :=
  ext_d4NodeE7 (fun i => d4EmbedE7_d4NodeE7 _ i) (by rw [d4EmbedE7_zero_apply, h0])
    (by rw [d4EmbedE7_five_apply, h5]) (by rw [d4EmbedE7_six_apply, h6])

theorem d4EmbedE7_injective : Function.Injective d4EmbedE7 := fun v w h => by
  rw [← e7RestrictD4_d4EmbedE7 v, h, e7RestrictD4_d4EmbedE7]

theorem d4EmbedE7_add (v w : Fin 4 → ℤ) : d4EmbedE7 (v + w) = d4EmbedE7 v + d4EmbedE7 w :=
  ext_d4NodeE7 (fun i => by simp only [d4EmbedE7_d4NodeE7, Pi.add_apply])
    (by simp only [Pi.add_apply, d4EmbedE7_zero_apply, add_zero])
    (by simp only [Pi.add_apply, d4EmbedE7_five_apply, add_zero])
    (by simp only [Pi.add_apply, d4EmbedE7_six_apply, add_zero])

theorem d4EmbedE7_neg (v : Fin 4 → ℤ) : d4EmbedE7 (-v) = -d4EmbedE7 v :=
  ext_d4NodeE7 (fun i => by simp only [d4EmbedE7_d4NodeE7, Pi.neg_apply])
    (by simp only [Pi.neg_apply, d4EmbedE7_zero_apply, neg_zero])
    (by simp only [Pi.neg_apply, d4EmbedE7_five_apply, neg_zero])
    (by simp only [Pi.neg_apply, d4EmbedE7_six_apply, neg_zero])

theorem d4EmbedE7_sub (v w : Fin 4 → ℤ) : d4EmbedE7 (v - w) = d4EmbedE7 v - d4EmbedE7 w := by
  rw [sub_eq_add_neg, d4EmbedE7_add, d4EmbedE7_neg, ← sub_eq_add_neg]

theorem d4EmbedE7_smul (n : ℤ) (v : Fin 4 → ℤ) : d4EmbedE7 (n • v) = n • d4EmbedE7 v :=
  ext_d4NodeE7 (fun i => by simp only [d4EmbedE7_d4NodeE7, Pi.smul_apply])
    (by simp only [Pi.smul_apply, d4EmbedE7_zero_apply, smul_zero])
    (by simp only [Pi.smul_apply, d4EmbedE7_five_apply, smul_zero])
    (by simp only [Pi.smul_apply, d4EmbedE7_six_apply, smul_zero])

theorem d4EmbedE7_zero : d4EmbedE7 0 = 0 :=
  ext_d4NodeE7 (fun i => by simp only [d4EmbedE7_d4NodeE7, Pi.zero_apply])
    (by simp only [Pi.zero_apply, d4EmbedE7_zero_apply])
    (by simp only [Pi.zero_apply, d4EmbedE7_five_apply])
    (by simp only [Pi.zero_apply, d4EmbedE7_six_apply])

theorem d4EmbedE7_single_check :
    ∀ i : Fin 4, d4EmbedE7 (Pi.single i 1) = Pi.single (d4NodeE7 i) 1 := by
  decide

theorem d4EmbedE7_single (i : Fin 4) : d4EmbedE7 (Pi.single i 1) = Pi.single (d4NodeE7 i) 1 :=
  d4EmbedE7_single_check i

theorem cartan_E7_d4NodeE7_check : ∀ p : Fin 4 × Fin 4,
    Tag.cartan .E7 (d4NodeE7 p.1) (d4NodeE7 p.2) = cartanD 4 p.1 p.2 := by
  decide

theorem sum_cartan_E7_mul_d4EmbedE7 (i : Fin 4) (v : Fin 4 → ℤ) :
    ∑ j, Tag.cartan .E7 (d4NodeE7 i) j * d4EmbedE7 v j = ∑ j, cartanD 4 i j * v j := by
  have h := fun j => cartan_E7_d4NodeE7_check (i, j)
  change (∑ j : Fin 7, Tag.cartan .E7 (d4NodeE7 i) j * d4EmbedE7 v j) = _
  rw [Fin.sum_univ_seven, Fin.sum_univ_four, ← h 0, ← h 1, ← h 2, ← h 3]
  change Tag.cartan .E7 (d4NodeE7 i) 0 * 0 + Tag.cartan .E7 (d4NodeE7 i) 1 * v 0 +
      Tag.cartan .E7 (d4NodeE7 i) 2 * v 2 + Tag.cartan .E7 (d4NodeE7 i) 3 * v 1 +
      Tag.cartan .E7 (d4NodeE7 i) 4 * v 3 + Tag.cartan .E7 (d4NodeE7 i) 5 * 0 +
      Tag.cartan .E7 (d4NodeE7 i) 6 * 0 =
    Tag.cartan .E7 (d4NodeE7 i) 1 * v 0 + Tag.cartan .E7 (d4NodeE7 i) 3 * v 1 +
      Tag.cartan .E7 (d4NodeE7 i) 2 * v 2 + Tag.cartan .E7 (d4NodeE7 i) 4 * v 3
  ring

theorem d4EmbedE7_reflection (i : Fin 4) (v : Fin 4 → ℤ) :
    d4EmbedE7 (reflection (cartanD 4) i v) = reflect .E7 (d4NodeE7 i) (d4EmbedE7 v) := by
  rw [reflection_apply, reflect, d4EmbedE7_sub, d4EmbedE7_smul, d4EmbedE7_single,
    sum_cartan_E7_mul_d4EmbedE7]

theorem isRoot_d4EmbedE7 {v : Fin 4 → ℤ} (hv : v ∈ roots (isFiniteType_cartanD 4) ∅) :
    IsRoot .E7 (d4EmbedE7 v) := by
  rcases hv with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
  · obtain ⟨ω, rfl⟩ :=
      (coxeterMatrix (isFiniteType_cartanD 4)).toCoxeterSystem.wordProd_surjective w
    induction ω with
    | nil =>
      rw [CoxeterSystem.wordProd_nil, map_one, Module.End.one_apply, d4EmbedE7_single]
      exact IsRoot.basis _
    | cons j ω ih =>
      rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple,
        d4EmbedE7_reflection]
      exact IsRoot.reflect _ ih
  · exact absurd hi (Set.notMem_empty i)

set_option maxRecDepth 100000 in
theorem d4RootsCheckE7 :
    ∀ γ ∈ rootFinset .E7, γ 0 = 0 → γ 5 = 0 → γ 6 = 0 → ∃ i j : Fin 4, i ≠ j ∧ ∃ s t : Bool,
      toStdD 4 (e7RestrictD4 γ) = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
  decide +kernel

theorem mem_rootsD_e7RestrictD4 {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : IsRoot .E7 γ) (h0 : γ 0 = 0) (h5 : γ 5 = 0) (h6 : γ 6 = 0) :
    e7RestrictD4 γ ∈ roots (isFiniteType_cartanD 4) ∅ := by
  obtain ⟨i, j, hij, s, t, h⟩ := d4RootsCheckE7 γ (mem_rootFinset.2 hγ) h0 h5 h6
  rw [rootsD_eq (n := 4) (by norm_num)]
  exact ⟨i, j, boolSign s, boolSign t, hij,
    CFSG.LieType.Universal.Spin.boolSign_eq_one_or_eq_neg_one s,
    CFSG.LieType.Universal.Spin.boolSign_eq_one_or_eq_neg_one t, h⟩

theorem isRoot_d4EmbedE7_iff {v : Fin 4 → ℤ} :
    IsRoot .E7 (d4EmbedE7 v) ↔ v ∈ roots (isFiniteType_cartanD 4) ∅ := by
  refine ⟨fun h => ?_, isRoot_d4EmbedE7⟩
  have := mem_rootsD_e7RestrictD4 h (d4EmbedE7_zero_apply v) (d4EmbedE7_five_apply v)
    (d4EmbedE7_six_apply v)
  rwa [e7RestrictD4_d4EmbedE7] at this

theorem add_self_not_mem_rootsD4_E7
    {α : Fin 4 → ℤ} : α + α ∉ roots (isFiniteType_cartanD 4) ∅ := fun h => by
  have h1 := isRoot_d4EmbedE7 h
  rw [d4EmbedE7_add] at h1
  exact not_isRoot_add_self_E7' h1

theorem iform_single_six (γ : Fin (Tag.rank .E7) → ℤ) :
    iform (Pi.single 6 1) γ = 2 * γ 6 - γ 5 := by
  rw [F4Pilot.iform_eq_sum_mul_iform_single]
  have h : ∀ j : Fin (Tag.rank .E7), iform (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ)
      (Pi.single j 1) = (if j = 6 then 2 else 0) - (if j = 5 then 1 else 0) := by
    decide +kernel
  simp only [h, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, mul_one]
  ring

theorem overlapRootsD4_high_seven_eq_image :
    overlapRootsD4 .high .seven = d4EmbedE7 '' roots (isFiniteType_cartanD 4) ∅ := by
  ext γ
  simp only [overlapRootsD4, Set.mem_inter_iff, orthRoots, Set.mem_ofPred_eq, root,
    thirdRoot_high_seven, iform_highRoot_E7, iform_d6HighRoot, iform_single_six]
  constructor
  · rintro ⟨⟨⟨hγ, h0⟩, -, h6⟩, -, h5⟩
    have h5' : γ 5 = 0 := by omega
    have h6' : γ 6 = 0 := by omega
    exact ⟨e7RestrictD4 γ, mem_rootsD_e7RestrictD4 hγ h0 h5' h6',
      d4EmbedE7_e7RestrictD4 h0 h5' h6'⟩
  · rintro ⟨v, hv, rfl⟩
    have hγ := isRoot_d4EmbedE7 hv
    exact ⟨⟨⟨hγ, rfl⟩, hγ, rfl⟩, hγ, rfl⟩

@[expose] def overlapWord : E7Neighbour → E7Neighbour → List (Fin (Tag.rank .E7))
  | high, seven => [5, 4, 3, 2, 1, 3, 4, 5]
  | seven, high => [5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]
  | high, four => [4, 5, 6, 2, 1, 3, 4, 5]
  | four, high => [4, 5, 6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]
  | seven, four => [5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 2, 0]
  | four, seven => [5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 0]
  | _, _ => []

noncomputable abbrev overlapWeyl (N N' : E7Neighbour) : WeylGroup .E7 :=
  (coxeterSystem .E7).wordProd (overlapWord N N')

theorem overlapWeyl_smul {N N' : E7Neighbour} (h : N ≠ N') :
    overlapWeyl N N' • highRoot .E7 = N.root ∧ overlapWeyl N N' • d6HighRoot = N'.root ∧
      overlapWeyl N N' • (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ) = N.thirdRoot N' := by
  cases N <;> cases N' <;> first | exact absurd rfl h | skip
  all_goals
    simp only [overlapWeyl, overlapWord, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil,
      mul_one, mul_smul, simple_smul]
    refine ⟨?_, ?_, ?_⟩ <;> exact List.ofFn_injective (by decide +kernel)

theorem image_smul_orthRoots_inter_E7
    (w : WeylGroup .E7) (a b : Fin (Tag.rank .E7) → ℤ) :
    (fun α => w • α) '' (orthRoots a ∩ orthRoots b) = orthRoots (w • a) ∩ orthRoots (w • b) := by
  rw [Set.image_inter (MulAction.injective w), image_smul_orthRoots, image_smul_orthRoots]

theorem image_overlapWeyl_parabolicRoots
    {N N' : E7Neighbour} (h : N ≠ N') :
    (fun α => overlapWeyl N N' • α) '' parabolicRoots .E7 overlapNodes =
      orthRoots N.root ∩ orthRoots N'.root := by
  rw [parabolicRoots_overlapNodes, image_smul_orthRoots_inter_E7, (overlapWeyl_smul h).1,
    (overlapWeyl_smul h).2.1]

theorem isRoot_thirdRoot {N N' : E7Neighbour} (h : N ≠ N') :
    IsRoot .E7 (N.thirdRoot N') := by
  rw [← (overlapWeyl_smul h).2.2]
  exact IsRoot.smul (isRoot_single _ 6) _

set_option maxRecDepth 100000 in
theorem orthRoots_inter_check_high_seven : ∀ γ ∈ rootFinset .E7,
    iform (highRoot .E7) γ = 0 → iform (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ) γ = 0 →
      γ = thirdRoot .high .seven ∨ γ = -thirdRoot .high .seven ∨
        iform (thirdRoot .high .seven) γ = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem orthRoots_inter_check_high_four : ∀ γ ∈ rootFinset .E7,
    iform (highRoot .E7) γ = 0 → iform (Pi.single 3 1 : Fin (Tag.rank .E7) → ℤ) γ = 0 →
      γ = thirdRoot .high .four ∨ γ = -thirdRoot .high .four ∨
        iform (thirdRoot .high .four) γ = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem orthRoots_inter_check_seven_four : ∀ γ ∈ rootFinset .E7,
    iform (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ) γ = 0 →
      iform (Pi.single 3 1 : Fin (Tag.rank .E7) → ℤ) γ = 0 →
      γ = thirdRoot .seven .four ∨ γ = -thirdRoot .seven .four ∨
        iform (thirdRoot .seven .four) γ = 0 := by
  decide +kernel

theorem orthRoots_inter_check {N N' : E7Neighbour} (h : N ≠ N')
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (h1 : iform N.root γ = 0)
    (h2 : iform N'.root γ = 0) :
    γ = N.thirdRoot N' ∨ γ = -N.thirdRoot N' ∨ iform (N.thirdRoot N') γ = 0 := by
  have hm := mem_rootFinset.2 hγ
  cases N <;> cases N' <;> first | exact absurd rfl h | skip
  · exact orthRoots_inter_check_high_seven γ hm h1 h2
  · exact orthRoots_inter_check_high_four γ hm h1 h2
  · exact orthRoots_inter_check_high_seven γ hm h2 h1
  · exact orthRoots_inter_check_seven_four γ hm h1 h2
  · exact orthRoots_inter_check_high_four γ hm h2 h1
  · exact orthRoots_inter_check_seven_four γ hm h2 h1

theorem iform_root_thirdRoot {N N' : E7Neighbour} (h : N ≠ N') :
    iform N.root (N.thirdRoot N') = 0 ∧ iform N'.root (N.thirdRoot N') = 0 := by
  cases N <;> cases N' <;> first | exact absurd rfl h | exact ⟨by decide +kernel, by decide +kernel⟩

theorem mem_orthRoots_inter {N N' : E7Neighbour} (h : N ≠ N')
    {γ : Fin (Tag.rank .E7) → ℤ} :
    γ ∈ orthRoots N.root ∩ orthRoots N'.root ↔
      γ = N.thirdRoot N' ∨ γ = -N.thirdRoot N' ∨ γ ∈ overlapRootsD4 N N' := by
  obtain ⟨h1, h2⟩ := iform_root_thirdRoot h
  have hr := isRoot_thirdRoot h
  constructor
  · rintro ⟨⟨hγ, hγ1⟩, -, hγ2⟩
    rcases orthRoots_inter_check h hγ hγ1 hγ2 with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr ⟨⟨⟨hγ, hγ1⟩, hγ, hγ2⟩, hγ, e⟩)
  · rintro (rfl | rfl | hγ)
    · exact ⟨⟨hr, h1⟩, hr, h2⟩
    · exact ⟨neg_mem_orthRoots ⟨hr, h1⟩, neg_mem_orthRoots ⟨hr, h2⟩⟩
    · exact hγ.1

end CFSG.SeitzReduction.E7Pilot
