module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Tags
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieRes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentLift
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.B113Lie CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

  (statedProjectiveSubspaceStabilizer statedProjectiveFlagStabilizer)
open scoped Pointwise

@[expose] noncomputable def pOmegaPlusSubspaces (n : ℕ) (K : Type) [Field K] (hn : 4 ≤ n) :
    Set (Submodule K (Fin n ⊕ Fin n → K)) :=
  {W | (∃ i : ℕ, 1 ≤ i ∧ i ≤ n - 2 ∧ W = OrthogonalSplit.flag n K i) ∨
    W = OrthogonalSplit.flag n K n ∨ W = OrthogonalSplit.Xstar n K (by omega)}

@[expose] noncomputable def lf_stab (n : ℕ) (K : Type) [Field K]
    (W : Submodule K (Fin n ⊕ Fin n → K)) :
    Subgroup ↥(orthElementaryGroup (quadPlus n K)) :=
  (MulAction.stabilizer ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) W).subgroupOf
    (orthElementaryGroup (quadPlus n K))

@[expose] noncomputable def pOmegaPlusParabolics (n : ℕ) (K : Type) [Field K] (hn : 4 ≤ n) :
    Set (Subgroup ↥(orthElementaryGroup (quadPlus n K))) :=
  (fun W => lf_stab n K W) '' pOmegaPlusSubspaces n K hn

@[expose] def POmegaPlusCover : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hn : 4 ≤ n)
    (A : Subgroup ↥(orthElementaryGroup (quadPlus n K))),
    (posUnip n K).subgroupOf (orthElementaryGroup (quadPlus n K)) ≤ A → A ≠ ⊤ →
      ∃ W ∈ pOmegaPlusSubspaces n K hn,
        A ≤ lf_stab n K W

@[expose] def POmegaPlusCharTwo : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hn : 4 ≤ n)
    (W : Submodule K (Fin n ⊕ Fin n → K)), W ∈ pOmegaPlusSubspaces n K hn →
      CharTwo (lf_stab n K W)

@[expose] def POmegaPlusCoatom : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hn : 4 ≤ n)
    (W : Submodule K (Fin n ⊕ Fin n → K)), W ∈ pOmegaPlusSubspaces n K hn →
      lf_stab n K W ⋖ ⊤

theorem lf_map_eq_of_fixes {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {W : Submodule K V} {f : V →ₗ[K] V} (h : ∀ x ∈ W, f x = x) : W.map f = W := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [h x hx]
    exact hx
  · intro x hx
    exact ⟨x, hx, h x hx⟩

theorem lf_mem_stabilizer_iff {n : ℕ} {K : Type} [Field K]
    (g : ↥(orthElementaryGroup (quadPlus n K))) (W : Submodule K (Fin n ⊕ Fin n → K)) :
    g ∈ lf_stab n K W ↔
      W.map (g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)).toLinearMap = W :=
  Iff.rfl

theorem lf_plus_sub_le {n : ℕ} {K : Type} [Field K] (hn : 4 ≤ n)
    {W : Submodule K (Fin n ⊕ Fin n → K)} (hW : W ∈ pOmegaPlusSubspaces n K hn) :
    (posUnip n K).subgroupOf (orthElementaryGroup (quadPlus n K)) ≤
      lf_stab n K W := by
  intro g hg
  have hgU : (g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) ∈ posUnip n K :=
    Subgroup.mem_subgroupOf.1 hg
  have hfix := ((mem_posBorel (r := n) (K := K)).1
    (posUnip_le_posBorel (r := n) (K := K) hgU)).2
  rw [lf_mem_stabilizer_iff]
  rcases hW with ⟨i, -, -, rfl⟩ | rfl | rfl
  · exact hfix i
  · exact hfix n
  · exact map_Xstar_of_mem_posUnip (by omega) hgU

theorem lf_plus_U_ne_bot {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 4 ≤ n) :
    (posUnip n K).subgroupOf (orthElementaryGroup (quadPlus n K)) ≠ ⊥ := by
  intro h
  have hc : Nat.card ((posUnip n K).subgroupOf (orthElementaryGroup (quadPlus n K))) =
      Nat.card (posUnip n K) :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (posUnip_le_orthElementaryGroup (r := n) (K := K))).toEquiv
  rw [h, Subgroup.card_bot, card_posUnip (r := n) (K := K)] at hc
  have h1 : 1 < Nat.card K := Finite.one_lt_card (α := K)
  have hnn : 1 ≤ n * (n - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h3 : Nat.card K ^ 1 ≤ Nat.card K ^ (n * (n - 1)) :=
    Nat.pow_le_pow_right (by omega) hnn
  rw [pow_one] at h3
  omega

theorem lf_plus_flag_ne {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n) :
    lf_stab n K (OrthogonalSplit.flag n K 1) ≠
      lf_stab n K (OrthogonalSplit.flag n K 2) := by
  obtain ⟨a, ha⟩ : ∃ a : Fin n, (a : ℕ) = 2 := ⟨⟨2, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n, (b : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hab : a ≠ b := fun h => by rw [h] at ha; omega
  have hQu : quadPlus n K (Pi.single (Sum.inl a) 1) = 0 := by
    rw [quadPlus_apply]
    simp [Pi.single_apply]
  have hQw : quadPlus n K (Pi.single (Sum.inr b) 1) = 0 := by
    rw [quadPlus_apply]
    simp [Pi.single_apply]
  have hpol : polar (quadPlus n K) (Pi.single (Sum.inl a) 1) (Pi.single (Sum.inr b) 1) = 0 := by
    rw [polar_quadPlus_single_inr n K, Pi.single_apply,
      if_neg (fun h => hab (Sum.inl_injective h).symm)]
  have hfix : ∀ x ∈ OrthogonalSplit.flag n K 1,
      eichler (quadPlus n K) (Pi.single (Sum.inl a) 1) (Pi.single (Sum.inr b) 1) x = x := by
    intro x hx
    obtain ⟨hr, hl⟩ := mem_flag_iff_coord.1 hx
    rw [eichler_apply hQu hpol x, polar_quadPlus_single_inl n K x a,
      polar_quadPlus_single_inr n K x b, hr a, hl b (by omega)]
    simp
  have hcomp : eichler (quadPlus n K) (Pi.single (Sum.inl a) 1) (Pi.single (Sum.inr b) 1)
      (Pi.single (Sum.inl b) 1) = Pi.single (Sum.inl b) 1 - Pi.single (Sum.inl a) 1 := by
    rw [eichler_apply hQu hpol, polar_quadPlus_single_inl n K _ a,
      polar_quadPlus_single_inr n K _ b, hQw]
    simp [Pi.single_apply, hab]
  have hbin : (Pi.single (Sum.inl b) 1 : Fin n ⊕ Fin n → K) ∈ OrthogonalSplit.flag n K 2 := by
    rw [mem_flag_iff_coord]
    refine ⟨fun k => by simp [Pi.single_apply], fun k hk => ?_⟩
    simp only [Pi.single_apply, Sum.inl.injEq]
    rw [if_neg]
    intro h
    subst h
    omega
  have hmem1 : (⟨eichler (quadPlus n K) (Pi.single (Sum.inl a) 1) (Pi.single (Sum.inr b) 1),
      eichler_mem_elementaryGroup (quadPlus n K) _ _⟩ : ↥(orthElementaryGroup (quadPlus n K))) ∈
      lf_stab n K (OrthogonalSplit.flag n K 1) :=
    (lf_mem_stabilizer_iff _ _).2 (lf_map_eq_of_fixes hfix)
  intro heq
  have hmem2 : (⟨eichler (quadPlus n K) (Pi.single (Sum.inl a) 1) (Pi.single (Sum.inr b) 1),
      eichler_mem_elementaryGroup (quadPlus n K) _ _⟩ : ↥(orthElementaryGroup (quadPlus n K))) ∈
      lf_stab n K (OrthogonalSplit.flag n K 2) := by
    rw [← heq]
    exact hmem1
  have hmap2 : (OrthogonalSplit.flag n K 2).map
      (eichler (quadPlus n K) (Pi.single (Sum.inl a) 1) (Pi.single (Sum.inr b) 1) :
        (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) = OrthogonalSplit.flag n K 2 :=
    (lf_mem_stabilizer_iff _ _).1 hmem2
  have hgb : eichler (quadPlus n K) (Pi.single (Sum.inl a) 1) (Pi.single (Sum.inr b) 1)
      (Pi.single (Sum.inl b) 1) ∈ OrthogonalSplit.flag n K 2 := by
    have h := Submodule.mem_map_of_mem (f := (eichler (quadPlus n K) (Pi.single (Sum.inl a) 1)
      (Pi.single (Sum.inr b) 1) : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K))) hbin
    rw [hmap2] at h
    exact h
  have hbad := (mem_flag_iff_coord.1 hgb).2 a (by omega)
  rw [hcomp] at hbad
  simp [Pi.single_apply, hab] at hbad

theorem lf_plus_sylowProps (hcov : POmegaPlusCover) (hchar : POmegaPlusCharTwo)
    (hcoat : POmegaPlusCoatom) {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hn : 4 ≤ n)
    [IsSimpleGroup ↥(orthElementaryGroup (quadPlus n K))] :
    SylowProps ↥(orthElementaryGroup (quadPlus n K)) := by
  haveI : Finite ↥(orthElementaryGroup (quadPlus n K)) := finite_orthElementaryGroup
  obtain ⟨S, hS⟩ := posUnip_isSylow (r := n) (K := K) 2 (by omega)
    (fun a ha => map_flag_top_ne_Xstar (r := n) (K := K) (by omega) ha)
  have hU : IsSylowTwoOf ((posUnip n K).subgroupOf (orthElementaryGroup (quadPlus n K))) ⊤ := by
    have h := CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_top_of_sylow S
    rwa [hS] at h
  have hU1 := lf_plus_U_ne_bot (K := K) hn
  have h1mem : OrthogonalSplit.flag n K 1 ∈ pOmegaPlusSubspaces n K hn :=
    Or.inl ⟨1, le_rfl, by omega, rfl⟩
  have h2mem : OrthogonalSplit.flag n K 2 ∈ pOmegaPlusSubspaces n K hn :=
    Or.inl ⟨2, by norm_num, by omega, rfl⟩
  have hco : ∀ P ∈ pOmegaPlusParabolics n K hn, P ⋖ ⊤ ∧
      (posUnip n K).subgroupOf (orthElementaryGroup (quadPlus n K)) ≤ P := by
    rintro P ⟨W, hW, rfl⟩
    exact ⟨hcoat n K hn W hW, lf_plus_sub_le hn hW⟩
  have hX : pCoreOf 2 (⊤ : Subgroup ↥(orthElementaryGroup (quadPlus n K))) = ⊥ :=
    pCoreOf_top_eq_bot_of_simple hU (lf_plus_sub_le hn h1mem)
      (hcoat n K hn _ h1mem).lt.ne
  have htwo : ∃ P ∈ pOmegaPlusParabolics n K hn, ∃ Q ∈ pOmegaPlusParabolics n K hn, P ≠ Q :=
    ⟨_, Set.mem_image_of_mem _ h1mem, _, Set.mem_image_of_mem _ h2mem,
      lf_plus_flag_ne (K := K) (by omega)⟩
  have hcover : ∀ A : Subgroup ↥(orthElementaryGroup (quadPlus n K)),
      (posUnip n K).subgroupOf (orthElementaryGroup (quadPlus n K)) ≤ A → A ≠ ⊤ →
        ∃ P ∈ pOmegaPlusParabolics n K hn, A ≤ P := by
    intro A hA hAt
    obtain ⟨W, hW, hAW⟩ := hcov n K hn A hA hAt
    exact ⟨_, Set.mem_image_of_mem _ hW, hAW⟩
  have hchar' : ∀ P ∈ pOmegaPlusParabolics n K hn, CharTwo P := by
    rintro P ⟨W, hW, rfl⟩
    exact hchar n K hn W hW
  have hF := (ParabolicData.of_coatoms hU hU1 hX hco htwo hcover hchar').sylowFacts
  have hall : ∀ T : Subgroup ↥(orthElementaryGroup (quadPlus n K)), IsSylowTwoOf T ⊤ →
      SylowFacts ↥(orthElementaryGroup (quadPlus n K)) T :=
    fun T hT => SylowFacts.of_isSylow hF hT
  exact ⟨overgroups_of_forall_sylowFacts hall, oddAut_of_forall_sylowFacts hall⟩

theorem asLieTwoAt_pOmegaPlus_of_gaps (hcov : POmegaPlusCover) (hchar : POmegaPlusCharTwo)
    (hcoat : POmegaPlusCoatom) : AsLieTwoAt .POmegaPlus := by
  intro n f X _ _ hS _ hmod
  obtain ⟨K, hK, hfin, hCh, -, hn, ⟨e⟩⟩ := exists_mulEquiv_elementaryGroup_of_lieModel hmod
  haveI : IsSimpleGroup ↥(orthElementaryGroup (quadPlus n K)) :=
    (MulEquiv.isSimpleGroup_congr e).1 hS
  have hE := lf_plus_sylowProps (K := K) hcov hchar hcoat hn
  exact ⟨Bridge.Over.Overgroups.of_mulEquiv e.symm hE.1,
    Bridge.SylowAutTrivial.of_mulEquiv e hE.2⟩

abbrev lfMinusModel (n : ℕ) (K : Type) [Field K] (b c : K) : Type :=
  StatedProj (StatedOmega (StatedQuadMinus n K b c))

@[expose] noncomputable def pOmegaMinusParabolics (n : ℕ) (K : Type) [Field K] (b c : K) :
    Set (Subgroup (lfMinusModel n K b c)) :=
  Set.range fun i : Fin (n - 1) => statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
    (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i)

theorem lf_mem_minusPs {n : ℕ} {K : Type} [Field K] {b c : K} (i : Fin (n - 1)) :
    statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
      (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i) ∈ pOmegaMinusParabolics n K b c :=
  Set.mem_range_self i

@[expose] def POmegaMinusCover : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K), 4 ≤ n →
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    ∀ S : Sylow 2 (lfMinusModel n K b c),
      statedProjectiveFlagStabilizer (StatedQuadMinus n K b c)
          (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2)) =
        Subgroup.normalizer ((S : Subgroup (lfMinusModel n K b c)) : Set (lfMinusModel n K b c)) →
      ∀ A : Subgroup (lfMinusModel n K b c), (S : Subgroup (lfMinusModel n K b c)) ≤ A →
        A ≠ ⊤ → ∃ i : Fin (n - 1), A ≤ statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
          (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i)

@[expose] def POmegaMinusCharTwo : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K), 4 ≤ n →
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) → ∀ i : Fin (n - 1),
      CharTwo (statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
        (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i))

@[expose] def POmegaMinusCoatom : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K), 4 ≤ n →
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) → ∀ i : Fin (n - 1),
      statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
        (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i) ⋖ ⊤

theorem lf_minus_sylowProps_model (hcov : POmegaMinusCover) (hchar : POmegaMinusCharTwo)
    (hcoat : POmegaMinusCoatom) {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hBI : OrthogonalTail.BorelInterface 2 (StatedQuadMinus n K b c)
      (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2)))
    [IsSimpleGroup (lfMinusModel n K b c)] [Finite (lfMinusModel n K b c)] :
    SylowProps (lfMinusModel n K b c) := by
  obtain ⟨hfl, ⟨S, hSB⟩, -, -, hidx⟩ := hBI
  obtain ⟨i0, hi0⟩ : ∃ i : Fin (n - 1), (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i : Fin (n - 1), (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hlt := hidx _ _ (hfl i1).1 (by rw [(hfl i1).2, hi1]) (hfl i0).1
    (by rw [(hfl i0).2, hi0])
  have hBle : ∀ i : Fin (n - 1),
      statedProjectiveFlagStabilizer (StatedQuadMinus n K b c)
          (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2)) ≤
        statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
          (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i) :=
    fun i => iInf_le _ i
  have hSB' : (S : Subgroup (lfMinusModel n K b c)) ≤
      statedProjectiveFlagStabilizer (StatedQuadMinus n K b c)
        (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2)) := by
    rw [hSB]
    exact Subgroup.le_normalizer
  have hSle : ∀ i : Fin (n - 1), (S : Subgroup (lfMinusModel n K b c)) ≤
      statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
        (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i) :=
    fun i => hSB'.trans (hBle i)
  have hP1 : statedProjectiveSubspaceStabilizer (StatedQuadMinus n K b c)
      (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i1) ≠ ⊤ := by
    intro h
    have h0 := Subgroup.index_ne_zero_of_finite (H := statedProjectiveSubspaceStabilizer
      (StatedQuadMinus n K b c) (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2) i0))
    rw [h, Subgroup.index_top] at hlt
    omega
  have hS_ne_bot : (S : Subgroup (lfMinusModel n K b c)) ≠ ⊥ := by
    intro h
    have hB1 : statedProjectiveFlagStabilizer (StatedQuadMinus n K b c)
        (OrthogonalTail.tailModelFlag (n - 1) K (Fin 2)) = ⊤ := by
      rw [hSB, h]
      exact Subgroup.normalizer_eq_top_iff.2 inferInstance
    have h1 := hBle i1
    rw [hB1] at h1
    exact hP1 (top_le_iff.1 h1)
  have hU : IsSylowTwoOf (S : Subgroup (lfMinusModel n K b c)) ⊤ :=
    CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_top_of_sylow S
  have hX := pCoreOf_top_eq_bot_of_simple hU (hSle i1) hP1
  have hco : ∀ Q ∈ pOmegaMinusParabolics n K b c, Q ⋖ ⊤ ∧ (S : Subgroup (lfMinusModel n K b c)) ≤ Q := by
    intro Q hQ
    obtain ⟨i, rfl⟩ := hQ
    exact ⟨hcoat n K b c hn hirr i, hSle i⟩
  have htwo : ∃ P ∈ pOmegaMinusParabolics n K b c, ∃ Q ∈ pOmegaMinusParabolics n K b c, P ≠ Q :=
    ⟨_, lf_mem_minusPs i0, _, lf_mem_minusPs i1, fun h => hlt.ne (congrArg Subgroup.index h)⟩
  have hcover : ∀ A : Subgroup (lfMinusModel n K b c),
      (S : Subgroup (lfMinusModel n K b c)) ≤ A → A ≠ ⊤ → ∃ P ∈ pOmegaMinusParabolics n K b c, A ≤ P := by
    intro A hA hAt
    obtain ⟨i, hi⟩ := hcov n K b c hn hirr S hSB A hA hAt
    exact ⟨_, lf_mem_minusPs i, hi⟩
  have hchar' : ∀ Q ∈ pOmegaMinusParabolics n K b c, CharTwo Q := by
    intro Q hQ
    obtain ⟨i, rfl⟩ := hQ
    exact hchar n K b c hn hirr i
  have hF := (ParabolicData.of_coatoms hU hS_ne_bot hX hco htwo hcover hchar').sylowFacts
  have hall : ∀ T : Subgroup (lfMinusModel n K b c), IsSylowTwoOf T ⊤ →
      SylowFacts (lfMinusModel n K b c) T :=
    fun T hT => SylowFacts.of_isSylow hF hT
  exact ⟨overgroups_of_forall_sylowFacts hall, oddAut_of_forall_sylowFacts hall⟩

theorem asLieTwoAt_pOmegaMinus_of_gaps (hcov : POmegaMinusCover) (hchar : POmegaMinusCharTwo)
    (hcoat : POmegaMinusCoatom) : AsLieTwoAt .POmegaMinus := by
  intro n f X _ _ hS _ hmod
  have hmc : StatedClassicalModel X .POmegaMinus n 2 f := hmod.statedClassicalModel (by decide)
  have hBI := OrthogonalTail.orthogonal_geometry_tail_model_Borel_overgroup_interface X
    .POmegaMinus (Or.inr rfl) n 2 f hmc
  obtain ⟨⟨-, -, hn⟩, K, hK, hfin, hcard, b, c, hirr, ⟨e⟩⟩ := hmc
  have hB := hBI K hcard b c hirr
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  haveI : IsSimpleGroup (lfMinusModel n K b c) := (MulEquiv.isSimpleGroup_congr e).1 hS
  haveI : Finite (lfMinusModel n K b c) := Finite.of_surjective e e.surjective
  have hM := lf_minus_sylowProps_model hcov hchar hcoat hn hirr hB
  exact ⟨Bridge.Over.Overgroups.of_mulEquiv e.symm hM.1,
    Bridge.SylowAutTrivial.of_mulEquiv e hM.2⟩

end CFSG.Quasithin.LieOver
