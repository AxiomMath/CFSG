module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerTBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6Y
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotClasses

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono map_perfectCore
  le_perfectCore_of_perfect perfectCore_eq_self_of_perfect)

local instance twistedE6PilotCentralizerTNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section Simple

theorem forall_normal_isPGroup_eq_bot_of_isPerfect {M : Type*} [Group M] [Finite M]
    [IsSimpleGroup M] [Group.IsPerfect M] (N : Subgroup M) (hN : N.Normal)
    (hp : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    rw [h] at hp
    have hM : IsPGroup 2 M := hp.of_equiv Subgroup.topEquiv
    exact Group.IsPerfect.not_isNilpotent M hM.isNilpotent

end Simple

section Defs

variable {K : Type} [Field K]

@[expose] noncomputable def tRadical (σ : K →+* K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  parabolicRadical TwistTag.E6.tag K E6GraphLevi.setA ⊓ graphFixedRootGroup TwistTag.E6 K σ

theorem tRadical_le_C0 (σ : K →+* K) : tRadical σ ≤ graphFixedRootGroup TwistTag.E6 K σ :=
  inf_le_right

end Defs



section Centralizer

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem centralizer_pinnedX_highRoot_inf_eq (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    centralizer ({pinnedX TwistTag.E6.tag K e6HighestRoot 1} : Set (ModGL TwistTag.E6.tag K)) ⊓
        graphFixedRootGroup TwistTag.E6 K σ =
      centralizer (E6GraphLevi.thetaRootGroup (algebraMap k K) :
        Set (ModGL TwistTag.E6.tag K)) ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
  have hK2 : (2 : K) = 0 := E6GraphLevi.two_eq_zero_of_card_sq hf hK
  have hX1 : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈
      E6GraphLevi.thetaRootGroup (algebraMap k K) :=
    (E6GraphLevi.mem_thetaRootGroup (algebraMap k K)).2 ⟨1, by rw [map_one]⟩
  refine le_antisymm (fun g hg => ?_) (inf_le_inf_right _ (centralizer_le
    (Set.singleton_subset_iff.2 (SetLike.mem_coe.2 hX1))))
  obtain ⟨hgC, hgG⟩ := mem_inf.1 hg
  have hgc : g * pinnedX TwistTag.E6.tag K e6HighestRoot 1 =
      pinnedX TwistTag.E6.tag K e6HighestRoot 1 * g := mem_centralizer_singleton_iff.1 hgC
  obtain ⟨-, hT⟩ := even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
  obtain ⟨hN, -, -, hfac, -, hC, -, -, -, -, -, -⟩ := hT
  have hgA : g ∈ adjointGroup TwistTag.E6.tag K := (graphFixedRootGroup_le _ _ _ hgG).1
  have hgP : g ∈ parabolicSubgroup TwistTag.E6.tag K E6GraphLevi.setA :=
    E6GraphHighestRootNormalizer.mem_parabolicSubgroup_of_conj hK2 hgA
      (c := 1) (by rw [hgc, mul_inv_cancel_right])
  have hgN : g ∈ normalizer (E6GraphLevi.thetaRootGroup (algebraMap k K) :
      Set (ModGL TwistTag.E6.tag K)) ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
    rw [hN]
    exact mem_inf.2 ⟨hgP, hgG⟩
  obtain ⟨⟨q, l, h⟩, ⟨hq, hl, hh, rfl⟩, -⟩ := hfac g hgN
  have hQL : (parabolicRadical TwistTag.E6.tag K E6GraphLevi.setA ⊓
      graphFixedRootGroup TwistTag.E6 K σ) ⊔ (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
        graphFixedRootGroup TwistTag.E6 K σ) ≤ centralizer
          (E6GraphLevi.thetaRootGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) := by
    rw [← hC]
    exact inf_le_left
  have hqC := hQL (mem_sup_left hq)
  have hlC := hQL (mem_sup_right hl)
  have hqX := mem_centralizer_iff.1 hqC _ hX1
  have hlX := mem_centralizer_iff.1 hlC _ hX1
  have hhX : h * pinnedX TwistTag.E6.tag K e6HighestRoot 1 =
      pinnedX TwistTag.E6.tag K e6HighestRoot 1 * h := by
    have e : h = l⁻¹ * q⁻¹ * (q * (l * h)) := by group
    have e1 : q * pinnedX TwistTag.E6.tag K e6HighestRoot 1 =
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 * q := hqX.symm
    have e2 : l * pinnedX TwistTag.E6.tag K e6HighestRoot 1 =
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 * l := hlX.symm
    calc h * pinnedX TwistTag.E6.tag K e6HighestRoot 1
        = l⁻¹ * q⁻¹ * ((q * (l * h)) * pinnedX TwistTag.E6.tag K e6HighestRoot 1) := by
          rw [← mul_assoc (l⁻¹ * q⁻¹), ← e]
      _ = l⁻¹ * q⁻¹ * (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * (q * (l * h))) := by
          rw [hgc]
      _ = l⁻¹ * (q⁻¹ * pinnedX TwistTag.E6.tag K e6HighestRoot 1 * q) * (l * h) := by group
      _ = l⁻¹ * pinnedX TwistTag.E6.tag K e6HighestRoot 1 * (l * h) := by
          rw [mul_assoc q⁻¹, ← e1]; group
      _ = pinnedX TwistTag.E6.tag K e6HighestRoot 1 * h := by
          rw [mul_assoc l⁻¹, ← mul_assoc _ l h, ← e2]; group
  obtain ⟨a, rfl⟩ := hh
  have h3 := E6GraphLevi.rootTorusSL2_conj_pinnedX_map hK2 (algebraMap k K) a 1
  rw [← E6GraphLevi.thetaTorusHom_apply] at h3
  rw [MonoidHom.comp_apply] at hhX
  have h4 : pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K ((a : k) ^ 2 * 1)) =
      pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1) := by
    rw [← h3, map_one, hhX, mul_inv_cancel_right]
  have h5 := (algebraMap k K).injective
    (pinnedX_injective (τ := TwistTag.E6.tag) (R := K) e6HighestRoot h4)
  have hk2 : (2 : k) = 0 := (algebraMap k K).injective (by rw [map_ofNat, map_zero]; exact hK2)
  have ha : a = 1 := Units.ext (eq_one_of_mul_self_eq_one_of_two_eq_zero hk2
    (by rw [← sq]; simpa using h5))
  rw [ha, map_one, mul_one]
  rw [hC]
  exact mul_mem (mem_sup_left hq) (mem_sup_right hl)

end Centralizer

section Levi

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem isPerfect_su6Levi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) : Group.IsPerfect (su6Levi σ) := by
  obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := (su6Levi_facts (k := k) hf hk hK hσ).2.2.2.2.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect (StatedSU 6 (2 ^ f) K') :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK' (by norm_num) (by simp)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem commutator_su6Levi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) : ⁅su6Levi σ, su6Levi σ⁆ = su6Levi σ :=
  Subgroup.isPerfect_iff.1 (isPerfect_su6Levi hf hk hK hσ)

theorem isSimpleGroup_su6Levi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsSimpleGroup (su6Levi σ) :=
  (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 6 2 f
    (su6Levi_facts (k := k) hf hk hK hσ).2.2.2.2.2.1).2

theorem forall_normal_isPGroup_eq_bot_su6Levi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (N : Subgroup (su6Levi σ)) (hN : N.Normal) (hp : IsPGroup 2 N) : N = ⊥ := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have := isSimpleGroup_su6Levi hf hk hK hσ
  have := isPerfect_su6Levi hf hk hK hσ
  exact forall_normal_isPGroup_eq_bot_of_isPerfect N hN hp

end Levi

section Structure

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem centralizer_stdRep_zero_inf_eq (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    centralizer ({stdRep K 0} : Set (ModGL TwistTag.E6.tag K)) ⊓
        graphFixedRootGroup TwistTag.E6 K σ = tRadical σ ⊔ su6Levi σ ∧
      su6Levi σ ≤ normalizer (tRadical σ : Set (ModGL TwistTag.E6.tag K)) ∧
      tRadical σ ⊓ su6Levi σ = ⊥ := by
  obtain ⟨-, hT⟩ := even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
  obtain ⟨-, -, -, -, -, hC, hQn, hQL, -, -, -, -⟩ := hT
  have h1 : centralizer ({stdRep K 0} : Set (ModGL TwistTag.E6.tag K)) ⊓
      graphFixedRootGroup TwistTag.E6 K σ = tRadical σ ⊔ su6Levi σ := by
    rw [show stdRep K 0 = pinnedX TwistTag.E6.tag K e6HighestRoot 1 from rfl,
      centralizer_pinnedX_highRoot_inf_eq (k := k) hf hk hK hσ, hC]
    rfl
  refine ⟨h1, ?_, hQL⟩
  have hn := (normal_subgroupOf_iff_le_normalizer (le_sup_left :
    tRadical σ ≤ tRadical σ ⊔ su6Levi σ)).1 hQn
  exact le_sup_right.trans hn

@[expose] noncomputable def stdRepC [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c)
    (κ : Fin 2) : graphFixedRootGroup TwistTag.E6 K σ :=
  ⟨stdRep K κ, stdRep_mem_C0 hσσ κ⟩

theorem centralizer_stdRepC_zero_eq [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) =
      (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ⊔
        (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  rw [centralizer_subtype_eq, ← subgroupOf_sup (tRadical_le_C0 σ)
    (su6Levi_le_graphFixedRootGroup σ), ← (centralizer_stdRep_zero_inf_eq (k := k) hf hk hK hσ).1,
    ← inf_subgroupOf_right]
  rfl

end Structure

section F3

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem isCoreLeviDecomp_stdRepC_zero [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsCoreLeviDecomp (centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)))
      (perfectCore (centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))) ⊓
          (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ
  obtain ⟨-, hLN, hQL⟩ := centralizer_stdRep_zero_inf_eq (k := k) hf hk hK hσ
  have hC := centralizer_stdRepC_zero_eq (k := k) hf hk hK hσ
  have hLC : su6Levi σ ≤ C₀ := su6Levi_le_graphFixedRootGroup σ
  have hQC : tRadical σ ≤ C₀ := tRadical_le_C0 σ
  have hperf : ⁅(su6Levi σ).subgroupOf C₀, (su6Levi σ).subgroupOf C₀⁆ =
      (su6Levi σ).subgroupOf C₀ := by
    apply map_injective C₀.subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hLC,
      commutator_su6Levi hf hk hK hσ]
  have hQ2 : IsPGroup 2 ((tRadical σ).subgroupOf C₀) := by
    obtain ⟨-, hT⟩ := even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
    obtain ⟨S, hS⟩ := hT.2.2.2.2.2.2.2.2.2.1
    refine S.isPGroup'.to_le ?_
    rw [hS]
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact mem_inf.2 ⟨parabolicRadical_le_posUnipotent _ (mem_inf.1 hx).1,
      graphFixedRootGroup_le _ _ _ x.2⟩
  have hLN' : (su6Levi σ).subgroupOf C₀ ≤ normalizer ((tRadical σ).subgroupOf C₀ : Set C₀) := by
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.1 (hLN hx) y
  have hdisj : Disjoint ((tRadical σ).subgroupOf C₀) ((su6Levi σ).subgroupOf C₀) := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := mem_inf.1 hx
    rw [mem_subgroupOf] at h1 h2
    have hx' : (x : ModGL TwistTag.E6.tag K) ∈ tRadical σ ⊓ su6Levi σ := mem_inf.2 ⟨h1, h2⟩
    rw [hQL, mem_bot] at hx'
    exact (mem_bot).2 (Subtype.ext hx')
  have hO2 : ∀ N : Subgroup ((su6Levi σ).subgroupOf C₀), N.Normal → IsPGroup 2 N → N = ⊥ :=
    forall_normal_isPGroup_eq_bot_of_mulEquiv' (subgroupOfEquivOfLe hLC).symm
      (forall_normal_isPGroup_eq_bot_su6Levi hf hk hK hσ)
  refine isCoreLeviDecomp_of_le_sup ?_ ?_ hperf hQ2 hLN' hdisj hO2
  · rw [hC]
    exact perfectCore_le _
  · rw [hC]
    exact le_sup_right




theorem factF3t_twistedE6 [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ Qt Mt : Subgroup (graphFixedRootGroup TwistTag.E6 K σ),
      perfectCore (centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
          Set (graphFixedRootGroup TwistTag.E6 K σ))) = Qt ⊔ Mt ∧
        IsPGroup 2 Qt ∧ Mt ≤ normalizer (Qt : Set (graphFixedRootGroup TwistTag.E6 K σ)) ∧
        Disjoint Qt Mt ∧ (∀ N : Subgroup Mt, N.Normal → IsPGroup 2 N → N = ⊥) ∧
        LieModel Mt .PSU 6 2 f := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := isCoreLeviDecomp_stdRepC_zero (k := k) hf hk hK hσ
  exact ⟨_, _, h1, h2, h3, h4, h5, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (subgroupOfEquivOfLe (su6Levi_le_graphFixedRootGroup σ)).symm
    (lieModel_su6Levi hf hk hK hσ)⟩

end F3

section Transport

variable {K : Type} [Field K]

@[expose] noncomputable def relWeylC (σ : K →+* K) (ω : List (Fin TwistTag.E6.foldedTag.rank)) :
    graphFixedRootGroup TwistTag.E6 K σ :=
  ⟨twistedE6RelWeyl K ω, twistedE6RelWeyl_mem σ ω⟩

theorem repXC_eq_conj [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (κ : Fin 2) :
    repXC hσσ κ = relWeylC σ (repWordX κ) * stdRepC hσσ κ * (relWeylC σ (repWordX κ))⁻¹ :=
  Subtype.ext (conj_repWordX κ).symm

theorem repYC_eq_conj [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (κ : Fin 2) :
    repYC hσσ κ = relWeylC σ (repWordY κ) * stdRepC hσσ κ * (relWeylC σ (repWordY κ))⁻¹ :=
  Subtype.ext (conj_repWordY κ).symm

theorem rootSubgroup_relAct_le_map [CharP K 2] (ω : List (Fin TwistTag.E6.foldedTag.rank))
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ) :
    rootSubgroup TwistTag.E6.tag K (twistedE6RelAct ω δ) ≤
      (rootSubgroup TwistTag.E6.tag K δ).map (MulAut.conj (twistedE6RelWeyl K ω)).toMonoidHom := by
  intro g hg
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
  exact ⟨pinnedX TwistTag.E6.tag K δ c, mem_rootSubgroup.2 ⟨c, rfl⟩,
    twistedE6RelWeyl_conj_pinnedX ω hδ c⟩

theorem pinnedX_mem_subsystemGroup_setA {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (h1 : γ 1 = 0) (c : K) :
    pinnedX TwistTag.E6.tag K γ c ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
  rw [subsystemGroup_eq_rootSpan]
  have hmem : γ ∈ parabolicRoots TwistTag.E6.tag E6GraphLevi.setA := by
    refine ⟨hγ, fun i hi => ?_⟩
    have hi1 : i = 1 := by
      by_contra h
      exact hi h
    rw [hi1]
    exact h1
  exact pinnedX_mem_rootSpan hmem c

theorem rootSubgroup_le_subsystemGroup_setA {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (h1 : γ 1 = 0) :
    rootSubgroup TwistTag.E6.tag K γ ≤ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
  intro g hg
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
  exact pinnedX_mem_subsystemGroup_setA hγ h1 c

end Transport

section Rank

variable {K : Type} [Field K]

@[expose] noncomputable def shortRankOneGroup {k : Type} [Field k] (ι : k →+* K) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  closure {g | ∃ c : k, g = pinnedX TwistTag.E6.tag K twistedE6ClassRootU (ι c) *
      pinnedX TwistTag.E6.tag K twistedE6ClassRootU' (ι c) ∨
    g = pinnedX TwistTag.E6.tag K (-twistedE6ClassRootU) (ι c) *
      pinnedX TwistTag.E6.tag K (-twistedE6ClassRootU') (ι c)}

theorem permLattice_neg_twistedE6ClassRootU :
    permLattice TwistTag.E6.perm (-twistedE6ClassRootU) = -twistedE6ClassRootU' := by decide

theorem shortRankOneGroup_le_C0 [CharP K 2] {k : Type} [Field k] {ι : k →+* K} {σ : K →+* K}
    (hσσ : ∀ c, σ (σ c) = c) (hσι : ∀ c, σ (ι c) = ι c) :
    shortRankOneGroup ι ≤ graphFixedRootGroup TwistTag.E6 K σ := by
  refine (closure_le _).2 ?_
  rintro g ⟨c, rfl | rfl⟩
  · have e : pinnedX TwistTag.E6.tag K twistedE6ClassRootU (ι c) *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootU' (ι c) =
          twistedE6PairX σ twistedE6ClassRootU (ι c) := by
      rw [twistedE6PairX, permLattice_twistedE6ClassRootU, hσι]
    rw [SetLike.mem_coe, e]
    exact twistedE6PairX_mem_graphFixedRootGroup hσσ isRoot_twistedE6ClassRoots.1 _
  · have e : pinnedX TwistTag.E6.tag K (-twistedE6ClassRootU) (ι c) *
        pinnedX TwistTag.E6.tag K (-twistedE6ClassRootU') (ι c) =
          twistedE6PairX σ (-twistedE6ClassRootU) (ι c) := by
      rw [twistedE6PairX, permLattice_neg_twistedE6ClassRootU, hσι]
    rw [SetLike.mem_coe, e]
    exact twistedE6PairX_mem_graphFixedRootGroup hσσ (CFSG.LieType.Chevalley.IsRoot.neg isRoot_twistedE6ClassRoots.1) _

theorem pinnedX_mem_map_relWeyl [CharP K 2] (ω : List (Fin TwistTag.E6.foldedTag.rank))
    {δ β : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ)
    (h : twistedE6RelAct ω δ = β) {H : Subgroup (ModGL TwistTag.E6.tag K)} {c : K}
    (hH : pinnedX TwistTag.E6.tag K δ c ∈ H) :
    pinnedX TwistTag.E6.tag K β c ∈ H.map (MulAut.conj (twistedE6RelWeyl K ω)).toMonoidHom :=
  ⟨_, hH, by rw [← h]; exact twistedE6RelWeyl_conj_pinnedX ω hδ c⟩

@[expose] def rootTX : Fin TwistTag.E6.tag.rank → ℤ := ![1, 0, 1, 1, 1, 1]

theorem transportT_check :
    twistedE6RelAct relWordTX rootTX = e6HighestRoot ∧
      twistedE6RelAct relWordTX (-rootTX) = -e6HighestRoot ∧
      twistedE6RelAct relWordTY rootE15 = twistedE6ClassRootU ∧
      twistedE6RelAct relWordTY rootE26 = twistedE6ClassRootU' ∧
      twistedE6RelAct relWordTY (-rootE15) = -twistedE6ClassRootU ∧
      twistedE6RelAct relWordTY (-rootE26) = -twistedE6ClassRootU' ∧
      rootTX ∈ rootFinset TwistTag.E6.tag := by
  decide +kernel

theorem thetaRankOneGroup_le_map_relWordTX [CharP K 2] {k : Type} [Field k] (ι : k →+* K) :
    E6GraphLevi.thetaRankOneGroup ι ≤
      (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA).map
        (MulAut.conj (twistedE6RelWeyl K relWordTX)).toMonoidHom := by
  obtain ⟨h1, h2, -, -, -, -, h7⟩ := transportT_check
  have hδ : IsRoot TwistTag.E6.tag rootTX := mem_rootFinset.1 h7
  refine sup_le ((closure_le _).2 ?_) ((closure_le _).2 ?_)
  · rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_map_relWeyl relWordTX hδ h1
      (pinnedX_mem_subsystemGroup_setA hδ rfl _)
  · rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_map_relWeyl relWordTX (CFSG.LieType.Chevalley.IsRoot.neg hδ) h2
      (pinnedX_mem_subsystemGroup_setA (CFSG.LieType.Chevalley.IsRoot.neg hδ) rfl _)

theorem shortRankOneGroup_le_map_relWordTY [CharP K 2] {k : Type} [Field k] (ι : k →+* K) :
    shortRankOneGroup ι ≤
      (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA).map
        (MulAut.conj (twistedE6RelWeyl K relWordTY)).toMonoidHom := by
  obtain ⟨-, -, h3, h4, h5, h6, -⟩ := transportT_check
  obtain ⟨hE, hE'⟩ := isRoot_rootE15
  refine (closure_le _).2 ?_
  rintro _ ⟨c, rfl | rfl⟩
  · exact mul_mem (pinnedX_mem_map_relWeyl relWordTY hE h3
      (pinnedX_mem_subsystemGroup_setA hE rfl _))
      (pinnedX_mem_map_relWeyl relWordTY hE' h4 (pinnedX_mem_subsystemGroup_setA hE' rfl _))
  · exact mul_mem (pinnedX_mem_map_relWeyl relWordTY (CFSG.LieType.Chevalley.IsRoot.neg hE) h5
      (pinnedX_mem_subsystemGroup_setA (CFSG.LieType.Chevalley.IsRoot.neg hE) rfl _))
      (pinnedX_mem_map_relWeyl relWordTY (CFSG.LieType.Chevalley.IsRoot.neg hE') h6
        (pinnedX_mem_subsystemGroup_setA (CFSG.LieType.Chevalley.IsRoot.neg hE') rfl _))

theorem rootSubgroup_short_le_map_relWordTY [CharP K 2] :
    (rootSubgroup TwistTag.E6.tag K twistedE6ClassRootU ⊔
        rootSubgroup TwistTag.E6.tag K (-twistedE6ClassRootU)) ⊔
      (rootSubgroup TwistTag.E6.tag K twistedE6ClassRootU' ⊔
        rootSubgroup TwistTag.E6.tag K (-twistedE6ClassRootU')) ≤
      (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA).map
        (MulAut.conj (twistedE6RelWeyl K relWordTY)).toMonoidHom := by
  obtain ⟨-, -, h3, h4, h5, h6, -⟩ := transportT_check
  obtain ⟨hE, hE'⟩ := isRoot_rootE15
  have key : ∀ {δ β : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag δ → δ 1 = 0 →
      twistedE6RelAct relWordTY δ = β →
      rootSubgroup TwistTag.E6.tag K β ≤ (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA).map
        (MulAut.conj (twistedE6RelWeyl K relWordTY)).toMonoidHom := by
    intro δ β hδ h0 h
    rw [← h]
    exact (rootSubgroup_relAct_le_map relWordTY hδ).trans
      (map_mono (rootSubgroup_le_subsystemGroup_setA hδ h0))
  exact sup_le (sup_le (key hE rfl h3) (key (CFSG.LieType.Chevalley.IsRoot.neg hE) rfl h5))
    (sup_le (key hE' rfl h4) (key (CFSG.LieType.Chevalley.IsRoot.neg hE') rfl h6))

theorem shortRootTorus_le_map_relWordTY [CharP K 2] {k : Type} [Field k] (ι : k →+* K) :
    shortRootTorus ι ≤
      (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA).map
        (MulAut.conj (twistedE6RelWeyl K relWordTY)).toMonoidHom := by
  rintro _ ⟨l, rfl⟩
  refine rootSubgroup_short_le_map_relWordTY ?_
  change rootDiagUnit Tag.E6 (d4CentralDiag (Units.map ι.toMonoidHom l)
    (Units.map ι.toMonoidHom l)) ∈ _
  rw [← rootTorusSL2_mul_rootTorusSL2_eq]
  refine mul_mem (mem_sup_left ?_) (mem_sup_right ?_)
  · have h := CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (K := K)
      (mem_rootFinset.1 shortRoots_check.1)
    have hm : rootTorusSL2 Tag.E6 K shortRootU (Units.map ι.toMonoidHom l) ∈
        rootSubgroup Tag.E6 K shortRootU ⊔ rootSubgroup Tag.E6 K (-shortRootU) := by
      rw [← h]
      exact ⟨_, rfl⟩
    exact hm
  · have h := CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (K := K)
      (mem_rootFinset.1 shortRoots_check.2.1)
    have hm : rootTorusSL2 Tag.E6 K shortRootU' (Units.map ι.toMonoidHom l) ∈
        rootSubgroup Tag.E6 K shortRootU' ⊔ rootSubgroup Tag.E6 K (-shortRootU') := by
      rw [← h]
      exact ⟨_, rfl⟩
    exact hm

end Rank

section TransportF3

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem lieModel_su6Levi_subgroupOf (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    LieModel ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) .PSU 6 2 f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (subgroupOfEquivOfLe (su6Levi_le_graphFixedRootGroup σ)).symm (lieModel_su6Levi hf hk hK hσ)

theorem factF3t_repX [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ Qt Mt : Subgroup (graphFixedRootGroup TwistTag.E6 K σ),
      perfectCore (centralizer ({repXC (apply_apply_eq hK hσ) 0} :
          Set (graphFixedRootGroup TwistTag.E6 K σ))) = Qt ⊔ Mt ∧
        IsPGroup 2 Qt ∧ Mt ≤ normalizer (Qt : Set (graphFixedRootGroup TwistTag.E6 K σ)) ∧
        Disjoint Qt Mt ∧ (∀ N : Subgroup Mt, N.Normal → IsPGroup 2 N → N = ⊥) ∧
        LieModel Mt .PSU 6 2 f ∧
        (E6GraphLevi.thetaRankOneGroup (algebraMap k K)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ) ≤ Mt := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  set n := relWeylC σ relWordTX with hn
  have hd := (isCoreLeviDecomp_stdRepC_zero (k := k) hf hk hK hσ).map (MulAut.conj n)
  rw [← centralizer_conj_eq_map] at hd
  rw [repXC_eq_conj (apply_apply_eq hK hσ) 0]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hd
  refine ⟨_, _, h1, h2, h3, h4, h5, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (((su6Levi σ).subgroupOf _).equivMapOfInjective (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective)
    (lieModel_su6Levi_subgroupOf hf hk hK hσ), subgroupOf_le_map_conj n fun x hx => ?_⟩
  refine mem_inf.2 ⟨mem_map_conj_iff.1 (thetaRankOneGroup_le_map_relWordTX _ hx), ?_⟩
  exact mul_mem (mul_mem (inv_mem n.2) (thetaRankOneGroup_le_C0 hf hk hK hσ hx)) n.2

theorem factF3t_repY [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ Qt Mt : Subgroup (graphFixedRootGroup TwistTag.E6 K σ),
      perfectCore (centralizer ({repYC (apply_apply_eq hK hσ) 0} :
          Set (graphFixedRootGroup TwistTag.E6 K σ))) = Qt ⊔ Mt ∧
        IsPGroup 2 Qt ∧ Mt ≤ normalizer (Qt : Set (graphFixedRootGroup TwistTag.E6 K σ)) ∧
        Disjoint Qt Mt ∧ (∀ N : Subgroup Mt, N.Normal → IsPGroup 2 N → N = ⊥) ∧
        LieModel Mt .PSU 6 2 f ∧
        (shortRankOneGroup (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
          Mt ∧
        (shortRootTorus (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
          Mt := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c =>
    (sigma_eq_self_iff hk hσ _).2 ⟨c, rfl⟩
  set n := relWeylC σ relWordTY with hn
  have hd := (isCoreLeviDecomp_stdRepC_zero (k := k) hf hk hK hσ).map (MulAut.conj n)
  rw [← centralizer_conj_eq_map] at hd
  rw [repYC_eq_conj (apply_apply_eq hK hσ) 0]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hd
  refine ⟨_, _, h1, h2, h3, h4, h5, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (((su6Levi σ).subgroupOf _).equivMapOfInjective (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective)
    (lieModel_su6Levi_subgroupOf hf hk hK hσ), subgroupOf_le_map_conj n fun x hx => ?_,
    subgroupOf_le_map_conj n fun x hx => ?_⟩
  · refine mem_inf.2 ⟨mem_map_conj_iff.1 (shortRankOneGroup_le_map_relWordTY _ hx), ?_⟩
    exact mul_mem (mul_mem (inv_mem n.2)
      (shortRankOneGroup_le_C0 (apply_apply_eq hK hσ) hσι hx)) n.2
  · refine mem_inf.2 ⟨mem_map_conj_iff.1 (shortRootTorus_le_map_relWordTY _ hx), ?_⟩
    exact mul_mem (mul_mem (inv_mem n.2) (shortRootTorus_le_C0 hσι hx)) n.2

end TransportF3

end CFSG.SeitzReduction.TwistedE6Pilot
