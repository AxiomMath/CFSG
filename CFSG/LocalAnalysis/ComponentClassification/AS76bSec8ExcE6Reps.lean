module

public import CFSG.LieType.Chevalley.E6EvenInvolution
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE6
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4Residual
public import CFSG.LieType.Chevalley.E6EvenRootTorusLevi
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.E6Sec8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Chevalley.E6EvenInvolution (jRep frame₁ frame₂ frame₃)
open CFSG.LieType.Chevalley.E6GraphLevi (setA thetaRankOneGroup)
open CFSG.ComponentClassification.RankTwoExceptional.Exc CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoExceptional.F4Sec8 (OddCommWitness residualMem_of_witness
  exists_card_eq_two_pow)
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def frameRep
    (F : List (Fin Tag.E6.rank → ℤ)) : adjointGroup .E6 K :=
  ⟨(F.map fun σ => pinnedX .E6 K σ 1).prod, list_prod_map_pinnedX_mem_adjointGroup F⟩

@[expose] def e6Reps
    : List (adjointGroup .E6 K) :=
  [frameRep frame₁, frameRep frame₂, frameRep frame₃]

abbrev rootElt
    (γ : Fin Tag.E6.rank → ℤ) : adjointGroup .E6 K :=
  ⟨pinnedX .E6 K γ 1, pinnedX_mem_adjointGroup _ _⟩

theorem coe_frameRep
    (F : List (Fin Tag.E6.rank → ℤ)) :
    ((frameRep F : adjointGroup .E6 K) : ModGL .E6 K) = (F.map fun σ => pinnedX .E6 K σ 1).prod :=
  rfl

theorem frameRep_pair
    (a b : Fin Tag.E6.rank → ℤ) :
    frameRep (K := K) [a, b] = rootElt a * rootElt b :=
  Subtype.ext (by simp [coe_frameRep])

theorem frameRep_triple
    (a b c : Fin Tag.E6.rank → ℤ) :
    frameRep (K := K) [a, b, c] = rootElt a * (rootElt b * rootElt c) :=
  Subtype.ext (by simp [coe_frameRep])

theorem isConj_of_frameProdConj
    {F F' : List (Fin Tag.E6.rank → ℤ)}
    (h : FrameProdConj .E6 K F F') : IsConj (frameRep (K := K) F) (frameRep F') := by
  obtain ⟨g, hg, e⟩ := h
  exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext e⟩

theorem frameConj_x
    [CharP K 2] : FrameProdConj .E6 K [highRoot .E6] frame₁ := by
  have h := frameWalkEnds_sound (K := K) (Or.inr (Or.inl rfl)) (F := [70]) (T := [0])
    (ms := [.word [1, 3, 2, 4, 3, 1, 5, 4, 3, 2]]) (by decide) (by decide +kernel)
    (by decide +kernel)
  have e1 : [70].map Tag.E6.rootCertificate.root = [highRoot .E6] := by
    apply List.map_injective_iff.2 List.ofFn_injective
    decide +kernel
  have e2 : [0].map Tag.E6.rootCertificate.root = frame₁ := by
    apply List.map_injective_iff.2 List.ofFn_injective
    decide +kernel
  rwa [e1, e2] at h

theorem frameConj_y
    [CharP K 2] : FrameProdConj .E6 K oddDerivE6YFrame frame₂ := by
  have h := frameWalkEnds_sound (K := K) (Or.inr (Or.inl rfl)) (F := [61, 62]) (T := [0, 5])
    (ms := [.word [0, 2, 3, 1, 5, 4, 3, 1, 2, 3, 4]]) (by decide) (by decide +kernel)
    (by decide +kernel)
  have e1 : [61, 62].map Tag.E6.rootCertificate.root = oddDerivE6YFrame := by
    apply List.map_injective_iff.2 List.ofFn_injective
    decide +kernel
  have e2 : [0, 5].map Tag.E6.rootCertificate.root = frame₂ := by
    apply List.map_injective_iff.2 List.ofFn_injective
    decide +kernel
  rwa [e1, e2] at h

theorem frameConj_z
    [CharP K 2] : FrameProdConj .E6 K oddDerivE6ZFrame frame₃ := by
  have h := frameWalkEnds_sound (K := K) (Or.inr (Or.inl rfl)) (F := [58, 56, 55])
    (T := [0, 3, 5]) (ms := [.word [3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2]]) (by decide)
    (by decide +kernel) (by decide +kernel)
  have e1 : [58, 56, 55].map Tag.E6.rootCertificate.root = oddDerivE6ZFrame := by
    apply List.map_injective_iff.2 List.ofFn_injective
    decide +kernel
  have e2 : [0, 3, 5].map Tag.E6.rootCertificate.root = frame₃ := by
    apply List.map_injective_iff.2 List.ofFn_injective
    decide +kernel
  rwa [e1, e2] at h

theorem classesCover_e6Reps
    [Finite K] [CharP K 2] :
    ClassesCover (e6Reps (K := K)) := by
  intro t ht2 ht1
  obtain ⟨g, hg⟩ := exists_conj_mem_innerRepsE6 (t := t) (by rw [sq]; exact ht2) ht1
  have hconj : IsConj (g * t * g⁻¹) t := isConj_iff.2 ⟨g⁻¹, by group⟩
  simp only [innerRepsE6, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h | h | h
  · refine ⟨frameRep frame₁, List.mem_cons_self .., ?_⟩
    have hx := isConj_of_frameProdConj (frameConj_x (K := K))
    have e : frameRep (K := K) [highRoot .E6] = g * t * g⁻¹ := by
      rw [h]
      exact Subtype.ext (by simp [coe_frameRep])
    rw [e] at hx
    exact hx.symm.trans hconj
  · refine ⟨frameRep frame₂, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    have hx := isConj_of_frameProdConj (frameConj_y (K := K))
    rw [show frameRep (K := K) oddDerivE6YFrame = g * t * g⁻¹ from h.symm] at hx
    exact hx.symm.trans hconj
  · refine ⟨frameRep frame₃, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)), ?_⟩
    have hx := isConj_of_frameProdConj (frameConj_z (K := K))
    rw [show frameRep (K := K) oddDerivE6ZFrame = g * t * g⁻¹ from h.symm] at hx
    exact hx.symm.trans hconj

section Residual

variable {C : Type*} [Group C]

theorem residualMem_conj_of {x : C} {P : Subgroup C} (hP : IsPGroup 2 P)
    (hPx : P ≤ Subgroup.closure {c | c * x = x * c ∧ Odd (orderOf c)}) (hx : x ∈ ⁅P, P⁆)
    (g : C) :
    ResidualMem (g * x * g⁻¹) := by
  have hg : g * x * g⁻¹ = MulAut.conj g x := (MulAut.conj_apply g x).symm
  rw [hg]
  have h1 : Subgroup.closure {c : C | c * MulAut.conj g x = MulAut.conj g x * c ∧
      Odd (orderOf c)} ≤
      oUpperTwo (cent (MulAut.conj g x)) :=
    closure_mono fun c hc => ⟨mem_centralizer_singleton_iff.2 hc.1, hc.2⟩
  have hP' := (map_mono hPx).trans (F4Sec8.map_closure_odd_le (MulAut.conj g) x)
  refine commutator_le_admResidual_of_isPGroup (hP'.trans (h1.trans le_sup_left))
    (hP.map _) ?_
  rw [← map_commutator]
  exact mem_map_of_mem _ hx

end Residual

theorem eq_of_ofFn {a b : Fin Tag.E6.rank → ℤ} (h : List.ofFn a = List.ofFn b) : a = b :=
  List.ofFn_injective h

theorem ne_of_ofFn {a b : Fin Tag.E6.rank → ℤ} (h : List.ofFn a ≠ List.ofFn b) : a ≠ b :=
  fun e => h (congrArg List.ofFn e)

theorem mem_of_getElem {l : List (Fin Tag.E6.rank → ℤ)} {a : Fin Tag.E6.rank → ℤ} (i : ℕ)
    (hi : i < l.length) (h : List.ofFn l[i] = List.ofFn a) : a ∈ l := by
  rw [← List.ofFn_injective h]
  exact List.getElem_mem hi

theorem isPGroup_closure_pos
    [Finite K] [CharP K 2] {S : Set (Fin Tag.E6.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot .E6 γ ∧ 0 < height γ) :
    IsPGroup 2 (closure ((fun γ => rootElt (K := K) γ) '' S)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ((isPGroup_posUnipotent (K := K) 2 .E6).comap_subtype
    (K := adjointGroup .E6 K)).to_le ?_
  rw [closure_le]
  rintro _ ⟨γ, hγ, rfl⟩
  exact pinnedX_mem_rootSpan (S := {α | IsRoot .E6 α ∧ 0 < height α}) (hS γ hγ) 1

theorem commutator_rootElt
    [CharP K 2] {a b : Fin Tag.E6.rank → ℤ} (ha : IsRoot .E6 a)
    (hb : IsRoot .E6 b) (hne : a ≠ b) (hne' : a ≠ -b) (hab : IsRoot .E6 (a + b)) :
    ⁅rootElt (K := K) a, rootElt (K := K) b⁆ = rootElt (K := K) (a + b) := by
  refine Subtype.ext ?_
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  have h := EvenOddRadical.pinnedX_conj_of_isRoot (τ := .E6) (R := K) (Or.inr (Or.inl rfl))
    CharTwo.two_eq_zero ha hb hne hne' hab 1 1
  change pinnedX .E6 K a 1 * pinnedX .E6 K b 1 * (pinnedX .E6 K a 1)⁻¹ *
    (pinnedX .E6 K b 1)⁻¹ = pinnedX .E6 K (a + b) 1
  rw [h, mul_one, mul_inv_cancel_right]

theorem isRoot_of_pos
    {γ : Fin Tag.E6.rank → ℤ} (n : ℕ)
    (hn : n < Tag.E6.rootCertificate.roots.length)
    (h : List.ofFn (Tag.E6.rootCertificate.root n) = List.ofFn γ) : IsRoot .E6 γ :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨n, hn, List.ofFn_injective h⟩

theorem rootElt_eq_commutator
    [CharP K 2] {a b c : Fin Tag.E6.rank → ℤ} (ha : IsRoot .E6 a)
    (hb : IsRoot .E6 b) (hne : a ≠ b) (hne' : a ≠ -b) (hc : IsRoot .E6 c) (habc : a + b = c) :
    rootElt (K := K) c = ⁅rootElt (K := K) a, rootElt (K := K) b⁆ := by
  rw [commutator_rootElt ha hb hne hne' (habc ▸ hc), habc]

theorem residual_witness_x
    [Finite K] [CharP K 2] :
    ∃ P : Subgroup (adjointGroup .E6 K), IsPGroup 2 P ∧
      P ≤ Subgroup.closure {c | c * frameRep [highRoot .E6] = frameRep [highRoot .E6] * c ∧
        Odd (orderOf c)} ∧ frameRep [highRoot .E6] ∈ ⁅P, P⁆ := by
  obtain ⟨n, hn1, hK⟩ := exists_card_eq_two_pow (K := K)
  have hβ : IsRoot .E6 ![1, 1, 2, 3, 2, 1] := isRoot_of_pos 68 (by decide) (by decide +kernel)
  have hα : IsRoot .E6 ![0, 1, 0, 0, 0, 0] := isRoot_of_pos 1 (by decide) (by decide +kernel)
  have hS : ∀ γ ∈ ({![1, 1, 2, 3, 2, 1], ![0, 1, 0, 0, 0, 0]} : Set (Fin Tag.E6.rank → ℤ)),
      IsRoot .E6 γ ∧ 0 < height γ := by
    rintro γ (rfl | rfl)
    · exact ⟨hβ, by decide⟩
    · exact ⟨hα, by decide⟩
  have ht : ((frameRep (K := K) [highRoot .E6] : adjointGroup .E6 K) : ModGL .E6 K) =
      pinnedX .E6 K (highRoot .E6) 1 := by
    rw [coe_frameRep, List.map_singleton, List.prod_singleton]
  refine ⟨_, isPGroup_closure_pos hS, ?_, ?_⟩
  · rw [closure_le]
    rintro _ ⟨γ, hγ, rfl⟩
    rcases (show n = 1 ∨ 2 ≤ n by omega) with h1 | hf
    · exact posUnipotent_le_closure_odd_E_two (Or.inl rfl) (by rw [hK, h1, pow_one]) ht
        (pinnedX_mem_rootSpan (S := {α | IsRoot .E6 α ∧ 0 < height α}) (hS γ hγ) 1)
    · exact pinnedX_mem_closure_odd_E (Or.inl rfl) hf hK ht (hS γ hγ).1 (hS γ hγ).2 1
  · have e : frameRep (K := K) [highRoot .E6] = rootElt (highRoot .E6) :=
      Subtype.ext (by rw [ht])
    rw [e, rootElt_eq_commutator (c := highRoot .E6) hβ hα (ne_of_ofFn (by decide +kernel))
      (ne_of_ofFn (by decide +kernel)) (isRoot_of_pos 70 (by decide) (by decide +kernel))
      (eq_of_ofFn (by decide +kernel))]
    exact commutator_mem_commutator (subset_closure ⟨_, Or.inl rfl, rfl⟩)
      (subset_closure ⟨_, Or.inr rfl, rfl⟩)

theorem residual_witness_y
    [Finite K] [CharP K 2] :
    ∃ P : Subgroup (adjointGroup .E6 K), IsPGroup 2 P ∧
      P ≤ Subgroup.closure {c | c * frameRep oddDerivE6YFrame = frameRep oddDerivE6YFrame * c ∧
        Odd (orderOf c)} ∧ frameRep oddDerivE6YFrame ∈ ⁅P, P⁆ := by
  have ha : IsRoot .E6 ![0, 0, 0, 0, 0, 1] := isRoot_of_pos 5 (by decide) (by decide +kernel)
  have hb : IsRoot .E6 ![1, 1, 2, 2, 1, 0] := isRoot_of_pos 55 (by decide) (by decide +kernel)
  have hc : IsRoot .E6 ![0, 0, 0, 0, 1, 1] := isRoot_of_pos 15 (by decide) (by decide +kernel)
  have hd : IsRoot .E6 ![1, 1, 1, 2, 1, 0] := isRoot_of_pos 48 (by decide) (by decide +kernel)
  have hS2 : ∀ γ ∈ ({![0, 0, 0, 0, 0, 1], ![1, 1, 2, 2, 1, 0], ![0, 0, 0, 0, 1, 1],
      ![1, 1, 1, 2, 1, 0]} : Set (Fin Tag.E6.rank → ℤ)), γ ∈ oddDerivE6YDeriv.map Prod.fst := by
    rintro γ (rfl | rfl | rfl | rfl)
    · exact mem_of_getElem 0 (by decide) (by decide +kernel)
    · exact mem_of_getElem 24 (by decide) (by decide +kernel)
    · exact mem_of_getElem 4 (by decide) (by decide +kernel)
    · exact mem_of_getElem 21 (by decide) (by decide +kernel)
  have hS : ∀ γ ∈ ({![0, 0, 0, 0, 0, 1], ![1, 1, 2, 2, 1, 0], ![0, 0, 0, 0, 1, 1],
      ![1, 1, 1, 2, 1, 0]} : Set (Fin Tag.E6.rank → ℤ)), IsRoot .E6 γ ∧ 0 < height γ := by
    rintro γ (rfl | rfl | rfl | rfl)
    · exact ⟨ha, by decide⟩
    · exact ⟨hb, by decide⟩
    · exact ⟨hc, by decide⟩
    · exact ⟨hd, by decide⟩
  refine ⟨_, isPGroup_closure_pos hS, ?_, ?_⟩
  · rw [closure_le]
    rintro _ ⟨γ, hγ, rfl⟩
    exact rootSpan_le_closure_odd_E6_y (t := frameRep oddDerivE6YFrame) (coe_frameRep _) _
      (pinnedX_mem_rootSpan (hS2 γ hγ) 1)
  · have e : frameRep (K := K) oddDerivE6YFrame =
        rootElt (K := K) ![1, 1, 2, 2, 1, 1] * rootElt (K := K) ![1, 1, 1, 2, 2, 1] :=
      frameRep_pair _ _
    rw [e, rootElt_eq_commutator (c := ![1, 1, 2, 2, 1, 1]) ha hb (ne_of_ofFn (by decide +kernel))
      (ne_of_ofFn (by decide +kernel)) (isRoot_of_pos 61 (by decide) (by decide +kernel))
      (eq_of_ofFn (by decide +kernel)), rootElt_eq_commutator (c := ![1, 1, 1, 2, 2, 1]) hc hd
      (ne_of_ofFn (by decide +kernel)) (ne_of_ofFn (by decide +kernel))
      (isRoot_of_pos 62 (by decide) (by decide +kernel)) (eq_of_ofFn (by decide +kernel))]
    exact mul_mem (commutator_mem_commutator (subset_closure ⟨_, Or.inl rfl, rfl⟩)
      (subset_closure ⟨_, Or.inr (Or.inl rfl), rfl⟩))
      (commutator_mem_commutator (subset_closure ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩)
        (subset_closure ⟨_, Or.inr (Or.inr (Or.inr rfl)), rfl⟩))

theorem residual_witness_z
    [Finite K] [CharP K 2] :
    ∃ P : Subgroup (adjointGroup .E6 K), IsPGroup 2 P ∧
      P ≤ Subgroup.closure {c | c * frameRep oddDerivE6ZFrame = frameRep oddDerivE6ZFrame * c ∧
        Odd (orderOf c)} ∧ frameRep oddDerivE6ZFrame ∈ ⁅P, P⁆ := by
  have ha : IsRoot .E6 ![0, 0, 0, 1, 1, 0] := isRoot_of_pos 13 (by decide) (by decide +kernel)
  have hb : IsRoot .E6 ![0, 1, 1, 1, 1, 1] := isRoot_of_pos 44 (by decide) (by decide +kernel)
  have hc : IsRoot .E6 ![0, 0, 0, 1, 0, 0] := isRoot_of_pos 3 (by decide) (by decide +kernel)
  have hd : IsRoot .E6 ![1, 1, 1, 1, 1, 1] := isRoot_of_pos 49 (by decide) (by decide +kernel)
  have he : IsRoot .E6 ![0, 0, 1, 1, 0, 0] := isRoot_of_pos 11 (by decide) (by decide +kernel)
  have hf : IsRoot .E6 ![1, 1, 1, 1, 1, 0] := isRoot_of_pos 39 (by decide) (by decide +kernel)
  have hS2 : ∀ γ ∈ ({![0, 0, 0, 1, 1, 0], ![0, 1, 1, 1, 1, 1], ![0, 0, 0, 1, 0, 0],
      ![1, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 0]} :
        Set (Fin Tag.E6.rank → ℤ)), γ ∈ oddDerivE6ZDeriv.map Prod.fst := by
    rintro γ (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact mem_of_getElem 1 (by decide) (by decide +kernel)
    · exact mem_of_getElem 8 (by decide) (by decide +kernel)
    · exact mem_of_getElem 0 (by decide) (by decide +kernel)
    · exact mem_of_getElem 13 (by decide) (by decide +kernel)
    · exact mem_of_getElem 2 (by decide) (by decide +kernel)
    · exact mem_of_getElem 11 (by decide) (by decide +kernel)
  have hS : ∀ γ ∈ ({![0, 0, 0, 1, 1, 0], ![0, 1, 1, 1, 1, 1], ![0, 0, 0, 1, 0, 0],
      ![1, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 0]} :
        Set (Fin Tag.E6.rank → ℤ)), IsRoot .E6 γ ∧ 0 < height γ := by
    rintro γ (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨ha, by decide⟩
    · exact ⟨hb, by decide⟩
    · exact ⟨hc, by decide⟩
    · exact ⟨hd, by decide⟩
    · exact ⟨he, by decide⟩
    · exact ⟨hf, by decide⟩
  refine ⟨_, isPGroup_closure_pos hS, ?_, ?_⟩
  · rw [closure_le]
    rintro _ ⟨γ, hγ, rfl⟩
    exact rootSpan_le_closure_odd_E6_z (t := frameRep oddDerivE6ZFrame) (coe_frameRep _) _
      (pinnedX_mem_rootSpan (hS2 γ hγ) 1)
  · have e : frameRep (K := K) oddDerivE6ZFrame = rootElt (K := K) ![0, 1, 1, 2, 2, 1] *
        (rootElt (K := K) ![1, 1, 1, 2, 1, 1] * rootElt (K := K) ![1, 1, 2, 2, 1, 0]) :=
      frameRep_triple _ _ _
    rw [e, rootElt_eq_commutator (c := ![0, 1, 1, 2, 2, 1]) ha hb (ne_of_ofFn (by decide +kernel))
      (ne_of_ofFn (by decide +kernel)) (isRoot_of_pos 58 (by decide) (by decide +kernel))
      (eq_of_ofFn (by decide +kernel)), rootElt_eq_commutator (c := ![1, 1, 1, 2, 1, 1]) hc hd
      (ne_of_ofFn (by decide +kernel)) (ne_of_ofFn (by decide +kernel))
      (isRoot_of_pos 56 (by decide) (by decide +kernel)) (eq_of_ofFn (by decide +kernel)),
      rootElt_eq_commutator (c := ![1, 1, 2, 2, 1, 0]) he hf (ne_of_ofFn (by decide +kernel))
      (ne_of_ofFn (by decide +kernel)) (isRoot_of_pos 55 (by decide) (by decide +kernel))
      (eq_of_ofFn (by decide +kernel))]
    refine mul_mem (commutator_mem_commutator (subset_closure ⟨_, Or.inl rfl, rfl⟩)
      (subset_closure ⟨_, Or.inr (Or.inl rfl), rfl⟩)) (mul_mem ?_ ?_)
    · exact commutator_mem_commutator (subset_closure ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩)
        (subset_closure ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩)
    · exact commutator_mem_commutator
        (subset_closure ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩)
        (subset_closure ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), rfl⟩)

theorem residualMem_e6Reps
    [Finite K] [CharP K 2] :
    ∀ x ∈ e6Reps (K := K), ResidualMem x := by
  intro x hx
  simp only [e6Reps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_of_frameProdConj (frameConj_x (K := K)))
    obtain ⟨P, hP, hPx, hx⟩ := residual_witness_x (K := K)
    rw [← hg]
    exact residualMem_conj_of hP hPx hx g
  · obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_of_frameProdConj (frameConj_y (K := K)))
    obtain ⟨P, hP, hPx, hx⟩ := residual_witness_y (K := K)
    rw [← hg]
    exact residualMem_conj_of hP hPx hx g
  · obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_of_frameProdConj (frameConj_z (K := K)))
    obtain ⟨P, hP, hPx, hx⟩ := residual_witness_z (K := K)
    rw [← hg]
    exact residualMem_conj_of hP hPx hx g

theorem involution_e6Reps
    [CharP K 2] : ∀ x ∈ e6Reps (K := K), x * x = 1 ∧ x ≠ 1 := by
  intro x hx
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [e6Reps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · obtain ⟨-, h1, h3⟩ := E6EvenInvolution.jRep₁_facts h2
    exact ⟨Subtype.ext h1, fun h => h3 (congrArg Subtype.val h)⟩
  · obtain ⟨-, h1, h3⟩ := E6EvenInvolution.jRep₂_facts h2
    exact ⟨Subtype.ext h1, fun h => h3 (congrArg Subtype.val h)⟩
  · obtain ⟨-, h1, h3⟩ := E6EvenInvolution.jRep₃_facts h2
    exact ⟨Subtype.ext h1, fun h => h3 (congrArg Subtype.val h)⟩

theorem charTwo_e6Reps
    [Finite K] [CharP K 2] : ∀ x ∈ e6Reps (K := K), CharTwo x := by
  intro x hx
  obtain ⟨hx2, hx1⟩ := involution_e6Reps x hx
  exact EvenOddRadical.charTwo_of_involution (.ordinary .E6) (x := x) hx2 hx1

theorem card_le_two_of_forall {G : Type*} [Group G] {H : Subgroup G} {a : G}
    (h : ∀ w ∈ H, w = 1 ∨ w = a) : Nat.card H ≤ 2 := by
  have hsub : (H : Set G) ⊆ {1, a} := fun w hw => by
    rcases h w hw with rfl | rfl <;> simp
  calc Nat.card H = (H : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, a} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

theorem eq_one_or_eq_of_mem_zx
    {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card K = 2 ^ f)
    {j : adjointGroup TwistTag.E6.tag K}
    (hjL : (j : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA)
    (hdc : ∀ w ∈ subsystemGroup TwistTag.E6.tag K setA, (∀ c ∈ subsystemGroup TwistTag.E6.tag K
      setA, c * (j : ModGL TwistTag.E6.tag K) = j * c → w * c = c * w) → w = 1 ∨ w = j)
    {w : adjointGroup TwistTag.E6.tag K} (hw : w ∈ zx j) : w = 1 ∨ w = j := by
  obtain ⟨-, hwz, -⟩ := hw
  have hF1 := E6EvenRootTorus.centralizer_thetaRankOneGroup hf hk
  have hXG := E6GraphRadical.thetaRankOneGroup_le_adjointGroup (E := K) (RingHom.id K)
  have hLG : subsystemGroup TwistTag.E6.tag K setA ≤ adjointGroup TwistTag.E6.tag K :=
    E6GraphLevi.subsystemGroup_le_adjointGroup
  have hjX := hjL
  rw [← hF1] at hjX
  have hwL : (w : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K setA := by
    rw [← hF1]
    refine mem_inf.2 ⟨w.2, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hyc : (⟨y, hXG hy⟩ : adjointGroup TwistTag.E6.tag K) ∈ cent j :=
      mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_iff.1 (mem_inf.1 hjX).2 y hy))
    exact (congrArg Subtype.val (hwz _ hyc)).symm
  rcases hdc _ hwL (fun c hc hcj => by
    have hcc : (⟨c, hLG hc⟩ : adjointGroup TwistTag.E6.tag K) ∈ cent j :=
      mem_centralizer_singleton_iff.2 (Subtype.ext hcj)
    exact congrArg Subtype.val (hwz _ hcc)) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem card_zx_e6Reps
    (hK : Nat.card K = 2) :
    ∀ x ∈ e6Reps (K := K), Nat.card (zx x) < 4 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have h2 : (2 : K) = 0 := E6GraphHighestRoot.two_eq_zero_of_card (n := 1) le_rfl (by rw [hK]; rfl)
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; rfl
  intro x hx
  simp only [e6Reps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · have : Nat.card (zx (frameRep (K := K) frame₁)) ≤ 2 :=
      card_le_two_of_forall fun w hw => eq_one_or_eq_of_mem_zx (j := frameRep frame₁)
      le_rfl hK' (E6EvenInvolution.jRep₁_facts h2).1
      (fun w hw hc => E6EvenInvolution.eq_one_or_eq_jRep₁ h2 hK hw hc) hw
    omega
  · have : Nat.card (zx (frameRep (K := K) frame₂)) ≤ 2 :=
      card_le_two_of_forall fun w hw => eq_one_or_eq_of_mem_zx (j := frameRep frame₂)
      le_rfl hK' (E6EvenInvolution.jRep₂_facts h2).1
      (fun w hw hc => E6EvenInvolution.eq_one_or_eq_jRep₂ h2 hK hw hc) hw
    omega
  · have : Nat.card (zx (frameRep (K := K) frame₃)) ≤ 2 :=
      card_le_two_of_forall fun w hw => eq_one_or_eq_of_mem_zx (j := frameRep frame₃)
      le_rfl hK' (E6EvenInvolution.jRep₃_facts h2).1
      (fun w hw hc => E6EvenInvolution.eq_one_or_eq_jRep₃ h2 hK hw hc) hw
    omega

end CFSG.ComponentClassification.RankTwoExceptional.E6Sec8
