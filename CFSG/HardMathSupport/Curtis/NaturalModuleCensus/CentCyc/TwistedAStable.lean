module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAKit
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.AGLEmbedding.ToralCensus
  Matrix Polynomial
open scoped commutatorElement

section Dichotomy

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {x : LinearMap.GeneralLinearGroup K V} {W : Submodule K V}

theorem eq_bot_or_le_of_multiplicity_le_one (hW : ∀ w ∈ W, (x : Module.End K V) w ∈ W)
    {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (hm : primaryMultiplicity (x : Module.End K V) a ≤ 1) :
    W ⊓ primaryComponent (x : Module.End K V) a = ⊥ ∨
      primaryComponent (x : Module.End K V) a ≤ W := by
  by_cases hbot : W ⊓ primaryComponent (x : Module.End K V) a = ⊥
  · exact Or.inl hbot
  right
  have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨hwW, hwa⟩ := Submodule.mem_inf.mp hw
  set w' : primaryComponent (x : Module.End K V) a := ⟨w, hwa⟩
  have hw'0 : w' ≠ 0 := fun h0 => hw0 (congrArg Subtype.val h0)
  have hpos : 0 < Module.finrank (AdjoinRoot a) (primaryComponent (x : Module.End K V) a) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨w', hw'0⟩
  have h1 : Module.finrank (AdjoinRoot a) (primaryComponent (x : Module.End K V) a) = 1 :=
    le_antisymm hm hpos
  intro v hv
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w' hw'0).mp h1 ⟨v, hv⟩
  have := coe_smul_mem hW a c (v := w') hwW
  rw [hc] at this
  exact this

end Dichotomy

section Good

variable {f : ℕ} {K : Type} [Field K] [Finite K] {r ε : ℕ}

omit [Finite K] in
theorem exists_perfect_centralizer_hyp (h : UnitaryFieldData 2 f K) [Finite K] (hf : 2 ≤ f)
    (t : hypSU h r ε)
    (hsq : Squarefree (minpoly K
      (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K))))
    {a : K[X]}
    (ha : a ∈ primaryFactors
      (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K)))
    (hm : 2 ≤ primaryMultiplicity
      (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K)) a) :
    ∃ W : Subgroup (hypSU h r ε), W ≠ ⊥ ∧ ⁅W, W⁆ = W ∧ ∀ w ∈ W, Commute w t := by
  classical
  have := h.finite
  set x : LinearMap.GeneralLinearGroup K (HypIndex r ε → K) :=
    GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) with hxdef
  have hxSU : x ∈ sesqSpecialUnitaryGroup (hypForm h r ε) :=
    toLin_mem_sesqSpecialUnitaryGroup_hyp h t
  have H : UnitaryPrimaryData h.bar (hypForm h r ε) x := hypPrimaryData h t hsq
  have hq2 : 2 ≤ 2 ^ f := by
    have : 1 < 2 ^ f := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hdeg : 1 ≤ a.natDegree := (irreducible_of_mem_primaryFactors ha).natDegree_pos
  have hexc : dualPoly h.bar a = a →
      (primaryMultiplicity (x : Module.End K (HypIndex r ε → K)) a,
        2 ^ (f * a.natDegree)) ∉ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
    intro _ hmem
    have h4 : 4 ≤ 2 ^ (f * a.natDegree) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f * a.natDegree) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    omega
  have hgood : IsGoodBlock h x ⟨a, ha⟩ := ⟨hm, hexc⟩
  have hfacts := specialBlockFacts_of_good H hq2 ⟨a, ha⟩ hgood
  have hquasi := hfacts.quasisimple hm
  have hle : specialBlock (hypForm h r ε) x a ≤ sesqSpecialUnitaryGroup (hypForm h r ε) :=
    specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq2 ⟨a, ha⟩ hgood
  set S := specialBlock (hypForm h r ε) x a with hS
  let Φ1 : S →* LinearMap.GeneralLinearGroup K (HypIndex r ε → K) := S.subtype
  let Φ : S →* hypSU h r ε :=
    ((GeneralLinearGroup.toLin (n := HypIndex r ε) (R := K)).symm.toMonoidHom.comp Φ1).codRestrict
      (hypSU h r ε) (fun s => by
        refine (toLin_mem_sesqSpecialUnitaryGroup_iff h _ _).mp ?_
        change GeneralLinearGroup.toLin (GeneralLinearGroup.toLin.symm (Φ1 s)) ∈ _
        rw [MulEquiv.apply_symm_apply]
        exact hle s.2)
  have hΦinj : Function.Injective Φ := by
    intro M N hMN
    have h1 : Φ1 M = Φ1 N := by
      have := congrArg (fun g : hypSU h r ε => (g : GL (HypIndex r ε) K)) hMN
      exact (GeneralLinearGroup.toLin (n := HypIndex r ε) (R := K)).symm.injective this
    exact Subtype.ext h1
  have hΦcomm : ∀ s : S, Commute (Φ s) t := by
    intro s
    have h1 := (mem_unitaryCentralizer.mp (specialBlock_le_unitaryCentralizer s.2)).2
    refine Subtype.ext ?_
    apply (GeneralLinearGroup.toLin (n := HypIndex r ε) (R := K)).injective
    change GeneralLinearGroup.toLin (((GeneralLinearGroup.toLin (n := HypIndex r ε)
      (R := K)).symm (Φ1 s)) * (t : GL (HypIndex r ε) K)) = GeneralLinearGroup.toLin
        ((t : GL (HypIndex r ε) K) *
          ((GeneralLinearGroup.toLin (n := HypIndex r ε) (R := K)).symm (Φ1 s)))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hxdef]
    exact Units.ext h1.eq
  refine ⟨Subgroup.map Φ ⊤, ?_, ?_, ?_⟩
  · obtain ⟨u, v, huv⟩ := hquasi.2.2
    have hnt : Nontrivial S := by
      by_contra hS1
      rw [not_nontrivial_iff_subsingleton] at hS1
      have : Subsingleton (S ⧸ Subgroup.center S) :=
        (QuotientGroup.mk'_surjective (Subgroup.center S)).subsingleton
      exact huv (Subsingleton.elim _ _)
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    intro hbot
    have : Φ s ∈ Subgroup.map Φ ⊤ := ⟨s, trivial, rfl⟩
    rw [hbot, Subgroup.mem_bot, ← map_one Φ] at this
    exact hs (hΦinj this)
  · rw [← Subgroup.map_commutator]
    congr 1
    exact hquasi.1.commutator_eq_top
  · rintro g ⟨s, -, rfl⟩
    exact hΦcomm s

end Good

section Stable

variable {f : ℕ} {K : Type} [Field K] [Finite K] {r ε : ℕ}

theorem multiplicity_le_one_of_no_perfect (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (t : hypSU h r ε)
    (hsq : Squarefree (minpoly K
      (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K))))
    (hperf : ∀ V : Subgroup (hypSU h r ε), (∀ w ∈ V, Commute w t) → ⁅V, V⁆ = V → V = ⊥)
    {a : K[X]}
    (ha : a ∈ primaryFactors
      (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K))) :
    primaryMultiplicity
      (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K))
      a ≤ 1 := by
  by_contra hlt
  obtain ⟨W, hW0, hWp, hWc⟩ := exists_perfect_centralizer_hyp h hf t hsq ha (by omega)
  exact hW0 (hperf W hWc hWp)

theorem forall_mulVec_mem_of_no_perfect (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (t : hypSU h r ε)
    (hsq : Squarefree (minpoly K
      (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K))))
    (hperf : ∀ V : Subgroup (hypSU h r ε), (∀ w ∈ V, Commute w t) → ⁅V, V⁆ = V → V = ⊥)
    {W : Submodule K (HypIndex r ε → K)}
    (hWt : ∀ w ∈ W, ((t : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w ∈ W)
    {y : hypSU h r ε} (hy : Commute y t) :
    ∀ w ∈ W, ((y : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w ∈ W := by
  classical
  set x : LinearMap.GeneralLinearGroup K (HypIndex r ε → K) :=
    GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) with hxdef
  have hx : (x : Module.End K (HypIndex r ε → K)) =
      mulVecLin ((t : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) :=
    GeneralLinearGroup.coe_toLin _
  have hWx : ∀ w ∈ W, (x : Module.End K (HypIndex r ε → K)) w ∈ W := by
    intro w hw
    rw [hx]
    exact hWt w hw
  have hcomm : Commute (mulVecLin ((y : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)) (x : Module.End K (HypIndex r ε → K)) := by
    rw [hx]
    show _ * _ = _ * _
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← mulVecLin_mul, ← mulVecLin_mul]
    have := congrArg (fun g : hypSU h r ε => ((g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)) hy.eq
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    rw [this]
  intro w hw
  have hsum : ∑ a ∈ primaryFactors (x : Module.End K (HypIndex r ε → K)),
      primaryProjection (x : Module.End K (HypIndex r ε → K)) a w = w := by
    have := congrArg (fun T : Module.End K (HypIndex r ε → K) => T w)
      (sum_primaryProjection hsq)
    simpa only [LinearMap.sum_apply, Module.End.one_apply] using this
  have hyw : ((y : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w =
      ∑ a ∈ primaryFactors (x : Module.End K (HypIndex r ε → K)),
        mulVecLin ((y : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
          (primaryProjection (x : Module.End K (HypIndex r ε → K)) a w) := by
    rw [← map_sum, hsum]
    rfl
  rw [hyw]
  refine Submodule.sum_mem _ fun a ha => ?_
  have hpa := primaryProjection_mem hsq ha w
  have hpW : primaryProjection (x : Module.End K (HypIndex r ε → K)) a w ∈ W :=
    aeval_mem_of_forall_mem hWx _ hw
  rcases eq_bot_or_le_of_multiplicity_le_one hWx ha
      (multiplicity_le_one_of_no_perfect h hf t hsq hperf ha) with hbot | hle
  · have hmem : primaryProjection (x : Module.End K (HypIndex r ε → K)) a w ∈
        W ⊓ primaryComponent (x : Module.End K (HypIndex r ε → K)) a :=
      Submodule.mem_inf.mpr ⟨hpW, hpa⟩
    rw [hbot, Submodule.mem_bot] at hmem
    rw [hmem, map_zero]
    exact Submodule.zero_mem _
  · exact hle (apply_mem_primaryComponent hcomm hpa)

end Stable

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
