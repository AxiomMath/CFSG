module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PairedBlock
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.DualPoly

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.AGLEmbedding.UnitaryLevi CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary Matrix Polynomial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

omit [Finite K] [CharP K 2] in
theorem exists_perfect_centralizer_of_good_block (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (t : StatedSU n (2 ^ f) K)
    (hsq : Squarefree (minpoly K (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    {a : K[X]}
    (ha : a ∈ primaryFactors (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hm : 2 ≤ primaryMultiplicity
      (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a)
    (hexc : dualPoly (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf).bar a = a →
      (primaryMultiplicity (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a,
        2 ^ (f * a.natDegree)) ∉ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ))) :
    ∃ W : Subgroup (StatedSU n (2 ^ f) K), W ≠ ⊥ ∧ ⁅W, W⁆ = W ∧ ∀ w ∈ W, Commute w t := by
  classical
  have h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  have := h.finite
  set x : LinearMap.GeneralLinearGroup K (Fin n → K) :=
    GeneralLinearGroup.toLin (t : GL (Fin n) K) with hxdef
  have hxSU : x ∈ sesqSpecialUnitaryGroup (stdHermForm h n) := by
    rw [stdHermForm_eq_gramForm, hxdef, toLin_mem_sesqSpecialUnitaryGroup_iff,
      ← unitarySU_eq_gramSU h]
    exact t.2
  have hx : (x : Module.End K (Fin n → K)) =
      mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    GeneralLinearGroup.coe_toLin _
  rw [← hx] at hsq ha hm hexc
  have H : UnitaryPrimaryData h.bar (stdHermForm h n) x :=
    ⟨fun c => h.bar_bar c, stdHermForm_isSymm h n, stdHermForm_separatingLeft h n,
      sesqSpecialUnitaryGroup_le _ hxSU, hsq⟩
  have hq2 : 2 ≤ 2 ^ f := by
    have : 1 < 2 ^ f := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hgood : IsGoodBlock h x ⟨a, ha⟩ := ⟨hm, hexc⟩
  have hfacts := specialBlockFacts_of_good H hq2 ⟨a, ha⟩ hgood
  have hquasi := hfacts.quasisimple hm
  have hle : specialBlock (stdHermForm h n) x a ≤ sesqSpecialUnitaryGroup (stdHermForm h n) :=
    specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq2 ⟨a, ha⟩ hgood
  set S := specialBlock (stdHermForm h n) x a with hS
  let Φ1 : S →* LinearMap.GeneralLinearGroup K (Fin n → K) := S.subtype
  let Φ : S →* StatedSU n (2 ^ f) K :=
    ((GeneralLinearGroup.toLin (n := Fin n) (R := K)).symm.toMonoidHom.comp Φ1).codRestrict
      (StatedSU n (2 ^ f) K) (fun s => toStatedSU_mem hK hf (hle s.2))
  have hΦinj : Function.Injective Φ := by
    intro M N hMN
    have h1 : Φ1 M = Φ1 N := by
      have := congrArg (fun g : StatedSU n (2 ^ f) K => (g : GL (Fin n) K)) hMN
      exact (GeneralLinearGroup.toLin (n := Fin n) (R := K)).symm.injective this
    exact Subtype.ext h1
  have hΦcomm : ∀ s : S, Commute (Φ s) t := by
    intro s
    have h1 := (mem_unitaryCentralizer.mp (specialBlock_le_unitaryCentralizer s.2)).2
    refine Subtype.ext ?_
    apply (GeneralLinearGroup.toLin (n := Fin n) (R := K)).injective
    change GeneralLinearGroup.toLin (((GeneralLinearGroup.toLin (n := Fin n) (R := K)).symm
      (Φ1 s)) * (t : GL (Fin n) K)) = GeneralLinearGroup.toLin ((t : GL (Fin n) K) *
        ((GeneralLinearGroup.toLin (n := Fin n) (R := K)).symm (Φ1 s)))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hxdef]
    exact Units.ext h1.eq
  have hnt : Nontrivial S := by
    obtain ⟨u, v, huv⟩ := hquasi.2.2
    by_contra hS1
    rw [not_nontrivial_iff_subsingleton] at hS1
    have : Subsingleton (S ⧸ Subgroup.center S) :=
      (QuotientGroup.mk'_surjective (Subgroup.center S)).subsingleton
    exact huv (Subsingleton.elim _ _)
  refine ⟨Subgroup.map Φ ⊤, ?_, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := exists_ne (1 : S)
    intro hbot
    have : Φ s ∈ Subgroup.map Φ ⊤ := ⟨s, trivial, rfl⟩
    rw [hbot, Subgroup.mem_bot, ← map_one Φ] at this
    exact hs (hΦinj this)
  · rw [← Subgroup.map_commutator]
    congr 1
    exact hquasi.1.commutator_eq_top
  · rintro g ⟨s, -, rfl⟩
    exact hΦcomm s

end CFSG.HardMathSupport.Curtis.UnitaryLevi
