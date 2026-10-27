module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Defs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeClosure
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs CFSG.RankThree.PartTwo.KFacts

theorem isLThreeFour_barOf_of_central {Y P : Type} [Group Y] [Finite Y] [Group P] [Finite P]
    (π : Y →* P) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y)
    (α : MulAut Y) (ψ : MulAut P) (hαψ : ∀ y, π (α y) = ψ (π y))
    {J : Subgroup Y} (hJ : GLAPComponent 3 (fixSubgroup α) J)
    (hr : IsLThreeFour (barOf 3 J)) :
    ∃ A : Subgroup P, GLAPComponent 3 (fixSubgroup ψ) A ∧ IsLThreeFour (barOf 3 A) := by
  have hA := glaPComponent_map_fixSubgroup π hker α ψ hαψ hπ Nat.prime_three hJ
  refine ⟨J.map π, hA, ?_⟩
  have hAq : CFSG.Open.IsQuasisimple (barOf 3 (J.map π)) :=
    isQuasisimple_barOf_of_glaPComponent Nat.prime_three hA
  let φ : ↥J →* ↥(J.map π) := π.subgroupMap J
  have hφ : Function.Surjective φ := π.subgroupMap_surjective J
  let f₀ : ↥J →* barOf 3 (J.map π) := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(J.map π))).comp φ
  have hk : GLAPPrimeCore 3 ↥J ≤ f₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 (map_gLAPPrimeCore_le' 3 φ hφ ⟨x, hx, rfl⟩)
  let f : barOf 3 J →* barOf 3 (J.map π) := QuotientGroup.lift _ f₀ hk
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥(J.map π)) y
    obtain ⟨j, rfl⟩ := hφ a
    exact ⟨QuotientGroup.mk j, rfl⟩
  haveI : IsSimpleGroup (barOf 3 J) := (isSimpleGroup_of_isLThreeFour hr).1
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    haveI := f.normal_ker
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact h
    · exfalso
      have hall : ∀ y : barOf 3 (J.map π), y = 1 := by
        intro y
        obtain ⟨x, rfl⟩ := hf y
        have : x ∈ f.ker := by rw [h]; exact Subgroup.mem_top x
        exact this
      have hsub : Subsingleton (barOf 3 (J.map π)) := ⟨fun a b => (hall a).trans (hall b).symm⟩
      have hs2 : Subsingleton (barOf 3 (J.map π) ⧸ Subgroup.center (barOf 3 (J.map π))) :=
        (QuotientGroup.mk'_surjective (Subgroup.center (barOf 3 (J.map π)))).subsingleton
      exact (not_nontrivial_iff_subsingleton.2 hs2) hAq.2.toNontrivial
  exact IsLThreeFour.of_mulEquiv (MulEquiv.ofBijective f ⟨hinj, hf⟩) hr

theorem isL34Type_of_isLThreeFour {K : Type} [Group K] (h : IsLThreeFour K) :
    CFSG.ComponentClassification.GrSLit.IsL34Type K := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hadm : StatedLieAdmissible .PSL 3 2 2 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hcm : StatedClassicalModel K .PSL 3 2 2 := by
    refine ⟨hadm, ?_⟩
    show ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 2 ^ 2 ∧
      Nonempty (K ≃* StatedProj (StatedSL 3 K'))
    exact ⟨F, hF, hFin, by rw [hcard]; norm_num, ⟨e⟩⟩
  exact Or.inl ⟨by decide, hcm⟩

theorem up34_center_eq_bot_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ Subgroup.center S := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.1 this b).symm)

theorem eq_one_of_centerDescend_eq_one {Q : Type} [Group Q] (hq : CFSG.Open.IsQuasisimple Q)
    {β : MulAut Q} (h : centerDescend Q β = 1) : β = 1 := by
  haveI : Group.IsPerfect Q := ⟨hq.1⟩
  refine eq_one_of_forall_mul_inv_mem_center fun s => ?_
  have h2 := congrArg (fun φ : MulAut (Q ⧸ Subgroup.center Q) => φ (s : Q ⧸ Subgroup.center Q)) h
  simp only [centerDescend_mk, MulAut.one_apply] at h2
  exact QuotientGroup.eq.mp h2.symm

theorem Up34Pumpup.descend {Q : Type} [Group Q] [Finite Q] (hq : CFSG.Open.IsQuasisimple Q)
    {β : MulAut Q} (h : Up34Pumpup Q β) :
    Up34Pumpup (Q ⧸ Subgroup.center Q) (centerDescend Q β) := by
  obtain ⟨hβ3, hβ1, J, hJ, hJ34⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_pow, hβ3, map_one]
  · intro h1
    exact hβ1 (eq_one_of_centerDescend_eq_one hq h1)
  · have hπ : Function.Surjective (QuotientGroup.mk' (Subgroup.center Q)) :=
      QuotientGroup.mk'_surjective _
    have hker : (QuotientGroup.mk' (Subgroup.center Q)).ker ≤ Subgroup.center Q := by
      rw [QuotientGroup.ker_mk']
    exact isLThreeFour_barOf_of_central (QuotientGroup.mk' (Subgroup.center Q)) hπ hker β
      (centerDescend Q β) (fun y => rfl) hJ hJ34

end CFSG.HardMathSupport.Dickson.Sec6
