module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.Goldschmidt.Steps.G37Quot
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Basic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem typeL2_barOf_of_central {Y P : Type} [Group Y] [Finite Y] [Group P] [Finite P]
    (π : Y →* P) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y)
    (α : MulAut Y) (ψ : MulAut P) (hαψ : ∀ y, π (α y) = ψ (π y))
    {J : Subgroup Y} (hJ : GLAPComponent 3 (fixSubgroup α) J) {r : ℕ}
    (hr : IsTypeL2 r (barOf 3 J)) :
    ∃ A : Subgroup P, GLAPComponent 3 (fixSubgroup ψ) A ∧ IsTypeL2 r (barOf 3 A) := by
  have hA := glaPComponent_map_fixSubgroup π hker α ψ hαψ hπ Nat.prime_three hJ
  refine ⟨J.map π, hA, ?_⟩
  have hJq : CFSG.Open.IsQuasisimple (barOf 3 J) :=
    isQuasisimple_barOf_of_glaPComponent Nat.prime_three hJ
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
  have hkc : f.ker ≤ Subgroup.center (barOf 3 J) := by
    have hJq' : CFSG.IsQuasisimple (barOf 3 J) :=
      ⟨Group.isPerfect_def.2 hJq.1, hJq.2, I923.exists_not_comm_of_quasisimple hJq⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hJq' (f.normal_ker) with h | h
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
    · exact h
  have hperf : Group.IsPerfect (barOf 3 J) := Group.isPerfect_def.2 hJq.1
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hperf f hf hkc
  obtain ⟨F, hF, hFin, hcard, ⟨g⟩⟩ := hr
  exact ⟨F, hF, hFin, hcard, ⟨e.symm.trans g⟩⟩

theorem exists_comp_typeL2_quotient {Y : Type} [Group Y] [Finite Y] (ξ : MulAut Y)
    {J : Subgroup Y} (hJ : GLAPComponent 3 (Lemma510Ns.fixSub ξ) J) {r : ℕ}
    (hr : IsTypeL2 r (barOf 3 J)) :
    ∃ A : Subgroup (Y ⧸ Subgroup.center Y),
      GLAPComponent 3 (Lemma510Ns.fixSub (centerDescend Y ξ)) A ∧ IsTypeL2 r (barOf 3 A) :=
  typeL2_barOf_of_central (QuotientGroup.mk' (Subgroup.center Y))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) ξ (centerDescend Y ξ)
    (fun y => rfl) hJ hr

end CFSG.HardMathSupport.Dickson.Sec6.I1431
