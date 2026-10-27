module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I155XCov
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I155XIso
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def I155XAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X K : Subgroup G) (x y : G), CFSG.Open.IsKGroup ↥X →
    GLAPComponent p X K → IsChevSimple 2 (PSimple p K) → x ∈ X → x ^ p = 1 → y ^ p = 1 →
    x * y = y * x → y ∉ Subgroup.zpowers x → y ∈ Subgroup.normalizer (K : Set G) →
    x ∈ Subgroup.normalizer (K : Set G) → ¬ CentMod p K x →
    InnDiagOn p (Subgroup.zpowers x) K → FieldOn p y K →
    ∀ J : Subgroup G,
      GLAPComponent p (closureIn K (Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G)) J →
      y ∈ Subgroup.normalizer (J : Set G) → NonInnDiag p y J ∧ ¬ (p = 3 ∧ IsTD4 3 J)

theorem i155At_of_X {G : Type} [Group G] [Finite G] {p : ℕ} (hX : I155XAt G p) :
    I155At G p := by
  intro hp hp2 X K x y hXk hK hKc hxX hxp hyp hcomm hyx hyN hprem J hJ hyJ
  by_cases hP : x ∈ Subgroup.normalizer (K : Set G) ∧ ¬ CentMod p K x
  · left
    obtain ⟨h1, h2⟩ := hprem hP
    exact hX hp hp2 X K x y hXk hK hKc hxX hxp hyp hcomm hyx hyN hP.1 hP.2 h1 h2 J hJ hyJ
  · right
    refine ⟨hP, ?_⟩
    by_cases hxN : x ∈ Subgroup.normalizer (K : Set G)
    · have hcm : CentMod p K x := by
        by_contra h
        exact hP ⟨hxN, h⟩
      have hJ' := hJ
      rw [closureIn_eq_self_of_mem_normalizer hxN] at hJ'
      have hcov : K ≤ J ⊔ centModSubgroup p K := cover_b hp hxp hK hcm hJ'
      have hJK : J ≤ K ⊔ centModSubgroup p K := hJ'.1.trans (inf_le_left.trans le_sup_left)
      exact exists_iso_of_covering hp hK hJ hJK hcov hyN
    · have hcov : K ≤ J ⊔ centModSubgroup p K := cover_c hp hxp hxX hK hxN hJ
      have hJK : J ≤ K ⊔ centModSubgroup p K :=
        hJ.1.trans (inf_le_left.trans (closureIn_le_sup_centMod hp hxp hxX hK hxN))
      exact exists_iso_of_covering hp hK hJ hJK hcov hyN

end CFSG.LocalAnalysis.GLTheoremA.I155X
