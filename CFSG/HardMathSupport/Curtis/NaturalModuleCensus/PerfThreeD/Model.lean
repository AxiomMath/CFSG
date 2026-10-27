module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentLift
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open Module QuadraticMap CFSG.AGLEmbedding.ToralCensus CFSG.RankThree.PartOne.KCOrthogonal

@[expose] def PerfThreeCent {X : Type*} [Group X] (v : X) : Prop :=
  ∃ P : Subgroup X, P ≤ Subgroup.centralizer ({v} : Set X) ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P

theorem PerfThreeCent.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {v : G}
    (h : PerfThreeCent (e v)) : PerfThreeCent v := by
  obtain ⟨P, hPc, hP, hP3⟩ := h
  refine ⟨P.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    have := Subgroup.mem_centralizer_singleton_iff.mp (hPc hp)
    simpa using this
  · rw [← Subgroup.map_commutator, hP]
  · rw [← Nat.card_congr
      (Subgroup.equivMapOfInjective P e.symm.toMonoidHom e.symm.injective).toEquiv]
    exact hP3

section Derived

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem perfThreeCent_orthDerived (hQ : (polarBilin Q).Nondegenerate)
    (a : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (ha3 : a ^ 3 = 1)
    (hPT : OddOrderIsometry Q 3 (a : V ≃ₗ[K] V) → PerfectThreeIn (isometryCentralizer Q a)) :
    PerfThreeCent a := by
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    norm_num
  have hx : OddOrderIsometry Q 3 (a : V ≃ₗ[K] V) :=
    ⟨Subgroup.commutator_le_self _ a.2, by rw [← Subgroup.coe_pow, ha3, Subgroup.coe_one], h3K,
      fun v hv => hQ.1 v hv⟩
  obtain ⟨W, hWC, hW, x, hxW, hx3, hx1⟩ := hPT hx
  have hWO : W ≤ TauCeti.QuadraticMap.orthogonalGroup Q := hWC.trans inf_le_left
  have hWD : W ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := hW ▸ Subgroup.commutator_mono hWO hWO
  refine ⟨W.subgroupOf _, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    have hy' := (mem_isometryCentralizer.1 (hWC hy)).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (LinearEquiv.ext fun v => hy' v)
  · apply Subgroup.map_injective (Subgroup.subtype_injective _)
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hWD, hW]
  · have hxD : (⟨x, hWD hxW⟩ :
        ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) ∈
        W.subgroupOf _ := hxW
    have h1 : orderOf (⟨x, hWD hxW⟩ :
        ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) = 3 := by
      refine orderOf_eq_prime ?_ ?_
      · exact Subtype.ext hx3
      · intro h
        exact hx1 (congrArg Subtype.val h)
    rw [← h1]
    exact Subgroup.orderOf_dvd_natCard _ hxD

end Derived

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
