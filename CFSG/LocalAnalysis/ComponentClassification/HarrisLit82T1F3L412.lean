module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L412O
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L412Id
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Twin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SpinCover

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CliffordAlgebra CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Model

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem spinOdd_lemma412_three (hK : Nat.card K = 3) (hn : 3 ≤ n) :
    Lemma412ConclThree (spinGroup (quadOdd n K)) := by
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have h2 := two_ne_zero_of_card_three hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : quadOdd n K ≠ 0 := (nondegenerate_quadOdd n K).ne_zero
  set z := spinGroup.negOne (quadOdd n K) hQ with hz
  have hz2 : orderOf z = 2 :=
    orderOf_eq_prime (by rw [sq]; exact spinGroup.negOne_mul_self _ hQ)
      (spinGroup.negOne_ne_one _ hQ)
  have hZ := center_spinGroup_quadOdd h2 hn
  have hzc : z ∈ center (spinGroup (quadOdd n K)) := hZ ▸ mem_zpowers z
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hrange : (spinAction (quadOdd n K)).range ≤ elementaryGroup (quadOdd n K) :=
    (range_spinAction_quadOdd h2 hn).le
  set F := (oddFrame n K).toHypFrame with hF
  set t := F.longSL2 hij true true (-1) with ht
  have h1 : F.longSL2 hij true false (-1) = z * t := longSL2_neg_one_not F hij hQ true true
  have ht' : F.longSL2 hij true false (-1) = t * z := by
    rw [h1]
    exact (mem_center_iff.mp hzc t).symm
  have hCt : centralizer ({F.longSL2 hij true false (-1)} : Set (spinGroup (quadOdd n K))) =
      centralizer {t} := by
    rw [h1]
    exact centralizer_mul_of_mem_center hzc
  have hO : pPrimeCore 2 ↥(centralizer ({t} : Set (spinGroup (quadOdd n K)))) = ⊥ :=
    pPrimeCore_centralizer_longSL2_three hK hij
  have key : ∀ s : Bool,
      IsSolvableTwoComponentIn (F.longSL2 hij true s).range (centralizer {t}) ∧
        Nonempty (↥(F.longSL2 hij true s).range ⧸ pPrimeCore 2 ↥(F.longSL2 hij true s).range ≃*
          SL(2, ZMod 3)) := by
    intro s
    have hCs : centralizer ({F.longSL2 hij true s (-1)} : Set (spinGroup (quadOdd n K))) =
        centralizer {t} := by
      cases s
      · exact hCt
      · rfl
    have hle := range_longSL2_le_centralizer F hij true s
    have hsn := P54.F3.isSubnormal_range_longSL2_of_odd F hij hodd hrange true s
    rw [hCs] at hle hsn
    have ho : pPrimeCore 2 ↥(F.longSL2 hij true s).range = ⊥ :=
      pPrimeCore_range_sl2_odd hodd _ (longSL2_injective F hij true s)
    have e : ↥(F.longSL2 hij true s).range ⧸ pPrimeCore 2 ↥(F.longSL2 hij true s).range ≃*
        SL(2, ZMod 3) :=
      ((QuotientGroup.quotientMulEquivOfEq ho).trans QuotientGroup.quotientBot).trans
        ((MonoidHom.ofInjective (longSL2_injective F hij true s)).symm.trans
          (LieType.HighestRoot.slEquivSL23 hK))
    refine ⟨⟨hle, hsn, ?_, Or.inr ⟨e⟩⟩, ⟨e⟩⟩
    rw [ho, hO, Subgroup.map_bot, Subgroup.map_bot]
  refine ⟨z, hz2, hZ, t, (F.longSL2 hij true true).range, (F.longSL2 hij true false).range,
    orderOf_longSL2_neg_one F hij hodd true true, ?_, (key true).1, (key false).1, (key true).2,
    (key false).2, map_center_range_sl2_odd hodd _ (longSL2_injective F hij true true), ?_⟩
  · rw [center_spinGroup_quadOdd_eq_ker h2 hn, MonoidHom.mem_ker]
    exact spinAction_longSL2_neg_one_ne_one F hij hodd true true
  · rw [map_center_range_sl2_odd hodd _ (longSL2_injective F hij true false), ht']

end Model

namespace L412

variable {A B : Type} [Group A] [Group B] (e : A ≃* B)

theorem subgroupOf_map_eq (J C : Subgroup A) :
    (J.map e.toMonoidHom).subgroupOf (C.map e.toMonoidHom) =
      (J.subgroupOf C).map (C.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom := by
  ext y
  rw [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨x', hx'C, hx'y⟩ := y.2
    have hxx' : x = x' := e.injective (hxy.trans hx'y.symm)
    exact ⟨⟨x, hxx' ▸ hx'C⟩, hx, Subtype.ext hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem map_pPrimeCore_map (J : Subgroup A) :
    (pPrimeCore 2 ↥(J.map e.toMonoidHom)).map (J.map e.toMonoidHom).subtype =
      ((pPrimeCore 2 ↥J).map J.subtype).map e.toMonoidHom := by
  rw [← pPrimeCore_map_iso 2 (J.equivMapOfInjective e.toMonoidHom e.injective),
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem nonempty_quotient_equiv (J : Subgroup A) :
    Nonempty (↥(J.map e.toMonoidHom) ⧸ pPrimeCore 2 ↥(J.map e.toMonoidHom) ≃*
      ↥J ⧸ pPrimeCore 2 ↥J) :=
  ⟨QuotientGroup.congr _ _ (J.equivMapOfInjective e.toMonoidHom e.injective).symm
    (pPrimeCore_map_iso 2 _)⟩

theorem isSolvableTwoComponentIn_map {J C : Subgroup A} (h : IsSolvableTwoComponentIn J C) :
    IsSolvableTwoComponentIn (J.map e.toMonoidHom) (C.map e.toMonoidHom) := by
  obtain ⟨hJC, hsn, hO, hiso⟩ := h
  obtain ⟨ψ⟩ := nonempty_quotient_equiv e J
  refine ⟨map_mono hJC, ?_, ?_, ?_⟩
  · rw [subgroupOf_map_eq]
    exact hsn.map (C.equivMapOfInjective e.toMonoidHom e.injective).surjective
  · rw [map_pPrimeCore_map, map_pPrimeCore_map, hO]
  · rcases hiso with h | h
    · obtain ⟨ε⟩ := h
      exact Or.inl ⟨ψ.trans ε⟩
    · obtain ⟨ε⟩ := h
      exact Or.inr ⟨ψ.trans ε⟩

end L412

section Transport

variable {A B : Type} [Group A] [Group B] (e : A ≃* B)

include e in
theorem Lemma412ConclThree.map (h : Lemma412ConclThree A) : Lemma412ConclThree B := by
  obtain ⟨z, hz2, hZ, t, J₁, J₂, ht2, htZ, hJ₁, hJ₂, ⟨ε₁⟩, ⟨ε₂⟩, hc₁, hc₂⟩ := h
  obtain ⟨ψ₁⟩ := L412.nonempty_quotient_equiv e J₁
  obtain ⟨ψ₂⟩ := L412.nonempty_quotient_equiv e J₂
  have hC := map_centralizer_singleton_mulEquiv e t
  refine ⟨e z, by rw [MulEquiv.orderOf_eq, hz2], ?_, e t, J₁.map e.toMonoidHom,
    J₂.map e.toMonoidHom, by rw [MulEquiv.orderOf_eq, ht2],
    fun h => htZ ((mem_center_mulEquiv_iff e t).mp h), ?_, ?_, ⟨ψ₁.trans ε₁⟩, ⟨ψ₂.trans ε₂⟩,
    ?_, ?_⟩
  · rw [← map_center_eq e, hZ]
    exact MonoidHom.map_zpowers _ z
  · rw [← hC]
    exact L412.isSolvableTwoComponentIn_map e hJ₁
  · rw [← hC]
    exact L412.isSolvableTwoComponentIn_map e hJ₂
  · rw [map_center_map_mulEquiv, hc₁, MonoidHom.map_zpowers]
    rfl
  · rw [map_center_map_mulEquiv, hc₂, MonoidHom.map_zpowers, map_mul]
    rfl

end Transport

theorem harris82Lemma412Three_holds : Harris82Lemma412Three := by
  intro X _ _ m hm hX
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_spinOdd_three hm hX
  exact Lemma412ConclThree.map e.symm (spinOdd_lemma412_three hK (by omega))

end CFSG.ComponentClassification.HarrisLit.T1
