module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutTab47

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.M23Std

theorem card_isConj_mul_card_centralizer {G : Type*} [Group G] [Finite G] (μ : G) :
    Nat.card {ν : G // IsConj ν μ} * Nat.card (centralizer ({μ} : Set G)) = Nat.card G := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) μ
  rw [ConjAct.card] at h
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
  simp only [Nat.card_eq_fintype_card]
  have e : Fintype.card {ν : G // IsConj ν μ} = Fintype.card (MulAction.orbit (ConjAct G) μ) :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun ν => ConjAct.mem_orbit_conjAct.symm)
  rw [e]
  exact h

theorem card_centralizer_eq_of_isConj {G : Type*} [Group G] [Finite G] {μ ν : G} (h : IsConj ν μ) :
    Nat.card (centralizer ({ν} : Set G)) = Nat.card (centralizer ({μ} : Set G)) := by
  have e : {x : G // IsConj x ν} ≃ {x : G // IsConj x μ} :=
    Equiv.subtypeEquivRight fun x => ⟨fun hx => hx.trans h, fun hx => hx.trans h.symm⟩
  have h1 := card_isConj_mul_card_centralizer ν
  have h2 := card_isConj_mul_card_centralizer μ
  rw [Nat.card_congr e] at h1
  have hpos : 0 < Nat.card {x : G // IsConj x μ} :=
    Nat.card_pos_iff.2 ⟨⟨⟨μ, IsConj.refl μ⟩⟩, inferInstance⟩
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

variable
  {F1 : Subgroup (Carrier .M22)}
  (hF : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)

include hF

theorem mem_invClass_of_isConj {c f : ℕ} {μ ν : ↥(autNorm F1)} (hμ : μ ∈ InvClass F1 c f)
    (hνμ : IsConj ν μ) : ν ∈ InvClass F1 c f := by
  obtain ⟨h1, h2, hc, hf⟩ := hμ
  obtain ⟨g, hg⟩ := isConj_iff.1 hνμ
  have hν : ν = g⁻¹ * μ * g := by
    rw [← hg]
    group
  have : Finite ↥(autNorm F1) := Nat.finite_of_card_ne_zero
    (by rw [card_normalizer_innerImage hF (nData_pinned hF)]; norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hν]
    calc g⁻¹ * μ * g * (g⁻¹ * μ * g) = g⁻¹ * (μ * μ) * g := by group
      _ = 1 := by rw [h1]; group
  · intro h
    apply h2
    have : μ = g * ν * g⁻¹ := by rw [hν]; group
    rw [this, h]
    group
  · rw [card_centralizer_eq_of_isConj hνμ]
    exact hc
  · rw [← hf]
    have hmem : ∀ y, y ∈ F1 ↔ (g : MulAut (Carrier .M22)) y ∈ F1 :=
      (mem_normalizer_innerImage_iff conj_injective_m22).1 g.2
    have key : ∀ y, (ν : MulAut (Carrier .M22)) y = y ↔
        (μ : MulAut (Carrier .M22)) ((g : MulAut (Carrier .M22)) y) =
          (g : MulAut (Carrier .M22)) y := by
      intro y
      have hνe : (ν : MulAut (Carrier .M22)) = (g : MulAut (Carrier .M22))⁻¹ * μ * g := by
        rw [hν]
        rfl
      rw [hνe]
      simp only [MulAut.mul_apply]
      constructor
      · intro h
        have := congrArg (g : MulAut (Carrier .M22)) h
        rwa [MulAut.apply_inv_self] at this
      · intro h
        rw [h, MulAut.inv_apply_self]
    refine Nat.card_congr
      { toFun := fun y => ⟨(g : MulAut (Carrier .M22)) y.1, (hmem y.1).1 y.2.1, (key y.1).1 y.2.2⟩
        invFun := fun z => ⟨(g : MulAut (Carrier .M22))⁻¹ z.1, ?_, ?_⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun z => Subtype.ext (by simp) }
    · rw [hmem, MulAut.apply_inv_self]
      exact z.2.1
    · rw [key, MulAut.apply_inv_self]
      exact z.2.2

theorem normalizer_involution_isConj {c f n : ℕ} (hcfn : (c, f, n) ∈ classTable)
    {μ ν : ↥(autNorm F1)} (hμ : μ ∈ InvClass F1 c f) (hν : ν ∈ InvClass F1 c f) : IsConj ν μ := by
  have hN : Nat.card ↥(autNorm F1) = 11520 := card_normalizer_innerImage hF (nData_pinned hF)
  have : Finite ↥(autNorm F1) := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  have hn : Nat.card (InvClass F1 c f) = n := by
    rw [card_invClass hF]
    obtain ⟨-, -, -, -, -, -, hcls⟩ := censusCheck_spec Certificates.certificate24790
    exact hcls (c, f, n) hcfn
  have hcn : n * c = 11520 ∧ 0 < c := by
    simp only [classTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hcfn
    rcases hcfn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ <;> norm_num
  have hsub : {x : ↥(autNorm F1) | IsConj x μ} ⊆ InvClass F1 c f := fun x hx =>
    mem_invClass_of_isConj hF hμ hx
  have hcl : ({x : ↥(autNorm F1) | IsConj x μ}).ncard = n := by
    have h := card_isConj_mul_card_centralizer μ
    rw [hN, hμ.2.2.1] at h
    have h2 : Nat.card {x : ↥(autNorm F1) // IsConj x μ} = n := by
      refine Nat.eq_of_mul_eq_mul_right hcn.2 ?_
      rw [h, hcn.1]
    rw [← h2]
    exact (Nat.card_coe_set_eq _).symm
  have hS : (InvClass F1 c f).ncard = n := by
    rw [← hn]
    exact (Nat.card_coe_set_eq _).symm
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hS, hcl]) (Set.toFinite _)
  have : ν ∈ {x : ↥(autNorm F1) | IsConj x μ} := by rw [heq]; exact hν
  exact this

end CFSG.EvenSporadicStandard.M22Std
