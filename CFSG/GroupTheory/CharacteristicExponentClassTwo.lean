module

public import CFSG.Goldschmidt.Steps.G56
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PartOne.S9.Planes.SecondCenter

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

theorem le_upperCentralSeries_two_of_card_eq {T : Type*} [Group T] [Finite T] {p : ℕ}
    [Fact p.Prime] (hT : IsPGroup p T) {B Z : Subgroup T} [hB : B.Normal] (hZB : Z ≤ B)
    (hZ : Z ≤ Subgroup.center T) (hcard : Nat.card B = p * Nat.card Z) :
    B ≤ Subgroup.upperCentralSeries T 2 := by
  haveI hZn : Z.Normal := Subgroup.normal_of_le_center hZ
  let π : T →* T ⧸ Z := QuotientGroup.mk' Z
  haveI : Fact (IsPGroup p (T ⧸ Z)) := ⟨hT.to_quotient Z⟩
  haveI : (B.map π).Normal := hB.map π (QuotientGroup.mk'_surjective Z)
  have hcardB' : Nat.card (B.map π) = p := by
    have h := Subgroup.card_ker_mul_card_range (π.domRestrict B)
    rw [MonoidHom.ker_restrict, MonoidHom.restrict_range, QuotientGroup.ker_mk',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv, hcard, mul_comm p] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hcent := CFSG.normal_subgroup_card_eq_prime_le_center (B.map π) hcardB'
  intro b hb
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
  intro y
  rw [Subgroup.upperCentralSeries_one]
  apply hZ
  have h1 : π ⁅b, y⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hcent (Subgroup.mem_map_of_mem π hb)) (π y)).symm
  rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1

theorem omega12_exp_class {T : Type} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hT : IsPGroup p T) :
    (∀ x ∈ Subgroup.closure {x : T | x ∈ Subgroup.upperCentralSeries T 2 ∧ x ^ p = 1},
        x ^ p = 1) ∧
      ⁅⁅Subgroup.closure {x : T | x ∈ Subgroup.upperCentralSeries T 2 ∧ x ^ p = 1},
          Subgroup.closure {x : T | x ∈ Subgroup.upperCentralSeries T 2 ∧ x ^ p = 1}⁆,
        Subgroup.closure {x : T | x ∈ Subgroup.upperCentralSeries T 2 ∧ x ^ p = 1}⁆ = ⊥ := by
  obtain ⟨-, hmem, hcentral, -⟩ :=
    CFSG.RankThree.PartOne.pgOddSecondCenterPrimeTorsion T p hp.out hp2 hT
  refine ⟨fun x hx => ((hmem x).1 hx).2, ?_⟩
  refine CFSG.RankThree.PartOne.Torsion37.commutator_commutator_eq_bot_of_central
    (Q := ⊤) le_top ?_
  intro w hw g _ u _
  exact Subgroup.mem_center_iff.mp (hcentral w hw g).1 u

theorem exists_characteristic_exponent_classTwo_card_ge_cube_type {R : Type} [Group R]
    [Finite R] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hR : IsPGroup p R)
    (h3 : 3 ≤ CFSG.groupRank R) (hnc : ¬ IsCyclic R) :
    ∃ W : Subgroup R, W.Characteristic ∧ (∀ x ∈ W, x ^ p = 1) ∧ ⁅⁅W, W⁆, W⁆ = ⊥ ∧
      p ^ 3 ≤ Nat.card W := by
  classical
  obtain ⟨hchar, hmem, -, hnc1⟩ :=
    CFSG.RankThree.PartOne.pgOddSecondCenterPrimeTorsion R p hp.out hp2 hR
  obtain ⟨hexp1, hcl1⟩ := omega12_exp_class hp2 hR
  set W1 : Subgroup R :=
    Subgroup.closure {x : R | x ∈ Subgroup.upperCentralSeries R 2 ∧ x ^ p = 1} with hW1
  by_cases hbig : p ^ 3 ≤ Nat.card W1
  · exact ⟨W1, hchar, hexp1, hcl1, hbig⟩
  push Not at hbig
  have hW1nc : ¬ IsCyclic W1 := hnc1 hnc
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hR.to_subgroup W1)
  have hk3 : k < 3 := by
    rw [hk] at hbig
    exact (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp hbig
  have hk2 : k = 2 := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with h0 | h1 | h2
    · exfalso
      rw [h0, pow_zero, Nat.card_eq_one_iff_unique] at hk
      haveI := hk.1
      exact hW1nc inferInstance
    · exfalso
      rw [h1, pow_one] at hk
      exact hW1nc (isCyclic_of_prime_card hk)
    · exact h2
  rw [hk2] at hk
  haveI hW1elem : CFSG.IsElementaryAbelian p W1 :=
    { is_comm := ⟨fun a b => IsPGroup.commutative_of_card_eq_prime_sq hk a b⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (hexp1 g.1 g.2) }
  haveI : W1.Characteristic := hchar
  haveI : W1.Normal := inferInstance
  obtain ⟨B, hBn, hBelem, hBcard, hW1B⟩ :=
    CFSG.exists_normal_elementaryAbelian_card_p3_containing_rank_two_normal hp2 hR h3
      (E := W1) ⟨hk, hW1elem⟩
  haveI := hBelem
  set C : Subgroup R := Subgroup.centralizer (W1 : Set R) with hC
  haveI : C.Characteristic := Subgroup.characteristic_centralizer
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBelem.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBC : B ≤ C := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => hBcomm w (hW1B hw) b hb
  have hW1C : W1 ≤ C := hW1B.trans hBC
  have hCp : IsPGroup p C := hR.to_subgroup C
  haveI : (B.subgroupOf C).Normal := hBn.subgroupOf C
  have hZBC : W1.subgroupOf C ≤ B.subgroupOf C := fun _ hx => hW1B hx
  have hZcent : W1.subgroupOf C ≤ Subgroup.center C := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp c.2 (z : R) hz).symm
  have hcardBC : Nat.card (B.subgroupOf C) = p * Nat.card (W1.subgroupOf C) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1C).toEquiv, hBcard, hk]
    ring
  have hB2 := le_upperCentralSeries_two_of_card_eq hCp hZBC hZcent hcardBC
  obtain ⟨hchar2, hmem2, -, -⟩ :=
    CFSG.RankThree.PartOne.pgOddSecondCenterPrimeTorsion C p hp.out hp2 hCp
  obtain ⟨hexp2, hcl2⟩ := omega12_exp_class hp2 hCp
  set W2 : Subgroup C :=
    Subgroup.closure {x : C | x ∈ Subgroup.upperCentralSeries C 2 ∧ x ^ p = 1} with hW2
  haveI : W2.Characteristic := hchar2
  have hBW2 : B.subgroupOf C ≤ W2 := fun b hb =>
    (hmem2 b).mpr ⟨hB2 hb, Subtype.ext (CFSG.elemPow_eq_one_of_isElementaryAbelian (A := B)
      (b : R) hb)⟩
  refine ⟨W2.map C.subtype, inferInstance, ?_, ?_, ?_⟩
  · rintro x ⟨w, hw, rfl⟩
    simpa using congrArg C.subtype (hexp2 w hw)
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hcl2, Subgroup.map_bot]
  · rw [Subgroup.card_subtype, ← hBcard,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv]
    exact Subgroup.card_le_of_le hBW2

theorem exists_characteristic_exponent_classTwo_card_ge_cube
    {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup p P) (h3 : 3 ≤ CFSG.Open.pRank p P) :
    ∃ X : Subgroup G, X ≤ P ∧ (X.subgroupOf P).Characteristic ∧
      (∀ x ∈ X, x ^ p = 1) ∧ ⁅⁅X, X⁆, X⁆ = ⊥ ∧ p ^ 3 ≤ Nat.card X := by
  obtain ⟨K, hKP, -, hKelem, hKcard⟩ :=
    CFSG.Goldschmidt.G55.exists_normal_isElemAbelian hp.out hp2 hP h3
  haveI hKe : CFSG.IsElementaryAbelian p (K.subgroupOf P) :=
    { is_comm := ⟨fun a b => by
        have key : ((a : P) : G) * ((b : P) : G) = ((b : P) : G) * ((a : P) : G) :=
          congrArg Subtype.val
            (hKelem.1.is_comm.comm (⟨((a : P) : G), a.2⟩ : K) ⟨((b : P) : G), b.2⟩)
        exact Subtype.ext (Subtype.ext key)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (Subtype.ext (hKelem.2 _ g.2)) }
  have hRk : 3 ≤ CFSG.groupRank P :=
    CFSG.groupRank_at_least_three_of_elementaryAbelian_subgroup_card_p3' (p := p)
      (B := K.subgroupOf P)
      ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv).trans hKcard)
  have hnc : ¬ IsCyclic P := fun hcyc => by
    have := CFSG.SectionRank.pRank_le_one_of_isCyclic hp.out hcyc
    omega
  obtain ⟨W, hWchar, hWexp, hWcl, hWcard⟩ :=
    exists_characteristic_exponent_classTwo_card_ge_cube_type hp2 hP hRk hnc
  refine ⟨W.map P.subtype, Subgroup.map_subtype_le W, ?_, ?_, ?_, ?_⟩
  · have hW : (W.map P.subtype).subgroupOf P = W :=
      Subgroup.comap_map_eq_self_of_injective P.subtype_injective W
    rw [hW]
    exact hWchar
  · rintro x ⟨w, hw, rfl⟩
    simpa using congrArg P.subtype (hWexp w hw)
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hWcl, Subgroup.map_bot]
  · rw [Subgroup.card_subtype]
    exact hWcard

end CFSG.GroupTheory
