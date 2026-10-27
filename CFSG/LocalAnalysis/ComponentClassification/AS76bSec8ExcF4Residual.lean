module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4Classes
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcSub

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.F4Sec8

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.SeitzReduction
open CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover (xr coe_commutatorElement_adjoint)
open CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open scoped commutatorElement

section Generic

variable {C : Type*} [Group C]

def OddCommWitness (x : C) : Prop :=
  ∃ P : Subgroup C, IsPGroup 2 P ∧ P ≤ closure {c | c * x = x * c ∧ Odd (orderOf c)} ∧
    x ∈ ⁅P, P⁆

theorem residualMem_of_witness {x : C} (h : OddCommWitness x) : ResidualMem x := by
  obtain ⟨P, hP, hPx, hx⟩ := h
  have h1 : closure {c : C | c * x = x * c ∧ Odd (orderOf c)} ≤ oUpperTwo (cent x) :=
    closure_mono fun c hc => ⟨mem_centralizer_singleton_iff.2 hc.1, hc.2⟩
  exact commutator_le_admResidual_of_isPGroup (hPx.trans (h1.trans le_sup_left)) hP hx

theorem map_closure_odd_le (α : MulAut C) (x : C) :
    (closure {c | c * x = x * c ∧ Odd (orderOf c)}).map α.toMonoidHom ≤
      closure {c | c * α x = α x * c ∧ Odd (orderOf c)} := by
  rw [MonoidHom.map_closure]
  refine closure_mono ?_
  rintro _ ⟨c, ⟨hc, hodd⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, hc, map_mul]
  · simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] using hodd

theorem OddCommWitness.map {x : C} (h : OddCommWitness x) (α : MulAut C) :
    OddCommWitness (α x) := by
  obtain ⟨P, hP, hPx, hx⟩ := h
  refine ⟨P.map α.toMonoidHom, hP.map _, (map_mono hPx).trans (map_closure_odd_le α x), ?_⟩
  rw [← map_commutator]
  exact mem_map_of_mem _ hx

theorem OddCommWitness.of_isConj {x y : C} (h : OddCommWitness x) (hxy : IsConj x y) :
    OddCommWitness y := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
  exact h.map (MulAut.conj c)

end Generic


section Witnesses

variable {K : Type} [Field K]

theorem isPGroup_closure_f4Rep
    [Finite K] [CharP K 2] {S : Set ℕ} (hS : ∀ p ∈ S, 24 ≤ p ∧ p ≤ 47) :
    IsPGroup 2 (closure ((fun p => f4Rep K [p]) '' S)) := by
  refine ((isPGroup_posUnipotent (K := K) 2 .F4).comap_subtype
    (K := adjointGroup .F4 K)).to_le ?_
  rw [closure_le]
  rintro _ ⟨p, hp, rfl⟩
  change (f4Rep K [p] : ModGL .F4 K) ∈ posUnipotent .F4 K
  rw [coe_f4Rep_singleton]
  exact f4x_mem_posUnipotent (hS p hp) 1

theorem f4Rep_eq_commutator
    {i j k : ℕ} (h : f4x K k 1 = ⁅f4x K i 1, f4x K j 1⁆) :
    f4Rep K [k] = ⁅f4Rep K [i], f4Rep K [j]⁆ :=
  Subtype.ext (by rw [coe_commutatorElement_adjoint, coe_f4Rep_singleton, coe_f4Rep_singleton,
    coe_f4Rep_singleton, h])

theorem f4Rep_singleton_eq (p : ℕ) :
    f4Rep K [p] = ⟨f4x K p 1, pinnedX_mem_adjointGroup _ _⟩ :=
  Subtype.ext (coe_f4Rep_singleton p)

theorem xr_eq_f4Rep (p : ℕ) :
    xr (K := K) (orbitCertRoot .F4 p) = f4Rep K [p] :=
  Subtype.ext (by rw [coe_f4Rep_singleton]; rfl)

theorem exists_card_eq_two_pow [Finite K] [CharP K 2] :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card K = 2 ^ n := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem oddCommWitness_t
    [Finite K] [CharP K 2] : OddCommWitness (f4Rep K [47]) := by
  obtain ⟨n, hn1, hK⟩ := exists_card_eq_two_pow (K := K)
  have hS : ∀ p ∈ ({33, 46} : Set ℕ), 24 ≤ p ∧ p ≤ 47 := by
    rintro p (rfl | rfl) <;> norm_num
  refine ⟨_, isPGroup_closure_f4Rep hS, ?_, ?_⟩
  · rw [closure_le]
    rintro _ ⟨p, hp, rfl⟩
    beta_reduce
    rw [f4Rep_singleton_eq p]
    rcases (show n = 1 ∨ 2 ≤ n by omega) with h1 | hf
    · have hK2 : Nat.card K = 2 := by rw [hK, h1, pow_one]
      have h := posUnipotent_le_closure_odd_longRoot_two hK2
        (u := ⟨f4x K p 1, pinnedX_mem_adjointGroup _ _⟩) (f4x_mem_posUnipotent (hS p hp) 1)
      rwa [xr_eq_f4Rep] at h
    · refine f4x_mem_closure_odd_of_two_le hf hK (fun u hu => ?_) (fun a h47 _ ha => ?_)
        (hS p hp) 1
      · refine Subtype.ext ?_
        simp only [Subgroup.coe_mul, coe_f4Rep_singleton]
        exact f4x_central (Or.inr rfl) 1 hu
      · refine Subtype.ext ?_
        simp only [Subgroup.coe_mul, coe_f4Rep_singleton, f4x]
        exact rootDiagUnit_commute_pinnedX_one (f4_isRoot_pos ⟨by norm_num, by norm_num⟩).1 h47
  · rw [f4Rep_eq_commutator (CFSG.Monster.B.GSide.f4x_47_eq_commutator 1)]
    exact commutator_mem_commutator (subset_closure ⟨33, Or.inl rfl, rfl⟩)
      (subset_closure ⟨46, Or.inr rfl, rfl⟩)

theorem oddCommWitness_u
    [Finite K] [CharP K 2] : OddCommWitness (f4Rep K [44]) := by
  have h := (oddCommWitness_t (K := K)).map (f4DescPhi K)
  rwa [(phi_f4Rep_classes (K := K)).1] at h

theorem oddCommWitness_tu
    [Finite K] [CharP K 2] : OddCommWitness (f4Rep K [47, 44]) := by
  obtain ⟨n, hn1, hK⟩ := exists_card_eq_two_pow (K := K)
  have hS : ∀ p ∈ ({33, 46, 24, 43} : Set ℕ), 24 ≤ p ∧ p ≤ 47 := by
    rintro p (rfl | rfl | rfl | rfl) <;> norm_num
  have e : f4Rep K [47, 44] = xr (orbitCertRoot .F4 47) * xr (orbitCertRoot .F4 44) := by
    rw [xr_eq_f4Rep, xr_eq_f4Rep, f4Rep_pair]
  refine ⟨_, isPGroup_closure_f4Rep hS, ?_, ?_⟩
  · rw [closure_le]
    rintro _ ⟨p, hp, rfl⟩
    beta_reduce
    rw [f4Rep_singleton_eq p]
    rcases (show n = 1 ∨ 2 ≤ n by omega) with h1 | hf
    · have hK2 : Nat.card K = 2 := by rw [hK, h1, pow_one]
      have hR : p ∈ f4MidRadical := by
        rcases hp with rfl | rfl | rfl | rfl <;> decide
      rw [e]
      exact parabolicRadical_mid_le_closure_odd hK2
        (u := ⟨f4x K p 1, pinnedX_mem_adjointGroup _ _⟩) (f4x_mem_parabolicRadical_mid hR 1)
    · refine f4x_mem_closure_odd_of_two_le hf hK (fun u hu => ?_) (fun a h47 h44 ha => ?_)
        (hS p hp) 1
      · refine Subtype.ext ?_
        simp only [Subgroup.coe_mul, coe_f4Rep, f4CollProd_cons, f4CollProd_nil, mul_one]
        rw [← mul_assoc, f4x_central (Or.inr rfl) 1 hu, mul_assoc, f4x_central (Or.inl rfl) 1 hu,
          mul_assoc]
      · refine Subtype.ext ?_
        simp only [Subgroup.coe_mul, coe_f4Rep, f4CollProd_cons, f4CollProd_nil, mul_one]
        rw [← mul_assoc, f4x, rootDiagUnit_commute_pinnedX_one
          (f4_isRoot_pos ⟨by norm_num, by norm_num⟩).1 h47, mul_assoc, f4x,
          rootDiagUnit_commute_pinnedX_one (f4_isRoot_pos ⟨by norm_num, by norm_num⟩).1 h44,
          mul_assoc]
  · rw [f4Rep_pair, f4Rep_eq_commutator (CFSG.Monster.B.GSide.f4x_47_eq_commutator 1),
      f4Rep_eq_commutator (CFSG.Monster.B.GSide.f4x_44_eq_commutator 1)]
    exact mul_mem (commutator_mem_commutator (subset_closure ⟨33, Or.inl rfl, rfl⟩)
        (subset_closure ⟨46, Or.inr (Or.inl rfl), rfl⟩))
      (commutator_mem_commutator (subset_closure ⟨24, Or.inr (Or.inr (Or.inl rfl)), rfl⟩)
        (subset_closure ⟨43, Or.inr (Or.inr (Or.inr rfl)), rfl⟩))

theorem f4Rep_41_45_eq_commutator
    [CharP K 2] :
    f4Rep K [41] = ⁅f4Rep K [29], f4Rep K [35]⁆ ∧ f4Rep K [45] = ⁅f4Rep K [32], f4Rep K [37]⁆ := by
  have h1 := f4x_commutator_eq (K := K) (i := 29) (j := 35) ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (by norm_num) 1 1
  have h2 := f4x_commutator_eq (K := K) (i := 32) (j := 37) ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (by norm_num) 1 1
  have l1 : (f4OddCommutatorFactors.lookup (29, 35)).getD [] = [(1, 1, 41)] := by decide +kernel
  have l2 : (f4OddCommutatorFactors.lookup (32, 37)).getD [] = [(1, 1, 45)] := by decide +kernel
  rw [l1] at h1
  rw [l2] at h2
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow] at h1 h2
  exact ⟨f4Rep_eq_commutator h1.symm, f4Rep_eq_commutator h2.symm⟩

theorem oddCommWitness_v
    [Finite K] [CharP K 2] : OddCommWitness (f4Rep K [41, 45]) := by
  obtain ⟨n, hn1, hK⟩ := exists_card_eq_two_pow (K := K)
  have hS : ∀ p ∈ ({29, 35, 32, 37} : Set ℕ), 24 ≤ p ∧ p ≤ 47 := by
    rintro p (rfl | rfl | rfl | rfl) <;> norm_num
  have e : f4Rep K [41, 45] = ⟨f4x K 41 1 * f4x K 45 1,
      mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩ :=
    Subtype.ext (by simp [coe_f4Rep])
  refine ⟨_, isPGroup_closure_f4Rep hS, ?_, ?_⟩
  · rw [closure_le]
    rintro _ ⟨p, hp, rfl⟩
    beta_reduce
    rw [f4Rep_singleton_eq p, e]
    rcases (show n = 1 ∨ 2 ≤ n by omega) with h1 | hf
    · have hK2 : Nat.card K = 2 := by rw [hK, h1, pow_one]
      have h3 : (3 : ℤ) ≤ height (orbitCertRoot .F4 p) := by
        rcases hp with rfl | rfl | rfl | rfl <;> decide +kernel
      exact heightSeries_three_le_closure_odd_classV_two hK2
        (u := ⟨f4x K p 1, pinnedX_mem_adjointGroup _ _⟩)
        (pinnedX_mem_rootSpan (S := {α | IsRoot .F4 α ∧ 0 < height α ∧ 3 ≤ height α})
          ⟨(f4_isRoot_pos (hS p hp)).1, (f4_isRoot_pos (hS p hp)).2, h3⟩ 1)
    · have hV : p ∈ f4CentListV := by
        rcases hp with rfl | rfl | rfl | rfl <;> decide
      exact f4x_mem_closure_odd_classV hf hK hV 1
  · obtain ⟨h41, h45⟩ := f4Rep_41_45_eq_commutator (K := K)
    rw [f4Rep_pair, h41, h45]
    exact mul_mem (commutator_mem_commutator (subset_closure ⟨29, Or.inl rfl, rfl⟩)
        (subset_closure ⟨35, Or.inr (Or.inl rfl), rfl⟩))
      (commutator_mem_commutator (subset_closure ⟨32, Or.inr (Or.inr (Or.inl rfl)), rfl⟩)
        (subset_closure ⟨37, Or.inr (Or.inr (Or.inr rfl)), rfl⟩))

theorem residualMem_levi
    [Finite K] [CharP K 2] :
    ∀ x ∈ [f4Rep K [32], f4Rep K [31], f4Rep K [32, 31], f4Rep K [28, 32]], ResidualMem x := by
  obtain ⟨c₁, c₂, c₃, c₄⟩ := isConj_f4Rep_levi (K := K)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact residualMem_of_witness (oddCommWitness_t.of_isConj c₁)
  · exact residualMem_of_witness (oddCommWitness_u.of_isConj c₂)
  · exact residualMem_of_witness (oddCommWitness_tu.of_isConj c₃)
  · exact residualMem_of_witness (oddCommWitness_v.of_isConj c₄)

theorem charTwo_of_involution
    [Finite K] [CharP K 2]
    {x : adjointGroup .F4 K} (hx2 : x * x = 1) (hx1 : x ≠ 1) : CharTwo x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hQ2 : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hQ1 : zpowers x ≠ ⊥ := fun h => hx1 (by
    have hx : x ∈ zpowers x := mem_zpowers x
    rw [h] at hx
    exact hx)
  obtain ⟨h, -⟩ := RootWeightDatum.defining_characteristic_root_local_groups_component_free
    (RootWeightDatum.ordinary .F4 : RootWeightDatum K) 2 (zpowers x) hQ2 hQ1
    (centralizer (zpowers x : Set (adjointGroup .F4 K))) (Or.inr rfl)
  have e : centralizer ((zpowers x : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) =
      cent x := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [CharTwo, ← e]
  exact h

end Witnesses

end CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
