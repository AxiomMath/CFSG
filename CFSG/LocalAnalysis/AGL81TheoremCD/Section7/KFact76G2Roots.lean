module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.OddSplitGenerationFinal
import CFSG.LieType.Chevalley.WeylRootTransport
import CFSG.LieType.Chevalley.Braid

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
  CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
open scoped commutatorElement

abbrev sCw : WeylGroup .G2 := sA * sR * sA * sR * sA

theorem sCw_r : sCw • gR = gR := by
  rw [mul_smul, mul_smul, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul, simple_smul,
    simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem sCw_b : sCw • gB = -gA := by
  rw [mul_smul, mul_smul, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul, simple_smul,
    simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem sCw_c : sCw • gC = -gC := by
  rw [mul_smul, mul_smul, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul, simple_smul,
    simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem sA_a : sA • gA = -gA := by
  rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)

theorem sR_r : sR • gR = -gR := by
  rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)

theorem sRCw_r : (sR * sCw) • gR = -gR := by rw [mul_smul, sCw_r, sR_r]

theorem sRCw_c : (sR * sCw) • gC = -gC := by
  rw [mul_smul, sCw_c, smul_neg, simple_smul]; exact List.ofFn_injective (by decide +kernel)

theorem sRA_a : (sR * sA) • gA = -gB := by
  rw [mul_smul, simple_smul, simple_smul]; exact List.ofFn_injective (by decide +kernel)

theorem sRA_c : (sR * sA) • gC = gA := by
  rw [mul_smul, simple_smul, simple_smul]; exact List.ofFn_injective (by decide +kernel)

variable {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

theorem conj_torusElt_iA (ν : Kˣ) :
    weylElt .G2 K iA 1 * weylElt .G2 K iR 1 * torusElt .G2 K iA ν *
        (weylElt .G2 K iA 1 * weylElt .G2 K iR 1)⁻¹ =
      torusElt .G2 K iA (ν ^ 2) * torusElt .G2 K iR ν := by
  have e1 := weylElt_one_mul_torusElt_mul_inv .G2 K iR iA ν
  have e2 := weylElt_one_mul_torusElt_mul_inv .G2 K iA iA ν
  have e3 := weylElt_one_mul_torusElt_mul_inv .G2 K iA iR ν
  have c1 : Tag.G2.cartan iA iR = -1 := by decide
  have c2 : Tag.G2.cartan iA iA = 2 := by decide
  have c3 : Tag.G2.cartan iR iA = -3 := by decide
  rw [c1, neg_neg, zpow_one] at e1
  rw [c2] at e2
  rw [c3, neg_neg] at e3
  have hν : ν * ν ^ (-2 : ℤ) * ν ^ (3 : ℤ) = ν ^ 2 := by group
  calc _ = weylElt .G2 K iA 1 * (weylElt .G2 K iR 1 * torusElt .G2 K iA ν *
          (weylElt .G2 K iR 1)⁻¹) * (weylElt .G2 K iA 1)⁻¹ := by group
    _ = (weylElt .G2 K iA 1 * torusElt .G2 K iA ν * (weylElt .G2 K iA 1)⁻¹) *
          (weylElt .G2 K iA 1 * torusElt .G2 K iR ν * (weylElt .G2 K iA 1)⁻¹) := by
        rw [e1]; group
    _ = torusElt .G2 K iA ν * torusElt .G2 K iA (ν ^ (-2 : ℤ)) *
          (torusElt .G2 K iR ν * torusElt .G2 K iA (ν ^ (3 : ℤ))) := by rw [e2, e3]
    _ = torusElt .G2 K iA (ν * ν ^ (-2 : ℤ) * ν ^ (3 : ℤ)) * torusElt .G2 K iR ν := by
        rw [torusElt_mul_comm iR iA, torusElt_mul, torusElt_mul]; group
    _ = _ := by rw [hν]

theorem commute_r_negC (t s : K) : Commute (X gR t) (X (-gC) s) :=
  commute_pinnedX_of_nil (τ := .G2) (r := ((6, 11, 12, []) : PairRow)) (by decide) rfl sCw
    (by rw [pos6]; exact sCw_r) (by rw [pos11]; exact sCw_c) t s

theorem commute_r_negA (t s : K) : Commute (X gR t) (X (-gA) s) :=
  commute_pinnedX_of_nil (τ := .G2) (r := ((6, 10, 12, []) : PairRow)) (by decide) rfl sCw
    (by rw [pos6]; exact sCw_r) (by rw [pos10]; exact sCw_b) t s

theorem commute_negR_negC (t s : K) : Commute (X (-gR) t) (X (-gC) s) :=
  commute_pinnedX_of_nil (τ := .G2) (r := ((6, 11, 12, []) : PairRow)) (by decide) rfl (sR * sCw)
    (by rw [pos6]; exact sRCw_r) (by rw [pos11]; exact sRCw_c) t s

theorem commute_negA_v (t s : K) : Commute (X (-gA) t) (X gV s) :=
  commute_pinnedX_of_nil (τ := .G2) (r := ((7, 9, 12, []) : PairRow)) (by decide) rfl sA
    (by rw [pos7]; exact sA_a) (by rw [pos9]; exact sA_v) t s

theorem commute_negA_b (t s : K) : Commute (X (-gA) t) (X gB s) :=
  commute_pinnedX_of_nil (τ := .G2) (r := ((7, 11, 12, []) : PairRow)) (by decide) rfl sA
    (by rw [pos7]; exact sA_a) (by rw [pos11]; exact sA_c) t s

theorem comm_negA_c : ∃ ε : K, ε * ε = 1 ∧ ∀ x y : K,
    ⁅X (-gA) x, X gC y⁆ = X gB (ε * x * y) := by
  obtain ⟨εf, hε, h⟩ := commutatorElement_pinnedX_signed (τ := .G2)
    (r := (7, 10, 12, [(1, 1, 11, 1)])) (by decide) sA
  refine ⟨((εf (1, 1, 11, 1) : ℤ) : K), ?_, fun x y => ?_⟩
  · rcases hε (1, 1, 11, 1) with he | he <;> simp [he]
  · have := @h K _ (-gA) gC (by rw [pos7]; exact sA_a) (by rw [pos10]; exact sA_b) x y
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pos11,
      sA_c] at this
    simpa using this

theorem comm_negB_c : ∃ ε : K, ε * ε = 1 ∧ ∀ x y : K,
    ⁅X (-gB) x, X gC y⁆ = X gA (ε * x * y) := by
  obtain ⟨εf, hε, h⟩ := commutatorElement_pinnedX_signed (τ := .G2)
    (r := (7, 10, 12, [(1, 1, 11, 1)])) (by decide) (sR * sA)
  refine ⟨((εf (1, 1, 11, 1) : ℤ) : K), ?_, fun x y => ?_⟩
  · rcases hε (1, 1, 11, 1) with he | he <;> simp [he]
  · have := @h K _ (-gB) gC (by rw [pos7]; exact sRA_a) (by rw [pos10]; exact sRA_b) x y
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pos11,
      sRA_c] at this
    simpa using this

theorem weylElt_iA_mem (t : Kˣ) :
    weylElt .G2 K iA t ∈ Subgroup.closure (Set.range (X gA) ∪ Set.range (X (-gA))) := by
  rw [weylElt_eq_xUnit_mul, xUnit_iA, yUnit_iA]
  exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
    (Subgroup.subset_closure (Or.inr ⟨_, rfl⟩))) (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))

theorem weylElt_iR_mem (t : Kˣ) :
    weylElt .G2 K iR t ∈ Subgroup.closure (Set.range (X gR) ∪ Set.range (X (-gR))) := by
  rw [weylElt_eq_xUnit_mul, xUnit_iR, yUnit_iR]
  exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
    (Subgroup.subset_closure (Or.inr ⟨_, rfl⟩))) (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))

theorem torusElt_iA_mem (t : Kˣ) :
    torusElt .G2 K iA t ∈ Subgroup.closure (Set.range (X gA) ∪ Set.range (X (-gA))) :=
  mul_mem (weylElt_iA_mem t) (weylElt_iA_mem (-1))

theorem torusElt_iR_mem (t : Kˣ) :
    torusElt .G2 K iR t ∈ Subgroup.closure (Set.range (X gR) ∪ Set.range (X (-gR))) :=
  mul_mem (weylElt_iR_mem t) (weylElt_iR_mem (-1))

theorem zr_mem : zr K ∈ Subgroup.closure (Set.range (X gR) ∪ Set.range (X (-gR))) := by
  unfold zr
  rw [xUnit_iR]
  exact mul_mem (weylElt_iR_mem 1) (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max
