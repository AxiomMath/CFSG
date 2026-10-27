module

public import CFSG.FeitThompson.Representations.NormalRestrictionSingleConstituentOrbit
public import CFSG.FeitThompson.Representations.CentralNormalSectionDegreeBound
public import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
import CFSG.FeitThompson.Representations.CentralSubgroupBoundsDegreeSquare
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.EReal.Inv

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexOrder commutatorElement

variable {K : Type*} [Group K] {B D C : Subgroup K}

theorem map_mk'_subgroupOf_le_center_iff [B.Normal] (hDC : D ≤ C) :
    (D.subgroupOf C).map (QuotientGroup.mk' (B.subgroupOf C)) ≤
        Subgroup.center (C ⧸ B.subgroupOf C) ↔ ⁅D, C⁆ ≤ B := by
  rw [map_mk'_le_center_iff]
  constructor
  · intro h
    rw [Subgroup.commutator_le]
    intro d hd c hc
    have h2 := h ⟨d, hDC hd⟩ (Subgroup.mem_subgroupOf.2 hd) ⟨c, hc⟩
    rw [Subgroup.mem_subgroupOf] at h2
    simpa [commutatorElement_def] using h2
  · intro h a ha g
    rw [Subgroup.mem_subgroupOf]
    have h2 := Subgroup.commutator_le.1 h (a : K) (Subgroup.mem_subgroupOf.1 ha) (g : K) g.2
    simpa [commutatorElement_def] using h2

theorem map_mk'_le_centralizer_map_iff [B.Normal] :
    D.map (QuotientGroup.mk' B) ≤
        Subgroup.centralizer (C.map (QuotientGroup.mk' B) : Set (K ⧸ B)) ↔ ⁅D, C⁆ ≤ B := by
  constructor
  · intro h
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hmem := Subgroup.mem_centralizer_iff.1 (h (Subgroup.mem_map_of_mem _ hx))
      ((QuotientGroup.mk' B) y) (Subgroup.mem_map_of_mem _ hy)
    rw [← QuotientGroup.ker_mk' B, MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, hmem]
  · intro h q hq
    obtain ⟨x, hx, rfl⟩ := hq
    rw [Subgroup.mem_centralizer_iff]
    rintro z ⟨y, hy, rfl⟩
    have h1 : (QuotientGroup.mk' B) ⁅x, y⁆ = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' B]
      exact h (Subgroup.commutator_mem_commutator hx hy)
    rw [commutatorElement_def] at h1
    simp only [map_mul, map_inv] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm

theorem exists_degree_le_index_mul_of_le_centralizer [Finite K]
    (hcen : D ≤ Subgroup.centralizer (C : Set K)) {θ : K → ℂ} (hθ : θ ∈ Irr K) :
    ∃ n m : ℕ, θ 1 = n ∧ n ≤ C.index * m ∧ m ^ 2 ≤ D.relIndex C := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype C := Fintype.ofFinite C
  have hcen' : D.subgroupOf C ≤ Subgroup.center C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro c
    have h := Subgroup.mem_centralizer_iff.1 (hcen (Subgroup.mem_subgroupOf.1 hx)) (c : K) c.2
    exact Subtype.ext (by simpa using h)
  obtain ⟨ψ, hψ⟩ := resConstituents_nonempty (N := C) hθ
  obtain ⟨hψIrr, hψpos⟩ := mem_resConstituents.1 hψ
  obtain ⟨m, hm1, hm2⟩ := exists_degree_eq_and_sq_le_index_of_le_center hψIrr hcen'
  obtain ⟨mult, hmult⟩ := exists_multiplicities_indClassFun (H := C) hψIrr
  have hdeg : ∀ χ : irrFinset K, ∃ d : ℕ, 0 < d ∧ (χ : K → ℂ) 1 = (d : ℂ) := fun χ =>
    NormalInducedFamily.exists_apply_one_eq_of_mem_Irr (mem_irrFinset.1 χ.2)
  choose d hdpos hd using hdeg
  set θ₀ : irrFinset K := ⟨θ, mem_irrFinset.2 hθ⟩ with hθ₀
  have hmultθ : 0 < mult θ₀ := by
    have h1 : (mult θ₀ : ℂ) = cfInner (indClassFun C ψ) θ :=
      (cfInner_eq_multiplicity hmult θ₀).symm
    rw [cfInner_indClassFun_eq_cfInner_resClassFun hθ hψIrr] at h1
    have h2 : (0 : ℂ) < (mult θ₀ : ℂ) := h1 ▸ hψpos
    exact_mod_cast h2
  have hsum : C.index * m = ∑ χ : irrFinset K, mult χ * d χ := by
    have h := congrFun hmult 1
    rw [NormalInducedFamily.indClassFun_one_eq_index_mul, hm1] at h
    have h2 : ((C.index * m : ℕ) : ℂ) = ((∑ χ : irrFinset K, mult χ * d χ : ℕ) : ℂ) := by
      push_cast
      rw [h]
      simp [Finset.sum_apply, hd]
    exact_mod_cast h2
  refine ⟨d θ₀, m, hd θ₀, ?_, by simpa [Subgroup.relIndex] using hm2⟩
  calc d θ₀ ≤ mult θ₀ * d θ₀ := Nat.le_mul_of_pos_left _ hmultθ
    _ ≤ ∑ χ : irrFinset K, mult χ * d χ :=
        Finset.single_le_sum (f := fun χ : irrFinset K => mult χ * d χ)
          (fun χ _ => Nat.zero_le _) (Finset.mem_univ θ₀)
    _ = C.index * m := hsum.symm

theorem exists_degree_eq_and_le_index_mul_sqrt_relIndex [Finite K] [B.Normal]
    (hBD : B ≤ D) (hDC : D ≤ C)
    (hcen : (D.subgroupOf C).map (QuotientGroup.mk' (B.subgroupOf C)) ≤
      Subgroup.center (C ⧸ B.subgroupOf C))
    {θ : K → ℂ} (hθ : θ ∈ Irr K) (hker : (B : Set K) ⊆ charValueKernel θ) :
    ∃ n : ℕ, θ 1 = n ∧ (n : ℝ) ≤ C.index * Real.sqrt (D.relIndex C) := by
  classical
  have hcomm : ⁅D, C⁆ ≤ B := (map_mk'_subgroupOf_le_center_iff hDC).1 hcen
  have hBC : B ≤ C := hBD.trans hDC
  obtain ⟨ψ, hψ, hcomp⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn (N := B)
    (mem_irrTrivialOn.2 ⟨hθ, fun n hn => mem_charValueKernel.1 (hker hn)⟩)
  obtain ⟨n, m, hn1, hnm, hm2⟩ := exists_degree_le_index_mul_of_le_centralizer
    (map_mk'_le_centralizer_map_iff.2 hcomm) hψ
  have hidx : (C.map (QuotientGroup.mk' B)).index = C.index :=
    Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective B) (by rwa [QuotientGroup.ker_mk'])
  have hrel : (D.map (QuotientGroup.mk' B)).relIndex (C.map (QuotientGroup.mk' B))
      = D.relIndex C := by
    rw [Subgroup.relIndex_map_map, QuotientGroup.ker_mk', sup_eq_left.2 hBD, sup_eq_left.2 hBC]
  rw [hidx] at hnm
  rw [hrel] at hm2
  refine ⟨n, by rw [← hcomp, comp_mk_one, hn1], ?_⟩
  have hms : (m : ℝ) ≤ Real.sqrt (D.relIndex C) :=
    (Real.le_sqrt (Nat.cast_nonneg m) (Nat.cast_nonneg _)).2 (by exact_mod_cast hm2)
  calc (n : ℝ) ≤ (C.index : ℝ) * (m : ℝ) := by exact_mod_cast hnm
    _ ≤ (C.index : ℝ) * Real.sqrt (D.relIndex C) :=
        mul_le_mul_of_nonneg_left hms (Nat.cast_nonneg _)

theorem apply_one_le_index_mul_sqrt_relIndex [Finite K] [B.Normal]
    (hBD : B ≤ D) (hDC : D ≤ C)
    (hcen : (D.subgroupOf C).map (QuotientGroup.mk' (B.subgroupOf C)) ≤
      Subgroup.center (C ⧸ B.subgroupOf C))
    {θ : K → ℂ} (hθ : θ ∈ Irr K) (hker : (B : Set K) ⊆ charValueKernel θ) :
    ‖θ 1‖ ≤ C.index * Real.sqrt (D.relIndex C) := by
  obtain ⟨n, hn1, hn2⟩ := exists_degree_eq_and_le_index_mul_sqrt_relIndex hBD hDC hcen hθ hker
  simpa [hn1] using hn2

theorem apply_one_le_index_mul_sqrt_relIndex_of_commutator_le [Finite K] [B.Normal]
    (hBD : B ≤ D) (hDC : D ≤ C) (hcomm : ⁅D, C⁆ ≤ B)
    {θ : K → ℂ} (hθ : θ ∈ Irr K) (hker : (B : Set K) ⊆ charValueKernel θ) :
    ‖θ 1‖ ≤ C.index * Real.sqrt (D.relIndex C) :=
  apply_one_le_index_mul_sqrt_relIndex hBD hDC
    ((map_mk'_subgroupOf_le_center_iff hDC).2 hcomm) hθ hker

end CFSG.FeitThompson
