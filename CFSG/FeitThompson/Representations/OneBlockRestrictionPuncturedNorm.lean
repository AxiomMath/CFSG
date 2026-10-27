module

public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
public import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
public import CFSG.FeitThompson.Representations.ConstantValuePuncturedSubgroupInteger
public import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
import Mathlib.Analysis.Complex.Polynomial.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

namespace OneBlockRestriction

variable {K : Type*} [Group K]

def irrTrivialOn (Q : Subgroup K) : Set (K → ℂ) :=
  {χ ∈ Irr K | (Q : Set K) ⊆ charValueKernel χ}

theorem mem_irrTrivialOn {Q : Subgroup K} {χ : K → ℂ} :
    χ ∈ irrTrivialOn Q ↔ χ ∈ Irr K ∧ ∀ x ∈ Q, χ x = χ 1 := by
  simp [irrTrivialOn, Set.subset_def]

theorem irrTrivialOn_subset_Irr (Q : Subgroup K) : irrTrivialOn Q ⊆ Irr K := fun _ hχ => hχ.1

theorem apply_eq_apply_one_of_mem_span_irrTrivialOn {Q : Subgroup K} {α : K → ℂ}
    (hα : α ∈ Submodule.span ℤ (irrTrivialOn Q)) {x : K} (hx : x ∈ Q) : α x = α 1 := by
  induction hα using Submodule.span_induction with
  | mem f hf => exact mem_charValueKernel.1 (hf.2 hx)
  | zero => rfl
  | add f g _ _ hf hg => simp only [Pi.add_apply, hf, hg]
  | smul m f _ hf => simp only [Pi.smul_apply, hf]

theorem exists_int_apply_one_of_mem_span_irrTrivialOn {Q : Subgroup K} {α : K → ℂ}
    (hα : α ∈ Submodule.span ℤ (irrTrivialOn Q)) : ∃ m : ℤ, α 1 = (m : ℂ) :=
  exists_int_apply_one_of_mem_span_Irr (Submodule.span_mono (irrTrivialOn_subset_Irr Q) hα)

theorem conj_apply_one_of_mem_span_irrTrivialOn {Q : Subgroup K} {α : K → ℂ}
    (hα : α ∈ Submodule.span ℤ (irrTrivialOn Q)) : conj (α 1) = α 1 := by
  obtain ⟨m, hm⟩ := exists_int_apply_one_of_mem_span_irrTrivialOn hα
  rw [hm]
  simp

theorem cfInner_eq_zero_of_mem_span_irrTrivialOn [Fintype K] {Q : Subgroup K} {α ψ : K → ℂ}
    (hα : α ∈ Submodule.span ℤ (irrTrivialOn Q)) (hψ : ψ ∈ Irr K)
    (hψQ : ¬ (Q : Set K) ⊆ charValueKernel ψ) : cfInner α ψ = 0 := by
  induction hα using Submodule.span_induction with
  | mem x hx => exact cfInner_eq_zero_of_mem_Irr hx.1 hψ fun h => hψQ (h ▸ hx.2)
  | zero => exact cfInner_zero_left ψ
  | add x y _ _ hx hy => rw [cfInner_add_left, hx, hy, add_zero]
  | smul m x _ hx => rw [cfInner_zsmul_left, hx, mul_zero]

variable {S : Type*} [Group S] [Fintype S]

theorem sum_eq_sum_subgroup {H : Subgroup S} [Fintype ↥H] {F : S → ℂ}
    (hF : ∀ s, s ∉ H → F s = 0) : ∑ s : S, F s = ∑ x : ↥H, F (x : S) := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ H)) (fun x => by simp) F]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro s _ hs
  exact hF s (by simpa using hs)

variable {H : Subgroup S} [Fintype ↥H]

omit [Fintype S] in
theorem sum_norm_sq_eq_card_mul_cfInner (g : ↥H → ℂ) :
    ∑ x : ↥H, (‖g x‖ : ℂ) ^ 2 = (Nat.card ↥H : ℂ) * cfInner g g := by
  rw [cfInner_self_eq_sum_norm_sq, ← mul_assoc, mul_inv_cancel₀ (by
    exact_mod_cast Nat.cast_ne_zero.2 (Nat.card_pos (α := ↥H)).ne'), one_mul]

omit [Fintype S] in
theorem cfInner_self_add_smul (α ζ : ↥H → ℂ) (h : cfInner α ζ = 0) (c : ℂ) :
    cfInner (c • ζ + α) (c • ζ + α) = c * conj c * cfInner ζ ζ + cfInner α α := by
  have h2 : cfInner ζ α = 0 := by rw [← conj_cfInner, h, map_zero]
  rw [cfInner_add_left, cfInner_add_right, cfInner_add_right, cfInner_smul_left,
    cfInner_smul_left, cfInner_smul_right, cfInner_smul_right, h, h2]
  ring

omit [Fintype S] in
open scoped Classical in
theorem sum_erase_norm_sq_smul_add (ζ α : ↥H → ℂ) (horth : cfInner α ζ = 0) (c : ℂ)
    (hc : conj c = c) {v : ℂ} (hζ1 : ζ 1 = v) (hv : conj v = v) {w : ℂ} (hα1 : α 1 = w)
    (hw : conj w = w) {g : ↥H → ℂ} (hg : ∀ x : ↥H, x ≠ 1 → g x = c * ζ x + α x) :
    ∑ x ∈ Finset.univ.erase (1 : ↥H), (‖g x‖ : ℂ) ^ 2
      = (Nat.card ↥H : ℂ) * (c ^ 2 * cfInner ζ ζ) - (c * v) ^ 2 - 2 * c * v * w
        + ∑ x ∈ Finset.univ.erase (1 : ↥H), (‖α x‖ : ℂ) ^ 2 := by
  classical
  set G : ↥H → ℂ := c • ζ + α with hG
  have hGx : ∀ x ∈ Finset.univ.erase (1 : ↥H), (‖g x‖ : ℂ) ^ 2 = (‖G x‖ : ℂ) ^ 2 := by
    intro x hx
    rw [hg x (Finset.ne_of_mem_erase hx), hG]
    simp [Pi.add_apply, Pi.smul_apply]
  rw [Finset.sum_congr rfl hGx]
  have hsum : ∀ F : ↥H → ℂ, ∑ x ∈ Finset.univ.erase (1 : ↥H), (‖F x‖ : ℂ) ^ 2
      = (∑ x : ↥H, (‖F x‖ : ℂ) ^ 2) - (‖F 1‖ : ℂ) ^ 2 := by
    intro F
    rw [eq_sub_iff_add_eq]
    exact Finset.sum_erase_add _ _ (Finset.mem_univ _)
  rw [hsum G, hsum α, sum_norm_sq_eq_card_mul_cfInner, sum_norm_sq_eq_card_mul_cfInner,
    cfInner_self_add_smul α ζ horth c, hc]
  have hG1 : G 1 = c * v + w := by rw [hG]; simp [hζ1, hα1]
  have hnG : (‖G 1‖ : ℂ) ^ 2 = (c * v + w) ^ 2 := by
    rw [← Complex.mul_conj', hG1, map_add, map_mul, hc, hv, hw]
    ring
  have hnα : (‖α 1‖ : ℂ) ^ 2 = w ^ 2 := by
    rw [← Complex.mul_conj', hα1, hw]
    ring
  rw [hnG, hnα]
  ring

variable [H.Normal]

theorem cfInner_self_resClassFun_indClassFun (θ : ↥H → ℂ) :
    cfInner (resClassFun H (indClassFun H θ)) (resClassFun H (indClassFun H θ))
      = (H.index : ℂ) * cfInner (indClassFun H θ) (indClassFun H θ) := by
  have hz : ∀ s : S, s ∉ H → (‖indClassFun H θ s‖ : ℂ) ^ 2 = 0 := fun s hs => by
    simp [indClassFun_eq_zero_of_notMem H θ hs]
  have key : ∑ s : S, (‖indClassFun H θ s‖ : ℂ) ^ 2
      = ∑ x : ↥H, (‖indClassFun H θ (x : S)‖ : ℂ) ^ 2 := sum_eq_sum_subgroup hz
  rw [cfInner_self_eq_sum_norm_sq, cfInner_self_eq_sum_norm_sq]
  simp only [resClassFun_apply]
  rw [key]
  have hcard : (Nat.card S : ℂ) = (Nat.card ↥H : ℂ) * (H.index : ℂ) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index]
  rw [hcard]
  have hH : (Nat.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hI : (H.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Subgroup.index_ne_zero_of_finite
  field_simp

open NormalInduction (conjClassFun conjClassFun_apply)

variable {P : Subgroup S}

omit [Fintype S] [Fintype ↥H] in
theorem not_subset_charValueKernel_conjClassFun [hP : P.Normal] {θ : ↥H → ℂ}
    (hθP : ¬ ((P.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊆ charValueKernel θ) (t : S) :
    ¬ ((P.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊆ charValueKernel (conjClassFun H t θ) := by
  intro h
  refine hθP fun z hz => ?_
  have hzP : (z : S) ∈ P := Subgroup.mem_subgroupOf.1 hz
  have hy : MulAut.conjNormal t z ∈ (P.subgroupOf H : Subgroup ↥H) :=
    Subgroup.mem_subgroupOf.2 (by simpa [MulAut.conjNormal_apply] using hP.conj_mem _ hzP t)
  have key := h hy
  have h1 : conjClassFun H t θ (MulAut.conjNormal t z) = θ z := by
    rw [conjClassFun_apply]
    exact congrArg θ (Subtype.ext (by simp))
  have h2 : conjClassFun H t θ 1 = θ 1 := by
    rw [conjClassFun_apply]
    exact congrArg θ (Subtype.ext (by simp))
  rw [mem_charValueKernel] at key
  rw [mem_charValueKernel, ← h1, ← h2]
  exact key

theorem cfInner_eq_zero_resClassFun_indClassFun [P.Normal] {θ : ↥H → ℂ} (hθ : θ ∈ Irr ↥H)
    (hθP : ¬ ((P.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊆ charValueKernel θ)
    {α : ↥H → ℂ} (hα : α ∈ Submodule.span ℤ (irrTrivialOn (P.subgroupOf H))) :
    cfInner α (resClassFun H (indClassFun H θ)) = 0 := by
  classical
  obtain ⟨T₀, hT₀, -⟩ := H.exists_isComplement_left 1
  set T : Finset S := T₀.toFinset with hTdef
  have hT : Subgroup.IsComplement (T : Set S) (H : Set S) := by rwa [hTdef, Set.coe_toFinset]
  rw [resClassFun_indClassFun_eq_sum H (Irr_subset_classFun hθ) hT, cfInner_sum_right]
  refine Finset.sum_eq_zero fun t _ => ?_
  exact cfInner_eq_zero_of_mem_span_irrTrivialOn hα (conjClassFun_mem_Irr H t hθ)
    (not_subset_charValueKernel_conjClassFun (P := P) hθP t)

variable [IsMulCommutative ↥H]

omit [Fintype ↥H] [H.Normal] in
theorem resClassFun_indClassFun_apply_one {θ : ↥H → ℂ} (hθ : θ ∈ Irr ↥H) :
    resClassFun H (indClassFun H θ) 1 = (H.index : ℂ) := by
  rw [resClassFun_apply, show ((1 : ↥H) : S) = 1 from rfl, indClassFun_apply_one]
  obtain ⟨V, hV, rfl⟩ := mem_Irr.1 hθ
  have : Representation.IsIrreducible V.ρ := hV
  rw [FDRep.char_one, Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative V.ρ]
  norm_num

omit [Fintype ↥H] [H.Normal] in
theorem cfInner_self_indClassFun_ne_zero {θ : ↥H → ℂ} (hθ : θ ∈ Irr ↥H) :
    cfInner (indClassFun H θ) (indClassFun H θ) ≠ 0 := by
  intro h
  have h1 := resClassFun_indClassFun_apply_one hθ (H := H)
  rw [cfInner_self_eq_zero.1 h] at h1
  simp only [resClassFun_apply, Pi.zero_apply] at h1
  exact Subgroup.index_ne_zero_of_finite (by exact_mod_cast h1.symm)

open scoped Classical in
theorem sum_erase_norm_sq_eq [P.Normal] {θ : ↥H → ℂ} (hθ : θ ∈ Irr ↥H)
    (hθP : ¬ ((P.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊆ charValueKernel θ)
    {n : ℕ} (hn : cfInner (indClassFun H θ) (indClassFun H θ) = (n : ℂ)) (a : ℤ)
    {α : ↥H → ℂ} (hα : α ∈ Submodule.span ℤ (irrTrivialOn (P.subgroupOf H)))
    {f : ↥H → ℂ}
    (hf : ∀ x : ↥H, x ≠ 1 → f x = (a : ℂ) / (n : ℂ) * indClassFun H θ (x : S) + α x) :
    ∑ x ∈ Finset.univ.erase (1 : ↥H), (‖f x‖ : ℂ) ^ 2
      = (a : ℂ) ^ 2 / (n : ℂ) * ((Nat.card S : ℂ) - (H.index : ℂ) ^ 2 / (n : ℂ))
        - 2 * (a : ℂ) * (H.index : ℂ) * α 1 / (n : ℂ)
        + ∑ x ∈ Finset.univ.erase (1 : ↥H), (‖α x‖ : ℂ) ^ 2 := by
  classical
  have hn0 : (n : ℂ) ≠ 0 := hn ▸ cfInner_self_indClassFun_ne_zero hθ
  set ζ : ↥H → ℂ := resClassFun H (indClassFun H θ) with hζdef
  have hnorm : cfInner ζ ζ = (H.index : ℂ) * (n : ℂ) := by
    rw [hζdef, cfInner_self_resClassFun_indClassFun, hn]
  have horth : cfInner α ζ = 0 :=
    cfInner_eq_zero_resClassFun_indClassFun (P := P) hθ hθP hα
  have hkey := sum_erase_norm_sq_smul_add ζ α horth ((a : ℂ) / (n : ℂ))
    (by simp [map_div₀])
    (resClassFun_indClassFun_apply_one hθ) (Complex.conj_natCast _) (w := α 1) rfl
    (conj_apply_one_of_mem_span_irrTrivialOn hα)
    (g := f) (fun x hx => by rw [hf x hx, hζdef, resClassFun_apply])
  rw [hkey, hnorm]
  have hcard : (Nat.card S : ℂ) = (Nat.card ↥H : ℂ) * (H.index : ℂ) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index]
  rw [hcard]
  field_simp

omit [Fintype S] [H.Normal] [IsMulCommutative ↥H] in
open scoped Classical in
theorem card_sub_one_mul_norm_sq_le_sum_erase_norm_sq (hPH : P ≤ H) {α : ↥H → ℂ}
    (hα : α ∈ Submodule.span ℤ (irrTrivialOn (P.subgroupOf H))) :
    ((Nat.card ↥P : ℝ) - 1) * ‖α 1‖ ^ 2
      ≤ ∑ x ∈ Finset.univ.erase (1 : ↥H), ‖α x‖ ^ 2 := by
  classical
  set A : Finset ↥H := ((P.subgroupOf H : Subgroup ↥H) : Set ↥H).toFinset with hA
  have hAcard : A.card = Nat.card ↥P := by
    rw [hA, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  have hsub : A.erase 1 ⊆ Finset.univ.erase (1 : ↥H) :=
    Finset.erase_subset_erase _ (Finset.subset_univ _)
  have hone : (1 : ↥H) ∈ A := by simp [hA]
  have hcard1 : 1 ≤ A.card := Finset.card_pos.2 ⟨1, hone⟩
  have hval : ∑ x ∈ A.erase 1, ‖α x‖ ^ 2 = ((A.card : ℝ) - 1) * ‖α 1‖ ^ 2 := by
    rw [Finset.sum_congr rfl (g := fun _ => ‖α 1‖ ^ 2) ?_, Finset.sum_const,
      Finset.card_erase_of_mem hone, nsmul_eq_mul, Nat.cast_sub hcard1]
    · norm_num
    · intro x hx
      rw [apply_eq_apply_one_of_mem_span_irrTrivialOn hα
        (by simpa [hA] using Finset.mem_of_mem_erase hx)]
  calc ((Nat.card ↥P : ℝ) - 1) * ‖α 1‖ ^ 2 = ∑ x ∈ A.erase 1, ‖α x‖ ^ 2 := by
        rw [hval, hAcard]
    _ ≤ ∑ x ∈ Finset.univ.erase (1 : ↥H), ‖α x‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity

end OneBlockRestriction

end CFSG.FeitThompson
