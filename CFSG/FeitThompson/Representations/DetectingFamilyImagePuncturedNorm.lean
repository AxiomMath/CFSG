module

public import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
public import CFSG.FeitThompson.Definitions.CoreDetectingNormalInducedFamily
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.AbelianNormalDetectingRestrictionSplit
import CFSG.FeitThompson.Representations.AbelianQuotientPuncturedNormBound
import CFSG.FeitThompson.Representations.CommutingCyclicAverageCharacterCongruence
import CFSG.FeitThompson.Representations.ConstantValuePuncturedSubgroupInteger
public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem apply_eq_apply_one_of_mem_span_irrTrivialOn {K : Type*} [Group K] {N : Subgroup K}
    {α : K → ℂ} (hα : α ∈ Submodule.span ℤ (irrTrivialOn N)) {z : K} (hz : z ∈ N) :
    α z = α 1 := by
  induction hα using Submodule.span_induction with
  | mem f hf => exact (mem_irrTrivialOn.1 hf).2 z hz
  | zero => rfl
  | add f g _ _ hf hg => simp only [Pi.add_apply, hf, hg]
  | smul m f _ hf => simp only [Pi.smul_apply, hf]

theorem sum_norm_sq_compl_one_ge_of_isMulCommutative {K : Type*} [Group K] [IsMulCommutative K]
    [Fintype K] [DecidableEq K] {Q : Subgroup K} (hQ : Q ≠ ⊥) {α : K → ℂ}
    (hα : α ∈ Submodule.span ℤ (irrTrivialOn Q)) (hα0 : α ≠ 0) :
    (Nat.card K : ℝ) - 1 ≤ ∑ z ∈ ({1} : Finset K)ᶜ, ‖α z‖ ^ 2 := by
  let _ : CommGroup K := IsMulCommutative.instCommGroup
  exact sum_norm_sq_compl_one_ge_of_mem_span_irrTrivialOn hQ hα hα0

variable {G : Type*} [Group G] [Fintype G] {S : Subgroup G} [Fintype ↥S] {H P : Subgroup ↥S}

open scoped Classical in
theorem exists_mem_span_irrTrivialOn_eq_of_forall_cfInner_eq_zero
    [H.Normal] [P.Normal] [IsMulCommutative ↥H] (hPH : P ≤ H)
    (ν : Submodule.span ℤ (indFamDetect H (P.subgroupOf H)) →+ Submodule.span ℤ (Irr G))
    (hν : ∀ f : charSpanZero (indFamDetect H (P.subgroupOf H)),
      (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ) = indClassFun S (f : ↥S → ℂ))
    (hcard : 2 ≤ (indFamDetect H (P.subgroupOf H)).ncard)
    {χ : G → ℂ} (hχ : χ ∈ Submodule.span ℤ (Irr G))
    (horth : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect H (P.subgroupOf H),
      cfInner (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) χ = 0) :
    ∃ α : ↥H → ℂ, α ∈ Submodule.span ℤ (irrTrivialOn (P.subgroupOf H)) ∧
      ∀ z : ↥H, z ≠ 1 → χ ((z : ↥S) : G) = α z := by
  classical
  obtain ⟨ζ, hζ, -⟩ := Set.exists_ne_of_one_lt_ncard hcard 0
  obtain ⟨a, n, b, -, ha, -, -, hbzero, hsplit⟩ :=
    exists_intCast_eq_on_sdiff_one_of_cfInner_eq_zero hPH ν hν hcard hζ hχ
      (fun ξ hξ _ => horth ξ hξ)
  have ha0 : a = 0 := by
    have h := ha.symm.trans (horth ζ hζ)
    exact_mod_cast h
  refine ⟨∑ θ ∈ irrFinset ↥H, (b θ : ℂ) • θ, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun θ hθ => ?_
    by_cases h0 : b θ = 0
    · simp [h0]
    · have hdet : ((P.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊆ charValueKernel θ := by
        by_contra hc
        exact h0 (hbzero θ hc)
      have hmem : θ ∈ irrTrivialOn (P.subgroupOf H) :=
        mem_irrTrivialOn.2 ⟨mem_irrFinset.1 hθ, fun z hz => mem_charValueKernel.1 (hdet hz)⟩
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  · intro z hz
    rw [hsplit z hz, ha0, Finset.sum_apply]
    simp

omit [Fintype G] [Fintype ↥S] in
open scoped Classical in
theorem card_sub_one_le_sum_norm_sq_of_eq_on_compl_one [Finite G] [Fintype ↥H]
    [IsMulCommutative ↥H]
    (hPH : P ≤ H) {χ : G → ℂ} (hχ : χ ∈ Submodule.span ℤ (Irr G))
    {q : ℕ} (hq : q.Prime) {x y : ↥S} (hxP : x ∈ P) (hx1 : x ≠ 1)
    (hy : orderOf y = q) (hxy : Commute x y)
    {Θ : ↥(Subgroup.zpowers (y : G)) → ℂ} (hΘ : Θ ∈ Irr ↥(Subgroup.zpowers (y : G)))
    (hmatch : ∀ j : ℕ, 1 ≤ j → j ≤ q - 1 →
      χ ((y : G) ^ j * (x : G)) = Θ (⟨(y : G), Subgroup.mem_zpowers _⟩ ^ j))
    {α : ↥H → ℂ} (hαmem : α ∈ Submodule.span ℤ (irrTrivialOn (P.subgroupOf H)))
    (hval : ∀ z : ↥H, z ≠ 1 → χ ((z : ↥S) : G) = α z) :
    (Nat.card ↥H : ℝ) - 1 ≤ ∑ z ∈ ({1} : Finset ↥H)ᶜ, ‖χ ((z : ↥S) : G)‖ ^ 2 := by
  classical
  obtain ⟨m, hm⟩ := exists_int_apply_one_of_mem_span_Irr
    (Submodule.span_mono irrTrivialOn_subset_Irr hαmem)
  have hxH : (⟨x, hPH hxP⟩ : ↥H) ≠ 1 := fun h => hx1 (by simpa using Subtype.ext_iff.1 h)
  have hcx : χ (x : G) = (m : ℂ) := by
    have h := hval ⟨x, hPH hxP⟩ hxH
    rw [apply_eq_apply_one_of_mem_span_irrTrivialOn hαmem
      (Subgroup.mem_subgroupOf.2 hxP), hm] at h
    exact h
  have hΘ1 : Θ 1 = ((1 : ℤ) : ℂ) := by
    rw [Irr.apply_one_eq_one_of_isMulCommutative hΘ]
    norm_num
  have hyord : orderOf (y : G) = q := by rw [← hy]; exact Subgroup.orderOf_coe y
  have hqdvd : (q : ℤ) ∣ m - 1 :=
    prime_dvd_sub_of_forall_apply_eq hq hyord (hxy.symm.map S.subtype) hχ
      (Submodule.subset_span hΘ) hcx hΘ1 hmatch
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, zero_sub, dvd_neg] at hqdvd
    exact hq.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hqdvd)
  have hα0 : α ≠ 0 := by
    intro h
    rw [h] at hm
    simp only [Pi.zero_apply] at hm
    exact hm0 (by exact_mod_cast hm.symm)
  have hPbot : P.subgroupOf H ≠ ⊥ := by
    intro h
    refine hxH ?_
    have hmem : (⟨x, hPH hxP⟩ : ↥H) ∈ P.subgroupOf H := Subgroup.mem_subgroupOf.2 hxP
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  refine (sum_norm_sq_compl_one_ge_of_isMulCommutative hPbot hαmem hα0).trans
    (le_of_eq (Finset.sum_congr rfl fun z hz => ?_))
  rw [hval z (by simpa using hz)]

open scoped Classical in
theorem card_sub_one_le_sum_norm_sq_of_forall_cfInner_eq_zero
    [H.Normal] [P.Normal] [IsMulCommutative ↥H] (hPH : P ≤ H)
    (ν : Submodule.span ℤ (indFamDetect H (P.subgroupOf H)) →+ Submodule.span ℤ (Irr G))
    (hν : ∀ f : charSpanZero (indFamDetect H (P.subgroupOf H)),
      (ν (Submodule.inclusion (charSpanZero_le _) f) : G → ℂ) = indClassFun S (f : ↥S → ℂ))
    (hcard : 2 ≤ (indFamDetect H (P.subgroupOf H)).ncard)
    {χ : G → ℂ} (hχ : χ ∈ Submodule.span ℤ (Irr G))
    (horth : ∀ ξ, ∀ hξ : ξ ∈ indFamDetect H (P.subgroupOf H),
      cfInner (ν ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) χ = 0)
    {q : ℕ} (hq : q.Prime) {x y : ↥S} (hxP : x ∈ P) (hx1 : x ≠ 1)
    (hy : orderOf y = q) (hxy : Commute x y)
    {Θ : ↥(Subgroup.zpowers (y : G)) → ℂ} (hΘ : Θ ∈ Irr ↥(Subgroup.zpowers (y : G)))
    (hmatch : ∀ j : ℕ, 1 ≤ j → j ≤ q - 1 →
      χ ((y : G) ^ j * (x : G)) = Θ (⟨(y : G), Subgroup.mem_zpowers _⟩ ^ j)) :
    (Nat.card ↥H : ℝ) - 1 ≤ ∑ z ∈ ({1} : Finset ↥H)ᶜ, ‖χ ((z : ↥S) : G)‖ ^ 2 := by
  obtain ⟨α, hαmem, hval⟩ :=
    exists_mem_span_irrTrivialOn_eq_of_forall_cfInner_eq_zero hPH ν hν hcard hχ horth
  exact card_sub_one_le_sum_norm_sq_of_eq_on_compl_one hPH hχ hq hxP hx1 hy hxy hΘ hmatch
    hαmem hval

end CFSG.FeitThompson
