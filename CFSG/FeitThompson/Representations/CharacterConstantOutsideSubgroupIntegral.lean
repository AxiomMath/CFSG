module

public import CFSG.FeitThompson.Representations.RationalAlgebraicIntegerIsInteger
public import CFSG.FeitThompson.Representations.CharacterValuesAlgebraicIntegers
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

variable {G : Type*} [Group G]

theorem exists_sum_subgroup_eq_intCast_mul_card_of_mem_Irr (H : Subgroup G) [Fintype H]
    {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    ∃ m : ℤ, ∑ x : H, χ (x : G) = (m : ℂ) * (Nat.card H : ℂ) := by
  obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hcard
  set ρ : Representation ℂ H V.V := V.ρ.comp H.subtype with hρ
  have hch : ∀ h : H, ρ.character h = FDRep.character V (h : G) := fun _ => rfl
  have key := Representation.card_inv_mul_sum_char_eq_finrank ρ
  refine ⟨(finrank ℂ ρ.invariants : ℤ), ?_⟩
  rw [Finset.sum_congr rfl (fun h (_ : h ∈ Finset.univ) => (hch h).symm)]
  push_cast
  rw [← key]
  field_simp

theorem exists_sum_subgroup_eq_intCast_mul_card_of_mem_span_Irr (H : Subgroup G) [Fintype H]
    {f : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G)) :
    ∃ m : ℤ, ∑ x : H, f (x : G) = (m : ℂ) * (Nat.card H : ℂ) := by
  induction hf using Submodule.span_induction with
  | mem χ hχ => exact exists_sum_subgroup_eq_intCast_mul_card_of_mem_Irr H hχ
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨m, hm⟩ := ihx
      obtain ⟨n, hn⟩ := ihy
      exact ⟨m + n, by simp only [Pi.add_apply, Finset.sum_add_distrib, hm, hn]; push_cast; ring⟩
  | smul a x hx ihx =>
      obtain ⟨m, hm⟩ := ihx
      exact ⟨a * m, by
        simp only [Pi.smul_apply, zsmul_eq_mul, ← Finset.mul_sum, hm]; push_cast; ring⟩

theorem isIntegral_int_of_mem_span_Irr [Finite G] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (g : G) : IsIntegral ℤ (f g) := by
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
      obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
      exact FDRep.isIntegral_character V g
  | zero => simpa using isIntegral_zero
  | add x y hx hy ihx ihy => exact ihx.add ihy
  | smul a x hx ihx => simpa using ihx.zsmul a

theorem sum_subgroup_eq_sum_add_of_eq_of_notMem {B K : Subgroup G} [Fintype B] [Fintype K]
    (hBK : B ≤ K) {f : G → ℂ} {c : ℂ} (hc : ∀ x ∈ K, x ∉ B → f x = c) :
    ∑ x : K, f (x : G) = ∑ x : B, f (x : G) + ((Nat.card K : ℂ) - (Nat.card B : ℂ)) * c := by
  classical
  have hKfin : ∑ x : K, f (x : G) = ∑ x ∈ (K : Set G).toFinset, f x := Finset.sum_set_coe _
  have hBfin : ∑ x : B, f (x : G) = ∑ x ∈ (B : Set G).toFinset, f x := Finset.sum_set_coe _
  have hsub : (B : Set G).toFinset ⊆ (K : Set G).toFinset := by
    intro x hx
    simp only [Set.mem_toFinset, SetLike.mem_coe] at hx ⊢
    exact hBK hx
  have hsplit := Finset.sum_sdiff (f := f) hsub
  have hconst : ∑ x ∈ (K : Set G).toFinset \ (B : Set G).toFinset, f x
      = (((K : Set G).toFinset \ (B : Set G).toFinset).card : ℂ) * c := by
    rw [Finset.sum_congr rfl (fun x hx => ?_), Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe] at hx
    exact hc x hx.1 hx.2
  have hcardK : ((K : Set G).toFinset).card = Nat.card K := by
    rw [Set.toFinset_card, Nat.card_eq_fintype_card]; rfl
  have hcardB : ((B : Set G).toFinset).card = Nat.card B := by
    rw [Set.toFinset_card, Nat.card_eq_fintype_card]; rfl
  have hcard : (((K : Set G).toFinset \ (B : Set G).toFinset).card : ℂ)
      = (Nat.card K : ℂ) - (Nat.card B : ℂ) := by
    rw [← hcardK, ← hcardB, ← Finset.card_sdiff_add_card_eq_card hsub]
    push_cast
    ring
  rw [hKfin, hBfin, ← hsplit, hconst, hcard]
  ring

theorem exists_int_eq_of_mem_span_Irr_of_eq_of_notMem [Finite G] {B K : Subgroup G}
    (hBK : B < K) {Psi : G → ℂ} (hPsi : Psi ∈ Submodule.span ℤ (Irr G)) {c : ℂ}
    (hc : ∀ k ∈ K, k ∉ B → Psi k = c) : ∃ n : ℤ, c = (n : ℂ) := by
  classical
  have : Finite B := Finite.Set.subset (K : Set G) hBK.le
  have : Fintype B := Fintype.ofFinite _
  have : Fintype K := Fintype.ofFinite _
  obtain ⟨m, hm⟩ := exists_sum_subgroup_eq_intCast_mul_card_of_mem_span_Irr K hPsi
  obtain ⟨n, hn⟩ := exists_sum_subgroup_eq_intCast_mul_card_of_mem_span_Irr B hPsi
  have hsplit := sum_subgroup_eq_sum_add_of_eq_of_notMem hBK.le hc
  rw [hm, hn] at hsplit
  have hne : ((Nat.card K : ℂ) - (Nat.card B : ℂ)) ≠ 0 := by
    have hlt : Nat.card B < Nat.card K :=
      Set.Finite.card_lt_card (Set.toFinite _) (show (B : Set G) ⊂ (K : Set G) from hBK)
    have hne' : (Nat.card B : ℂ) ≠ (Nat.card K : ℂ) := by
      simpa using (Nat.cast_injective.ne hlt.ne : (Nat.card B : ℂ) ≠ (Nat.card K : ℂ))
    exact fun h => hne' (by linear_combination -h)
  refine (Complex.isIntegral_int_iff_exists_int_of_exists_rat
    ⟨(m * Nat.card K - n * Nat.card B : ℤ) / ((Nat.card K : ℤ) - (Nat.card B : ℤ)), ?_⟩).1 ?_
  · push_cast
    rw [eq_div_iff hne]
    linear_combination -hsplit
  · obtain ⟨k, hkK, hkB⟩ := Set.exists_of_ssubset hBK
    rw [← hc k hkK hkB]
    exact isIntegral_int_of_mem_span_Irr hPsi k

theorem mem_range_intCast_of_mem_span_Irr_of_eq_of_notMem [Finite G] {B K : Subgroup G}
    (hBK : B < K) {Psi : G → ℂ} (hPsi : Psi ∈ Submodule.span ℤ (Irr G)) {c : ℂ}
    (hc : ∀ k ∈ K, k ∉ B → Psi k = c) : c ∈ Set.range (Int.cast : ℤ → ℂ) := by
  obtain ⟨n, hn⟩ := exists_int_eq_of_mem_span_Irr_of_eq_of_notMem hBK hPsi hc
  exact ⟨n, hn.symm⟩

end CFSG.FeitThompson
