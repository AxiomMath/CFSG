module

public import CFSG.FeitThompson.Representations.BlockDifferenceOrthogonalConstantOffCore
public import CFSG.FeitThompson.Representations.CentralFrobeniusLayerDegreeSquareSum
import CFSG.FeitThompson.Representations.FreeCentralSectionInducedLayerIrreducible
import CFSG.FeitThompson.Representations.RegularCharacterDegreeSquareSum
import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

section Family

variable {L : Type*} [Group L] [Fintype L]

noncomputable def centralLayerFinset (P : Subgroup L) (H : Subgroup P) : Finset (L → ℂ) :=
  (finite_indFamDetect P H).toFinset

@[simp] theorem mem_centralLayerFinset {P : Subgroup L} {H : Subgroup P} {f : L → ℂ} :
    f ∈ centralLayerFinset P H ↔ f ∈ indFamDetect P H := Set.Finite.mem_toFinset _

@[simp] theorem coe_centralLayerFinset (P : Subgroup L) (H : Subgroup P) :
    (centralLayerFinset P H : Set (L → ℂ)) = indFamDetect P H := Set.Finite.coe_toFinset _

noncomputable def centralLayerWeightedChar (P : Subgroup L) (H : Subgroup P) (e : ℂ) : L → ℂ :=
  e⁻¹ • ∑ ξ ∈ centralLayerFinset P H, ξ 1 • ξ

theorem centralLayerWeightedChar_apply (P : Subgroup L) (H : Subgroup P) (e : ℂ) (x : L) :
    centralLayerWeightedChar P H e x = e⁻¹ * ∑ ξ ∈ centralLayerFinset P H, ξ 1 * ξ x := by
  simp [centralLayerWeightedChar, Finset.sum_apply, Finset.mul_sum]

theorem centralLayerWeightedChar_eq_sum_smul (P : Subgroup L) (H : Subgroup P) (e : ℂ) :
    centralLayerWeightedChar P H e = ∑ ξ ∈ centralLayerFinset P H, (ξ 1 / e) • ξ := by
  rw [centralLayerWeightedChar, Finset.smul_sum]
  exact Finset.sum_congr rfl fun ξ _ => by rw [smul_smul, div_eq_inv_mul]

end Family

section Characters

variable {L : Type*} [Group L]

theorem exists_fdRep_character_eq_zero : ∃ W : FDRep ℂ L, FDRep.character W = 0 := by
  obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq
    (Representation.trivial ℂ L (Fin 0 → ℂ))
  refine ⟨W, ?_⟩
  rw [hW]
  funext g
  simp [Representation.character, Representation.trivial, LinearMap.trace_one]

theorem exists_fdRep_character_eq_add {f g : L → ℂ}
    (hf : ∃ W : FDRep ℂ L, FDRep.character W = f) (hg : ∃ W : FDRep ℂ L, FDRep.character W = g) :
    ∃ W : FDRep ℂ L, FDRep.character W = f + g := by
  obtain ⟨V, rfl⟩ := hf
  obtain ⟨W, rfl⟩ := hg
  obtain ⟨U, hU⟩ := NormalInducedFamily.exists_fdRep_character_eq
    (Representation.prod (V := (V.V : Type)) (W := (W.V : Type)) V.ρ W.ρ)
  refine ⟨U, ?_⟩
  rw [hU, Representation.character_prod]
  funext g
  simp [FDRep.character, Representation.character]

theorem exists_fdRep_character_eq_nsmul {f : L → ℂ} (n : ℕ)
    (hf : ∃ W : FDRep ℂ L, FDRep.character W = f) :
    ∃ W : FDRep ℂ L, FDRep.character W = (n : ℂ) • f := by
  induction n with
  | zero => simpa using exists_fdRep_character_eq_zero
  | succ k ih =>
      have h : ((k + 1 : ℕ) : ℂ) • f = (k : ℂ) • f + f := by push_cast; module
      rw [h]
      exact exists_fdRep_character_eq_add ih hf

theorem exists_fdRep_character_eq_sum_smul (s : Finset (L → ℂ)) (c : (L → ℂ) → ℂ)
    (hc : ∀ χ ∈ s, ∃ n : ℕ, c χ = (n : ℂ))
    (hchar : ∀ χ ∈ s, ∃ W : FDRep ℂ L, FDRep.character W = χ) :
    ∃ W : FDRep ℂ L, FDRep.character W = ∑ χ ∈ s, c χ • χ := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using exists_fdRep_character_eq_zero
  | cons a s ha ih =>
      rw [Finset.sum_cons]
      obtain ⟨n, hn⟩ := hc a (Finset.mem_cons_self a s)
      refine exists_fdRep_character_eq_add ?_
        (ih (fun χ hχ => hc χ (Finset.mem_cons_of_mem hχ))
          (fun χ hχ => hchar χ (Finset.mem_cons_of_mem hχ)))
      rw [hn]
      exact exists_fdRep_character_eq_nsmul n (hchar a (Finset.mem_cons_self a s))

end Characters

section Regular

variable {L : Type*} [Group L] [Finite L]

theorem sum_irrFinset_quotient_eq_sum_irrTrivialOnFinset (Z : Subgroup L) [Z.Normal]
    (F : (L → ℂ) → ℂ) :
    ∑ ψ ∈ irrFinset (L ⧸ Z), F (ψ ∘ (QuotientGroup.mk : L → L ⧸ Z))
      = ∑ χ ∈ irrTrivialOnFinset Z, F χ := by
  classical
  refine Finset.sum_bij (fun (ψ : L ⧸ Z → ℂ) _ => ψ ∘ (QuotientGroup.mk : L → L ⧸ Z)) ?_ ?_ ?_ ?_
  · intro ψ hψ
    exact mem_irrTrivialOnFinset.2 (mem_irrTrivialOn_comp_mk (mem_irrFinset.1 hψ))
  · intro ψ₁ _ ψ₂ _ hh
    exact comp_mk_injective hh
  · intro χ hχ
    obtain ⟨ψ, hψ, hcomp⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn (mem_irrTrivialOnFinset.1 hχ)
    exact ⟨ψ, mem_irrFinset.2 hψ, hcomp⟩
  · intro ψ _
    rfl

theorem sum_irrTrivialOnFinset_apply (Z : Subgroup L) [Z.Normal] (x : L) :
    ∑ χ ∈ irrTrivialOnFinset Z, χ 1 * χ x
      = (Representation.leftRegular ℂ (L ⧸ Z)).character (QuotientGroup.mk x) := by
  classical
  have h := leftRegular_character_eq_sum (G := L ⧸ Z)
  rw [Finset.sum_coe_sort (irrFinset (L ⧸ Z)) (fun ψ : L ⧸ Z → ℂ => ψ 1 • ψ)] at h
  rw [h]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact (sum_irrFinset_quotient_eq_sum_irrTrivialOnFinset Z (fun χ => χ 1 * χ x)).symm

theorem sum_irrFinset_apply (x : L) :
    ∑ χ ∈ irrFinset L, χ 1 * χ x = (Representation.leftRegular ℂ L).character x := by
  classical
  have h := leftRegular_character_eq_sum (G := L)
  rw [Finset.sum_coe_sort (irrFinset L) (fun ψ : L → ℂ => ψ 1 • ψ)] at h
  have hx := congrFun h x
  simpa [Finset.sum_apply] using hx.symm

theorem inflated_leftRegular_character_apply_of_mem (Z : Subgroup L) [Z.Normal] {x : L}
    (hx : x ∈ Z) :
    (Representation.leftRegular ℂ (L ⧸ Z)).character (QuotientGroup.mk x) = (Z.index : ℂ) := by
  classical
  rw [leftRegular_character_apply, if_pos ((QuotientGroup.eq_one_iff x).2 hx),
    Subgroup.index_eq_card]

theorem inflated_leftRegular_character_apply_of_notMem (Z : Subgroup L) [Z.Normal] {x : L}
    (hx : x ∉ Z) :
    (Representation.leftRegular ℂ (L ⧸ Z)).character (QuotientGroup.mk x) = 0 :=
  leftRegular_character_of_ne_one fun h => hx ((QuotientGroup.eq_one_iff x).1 h)

end Regular

section Split

variable {L : Type*} [Group L] [Fintype L]

theorem disjoint_irrDetectFinset_irrTrivialOnFinset (Z : Subgroup L) [Z.Normal] :
    Disjoint (irrDetectFinset Z) (irrTrivialOnFinset Z) := by
  classical
  refine Finset.disjoint_left.2 fun χ hχ hχ' => ?_
  have h1 : χ ∈ irrDetect ℂ Z := by rw [← coe_irrDetectFinset Z]; exact hχ
  have h2 := mem_irrTrivialOn.1 (mem_irrTrivialOnFinset.1 hχ')
  exact (mem_irrDetect.1 h1).2 fun z hz => mem_charValueKernel.2 (h2.2 z hz)

theorem irrFinset_eq_irrDetectFinset_union_irrTrivialOnFinset (Z : Subgroup L) [Z.Normal] :
    irrFinset L = irrDetectFinset Z ∪ irrTrivialOnFinset Z := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · intro χ hχ
    by_cases h : χ ∈ irrDetectFinset Z
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _
        (mem_irrTrivialOnFinset.2 (mem_irrTrivialOn_of_notMem_irrDetectFinset Z hχ h))
  · intro χ hχ
    rcases Finset.mem_union.1 hχ with h | h
    · exact irrDetectFinset_subset_irrFinset Z h
    · exact mem_irrFinset.2 (irrTrivialOn_subset_Irr (mem_irrTrivialOnFinset.1 h))

theorem sum_irrDetectFinset_apply (Z : Subgroup L) [Z.Normal] (x : L) :
    ∑ χ ∈ irrDetectFinset Z, χ 1 * χ x
      = (Representation.leftRegular ℂ L).character x
        - (Representation.leftRegular ℂ (L ⧸ Z)).character (QuotientGroup.mk x) := by
  classical
  have hsplit : ∑ χ ∈ irrFinset L, χ 1 * χ x
      = ∑ χ ∈ irrDetectFinset Z, χ 1 * χ x + ∑ χ ∈ irrTrivialOnFinset Z, χ 1 * χ x := by
    rw [irrFinset_eq_irrDetectFinset_union_irrTrivialOnFinset Z,
      Finset.sum_union (disjoint_irrDetectFinset_irrTrivialOnFinset Z)]
  rw [← sum_irrFinset_apply x, ← sum_irrTrivialOnFinset_apply Z x, hsplit]
  ring

end Split

section Node

variable {L : Type*} [Group L] [Fintype L] {p a : ℕ} {P E Z : Subgroup L}

theorem centralLayerFinset_eq_irrDetectFinset [P.Normal] [Z.Normal] (hZP : Z ≤ P)
    (hZc : Z ≤ centralizer (P : Set L)) (hPE : P ⊔ E = ⊤)
    (hfree : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1) :
    centralLayerFinset P (Z.subgroupOf P) = irrDetectFinset Z := by
  classical
  refine Finset.coe_injective ?_
  rw [coe_centralLayerFinset, coe_irrDetectFinset]
  exact indFamDetect_eq_irrDetect (E := E) hZP hZc hPE hfree

theorem centralLayerWeightedChar_eq_regular_sub [P.Normal] [Z.Normal] (hZP : Z ≤ P)
    (hZc : Z ≤ centralizer (P : Set L)) (hPE : P ⊔ E = ⊤)
    (hfree : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1) (x : L) :
    centralLayerWeightedChar P (Z.subgroupOf P) (P.index : ℂ) x
      = ((Representation.leftRegular ℂ L).character x
          - (Representation.leftRegular ℂ (L ⧸ Z)).character (QuotientGroup.mk x))
        / (P.index : ℂ) := by
  rw [centralLayerWeightedChar_apply,
    centralLayerFinset_eq_irrDetectFinset (E := E) hZP hZc hPE hfree,
    sum_irrDetectFinset_apply Z x, div_eq_inv_mul]

theorem exists_fdRep_character_eq_of_mem_centralLayerFinset {H : Subgroup P} {ξ : L → ℂ}
    (hξ : ξ ∈ centralLayerFinset P H) : ∃ W : FDRep ℂ L, FDRep.character W = ξ := by
  have h := indFamDetect_subset_indFam_irrChar P H (mem_centralLayerFinset.1 hξ)
  rw [irrChar_eq_Irr] at h
  exact NormalInducedFamily.exists_fdRep_character_eq_of_mem_indFam P h

theorem exists_apply_one_div_index_eq (hp : p.Prime) (hP : Nat.card P = p ^ a)
    (hZ : Z ≤ P ⊓ centralizer (P : Set L)) {ξ : L → ℂ}
    (hξ : ξ ∈ centralLayerFinset P (Z.subgroupOf P)) :
    ∃ n : ℕ, ξ 1 / (P.index : ℂ) = (n : ℂ) := by
  obtain ⟨b, hb, -⟩ :=
    exists_degree_eq_index_mul_pow_and_sq_dvd hp hP hZ (mem_centralLayerFinset.1 hξ)
  refine ⟨p ^ b, ?_⟩
  have hidx : (P.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero
  rw [hb]
  push_cast
  field_simp

theorem isCharacter_centralLayerWeightedChar (hp : p.Prime) (hP : Nat.card P = p ^ a)
    (hZ : Z ≤ P ⊓ centralizer (P : Set L)) :
    ∃ W : FDRep ℂ L,
      FDRep.character W = centralLayerWeightedChar P (Z.subgroupOf P) (P.index : ℂ) := by
  rw [centralLayerWeightedChar_eq_sum_smul]
  exact exists_fdRep_character_eq_sum_smul _ _
    (fun ξ hξ => exists_apply_one_div_index_eq hp hP hZ hξ)
    fun ξ hξ => exists_fdRep_character_eq_of_mem_centralLayerFinset hξ

theorem centralLayerWeightedChar_apply_one [P.Normal] [Z.Normal] (hZP : Z ≤ P)
    (hZc : Z ≤ centralizer (P : Set L)) (hPE : P ⊔ E = ⊤)
    (hfree : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1) :
    centralLayerWeightedChar P (Z.subgroupOf P) (P.index : ℂ) 1
      = (Z.relIndex P : ℂ) * ((Nat.card Z : ℂ) - 1) := by
  classical
  rw [centralLayerWeightedChar_eq_regular_sub (E := E) hZP hZc hPE hfree,
    leftRegular_character_one, inflated_leftRegular_character_apply_of_mem Z Z.one_mem]
  have hmul : Z.relIndex P * P.index = Z.index := Subgroup.relIndex_mul_index hZP
  have hcard : Z.index * Nat.card Z = Nat.card L := Subgroup.index_mul_card Z
  have hidx : (P.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero
  have h1 : (Nat.card L : ℂ) = (Z.index : ℂ) * (Nat.card Z : ℂ) := by
    rw [← hcard]; push_cast; ring
  rw [h1, ← hmul]
  push_cast
  field_simp

theorem centralLayerWeightedChar_apply_of_mem_of_ne_one [P.Normal] [Z.Normal] (hZP : Z ≤ P)
    (hZc : Z ≤ centralizer (P : Set L)) (hPE : P ⊔ E = ⊤)
    (hfree : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1) {z : L} (hz : z ∈ Z)
    (hz1 : z ≠ 1) :
    centralLayerWeightedChar P (Z.subgroupOf P) (P.index : ℂ) z = -(Z.relIndex P : ℂ) := by
  classical
  rw [centralLayerWeightedChar_eq_regular_sub (E := E) hZP hZc hPE hfree,
    leftRegular_character_of_ne_one hz1, inflated_leftRegular_character_apply_of_mem Z hz]
  have hmul : Z.relIndex P * P.index = Z.index := Subgroup.relIndex_mul_index hZP
  have hidx : (P.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero
  rw [← hmul]
  push_cast
  field_simp
  ring

theorem centralLayerWeightedChar_apply_one_sub [P.Normal] [Z.Normal] (hZP : Z ≤ P)
    (hZc : Z ≤ centralizer (P : Set L)) (hPE : P ⊔ E = ⊤)
    (hfree : ∀ u ∈ E, u ≠ 1 → ∀ z ∈ Z, u * z = z * u → z = 1) {z : L} (hz : z ∈ Z)
    (hz1 : z ≠ 1) :
    centralLayerWeightedChar P (Z.subgroupOf P) (P.index : ℂ) 1
        - centralLayerWeightedChar P (Z.subgroupOf P) (P.index : ℂ) z = (Nat.card P : ℂ) := by
  rw [centralLayerWeightedChar_apply_one (E := E) hZP hZc hPE hfree,
    centralLayerWeightedChar_apply_of_mem_of_ne_one (E := E) hZP hZc hPE hfree hz hz1]
  have hPcard : Z.relIndex P * Nat.card Z = Nat.card P := relIndex_mul_card_of_le hZP
  rw [← hPcard]
  push_cast
  ring

end Node

namespace IsFreeCentralSection

variable {G : Type*} [Group G] {p a : ℕ} {L P E Z : Subgroup G}
  (h : IsFreeCentralSection p a L P E Z)

include h

theorem relIndex_subgroupOf_eq :
    (Z.subgroupOf L).relIndex (P.subgroupOf L) = Z.relIndex P :=
  Subgroup.relIndex_subgroupOf h.P_le

theorem natCard_P_subgroupOf : Nat.card (P.subgroupOf L) = Nat.card P :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.P_le).toEquiv

theorem centralLayerWeightedChar_natCard_E_eq [Finite G] [Fintype ↥L] :
    centralLayerWeightedChar (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
        (Nat.card E : ℂ)
      = centralLayerWeightedChar (P.subgroupOf L)
          ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ((P.subgroupOf L).index : ℂ) := by
  rw [h.index_subgroupOf_eq]

section Conclusions

variable [Fintype ↥L] [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal]

theorem centralLayerWeightedChar_eq_regular_sub (x : ↥L) :
    centralLayerWeightedChar (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
        ((P.subgroupOf L).index : ℂ) x
      = ((Representation.leftRegular ℂ ↥L).character x
          - (Representation.leftRegular ℂ (↥L ⧸ Z.subgroupOf L)).character
              (QuotientGroup.mk x)) / ((P.subgroupOf L).index : ℂ) :=
  CFSG.FeitThompson.centralLayerWeightedChar_eq_regular_sub
    (E := E.subgroupOf L) (fun _ hx => h.Z_le_P hx) h.Z_subgroupOf_le_centralizer
    h.sup_subgroupOf h.free_subgroupOf x

theorem isCharacter_centralLayerWeightedChar :
    ∃ W : FDRep ℂ ↥L, FDRep.character W =
      centralLayerWeightedChar (P.subgroupOf L)
        ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ((P.subgroupOf L).index : ℂ) := by
  refine CFSG.FeitThompson.isCharacter_centralLayerWeightedChar
    (a := a) h.prime ?_ ?_
  · rw [← h.natCard_P]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.P_le).toEquiv
  · exact le_inf (fun _ hx => h.Z_le_P hx) h.Z_subgroupOf_le_centralizer

theorem centralLayerWeightedChar_apply_one :
    centralLayerWeightedChar (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
        ((P.subgroupOf L).index : ℂ) 1
      = ((Z.subgroupOf L).relIndex (P.subgroupOf L) : ℂ)
        * ((Nat.card (Z.subgroupOf L) : ℂ) - 1) :=
  CFSG.FeitThompson.centralLayerWeightedChar_apply_one
    (E := E.subgroupOf L) (fun _ hx => h.Z_le_P hx) h.Z_subgroupOf_le_centralizer
    h.sup_subgroupOf h.free_subgroupOf

theorem centralLayerWeightedChar_apply_of_mem_of_ne_one {z : ↥L} (hz : z ∈ Z.subgroupOf L)
    (hz1 : z ≠ 1) :
    centralLayerWeightedChar (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
        ((P.subgroupOf L).index : ℂ) z
      = -((Z.subgroupOf L).relIndex (P.subgroupOf L) : ℂ) :=
  CFSG.FeitThompson.centralLayerWeightedChar_apply_of_mem_of_ne_one
    (E := E.subgroupOf L) (fun _ hx => h.Z_le_P hx) h.Z_subgroupOf_le_centralizer
    h.sup_subgroupOf h.free_subgroupOf hz hz1

theorem centralLayerWeightedChar_apply_one_sub {z : ↥L} (hz : z ∈ Z.subgroupOf L) (hz1 : z ≠ 1) :
    centralLayerWeightedChar (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
          ((P.subgroupOf L).index : ℂ) 1
        - centralLayerWeightedChar (P.subgroupOf L)
          ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ((P.subgroupOf L).index : ℂ) z
      = (Nat.card (P.subgroupOf L) : ℂ) :=
  CFSG.FeitThompson.centralLayerWeightedChar_apply_one_sub
    (E := E.subgroupOf L) (fun _ hx => h.Z_le_P hx) h.Z_subgroupOf_le_centralizer
    h.sup_subgroupOf h.free_subgroupOf hz hz1

section Values

variable [Finite G]

theorem centralLayerWeightedChar_natCard_E_apply_one :
    centralLayerWeightedChar (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
        (Nat.card E : ℂ) 1
      = (Z.relIndex P : ℂ) * ((Nat.card Z : ℂ) - 1) := by
  rw [h.centralLayerWeightedChar_natCard_E_eq, h.centralLayerWeightedChar_apply_one,
    h.relIndex_subgroupOf_eq, h.natCard_Z_subgroupOf]

theorem centralLayerWeightedChar_natCard_E_apply_of_mem_of_ne_one {z : G} (hzL : z ∈ L)
    (hz : z ∈ Z) (hz1 : z ≠ 1) :
    centralLayerWeightedChar (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
        (Nat.card E : ℂ) ⟨z, hzL⟩
      = -(Z.relIndex P : ℂ) := by
  rw [h.centralLayerWeightedChar_natCard_E_eq,
    h.centralLayerWeightedChar_apply_of_mem_of_ne_one (z := ⟨z, hzL⟩) hz
      (fun hcon => hz1 (congrArg Subtype.val hcon)),
    h.relIndex_subgroupOf_eq]

theorem centralLayerWeightedChar_natCard_E_apply_one_sub {z : G} (hzL : z ∈ L) (hz : z ∈ Z)
    (hz1 : z ≠ 1) :
    centralLayerWeightedChar (P.subgroupOf L) ((Z.subgroupOf L).subgroupOf (P.subgroupOf L))
          (Nat.card E : ℂ) 1
        - centralLayerWeightedChar (P.subgroupOf L)
          ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) (Nat.card E : ℂ) ⟨z, hzL⟩
      = (Nat.card P : ℂ) := by
  rw [h.centralLayerWeightedChar_natCard_E_eq,
    h.centralLayerWeightedChar_apply_one_sub (z := ⟨z, hzL⟩) hz
      (fun hcon => hz1 (congrArg Subtype.val hcon)),
    h.natCard_P_subgroupOf]

end Values

end Conclusions

end IsFreeCentralSection

end CFSG.FeitThompson
