module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutClasses
public import Certificates.Certificate27205

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.G24Aut

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard.Induction.AutBound
open Subgroup

section Rigid


theorem g24_rigid :
    ∃ b : ℕ → PP, ∃ tests : ℕ → List (List ℕ × ℕ), Rep nn tAa (b 0) ∧
      (∀ j, ∃ d ∈ twoBD, b j = d * b 0 * d⁻¹) ∧ Subgroup.closure (b '' {j | j < 4}) = twoBD ∧
      ∀ i, 1 ≤ i → i < 4 →
        (∀ t ∈ tests i, (∀ l ∈ t.1, l ≤ i) ∧ 0 < t.2 ∧ orderOf (tupleWord b (b i) t.1) = t.2) ∧
        {z | (∃ d ∈ twoBD, z = d * b 0 * d⁻¹) ∧
          ∀ t ∈ tests i, orderOf (tupleWord b z t.1) = t.2}.ncard ≤
          if i = 1 then 1024 else if i = 2 then 60 else 2 := by
  have h := Certificates.certificate27205
  have hX : permOfArr 1365 xa = xBar := strong0_eq
  have hY : permOfArr 1365 ya = yBar := strong1_eq
  rw [hX, hY] at h
  exact h

theorem g24_aut_card_le :
    Nat.card (MulAut ↥twoBD) ≤ 2 * Nat.card ↥twoBD := by
  classical
  obtain ⟨tA, htA, htAD, htAsq, htA1, -, hLa2, hLsz, hxcard, hfus⟩ := g24_classes
  obtain ⟨bP, tests, hrep0, hcl, hgenP, hlev⟩ := g24_rigid
  have hb0 : bP 0 = tA := Rep.unique hrep0 htA
  have hbD : ∀ j, bP j ∈ twoBD := fun j => by
    obtain ⟨d, hd, h⟩ := hcl j
    rw [h, hb0]
    exact mul_mem (mul_mem hd htAD) (inv_mem hd)
  let b : ℕ → ↥twoBD := fun j => ⟨bP j, hbD j⟩
  have hb0' : ((b 0 : ↥twoBD) : PP) = tA := hb0
  have hgen : Subgroup.closure (b '' {j | j < 4}) = ⊤ :=
    closure_eq_top_of_closure_coe twoBD b _ hgenP
  have hfusX : ∀ z : ↥twoBD, z * z = 1 → z ≠ 1 →
      (∃ g : ↥twoBD, g * z * g⁻¹ = b 0) ∨ ∃ g : ↥twoBD, g * z * g⁻¹ = xD := by
    intro z hz1 hz2
    have hz1' : (z : PP) * z = 1 := congrArg Subtype.val hz1
    have hz2' : (z : PP) ≠ 1 := fun h => hz2 (Subtype.ext h)
    rcases hfus z z.2 hz1' hz2' with ⟨d, hd, h⟩ | ⟨d, hd, h⟩
    · exact Or.inl ⟨⟨d, hd⟩, Subtype.ext (by rw [hb0']; exact h)⟩
    · exact Or.inr ⟨⟨d, hd⟩, Subtype.ext h⟩
  have hcard1 : (conjClass (b 0)).ncard ≤ 4095 := by
    rw [← Set.ncard_image_of_injective _ (Subtype.val_injective (p := (· ∈ twoBD))), ← hLsz]
    refine ncard_le_of_rep fun z ⟨w, hw, hwz⟩ => hLa2 z ?_
    obtain ⟨g, hg⟩ := mem_conjClass_iff.1 hw
    refine ⟨(g : PP), g.2, ?_⟩
    have := congrArg Subtype.val hg
    rw [← hwz, this]
    change (g : PP) * ((b 0 : ↥twoBD) : PP) * (g : PP)⁻¹ = (g : PP) * tA * (g : PP)⁻¹
    rw [hb0']
  have hcard2 : 4096 ≤ (conjClass xD).ncard := by
    rw [← Set.ncard_image_of_injective _ (Subtype.val_injective (p := (· ∈ twoBD)))]
    refine le_trans hxcard (Set.ncard_le_ncard ?_ (Set.toFinite _))
    rintro z ⟨d, hd, rfl⟩
    refine ⟨⟨d, hd⟩ * xD * ⟨d, hd⟩⁻¹, mem_conjClass_iff.2 ⟨⟨d, hd⟩, rfl⟩, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hu : b 0 * b 0 = 1 := Subtype.ext (by
    change ((b 0 : ↥twoBD) : PP) * ((b 0 : ↥twoBD) : PP) = 1
    rw [hb0']
    exact htAsq)
  have hu1 : b 0 ≠ 1 := fun h => htA1 (by rw [← hb0', h]; rfl)
  have hlevel : ∀ i, 1 ≤ i → i < 4 →
      (∀ α : MulAut ↥twoBD, (∀ j < i, α (b j) = b j) → α (b i) ∈ testClass b (b 0) (tests i)) ∧
        (testClass b (b 0) (tests i)).ncard ≤ if i = 1 then 1024 else if i = 2 then 60 else 2 := by
    intro i hi1 hi4
    obtain ⟨hown, hcnt⟩ := hlev i hi1 hi4
    have hbi : b i ∈ conjClass (b 0) := by
      obtain ⟨d, hd, h⟩ := hcl i
      exact mem_conjClass_iff.2 ⟨⟨d, hd⟩, Subtype.ext h⟩
    refine ⟨fun α hα => aut_mem_testClass α b hi1 hα hbi
      (fun t ht l hl => Nat.lt_succ_of_le ((hown t ht).1 l hl)) fun t ht => ?_, ?_⟩
    · rw [← orderOf_coe_tupleWord twoBD b (b i) t.1]
      exact (hown t ht).2.2
    · rw [← Set.ncard_image_of_injective _ (Subtype.val_injective (p := (· ∈ twoBD)))]
      exact le_trans (Set.ncard_le_ncard (coe_testClass_subset twoBD b (b 0) (tests i))
        (Set.toFinite _)) hcnt
  let T : ℕ → List (List ℕ × ℕ) := fun i => if i = 0 then [] else tests i
  have hT0 : T 0 = [] := by simp [T]
  have hTi : ∀ i, i ≠ 0 → T i = tests i := fun i hi => by simp [T, hi]
  have hS : ∀ i < 4, ∀ α : MulAut ↥twoBD, (∀ j < i, α (b j) = b j) →
      α (b i) ∈ testClass b (b 0) (T i) := by
    intro i hi α hα
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hT0]
      exact ⟨aut_preserves_class α hfusX (lt_of_le_of_lt hcard1 (by omega)) hu hu1,
        fun t ht => absurd ht List.not_mem_nil⟩
    · rw [hTi i (by omega)]
      exact (hlevel i hpos hi).1 α hα
  have hbound := card_mulAut_le_of_rigid (X := ↥twoBD) 4 b hgen
    (fun i => testClass b (b 0) (T i)) hS (fun i _ => Set.toFinite _)
  have hN0 : (testClass b (b 0) (T 0)).ncard ≤ 4095 := by
    have : testClass b (b 0) (T 0) = conjClass (b 0) := by
      ext w
      simp [testClass, hT0]
    rw [this]
    exact hcard1
  have hN1 : (testClass b (b 0) (T 1)).ncard ≤ 1024 := by
    have := (hlevel 1 le_rfl (by norm_num)).2
    rw [if_pos rfl] at this
    rwa [hTi 1 (by norm_num)]
  have hN2 : (testClass b (b 0) (T 2)).ncard ≤ 60 := by
    have := (hlevel 2 (by norm_num) (by norm_num)).2
    rw [if_neg (by norm_num), if_pos rfl] at this
    rwa [hTi 2 (by norm_num)]
  have hN3 : (testClass b (b 0) (T 3)).ncard ≤ 2 := by
    have := (hlevel 3 (by norm_num) (by norm_num)).2
    rw [if_neg (by norm_num), if_neg (by norm_num)] at this
    rwa [hTi 3 (by norm_num)]
  calc Nat.card (MulAut ↥twoBD) ≤ _ := hbound
    _ ≤ 4095 * 1024 * 60 * 2 := by
        rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
          Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hN0 hN1) hN2) hN3
    _ = 2 * 251596800 := by norm_num
    _ = 2 * Nat.card ↥twoBD := by rw [card_twoBD]

end Rigid

end CFSG.EvenSporadicStandard.G24Aut
