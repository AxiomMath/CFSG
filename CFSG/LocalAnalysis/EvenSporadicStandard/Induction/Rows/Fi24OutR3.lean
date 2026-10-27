module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutR2
public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi24RowAut

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Fi24 (R J JR tR D24 jR M MR jR_mem_JR tR_mul_tR tR_inv tR_not_mem_JR
  index_JR MR_le_JR mem_MR_or_of_commute commute_tR_of_mem_MR mul_tR_mem_MR J_le_R)
open CFSG.EvenSporadicStandard.Solomon78.Fi24Row (fi24_autModel fi24_equiv_P fi24_outer_cases)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Basic


theorem fi24OutR_mul_tR_mem {a : R} (ha : a ∉ (JR : Subgroup R)) : a * tR ∈ (JR : Subgroup R) :=
  (mul_mem_iff_of_index_two index_JR).2 (iff_of_false ha tR_not_mem_JR)

theorem fi24OutR_mul_mem {a b : R} (ha : a ∉ (JR : Subgroup R)) (hb : b ∉ (JR : Subgroup R)) :
    a * b ∈ (JR : Subgroup R) :=
  (mul_mem_iff_of_index_two index_JR).2 (iff_of_false ha hb)

theorem fi24OutR_inf_centralizer_tR : (JR : Subgroup R) ⊓ centralizer {tR} = MR := by
  ext x
  constructor
  · rintro ⟨hxJ, hxc⟩
    rcases mem_MR_or_of_commute hxc with h | h
    · exact h
    · exact absurd (((mul_mem_iff_of_index_two index_JR).1 (MR_le_JR h)).1 hxJ) tR_not_mem_JR
  · intro hx
    exact ⟨MR_le_JR hx, mem_centralizer_singleton_iff.2 (commute_tR_of_mem_MR hx)⟩

theorem fi24OutR_eq_conj_of_mem_D24 {x : R} (hx : x ∈ D24) :
    ∃ n ∈ (JR : Subgroup R), x = n * tR * n⁻¹ := by
  obtain ⟨g, hg⟩ := CFSG.Sporadic.Fi24.exists_conj_eq_tR hx
  exact ⟨(jR g)⁻¹, (JR : Subgroup R).inv_mem (jR_mem_JR g), by rw [← hg]; group⟩

theorem fi24OutR_coatom :
    IsCoatom (((JR : Subgroup R) ⊓ centralizer {tR}).subgroupOf (JR : Subgroup R)) := by
  rw [fi24OutR_inf_centralizer_tR]
  exact fi24OutR_isCoatom_map J_le_R CFSG.Sporadic.Fi24.isCoatom_M

section Fi23


theorem fi24OutR_card_MR : Nat.card ↥MR = 4089470473293004800 := by
  rw [Nat.card_congr CFSG.Sporadic.Fi24.fi23EquivJMR.toEquiv, CFSG.Sporadic.Fi23.card_J]

theorem fi24OutR_center : center ↥((JR : Subgroup R) ⊓ centralizer {tR}) = ⊥ := by
  rw [fi24OutR_inf_centralizer_tR]
  exact CFSG.Sporadic.Fi24.center_MR

theorem fi24OutR_card_cent :
    Nat.card ↥((JR : Subgroup R) ⊓ centralizer {tR}) = 4089470473293004800 := by
  rw [fi24OutR_inf_centralizer_tR, fi24OutR_card_MR]


theorem fi24OutR_card_inf_centralizer {f : R} (hf : f ∈ CFSG.Blueprint.Fischer.LocalClass D24 tR) :
    Nat.card ↥(MR ⊓ centralizer {f * tR}) = 129123503308800 := by
  set s : MR := ⟨f * tR, mul_tR_mem_MR hf⟩
  have h1 : MR ⊓ centralizer {f * tR} = (centralizer ({s} : Set MR)).map MR.subtype :=
    (fi24OutR_map_centralizer MR s).symm
  rw [h1, Subgroup.card_map_of_injective MR.subtype_injective,
    @fi24OutR_card_centralizer_equiv ↥MR ↥CFSG.Sporadic.Fi23.J (Subgroup.toGroup _)
      (Subgroup.toGroup _) CFSG.Sporadic.Fi24.fi23EquivJMR s]
  exact CFSG.Sporadic.Fi23.card_centralizer_of_mem (CFSG.Sporadic.Fi24.isConj_d_fi23EquivJMR hf)

theorem fi24OutR_pair : ∃ n ∈ (JR : Subgroup R), tR * n * tR⁻¹ * n⁻¹ ≠ 1 ∧
    tR * n * tR⁻¹ * n⁻¹ * tR = tR * (tR * n * tR⁻¹ * n⁻¹) ∧
    twoAdic ((JR : Subgroup R) ⊓ centralizer {tR} ⊓ centralizer {tR * n * tR⁻¹ * n⁻¹}) =
      twoAdic ((JR : Subgroup R) ⊓ centralizer {tR}) := by
  obtain ⟨f, hf, -⟩ := CFSG.Sporadic.Fi24.exists_two_mem_localClass
  obtain ⟨g, hg⟩ := CFSG.Sporadic.Fi24.exists_conj_eq_tR hf.1
  have hf' : f = (jR g)⁻¹ * tR * jR g := by rw [← hg]; group
  have hkey : tR * (jR g)⁻¹ * tR⁻¹ * (jR g)⁻¹⁻¹ = f * tR := by
    rw [tR_inv, inv_inv, hf.2.2, hf']
    group
  refine ⟨(jR g)⁻¹, (JR : Subgroup R).inv_mem (jR_mem_JR g), ?_, ?_, ?_⟩ <;> rw [hkey]
  · intro h
    apply hf.2.1
    calc f = f * tR * tR := by rw [mul_assoc, tR_mul_tR, mul_one]
      _ = tR := by rw [h, one_mul]
  · calc f * tR * tR = f := by rw [mul_assoc, tR_mul_tR, mul_one]
      _ = tR * f * tR := by rw [← hf.2.2, mul_assoc, tR_mul_tR, mul_one]
      _ = tR * (f * tR) := by rw [mul_assoc]
  · unfold twoAdic
    rw [fi24OutR_inf_centralizer_tR, fi24OutR_card_inf_centralizer hf, fi24OutR_card_MR,
      show (129123503308800 : ℕ) = 2 ^ 18 * 492567075 by norm_num,
      show (4089470473293004800 : ℕ) = 2 ^ 18 * 15600091832325 by norm_num,
      fi24OutR_factorization_two (by decide), fi24OutR_factorization_two (by decide)]

end Fi23

end Basic

section Facts


theorem fi24OutR_fusion (w : R) (hw : w * w = 1) :
    ∃ n ∈ (JR : Subgroup R), w * (n * tR * n⁻¹) = n * tR * n⁻¹ * w := by
  obtain ⟨x, hx, hwx⟩ := CFSG.Sporadic.Fi24.exists_commute_D24 CFSG.Fischer.polarFacts hw
  obtain ⟨n, hn, rfl⟩ := fi24OutR_eq_conj_of_mem_D24 hx
  exact ⟨n, hn, hwx⟩

theorem fi24OutR_allInner : AllInner ↥((JR : Subgroup R) ⊓ centralizer {tR}) := by
  rw [fi24OutR_inf_centralizer_tR]
  exact @AllInner.of_mulEquiv Fi23 ↥MR _ _ CFSG.Sporadic.Fi24.fi23EquivMR.symm
    fun α => CFSG.Sporadic.FischerOddCore.fi23_mulAut_eq_conj α

theorem fi24OutR_std :
    @Fi24OutFacts ↥(JR : Subgroup R) (Subgroup.toGroup _) (MulAut.conjNormal tR) :=
  fi24OutR_std_of fi24_autModel tR_mul_tR (fun _ ha => fi24OutR_mul_tR_mem ha) fi24OutR_fusion
    fi24OutR_pair fi24OutR_coatom fi24OutR_allInner fi24OutR_center fi24OutR_card_cent.le

end Facts

section Class


theorem fi24OutR_cases (w : R) (hw : w * w = 1) (hwJ : w ∉ (JR : Subgroup R)) :
    (∃ n ∈ (JR : Subgroup R), w = n * tR * n⁻¹) ∨
      ∃ n₁ n₂ x₃ : R, n₁ * tR * n₁⁻¹ ≠ n₂ * tR * n₂⁻¹ ∧
        n₁ * tR * n₁⁻¹ * (n₂ * tR * n₂⁻¹) = n₂ * tR * n₂⁻¹ * (n₁ * tR * n₁⁻¹) ∧
        ∀ c : R, c * w = w * c → ∀ x ∈ ({n₁ * tR * n₁⁻¹, n₂ * tR * n₂⁻¹, x₃} : Set R),
          c * x * c⁻¹ ∈ ({n₁ * tR * n₁⁻¹, n₂ * tR * n₂⁻¹, x₃} : Set R) := by
  rcases fi24_outer_cases hw hwJ with hD | hT
  · exact Or.inl (fi24OutR_eq_conj_of_mem_D24 hD)
  · obtain ⟨x₁, x₂, x₃, h₁, h₂, -, n12, -, -, c12, -, -, -, hperm⟩ := hT
    obtain ⟨n₁, -, rfl⟩ := fi24OutR_eq_conj_of_mem_D24 h₁
    obtain ⟨n₂, -, rfl⟩ := fi24OutR_eq_conj_of_mem_D24 h₂
    exact Or.inr ⟨n₁, n₂, x₃, n12, c12, hperm⟩

theorem fi24OutR_class {ν : MulAut ↥(JR : Subgroup R)} (hν : ν * ν = 1)
    (hnot : ¬ ∃ g : ↥(JR : Subgroup R), ν = MulAut.conj g) {B : Subgroup ↥(JR : Subgroup R)}
    (hB : B ≤ (fixSubgroup ν : Subgroup ↥(JR : Subgroup R))) (hperf : ⁅B, B⁆ = B)
    (hcard : 4089470473293004800 ≤ Nat.card B) :
    @Fi24OutFacts ↥(JR : Subgroup R) (Subgroup.toGroup _) ν ∧
      B = (fixSubgroup ν : Subgroup ↥(JR : Subgroup R)) :=
  fi24OutR_class_of fi24_autModel tR_mul_tR tR_not_mem_JR (fun _ _ ha hb => fi24OutR_mul_mem ha hb)
    fi24OutR_std fi24OutR_center fi24OutR_card_cent fi24OutR_cases hν hnot hB hperf hcard

theorem fi24OutR_class_of_isSporadic {Y : Type} [Group Y] (hY : IsSporadic Y .Fi24Prime)
    {ν : MulAut Y} (hν : ν * ν = 1) (hnot : ¬ ∃ g : Y, ν = MulAut.conj g) {B : Subgroup Y}
    (hB : B ≤ fixSubgroup ν) (hperf : ⁅B, B⁆ = B) (hcard : 4089470473293004800 ≤ Nat.card B) :
    Fi24OutFacts Y ν ∧ B = fixSubgroup ν := by
  obtain ⟨e⟩ := fi24_equiv_P hY
  exact @fi24OutR_class_transport Y ↥(JR : Subgroup R) _ (Subgroup.toGroup _) e
    (fun _ h1 h2 _ h3 h4 h5 => fi24OutR_class h1 h2 h3 h4 h5) _ hν hnot _ hB hperf hcard

end Class

end CFSG.EvenSporadicStandard.Induction
