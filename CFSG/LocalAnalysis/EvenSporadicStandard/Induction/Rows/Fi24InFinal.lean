module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InWitness
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingInclusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Step
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Sporadic CFSG.Sporadic.Fi24 CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78
open CFSG.EvenSporadicStandard.Solomon78.Fi24Row (fi24_isConj_cases)
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Discharge

attribute [-instance] Subgroup.mul

theorem fi24inK_map_jR : fi24inK.map jR = Fi24.LE := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact fi24in_jR_mem_LE hk
  · intro hx
    obtain ⟨k, hk, rfl⟩ := fi24in_exists_of_mem_LE hx
    exact ⟨k, hk, rfl⟩

theorem fi24inK_perfect : ⁅fi24inK, fi24inK⁆ = fi24inK := by
  apply Subgroup.map_injective jR_injective
  rw [Subgroup.map_commutator, fi24inK_map_jR]
  exact Cover.commutator_eq_self_of_isPerfect (Group.isPerfect_def.2 commutator_LE)

theorem fi24inK_card : Nat.card fi24inK = 2 * 64561751654400 := by
  rw [← Subgroup.card_map_of_injective jR_injective, fi24inK_map_jR]
  exact card_LE

theorem fi24in_base_J : Fi24InBase ↥J tJ fi24inK := by
  have h1 : IsSporadic ↥J .Fi24Prime := ⟨fi24EquivJ.symm⟩
  have h2 : orderOf tJ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact tJ_mul_tJ) tJ_ne_one
  have h3 : ∀ k ∈ fi24inK, k * tJ = tJ * k := fun k hk => by
    have h := (Subgroup.mem_inf.1 hk).1
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    exact h
  have h5 : 2 * 64561751654400 ≤ Nat.card fi24inK := by rw [fi24inK_card]
  exact fi24in_base h1 h2 h3 fi24inK_perfect h5

theorem fi24in_exists_pinned_equiv {Y : Type} [Group Y] [Finite Y] (hY : IsSporadic Y .Fi24Prime)
    {uY : Y} {KY : Subgroup Y} (hu2 : orderOf uY = 2) (hKu : ∀ k ∈ KY, k * uY = uY * k)
    (hKp : ⁅KY, KY⁆ = KY) (hcard : 2 * 64561751654400 ≤ Nat.card KY) :
    ∃ f : Y ≃* ↥J, f uY = tJ ∧ KY.map f.toMonoidHom = fi24inK := by
  obtain ⟨e⟩ := hY
  let e1 : Y ≃* ↥J := e.trans fi24EquivJ
  have hs2 : e1 uY * e1 uY = 1 := by
    rw [← map_mul, mul_self_eq_one_of_orderOf_eq_two hu2, map_one]
  have hs1 : e1 uY ≠ 1 := fun h => by
    have := (map_eq_one_iff e1 e1.injective).1 h
    rw [this, orderOf_one] at hu2
    omega
  rcases fi24_isConj_cases CFSG.Fischer.polarFacts hs2 hs1 with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    obtain ⟨f, hf⟩ : ∃ f : Y ≃* ↥J, f = e1.trans (MulAut.conj c) := ⟨_, rfl⟩
    have hfu : f uY = tJ := by
      rw [hf]
      show c * e1 uY * c⁻¹ = tJ
      exact hc
    refine ⟨f, hfu, ?_⟩
    have hPc : KY.map f.toMonoidHom ≤ centralizer ({tJ} : Set ↥J) := by
      rintro _ ⟨k, hk, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      show f k * tJ = tJ * f k
      rw [← hfu, ← map_mul, ← map_mul, hKu k hk]
    have hPperf : ⁅KY.map f.toMonoidHom, KY.map f.toMonoidHom⁆ = KY.map f.toMonoidHom := by
      rw [← Subgroup.map_commutator, hKp]
    have hle := fi24in_base_J.le_of_perfect_le_centralizer hPperf hPc
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective f.injective, fi24inK_card]
    exact hcard
  · exfalso
    have hC := CFSG.Sporadic.FischerOddCore.card_centralizer_of_isConj h
    have hle : KY.map e1.toMonoidHom ≤ centralizer ({e1 uY} : Set ↥J) := by
      rintro _ ⟨k, hk, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      show e1 k * e1 uY = e1 uY * e1 k
      rw [← map_mul, ← map_mul, hKu k hk]
    have h3 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective e1.injective] at h3
    have h4 := (CFSG.Sporadic.FischerOddCore.fi24R2_centralizer_structure).1
    have h5 : Nat.card ↥(centralizer ({e1 uY} : Set ↥J)) = 160526499840 := by
      rw [← hC]
      exact h4
    omega

theorem fi24in_pairs : Fi24InPairs := by
  intro Y _ _ hY uY KY hpair
  obtain ⟨hu2, hKu, hKp, hcard⟩ := hpair
  obtain ⟨f, hfu, hfK⟩ := fi24in_exists_pinned_equiv hY hu2 hKu hKp hcard
  refine fi24in_vPairs_nonempty_of_equiv f hfK ?_
  rw [hfu]
  exact fi24in_pairs_pinned

theorem fi24in_generate : Fi24InGenerate := by
  intro Y _ _ hY uY KY hpair
  obtain ⟨hu2, hKu, hKp, hcard⟩ := hpair
  obtain ⟨f, hfu, hfK⟩ := fi24in_exists_pinned_equiv hY hu2 hKu hKp hcard
  refine fi24in_sol78Generate_of_equiv f hfK ?_
  rw [hfu]
  obtain ⟨v, hv, h2, -⟩ := fi24in_exists_witness
  intro l _ hl
  exact fi24in_generate_pinned ⟨v, hv, h2⟩ l hl

end Discharge

section Wrappers

theorem sol78Closing_fi24in_proved : Sol78Closing [.Fi24Prime] (fun _ => fiIn24) :=
  sol78Closing_fi24in fi24in_pairs fi24in_generate

end Wrappers

end CFSG.EvenSporadicStandard.Induction
