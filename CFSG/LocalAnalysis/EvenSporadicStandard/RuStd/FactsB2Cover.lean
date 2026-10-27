
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB2Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.TwoPart
public import CFSG.Sporadic.Schreier.RuSEnum
public import Certificates.Certificate24930
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneBase

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.EvenSporadicStandard.HypOne
  CFSG.EvenSporadicStandard.TwoRu.HypOne CFSG.Sporadic.RuSchreier

namespace B2

theorem cGens_spec :
    ∀ l < cGens.size, CFSG.Sporadic.Th.Rep 4060 cGens[l]! ([ruC0, ruC1].getD l 1) ∧
      CFSG.Sporadic.Th.Rep 4060 cGensInv[l]! ([ruC0, ruC1].getD l 1)⁻¹ ∧
      [ruC0, ruC1].getD l 1 ∈ ruC := by
  have hC0 : ruC0 ∈ ruC := Subgroup.subset_closure (Set.mem_insert _ _)
  have hC1 : ruC1 ∈ ruC := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  intro l hl
  have hl2 : l < 2 := by simpa [cGens] using hl
  interval_cases l
  · exact ⟨by simpa [cGens] using rep_tblOfArr rep_ruC0,
      by simpa [cGensInv] using
        rep_tblOfArr (rep_ruInv rep_ruC0 ruBasic_check.2.2.2.2.2.2.1), by simpa using hC0⟩
  · exact ⟨by simpa [cGens] using rep_tblOfArr rep_ruC1,
      by simpa [cGensInv] using
        rep_tblOfArr (rep_ruInv rep_ruC1 ruBasic_check.2.2.2.2.2.2.2.1), by simpa using hC1⟩

theorem ruC_le_closure_cGens :
    ruC ≤ Subgroup.closure (([ruC0, ruC1].getD · 1) '' {l | l < cGens.size}) := by
  refine (Subgroup.closure_le _).2 ?_
  intro g hg
  have hsz : cGens.size = 2 := rfl
  rcases hg with rfl | rfl
  · exact Subgroup.subset_closure ⟨0, by simp [hsz], rfl⟩
  · exact Subgroup.subset_closure ⟨1, by simp [hsz], rfl⟩

theorem classFacts_of_check {r : Table}
    {rg : Equiv.Perm (Fin 4060)} (hr : CFSG.Sporadic.Th.Rep 4060 r rg)
    {q : Array Table × Array ℕ × Array ℕ} {N : ℕ}
    (h : classCheckOf 4060 cGens cGensInv r q N = true) :
    (conjSet ruC rg).ncard = N ∧ ∀ T ∈ q.1.toList, ∀ g : Equiv.Perm (Fin 4060),
      CFSG.Sporadic.Th.Rep 4060 T g → g ∈ conjSet ruC rg :=
  classCheckOf_spec ruC cGens_spec ruC_le_closure_cGens hr h

theorem exists_rep_ruInvRepOf {w : List ℤ}
    (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 2) :
    ∃ rg : Equiv.Perm (Fin 4060), CFSG.Sporadic.Th.Rep 4060 (ruInvRepOf w) rg := by
  obtain ⟨g, -, hg⟩ := rep_wordTables (by norm_num : (4060 : ℕ) < 2 ^ 32) ruC cGens_spec
    (w := w) hw
  exact ⟨g, hg⟩

theorem ruInv_cover
    (hall : all2 4060 ruLevS ruInvCoverTest = true) :
    ∀ s ∈ ruS, orderOf s = 2 → (fixSet s).ncard = 92 →
      ∃ T ∈ ruInvAll.toList, CFSG.Sporadic.Th.Rep 4060 T s := by
  refine ruS_forall (p := ruInvCoverTest)
    (P := fun s => orderOf s = 2 → (fixSet s).ncard = 92 →
      ∃ T ∈ ruInvAll.toList, CFSG.Sporadic.Th.Rep 4060 T s) ?_ hall
  intro t g ht hp h2 hfix
  have h1 : (ruIsInvolA t && ruFixCount t == 92) = true := by
    rw [Bool.and_eq_true, ruIsInvolA_iff ht, beq_iff_eq, ruFixCount_eq ht]
    exact ⟨h2, hfix⟩
  simp only [ruInvCoverTest, h1, Bool.not_true, Bool.false_or] at hp
  obtain ⟨T, hT, hTe⟩ := Array.any_eq_true'.1 (memT_of_memTH hp)
  exact ⟨T, Array.mem_toList_iff.2 hT, rep_of_tblEq (rep_tblOfArr ht) (tblEq_symm hTe)⟩

theorem exists_conj_mem_ruS_of_mem_ruC
    {x : Equiv.Perm (Fin 4060)}
    (hx : x ∈ ruC) (h2 : orderOf x = 2) : ∃ c ∈ ruC, c⁻¹ * x * c ∈ ruS := by
  have hS : Nat.card ruS = 2 ^ (Nat.card ruC).factorization 2 := by
    rw [card_ruS, card_ruC, two_pow_factorization_eq (k := 14) (b := 15) (by norm_num)
      (by norm_num)]
    norm_num
  have hx2 : x ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one x
  have hx4 : x ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hx2, one_pow]
  exact exists_conj_mem_of_card_pow_four ruS_leC hS hx hx4

theorem card_ruC_inf_centralizer_of_fixed
    {x : Equiv.Perm (Fin 4060)}
    (hx : x ∈ ruC) (h2 : orderOf x = 2) (hfix : (fixSet x).ncard = 92) (hz : x ≠ ruZ) :
    Nat.card ↥(ruC ⊓ Subgroup.centralizer {x}) = 8192 ∨
      Nat.card ↥(ruC ⊓ Subgroup.centralizer {x}) = 1024 ∨
      Nat.card ↥(ruC ⊓ Subgroup.centralizer {x}) = 512 ∨
      Nat.card ↥(ruC ⊓ Subgroup.centralizer {x}) = 384 := by
  have hcheck := Certificates.certificate24930
  simp only [ruInvCheck, Bool.and_eq_true] at hcheck
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2'⟩, h3⟩, h4⟩, hall⟩ := hcheck
  obtain ⟨c, hc, hs⟩ := exists_conj_mem_ruS_of_mem_ruC hx h2
  set s : Equiv.Perm (Fin 4060) := c⁻¹ * x * c with hsdef
  have hs2 : orderOf s = 2 := by
    have : s = (MulAut.conj c⁻¹) x := by simp [hsdef]
    rw [this, MulEquiv.orderOf_eq, h2]
  have hsfix : (fixSet s).ncard = 92 := by
    have h := ncard_fixSet_conj c⁻¹ x
    rw [inv_inv] at h
    rw [hsdef]
    exact h.trans hfix
  obtain ⟨T, hT, hTs⟩ := ruInv_cover hall s hs hs2 hsfix
  have hsx : s ∈ conjSet ruC x := ⟨c⁻¹, ruC.inv_mem hc, by simp [hsdef]⟩
  have key : ∀ {rg : Equiv.Perm (Fin 4060)} {q : Array Table × Array ℕ × Array ℕ} {N : ℕ},
      (conjSet ruC rg).ncard = N →
      (∀ T ∈ q.1.toList, ∀ g : Equiv.Perm (Fin 4060),
        CFSG.Sporadic.Th.Rep 4060 T g → g ∈ conjSet ruC rg) → T ∈ q.1.toList →
      conjSet ruC x = conjSet ruC rg ∧ (conjSet ruC x).ncard = N := by
    intro rg q N hN hmem hTq
    have hsr : s ∈ conjSet ruC rg := hmem T hTq s hTs
    have heq : conjSet ruC x = conjSet ruC rg :=
      (conjSet_eq_of_mem hsx).symm.trans (conjSet_eq_of_mem hsr)
    exact ⟨heq, by rw [heq, hN]⟩
  have hos := ncard_conjSet_mul_card ruC x
  rw [card_ruC] at hos
  simp only [ruInvAll, Array.toList_append, List.mem_append] at hT
  rcases hT with (((hT | hT) | hT) | hT) | hT
  ·
    obtain ⟨hN, hmem⟩ := classFacts_of_check (rg := ruZ) (rep_tblOfArr rep_ruZ) h0
    obtain ⟨heq, hcard⟩ := key hN hmem hT
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hcard
    have hxa : x ∈ conjSet ruC x := self_mem_conjSet ruC x
    have hza : ruZ ∈ conjSet ruC x := by
      rw [heq]
      exact self_mem_conjSet ruC ruZ
    rw [ha, Set.mem_singleton_iff] at hxa hza
    exact absurd (hxa.trans hza.symm) hz
  · obtain ⟨rg, hrg⟩ := exists_rep_ruInvRepOf (w := ruInvWord1)
      (by simp only [ruInvWord1]; decide)
    obtain ⟨hN, hmem⟩ := classFacts_of_check hrg h1
    obtain ⟨-, hcard⟩ := key hN hmem hT
    rw [hcard] at hos
    omega
  · obtain ⟨rg, hrg⟩ := exists_rep_ruInvRepOf (w := ruInvWord2)
      (by simp only [ruInvWord2]; decide)
    obtain ⟨hN, hmem⟩ := classFacts_of_check hrg h2'
    obtain ⟨-, hcard⟩ := key hN hmem hT
    rw [hcard] at hos
    omega
  · obtain ⟨rg, hrg⟩ := exists_rep_ruInvRepOf (w := ruInvWord3)
      (by simp only [ruInvWord3]; decide)
    obtain ⟨hN, hmem⟩ := classFacts_of_check hrg h3
    obtain ⟨-, hcard⟩ := key hN hmem hT
    rw [hcard] at hos
    omega
  · obtain ⟨rg, hrg⟩ := exists_rep_ruInvRepOf (w := ruInvWord4)
      (by simp only [ruInvWord4]; decide)
    obtain ⟨hN, hmem⟩ := classFacts_of_check hrg h4
    obtain ⟨-, hcard⟩ := key hN hmem hT
    rw [hcard] at hos
    omega

end B2

end CFSG.EvenSporadicStandard.RuStd
