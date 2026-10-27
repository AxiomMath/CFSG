module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporBase
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1SporTable

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.GS82PumpInputs.PCSpor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf HarrisLit.T1.SporRow
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem factorial_div_two_ne {c N : ℕ} (hN : c < N.factorial / 2)
    (hchk : ∀ n < N, n.factorial / 2 ≠ c) (n : ℕ) : n.factorial / 2 ≠ c := by
  by_cases hn : n < N
  · exact hchk n hn
  · have h1 : N.factorial ≤ n.factorial := Nat.factorial_le (not_lt.1 hn)
    have h2 : N.factorial / 2 ≤ n.factorial / 2 := Nat.div_le_div_right h1
    omega

theorem three_dvd_factorial_div_two {n : ℕ} (hn : 3 ≤ n) : 3 ∣ n.factorial / 2 := by
  obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hn
  rw [hk, show Nat.factorial 3 = 2 * 3 by decide, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  exact dvd_mul_right 3 k

theorem not_cTypeOrder_of_rows {s : TauCeti.SporadicName} (hT : SporTable.TableExcl s)
    (hrow : ∀ c, (CatFC.SporadicInnerRow s c ∨ CatFC.SporadicOuterRow s c) →
      (∀ n : ℕ, n.factorial / 2 ≠ c) ∧ c ≠ 20160)
    {c : ℕ} (hd : c ∣ AGLEmbedding.sporOrd s)
    (hc : CatFC.SporadicInnerRow s c ∨ CatFC.SporadicOuterRow s c) : ¬ CTypeOrder c := by
  rintro (hO | ⟨n, -, rfl⟩ | rfl)
  · obtain ⟨h1, h2⟩ := hT c hO hd
    rcases hc with hc | hc
    · exact h1 hc
    · exact h2 hc
  · exact (hrow _ hc).1 n rfl
  · exact (hrow _ hc).2 rfl

theorem false_of_ru_rows {c : ℕ} (hd : c ∣ AGLEmbedding.sporOrd .Ru)
    (hc : CatFC.SporadicInnerRow .Ru c ∨ CatFC.SporadicOuterRow .Ru c) : ¬ CTypeOrder c := by
  rcases hc with hc | hc
  · simp only [CatFC.SporadicInnerRow] at hc
    rintro (hO | ⟨n, hn, rfl⟩ | rfl)
    · exact SporNum.not_oddLieOrder_ru (by simpa [AGLEmbedding.sporOrd] using hd) hc hO
    · exact hc (three_dvd_factorial_div_two (by omega))
    · exact hc (by norm_num)
  · simp only [CatFC.SporadicOuterRow] at hc

theorem rows_co1 : ∀ c, (CatFC.SporadicInnerRow .Co1 c ∨ CatFC.SporadicOuterRow .Co1 c) →
    (∀ n : ℕ, n.factorial / 2 ≠ c) ∧ c ≠ 20160 := by
  intro c hc
  simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow, or_false] at hc
  subst hc
  exact ⟨factorial_div_two_ne (N := 14) (by decide) (by decide), by norm_num⟩

theorem rows_fi22 : ∀ c, (CatFC.SporadicInnerRow .Fi22 c ∨ CatFC.SporadicOuterRow .Fi22 c) →
    (∀ n : ℕ, n.factorial / 2 ≠ c) ∧ c ≠ 20160 := by
  intro c hc
  simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow] at hc
  rcases hc with rfl | rfl | rfl
  · exact ⟨factorial_div_two_ne (N := 15) (by decide) (by decide), by norm_num⟩
  · exact ⟨factorial_div_two_ne (N := 13) (by decide) (by decide), by norm_num⟩
  · exact ⟨factorial_div_two_ne (N := 11) (by decide) (by decide), by norm_num⟩

theorem rows_b : ∀ c, (CatFC.SporadicInnerRow .B c ∨ CatFC.SporadicOuterRow .B c) →
    (∀ n : ℕ, n.factorial / 2 ≠ c) ∧ c ≠ 20160 := by
  intro c hc
  simp only [CatFC.SporadicInnerRow, CatFC.SporadicOuterRow, or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨factorial_div_two_ne (N := 25) (by decide) (by decide), by norm_num⟩
  · exact ⟨factorial_div_two_ne (N := 19) (by decide) (by decide), by norm_num⟩

section Table


theorem oddCore_fixed_eq_bot {s : TauCeti.SporadicName} (hfree : CatalogueU.SporadicOddCoreFree s)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier s) (σ : MulAut S) (hσ : orderOf σ = 2) :
    CFSG.oddCore (fixedSubgroup σ) = ⊥ :=
  oddCore_fixedSubgroup_eq_bot_of_mulAut hna
    (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hfree hna e) hσ

theorem false_of_rows (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    {s : TauCeti.SporadicName} (hfree : CatalogueU.SporadicOddCoreFree s)
    (hexcl : ∀ c, c ∣ AGLEmbedding.sporOrd s →
      (CatFC.SporadicInnerRow s c ∨ CatFC.SporadicOuterRow s c) → ¬ CTypeOrder c)
    {Y : Type} [Group Y] [Finite Y] {β : MulAut Y} {T : Subgroup Y} (h : Setting Y β T)
    (hTtop : T ≠ ⊤) (e : Y ⧸ center Y ≃* NativeSporadic.Carrier s) : False := by
  have : IsSimpleGroup (Quot Y) := isSimpleGroup_quot h.quasisimple h.oddCore
  have hna := nonabelian_quot h.quasisimple h.oddCore
  set e' := (quotEquiv h.oddCore).trans e
  obtain ⟨σ, hI⟩ := exists_image_of_oddCore h hTtop (oddCore_fixed_eq_bot hfree hna e')
  obtain ⟨hd, hin, hout⟩ := SporTable.comp_data hMcard hfree hna e' hI.proper
  obtain ⟨eT⟩ := hI.fus
  have hc := cTypeOrder_of_typC h.typC
  rw [Nat.card_congr eT.toEquiv] at hc
  set c := Nat.card (T.map (rho Y) ⧸ Open.fusionZStar (T.map (rho Y)))
  have hrow' : CatFC.SporadicInnerRow s c ∨ CatFC.SporadicOuterRow s c := by
    by_cases hσ : σ ∈ (MulAut.conj : Quot Y →* MulAut (Quot Y)).range
    · exact Or.inl (hin hσ)
    · exact Or.inr (hout hσ)
  exact hexcl _ hd hrow' hc

theorem false_of_ru (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    (hfree : CatalogueU.SporadicOddCoreFree .Ru)
    {Y : Type} [Group Y] [Finite Y] {β : MulAut Y} {T : Subgroup Y} (h : Setting Y β T)
    (hTtop : T ≠ ⊤) (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .Ru) : False :=
  false_of_rows hMcard hfree (fun _ hd hc => false_of_ru_rows hd hc) h hTtop e

theorem false_of_co1 (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    (hfree : CatalogueU.SporadicOddCoreFree .Co1)
    {Y : Type} [Group Y] [Finite Y] {β : MulAut Y} {T : Subgroup Y} (h : Setting Y β T)
    (hTtop : T ≠ ⊤) (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .Co1) : False :=
  false_of_rows hMcard hfree
    (fun _ hd hc => not_cTypeOrder_of_rows SporTable.tableExcl_Co1 rows_co1 hd hc) h hTtop e

theorem false_of_fi22 (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    (hfree : CatalogueU.SporadicOddCoreFree .Fi22)
    {Y : Type} [Group Y] [Finite Y] {β : MulAut Y} {T : Subgroup Y} (h : Setting Y β T)
    (hTtop : T ≠ ⊤) (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .Fi22) : False :=
  false_of_rows hMcard hfree
    (fun _ hd hc => not_cTypeOrder_of_rows SporTable.tableExcl_Fi22 rows_fi22 hd hc) h hTtop e

theorem false_of_b (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    (hfree : CatalogueU.SporadicOddCoreFree .B)
    {Y : Type} [Group Y] [Finite Y] {β : MulAut Y} {T : Subgroup Y} (h : Setting Y β T)
    (hTtop : T ≠ ⊤) (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .B) : False :=
  false_of_rows hMcard hfree
    (fun _ hd hc => not_cTypeOrder_of_rows SporTable.tableExcl_B rows_b hd hc) h hTtop e

end Table

end CFSG.ComponentClassification.GS82PumpInputs.PCSpor
