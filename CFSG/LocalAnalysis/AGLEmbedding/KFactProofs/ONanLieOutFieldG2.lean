module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldDefs
public import CFSG.RankThree.PartOne.S11d.FixedFactsExc

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.FieldFix
open CFSG.RankThree.LocalRank SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)
open CFSG.ComponentClassification.UnbalancedCatalog (even_G2_exact_automorphism_normal_form)

theorem fixesNonLocalized_g2
    (hNL : ChevalleySubfieldNonLocalized)
    {T : Type} [Group T] [Finite T] {p f : ℕ} (hp : p.Prime)
    (hM : LieModel T .G2 0 2 f) (hq : f ≠ p) {α : MulAut T} (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut T) : FixesNonLocalized α := by
  have hadm : StatedLieAdmissible .G2 0 2 f := ((lieModel_untwisted_iff untwistedTag_G2).mp hM).2.1
  have hf2 : 2 ≤ f := two_le_of_admissible_G2 hadm
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_G2 hM
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (adjointGroup .G2 K) := MulAut.congr e α with hα'
  obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hf2 K hKcard
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α'
  have hα'eq : α' = MulAut.conj x * entrywiseAdjointAut .G2 σ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hxσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_entrywiseAdjointAut]
  obtain ⟨hσord, hpf, ⟨h0, hh0⟩, -⟩ :=
    even_G2_noninner_prime_local_core_trivial hf2 hKcard hp ⊤ le_top ⟨α', Subgroup.mem_top _⟩
      hα'inn (by rw [Subgroup.orderOf_mk]; exact hα'ord) x σ hα'eq
  obtain ⟨f₀, hff⟩ := hpf
  have hf₀2 : 2 ≤ f₀ := by
    by_contra hlt
    have h1 : f₀ = 1 := by
      rcases Nat.eq_zero_or_pos f₀ with h2 | h2
      · rw [h2, mul_zero] at hff
        omega
      · omega
    exact hq (by rw [hff, h1, mul_one])
  obtain ⟨-, hkcard, -, hJC1, -⟩ := even_G2_canonical_field_centralizer_all_orders hf2 hKcard σ
  have hk4 : 3 ≤ Nat.card (fixSubfield σ) := by
    rw [hkcard, hσord, hff, Nat.mul_div_cancel_left f₀ hp.pos]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀2
  have hq' : CFSG.IsQuasisimple ↥(adjointGroup .G2 (fixSubfield σ)) :=
    CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card _ hk4
  obtain ⟨hsimple, hnc⟩ := fixedFieldImage_simple_of_quasisimple σ hq'
  have hM' : LieModel T .G2 0 2 (p * f₀) := by rw [← hff]; exact hM
  have hKcard' : Nat.card K = 2 ^ (p * f₀) := by rw [← hff]; exact hKcard
  have hadm' : StatedLieAdmissible .G2 0 2 f₀ := admissible_G2 hf₀2
  exact FixesNonLocalized.of_fixedFacts
    (exc_fixedFacts_of_conj_entrywise untwistedTag_G2 hp hadm' hKcard' e hM' α σ hσord
      (MulAut.conj h0) hh0 hJC1 hsimple hnc (hNL .G2 (Or.inl rfl) σ))

end CFSG.AGLEmbedding.LieOut
