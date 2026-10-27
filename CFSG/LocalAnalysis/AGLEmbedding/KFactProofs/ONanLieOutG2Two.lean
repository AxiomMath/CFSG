module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutPspTwoGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutG2TwoGroup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutPrimeMain
import CFSG.RankThree.PartOne.S11c.Sec66Glue

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.FieldFix
open CFSG.RankThree.LocalRank SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)
open CFSG.ComponentClassification.UnbalancedCatalog (even_G2_exact_automorphism_normal_form)


theorem genFixes_g2_two {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : LieModel T .G2 0 2 p) {α : MulAut T} (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) :
    GenFixes p α := by
  have hadm : StatedLieAdmissible .G2 0 2 p := ((lieModel_untwisted_iff untwistedTag_G2).mp hM).2.1
  have hf2 : 2 ≤ p := by omega
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
  obtain ⟨-, hkcard, -, hJC1, -⟩ := even_G2_canonical_field_centralizer_all_orders hf2 hKcard σ
  have hk2 : Nat.card (fixSubfield σ) = 2 := by
    rw [hkcard, hσord, Nat.div_self hp.pos, pow_one]
  have hNLJ := CFSG.SignalizerFunctorTheorem.NonLocalExc.nonLocalized_G2_of_card_eq_two σ hk2
  set φ : T ≃* adjointGroup .G2 K := e.trans (MulAut.conj h0) with hφ
  have hφα : MulAut.congr φ α = entrywiseAdjointAut .G2 σ := by
    have : MulAut.congr φ α = MulAut.conj h0 * MulAut.congr e α * (MulAut.conj h0)⁻¹ := rfl
    rw [this, ← hα']
    exact hh0
  have hfix : fixSub (entrywiseAdjointAut .G2 σ) =
      (fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K) := by
    ext y
    rw [Subgroup.mem_subgroupOf, ← hJC1]
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      exact (Subtype.ext hzy) ▸ hz
  have hNL : NonLocalized (fixSub α) :=
    nonLocalized_of_map_eq (φ := φ) ((fixSub_congr φ α).symm.trans (by rw [hφα]))
      (by rw [hfix]; exact hNLJ)
  have e3 : ↥(fixSub (entrywiseAdjointAut .G2 σ)) ≃* ↥(fixedFieldImage .G2 σ) :=
    (Subgroup.equivMapOfInjective _ (adjointGroup .G2 K).subtype
      (adjointGroup .G2 K).subtype_injective).trans (MulEquiv.subgroupCongr hJC1)
  have : Finite (fixSubfield σ) := inferInstance
  have hchar : CharP (fixSubfield σ) 2 := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hk2]; simp)
  let Φ : ↥(fixSub α) ≃* adjointGroup .G2 (fixSubfield σ) :=
    (fixSubEquiv φ α).trans ((MulEquiv.subgroupCongr (by rw [hφα])).trans
      (e3.trans (fixedFieldImageEquiv σ).symm))
  exact genFixes_of_equiv hp5 α Φ adjointGroup_closure_involutions (g2Two_exists_perfect hk2) hNL

theorem lieOut_of_g2_two {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {p : ℕ} {x : Y}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxp : x ^ p = 1)
    (hαinn : centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L))
    [Nontrivial (↥L ⧸ Subgroup.center ↥L)]
    (h : LieModel (↥L ⧸ Subgroup.center ↥L) .G2 0 2 p) : LieOutConcl L x :=
  lieOutConcl_of_genFixes hx hp hxp (overgroupLocal_of_lieModel_g2 h)
    (genFixes_g2_two hp hp5 h (centerQuotientConj_pow hx hxp) hαinn)

end CFSG.AGLEmbedding.LieOut
