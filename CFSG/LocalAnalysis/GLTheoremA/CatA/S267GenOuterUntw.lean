module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenOuterBase
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPFamilies
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Diag
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignTori
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (ExcCopy.exists_fixed_structure
  ExcCopy.isPerfect_adjointGroup ExcCopy.isSimpleGroup_adjointGroup_of_perfect
  exists_field_or_inndiag_FG exists_field_or_inndiag_E
  mem_of_pow_eq_one_of_pow_mem)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner_le_innAutDerived
  commutator_le_innAutDerived mem_innAutDerived_congr)

private theorem three_le_card_of_ringChar_ne_two {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) : 3 ≤ Nat.card K := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hn]
  have h2 := hℓ.two_le
  calc 3 ≤ ringChar K := by omega
    _ ≤ ringChar K ^ (n : ℕ) := Nat.le_self_pow n.ne_zero _

private theorem three_le_card_subfield {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    (k : Subfield K) : 3 ≤ Nat.card k := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : CharP k (ringChar K) := (k.subtype.charP_iff k.subtype_injective _).2 inferInstance
  haveI : Finite k := Subtype.finite
  exact three_le_card_of_ringChar_ne_two (by rw [ringChar.eq k (ringChar K)]; exact hK2)

section Field


theorem compsNormal_entrywiseAdjointAut (τ : Tag) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hk : τ = .G2 → 3 ≤ Nat.card (fixSubfield σ)) :
    CompsNormal ↥(fixSubgroup (entrywiseAdjointAut τ σ)) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨ι, hι, hJC, hJn, hsol⟩ := ExcCopy.exists_fixed_structure τ σ
  haveI : Finite (fixSubfield σ) := Subtype.finite
  obtain ⟨hs, hnc⟩ := ExcCopy.isSimpleGroup_adjointGroup_of_perfect τ (fixSubfield σ)
    (ExcCopy.isPerfect_adjointGroup τ (fixSubfield σ) hk)
  let e : adjointGroup τ (fixSubfield σ) ≃* ι.range := MonoidHom.ofInjective hι
  have hJs : IsSimpleGroup ι.range := e.symm.isSimpleGroup
  have hJnc : ∃ x y : ι.range, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨e x, e y, fun h => hxy (e.injective (by simpa using h))⟩
  haveI := hJn
  exact compsNormal_fixSubgroup_of_le hJC
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hJs
      hJnc) hsol

end Field

section Inndiag


theorem mem_innAutDerived_of_inndiag {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (β : MulAut ↥(adjointGroup τ K)) {h : ModGL τ K}
    (hh : h ∈ inndiagGroup τ K) (hβh : ∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹)
    (hp1 : h ^ p = 1) : β ∈ innAutDerived ↥(adjointGroup τ K) := by
  classical
  have hinn : h ∈ adjointGroup τ K → β ∈ innAutDerived ↥(adjointGroup τ K) := fun hmem =>
    inner_le_innAutDerived _ ⟨⟨h, hmem⟩, MulEquiv.ext fun c => Subtype.ext (by
      rw [hβh c]
      rfl)⟩
  obtain ⟨b, j, hj, rfl⟩ := hh
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact hinn (mul_mem (rootDiagUnit_mem_adjointGroup_of_det_one (Or.inl rfl) b) hj)
  · exact hinn (mul_mem (rootDiagUnit_mem_adjointGroup_of_det_one (Or.inr (Or.inl rfl)) b) hj)
  · refine commutator_le_innAutDerived _
      (CFSG.HardMathSupport.Dickson.Sec6.I923.e6Inndiag_le_commutator K ?_)
    have hβe : β = rootDiagAutHom Tag.E6 K b * MulAut.conj ⟨j, hj⟩ :=
      MulEquiv.ext fun c => Subtype.ext (by
        rw [hβh c, MulAut.mul_apply, MulAut.conj_apply]
        change _ = rootDiagUnit Tag.E6 b * ((⟨j, hj⟩ : adjointGroup Tag.E6 K) * c *
          (⟨j, hj⟩ : adjointGroup Tag.E6 K)⁻¹ : adjointGroup Tag.E6 K) *
          (rootDiagUnit Tag.E6 b)⁻¹
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group)
    rw [hβe]
    exact mul_mem (Subgroup.mem_sup_right ⟨b, rfl⟩) (Subgroup.mem_sup_left ⟨⟨j, hj⟩, rfl⟩)
  · refine hinn (mem_of_pow_eq_one_of_pow_mem _
      ((Nat.coprime_primes hp Nat.prime_two).2 hp2) hp1 ?_)
    have h1 : rootDiagUnit Tag.E7 (b * b) ∈ adjointGroup Tag.E7 K :=
      CFSG.SeitzReduction.E7Pilot.rootDiagUnit_mem_adjointGroup_of_isSquare fun l => ⟨b l, rfl⟩
    have h2 : rootDiagUnit Tag.E7 b⁻¹ * j * (rootDiagUnit Tag.E7 b⁻¹)⁻¹ ∈ adjointGroup Tag.E7 K :=
      conj_rootDiagUnit_mem_adjointGroup b⁻¹ hj
    have e : (rootDiagUnit Tag.E7 b * j) ^ 2 = rootDiagUnit Tag.E7 (b * b) *
        (rootDiagUnit Tag.E7 b⁻¹ * j * (rootDiagUnit Tag.E7 b⁻¹)⁻¹) * j := by
      rw [sq, rootDiagUnit_mul, ← rootDiagUnit_inv, inv_inv]
      group
    rw [e]
    exact mul_mem (mul_mem h1 h2) hj
  · exact hinn (mul_mem (rootDiagUnit_mem_adjointGroup_of_det_one (Or.inr (Or.inr rfl)) b) hj)

end Inndiag

section Untw


theorem compsNormal_untw {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (β : MulAut ↥(adjointGroup τ K)) (hβ : β ^ p = 1) (hβ1 : β ≠ 1)
    (hout : β ∉ innAutDerived ↥(adjointGroup τ K)) : CompsNormal ↥(fixSubgroup β) := by
  classical
  have hG2K : τ = .G2 → 3 ≤ Nat.card K := fun _ => three_le_card_of_ringChar_ne_two hK2
  have hdisp : (∃ (σ : K ≃+* K) (ψ : MulAut ↥(adjointGroup τ K)),
      σ ≠ 1 ∧ ψ * β * ψ⁻¹ = entrywiseAdjointAut τ σ) ∨
    (∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧
      h ^ p = 1 ∧ h ≠ 1) := by
    rcases hτ with h | h | h | h | h
    · exact exists_field_or_inndiag_FG (Or.inr h) hG2K hp hp2 β hβ hβ1
    · exact exists_field_or_inndiag_FG (Or.inl h) hG2K hp hp2 β hβ hβ1
    · exact exists_field_or_inndiag_E (Or.inl h) hp hp2 β hβ hβ1
    · exact exists_field_or_inndiag_E (Or.inr (Or.inl h)) hp hp2 β hβ hβ1
    · exact exists_field_or_inndiag_E (Or.inr (Or.inr h)) hp hp2 β hβ hβ1
  rcases hdisp with ⟨σ, ψ, -, hψ⟩ | ⟨h, hh, hβh, hp1, -⟩
  · refine compsNormal_fixSubgroup_of_conj ψ β ?_
    rw [hψ]
    exact compsNormal_entrywiseAdjointAut τ σ fun _ => three_le_card_subfield hK2 _
  · exact absurd (mem_innAutDerived_of_inndiag hτ hp hp2 β hh hβh hp1) hout

theorem compsNormal_untw_cat {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : TauCeti.PrimePower)
    (hv : (c q).Valid) (hq2 : q.p ≠ 2) {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (β : MulAut S) (hβ : β ^ p = 1) (hβ1 : β ≠ 1) (hout : β ∉ innAutDerived S) :
    CompsNormal ↥(fixSubgroup β) := by
  classical
  obtain ⟨K, _, hKfin, -, hKchar, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  let e' : S ≃* ↥(adjointGroup τ K) := e.trans eK
  refine compsNormal_fixSubgroup_of_congr e' ?_
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e' β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  have hout' : MulAut.congr e' β ∉ innAutDerived ↥(adjointGroup τ K) := fun h =>
    hout ((mem_innAutDerived_congr e').1 h)
  exact compsNormal_untw hτ (by rw [ringChar.eq K q.p]; exact hq2) hp hp2 _ hβ' hβ1' hout'

end Untw

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
