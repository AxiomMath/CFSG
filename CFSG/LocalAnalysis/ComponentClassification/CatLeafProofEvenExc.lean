module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofGLS3Split
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenGFE
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionFixedFourGroupTransport
public import CFSG.GH74.Orders.LieType

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem untwistedChevalleyModel_of_mulEquiv
    {G : Type} [Group G] {τ : Tag} {k : Type} [Field k] [Finite k] {q : ℕ}
    (hk : Nat.card k = q) (e : G ≃* adjointGroup τ k) :
    UntwistedChevalleyModel G τ q :=
  ⟨k, inferInstance, inferInstance, hk, ⟨e.trans (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).symm)⟩⟩

@[expose] def fixedSubgroupCongrEquiv {K C' : Type} [Group K] [Group C'] (e : K ≃* C')
    (α : MulAut K) : fixedSubgroup α ≃* fixedSubgroup (MulAut.congr e α) :=
  ((fixedSubgroup α).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (ExcSelector.fixedSubgroup_congr e α).symm)

variable {F : Type} [Field F]

theorem even_E7_E8_outer_fixed
    [Finite F] {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) (β : MulAut (adjointGroup τ F)) (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ inner (adjointGroup τ F)) :
    ∃ e : ℕ, 1 ≤ e ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ e ∧
      IsSimpleGroup (adjointGroup τ k) ∧ Nonempty (fixedSubgroup β ≃* adjointGroup τ k) := by
  have : CharP F 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hF
  have hchar : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf F hF τ hτ
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF β
  have hσ : Θ β = σ := hΘ β g σ hgσ
  rcases hinv β hβ2 with h1 | ⟨⟨e, he⟩, hpow⟩
  · have hker' : β ∈ Θ.ker := MonoidHom.mem_ker.2 h1
    rw [hker] at hker'
    exact absurd hker' hβo
  have he1 : 1 ≤ e := by omega
  have hF' : Nat.card F = 2 ^ (2 * e) := by rw [hF, he, two_mul]
  have hσe : ∀ c, σ c = c ^ 2 ^ e := fun c => by
    rw [← hσ, hpow c, show f / 2 = e by omega]
  obtain ⟨_, -, hdesc⟩ :=
    (even_exceptional_quadratic_field_graph_field_involution_descent he1 F hF' σ.toRingHom
      hσe).1 τ
  obtain ⟨ψ, hψ, -⟩ := (hdesc g 1).2 β
    (fun u => by rw [hgσ u, rootDiagUnit_one, mul_one, inv_one, mul_one]) (by rw [← sq, hβ2])
  have hk := ExcSelector.card_fixSubfield_of_pow he1 hF' hσe
  have hfix := ExcSelector.fixedSubgroup_eq_fixedFieldImage_even (τ := τ) (by
    rcases hτ with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hchar σ hψ
  have hc : MulAut.congr ψ β = ψ * β * ψ⁻¹ := MulEquiv.ext fun _ => rfl
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ F := fun x hx => (fixedFieldImage_le hx).1
  have hβψ : fixedSubgroup (MulAut.congr ψ β) =
      (fixedFieldImage τ σ).subgroupOf (adjointGroup τ F) := by rw [hc, hfix]
  have hs : IsSimpleGroup (adjointGroup τ (fixSubfield σ)) := by
    rcases hτ with rfl | rfl
    · exact (ExcSelector.adjointGroup_E7_even he1 hk).1
    · exact (ExcSelector.adjointGroup_E8_even he1 hk).1
  refine ⟨e, he1, fixSubfield σ, inferInstance, inferInstance, hk, hs, ⟨?_⟩⟩
  exact (fixedSubgroupCongrEquiv ψ β).trans ((MulEquiv.subgroupCongr hβψ).trans
    ((Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm))

theorem lieModel_of_mulEquiv_adjointGroup_E7_E8
    {G : Type} [Group G] {t : StatedLieTag} {τ : Tag}
    (htτ : t = .E7 ∧ τ = .E7 ∨ t = .E8 ∧ τ = .E8) {k : Type} [Field k] [Finite k] {e : ℕ}
    (he : 1 ≤ e) (hk : Nat.card k = 2 ^ e) (E : G ≃* adjointGroup τ k) :
    StatedLieAdmissible t 0 2 e ∧ LieModel G t 0 2 e := by
  rcases htτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨⟨Nat.prime_two, he, rfl⟩, Or.inr (Or.inl ⟨rfl, by decide,
      ⟨⟨Nat.prime_two, he, rfl⟩, untwistedChevalleyModel_of_mulEquiv hk E⟩⟩)⟩
  · exact ⟨⟨Nat.prime_two, he, rfl⟩, Or.inr (Or.inl ⟨rfl, by decide,
      ⟨⟨Nat.prime_two, he, rfl⟩, untwistedChevalleyModel_of_mulEquiv hk E⟩⟩)⟩

theorem evenOuterFamilyInput_E7_E8
    {t : StatedLieTag} (ht : t = .E7 ∨ t = .E8) : EvenOuterFamilyInput t := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨τ, hτ, htτ, hu⟩ : ∃ τ : Tag, (τ = .E7 ∨ τ = .E8) ∧
      (t = .E7 ∧ τ = .E7 ∨ t = .E8 ∧ τ = .E8) ∧ UntwistedChevalleyModel K τ (2 ^ f) := by
    rcases ht with rfl | rfl
    · exact ⟨.E7, Or.inl rfl, Or.inl ⟨rfl, rfl⟩,
        (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2⟩
    · exact ⟨.E8, Or.inr rfl, Or.inr ⟨rfl, rfl⟩,
        (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hu
  have : Finite (ModGL τ F) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup τ F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨e', he', k, _, _, hk, hs, ⟨Φ⟩⟩ := even_E7_E8_outer_fixed hτ hf hF β hβ2 hβo
  have : Finite (ModGL τ k) := finite_modGL
  obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
    ((fixedSubgroupCongrEquiv e α).trans Φ) hP
  exact Or.inl ⟨t, 0, e', lieModel_of_mulEquiv_adjointGroup_E7_E8 htτ he' hk E⟩

theorem evenOuterFamilyInput_E7
    : EvenOuterFamilyInput .E7 :=
  evenOuterFamilyInput_E7_E8 (Or.inl rfl)

theorem evenOuterFamilyInput_E8
    : EvenOuterFamilyInput .E8 :=
  evenOuterFamilyInput_E7_E8 (Or.inr rfl)

end CFSG.ComponentClassification.CatLeafProof
