module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderOfNatural
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.NaturalSectionLS

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG.AGLEmbedding (blockV)
open CFSG.RankThree.PartTwo (altHeart)
open CFSG.Quasithin (IsMaxElemAbelian)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

variable {G : Type} [Group G]

theorem NaturalSectionLSL.exists_theta_shapes [Finite G] {S L : Subgroup G} {d : ℕ}
    (hd : d = 7 ∨ 9 ≤ d) (h : NaturalSectionLSL S L d)
    (hVS : blockV S L ≤ S) (hVN : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G))
    (hV : CFSG.Open.IsElemAbelian 2 (blockV S L)) :
    ∃ θ : ↥(L ⊔ S) →* Equiv.Perm (Fin d),
      (∀ σ ∈ alternatingGroup (Fin d), ∃ l : ↥L, θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = σ) ∧
      (∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ Subgroup.centralizer (blockV S L : Set G)) ∧
      ∀ A : Subgroup G, IsMaxElemAbelian S A →
        OffenderShapeConcl ((A.subgroupOf (L ⊔ S)).map θ) := by
  obtain ⟨π, θ, hπ, -, hAd, hequiv, hker⟩ := h
  have hUV : ⁅blockV S L, L⁆ ≤ blockV S L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have hl' : l ∈ Subgroup.normalizer (blockV S L : Set G) := hVN (Subgroup.mem_sup_left hl)
    have h1 : l * v⁻¹ * l⁻¹ ∈ blockV S L := by
      have := (Subgroup.mem_normalizer_iff.1 hl' v⁻¹).1 ((blockV S L).inv_mem hv)
      simpa [mul_assoc] using this
    simpa [commutatorElement_def, mul_assoc] using (blockV S L).mul_mem hv h1
  refine ⟨θ, hAd, theta_eq_one_iff (by omega) hπ hequiv hUV hker, fun A hA => ?_⟩
  exact offender_shape_of_section hd hπ hequiv (isElemAb2_of_isElemAbelian hV) hVS hUV
    (isElemAb2_of_isElemAbelian hA.2.1) hA.1 (hA.1.trans le_sup_right)
    (fun B hBS hB => hA.2.2 B hBS (isElemAbelian_of_isElemAb2 hB)) hker

@[expose] def NaturalSectionTheta (S L : Subgroup G) (d : ℕ) (θ : ↥(L ⊔ S) →* Equiv.Perm (Fin d)) :
    Prop :=
  ∃ π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d),
    Function.Surjective π ∧
    π.ker = (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅blockV S L, L⁆ ∧
    (∀ σ ∈ alternatingGroup (Fin d), ∃ l : ↥L, θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = σ) ∧
    SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ ∧
    ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G)

theorem NaturalSectionLSL.exists_theta_section_shapes [Finite G] {S L : Subgroup G} {d : ℕ}
    (hd : d = 7 ∨ 9 ≤ d) (h : NaturalSectionLSL S L d)
    (hVS : blockV S L ≤ S) (hVN : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G))
    (hV : CFSG.Open.IsElemAbelian 2 (blockV S L)) :
    ∃ θ : ↥(L ⊔ S) →* Equiv.Perm (Fin d),
      NaturalSectionTheta S L d θ ∧
      (∀ σ ∈ alternatingGroup (Fin d), ∃ l : ↥L, θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = σ) ∧
      (∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ Subgroup.centralizer (blockV S L : Set G)) ∧
      ∀ A : Subgroup G, IsMaxElemAbelian S A →
        OffenderShapeConcl ((A.subgroupOf (L ⊔ S)).map θ) := by
  obtain ⟨π, θ, hπ, hkerπ, hAd, hequiv, hker⟩ := h
  have hUV : ⁅blockV S L, L⁆ ≤ blockV S L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have hl' : l ∈ Subgroup.normalizer (blockV S L : Set G) := hVN (Subgroup.mem_sup_left hl)
    have h1 : l * v⁻¹ * l⁻¹ ∈ blockV S L := by
      have := (Subgroup.mem_normalizer_iff.1 hl' v⁻¹).1 ((blockV S L).inv_mem hv)
      simpa [mul_assoc] using this
    simpa [commutatorElement_def, mul_assoc] using (blockV S L).mul_mem hv h1
  refine ⟨θ, ⟨π, hπ, hkerπ, hAd, hequiv, hker⟩, hAd,
    theta_eq_one_iff (by omega) hπ hequiv hUV hker, fun A hA => ?_⟩
  exact offender_shape_of_section hd hπ hequiv (isElemAb2_of_isElemAbelian hV) hVS hUV
    (isElemAb2_of_isElemAbelian hA.2.1) hA.1 (hA.1.trans le_sup_right)
    (fun B hBS hB => hA.2.2 B hBS (isElemAbelian_of_isElemAb2 hB)) hker

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
