module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdDefs
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG.Open CFSG.GH74.GLS

section Map

variable {G : Type} [Group G]

theorem centralizer_map_equiv (φ : G ≃* G) (L : Subgroup G) :
    centralizer ((L.map φ.toMonoidHom : Subgroup G) : Set G) =
      (centralizer (L : Set G)).map φ.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨φ.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := Subgroup.mem_centralizer_iff.1 hx (φ l) ⟨l, hl, rfl⟩
    apply φ.injective
    simpa using h1
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hy l hl
    simpa using congrArg φ h1

theorem normalizer_map_equiv (φ : G ≃* G) (L : Subgroup G) :
    normalizer ((L.map φ.toMonoidHom : Subgroup G) : Set G) =
      (normalizer (L : Set G)).map φ.toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq L φ).symm

theorem standardComponentIsStandard_map (φ : G ≃* G) {L : Subgroup G}
    (h : standardComponentIsStandard L) :
    standardComponentIsStandard (L.map φ.toMonoidHom) :=
  CFSG.Open.standardComponentIsStandard.map_mulEquiv φ h

theorem conjugate_eq_map (L : Subgroup G) (g : G) :
    CFSG.conjugate L g = L.map (MulAut.conj g⁻¹).toMonoidHom := rfl

theorem mem_conjugate_iff' {L : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate L g ↔ g * x * g⁻¹ ∈ L := by
  rw [conjugate_eq_map, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

theorem conj_mem_conjugate {L : Subgroup G} {g x : G} (hx : x ∈ L) :
    g⁻¹ * x * g ∈ CFSG.conjugate L g := by
  rw [mem_conjugate_iff']
  simpa [mul_assoc] using hx

theorem card_conjugate (L : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate L g) = Nat.card L :=
  (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective)

theorem standardComponentIsStandard_conjugate (g : G) {L : Subgroup G}
    (h : standardComponentIsStandard L) :
    standardComponentIsStandard (CFSG.conjugate L g) :=
  standardComponentIsStandard_map (MulAut.conj g⁻¹) h

theorem centralizer_conjugate (L : Subgroup G) (g : G) :
    centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) =
      CFSG.conjugate (centralizer (L : Set G)) g :=
  centralizer_map_equiv (MulAut.conj g⁻¹) L

theorem normalizer_conjugate (L : Subgroup G) (g : G) :
    normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) =
      CFSG.conjugate (normalizer (L : Set G)) g :=
  normalizer_map_equiv (MulAut.conj g⁻¹) L

end Map

section StdMap

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {n : ℕ} {z : G}

theorem StdSetup.map (h : StdSetup G L n z) (φ : G ≃* G) :
    StdSetup G (L.map φ.toMonoidHom) n (φ z) := by
  have hC := centralizer_map_equiv φ L
  refine ⟨h.nonab, standardComponentIsStandard_map φ h.standard, h.hn, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact isDoubleCoverOfAlt_congr' (Subgroup.equivMapOfInjective L φ.toMonoidHom φ.injective)
      h.cover
  · rw [MulEquiv.orderOf_eq]
    exact h.hz
  · exact Subgroup.mem_map_of_mem _ h.z_mem
  · rw [hC]
    exact Subgroup.mem_map_of_mem _ h.z_cent
  · rw [centralizer_singleton_map_mulEquiv φ z, normalizer_map_equiv, h.cent_eq]
  · obtain ⟨g, hg1, hg2⟩ := h.exists_partner
    have key : (φ g)⁻¹ * φ z * φ g = φ (g⁻¹ * z * g) := by simp
    refine ⟨φ g, ?_, ?_⟩
    · rw [key]
      exact fun he => hg1 (φ.injective he)
    · rw [key, ← map_mul, ← map_mul]
      exact congrArg φ hg2
  · intro P hP hP2
    have hP' : P.map φ.symm.toMonoidHom ≤ centralizer (L : Set G) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      have h1 := hP hy
      rw [hC] at h1
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 h1
      simpa using hw
    let e : ↥P ≃* ↥(P.map φ.symm.toMonoidHom) :=
      Subgroup.equivMapOfInjective P φ.symm.toMonoidHom φ.symm.injective
    have hcyc := h.cyclic _ hP' (hP2.of_equiv e)
    exact isCyclic_of_surjective (e.symm : ↥(P.map φ.symm.toMonoidHom) →* ↥P) e.symm.surjective
  · intro x hx hx2
    rw [hC] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hy2 : orderOf y = 2 := by
      rw [← hx2]
      exact (MulEquiv.orderOf_eq φ y).symm
    exact congrArg φ (h.inv_unique y hy hy2)

theorem StdSetup.conj (h : StdSetup G L n z) (g : G) :
    StdSetup G (CFSG.conjugate L g) n (g⁻¹ * z * g) := by
  have e : (MulAut.conj g⁻¹ : G ≃* G) z = g⁻¹ * z * g := by simp
  rw [← e]
  exact h.map (MulAut.conj g⁻¹)

end StdMap

end CFSG.OddStandard.Solomon75
