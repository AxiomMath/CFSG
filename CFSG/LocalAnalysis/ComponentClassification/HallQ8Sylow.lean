module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallLift

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G]

@[expose] def cjS (V : Subgroup G) (g : G) : Subgroup G :=
  V.map (MulAut.conj g⁻¹).toMonoidHom

theorem mem_cjS {V : Subgroup G} {g x : G} : x ∈ cjS V g ↔ g * x * g⁻¹ ∈ V := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    have : g * (MulAut.conj g⁻¹).toMonoidHom v * g⁻¹ = v := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [this]
    exact hv
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem cjS_mul {V : Subgroup G} {g h : G} : cjS (cjS V g) h = cjS V (g * h) := by
  ext x
  rw [mem_cjS, mem_cjS, mem_cjS, show g * h * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ by group]

theorem card_cjS (V : Subgroup G) (g : G) : Nat.card (cjS V g) = Nat.card V :=
  card_map_of_injective (MulAut.conj g⁻¹).injective

theorem isPGroup_cjS {V : Subgroup G} (hV : IsPGroup 2 V) (g : G) : IsPGroup 2 (cjS V g) :=
  hV.map _

theorem cjS_eq_of_mem_normalizer {W : Subgroup G} {n : G} (hn : n ∈ normalizer (W : Set G)) :
    cjS W n = W := by
  ext x
  rw [mem_cjS]
  exact (mem_normalizer_iff.mp hn x).symm

theorem exists_conj_sylow [Finite G] {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) {V : Subgroup G}
    (hSV : S ≤ normalizer (V : Set G)) (g : G) {R : Subgroup G} (hR : IsPGroup 2 R)
    (hRN : R ≤ normalizer ((cjS V g : Subgroup G) : Set G)) :
    ∃ t : G, cjS V t = cjS V g ∧ R ≤ cjS S t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer ((cjS V g : Subgroup G) : Set G) with hN
  have hS'N : cjS S g ≤ N := by
    intro x hx
    rw [mem_cjS] at hx
    rw [hN, mem_normalizer_iff]
    intro v
    rw [mem_cjS, mem_cjS]
    have h1 := mem_normalizer_iff.mp (hSV hx) (g * v * g⁻¹)
    rw [show g * x * g⁻¹ * (g * v * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * v * x⁻¹) * g⁻¹ by group]
      at h1
    exact h1
  obtain ⟨P, hP, hRP⟩ := FooteLit.exists_isSylowOf_ge_of_le hRN hR
  obtain ⟨n, hnN, hn⟩ := FooteLit.exists_conj_le_of_isSylowOf hP hS'N (isPGroup_cjS hS.isPGroup g)
  have hle : cjS (cjS S g) n ≤ P := by
    intro x hx
    rw [mem_cjS] at hx
    have := hn _ hx
    rwa [show n⁻¹ * (n * x * n⁻¹) * n = x by group] at this
  have hcard : Nat.card P ≤ Nat.card (cjS (cjS S g) n) := by
    rw [card_cjS, card_cjS]
    exact card_le_of_isSylowOf_top hS hP.isPGroup |>.trans' le_rfl
  have heq : cjS (cjS S g) n = P := eq_of_le_of_card_ge hle hcard
  refine ⟨g * n, ?_, ?_⟩
  · rw [← cjS_mul, cjS_eq_of_mem_normalizer hnN]
  · rw [← cjS_mul, heq]
    exact hRP

end CFSG.ComponentClassification.Foote5.HallGen
