module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Facts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Quasithin
open CFSG.EvenSmallLie.UnitarySix.SolomonWong (card_conjSubgroup conjSubgroup_sq)

variable {G : Type*} [Group G] {t : G} {L E : Subgroup G}

theorem mem_normalizer_conjSubgroup_iff {l x : G} :
    x ∈ normalizer (conjSubgroup E l : Set G) ↔ l * x * l⁻¹ ∈ normalizer (E : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  simp only [mem_conjSubgroup_iff]
  constructor
  · intro h e
    have h1 := h (l⁻¹ * e * l)
    have e1 : l * (l⁻¹ * e * l) * l⁻¹ = e := by group
    have e2 : l * (x * (l⁻¹ * e * l) * x⁻¹) * l⁻¹ = l * x * l⁻¹ * e * (l * x * l⁻¹)⁻¹ := by group
    rwa [e1, e2] at h1
  · intro h y
    have h1 := h (l * y * l⁻¹)
    have e2 : l * (x * y * x⁻¹) * l⁻¹ = l * x * l⁻¹ * (l * y * l⁻¹) * (l * x * l⁻¹)⁻¹ := by group
    rwa [e2]

theorem Facts.conjSubgroup_of_mem (D : Facts G t L E) {l : G} (hl : l ∈ L) :
    Facts G t L (conjSubgroup E l) := by
  have hLl : conjSubgroup L l = L :=
    conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hl)
  have hNl : normalizer ((conjSubgroup E l : Subgroup G) : Set G) =
      conjSubgroup (normalizer (E : Set G)) l := by
    ext x
    rw [mem_normalizer_conjSubgroup_iff, mem_conjSubgroup_iff]
  refine ⟨D.le_centralizer, D.centralizer_le, ?_,
    conjSubgroup_sq D.E_sq l, ?_, D.rank, D.inv, ?_, ?_, ?_, ?_, D.outer⟩
  · intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have h1 := D.E_le hx
    have h2 : x = l⁻¹ * (l * x * l⁻¹) * l := by group
    rw [h2]
    exact L.mul_mem (L.mul_mem (L.inv_mem hl) h1) hl
  · rw [card_conjSubgroup, D.card_E]
  · intro s hs hs2
    obtain ⟨l₀, hl₀, h₀⟩ := D.fuse s hs hs2
    refine ⟨l₀ * l, L.mul_mem hl₀ hl, ?_⟩
    rw [mem_conjSubgroup_iff]
    have h1 : l * ((l₀ * l)⁻¹ * s * (l₀ * l)) * l⁻¹ = l₀⁻¹ * s * l₀ := by group
    rw [h1]
    exact h₀
  · intro x hx
    obtain ⟨hxN, hxL⟩ := hx
    have hx'N : l * x * l⁻¹ ∈ normalizer (E : Set G) := mem_normalizer_conjSubgroup_iff.1 hxN
    have hx'L : l * x * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl)
    have h1 := D.gen ⟨hx'N, hx'L⟩
    have h2 : x ∈ (E ⊔ closure {y | y ∈ normalizer (E : Set G) ⊓ L ∧ Odd (orderOf y)}).map
        (MulAut.conj l⁻¹).toMonoidHom := by
      refine ⟨l * x * l⁻¹, h1, ?_⟩
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
      group
    rw [Subgroup.map_sup, MonoidHom.map_closure] at h2
    refine sup_le_sup_left (Subgroup.closure_mono ?_) _ h2
    rintro _ ⟨y, ⟨hyN, hyodd⟩, rfl⟩
    have e1 : (MulAut.conj l⁻¹).toMonoidHom y = l⁻¹ * y * l := by
      simp [MulAut.conj_apply]
    rw [Set.mem_setOf_eq, e1]
    refine ⟨⟨mem_normalizer_conjSubgroup_iff.2 ?_, ?_⟩, ?_⟩
    · have h4 : l * (l⁻¹ * y * l) * l⁻¹ = y := by group
      rw [h4]
      exact hyN.1
    · exact L.mul_mem (L.mul_mem (L.inv_mem hl) hyN.2) hl
    · have h4 := MulEquiv.orderOf_eq (MulAut.conj l⁻¹) y
      rw [MulAut.conj_apply, inv_inv] at h4
      rw [h4]
      exact hyodd
  · rw [hNl]
    have h2 := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj l⁻¹).toMonoidHom)
      (normalizer (E : Set G)) L (MulAut.conj l⁻¹).injective
    have h3 : L.map (MulAut.conj l⁻¹).toMonoidHom = L := hLl
    rw [h3] at h2
    exact h2 ▸ D.odd_index
  · intro B hB hB2 hBn
    have hB0 : conjSubgroup B l⁻¹ ≤ normalizer (E : Set G) ⊓ L := by
      intro x hx
      rw [mem_conjSubgroup_iff] at hx
      obtain ⟨h1, h2⟩ := hB hx
      refine ⟨?_, ?_⟩
      · have h3 := mem_normalizer_conjSubgroup_iff.1 h1
        have h4 : l * (l⁻¹ * x * l⁻¹⁻¹) * l⁻¹ = x := by group
        rwa [h4] at h3
      · have h4 : x = l * (l⁻¹ * x * l⁻¹⁻¹) * l⁻¹ := by group
        rw [h4]
        exact L.mul_mem (L.mul_mem hl h2) (L.inv_mem hl)
    have heq := D.unique _ hB0 (conjSubgroup_sq hB2 l⁻¹)
      (by rw [card_conjSubgroup, hBn])
    have h5 := congrArg (fun A => conjSubgroup A l) heq
    simpa only [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] using h5

theorem Facts.of_elementary [Finite G] (D : Facts G t L E) {B : Subgroup G} (hBL : B ≤ L)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBn : Nat.card B = 2 ^ 11) : Facts G t L B := by
  obtain ⟨l, hl, rfl⟩ := D.conj_class B hBL hB2 hBn
  exact D.conjSubgroup_of_mem hl

end CFSG.EvenSporadicStandard.TwoFi22.DS81
