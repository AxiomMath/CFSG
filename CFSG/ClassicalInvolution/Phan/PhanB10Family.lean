module

public import CFSG.ClassicalInvolution.Phan.PhanB9Glue

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort SymplecticPhanPair)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}
  (C : B2Coord hK F h2) {G : Type} [Group G]

theorem exists_mulAut_extend_zero (hK : Nat.card K = (p ^ f) ^ 2) (α : MulAut (Su K p f 2))
    (hα : (torusTwo (unitaryInvolution K p f)).range.map α.toMonoidHom ≤
      (torusTwo (unitaryInvolution K p f)).range) :
    ∃ β : MulAut (Su K p f 3),
      (∀ A, β (embSUid (unitaryInvolution K p f) 0 A) =
        embSUid (unitaryInvolution K p f) 0 (α A)) ∧
      (B12 K p f).map β.toMonoidHom = B12 K p f ∧ (B23 K p f).map β.toMonoidHom = B23 K p f := by
  obtain ⟨a, b, φ, rfl⟩ := exists_diagConj_fieldAut hK α hα
  have hdc : diagConj p f hK ![a * b⁻¹, 1] = diagConj p f hK ![a, b] := by
    refine MulEquiv.ext fun A => ?_
    show conjDiag hK ![a * b⁻¹, 1] A = conjDiag hK ![a, b] A
    rw [conjDiag_two hK a b]
  refine ⟨pairExt hK 1 (a * b⁻¹) φ, fun A => ?_,
    map_range_eq_of_comp _ _ _ (pairExt_embSUid_two hK 1 (a * b⁻¹) φ),
    map_range_eq_of_comp _ _ _ (pairExt_embSUid_zero hK 1 (a * b⁻¹) φ)⟩
  rw [pairExt_embSUid_zero, hdc]

theorem exists_familyB3 (hq : 5 ≤ p ^ f) (hmod : p ^ f % 4 = 3) {U : Fin 3 → Subgroup G}
    (hcomm : Commutes (U 0) (U 2))
    (h01 : ∃ W, UnitaryBlockStandardPair K p f W (U 0) (U 1))
    (h12 : ∃ W, SymplecticPhanPair F h2 W (U 1) (U 2)) :
    ∃ E : PhanFamilyB3 C G, ∀ i, (E.ι i).range = U i := by
  obtain ⟨W₁, h01⟩ := h01
  obtain ⟨θ₀, -, hker0, hU0, hU1⟩ := pair_normalize h01
  obtain ⟨-, hr0, hj, hr1⟩ := pair_block_inj hK hker0 hU0 hU1
  obtain ⟨W₂, h12⟩ := h12
  obtain ⟨θ, c, -, hkerθ, hinjL, hLU, hSV⟩ := h12
  set ϑ : StatedSp 2 F →* G := θ.comp (MulAut.conj c⁻¹).toMonoidHom with hϑ
  have hLϑ : (longBlock F 2 1).range.map ϑ = U 1 := by
    rw [hϑ, map_comp_mulEquiv]; exact hLU
  have hSϑ : (twShort h2).range.map ϑ = U 2 := by
    rw [hϑ, map_comp_mulEquiv]; exact hSV
  have hkinj : Function.Injective (ϑ.comp C.ℓ) := by
    intro x y hxy
    have hx : C.ℓ x ∈ (longBlock F 2 1).range := C.ℓ_range ▸ ⟨x, rfl⟩
    have hy : C.ℓ y ∈ (longBlock F 2 1).range := C.ℓ_range ▸ ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have hab : a = b := by
      apply hinjL
      show ϑ (longBlock F 2 1 a) = ϑ (longBlock F 2 1 b)
      rw [ha, hb]
      exact hxy
    exact C.ℓ_inj (by rw [← ha, ← hb, hab])
  have hkrange : (ϑ.comp C.ℓ).range = U 1 := by
    rw [MonoidHom.range_comp, C.ℓ_range, ← hLϑ]
  obtain ⟨α, hα⟩ := exists_mulEquiv_comp_eq hkinj hj (by rw [hkrange, hr1])
  have hαϑ : ∀ g, θ₀ (embSUid (unitaryInvolution K p f) 0 (α g)) = ϑ (C.ℓ g) := fun g => hα g
  have hsrange : C.s.range.map ϑ = U 2 := by rw [C.s_range]; exact hSϑ
  have hq7 : 7 ≤ p ^ f := by omega
  have hcomm' : ∀ x ∈ (B12 K p f).map θ₀, ∀ y ∈ C.s.range.map ϑ, x * y = y * x := by
    rw [hU0, hsrange]
    exact hcomm
  have htor := alpha_torus_le C hq7 hker0 hcomm' α hαϑ
  obtain ⟨β, hβ0, hβ12, hβ23⟩ := exists_mulAut_extend_zero hK α htor
  set θ₁ : Su K p f 3 →* G := θ₀.comp β.toMonoidHom with hθ₁
  have hℓ : ϑ.comp C.ℓ = θ₁.comp (embSUid (unitaryInvolution K p f) 0) := by
    refine MonoidHom.ext fun g => ?_
    show ϑ (C.ℓ g) = θ₀ (β (embSUid (unitaryInvolution K p f) 0 g))
    rw [hβ0, hαϑ]
  have hr0' : (θ₁.comp (embSUid (unitaryInvolution K p f) 2)).range = U 0 := by
    rw [MonoidHom.range_comp]
    show (B12 K p f).map θ₁ = U 0
    rw [hθ₁, map_comp_mulEquiv, hβ12, hU0]
  have hr2' : (ϑ.comp C.s).range = U 2 := by
    rw [MonoidHom.range_comp]
    exact hsrange
  have hr1' : (θ₁.comp (embSUid (unitaryInvolution K p f) 0)).range = U 1 := by
    rw [← hℓ]
    exact hkrange
  refine ⟨⟨![θ₁.comp (embSUid (unitaryInvolution K p f) 2),
      θ₁.comp (embSUid (unitaryInvolution K p f) 0), ϑ.comp C.s], θ₁, ϑ, rfl, rfl, hℓ, rfl,
    fun a b => ?_⟩, fun i => ?_⟩
  · have ha : (θ₁.comp (embSUid (unitaryInvolution K p f) 2)) a ∈ U 0 := by
      rw [← hr0']
      exact ⟨a, rfl⟩
    have hb : (ϑ.comp C.s) b ∈ U 2 := by
      rw [← hr2']
      exact ⟨b, rfl⟩
    exact hcomm _ ha _ hb
  · fin_cases i
    · exact hr0'
    · exact hr1'
    · exact hr2'

end CFSG.ClassicalInvolution.PhanB3
