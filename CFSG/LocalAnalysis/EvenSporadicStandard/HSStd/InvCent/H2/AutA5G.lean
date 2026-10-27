module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.AutA5

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup

variable {G : Type*} [Group G]

theorem exists_inner_of_normalizes {S : Subgroup G} (φ : ↥S ≃* alternatingGroup (Fin 5)) {a b : G}
    (ha : a ∈ S) (hb : b ∈ S) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (ha2 : a * a = 1)
    (hb2 : b * b = 1) (hcomm : a * b = b * a) {c : G} (hc : c ∈ normalizer (S : Set G))
    (hca : c * a = a * c) (hcb : c * b = b * c) :
    ∃ x : G, (x = 1 ∨ x = a ∨ x = b ∨ x = a * b) ∧ ∀ s ∈ S, c * s * c⁻¹ = x * s * x⁻¹ := by
  have ha'1 : φ ⟨a, ha⟩ ≠ 1 := by
    intro h
    refine ha1 ?_
    have h1 : (⟨a, ha⟩ : ↥S) = 1 := φ.injective (by rw [h, map_one])
    simpa using congrArg Subtype.val h1
  have hb'1 : φ ⟨b, hb⟩ ≠ 1 := by
    intro h
    refine hb1 ?_
    have h1 : (⟨b, hb⟩ : ↥S) = 1 := φ.injective (by rw [h, map_one])
    simpa using congrArg Subtype.val h1
  have hab' : φ ⟨a, ha⟩ ≠ φ ⟨b, hb⟩ := fun h =>
    hab (by simpa using congrArg Subtype.val (φ.injective h))
  have ha'2 : φ ⟨a, ha⟩ * φ ⟨a, ha⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨a, ha⟩ : ↥S) * ⟨a, ha⟩ = 1 := Subtype.ext (by simpa using ha2)
    rw [h1, map_one]
  have hb'2 : φ ⟨b, hb⟩ * φ ⟨b, hb⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨b, hb⟩ : ↥S) * ⟨b, hb⟩ = 1 := Subtype.ext (by simpa using hb2)
    rw [h1, map_one]
  have hcomm' : φ ⟨a, ha⟩ * φ ⟨b, hb⟩ = φ ⟨b, hb⟩ * φ ⟨a, ha⟩ := by
    have hsub : (⟨a, ha⟩ : ↥S) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      ext
      simpa using hcomm
    rw [← map_mul, ← map_mul, hsub]
  let κ : MulAut ↥S :=
    { toFun := fun s => ⟨c * (s : G) * c⁻¹, (hc (s : G)).mp s.2⟩
      invFun := fun s => ⟨c⁻¹ * (s : G) * c,
        ((Subgroup.mem_set_normalizer_iff''.mp hc) (s : G)).mp s.2⟩
      left_inv := fun s => by ext; simp only [Subgroup.coe_mk]; group
      right_inv := fun s => by ext; simp only [Subgroup.coe_mk]; group
      map_mul' := fun s t => by
        ext; simp only [Subgroup.coe_mk, Subgroup.coe_mul]; group }
  let σ : MulAut (alternatingGroup (Fin 5)) := (φ.symm.trans κ).trans φ
  have hκa : κ ⟨a, ha⟩ = ⟨a, ha⟩ := by
    apply Subtype.ext
    show c * a * c⁻¹ = a
    rw [hca, mul_assoc, mul_inv_cancel, mul_one]
  have hκb : κ ⟨b, hb⟩ = ⟨b, hb⟩ := by
    apply Subtype.ext
    show c * b * c⁻¹ = b
    rw [hcb, mul_assoc, mul_inv_cancel, mul_one]
  have hσa : σ (φ ⟨a, ha⟩) = φ ⟨a, ha⟩ := by
    show φ (κ (φ.symm (φ ⟨a, ha⟩))) = φ ⟨a, ha⟩
    rw [MulEquiv.symm_apply_apply, hκa]
  have hσb : σ (φ ⟨b, hb⟩) = φ ⟨b, hb⟩ := by
    show φ (κ (φ.symm (φ ⟨b, hb⟩))) = φ ⟨b, hb⟩
    rw [MulEquiv.symm_apply_apply, hκb]
  obtain ⟨x', hx'mem, hx'act⟩ :=
    aut_alt5_of_fixes ha'1 hb'1 hab' ha'2 hb'2 hcomm' σ hσa hσb
  refine ⟨(φ.symm x' : ↥S), ?_, ?_⟩
  · rcases hx'mem with h | h | h | h
    · left; rw [h, map_one]; rfl
    · right; left; rw [h, MulEquiv.symm_apply_apply]
    · right; right; left; rw [h, MulEquiv.symm_apply_apply]
    · right; right; right
      rw [h, map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      rfl
  · intro s hs
    have hEq : φ (⟨c * s * c⁻¹, (hc s).mp hs⟩ : ↥S) = x' * φ ⟨s, hs⟩ * x'⁻¹ := by
      have h := hx'act (φ ⟨s, hs⟩)
      change φ (κ (φ.symm (φ ⟨s, hs⟩))) = x' * φ ⟨s, hs⟩ * x'⁻¹ at h
      rw [MulEquiv.symm_apply_apply] at h
      exact h
    have hsub : (⟨c * s * c⁻¹, (hc s).mp hs⟩ : ↥S) =
        φ.symm (x' * φ ⟨s, hs⟩ * x'⁻¹) := by
      refine φ.injective ?_
      rw [MulEquiv.apply_symm_apply]
      exact hEq
    have hfinal : (↑(φ.symm (x' * φ ⟨s, hs⟩ * x'⁻¹)) : G) =
        (↑(φ.symm x') : G) * s * (↑(φ.symm x') : G)⁻¹ := by
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (congrArg Subtype.val hsub).trans hfinal

theorem exists_conj_of_involutions {S : Subgroup G} (φ : ↥S ≃* alternatingGroup (Fin 5)) {x y : G}
    (hx : x ∈ S) (hy : y ∈ S) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hx2 : x * x = 1) (hy2 : y * y = 1) :
    ∃ s ∈ S, s * x * s⁻¹ = y := by
  have hx'1 : φ ⟨x, hx⟩ ≠ 1 := by
    intro h
    refine hx1 ?_
    have h1 : (⟨x, hx⟩ : ↥S) = 1 := φ.injective (by rw [h, map_one])
    simpa using congrArg Subtype.val h1
  have hy'1 : φ ⟨y, hy⟩ ≠ 1 := by
    intro h
    refine hy1 ?_
    have h1 : (⟨y, hy⟩ : ↥S) = 1 := φ.injective (by rw [h, map_one])
    simpa using congrArg Subtype.val h1
  have hx'2 : φ ⟨x, hx⟩ * φ ⟨x, hx⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨x, hx⟩ : ↥S) * ⟨x, hx⟩ = 1 := Subtype.ext (by simpa using hx2)
    rw [h1, map_one]
  have hy'2 : φ ⟨y, hy⟩ * φ ⟨y, hy⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨y, hy⟩ : ↥S) * ⟨y, hy⟩ = 1 := Subtype.ext (by simpa using hy2)
    rw [h1, map_one]
  obtain ⟨s', hs'⟩ := alt5_involutions_conj hx'1 hy'1 hx'2 hy'2
  refine ⟨(φ.symm s' : ↥S), (φ.symm s').2, ?_⟩
  have hval : ((φ.symm s' : ↥S) * ⟨x, hx⟩ * (φ.symm s')⁻¹ : ↥S) = ⟨y, hy⟩ := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hs'
  simpa using congrArg Subtype.val hval

theorem card_of_equiv_alt5 {S : Subgroup G} (φ : ↥S ≃* alternatingGroup (Fin 5)) :
    Nat.card ↥S = 60 := by
  rw [← card_alt5]
  exact Nat.card_congr φ.toEquiv

end CFSG.EvenSporadicStandard.HSStd.InvCent
