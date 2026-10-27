module

public import CFSG.Fischer.Aut.Complete

public section

namespace CFSG.Fischer

variable {H : Type*} [Group H]

@[expose] noncomputable def quotCenterAut (β : MulAut H) : MulAut (H ⧸ Subgroup.center H) :=
  QuotientGroup.congr _ _ β (Subgroup.map_center_eq β)

theorem quotCenterAut_mk (β : MulAut H) (x : H) :
    quotCenterAut β (QuotientGroup.mk x) = QuotientGroup.mk (β x) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem sq_eq_one_of_quot_trivial (hZ : Subgroup.center H ≤ commutator H)
    (hexp : ∀ z ∈ Subgroup.center H, z * z = 1) {β : MulAut H}
    (hβ : ∀ x : H, x⁻¹ * β x ∈ Subgroup.center H) : β ^ 2 = 1 := by
  let ζ : H →* Subgroup.center H :=
    { toFun := fun x => ⟨x⁻¹ * β x, hβ x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => by
        apply Subtype.ext
        show (x * y)⁻¹ * β (x * y) = x⁻¹ * β x * (y⁻¹ * β y)
        have hc := Subgroup.mem_center_iff.1 (hβ x) y⁻¹
        calc (x * y)⁻¹ * β (x * y) = y⁻¹ * (x⁻¹ * β x) * β y := by rw [map_mul]; group
          _ = x⁻¹ * β x * y⁻¹ * β y := by rw [hc]
          _ = x⁻¹ * β x * (y⁻¹ * β y) := by group }
  have hker : commutator H ≤ ζ.ker := Abelianization.commutator_subset_ker ζ
  have hfix : ∀ z ∈ Subgroup.center H, β z = z := by
    intro z hz
    have := MonoidHom.mem_ker.1 (hker (hZ hz))
    have h1 : z⁻¹ * β z = 1 := congrArg Subtype.val this
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  ext x
  rw [sq, MulAut.mul_apply, MulAut.one_apply]
  have hz := hfix _ (hβ x)
  have hx : β x = x * (x⁻¹ * β x) := by group
  calc β (β x) = β (x * (x⁻¹ * β x)) := by rw [← hx]
    _ = β x * β (x⁻¹ * β x) := map_mul _ _ _
    _ = β x * (x⁻¹ * β x) := by rw [hz]
    _ = x * ((x⁻¹ * β x) * (x⁻¹ * β x)) := by group
    _ = x := by rw [hexp _ (hβ x), mul_one]

theorem outTwo_of_complete_quotient
    (hQ : ∀ φ : MulAut (H ⧸ Subgroup.center H), ∃ q, φ = MulAut.conj q)
    (hZ : Subgroup.center H ≤ commutator H) (hexp : ∀ z ∈ Subgroup.center H, z * z = 1) :
    OutTwo H := by
  intro β
  obtain ⟨q, hq⟩ := hQ (quotCenterAut β)
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  set β' := MulAut.conj h⁻¹ * β with hβ'
  have key : ∀ z ∈ Subgroup.center H, h⁻¹ * z * h = z := fun z hz => by
    rw [Subgroup.mem_center_iff.1 hz h⁻¹]; group
  have hβ'Z : ∀ x : H, x⁻¹ * β' x ∈ Subgroup.center H := by
    intro x
    have e := congrArg (fun φ : MulAut _ => φ (QuotientGroup.mk x)) hq
    simp only [quotCenterAut_mk, MulAut.conj_apply] at e
    have e2 : (QuotientGroup.mk (h * x * h⁻¹) : H ⧸ Subgroup.center H) =
        QuotientGroup.mk (β x) := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact e.symm
    have e' := QuotientGroup.eq.1 e2
    have : x⁻¹ * β' x = h⁻¹ * ((h * x * h⁻¹)⁻¹ * β x) * h := by
      rw [hβ', MulAut.mul_apply, MulAut.conj_apply]
      group
    rw [this, key _ e']
    exact e'
  have hsq : β' ^ 2 = 1 := sq_eq_one_of_quot_trivial hZ hexp hβ'Z
  have hβ : β = MulAut.conj h * β' := by
    rw [hβ', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine ⟨1, h * β' h, ?_⟩
  calc β ^ (2 ^ 1) = MulAut.conj h * β' * (MulAut.conj h * β') := by rw [pow_one, sq, ← hβ]
    _ = MulAut.conj h * (β' * MulAut.conj h * β'⁻¹) * (β' * β') := by group
    _ = MulAut.conj h * MulAut.conj (β' h) * β' ^ 2 := by rw [mul_conj_mul_inv, ← sq]
    _ = MulAut.conj (h * β' h) := by rw [hsq, mul_one, ← map_mul]

end CFSG.Fischer
