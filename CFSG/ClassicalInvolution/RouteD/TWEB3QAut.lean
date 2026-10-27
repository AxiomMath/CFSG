module

public import CFSG.ClassicalInvolution.RouteD.TWEB3PLift

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

section Aut

variable {S X : Type} [Group S] [Group X]

theorem exists_rangeAut_of_sq (ψ : S →* X) (σ σd : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y)
    (hσdd : ∀ y, σd (σd y) = σ y) (hσr : ∀ k, σ (ψ k) ∈ ψ.range)
    (hσdr : ∀ k, σd (ψ k) ∈ ψ.range) :
    ∃ σR : ↥ψ.range ≃* ↥ψ.range, ∀ r : ↥ψ.range, ((σR r : ↥ψ.range) : X) = σd r := by
  have hrd : ∀ r ∈ ψ.range, σd r ∈ ψ.range := by
    rintro _ ⟨k, rfl⟩
    exact hσdr k
  have hsymm : ∀ r, σd.symm r = σd (σ r) := fun r =>
    σd.injective (by rw [σd.apply_symm_apply, hσdd, hσ2])
  have hrd' : ∀ r ∈ ψ.range, σd.symm r ∈ ψ.range := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := hσr k
    rw [hsymm, ← hk']
    exact hσdr k'
  exact ⟨{ toFun := fun r => ⟨σd r, hrd r r.2⟩
           invFun := fun r => ⟨σd.symm r, hrd' r r.2⟩
           left_inv := fun r => Subtype.ext (σd.symm_apply_apply r)
           right_inv := fun r => Subtype.ext (σd.apply_symm_apply r)
           map_mul' := fun a b => Subtype.ext (map_mul σd (a : X) (b : X)) }, fun r => rfl⟩

theorem conj_comm_of_fix (ψ : S →* X) (σR : ↥ψ.range ≃* ↥ψ.range) (T : Subgroup S)
    (hfix : ∀ t ∈ T, σR (ψ.rangeRestrict t) = ψ.rangeRestrict t) :
    ∀ s ∈ T ⊔ Subgroup.center S, ∀ ℓ : ↥ψ.range,
      σR (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σR ℓ * (ψ.rangeRestrict s)⁻¹ := by
  have hcentral : ∀ z ∈ Subgroup.center S,
      ∀ ℓ : ↥ψ.range, ψ.rangeRestrict z * ℓ = ℓ * ψ.rangeRestrict z := by
    intro z hz ℓ
    obtain ⟨y, rfl⟩ := MonoidHom.rangeRestrict_surjective ψ ℓ
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  let P : Subgroup S :=
    { carrier := {s | ∀ ℓ : ↥ψ.range, σR (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σR ℓ * (ψ.rangeRestrict s)⁻¹}
      mul_mem' := by
        intro a b ha hb ℓ
        have e : ψ.rangeRestrict (a * b) * ℓ * (ψ.rangeRestrict (a * b))⁻¹ =
            ψ.rangeRestrict a * (ψ.rangeRestrict b * ℓ * (ψ.rangeRestrict b)⁻¹) *
              (ψ.rangeRestrict a)⁻¹ := by
          rw [map_mul]
          group
        rw [e, ha, hb, map_mul]
        group
      one_mem' := by
        intro ℓ
        simp
      inv_mem' := by
        intro a ha ℓ
        have h1 := ha ((ψ.rangeRestrict a)⁻¹ * ℓ * ψ.rangeRestrict a)
        rw [show ψ.rangeRestrict a * ((ψ.rangeRestrict a)⁻¹ * ℓ * ψ.rangeRestrict a) *
          (ψ.rangeRestrict a)⁻¹ = ℓ by group] at h1
        rw [map_inv, inv_inv]
        have h2' : σR ((ψ.rangeRestrict a)⁻¹ * ℓ * ψ.rangeRestrict a) =
            (ψ.rangeRestrict a)⁻¹ * σR ℓ * ψ.rangeRestrict a := by
          rw [h1]
          group
        exact h2' }
  have hTP : T ≤ P := fun r hr ℓ => by
    rw [map_mul, map_mul, map_inv, hfix r hr]
  have hZP : Subgroup.center S ≤ P := fun z hz ℓ => by
    have hc := hcentral z hz
    have e : ψ.rangeRestrict z * ℓ * (ψ.rangeRestrict z)⁻¹ = ℓ := by
      rw [hc ℓ]
      group
    have e' : ψ.rangeRestrict z * σR ℓ * (ψ.rangeRestrict z)⁻¹ = σR ℓ := by
      rw [hc (σR ℓ)]
      group
    rw [e, e']
  exact fun s hs => (sup_le hTP hZP) hs

end Aut

end CFSG.ClassicalInvolution.RouteD.TWE.B3
