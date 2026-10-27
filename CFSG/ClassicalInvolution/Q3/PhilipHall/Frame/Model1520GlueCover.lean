module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwinDefs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

theorem mem_center_of_commutators_central {K : Type*} [Group K] (hK : Group.IsPerfect K) {k : K}
    (h : ∀ y : K, k * y * k⁻¹ * y⁻¹ ∈ Subgroup.center K) : k ∈ Subgroup.center K := by
  let c : K →* Subgroup.center K :=
    { toFun := fun y => ⟨k * y * k⁻¹ * y⁻¹, h y⟩
      map_one' := by refine Subtype.ext ?_; simp
      map_mul' := fun y z => by
        refine Subtype.ext ?_
        have hc := Subgroup.mem_center_iff.mp (h z) (k * y * k⁻¹)
        simp only [Subgroup.coe_mul]
        calc k * (y * z) * k⁻¹ * (y * z)⁻¹
            = (k * y * k⁻¹) * (k * z * k⁻¹ * z⁻¹) * y⁻¹ := by group
          _ = (k * z * k⁻¹ * z⁻¹) * (k * y * k⁻¹) * y⁻¹ := by rw [hc]
          _ = k * y * k⁻¹ * y⁻¹ * (k * z * k⁻¹ * z⁻¹) := by
            have hc' := Subgroup.mem_center_iff.mp (h y) (k * z * k⁻¹ * z⁻¹)
            calc (k * z * k⁻¹ * z⁻¹) * (k * y * k⁻¹) * y⁻¹
                = ((k * z * k⁻¹ * z⁻¹) * (k * y * k⁻¹ * y⁻¹)) := by group
              _ = (k * y * k⁻¹ * y⁻¹) * (k * z * k⁻¹ * z⁻¹) := hc' }
  have hker : commutator K ≤ c.ker := Abelianization.commutator_subset_ker c
  have htop : commutator K = ⊤ := hK.commutator_eq_top
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : y ∈ c.ker := hker (htop ▸ Subgroup.mem_top y)
  have h2 : k * y * k⁻¹ * y⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp h1)
  calc y * k = (k * y * k⁻¹ * y⁻¹)⁻¹ * (k * y) := by group
    _ = k * y := by rw [h2]; simp

theorem exists_equiv_of_covers {K X P : Type*} [Group K] [Group X] [Group P]
    (hK : Group.IsPerfect K) (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hψker : ψ.ker ≤ Subgroup.center K) (π : K →* P) (hπ : Function.Surjective π)
    (hπker : π.ker = Subgroup.center K) :
    ∃ e : X ⧸ Subgroup.center X ≃* P, ∀ k, e (QuotientGroup.mk (ψ k)) = π k := by
  let q : K →* X ⧸ Subgroup.center X := (QuotientGroup.mk' (Subgroup.center X)).comp ψ
  have hq : Function.Surjective q := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, rfl⟩ := hψ x
    exact ⟨k, rfl⟩
  have hqker : q.ker = Subgroup.center K := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hk
      refine mem_center_of_commutators_central hK fun y => hψker ?_
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      have := Subgroup.mem_center_iff.mp hk (ψ y)
      calc ψ k * ψ y * (ψ k)⁻¹ * (ψ y)⁻¹ = (ψ y * ψ k) * (ψ k)⁻¹ * (ψ y)⁻¹ := by rw [this]
        _ = 1 := by group
    · intro hk
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨y, rfl⟩ := hψ x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hk y]
  let e₁ : K ⧸ q.ker ≃* X ⧸ Subgroup.center X := QuotientGroup.quotientKerEquivOfSurjective q hq
  let e₂ : K ⧸ q.ker ≃* K ⧸ π.ker := QuotientGroup.quotientMulEquivOfEq (hqker.trans hπker.symm)
  let e₃ : K ⧸ π.ker ≃* P := QuotientGroup.quotientKerEquivOfSurjective π hπ
  refine ⟨e₁.symm.trans (e₂.trans e₃), fun k => ?_⟩
  have h1 : (QuotientGroup.mk (ψ k) : X ⧸ Subgroup.center X) = e₁ (QuotientGroup.mk k) := rfl
  rw [h1]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
