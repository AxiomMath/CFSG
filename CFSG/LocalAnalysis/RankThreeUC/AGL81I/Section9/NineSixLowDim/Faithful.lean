module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem le_centralizer_of_normalizerQuotCenterHom_eq_one {X : Type*} [Group X]
    {C : Subgroup X} (hC : Group.IsPerfect ↥C) {g : ↥(Subgroup.normalizer (C : Set X))}
    (hg : normalizerQuotCenterHom C g = 1) :
    C ≤ Subgroup.centralizer ({(g : X)} : Set X) := by
  set a := C.normalizerMonoidHom g
  have hz : ∀ c : ↥C, c⁻¹ * a c ∈ Subgroup.center ↥C := fun c => by
    have h := congrArg (fun φ : MulAut (↥C ⧸ Subgroup.center ↥C) => φ (QuotientGroup.mk' _ c)) hg
    simp only [normalizerQuotCenterHom, MonoidHom.comp_apply,
      FiveTransitive.CharacteristicAutomorphism.quotient_apply_mk, MulAut.one_apply] at h
    exact QuotientGroup.eq.mp h.symm
  let f : ↥C →* ↥(Subgroup.center ↥C) :=
    { toFun := fun c => ⟨c⁻¹ * a c, hz c⟩
      map_one' := by ext; simp
      map_mul' := fun c d => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (hz c) d⁻¹
        change (c * d)⁻¹ * a (c * d) = c⁻¹ * a c * (d⁻¹ * a d)
        rw [mul_inv_rev, map_mul]
        calc d⁻¹ * c⁻¹ * (a c * a d) = d⁻¹ * (c⁻¹ * a c) * a d := by group
          _ = c⁻¹ * a c * (d⁻¹ * a d) := by rw [hc]; group }
  intro c hc
  have hker : f ⟨c, hc⟩ = 1 :=
    Abelianization.commutator_subset_ker f (by rw [hC.commutator_eq_top]; trivial)
  have h1 : a ⟨c, hc⟩ = ⟨c, hc⟩ := by
    exact (inv_mul_eq_one.mp (congrArg Subtype.val hker)).symm
  have h2 : (g : X) * c * (g : X)⁻¹ = c := congrArg Subtype.val h1
  rw [Subgroup.mem_centralizer_iff]
  rintro y rfl
  exact mul_inv_eq_iff_eq_mul.mp h2

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
