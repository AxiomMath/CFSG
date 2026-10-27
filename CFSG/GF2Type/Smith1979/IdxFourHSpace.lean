module

public import CFSG.LargeExtraspecial.S4Span

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def fixO (t : S.O) : Submodule (ZMod 2) S.Qt :=
  fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)

@[expose] noncomputable def commO (t : S.O) : Submodule (ZMod 2) S.Qt :=
  commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)

variable {S}

theorem mem_fixO {t : S.O} {v : S.Qt} : v ∈ fixO S t ↔ (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  mem_fixSpace

theorem mem_commO {t : S.O} {w : S.Qt} :
    w ∈ commO S t ↔ ∃ v, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v = w :=
  mem_commSpace

theorem coe_mul_apply_O (x y : S.O) (v : S.Qt) :
    ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := rfl

theorem coe_mul_self_O {t : S.O} (htt : t * t = 1) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 :=
  congrArg Subtype.val htt

theorem commO_le_fixO {t : S.O} (htt : t * t = 1) : commO S t ≤ fixO S t :=
  commSpace_le_fixSpace (coe_mul_self_O htt)

theorem fixO_eq_orthogonal {t : S.O} (htt : t * t = 1) :
    fixO S t = LinearMap.BilinForm.orthogonal S.q.polarBilin (commO S t) :=
  fixSpace_eq_orthogonal_commSpace S.q_nondegenerate t.2 (coe_mul_self_O htt)

theorem finrank_commO_add_fixO (t : S.O) :
    finrank (ZMod 2) (commO S t) + finrank (ZMod 2) (fixO S t) = finrank (ZMod 2) S.Qt :=
  finrank_commSpace_add_finrank_fixSpace _

theorem apply_mem_commO {t θ : S.O} (h : θ * t = t * θ) {w : S.Qt} (hw : w ∈ commO S t) :
    (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ commO S t := by
  obtain ⟨v, rfl⟩ := mem_commO.mp hw
  refine mem_commO.mpr ⟨(θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v, ?_⟩
  have := congrArg (fun x : S.O => (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) h
  simp only [coe_mul_apply_O] at this
  rw [map_sub, ← this]

theorem finrank_fixO_conj (m t : S.O) :
    finrank (ZMod 2) (fixO S (m * t * m⁻¹)) = finrank (ZMod 2) (fixO S t) := by
  have h : fixO S (m * t * m⁻¹) = (fixO S t).map (m : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    ext v
    rw [mem_fixO, Submodule.mem_map]
    constructor
    · intro hv
      refine ⟨((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, ?_, ?_⟩
      · rw [mem_fixO]
        have := congrArg (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) hv
        simp only [coe_mul_apply_O] at this
        have h1 : ((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt)
              (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v))) =
            (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
          have := CFSG.LargeExtraspecial.S4.inv_apply_apply_O m
            ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v))
          exact this
        rw [h1] at this
        exact this
      · exact CFSG.LargeExtraspecial.S4.apply_inv_apply_O m v
    · rintro ⟨u, hu, rfl⟩
      rw [mem_fixO] at hu
      simp only [coe_mul_apply_O, LinearEquiv.coe_coe]
      rw [CFSG.LargeExtraspecial.S4.inv_apply_apply_O, hu]
  rw [h]
  exact LinearEquiv.finrank_map_eq (m : S.Qt ≃ₗ[ZMod 2] S.Qt) _

end CFSG.GF2Type.Smith1979.IdxFour
