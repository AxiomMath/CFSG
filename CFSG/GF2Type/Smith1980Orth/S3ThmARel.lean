module

public import CFSG.GF2Type.Smith1980Orth.S3ThmAW4
public import CFSG.GF2Type.Smith1980Orth.ConjBad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Pre

theorem exists_mul_bad_mem_M1 {M1 : Subgroup S.O} (D : S2Pre S M1) {k : G} (hbad : Bad S k) :
    ∃ m : S.M, ∃ hb : Bad S ((m : G) * k), S.ρ ⟨_, hb.mem_M⟩ ∈ M1 := by
  have hxM := hbad.mem_M
  have hx2 : (k * S.z * k⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hxx : S.ρ ⟨k * S.z * k⁻¹, hxM⟩ * S.ρ ⟨k * S.z * k⁻¹, hxM⟩ = 1 :=
    Subtype.ext (S.ρ_mul_self hxM hx2)
  obtain ⟨y, hy, hconj⟩ :=
    D.rel.inv_conj (S.ρ ⟨k * S.z * k⁻¹, hxM⟩) (MonoidHom.mem_range.mpr ⟨_, rfl⟩) hxx
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hy
  refine ⟨m, hbad.mul_left m.2, ?_⟩
  have e : (⟨(m : G) * k * S.z * ((m : G) * k)⁻¹, (hbad.mul_left m.2).mem_M⟩ : S.M) =
      m * ⟨k * S.z * k⁻¹, hxM⟩ * m⁻¹ := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group)
  rw [e, map_mul, map_mul, map_inv]
  exact hconj

end S2Pre

namespace S2Data

theorem oKComm {M1 : Subgroup S.O} (D : S2Data S M1) : OKComm S := by
  intro k hbad
  obtain ⟨m, hb, hx1⟩ := S2Pre.exists_mul_bad_mem_M1 D.toS2Pre hbad
  have hxC : S.ρ ⟨_, hb.mem_M⟩ ∈ D.Cbar := by
    by_contra h
    exact D.not_bad_of_not_mem_Cbar_of_mem_M1 hb.mem_M hx1 h hb
  exact lbar_comm_of_mul_left m.2 (D.lbar_comm_of_bad hb hxC)

theorem not_bad_of_width_eq_four {M1 : Subgroup S.O} (D : S2Data S M1)
    (hw : S.width = 4) (k : G) : ¬ Bad S k := by
  intro hbad
  obtain ⟨m, hb, hx1⟩ := S2Pre.exists_mul_bad_mem_M1 D.toS2Pre hbad
  exact D.false_of_badData_four
    (D.half_of_bad_of_comm hb hx1 (commute_of_bad_of_oKComm D.oKComm hb)) hw

theorem oe34a_of_width_eq_four {M1 : Subgroup S.O} (D : S2Data S M1)
    (hw : S.width = 4) : OE34a S :=
  D.oe34a_of_forall_not_bad (D.not_bad_of_width_eq_four hw)

theorem oDelta_of_width_eq_four {M1 : Subgroup S.O} (D : S2Data S M1)
    (hw : S.width = 4) : ODelta S := by
  intro k hxM hxQ hbot
  obtain ⟨a, ha, haΔ⟩ := exists_of_not_bad (D.not_bad_of_width_eq_four hw k) hxM hxQ
  rw [hbot, Subgroup.mem_bot] at haΔ
  subst haΔ
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  apply S.z_ne_one
  calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
    _ = 1 := by rw [hg]; group

end S2Data

end CFSG.GF2Type.Smith1980Orth

