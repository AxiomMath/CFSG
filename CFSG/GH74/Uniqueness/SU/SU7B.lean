module

public import CFSG.GH74.Uniqueness.SU.SU7Claim

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG.Blueprint

namespace Claim

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}

theorem barS_inf_F (hKI3 : K.KI3) (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) :
    barImage M (S : Subgroup G) ⊓ generalizedFitting (Mbar M) = barImage M (Tsub S U) := by
  have hTle := hcl.T_le
  rcases hcl.case with ha | hb
  · obtain ⟨hLie, -, h9⟩ := ha
    have hJ := Base.j2facts hH hconf hcl
    have hxF := xbar_not_mem hKI3 hH hconf hLie h9
    have hxM := hconf.x_mem
    apply le_antisymm
    · rintro y ⟨hyS, hyF⟩
      obtain ⟨s, hsS, rfl⟩ := mem_barImage_iff.1 hyS
      rcases hJ.S_cover s hsS with hsT | hxsT
      · exact mem_barImage_iff.2 ⟨s, hsT, rfl⟩
      · exfalso
        apply hxF
        have hxsM : x * (s : G) ∈ M := M.mul_mem hxM s.2
        have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x * (s : G), hxsM⟩ ∈
            barImage M (Tsub S U) := mem_barImage_iff.2 ⟨⟨x * (s : G), hxsM⟩, hxsT, rfl⟩
        have h2 := hTle h1
        have e : xbar M x hxM = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x * (s : G), hxsM⟩ *
            (QuotientGroup.mk' (pPrimeCore 2 ↥M) s)⁻¹ := by
          rw [← map_inv, ← map_mul]
          unfold xbar
          congr 1
          exact Subtype.ext (by simp)
        rw [e]
        exact (generalizedFitting (Mbar M)).mul_mem h2
          ((generalizedFitting (Mbar M)).inv_mem hyF)
    · exact le_inf (barImage_mono Base.T_le_S) hTle
  · rw [← hb]
    exact inf_eq_right.2 (barImage_mono Base.T_le_S)

theorem conj_mem_T (hKI3 : K.KI3) (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) {n u : G} (hnM : n ∈ M) (huU : u ∈ U)
    (hy : n * u * n⁻¹ ∈ (S : Subgroup G)) : n * u * n⁻¹ ∈ Tsub S U := by
  have hTM : Tsub S U ≤ M := Base.T_le_S.trans hconf.S_le
  have huT : u ∈ Tsub S U := Base.U_le_T hH hconf hcl huU
  have huM : u ∈ M := hTM huT
  have hyM : n * u * n⁻¹ ∈ M := M.mul_mem (M.mul_mem hnM huM) (M.inv_mem hnM)
  have hbarF : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨n * u * n⁻¹, hyM⟩ ∈
      generalizedFitting (Mbar M) := by
    have hu1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨u, huM⟩ ∈ generalizedFitting (Mbar M) :=
      hcl.T_le (mem_barImage_iff.2 ⟨⟨u, huM⟩, huT, rfl⟩)
    have e : (⟨n * u * n⁻¹, hyM⟩ : ↥M) = ⟨n, hnM⟩ * ⟨u, huM⟩ * ⟨n, hnM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (Gen.normal_generalizedFitting _).conj_mem _ hu1 _
  have hbarS : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨n * u * n⁻¹, hyM⟩ ∈
      barImage M (S : Subgroup G) := mem_barImage_iff.2 ⟨⟨n * u * n⁻¹, hyM⟩, hy, rfl⟩
  have hbarT : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨n * u * n⁻¹, hyM⟩ ∈
      barImage M (Tsub S U) := by
    rw [← barS_inf_F hKI3 hH hconf hcl]
    exact ⟨hbarS, hbarF⟩
  obtain ⟨m, hmT, hm⟩ := mem_barImage_iff.1 hbarT
  have hmS : (m : G) ∈ (S : Subgroup G) := Base.T_le_S hmT
  have hmeq : (m : G) = n * u * n⁻¹ := Bar.eq_of_proj_eq S.isPGroup' hconf.S_le hmS hy hm
  rw [← hmeq]
  exact hmT

end Claim

end CFSG.GH74.Uniqueness.SU.SU7
