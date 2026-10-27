module

public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexAEng
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Three.late_cls (d : Std20Three K K' J S R R' W V z t) :
    Q3CL.ClassicalClause (CoreAssembly.conjClass K) :=
  Q3CL.classicalClause_of_modU d.hyp

private theorem Std20Three.late_toF (d : Std20Three K K' J S R R' W V z t) :
    Std20F K K' J S R R' W V z t :=
  { d with
    hyp := d.late_hΩ
    late_ne_inv := d.late_ne_inv
    late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.late_hΩ d.viol.star d.viol.hzJ
    late_card2 := fun hU hK hR =>
      Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ hU hK hR }

theorem Std20Three.late_isSylow2In_S (d : Std20Three K K' J S R R' W V z t) :
    IsSylow2In (S : Subgroup G) (Subgroup.centralizer ({z} : Set G)) := by
  exact d.late_toF.late_isSylow2In_S

theorem Std20Three.late_nbr (d : Std20Three K K' J S R R' W V z t) :
    ∀ L ∈ omegaNbr (CoreAssembly.conjClass K) K, L ∈ twinSet (CoreAssembly.conjClass K) K := by
  exact d.late_toF.late_nbr

section Pair

variable {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem exists_zpowers_eq_inf_WGen (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) {R : Subgroup G}
    (hR : R ∈ DSet Ω W) : ∃ u : G, Subgroup.zpowers u = R ⊓ W := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  have hcyc := (Q3CL.Thompson.inf_W_of_mem_D hΩ hW hR hK hRK).2.2.1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(R ⊓ W))
  refine ⟨g, le_antisymm (Subgroup.zpowers_le.mpr g.2) fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  exact ⟨k, congrArg Subtype.val hk⟩

theorem eq_closure_pairGen (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) {R : Subgroup G}
    (hR : R ∈ DSet Ω W) {u r : G} (hu : Subgroup.zpowers u = R ⊓ W) (hr : r ∈ R) (hrW : r ∉ W) :
    R = Subgroup.closure {u, r} := by
  have hu' : u ∈ R ⊓ W := hu ▸ Subgroup.mem_zpowers u
  apply le_antisymm
  · intro x hx
    by_cases hxW : x ∈ W
    · have : x ∈ Subgroup.zpowers u := hu ▸ ⟨hx, hxW⟩
      exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert u _))) this
    · have h1 : r⁻¹ * x ∈ Subgroup.zpowers u :=
        hu ▸ ⟨R.mul_mem (R.inv_mem hr) hx, Q3CL.Thompson.D_inv_mul_mem hΩ hW hR hr hx hrW hxW⟩
      have h2 : x = r * (r⁻¹ * x) := by group
      rw [h2]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton r)))
        ((Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert u _))) h1)
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hu'.1
    · exact hr

theorem late_exists_dDataGen (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) {R K : Subgroup G}
    (hR : R ∈ DSet Ω W) (hK : K ∈ Ω) (hRK : IsSylow2In R K) {z : G}
    (hz : IsUniqueInvolution K z) : ∃ u r : G, Sec71.DData Ω W R K u r z := by
  obtain ⟨u, hu⟩ := exists_zpowers_eq_inf_WGen hΩ hW hR
  obtain ⟨r, hrR, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hR
  have hRcl := eq_closure_pairGen hΩ hW hR hu hrR hrW
  obtain ⟨K₂, z₂, hd⟩ := exists_dDataGen hΩ hW hR hu hRcl
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR.1
  have hK₂ : K₂ = K := Sec6Gen.eq_of_le_of_le hΩ hd.memK hK hRK.2.1 (by omega) hd.le hRK.1
  subst hK₂
  have hz₂ : z₂ = z := hd.uinv.eq hz
  subst hz₂
  exact ⟨u, r, hd⟩

theorem late_pairGen (hΩ : HypOmegaGen Ω) (hcl : Q3CL.ClassicalClause Ω)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {R K T L : Subgroup G} {u r z v s a : G}
    (hd : Sec71.DData Ω W R K u r z) (hd' : Sec71.DData Ω W T L v s a) (hKL : K ≠ L)
    (hza : z ≠ a) (hnot : L ∉ omegaNbr Ω K) :
    ∃ i k : ℤ, Odd i ∧ Odd k ∧ r * v * r⁻¹ = v * u ^ i ∧ s * u * s⁻¹ = u * v ^ k ∧
      r * a * r⁻¹ = a * z ∧ s * z * s⁻¹ = z * a := by
  obtain ⟨i, hi⟩ := hd.exists_rel hd'.u_memW (hd.le_normalizer hd'.u_memW)
  obtain ⟨k, hk⟩ := hd'.exists_rel hd.u_memW (hd'.le_normalizer hd.u_memW)
  have hio : Odd i := by
    by_contra h
    have hie : Even i := Int.not_odd_iff_even.mp h
    have hke := even_of_evenGen hΩ hd hd' hWc hza hi hk hie
    exact hnot (case_two_of_evenGen hΩ hcl hd hd' hWc hKL hza hi hk hie hke).1
  have hko : Odd k := by
    by_contra h
    have hke : Even k := Int.not_odd_iff_even.mp h
    have hie := even_of_evenGen hΩ hd' hd hWc (Ne.symm hza) hk hi hke
    exact (Int.not_even_iff_odd.mpr hio) hie
  refine ⟨i, k, hio, hko, hi, hk, ?_, ?_⟩
  · have := Sec71.conj_pow_eq (hWc u hd.u_memW v hd'.u_memW) hi (orderOf u / 2)
    rwa [jEqGen hΩ hd hd', hd.z_eq, Sec71.zpow_eq_self_of_odd hd.uinv.sq hio] at this
  · rw [conj_z_eqGen hΩ hd hd' hWc hk, Sec71.zpow_eq_self_of_odd hd'.uinv.sq hko]

end Pair

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
