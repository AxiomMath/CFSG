module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLateCfg
import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexAEng
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonInputs
public import CFSG.ClassicalInvolution.AschTight.Sec71Cases
public import CFSG.ClassicalInvolution.AschTight.Sec7L713I

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

private theorem Std20.late_toF (d : Std20 p f K K' J S R R' W V z t) :
    Std20F K K' J S R R' W V z t :=
  { d with
    hyp := d.late_hΩ
    late_ne_inv := d.late_ne_inv
    late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.branch.odd d.hyp d.viol.star d.viol.hzJ
    late_card2 := fun hU hK hR =>
      Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp hU hK hR }

theorem Std20.late_isSylow2In_S (d : Std20 p f K K' J S R R' W V z t) :
    IsSylow2In (S : Subgroup G) (Subgroup.centralizer ({z} : Set G)) := by
  exact d.late_toF.late_isSylow2In_S

theorem Std20.late_nbr (d : Std20 p f K K' J S R R' W V z t) :
    ∀ L ∈ omegaNbr (CoreAssembly.conjClass K) K, L ∈ twinSet (CoreAssembly.conjClass K) K := by
  exact d.late_toF.late_nbr

end Std

section Pair

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem late_exists_dData (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {R K : Subgroup G} (hR : R ∈ DSet Ω W) (hK : K ∈ Ω)
    (hRK : IsSylow2In R K) {z : G} (hz : IsUniqueInvolution K z) :
    ∃ u r : G, Sec71.DData Ω W R K u r z := by
  have h611 : Sec7.EtaMeets Ω := l6_11_proved p f hp hq G Ω hΩ
  obtain ⟨u, hu⟩ := Thompson.exists_zpowers_eq_inf_W hp hq hΩ hW hR
  obtain ⟨r, hrR, hrW⟩ := Sec7.exists_not_mem_W hp hΩ h611 hW hR hK hRK.1
  have hRcl := Thompson.eq_closure_pair hp hq hΩ hW hR hu hrR hrW
  obtain ⟨K₂, z₂, hd⟩ := Sec71.exists_dData hp hq hΩ hW hR hu hRcl
  have hΩg := hypOmegaGen_of_mod hp hq hΩ
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩg hR.1
  have hK₂ : K₂ = K := Sec6Gen.eq_of_le_of_le hΩg hd.memK hK hRK.2.1 (by omega) hd.le hRK.1
  subst hK₂
  have hz₂ : z₂ = z := hd.uinv.eq hz
  subst hz₂
  exact ⟨u, r, hd⟩

theorem late_pair (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
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
    have hke := Sec71.even_of_even hp hq hΩ hd hd' hWc hza hi hk hie
    exact hnot (Sec71.case_two_of_even hp hq hΩ hd hd' hWc hKL hza hi hk hie hke).1
  have hko : Odd k := by
    by_contra h
    have hke : Even k := Int.not_odd_iff_even.mp h
    have hie := Sec71.even_of_even hp hq hΩ hd' hd hWc (Ne.symm hza) hk hi hke
    exact (Int.not_even_iff_odd.mpr hio) hie
  refine ⟨i, k, hio, hko, hi, hk, ?_, ?_⟩
  · have := Sec71.conj_pow_eq (hWc u hd.u_memW v hd'.u_memW) hi (orderOf u / 2)
    rwa [hd.j_eq hΩ hd', hd.z_eq, Sec71.zpow_eq_self_of_odd hd.uinv.sq hio] at this
  · rw [Sec71.conj_z_eq hΩ hd hd' hWc hk, Sec71.zpow_eq_self_of_odd hd'.uinv.sq hko]

end Pair

end CFSG.ClassicalInvolution.Asc77.T3CII
