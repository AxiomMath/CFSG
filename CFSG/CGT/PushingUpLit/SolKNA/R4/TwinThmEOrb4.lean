module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOrb1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf23Orb4Data

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

namespace ThmE

section Orb4Pair

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem goodFourD_pair' (hΩ : HypOmegaGen Ω) (S : Sylow 2 G) {W H : Subgroup G}
    (hWn : ∀ s ∈ (S : Subgroup G), conjSub s W = W) (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    {Ka Kb Ra Rb : Subgroup G} {z t u u' : G} (hKa : Ka ∈ Ω)
    (hKb : Kb ∈ Ω) (hKab : Ka ≠ Kb) (hza : IsUniqueInvolution Ka z) (hzb : IsUniqueInvolution Kb z)
    (hRa : Ra ∈ RSet Ω) (hRb : Rb ∈ RSet Ω) (hRaK : Ra ≤ Ka) (hRbK : Rb ≤ Kb)
    (hRaS : Ra ≤ (S : Subgroup G)) (hRbS : Rb ≤ (S : Subgroup G)) (htz : t * z = z * t)
    (hua : u ∈ Ra) (hu4 : orderOf u = 4) (huW : u ∈ W) (hub : u' ∈ Rb) (hu'4 : orderOf u' = 4)
    (hu'W : u' ∈ W) (htd : (u * u') * t = t * (u * u'))
    (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ Ra ⊔ Rb, a ∈ W → a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H) :
    TwinThmEW.GoodFourWD (S : Subgroup G) H W t := by
  have hu2 : u * u = z := sq_eq_of_orderOf_four hza (hRaK hua) hu4
  have hu'2 : u' * u' = z := sq_eq_of_orderOf_four hzb (hRbK hub) hu'4
  have hRne : Ra ≠ Rb := orb4_rset_ne_of_ne hΩ hKa hKb hKab hRa hRaK hRbK
  have hcomm : Commutes Ra Rb := TwinThmEW.orb4_rset_commutes hΩ S hRa hRb hRaS hRbS hRne
  have huu' : u * u' = u' * u := hcomm u hua u' hub
  have huR' : u ∈ Ra ⊔ Rb := Subgroup.mem_sup_left hua
  have hu'R' : u' ∈ Ra ⊔ Rb := Subgroup.mem_sup_right hub
  have hzu : z * u = u * z := hza.commute_of_mem (hRaK hua)
  have hzu' : z * u' = u' * z := hzb.commute_of_mem (hRbK hub)
  have hno : ∀ x ∈ Ka, x ∈ Kb → orderOf x = 4 → False := by
    intro x hxK hxK' hx4
    have h := hΩ.card_le_two_of_le_inf hKa hKb hKab (isPGroup_zpowers_of_orderOf_four hx4)
      (Subgroup.zpowers_le.mpr hxK) (Subgroup.zpowers_le.mpr hxK')
    rw [Nat.card_zpowers, hx4] at h
    omega
  obtain ⟨d, hd⟩ : ∃ d, d = u * u' := ⟨_, rfl⟩
  have hdd : d * d = 1 := by
    calc d * d = u * (u' * u) * u' := by rw [hd]; group
      _ = u * (u * u') * u' := by rw [huu']
      _ = (u * u) * (u' * u') := by group
      _ = 1 := by rw [hu2, hu'2, hza.sq]
  have hd1 : d ≠ 1 := by
    intro h
    have h1 : u' = u⁻¹ := by
      have : u * u' = 1 := hd ▸ h
      exact (inv_eq_of_mul_eq_one_right this).symm
    have hu_K' : u ∈ Kb := by
      have := Kb.inv_mem (hRbK hub)
      rwa [h1, inv_inv] at this
    exact hno u (hRaK hua) hu_K' hu4
  have hdR : d ∈ Ra ⊔ Rb := hd ▸ (Ra ⊔ Rb).mul_mem huR' hu'R'
  have hzR : z ∈ Ra ⊔ Rb := hu2 ▸ (Ra ⊔ Rb).mul_mem huR' huR'
  have hzd : z * d = d * z := by
    calc z * d = (z * u) * u' := by rw [hd]; group
      _ = u * z * u' := by rw [hzu]
      _ = u * (z * u') := by group
      _ = u * (u' * z) := by rw [hzu']
      _ = d * z := by rw [hd]; group
  have htd' : d * t = t * d := hd ▸ htd
  have hzdne : z * d ≠ 1 := by
    intro h
    have h1 : u' = u⁻¹ * z := by
      have h2' : u * u' = z⁻¹ := by
        have : z * (u * u') = 1 := by rw [← hd]; exact h
        exact eq_inv_of_mul_eq_one_right this
      rw [inv_eq_of_mul_eq_one_right hza.sq] at h2'
      calc u' = u⁻¹ * (u * u') := by group
        _ = u⁻¹ * z := by rw [h2']
    have hu'K0 : u' ∈ Ka := by rw [h1]; exact Ka.mul_mem (Ka.inv_mem (hRaK hua)) hza.mem
    exact hno u' hu'K0 (hRbK hub) hu'4
  have hzdsq : (z * d) * (z * d) = 1 := by
    calc (z * d) * (z * d) = z * (d * z) * d := by group
      _ = z * (z * d) * d := by rw [hzd]
      _ = (z * z) * (d * d) := by group
      _ = 1 := by rw [hza.sq, hdd, one_mul]
  have hzW' : z ∈ W := hu2 ▸ W.mul_mem huW huW
  have hdW : d ∈ W := hd ▸ W.mul_mem huW hu'W
  have hshape : TwinThmEW.D4Shape (S : Subgroup G) t z d := by
    rw [hd]
    exact shape_commute' hΩ S hWn hWab hKa hKb hKab hRa hRb hRaK hRbK hRaS hRbS hza hzb hua huW hu4 hub hu'W hu'4 hu2 hu'2 t
  refine ⟨z, d, ⟨hza.ne_one, hza.sq, htz.symm, hzcent⟩, ⟨hd1, hdd, htd', ?_⟩,
    ⟨hzdne, hzdsq, ?_, ?_⟩, hzd, hzW', hdW, hshape⟩
  · exact h2 d hdR hdW hd1 hdd
  · calc z * d * t = z * (d * t) := by group
      _ = z * (t * d) := by rw [htd']
      _ = (z * t) * d := by group
      _ = (t * z) * d := by rw [htz]
      _ = t * (z * d) := by group
  · exact h2 (z * d) ((Ra ⊔ Rb).mul_mem hzR hdR) (W.mul_mem hzW' hdW) hzdne hzdsq

end Orb4Pair

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
