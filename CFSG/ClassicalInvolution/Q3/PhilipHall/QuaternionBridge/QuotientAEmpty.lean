module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.QuotientFamily
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotAEmpty

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {N : Subgroup Y} [N.Normal]

theorem conjSub_eq_of_map_conjSub_eq (hd : TightDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) {u : Y}
    (h : conjSub (QuotientGroup.mk' N u) ((tightCore R).map (QuotientGroup.mk' N)) =
      (tightCore R).map (QuotientGroup.mk' N)) :
    conjSub u (tightCore R) = tightCore R := by
  have h0 := core_inf_eq_bot hd hN2 htN
  have htK : t ∈ tightCore R := hd.isUniqueInvolution_core.mem
  have hx : QuotientGroup.mk' N (u * t * u⁻¹) ∈ (tightCore R).map (QuotientGroup.mk' N) := by
    rw [← h]
    have h1 := conj_mem_conjSub (n := QuotientGroup.mk' N u)
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' N) htK)
    rwa [← map_inv, ← map_mul, ← map_mul] at h1
  obtain ⟨k, hk, hkx⟩ := hx
  have hνN : k⁻¹ * (u * t * u⁻¹) ∈ N := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkx
    exact hkx
  set ν : Y := k⁻¹ * (u * t * u⁻¹) with hν
  have hxe : u * t * u⁻¹ = k * ν := by rw [hν]; group
  have hνZ : ∀ a : Y, a * ν = ν * a := Subgroup.mem_center_iff.mp (hNc hνN)
  have hx2 : (u * t * u⁻¹) * (u * t * u⁻¹) = 1 := by
    calc (u * t * u⁻¹) * (u * t * u⁻¹) = u * (t * t) * u⁻¹ := by group
      _ = 1 := by rw [t_mul_t hd]; group
  have hkk : k * k = 1 := by
    rw [hxe] at hx2
    have e1 : (k * ν) * (k * ν) = (k * k) * (ν * ν) := by
      calc (k * ν) * (k * ν) = k * (ν * k) * ν := by group
        _ = k * (k * ν) * ν := by rw [← hνZ k]
        _ = (k * k) * (ν * ν) := by group
    rw [e1] at hx2
    have h2 : k * k ∈ tightCore R ⊓ N := by
      refine ⟨(tightCore R).mul_mem hk hk, ?_⟩
      have : k * k = (ν * ν)⁻¹ := eq_inv_of_mul_eq_one_left hx2
      rw [this]
      exact N.inv_mem (N.mul_mem hνN hνN)
    rw [h0, Subgroup.mem_bot] at h2
    exact h2
  rcases hd.isUniqueInvolution_core.unique k hk hkk with hk1 | hkt
  ·
    exfalso
    apply htN
    have hxN : u * t * u⁻¹ ∈ N := by rw [hxe, hk1, one_mul]; exact hνN
    have h3 := (inferInstance : N.Normal).conj_mem _ hxN u⁻¹
    rwa [show u⁻¹ * (u * t * u⁻¹) * u⁻¹⁻¹ = t by group] at h3
  · by_cases hν1 : ν = 1
    · have hut : u * t * u⁻¹ = t := by rw [hxe, hkt, hν1, mul_one]
      have hC : u ∈ Subgroup.centralizer ({t} : Set Y) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc u * t = (u * t * u⁻¹) * u := by group
          _ = t * u := by rw [hut]
      exact mem_normalizer_iff_conjSub_eq.mp (hd.le_normalizer_core hC)
    · exfalso
      exact conjSub_map_ne_of_twin hd hq8 hNc hN2 htN (c := ν) (y := u) hνN hν1
        (by rw [hxe, hkt]) h

theorem centQuotGen_of_tight (hd : TightDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) :
    CentQuotGen (CoreAssembly.conjClass (tightCore R)) N where
  hyp := hd.hypOmegaGen
  hyp' := by
    have h : quotFamily (CoreAssembly.conjClass (tightCore R)) N =
        CoreAssembly.conjClass ((tightCore R).map (QuotientGroup.mk' N)) :=
      image_conjClass (N := N) (tightCore R)
    rw [h]
    exact hypOmegaGen_map hd hNc hN2 htN
  meet J hJ := by
    rw [inf_comm]
    exact inf_conj_eq_bot hd hN2 htN hJ
  eq_of_map := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ hmap
    rw [TwistQ.conjSub_map (N := N), TwistQ.conjSub_map (N := N)] at hmap
    have h1 : conjSub (QuotientGroup.mk' N (h⁻¹ * g)) ((tightCore R).map (QuotientGroup.mk' N)) =
        (tightCore R).map (QuotientGroup.mk' N) := by
      rw [map_mul, map_inv, conjSub_mul, hmap, conjSub_inv_conjSub]
    have h2 := conjSub_eq_of_map_conjSub_eq hd hq8 hNc hN2 htN h1
    calc conjSub g (tightCore R) = conjSub h (conjSub (h⁻¹ * g) (tightCore R)) := by
          rw [← conjSub_mul]
          congr 1
          group
      _ = conjSub h (tightCore R) := by rw [h2]
  normalizer_of_map := by
    rintro _ ⟨g, rfl⟩ u hu
    rw [TwistQ.conjSub_map (N := N), mem_normalizer_iff_conjSub_eq] at hu
    have h1 : conjSub (QuotientGroup.mk' N (g⁻¹ * u * g))
        ((tightCore R).map (QuotientGroup.mk' N)) = (tightCore R).map (QuotientGroup.mk' N) := by
      have : conjSub (QuotientGroup.mk' N g)⁻¹ (conjSub (QuotientGroup.mk' N u)
          (conjSub (QuotientGroup.mk' N g) ((tightCore R).map (QuotientGroup.mk' N)))) =
          (tightCore R).map (QuotientGroup.mk' N) := by
        rw [hu, conjSub_inv_conjSub]
      rw [map_mul, map_mul, map_inv, conjSub_mul, conjSub_mul]
      exact this
    have h2 := conjSub_eq_of_map_conjSub_eq hd hq8 hNc hN2 htN h1
    rw [mem_normalizer_iff_conjSub_eq]
    calc conjSub u (conjSub g (tightCore R))
        = conjSub g (conjSub (g⁻¹ * u * g) (tightCore R)) := by
          rw [← conjSub_mul, ← conjSub_mul]
          congr 1
          group
      _ = conjSub g (tightCore R) := by rw [h2]

theorem aEmpty_map (hd : TightDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) :
    AEmpty (CoreAssembly.conjClass ((tightCore R).map (QuotientGroup.mk' N)))
      ((tightCore R).map (QuotientGroup.mk' N)) := by
  have h : quotFamily (CoreAssembly.conjClass (tightCore R)) N =
      CoreAssembly.conjClass ((tightCore R).map (QuotientGroup.mk' N)) :=
    image_conjClass (N := N) (tightCore R)
  have := (centQuotGen_of_tight hd hq8 hNc hN2 htN).aEmpty_quotFamily (fun J hJ => hd.aEmpty J hJ)
    ((tightCore R).map (QuotientGroup.mk' N))
    (map_mem_quotFamily (CoreAssembly.mem_conjClass_self _))
  rw [h] at this
  exact this

theorem aEmpty_map' (hd : TightDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) :
    AEmpty (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
      (tightCore (R.map (QuotientGroup.mk' N))) := by
  rw [← TwistQ.tightCore_map (TwistQ.inf_eq_bot hd hN2 htN)]
  exact aEmpty_map hd hq8 hNc hN2 htN

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
