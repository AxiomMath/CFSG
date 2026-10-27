module

public import CFSG.CharacterTheory.Semidihedral.PrimeOrderCyclicConfinementLift
public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementFixedFactorSupport

public section

namespace CFSG.Semidihedral.StationaryConfinement

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.PrimeOrderCyclicConfinementLift (original_positive_power_prime_order)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem fixed_factor_cyclic (Na W A₀ : Subgroup G) [IsCyclic W] (g : G)
    (hWA : ∀ w ∈ W, ∀ a ∈ A₀, w * a = a * w) (hA₀ : A₀ ≤ Na)
    (hgB : g ∈ Subgroup.normalizer ((W ⊔ A₀ : Subgroup G) : Set G))
    (hTI : Na ⊓ Na.map (MulAut.conj g).toMonoidHom = ⊥) :
    IsCyclic A₀ ∧ Nat.card A₀ ∣ Nat.card W := by
  set A' := A₀.map (MulAut.conj g).toMonoidHom with hA'def
  have hA'B : A' ≤ W ⊔ A₀ := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hgB a).mp (Subgroup.mem_sup_right ha)
  have hA'A : A' ⊓ A₀ = ⊥ := by
    rw [eq_bot_iff, ← hTI]
    exact fun x hx => ⟨hA₀ hx.2, Subgroup.map_mono hA₀ hx.1⟩
  obtain ⟨hcyc, hdvd⟩ := cyclic_of_inf_eq_bot_of_commute hWA hA'B hA'A
  let e := A₀.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  refine ⟨isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact hdvd

theorem fixed_factor_fixed_point_free (t s : G) (Na U A₀ W : Subgroup G) [IsCyclic A₀] (g : G)
    (hNaC : Na ≤ C t) (hNaodd : Odd (Nat.card Na))
    (hU : ∀ x : G, x ∈ U ↔ x ∈ Na ∧ s * x * s⁻¹ = x⁻¹) (hA₀ : A₀ ≤ Na)
    (hWA : ∀ w ∈ W, ∀ a ∈ A₀, w * a = a * w) (hWA' : W ⊓ A₀ = ⊥)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, u * w = w * u)
    (hgB : g ∈ Subgroup.normalizer ((W ⊔ A₀ : Subgroup G) : Set G))
    (hg : g * (t * s) * g⁻¹ = t)
    (hcent : ∀ x ∈ Na, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ C t) :
    ∀ a ∈ A₀, a ≠ 1 → U ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by
  have hprime : ∀ x ∈ A₀, (orderOf x).Prime →
      U ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
    intro x hx hxp
    have hx1 : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hxp
      exact Nat.not_prime_one hxp
    rw [eq_bot_iff]
    rintro u ⟨huU, hux⟩
    rw [Subgroup.mem_bot]
    have hux' : u * x = x * u := Subgroup.mem_centralizer_singleton_iff.mp hux
    obtain ⟨huN, hsu⟩ := (hU u).mp huU
    set y := g⁻¹ * x * g with hydef
    have hyB : y ∈ W ⊔ A₀ := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgB) x).mp
        (Subgroup.mem_sup_right hx)
      simpa only [inv_inv] using h
    have hyr : y ^ orderOf x = 1 := by
      rw [hydef, show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by rw [inv_inv], conj_pow,
        pow_orderOf_eq_one, mul_one, mul_inv_cancel]
    obtain ⟨w, hw, a, ha, hwa⟩ := mem_sup_of_commute hWA hyB
    have hcomm : Commute w a := hWA w hw a ha
    have hwar : w ^ orderOf x * a ^ orderOf x = 1 := by
      rw [← hcomm.mul_pow, ← hwa, hyr]
    have hwr : w ^ orderOf x = 1 := by
      have hmem : w ^ orderOf x ∈ W ⊓ A₀ := ⟨W.pow_mem hw _, by
        rw [eq_inv_of_mul_eq_one_left hwar]
        exact A₀.inv_mem (A₀.pow_mem ha _)⟩
      rw [hWA', Subgroup.mem_bot] at hmem
      exact hmem
    have har : a ^ orderOf x = 1 := by
      rw [hwr, one_mul] at hwar
      exact hwar
    have hax : a ∈ Subgroup.zpowers x := mem_zpowers_of_pow_prime_eq_one hx ha hxp rfl har
    have hua : u * a = a * u := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hax
      exact (Commute.zpow_right (show Commute u x from hux') m).eq
    have huw : u * w = w * u := hUW u huU w hw
    have huy : u * y = y * u := by
      rw [hwa]
      calc u * (w * a) = w * (u * a) := by rw [← mul_assoc, huw, mul_assoc]
        _ = w * a * u := by rw [hua, mul_assoc]
    have hgux : (g * u * g⁻¹) * x = x * (g * u * g⁻¹) := by
      have hx' : x = g * y * g⁻¹ := by rw [hydef]; group
      rw [hx']
      calc g * u * g⁻¹ * (g * y * g⁻¹) = g * (u * y) * g⁻¹ := by group
        _ = g * (y * u) * g⁻¹ := by rw [huy]
        _ = g * y * g⁻¹ * (g * u * g⁻¹) := by group
    have hguC : g * u * g⁻¹ ∈ C t :=
      hcent x (hA₀ hx) hx1 (Subgroup.mem_centralizer_singleton_iff.mpr hgux)
    have htu : Commute t u := (Subgroup.mem_centralizer_singleton_iff.mp (hNaC huN)).symm
    have hinv : t * (g * u * g⁻¹) * t⁻¹ = (g * u * g⁻¹)⁻¹ := by
      rw [← hg]
      have h1 : (t * s) * u * (t * s)⁻¹ = u⁻¹ := by
        calc (t * s) * u * (t * s)⁻¹ = t * (s * u * s⁻¹) * t⁻¹ := by group
          _ = t * u⁻¹ * t⁻¹ := by rw [hsu]
          _ = u⁻¹ := by rw [htu.inv_right.eq, mul_inv_cancel_right]
      calc g * (t * s) * g⁻¹ * (g * u * g⁻¹) * (g * (t * s) * g⁻¹)⁻¹ =
            g * ((t * s) * u * (t * s)⁻¹) * g⁻¹ := by group
        _ = (g * u * g⁻¹)⁻¹ := by rw [h1]; group
    have hfix : t * (g * u * g⁻¹) * t⁻¹ = g * u * g⁻¹ := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp hguC, mul_inv_cancel_right]
    have hodd : Odd (orderOf (g * u * g⁻¹)) := by
      rw [show g * u * g⁻¹ = MulAut.conj g u from rfl, MulEquiv.orderOf_eq]
      exact hNaodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Na huN)
    have h1 := eq_one_of_conj_fixed_inverted hodd hfix hinv
    have hu : u = g⁻¹ * (g * u * g⁻¹) * g := by group
    rw [hu, h1]
    group
  intro a ha ha1
  obtain ⟨k, r, -, hr, -, hak, hord⟩ := original_positive_power_prime_order ha ha1
  have h := hprime (a ^ k) hak (hord ▸ hr)
  rw [eq_bot_iff, ← h]
  refine inf_le_inf_left _ ?_
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
  exact ((Commute.pow_right (show Commute z a from hz) k)).eq

end CFSG.Semidihedral.StationaryConfinement
