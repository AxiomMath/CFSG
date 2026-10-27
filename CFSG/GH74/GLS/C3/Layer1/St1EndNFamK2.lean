module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamCl5
public import CFSG.GH74.GLS.C3.Layer1.St1L710Lift

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open scoped commutatorElement

namespace Lem711Cfg

variable {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X}

theorem two_dvd_card_K (h : Lem711Cfg X L K x y) : 2 ∣ Nat.card ↥K := by
  have h360 : 360 ∣ Nat.card ↥K := by
    rw [← h.card_K_bar]
    exact Subgroup.card_quotient_dvd_card _
  exact (by norm_num : 2 ∣ 360).trans h360

theorem normalizes_of_centralizer (h : Lem711Cfg X L K x y) :
    ∀ g ∈ centralizer ({x} : Set X), g ∈ normalizer (K : Set X) := by
  intro g hg
  have hgx : g * x = x * g := mem_centralizer_singleton_iff.1 hg
  have hgxg : g * x * g⁻¹ = x := by rw [hgx]; group
  set K' : Subgroup X := K.map (MulAut.conj g).toMonoidHom with hK'
  have hC : (centralizer ({x} : Set X)).map (MulAut.conj g).toMonoidHom = centralizer ({x} : Set X) := by
    rw [Stage1.Thm2.Recip.map_centralizer_singleton_conj, hgxg]
  have hcomp' : IsCompIn (centralizer ({x} : Set X)) K' := by
    have := LU.Local.isCompIn_map_conj h.comp g
    rwa [hC] at this
  by_contra hnot
  have hne : K' ≠ K := fun he => hnot (Subgroup.mem_normalizer_iff_map_conj_eq.2 he)
  rcases LocalCores.distinct_components_commute h.comp.2 hcomp'.2 with heq | hcomm
  · have h1 := Subgroup.subgroupOf_inj.1 heq
    rw [inf_eq_left.2 h.comp.1, inf_eq_left.2 hcomp'.1] at h1
    exact hne h1.symm
  ·
    have h2 : 2 ∣ Nat.card ↥K' := by
      have : Nat.card ↥K' = Nat.card ↥K := Subgroup.card_map_of_injective (MulAut.conj g).injective
      rw [this]
      exact h.two_dvd_card_K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') 2 h2
    have hu2 : orderOf (u : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
    have huK : ∀ k ∈ K, (u : X) * k = k * (u : X) := by
      intro k hk
      have hk' : (⟨k, h.comp.1 hk⟩ : ↥(centralizer ({x} : Set X))) ∈ K.subgroupOf (centralizer ({x} : Set X)) := hk
      have hu' : (⟨(u : X), hcomp'.1 u.2⟩ : ↥(centralizer ({x} : Set X))) ∈
          K'.subgroupOf (centralizer ({x} : Set X)) := u.2
      have := Subgroup.commutator_le.1 (le_of_eq hcomm) _ hk' _ hu'
      have h3 : ⁅(⟨k, h.comp.1 hk⟩ : ↥(centralizer ({x} : Set X))),
          (⟨(u : X), hcomp'.1 u.2⟩ : ↥(centralizer ({x} : Set X)))⁆ = 1 := by
        simpa using this
      have h4 := congrArg Subtype.val h3
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h4
      calc (u : X) * k = (k * (u : X) * k⁻¹ * (u : X)⁻¹) * ((u : X) * k) := by rw [h4]; group
        _ = k * (u : X) := by group
    have hux : (u : X) * x = x * (u : X) := mem_centralizer_singleton_iff.1 (hcomp'.1 u.2)
    have hxu : (u : X) = x := h.h1 (u : X) hu2 huK hux
    have hxK' : x ∈ K' := hxu ▸ u.2
    obtain ⟨k0, hk0, hk0x⟩ := hxK'
    have hk0' : k0 = x := by
      have : g * k0 * g⁻¹ = x := hk0x
      have h5 : k0 = x := by
        calc k0 = g⁻¹ * (g * k0 * g⁻¹) * g := by group
          _ = g⁻¹ * x * g := by rw [this]
          _ = x := by rw [mul_assoc, ← hgx, ← mul_assoc, inv_mul_cancel, one_mul]
      exact h5
    rw [hk0'] at hk0
    have hxc : (⟨x, hk0⟩ : ↥K) ∈ center ↥K := Subgroup.mem_center_iff.2 fun k =>
      Subtype.ext (mem_centralizer_singleton_iff.1 (h.comp.1 k.2))
    exact h.center_K_no_involution ⟨x, hk0⟩ hxc h.hx


omit [Finite X] in
theorem odd_orderOf_of_mem_pPrimeCoreOf [Finite X] {M : Subgroup X} {w : X} (hw : w ∈ pPrimeCoreOf 2 M) :
    Odd (orderOf w) := by
  have h1 : orderOf (⟨w, hw⟩ : ↥(pPrimeCoreOf 2 M)) ∣ Nat.card ↥(pPrimeCoreOf 2 M) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd M) h1

theorem local_data (h : Lem711Cfg X L K x y) (hZ : pPrimeCore 2 ↥K = ⊥) :
    ∃ k w : X, k ∈ K ∧ k ≠ 1 ∧ Odd (orderOf k) ∧ w ∈ pPrimeCoreOf 2 (centralizer ({y} : Set X)) ∧
      orderOf k ∣ orderOf w ∧ y * k = k * y ∧
      (∀ g ∈ K, y * g = g * y → ⁅k, g⁆ ∈ pPrimeCoreOf 2 (centralizer ({y} : Set X))) := by
  have hZc : center ↥K = ⊥ := by rw [← h.pPrimeCore_eq_center]; exact hZ
  have hOK : pPrimeCoreOf 2 K = ⊥ := by
    unfold pPrimeCoreOf
    rw [hZ, Subgroup.map_bot]
  have hyC : y ∈ centralizer ({x} : Set X) := mem_centralizer_singleton_iff.2 h.hxy.symm
  have hyN : y ∈ normalizer (K : Set X) := h.normalizes_of_centralizer y hyC
  obtain ⟨w, ⟨hwO, hwC⟩, hwS⟩ := IsConcreteLE.not_le_iff_exists.1 h.unb
  have hwN : w ∈ normalizer (K : Set X) := h.normalizes_of_centralizer w hwC
  have hwodd : Odd (orderOf w) := odd_orderOf_of_mem_pPrimeCoreOf hwO
  have hwy : w ∈ centralizer ({y} : Set X) := (TwoThin.pPrimeCoreOf_le _) hwO
  have hwy' : w * y = y * w := mem_centralizer_singleton_iff.1 hwy
  obtain ⟨k, hkK, hky, hkw⟩ := C3.Layer1.EndN.L710.exists_lift_inner h.l2 h.hy hyN hwN hwy' hwodd
  set c : X := k⁻¹ * w with hcdef
  have hc : ∀ k' ∈ K, k' * c = c * k' := by
    intro k' hk'
    have h1 := hkw k' hk'
    rw [hOK, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hw_eq : w = k * c := by rw [hcdef]; group
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply hwS
    refine ⟨hwN, TwoThin.mem_normalizer_pPrimeCoreOf hwN, fun k' hk' => ?_⟩
    rw [hOK, Subgroup.mem_bot]
    apply commutatorElement_eq_one_iff_mul_comm.2
    have := hc k' hk'
    simpa [hcdef] using this
  have hkcomm : Commute k c := hc k hkK
  have key : ∀ n : ℕ, w ^ n = k ^ n * c ^ n := fun n => by
    conv_lhs => rw [hw_eq]
    exact hkcomm.mul_pow n
  have hkn : k ^ orderOf w = 1 := by
    have h1 : w ^ orderOf w = 1 := pow_orderOf_eq_one w
    rw [key] at h1
    have h3 : k ^ orderOf w = (c ^ orderOf w)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h4 : (⟨k ^ orderOf w, pow_mem hkK _⟩ : ↥K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k'
      apply Subtype.ext
      show (k' : X) * k ^ orderOf w = k ^ orderOf w * (k' : X)
      rw [h3]
      have h5 : Commute (c ^ orderOf w) (k' : X) := (show Commute c (k' : X) from (hc k' k'.2).symm).pow_left _
      have h6 : Commute (c ^ orderOf w)⁻¹ (k' : X) := h5.inv_left
      exact h6.symm.eq
    rw [hZc, Subgroup.mem_bot] at h4
    exact congrArg Subtype.val h4
  have hkdvd : orderOf k ∣ orderOf w := orderOf_dvd_of_pow_eq_one hkn
  refine ⟨k⁻¹, w, Subgroup.inv_mem _ hkK, inv_ne_one.2 hk1, by rw [orderOf_inv]; exact Odd.of_dvd_nat hwodd hkdvd, hwO,
    by rw [orderOf_inv]; exact hkdvd, (Commute.inv_right (show Commute y k from hky)).eq, fun g hg hgy => ?_⟩
  have hgC : g ∈ centralizer ({y} : Set X) := mem_centralizer_singleton_iff.2 hgy.symm
  have h1 : g * w * g⁻¹ ∈ pPrimeCoreOf 2 (centralizer ({y} : Set X)) :=
    TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer (Subgroup.le_normalizer hgC) hwO
  have h2 : w⁻¹ * (g * w * g⁻¹) ∈ pPrimeCoreOf 2 (centralizer ({y} : Set X)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hwO) h1
  have hcg : c * (k⁻¹ * g * k) = (k⁻¹ * g * k) * c := by
    have := hc _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkK) hg) hkK)
    exact this.symm
  have h3 : w⁻¹ * (g * w * g⁻¹) = k⁻¹ * (g * k * g⁻¹) := by
    calc w⁻¹ * (g * w * g⁻¹) = (c⁻¹ * (k⁻¹ * g * k) * c) * g⁻¹ := by
          rw [hw_eq]; group
      _ = (k⁻¹ * g * k) * g⁻¹ := by
          have h7 : c⁻¹ * (k⁻¹ * g * k) * c = k⁻¹ * g * k := by
            rw [mul_assoc, ← hcg, inv_mul_cancel_left]
          rw [h7]
      _ = k⁻¹ * (g * k * g⁻¹) := by group
  rw [commutatorElement_def]
  have h4 : k⁻¹ * g * k⁻¹⁻¹ * g⁻¹ = k⁻¹ * (g * k * g⁻¹) := by group
  rw [h4, ← h3]
  exact h2

end Lem711Cfg

end CFSG.GH74.GLS
