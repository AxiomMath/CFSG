module

public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Shape
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.GH74.GLS.Stage2.Local.Basic
import CFSG.GroupTheory.LocalCores.Components
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12

open Subgroup CFSG CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

theorem odd_orderOf_of_mem_pPrimeCore' {H : Type} [Group H] [Finite H] {o : H}
    (ho : o ∈ pPrimeCore 2 H) : Odd (orderOf o) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf o ∣ Nat.card (pPrimeCore 2 H) := by
    rw [← Subgroup.orderOf_mk o ho]
    exact orderOf_dvd_natCard _
  exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h1

section Extract

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem m12_data' (hctx : Stage2Ctx G z Kind.m12 S) : Stage1M12 G z S := by
  have hd := hctx.data
  cases hd with
  | m12 h => exact h

theorem barShape_of_ctx (hctx : Stage2Ctx G z Kind.m12 S) :
    BarShape (CentralizerBar z) (toBar z ⟨z, mem_Cen_self z⟩) := by
  classical
  have h := m12_data' hctx
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  have hz2' : orderOf (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hz2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    have hmem : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) :=
      (QuotientGroup.eq_one_iff _).1 h1
    have hodd := odd_orderOf_of_mem_pPrimeCore' hmem
    rw [hz2'] at hodd
    exact absurd hodd (by decide)
  · rw [← map_mul]
    have : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) * ⟨z, mem_Cen_self z⟩ = 1 :=
      Subtype.ext (by
        have := pow_orderOf_eq_one z
        rwa [hz2, pow_two] at this)
    rw [this, map_one]
  · intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
    show toBar z c * toBar z ⟨z, mem_Cen_self z⟩ = toBar z ⟨z, mem_Cen_self z⟩ * toBar z c
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.1 c.2)
  · exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  · obtain ⟨A, B, hcp, ⟨eA⟩, ⟨eB⟩, hAn⟩ := h.W_shape
    obtain ⟨A₃, ⟨e3⟩, -, -, hF, hWA, hfix⟩ := h.L_shape
    obtain ⟨hWn, ⟨eq⟩⟩ := h.quot
    refine ⟨WBar z, A, B, A₃, hWn, ?_, hcp, ⟨eA⟩, ⟨eB⟩, hAn, ⟨e3⟩, hF, hWA, ?_, ⟨eq⟩⟩
    · obtain ⟨U, -, -, -, hzU, hUW, -⟩ := h.four_group
      exact ⟨⟨z, mem_Cen_self z⟩, Subgroup.mem_subgroupOf.2 (hUW hzU), rfl⟩
    · intro w hw hcomm
      obtain ⟨c, hc, rfl⟩ := hfix w hw hcomm
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hc)
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [← map_zpow]
      congr 1
      apply Subtype.ext
      simpa using hk


end Extract

section ClaimA

variable {X : Type} [Group X] [Finite X]

theorem mem_fitting_of_barShape {x : X} (hx2 : orderOf x = 2)
    (hJs : IsSimpleGroup ↥(generalizedFitting X))
    (hJn : ∃ a b : ↥(generalizedFitting X), a * b ≠ b * a)
    (T : Sylow 2 X) (hTc : ∀ t ∈ (T : Subgroup X), t * x = x * t)
    {P : Type} [Group P] [Finite P] {zc : P} (hP : BarShape P zc)
    (ρ : ↥(centralizer ({x} : Set X)) →* P) (hρ : Function.Surjective ρ)
    (hodd : ∀ y ∈ ρ.ker, Odd (orderOf y))
    (hρx : ρ ⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = zc) :
    x ∈ generalizedFitting X := by
  classical
  by_contra hxJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJnorm : (generalizedFitting X).Normal := LocalCores.generalized_fitting_characteristic.2
  obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal T (N := generalizedFitting X)
  have hJeven : 2 ∣ Nat.card ↥(generalizedFitting X) := by
    by_contra h
    have hodd' : Odd (Nat.card ↥(generalizedFitting X)) := Nat.odd_iff.mpr (by omega)
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
    obtain ⟨a, b, hab⟩ := hJn
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)
  have hQcard : 2 ∣ Nat.card ↥(Q : Subgroup ↥(generalizedFitting X)) := by
    rw [Sylow.card_eq_multiplicity Q]
    have h1 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two
      (Nat.card_pos (α := ↥(generalizedFitting X))).ne' hJeven
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.1 h1)
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Q : Subgroup ↥(generalizedFitting X))) 2 hQcard
  set t₀ : ↥(generalizedFitting X) := (t' : ↥(generalizedFitting X)) with ht₀def
  set t : X := (t₀ : X) with htdef
  have ht2 : orderOf t = 2 := by
    rw [htdef, Subgroup.orderOf_coe, ht₀def, Subgroup.orderOf_coe]; exact ht'
  have htT : t ∈ (T : Subgroup X) := by
    have : t₀ ∈ (Q : Subgroup ↥(generalizedFitting X)) := t'.2
    rw [hQ, Subgroup.mem_subgroupOf] at this
    exact this.1
  have htJ : t ∈ generalizedFitting X := t₀.2
  have htC : t ∈ centralizer ({x} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 (hTc t htT)
  set Yx : Subgroup ↥(centralizer ({x} : Set X)) := (generalizedFitting X).subgroupOf (centralizer ({x} : Set X)) with hYx
  have hYxn : Yx.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [hYx, Subgroup.mem_subgroupOf] at ha ⊢
    exact hJnorm.conj_mem _ ha g
  have htY : (⟨t, htC⟩ : ↥(centralizer ({x} : Set X))) ∈ Yx := Subgroup.mem_subgroupOf.2 htJ
  have hρt : ρ ⟨t, htC⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨t, htC⟩ : ↥(centralizer ({x} : Set X))) ∈ ρ.ker := h1
    have := hodd _ hmem
    have h2 : orderOf (⟨t, htC⟩ : ↥(centralizer ({x} : Set X))) = 2 := by rw [← Subgroup.orderOf_coe]; exact ht2
    rw [h2] at this
    exact absurd this (by decide)
  have hN : (Yx.map ρ).Normal := hYxn.map ρ hρ
  have hNne : Yx.map ρ ≠ ⊥ := by
    intro h
    apply hρt
    have : ρ ⟨t, htC⟩ ∈ Yx.map ρ := Subgroup.mem_map_of_mem ρ htY
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hzcN : zc ∈ Yx.map ρ := hP.zc_mem_of_normal hNne
  obtain ⟨y, hyY, hρy⟩ := Subgroup.mem_map.1 hzcN
  have hxC : x ∈ centralizer ({x} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set xC : ↥(centralizer ({x} : Set X)) := ⟨x, hxC⟩ with hxCdef
  have hk : y * xC⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρy, hρx, mul_inv_cancel]
  have hkodd := hodd _ hk
  have hcomm : y * xC = xC * y := by
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.1 y.2
    simpa [hxCdef] using this
  have hxC2 : xC * xC = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  obtain ⟨j, hj⟩ := hkodd
  set k : ↥(centralizer ({x} : Set X)) := y * xC⁻¹ with hkdef
  have hkx : Commute k xC := by
    show k * xC = xC * k
    rw [hkdef]
    calc y * xC⁻¹ * xC = y := by group
      _ = xC * (y * xC⁻¹) := by
        rw [← mul_assoc, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hy : y = k * xC := by rw [hkdef]; group
  have hym : y ^ (orderOf k) = xC := by
    rw [hy, hkx.mul_pow, pow_orderOf_eq_one, one_mul, hj]
    have : xC ^ (2 * j + 1) = xC := by
      rw [pow_succ, pow_mul, show xC ^ 2 = 1 by rw [pow_two]; exact hxC2, one_pow, one_mul]
    exact this
  apply hxJ
  have hyJ : (y : X) ∈ generalizedFitting X := Subgroup.mem_subgroupOf.1 hyY
  have : ((y ^ (orderOf k) : ↥(centralizer ({x} : Set X))) : X) = x := by rw [hym]
  rw [Subgroup.coe_pow] at this
  rw [← this]
  exact Subgroup.pow_mem _ hyJ _


end ClaimA

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12
