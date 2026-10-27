module

public import CFSG.LargeExtraspecial.S12Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem s12_rho_eq_one_of_odd {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) (h : S.M) (hodd : Odd (orderOf (h : G)))
    (hC : S.ρ h ∈ centralizer (S.Lbar g : Set S.O)) : S.ρ h = 1 := by
  set a := g * S.z * g⁻¹ with ha
  set T := S.conjBy g
  have hTz : T.z = a := rfl
  have hhm : (h : G) ^ orderOf (h : G) = 1 := pow_orderOf_eq_one _
  have hhz : (h : G) * S.z * (h : G)⁻¹ = S.z := S.s12_conj_z_of_mem_M h.2
  have hN : S.ρ h ∈ normalizer (S.Lbar g : Set S.O) := by
    rw [mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      rw [← mem_centralizer_iff.mp hC t ht, mul_inv_cancel_right]
      exact ht
    · intro ht
      have e := mem_centralizer_iff.mp hC _ ht
      have e2 : t = S.ρ h * t * (S.ρ h)⁻¹ := by
        calc t = (S.ρ h)⁻¹ * (S.ρ h * t * (S.ρ h)⁻¹ * S.ρ h) := by group
          _ = S.ρ h * t * (S.ρ h)⁻¹ := by rw [e]; group
      rw [e2]
      exact ht
  have hfix := (S.timmesfeld_12_4_1 haQ hne hn h).mp hN
  have hha : (h : G) * a * (h : G)⁻¹ = a := by
    rw [S.ρ_cl h haQ] at hfix
    rcases (S.cl_eq_cl_iff haQ (S.conj_mem_QG h.2 haQ)).mp hfix.symm with h1 | h1
    · exact h1
    · exfalso
      have h2 : (h : G) * a * (h : G)⁻¹ = S.z * a := by rw [h1, S.z_comm_QG haQ]
      exact S.z_ne_one (s12_eq_one_of_conj_odd hhz h2 S.z_sq hhm hodd)
  have hCa : (h : G) ∈ T.M := by
    rw [Setting.mem_M_iff, hTz]
    calc (h : G) * a = (h : G) * a * (h : G)⁻¹ * h := by group
      _ = a * h := by rw [hha]
  have hCa' : (h : G)⁻¹ ∈ T.M := T.M.inv_mem hCa
  have hhM' : (h : G)⁻¹ ∈ S.M := S.M.inv_mem h.2
  have hNQa : ∀ {k : G}, k ∈ T.M → ∀ w ∈ S.Qa g, k * w * k⁻¹ ∈ S.Qa g :=
    fun hk w hw => T.conj_mem_QG hk hw
  have hNL0 : ∀ {k : G}, k ∈ T.M → k ∈ S.M → ∀ y ∈ S.L0 g, k * y * k⁻¹ ∈ S.L0 g :=
    fun hk hkM y hy => ⟨hNQa hk y hy.1, S.M.mul_mem (S.M.mul_mem hkM hy.2) (S.M.inv_mem hkM)⟩
  have hNN : ∀ x ∈ S.QG ⊓ S.Qa g, (h : G) * x * (h : G)⁻¹ ∈ S.QG ⊓ S.Qa g :=
    fun x hx => ⟨S.conj_mem_QG h.2 hx.1, hNQa hCa x hx.2⟩
  have haN : a ∈ S.QG ⊓ S.Qa g := ⟨haQ, T.z_mem_QG⟩
  have hA0 : ∀ y ∈ S.L0 g, (h : G) * y * (h : G)⁻¹ * y⁻¹ ∈ S.QG ⊓ S.Qa g := by
    intro y hy
    refine ⟨?_, (S.Qa g).mul_mem (hNQa hCa y hy.1) ((S.Qa g).inv_mem hy.1)⟩
    have hyM : y ∈ S.M := hy.2
    have hmem : (h : G) * y * (h : G)⁻¹ * y⁻¹ ∈ S.M :=
      S.M.mul_mem (S.M.mul_mem (S.M.mul_mem h.2 hyM) hhM') (S.M.inv_mem hyM)
    have hρy : S.ρ ⟨y, hyM⟩ ∈ S.Lbar g := S.s12_mem_Lbar.mpr ⟨y, hy, rfl⟩
    have hcomm := mem_centralizer_iff.mp hC _ hρy
    have h1 : S.ρ ⟨(h : G) * y * (h : G)⁻¹ * y⁻¹, hmem⟩ = 1 := by
      have e : (⟨(h : G) * y * (h : G)⁻¹ * y⁻¹, hmem⟩ : S.M) = h * ⟨y, hyM⟩ * h⁻¹ * ⟨y, hyM⟩⁻¹ :=
        rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    exact (S.ρ_eq_one_iff _).mp h1
  have hrel := S.relIndex_L0 haQ hne
  have hA1 : ∀ w ∈ S.Qa g, (h : G) * w * (h : G)⁻¹ * w⁻¹ ∈ S.L0 g := by
    intro w hw
    have hhw := hNQa hCa w hw
    refine (mul_mem_iff_of_relIndex_eq_two hrel hhw ((S.Qa g).inv_mem hw)).mpr ?_
    constructor
    · intro h1
      have := hNL0 hCa' hhM' _ h1
      rw [show (h : G)⁻¹ * ((h : G) * w * (h : G)⁻¹) * (h : G)⁻¹⁻¹ = w by group] at this
      exact (S.L0 g).inv_mem this
    · intro h1
      have := hNL0 hCa h.2 _ ((S.L0 g).inv_mem h1)
      rwa [inv_inv] at this
  have hA2 : ∀ w ∈ S.Qa g,
      ((h : G) ^ 2) * w * ((h : G) ^ 2)⁻¹ * w⁻¹ ∈ S.QG ⊓ S.Qa g := by
    intro w hw
    set c := (h : G) * w * (h : G)⁻¹ * w⁻¹ with hc
    have hcL := hA1 w hw
    have e : ((h : G) ^ 2) * w * ((h : G) ^ 2)⁻¹ * w⁻¹ =
        ((h : G) * c * (h : G)⁻¹ * c⁻¹) * (c * c) := by
      rw [hc, pow_two]
      group
    rw [e]
    refine (S.QG ⊓ S.Qa g).mul_mem (hA0 c hcL) ?_
    rcases T.sq_eq_one_or_z hcL.1 with h2 | h2
    · rw [← pow_two, h2]
      exact (S.QG ⊓ S.Qa g).one_mem
    · rw [← pow_two, h2]
      exact haN
  have hNN2 : ∀ j : ℕ, ∀ x ∈ S.QG ⊓ S.Qa g,
      ((h : G) ^ 2) ^ j * x * (((h : G) ^ 2) ^ j)⁻¹ ∈ S.QG ⊓ S.Qa g := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      have e : ((h : G) ^ 2) ^ (j + 1) * x * (((h : G) ^ 2) ^ (j + 1))⁻¹ =
          (h : G) * ((h : G) * (((h : G) ^ 2) ^ j * x * (((h : G) ^ 2) ^ j)⁻¹) * (h : G)⁻¹) *
            (h : G)⁻¹ := by group
      rw [e]
      exact hNN _ (hNN _ (ih x hx))
  have hA3 : ∀ j : ℕ, ∀ w ∈ S.Qa g,
      ((h : G) ^ 2) ^ j * w * (((h : G) ^ 2) ^ j)⁻¹ * w⁻¹ ∈ S.QG ⊓ S.Qa g := by
    intro j
    induction j with
    | zero => intro w _; simp
    | succ j ih =>
      intro w hw
      have e : ((h : G) ^ 2) ^ (j + 1) * w * (((h : G) ^ 2) ^ (j + 1))⁻¹ * w⁻¹ =
          (((h : G) ^ 2) ^ j * ((h : G) ^ 2 * w * ((h : G) ^ 2)⁻¹ * w⁻¹) *
            (((h : G) ^ 2) ^ j)⁻¹) * (((h : G) ^ 2) ^ j * w * (((h : G) ^ 2) ^ j)⁻¹ * w⁻¹) := by
        group
      rw [e]
      exact (S.QG ⊓ S.Qa g).mul_mem (hNN2 j _ (hA2 w hw)) (ih w hw)
  obtain ⟨j, hj⟩ := hodd
  have hhpow : ((h : G) ^ 2) ^ (j + 1) = h := by
    rw [← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, ← hj, pow_succ, hhm, one_mul]
  have hA : ∀ w ∈ S.Qa g, (h : G) * w * (h : G)⁻¹ * w⁻¹ ∈ S.QG ⊓ S.Qa g := by
    intro w hw
    have := hA3 (j + 1) w hw
    rwa [hhpow] at this
  have hodd' : Odd (orderOf (h : G)) := ⟨j, hj⟩
  have hB : ∀ x ∈ S.QG ⊓ S.Qa g, (h : G) * x * (h : G)⁻¹ = x := by
    intro x hx
    set x' := (h : G) * x * (h : G)⁻¹ with hx'
    have hx'N := hNN x hx
    have hcomm : ∀ w ∈ S.Qa g, (x⁻¹ * x') * w = w * (x⁻¹ * x') := by
      intro w hw
      set w' := (h : G)⁻¹ * w * (h : G) with hw'
      have hw'Q : w' ∈ S.Qa g := by
        have := hNQa hCa' w hw
        rwa [inv_inv] at this
      have hnN : w' * w⁻¹ ∈ S.QG ⊓ S.Qa g := by
        have := (S.QG ⊓ S.Qa g).inv_mem (hA w' hw'Q)
        rwa [show ((h : G) * w' * (h : G)⁻¹ * w'⁻¹)⁻¹ = w' * w⁻¹ by rw [hw']; group] at this
      have e1 : x' * w * x'⁻¹ * w⁻¹ = (h : G) * (x * w' * x⁻¹ * w'⁻¹) * (h : G)⁻¹ := by
        rw [hx', hw']
        group
      have e2 : (h : G) * (x * w' * x⁻¹ * w'⁻¹) * (h : G)⁻¹ = x * w' * x⁻¹ * w'⁻¹ := by
        rcases T.commutator_eq_one_or_z hx.2 hw'Q with h1 | h1 <;> rw [h1]
        · group
        · exact hha
      have hxn : x * (w' * w⁻¹) = (w' * w⁻¹) * x := S.QG_inf_Qa_comm hne hx hnN
      have e3 : x * w' * x⁻¹ * w'⁻¹ = x * w * x⁻¹ * w⁻¹ := by
        set n := w' * w⁻¹ with hn
        have hw'eq : w' = n * w := by rw [hn]; group
        rw [hw'eq]
        have e : x * (n * w) * x⁻¹ * (n * w)⁻¹ = n * (x * w * x⁻¹ * w⁻¹) * n⁻¹ := by
          calc x * (n * w) * x⁻¹ * (n * w)⁻¹ = (x * n) * w * x⁻¹ * w⁻¹ * n⁻¹ := by group
            _ = (n * x) * w * x⁻¹ * w⁻¹ * n⁻¹ := by rw [hxn]
            _ = n * (x * w * x⁻¹ * w⁻¹) * n⁻¹ := by group
        rw [e]
        rcases T.commutator_eq_one_or_z hx.2 hw with h1 | h1 <;> rw [h1]
        · group
        · have hna : n * a = a * n := T.z_comm_QG hnN.2
          calc n * T.z * n⁻¹ = a * n * n⁻¹ := by rw [hTz, hna]
            _ = T.z := by rw [hTz]; group
      have e4 : x' * w * x'⁻¹ * w⁻¹ = x * w * x⁻¹ * w⁻¹ := by rw [e1, e2, e3]
      calc (x⁻¹ * x') * w = x⁻¹ * (x' * w * x'⁻¹ * w⁻¹) * w * x' := by group
        _ = x⁻¹ * (x * w * x⁻¹ * w⁻¹) * w * x' := by rw [e4]
        _ = w * (x⁻¹ * x') := by group
    rcases T.eq_one_or_z_of_commute (T.QG.mul_mem (T.QG.inv_mem hx.2) hx'N.2) hcomm with h1 | h1
    · calc (h : G) * x * (h : G)⁻¹ = x * (x⁻¹ * x') := by rw [hx']; group
        _ = x := by rw [h1, mul_one]
    · exfalso
      have h2 : (h : G) * x * (h : G)⁻¹ = a * x := by
        calc (h : G) * x * (h : G)⁻¹ = x * (x⁻¹ * x') := by rw [hx']; group
          _ = x * a := by rw [h1, hTz]
          _ = a * x := T.z_comm_QG hx.2
      exact S.s12_conj_z_ne_one g (s12_eq_one_of_conj_odd hha h2 (S.s12_conj_z_sq g) hhm hodd')
  have hC' : ∀ w ∈ S.Qa g, (h : G) * w = w * (h : G) := by
    intro w hw
    set c := (h : G) * w * (h : G)⁻¹ * w⁻¹ with hc
    have hcN := hA w hw
    have h1 : (h : G) * c * (h : G)⁻¹ = c := hB c hcN
    have h2 : (h : G) * w * (h : G)⁻¹ = c * w := by rw [hc]; group
    have hc1 := s12_eq_one_of_conj_odd h1 h2 (S.QG_inf_Qa_sq hne hcN) hhm hodd'
    calc (h : G) * w = (h : G) * w * (h : G)⁻¹ * (h : G) := by group
      _ = c * w * h := by rw [h2]
      _ = w * h := by rw [hc1, one_mul]
  have hhQa : (h : G) ∈ T.QG := T.mem_QG_of_commute hCa hC'
  have hL : S.ρ h ∈ S.Lbar g := S.s12_mem_Lbar.mpr ⟨h, ⟨hhQa, h.2⟩, rfl⟩
  have : IsElementaryAbelian 2 (S.Lbar g) := S.isElementaryAbelian_Lbar haQ
  have h2 : S.ρ h ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hL
  have hd1 : orderOf (S.ρ h) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hd2 : orderOf (S.ρ h) ∣ orderOf (h : G) := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_map_dvd _ _
  have hodd2 : Odd (orderOf (S.ρ h)) := Odd.of_dvd_nat hodd' hd2
  have h1 : orderOf (S.ρ h) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd1 with h | h
    · exact h
    · rw [h] at hodd2
      exact absurd hodd2 (by decide)
  exact orderOf_eq_one_iff.mp h1

theorem timmesfeld_12_4_2 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) : IsPGroup 2 ↥(S.Mbar ⊓ centralizer (S.Lbar g : Set S.O)) := by
  rintro ⟨x, hxM, hxC⟩
  obtain ⟨h, rfl⟩ := hxM
  have ho : orderOf (h : G) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨k, r, hr, hkr⟩ := Nat.exists_eq_two_pow_mul_odd ho
  have hodd : Odd (orderOf ((h ^ 2 ^ k : S.M) : G)) := by
    refine Odd.of_dvd_nat hr (orderOf_dvd_of_pow_eq_one ?_)
    rw [Subgroup.coe_pow, ← pow_mul, ← hkr, pow_orderOf_eq_one]
  have hC : S.ρ (h ^ 2 ^ k) ∈ centralizer (S.Lbar g : Set S.O) := by
    rw [map_pow]
    exact (centralizer (S.Lbar g : Set S.O)).pow_mem hxC _
  have h1 := S.s12_rho_eq_one_of_odd haQ hne hn (h ^ 2 ^ k) hodd hC
  refine ⟨k, Subtype.ext ?_⟩
  rw [map_pow] at h1
  simpa using h1

end Setting

end CFSG.LargeExtraspecial
