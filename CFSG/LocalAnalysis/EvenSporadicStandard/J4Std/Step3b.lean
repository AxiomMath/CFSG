module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Step3
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup

variable {G : Type} [Group G] {L U T0 : Subgroup G} {z : G}

structure LocalData11 (L U : Subgroup G) (p q u0 : G) : Prop where
  p_mem : p ∈ Hloc L U
  q_mem : q ∈ Hloc L U
  u0_mem : u0 ∈ U
  u0_ne : u0 ≠ 1
  p_order : orderOf p = 11
  q_conj : q * p * q⁻¹ = p ^ 2
  u0_fix : p * u0 = u0 * p
  fix : ∀ u ∈ U, p * u = u * p → u = 1 ∨ u = u0
  cent : ∀ h ∈ Hloc L U, p * h = h * p → ∃ k : ℕ, ∃ u ∈ U, h = p ^ k * u
  comm : ∀ s : G, (∀ u ∈ U, s * u * s⁻¹ ∈ U) → s * p = p * s →
    (∃ k : ℕ, ∀ u ∈ U, s * (s * u * s⁻¹) * s⁻¹ = p ^ k * u * (p ^ k)⁻¹) →
    ∃ m : ℕ, ∀ u ∈ U, s * u * s⁻¹ = p ^ m * u * (p ^ m)⁻¹

theorem N_inf_centralizer_eq (hS : Setting L z) (hU : U ≤ L) :
    Nsub U z ⊓ centralizer ({z} : Set G) = Vsub (Hloc L U) z := by
  apply le_antisymm
  · intro n hn
    obtain ⟨hnN, hnc⟩ := mem_inf.1 hn
    have hc : z * n = n * z := (mem_centralizer_singleton_iff.1 hnc).symm
    obtain ⟨l, hl, hnl⟩ := exists_Hloc_of_mem_N_comm hS hU hnN hc
    refine (mem_Vsub_iff hS Hloc_le_L).2 ⟨l, hl, ?_⟩
    rcases hnl with hnl | hnl
    · exact Or.inl hnl
    · exact Or.inr (by rw [hnl, hS.z_comm l (Hloc_le_L hl)])
  · refine sup_le (fun h hh => mem_inf.2 ⟨Hloc_le_N hS hU hh, ?_⟩) ?_
    · exact mem_centralizer_singleton_iff.2 (hS.z_comm h (Hloc_le_L hh)).symm
    · rw [zpowers_le]
      exact mem_inf.2 ⟨V_le_N z_mem_V, mem_centralizer_singleton_iff.2 rfl⟩

variable (hS : Setting L z) (hD : LocalData L U T0)
  (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u)

include hS hD htrans

theorem card_N_of_trans [Finite G] :
    Nat.card (Nsub U z) = 2 ^ 12 * Nat.card (Hloc L U) := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  have hcentN : Nat.card (Nsub U z ⊓ centralizer ({z} : Set G) : Subgroup G) =
      2 * Nat.card (Hloc L U) := by
    rw [N_inf_centralizer_eq hS hUL]; exact card_Vsub hS Hloc_le_L
  have hDset : Dset U z = (U : Set G) :=
    Set.ext fun u => ⟨fun h => h.1, fun hu => ⟨hu, htrans u hu⟩⟩
  have hXcard : {m | ∃ k ∈ Nsub U z, m = k * z * k⁻¹}.ncard = 2 ^ 11 := by
    rw [Dset_card_eq hS hUL, hDset, show (U : Set G).ncard = Nat.card U from
      (Nat.card_coe_set_eq (U : Set G)).symm, hD.card_U]
  have := card_inf_centralizer_mul_ncard (Nsub U z) z
  rw [hcentN, hXcard] at this
  rw [← this]
  ring

theorem factorization_N [Finite G] : (Nat.card (Nsub U z)).factorization 11 = 1 := by
  rw [card_N_of_trans hS hD htrans, hD.card_H]
  have e : 2 ^ 12 * 501397585920 = 11 * (2 ^ 12 * 45581598720) := by norm_num
  rw [e, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num : Nat.Prime 11),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_swap [Finite G] {p q u0 : G} (hD11 : LocalData11 L U p q u0) :
    ∃ s ∈ Nsub U z, s * z * s⁻¹ = z * u0 ∧ s * p * s⁻¹ ∈ zpowers p := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  have h11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hpL : p ∈ L := Hloc_le_L hD11.p_mem
  have hpN : p ∈ Nsub U z := Hloc_le_N hS hUL hD11.p_mem
  have hpz : p * z = z * p := (hS.z_comm p hpL).symm
  have hzN : z ∈ Nsub U z := V_le_N z_mem_V
  have hPN : zpowers p ≤ Nsub U z := by rw [zpowers_le]; exact hpN
  have hcard : Nat.card ((zpowers p).subgroupOf (Nsub U z)) =
      11 ^ (Nat.card (Nsub U z)).factorization 11 := by
    rw [factorization_N hS hD htrans, pow_one,
      Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv, Nat.card_zpowers, hD11.p_order]
  let PS : Sylow 11 (Nsub U z) := Sylow.ofCard _ hcard
  have hPS : (PS : Subgroup (Nsub U z)) = (zpowers p).subgroupOf (Nsub U z) := rfl
  obtain ⟨n, hnN, hnz⟩ := htrans u0 hD11.u0_mem
  have hPmem : ∀ h : Nsub U z, h ∈ (PS : Subgroup (Nsub U z)) → ∃ k : ℤ, p ^ k = (h : G) := by
    intro h hh
    rw [hPS] at hh
    exact mem_zpowers_iff.1 hh
  have hx : (⟨z, hzN⟩ : Nsub U z) ∈ centralizer ((PS : Subgroup (Nsub U z)) : Set (Nsub U z)) := by
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, hk⟩ := hPmem h hh
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hk]
    exact (Commute.zpow_left (show Commute p z from hpz) k).eq
  have hu0z : Commute p (z * u0) := by
    have h1 : Commute p z := hpz
    have h2 : Commute p u0 := hD11.u0_fix
    exact h1.mul_right h2
  have hy : (⟨n⁻¹, inv_mem hnN⟩ : Nsub U z)⁻¹ * ⟨z, hzN⟩ * ⟨n⁻¹, inv_mem hnN⟩ ∈
      centralizer ((PS : Subgroup (Nsub U z)) : Set (Nsub U z)) := by
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, hk⟩ := hPmem h hh
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [hnz, ← hk]
    exact (Commute.zpow_left hu0z k).eq
  obtain ⟨n', hn'norm, heq⟩ :=
    PS.conj_eq_normalizer_conj_of_mem_centralizer ⟨z, hzN⟩ ⟨n⁻¹, inv_mem hnN⟩ hx hy
  have heq' := congrArg Subtype.val heq
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at heq'
  refine ⟨(n' : G)⁻¹, inv_mem n'.2, ?_, ?_⟩
  · rw [inv_inv, ← heq']
    exact hnz
  · have hn'' : n'⁻¹ ∈ normalizer ((PS : Subgroup (Nsub U z)) : Set (Nsub U z)) :=
      inv_mem hn'norm
    have hp' : (⟨p, hpN⟩ : Nsub U z) ∈ (PS : Subgroup (Nsub U z)) := by
      rw [hPS]; exact mem_subgroupOf.2 (mem_zpowers p)
    have h1 := (mem_normalizer_iff.1 hn'' ⟨p, hpN⟩).1 hp'
    rw [hPS] at h1
    have h2 := mem_subgroupOf.1 h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using h2

omit hS hD htrans in
theorem conj_pow_eq_of_q {p q : G} (hq : q * p * q⁻¹ = p ^ 2) (b : ℕ) :
    q ^ b * p * (q ^ b)⁻¹ = p ^ (2 ^ b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    calc q ^ (b + 1) * p * (q ^ (b + 1))⁻¹ = q * (q ^ b * p * (q ^ b)⁻¹) * q⁻¹ := by
          rw [pow_succ']; group
      _ = q * p ^ (2 ^ b) * q⁻¹ := by rw [ih]
      _ = (q * p * q⁻¹) ^ (2 ^ b) := (conj_pow).symm
      _ = (p ^ 2) ^ (2 ^ b) := by rw [hq]
      _ = p ^ (2 ^ (b + 1)) := by rw [← pow_mul, pow_succ, mul_comm]

theorem false_of_Csub_eq_V [Finite G] {p q u0 : G} (hD11 : LocalData11 L U p q u0)
    (hCV : Csub U z = Vsub U z) : False := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  have hpH := hD11.p_mem
  have hpL : p ∈ L := Hloc_le_L hpH
  have hpN : p ∈ Nsub U z := Hloc_le_N hS hUL hpH
  have hqH := hD11.q_mem
  have hqL : q ∈ L := Hloc_le_L hqH
  have hqN : q ∈ Nsub U z := Hloc_le_N hS hUL hqH
  have hzp : z * p = p * z := hS.z_comm p hpL
  have hzq : z * q = q * z := hS.z_comm q hqL
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hS.z_mul_self
  have hu0U := hD11.u0_mem
  obtain ⟨s, hsN, hsz, hsp⟩ := exists_swap hS hD htrans hD11
  obtain ⟨j, hj⟩ : ∃ j : ℕ, s * p * s⁻¹ = p ^ j := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hsp
    refine ⟨(k % 11).toNat, ?_⟩
    have h := zpow_mod_orderOf p k
    rw [hD11.p_order] at h
    rw [← hk, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    exact_mod_cast h.symm
  have hp1 : p ≠ 1 := by
    intro h1
    have := hD11.p_order
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hp11 : p ^ 11 = 1 := by rw [← hD11.p_order]; exact pow_orderOf_eq_one p
  have hj0 : ¬ 11 ∣ j := by
    intro hd
    obtain ⟨t, rfl⟩ := hd
    apply hp1
    have : s * p * s⁻¹ = 1 := by rw [hj, pow_mul, hp11, one_pow]
    have h2 : p = s⁻¹ * (s * p * s⁻¹) * s := by group
    rw [h2, this]; group
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (2 ^ b * j) % 11 = 1 := by
    have h := (by decide : ∀ x : ZMod 11, x ≠ 0 → ∃ b : Fin 10, (2 : ZMod 11) ^ (b : ℕ) * x = 1)
    have hjz : (j : ZMod 11) ≠ 0 := by
      intro hz
      exact hj0 ((ZMod.natCast_eq_zero_iff j 11).1 hz)
    obtain ⟨b, hb⟩ := h (j : ZMod 11) hjz
    refine ⟨b, ?_⟩
    have : ((2 ^ (b : ℕ) * j : ℕ) : ZMod 11) = ((1 : ℕ) : ZMod 11) := by
      push_cast
      exact hb
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).1 this
    simpa [Nat.ModEq] using h2
  have hpb : p ^ (2 ^ b * j) = p := by
    have h1 : 2 ^ b * j = 11 * ((2 ^ b * j) / 11) + 1 := by
      have := Nat.div_add_mod (2 ^ b * j) 11
      rw [hb] at this
      exact this.symm
    rw [h1, pow_add, pow_mul, hp11, one_pow, one_mul, pow_one]
  have hqb : q ^ b * p * (q ^ b)⁻¹ = p ^ (2 ^ b) := conj_pow_eq_of_q hD11.q_conj b
  have hqbH : q ^ b ∈ Hloc L U := pow_mem hqH b
  have hqbL : q ^ b ∈ L := Hloc_le_L hqbH
  have hqbz : (q ^ b) * z = z * (q ^ b) := (hS.z_comm _ hqbL).symm
  have hqbu : q ^ b * u0 * (q ^ b)⁻¹ = u0 := by
    set w := q ^ b * u0 * (q ^ b)⁻¹ with hw
    have hwU : w ∈ U := Hloc_conj_mem hqbH hu0U
    have hwc : w * p ^ (2 ^ b) = p ^ (2 ^ b) * w := by
      rw [← hqb, hw]
      calc q ^ b * u0 * (q ^ b)⁻¹ * (q ^ b * p * (q ^ b)⁻¹) = q ^ b * (u0 * p) * (q ^ b)⁻¹ := by
            group
        _ = q ^ b * (p * u0) * (q ^ b)⁻¹ := by rw [hD11.u0_fix]
        _ = q ^ b * p * (q ^ b)⁻¹ * (q ^ b * u0 * (q ^ b)⁻¹) := by group
    have hwp : p * w = w * p := by
      have h1 : Commute w (p ^ (2 ^ b)) := hwc
      have h2 : Commute w ((p ^ (2 ^ b)) ^ j) := h1.pow_right j
      rw [← pow_mul, hpb] at h2
      exact h2.symm
    rcases hD11.fix w hwU hwp with h1 | h1
    · exfalso
      apply hD11.u0_ne
      have : u0 = (q ^ b)⁻¹ * w * q ^ b := by rw [hw]; group
      rw [this, h1]; group
    · exact h1
  obtain ⟨s', hs'N, hs'p, hs'z⟩ : ∃ s' ∈ Nsub U z, s' * p * s'⁻¹ = p ∧ s' * z * s'⁻¹ = z * u0 := by
    refine ⟨q ^ b * s, mul_mem (pow_mem hqN b) hsN, ?_, ?_⟩
    · calc q ^ b * s * p * (q ^ b * s)⁻¹ = q ^ b * (s * p * s⁻¹) * (q ^ b)⁻¹ := by group
        _ = q ^ b * p ^ j * (q ^ b)⁻¹ := by rw [hj]
        _ = (q ^ b * p * (q ^ b)⁻¹) ^ j := conj_pow.symm
        _ = (p ^ (2 ^ b)) ^ j := by rw [hqb]
        _ = p := by rw [← pow_mul, hpb]
    · calc q ^ b * s * z * (q ^ b * s)⁻¹ = q ^ b * (s * z * s⁻¹) * (q ^ b)⁻¹ := by group
        _ = q ^ b * (z * u0) * (q ^ b)⁻¹ := by rw [hsz]
        _ = z * (q ^ b * u0 * (q ^ b)⁻¹) := by
          calc q ^ b * (z * u0) * (q ^ b)⁻¹ = (q ^ b * z) * u0 * (q ^ b)⁻¹ := by group
            _ = (z * q ^ b) * u0 * (q ^ b)⁻¹ := by rw [hqbz]
            _ = z * (q ^ b * u0 * (q ^ b)⁻¹) := by group
        _ = z * u0 := by rw [hqbu]
  have hs'pc : s' * p = p * s' := by
    have : s' * p = (s' * p * s'⁻¹) * s' := by group
    rw [this, hs'p]
  have hs'U : ∀ u ∈ U, s' * u * s'⁻¹ ∈ U := fun u hu => conj_U_mem hS hD htrans hs'N hu
  have hs'u0 : s' * u0 * s'⁻¹ = u0 := by
    set w := s' * u0 * s'⁻¹ with hw
    have hwU : w ∈ U := hs'U u0 hu0U
    have hwp : p * w = w * p := by
      calc p * w = (s' * p * s'⁻¹) * w := by rw [hs'p]
        _ = s' * (p * u0) * s'⁻¹ := by rw [hw]; group
        _ = s' * (u0 * p) * s'⁻¹ := by rw [hD11.u0_fix]
        _ = w * (s' * p * s'⁻¹) := by rw [hw]; group
        _ = w * p := by rw [hs'p]
    rcases hD11.fix w hwU hwp with h1 | h1
    · exfalso
      apply hD11.u0_ne
      have : u0 = s'⁻¹ * w * s' := by rw [hw]; group
      rw [this, h1]; group
    · exact h1
  have htN : s' * s' ∈ Nsub U z := mul_mem hs'N hs'N
  have htz : z * (s' * s') = (s' * s') * z := by
    have h1 : s' * z * s'⁻¹ = z * u0 := hs'z
    have h2 : s' * (z * u0) * s'⁻¹ = z * u0 * u0 := by
      calc s' * (z * u0) * s'⁻¹ = (s' * z * s'⁻¹) * (s' * u0 * s'⁻¹) := by group
        _ = z * u0 * u0 := by rw [h1, hs'u0]
    have h3 : z * u0 * u0 = z := by
      calc z * u0 * u0 = z * (u0 * u0) := by group
        _ = z := by rw [hD.U_sq u0 hu0U, mul_one]
    have h4 : (s' * s') * z * (s' * s')⁻¹ = z := by
      calc (s' * s') * z * (s' * s')⁻¹ = s' * (s' * z * s'⁻¹) * s'⁻¹ := by group
        _ = s' * (z * u0) * s'⁻¹ := by rw [h1]
        _ = z := by rw [h2, h3]
    calc z * (s' * s') = ((s' * s') * z * (s' * s')⁻¹) * (s' * s') := by rw [h4]
      _ = (s' * s') * z := by group
  have htp : p * (s' * s') = (s' * s') * p := by
    calc p * (s' * s') = (p * s') * s' := by group
      _ = (s' * p) * s' := by rw [hs'pc]
      _ = s' * (p * s') := by group
      _ = s' * (s' * p) := by rw [hs'pc]
      _ = (s' * s') * p := by group
  obtain ⟨l, hlH, htl⟩ := exists_Hloc_of_mem_N_comm hS hUL htN htz
  have hlp : p * l = l * p := by
    rcases htl with htl | htl
    · rw [← htl]; exact htp
    · have hpl : p * (l * z) = (l * z) * p := by rw [← htl]; exact htp
      have hlz : l * z = z * l := (hS.z_comm l (Hloc_le_L hlH)).symm
      calc p * l = p * (l * z) * z := by
            calc p * l = p * (l * (z * z)) := by rw [hS.z_mul_self, mul_one]
              _ = p * (l * z) * z := by group
        _ = (l * z) * p * z := by rw [hpl]
        _ = l * (z * p) * z := by group
        _ = l * (p * z) * z := by rw [hzp]
        _ = l * p * (z * z) := by group
        _ = l * p := by rw [hS.z_mul_self, mul_one]
  obtain ⟨k, u, huU, hlku⟩ := hD11.cent l hlH hlp
  have hact : ∀ x ∈ U, s' * (s' * x * s'⁻¹) * s'⁻¹ = p ^ k * x * (p ^ k)⁻¹ := by
    intro x hx
    have hzx : z * x * z⁻¹ = x := by
      calc z * x * z⁻¹ = x * z * z⁻¹ := by rw [z_comm_U hS hUL hx]
        _ = x := by group
    have hux : u * x * u⁻¹ = x := by
      have := hD.U_comm u huU x hx
      calc u * x * u⁻¹ = x * u * u⁻¹ := by rw [this]
        _ = x := by group
    have hlx : l * x * l⁻¹ = p ^ k * x * (p ^ k)⁻¹ := by
      rw [hlku]
      calc p ^ k * u * x * (p ^ k * u)⁻¹ = p ^ k * (u * x * u⁻¹) * (p ^ k)⁻¹ := by group
        _ = p ^ k * x * (p ^ k)⁻¹ := by rw [hux]
    have htx : (s' * s') * x * (s' * s')⁻¹ = l * x * l⁻¹ := by
      rcases htl with htl | htl
      · rw [htl]
      · rw [htl]
        calc l * z * x * (l * z)⁻¹ = l * (z * x * z⁻¹) * l⁻¹ := by group
          _ = l * x * l⁻¹ := by rw [hzx]
    calc s' * (s' * x * s'⁻¹) * s'⁻¹ = (s' * s') * x * (s' * s')⁻¹ := by group
      _ = l * x * l⁻¹ := htx
      _ = p ^ k * x * (p ^ k)⁻¹ := hlx
  obtain ⟨m, hm⟩ := hD11.comm s' hs'U hs'pc ⟨k, hact⟩
  have hcN : (p ^ m)⁻¹ * s' ∈ Nsub U z := mul_mem (inv_mem (pow_mem hpN m)) hs'N
  have hcU : ∀ x ∈ U, ((p ^ m)⁻¹ * s') * x = x * ((p ^ m)⁻¹ * s') := by
    intro x hx
    have h1 := hm x hx
    calc (p ^ m)⁻¹ * s' * x = (p ^ m)⁻¹ * (s' * x * s'⁻¹) * s' := by group
      _ = (p ^ m)⁻¹ * (p ^ m * x * (p ^ m)⁻¹) * s' := by rw [h1]
      _ = x * ((p ^ m)⁻¹ * s') := by group
  have hcV : (p ^ m)⁻¹ * s' ∈ Vsub U z := by
    rw [← hCV]
    exact mem_Csub.2 ⟨hcN, hcU⟩
  obtain ⟨w, hwU, hcw⟩ := (mem_Vsub_iff hS hUL).1 hcV
  have hcz : ((p ^ m)⁻¹ * s') * z = z * ((p ^ m)⁻¹ * s') := by
    rcases hcw with hcw | hcw
    · rw [hcw]; exact (z_comm_U hS hUL hwU).symm
    · rw [hcw]
      calc z * w * z = z * (w * z) := by group
        _ = z * (z * w) := by rw [← z_comm_U hS hUL hwU]
  have hcz' : ((p ^ m)⁻¹ * s') * z * ((p ^ m)⁻¹ * s')⁻¹ = z := by
    calc ((p ^ m)⁻¹ * s') * z * ((p ^ m)⁻¹ * s')⁻¹
        = z * ((p ^ m)⁻¹ * s') * ((p ^ m)⁻¹ * s')⁻¹ := by rw [hcz]
      _ = z := by group
  have hs'eq : s' * z * s'⁻¹ = z := by
    have e : s' = p ^ m * ((p ^ m)⁻¹ * s') := by group
    have hpmz : p ^ m * z * (p ^ m)⁻¹ = z := by
      have : Commute (p ^ m) z := Commute.pow_left (show Commute p z from hzp.symm) m
      calc p ^ m * z * (p ^ m)⁻¹ = z * p ^ m * (p ^ m)⁻¹ := by rw [this.eq]
        _ = z := by group
    calc s' * z * s'⁻¹
        = (p ^ m * ((p ^ m)⁻¹ * s')) * z * (p ^ m * ((p ^ m)⁻¹ * s'))⁻¹ := by rw [← e]
      _ = p ^ m * (((p ^ m)⁻¹ * s') * z * ((p ^ m)⁻¹ * s')⁻¹) * (p ^ m)⁻¹ := by group
      _ = p ^ m * z * (p ^ m)⁻¹ := by rw [hcz']
      _ = z := hpmz
  apply hD11.u0_ne
  have h1 : z * u0 = z * 1 := by rw [← hs'z, hs'eq, mul_one]
  exact mul_left_cancel h1

end CFSG.EvenSporadicStandard.J4Std
