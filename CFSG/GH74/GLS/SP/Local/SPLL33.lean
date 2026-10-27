module

public import CFSG.GH74.GLS.SP.Local.SPLL33c
public import CFSG.GH74.GLS.SP.Local.SPLCoprime

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section L33

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem a_Y₀_iff (hA : SPL3Aa D) (y : G) : y ∈ D.Y₀ ↔ D.a * y * D.a⁻¹ ∈ D.Y₀ := by
  rw [← mem_conjBy_iff]
  exact (SetLike.ext_iff.mp hA.a_Y₀ y).symm

omit [Finite G] in
theorem a_conj_C₀ (hA : SPL3Aa D) {g : G} (hg : g ∈ D.C₀) : D.a * g * D.a⁻¹ ∈ D.C₀ := by
  rw [mem_C₀]
  intro y hy
  have hy₁ : D.a⁻¹ * y * D.a ∈ D.Y₀ := by
    rw [a_Y₀_iff D hA]
    have : D.a * (D.a⁻¹ * y * D.a) * D.a⁻¹ = y := by group
    rw [this]; exact hy
  have h := (mem_C₀ D).mp hg _ hy₁
  calc y * (D.a * g * D.a⁻¹) = D.a * ((D.a⁻¹ * y * D.a) * g) * D.a⁻¹ := by group
    _ = D.a * (g * (D.a⁻¹ * y * D.a)) * D.a⁻¹ := by rw [h]
    _ = (D.a * g * D.a⁻¹) * y := by group

omit [Finite G] in
theorem a_conj_C₀' (hA : SPL3Aa D) {g : G} (hg : g ∈ D.C₀) : D.a⁻¹ * g * D.a ∈ D.C₀ := by
  rw [mem_C₀]
  intro y hy
  have hy₁ : D.a * y * D.a⁻¹ ∈ D.Y₀ := (a_Y₀_iff D hA y).mp hy
  have h := (mem_C₀ D).mp hg _ hy₁
  calc y * (D.a⁻¹ * g * D.a) = D.a⁻¹ * ((D.a * y * D.a⁻¹) * g) * D.a := by group
    _ = D.a⁻¹ * (g * (D.a * y * D.a⁻¹)) * D.a := by rw [h]
    _ = (D.a⁻¹ * g * D.a) * y := by group

omit [Finite G] in
theorem a_conj_t (hA : SPL3Aa D) : D.a * D.t * D.a⁻¹ = D.t := by
  have hat : D.a * D.t = D.t * D.a := mem_centralizer_singleton_iff.mp hA.a_mem
  rw [hat]; group

omit [Finite G] in
theorem a_conj_zt (hs : SPLSetup D.toSPLNot0) (hA : SPL3Aa D) : D.a * (D.z * D.t) * D.a⁻¹ = D.z := by
  have htt := t_mul_t D hs
  calc D.a * (D.z * D.t) * D.a⁻¹ = (D.a * D.z * D.a⁻¹) * (D.a * D.t * D.a⁻¹) := by group
    _ = (D.z * D.t) * D.t := by rw [a_z_conj D hs hA, a_conj_t D hA]
    _ = D.z := by
      calc (D.z * D.t) * D.t = D.z * (D.t * D.t) := by group
        _ = D.z := by rw [htt]; group

theorem cen_z_odd_Y₀ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) {c : G}
    (hc0 : c ∈ D.C₀) (hcz : c * D.z = D.z * c) (hodd : Odd (orderOf c)) : c ∈ D.X := by
  have htt := t_mul_t D hs
  refine cen_z_odd D hs h1 h3 hcz hodd (fun a₁ ha₁ => ?_) (fun b hb => ?_)
  · refine ⟨D.t * a₁ * D.t⁻¹, t_mem_X₂ D hs ha₁, ?_⟩
    exact ((mem_C₀ D).mp hc0 _ (diag_mem_Y₀ D hs h3 ha₁)).symm
  · have ha₁ : D.t * b * D.t⁻¹ ∈ D.X₁ := t_mem_X₁ D hb
    have e : D.t * (D.t * b * D.t⁻¹) * D.t⁻¹ = b := by
      calc D.t * (D.t * b * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * b * (D.t * D.t)⁻¹ := by group
        _ = b := by rw [htt]; group
    refine ⟨D.t * b * D.t⁻¹, ha₁, ?_⟩
    have hy := diag_mem_Y₀ D hs h3 ha₁
    rw [e] at hy
    exact ((mem_C₀ D).mp hc0 _ hy).symm

theorem l33_core (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hc : SPL2Ct D.toSPLNot2)
    (h3 : SPL3X D) (hA : SPL3Aa D) : ∀ x ∈ D.X, ∀ y ∈ D.X₃, x * y = y * x := by
  classical
  obtain ⟨V, hVC, hVn, hVodd, hNV, hVall, hVT⟩ := exists_V₀ D hs hc h3
  have htt := t_mul_t D hs
  have hzz := z_mul_z D hs
  have hzt := z_comm_t D hs
  have hpodd : Odd D.p := hs.prime.odd_of_ne_two hs.p_ne_two
  have : Fact D.p.Prime := ⟨hs.prime⟩
  have hVel : ∀ v ∈ V, Odd (orderOf v) := fun v hv =>
    hVodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard V hv)
  have hzV : ∀ v ∈ V, D.z * v * D.z⁻¹ ∈ V := fun v hv => hVn D.z (z_mem_C₀ D hs h3) v hv
  have htV : ∀ v ∈ V, D.t * v * D.t⁻¹ ∈ V := fun v hv => hVn D.t (t_mem_C₀ D) v hv
  have hVa : ∀ v ∈ V, D.a * v * D.a⁻¹ ∈ V := fun v hv =>
    hVall _ (a_conj_C₀ D hA (hVC hv)) (by rw [orderOf_conj']; exact hVel v hv)
  have hVa' : ∀ v ∈ V, D.a⁻¹ * v * D.a ∈ V := fun v hv =>
    hVall _ (a_conj_C₀' D hA (hVC hv)) (by
      have := orderOf_conj' D.a⁻¹ v
      simp only [inv_inv] at this
      rw [this]; exact hVel v hv)
  have hXodd : ∀ x ∈ D.X, Odd (orderOf x) := fun x hx =>
    hpodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one (X_exp D hs h3 x hx))
  have hXV : D.X ≤ V := fun x hx => hVall x (X_le_C₀ D hs h3 hx) (hXodd x hx)
  have hX'V : conjBy D.a D.X ≤ V := by
    intro x hx
    have hx₀ : D.a * x * D.a⁻¹ ∈ D.X := mem_conjBy_iff.mp hx
    have := hVa' _ (hXV hx₀)
    have e : D.a⁻¹ * (D.a * x * D.a⁻¹) * D.a = x := by group
    rwa [e] at this
  have hXp : IsPGroup D.p ↥D.X := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (X_exp D hs h3 g g.2)⟩
  have hX'exp : ∀ x ∈ conjBy D.a D.X, x ^ D.p = 1 := by
    intro x hx
    have hx₀ : D.a * x * D.a⁻¹ ∈ D.X := mem_conjBy_iff.mp hx
    have h := X_exp D hs h3 _ hx₀
    rw [conj_pow] at h
    calc x ^ D.p = D.a⁻¹ * (D.a * x ^ D.p * D.a⁻¹) * D.a := by group
      _ = 1 := by rw [h]; group
  have hX'p : IsPGroup D.p ↥(conjBy D.a D.X) := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hX'exp g g.2)⟩
  have hXz : ∀ x ∈ D.X, D.z * x * D.z⁻¹ ∈ D.X := by
    intro x hx
    have := z_cen_K D hs x (X_le_K' D hs h3 hx)
    have e : D.z * x * D.z⁻¹ = x := by rw [this]; group
    rw [e]; exact hx
  have hXt : ∀ x ∈ D.X, D.t * x * D.t⁻¹ ∈ D.X := by
    intro x hx
    obtain ⟨a₁, ha₁, b, hb, rfl⟩ := mem_sup_of_commute (X₁_X₂_comm D hs h3) hx
    have e : D.t * (a₁ * b) * D.t⁻¹ = (D.t * a₁ * D.t⁻¹) * (D.t * b * D.t⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (t_mem_X₂ D hs ha₁))
      (Subgroup.mem_sup_left (t_mem_X₁ D hb))
  have hX'fix : ∀ x ∈ conjBy D.a D.X, (D.z * D.t) * x = x * (D.z * D.t) := by
    intro x hx
    obtain ⟨x₀, hx₀def⟩ : ∃ x₀, x₀ = D.a * x * D.a⁻¹ := ⟨_, rfl⟩
    have hx₀X : x₀ ∈ D.X := by rw [hx₀def]; exact mem_conjBy_iff.mp hx
    have hz0 : D.z * x₀ = x₀ * D.z := z_cen_K D hs _ (X_le_K' D hs h3 hx₀X)
    have hzt' : D.a * (D.z * D.t) * D.a⁻¹ = D.z := a_conj_zt D hs hA
    have hxx : x = D.a⁻¹ * x₀ * D.a := by rw [hx₀def]; group
    have hzt'' : D.z * D.t = D.a⁻¹ * D.z * D.a := by
      calc D.z * D.t = D.a⁻¹ * (D.a * (D.z * D.t) * D.a⁻¹) * D.a := by group
        _ = D.a⁻¹ * D.z * D.a := by rw [hzt']
    calc (D.z * D.t) * x = (D.a⁻¹ * D.z * D.a) * (D.a⁻¹ * x₀ * D.a) := by rw [← hzt'', ← hxx]
      _ = D.a⁻¹ * (D.z * x₀) * D.a := by group
      _ = D.a⁻¹ * (x₀ * D.z) * D.a := by rw [hz0]
      _ = (D.a⁻¹ * x₀ * D.a) * (D.a⁻¹ * D.z * D.a) := by group
      _ = x * (D.z * D.t) := by rw [← hxx, ← hzt'']
  have hfixzt : ∀ v ∈ V, (D.z * D.t) * v = v * (D.z * D.t) → v ∈ conjBy D.a D.X := by
    intro v hv hcomm
    have hv' : D.a * v * D.a⁻¹ ∈ V := hVa v hv
    have hzt' : D.a * (D.z * D.t) * D.a⁻¹ = D.z := a_conj_zt D hs hA
    have hcz : (D.a * v * D.a⁻¹) * D.z = D.z * (D.a * v * D.a⁻¹) := by
      calc (D.a * v * D.a⁻¹) * D.z = (D.a * v * D.a⁻¹) * (D.a * (D.z * D.t) * D.a⁻¹) := by rw [hzt']
        _ = D.a * (v * (D.z * D.t)) * D.a⁻¹ := by group
        _ = D.a * ((D.z * D.t) * v) * D.a⁻¹ := by rw [hcomm]
        _ = (D.a * (D.z * D.t) * D.a⁻¹) * (D.a * v * D.a⁻¹) := by group
        _ = D.z * (D.a * v * D.a⁻¹) := by rw [hzt']
    have hX := cen_z_odd_Y₀ D hs h1 h3 (hVC hv') hcz (hVel _ hv')
    exact mem_conjBy_iff.mpr hX
  obtain ⟨P, hPV, hPp, hXP, hX'P, hzP, htP⟩ :=
    exists_pgroup_containing_fixed_points V hVodd D.z D.t hzz htt hzt hzV htV D.p hs.prime D.X
      (conjBy D.a D.X) hXV hX'V hXp hX'p hXz hXt
      (fun x hx => hX'fix x hx) hfixzt
  have hPC : P ≤ D.C₀ := hPV.trans hVC
  have hPodd : Odd (Nat.card ↥P) := by
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn]; exact hpodd.pow
  have hY₀P : D.Y₀ ≤ P := (Y₀_le_X D).trans hXP
  have hYc : ∀ y ∈ D.Y₀, ∀ x ∈ P, y * x = x * y := fun y hy x hx => (mem_C₀ D).mp (hPC hx) y hy
  have hfix : ∀ v ∈ P, D.t * v = v * D.t → v ∈ D.Y₀ := by
    intro v hvP htv
    have hvV : v ∈ V := hPV hvP
    have hvC : v ∈ D.C₀ := hVC hvV
    have hvCt : v ∈ D.Ct := mem_centralizer_singleton_iff.mpr htv.symm
    obtain ⟨y, hy, a₀, ha₀, s, hsT, hdec⟩ :=
      Q_decomp D hs hc h3 hvCt (fun y hy => ((mem_C₀ D).mp hvC y hy).symm)
    have hyaV : y * a₀ ∈ V :=
      hNV (Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right ha₀))
    have hsV : s ∈ V := by
      have : s = (y * a₀)⁻¹ * v := by rw [hdec]; group
      rw [this]; exact V.mul_mem (V.inv_mem hyaV) hvV
    have hs1 : s = 1 := eq_one_of_odd_of_mem_two_group (T0_pgroup D hs hc) hsT (hVel s hsV)
    have hv : v = y * a₀ := by rw [hdec, hs1]; group
    obtain ⟨k, hk⟩ := hPp ⟨v, hvP⟩
    have hk' : v ^ (D.p ^ k) = 1 := congrArg Subtype.val hk
    have hcomm : Commute y a₀ := Y₀_A_comm D hs hc h3 y hy a₀ ha₀
    have h2 : y ^ (D.p ^ k) * a₀ ^ (D.p ^ k) = 1 := by
      rw [← hcomm.mul_pow, ← hv]; exact hk'
    have hmemY : a₀ ^ (D.p ^ k) ∈ D.Y₀ := by
      have : a₀ ^ (D.p ^ k) = (y ^ (D.p ^ k))⁻¹ := eq_inv_of_mul_eq_one_right h2
      rw [this]; exact D.Y₀.inv_mem (D.Y₀.pow_mem hy _)
    have hmemA : a₀ ^ (D.p ^ k) ∈ D.A := D.A.pow_mem ha₀ _
    have hbot : a₀ ^ (D.p ^ k) ∈ D.A ⊓ D.I := ⟨hmemA, Y₀_le_I D hs hc h3 hmemY⟩
    rw [hc.AI_inf] at hbot
    have ha1 : a₀ ^ (D.p ^ k) = 1 := Subgroup.mem_bot.mp hbot
    have hord1 : orderOf a₀ ∣ D.p ^ k := orderOf_dvd_of_pow_eq_one ha1
    have hord2 : orderOf a₀ ∣ D.e := by
      have := Subgroup.orderOf_dvd_natCard D.A ha₀
      rwa [hc.A_card] at this
    have hcop : Nat.Coprime D.e (D.p ^ k) := (e_coprime D hs).pow_right k
    have hord : orderOf a₀ ∣ Nat.gcd D.e (D.p ^ k) := Nat.dvd_gcd hord2 hord1
    rw [hcop.gcd_eq_one] at hord
    have ha₀1 : a₀ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
    rw [hv, ha₀1, mul_one]
    exact hy
  have hcommP := commutator_le_of_fixedPointFree P D.Y₀ hPodd hY₀P hYc D.t htt htP hfix
  intro x hx y hy
  have hxP : x ∈ P := hXP hx
  have hyP : y ∈ P := by
    refine hX'P ?_
    rw [SPLNot3.X₃, mem_conjBy_iff] at hy
    exact mem_conjBy_iff.mpr (h3.Y₁_le hy)
  have hzY : ∀ y ∈ D.Y₀, D.z * y * D.z⁻¹ = y := by
    intro y hy
    have := z_cen_K D hs y (X_le_K' D hs h3 (Y₀_le_X D hy))
    rw [this]; group
  have hzx : D.z * x * D.z⁻¹ = x := by
    have := z_cen_K D hs x (X_le_K' D hs h3 hx)
    rw [this]; group
  exact commute_of_inverted P D.Y₀ hPodd hcommP hYc D.z hzP hzY x y hxP hyP hzx
    (z_inv_X₃ D hs h3 hA y hy)

end L33

theorem splInL33 : SPLInL33 := by
  intro G _ _ _ D hs h1 hc _ h3 hA
  exact l33_core D hs h1 hc h3 hA

end CFSG.GH74.GLS.SP.Local
