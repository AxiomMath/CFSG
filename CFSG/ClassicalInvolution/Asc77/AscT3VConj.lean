module

public import CFSG.ClassicalInvolution.Asc77.AscT3VAdj
public import CFSG.ClassicalInvolution.Asc77.AscT3VNine8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Basic

variable {G : Type*} [Group G]

theorem zpow_pow_comm' (g : G) (i : ℤ) (n : ℕ) : (g ^ i) ^ n = (g ^ n) ^ i := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem invol_zpow {y : G} (hy : y * y = 1) (m : ℤ) :
    (Even m → y ^ m = 1) ∧ (Odd m → y ^ m = y) := by
  have h2 : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy
  constructor
  · rintro ⟨r, rfl⟩
    rw [← two_mul, zpow_mul, h2, one_zpow]
  · rintro ⟨r, rfl⟩
    rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem eq_one_of_zpow_odd {y : G} (hy : ∃ m : ℕ, y ^ 2 ^ m = 1) {j : ℤ} (hj : Odd j)
    (h : y ^ j = 1) : y = 1 := by
  obtain ⟨m, hm⟩ := hy
  have h1 : orderOf y ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  obtain ⟨m', -, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : (orderOf y : ℤ) ∣ j := (orderOf_dvd_iff_zpow_eq_one).mpr h
  by_cases hm0 : m' = 0
  · rw [hm0, pow_zero] at hm'
    exact orderOf_eq_one_iff.mp hm'
  · exfalso
    have h3 : (2 : ℤ) ∣ (orderOf y : ℤ) := by
      rw [hm']
      push_cast
      exact dvd_pow_self 2 hm0
    have h4 : (2 : ℤ) ∣ j := h3.trans h2
    exact (Int.not_even_iff_odd.mpr hj) (even_iff_two_dvd.mpr h4)

end Basic

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.v_KJ_bot (d : Std20 p f K K' J S R R' W V z t) :
    ∀ x ∈ W ⊓ K, x ∈ W ⊓ J → x = 1 := by
  intro x hxK hxJ
  by_contra hx1
  have hA : IsPGroup 2 ↥(Subgroup.zpowers x) :=
    S.isPGroup'.to_le ((Subgroup.zpowers_le.mpr hxK.1).trans d.hWS)
  have hcard := Sec6Gen.card_le_two_of_le_inf d.late_hΩ d.late_mem_K d.late_mem_J
    d.late_J_ne_K.symm hA (Subgroup.zpowers_le.mpr hxK.2) (Subgroup.zpowers_le.mpr hxJ.2)
  rw [Nat.card_zpowers] at hcard
  have hord : orderOf x = 2 := by
    have h1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    have h0 : 0 < orderOf x := orderOf_pos x
    omega
  have hx2 : x * x = 1 := by rw [← pow_two, ← hord, pow_orderOf_eq_one]
  have hxz : x = z := (d.viol.hzK.unique x hxK.2 hx2).resolve_left hx1
  have hxt : x = t := (d.viol.hzJ.unique x hxJ.2 hx2).resolve_left hx1
  exact d.late_ne_inv (hxt.symm.trans hxz)

theorem Std20.v_W_gen (d : Std20 p f K K' J S R R' W V z t) {u : G} {k : ℕ}
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1)) :
    ∃ v₀ : G, Subgroup.zpowers v₀ = J ⊓ W ∧ orderOf v₀ = 2 ^ (k + 1) ∧ v₀ ^ 2 ^ k = t ∧
      u ^ 2 ^ k = z ∧ W = Subgroup.zpowers u ⊔ Subgroup.zpowers v₀ ∧ u * v₀ = v₀ * u ∧
      Subgroup.zpowers u ⊓ Subgroup.zpowers v₀ = ⊥ := by
  have hKWU := d.late_KW
  have hJWU := d.late_JW
  have hcyc : IsCyclic ↥(J ⊓ W) := by
    obtain ⟨-, -, -, hc, -⟩ := hJWU
    exact hc
  obtain ⟨v₀, hv₀⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (J ⊓ W)).mp hcyc
  have hcR1 := Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp hKWU d.late_mem_K d.hR
  have hcR2 := Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp hJWU d.late_mem_K d.hR
  have hcK : Nat.card ↥(K ⊓ W) = 2 ^ (k + 1) := by rw [← hu, Nat.card_zpowers, huo]
  have hv₀o : orderOf v₀ = 2 ^ (k + 1) := by
    rw [← Nat.card_zpowers, hv₀]
    omega
  have hu_mem : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have hv_mem : v₀ ∈ J ⊓ W := hv₀ ▸ Subgroup.mem_zpowers v₀
  have hpow2 : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by ring
  have hlt : 2 ^ k < 2 ^ (k + 1) := by
    have : 0 < 2 ^ k := by positivity
    rw [pow_succ]
    omega
  have huz : u ^ 2 ^ k = z := by
    have h2 : (u ^ 2 ^ k) * (u ^ 2 ^ k) = 1 := by
      rw [← pow_add, hpow2, ← huo, pow_orderOf_eq_one]
    have h1 : u ^ 2 ^ k ≠ 1 :=
      pow_ne_one_of_lt_orderOf (by positivity) (by rw [huo]; exact hlt)
    exact (d.viol.hzK.unique _ (K.pow_mem hu_mem.1 _) h2).resolve_left h1
  have hvt : v₀ ^ 2 ^ k = t := by
    have h2 : (v₀ ^ 2 ^ k) * (v₀ ^ 2 ^ k) = 1 := by
      rw [← pow_add, hpow2, ← hv₀o, pow_orderOf_eq_one]
    have h1 : v₀ ^ 2 ^ k ≠ 1 :=
      pow_ne_one_of_lt_orderOf (by positivity) (by rw [hv₀o]; exact hlt)
    exact (d.viol.hzJ.unique _ (J.pow_mem hv_mem.1 _) h2).resolve_left h1
  refine ⟨v₀, hv₀, hv₀o, hvt, huz, ?_, d.late_hWc u hu_mem.2 v₀ hv_mem.2, ?_⟩
  · have := d.late_hW
    rwa [inf_comm W K, inf_comm W J, ← hu, ← hv₀] at this
  · refine Subgroup.eq_bot_iff_forall _ |>.mpr fun x hx => ?_
    have h1 : x ∈ K ⊓ W := hu ▸ hx.1
    have h2 : x ∈ J ⊓ W := hv₀ ▸ hx.2
    exact d.v_KJ_bot x ⟨h1.2, h1.1⟩ ⟨h2.2, h2.1⟩

theorem Std20.v_conj_t (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hat : a * t * a⁻¹ = t)
    {u : G} {k : ℕ} (hk : 2 ≤ k) (hu : Subgroup.zpowers u = K ⊓ W)
    (huo : orderOf u = 2 ^ (k + 1))
    (hact : (∀ x ∈ K ⊓ W, a * x * a⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) ∨
      ∀ x ∈ K ⊓ W, a * x * a⁻¹ = x ^ ((2 : ℤ) ^ k - 1)) :
    ∃ c : G, c * a = a * c ∧ c * z * c⁻¹ = t := by
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  obtain ⟨κ, hκ, hactκ⟩ : ∃ κ : ℤ, (κ = 2 ^ k + 1 ∨ κ = 2 ^ k - 1) ∧
      ∀ x ∈ K ⊓ W, a * x * a⁻¹ = x ^ κ := by
    rcases hact with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  obtain ⟨v₀, hv₀, hv₀o, hv₀t, huz, hWgen, huv₀, hdis⟩ := d.v_W_gen hu huo
  have hc : Commute u v₀ := huv₀
  have hWa : a ∈ Subgroup.normalizer (W : Set G) := d.hWN haS
  have hgz : a * z * a⁻¹ = z := d.late_S_act_z haS
  have hα_u : a * u * a⁻¹ = u ^ κ := hactκ u huKW
  have haK : conjSub a K = K := by
    rcases d.late_conj_K (d.hSz haS) with h | h
    · exact h
    · exfalso
      have hxK' : u ^ κ ∈ K' := by
        have := conj_mem_conjSub (n := a) huKW.1
        rw [h, hα_u] at this
        exact this
      have hxK : u ^ κ ∈ K := K.zpow_mem huKW.1 κ
      have hxW : u ^ κ ∈ W := W.zpow_mem huKW.2 κ
      have hA : IsPGroup 2 ↥(Subgroup.zpowers (u ^ κ)) :=
        S.isPGroup'.to_le ((Subgroup.zpowers_le.mpr hxW).trans d.hWS)
      have hcard := Sec6Gen.card_le_two_of_le_inf d.late_hΩ d.late_mem_K d.late_mem_K'
        d.ne.symm hA (Subgroup.zpowers_le.mpr hxK) (Subgroup.zpowers_le.mpr hxK')
      rw [Nat.card_zpowers] at hcard
      have hsq : (u ^ κ) * (u ^ κ) = 1 := by
        have h0 : 0 < orderOf (u ^ κ) := orderOf_pos _
        have : orderOf (u ^ κ) = 1 ∨ orderOf (u ^ κ) = 2 := by omega
        rcases this with h1 | h1
        · have := orderOf_eq_one_iff.mp h1
          rw [this, one_mul]
        · rw [← pow_two, ← h1, pow_orderOf_eq_one]
      rw [← zpow_add] at hsq
      have hdiv : (orderOf u : ℤ) ∣ κ + κ := (orderOf_dvd_iff_zpow_eq_one).mpr hsq
      rw [huo] at hdiv
      have hN : (4 : ℤ) ≤ 2 ^ k := by
        calc (4 : ℤ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
      obtain ⟨c, hcc⟩ := hdiv
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ] at hcc
      rcases hκ with rfl | rfl
      · rcases le_or_gt c 1 with h1 | h1
        · nlinarith
        · nlinarith
      · rcases le_or_gt c 0 with h1 | h1
        · nlinarith
        · nlinarith
  have hY := d.v_normal_Y haS haK hat
  obtain ⟨x, hxY, hxW, hxodd, hxz, hxexp⟩ := d.v_same_aut_exp haS haK hat
  have hα_v : a * (x * u * x⁻¹) * a⁻¹ = (x * u * x⁻¹) ^ κ := hxexp u huKW.2 κ hα_u
  have hvW : x * u * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hxW u).mp huKW.2
  obtain ⟨i, j, hij⟩ := T3V.mem_sup_zpowers_of_commute huv₀ (hWgen ▸ hvW)
  have hvt : (x * u * x⁻¹) ^ 2 ^ k = t := by rw [conj_pow, huz, hxz]
  have hjodd : Odd j := by
    have h1 : (u ^ i * v₀ ^ j) ^ 2 ^ k = z ^ i * t ^ j := by
      rw [(hc.zpow_zpow i j).mul_pow, zpow_pow_comm', zpow_pow_comm', huz, hv₀t]
    rw [hij, h1] at hvt
    by_contra hjo
    have hje : Even j := Int.not_odd_iff_even.mp hjo
    rw [(invol_zpow ht2 j).1 hje, mul_one] at hvt
    rcases Int.even_or_odd i with hie | hio
    · rw [(invol_zpow hz2 i).1 hie] at hvt
      exact d.viol.hzJ.ne_one hvt.symm
    · rw [(invol_zpow hz2 i).2 hio] at hvt
      exact d.late_ne_inv hvt.symm
  have hv₀α : a * v₀ * a⁻¹ = v₀ ^ κ := by
    have e1 : a * (u ^ i * v₀ ^ j) * a⁻¹ = (u ^ κ) ^ i * (a * v₀ * a⁻¹) ^ j := by
      have : a * (u ^ i * v₀ ^ j) * a⁻¹ = (a * u ^ i * a⁻¹) * (a * v₀ ^ j * a⁻¹) := by group
      rw [this, ← conj_zpow, ← conj_zpow, hα_u]
    have e2 : (u ^ i * v₀ ^ j) ^ κ = (u ^ κ) ^ i * (v₀ ^ κ) ^ j := by
      rw [(hc.zpow_zpow i j).mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul,
        mul_comm i κ, mul_comm j κ]
    rw [hij, e1, e2] at hα_v
    have e3 : (a * v₀ * a⁻¹) ^ j = (v₀ ^ κ) ^ j := mul_left_cancel hα_v
    have hv₀W : v₀ ∈ W := (hv₀ ▸ Subgroup.mem_zpowers v₀ : v₀ ∈ J ⊓ W).2
    have hAW : a * v₀ * a⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hWa v₀).mp hv₀W
    have hBW : v₀ ^ κ ∈ W := W.zpow_mem hv₀W κ
    have hcomm : Commute (a * v₀ * a⁻¹) (v₀ ^ κ)⁻¹ :=
      Commute.inv_right (d.late_hWc _ hAW _ hBW : _ * _ = _ * _)
    have hy1 : (a * v₀ * a⁻¹ * (v₀ ^ κ)⁻¹) ^ j = 1 := by
      rw [hcomm.mul_zpow, inv_zpow, e3, mul_inv_cancel]
    have hyW : a * v₀ * a⁻¹ * (v₀ ^ κ)⁻¹ ∈ W := W.mul_mem hAW (W.inv_mem hBW)
    have hy2 : ∃ m : ℕ, (a * v₀ * a⁻¹ * (v₀ ^ κ)⁻¹) ^ 2 ^ m = 1 := by
      obtain ⟨m, hm⟩ := S.isPGroup' ⟨_, d.hWS hyW⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    have := eq_one_of_zpow_odd hy2 hjodd hy1
    exact mul_inv_eq_one.mp this
  have hα : ∀ w ∈ W, a * w * a⁻¹ = w ^ κ := by
    intro w hw
    obtain ⟨i', j', rfl⟩ := T3V.mem_sup_zpowers_of_commute huv₀ (hWgen ▸ hw)
    have e1 : a * (u ^ i' * v₀ ^ j') * a⁻¹ = (u ^ κ) ^ i' * (v₀ ^ κ) ^ j' := by
      have : a * (u ^ i' * v₀ ^ j') * a⁻¹ = (a * u ^ i' * a⁻¹) * (a * v₀ ^ j' * a⁻¹) := by group
      rw [this, ← conj_zpow, ← conj_zpow, hα_u, hv₀α]
    rw [e1, (hc.zpow_zpow i' j').mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul,
      mul_comm κ i', mul_comm κ j']
  have hy := d.v_Y_odd hY hWa hgz hat hxY hxW hxodd
  obtain ⟨q₂, hq₂, w₂, hw₂, hyq⟩ := d.v_decomp hy
  set D : Subgroup G := pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G) with hD
  have hDle : D ≤ Subgroup.normalizer (W : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer _ hg.2
  have hQN : oddCoreOf D ≤ Subgroup.normalizer (W : Set G) := (oddCoreOf_le_self D).trans hDle
  have hND : ∀ g ∈ Subgroup.normalizer ((pairNormalizers K J z t : Subgroup G) : Set G),
      g ∈ Subgroup.normalizer (W : Set G) → g ∈ Subgroup.normalizer (D : Set G) :=
    fun g hgY hgW => late_mem_normalizer_inf hgY (T3V.mem_normalizer_centralizer hgW)
  have haQ := mem_normalizer_oddCore_of_mem_normalizer (hND a hY hWa)
  have hxQ := mem_normalizer_oddCore_of_mem_normalizer (hND x (Subgroup.le_normalizer hxY) hxW)
  have hsx : ∃ q₂' ∈ oddCoreOf D, ∃ w₂' ∈ W, a * x * a⁻¹ = x * q₂' * w₂' := by
    refine ⟨q₂, hq₂, w₂, hw₂, ?_⟩
    calc a * x * a⁻¹ = x * (x⁻¹ * (a * x * a⁻¹)) := by group
      _ = x * (q₂ * w₂) := by rw [hyq]
      _ = x * q₂ * w₂ := by group
  obtain ⟨q, hqQ, w₁, hw₁W, hfix⟩ := T3V.exists_fixed_coset (W := W) (Q := oddCoreOf D)
    (x := x) (s := a) hxW hWa hQN (oddCoreOf_odd_natCard D)
    (fun q hq hqW => by
      have hodd := odd_orderOf_of_mem_oddCoreOf D hq
      have h2 : ∃ m : ℕ, q ^ 2 ^ m = 1 := by
        obtain ⟨m, hm⟩ := S.isPGroup' ⟨_, d.hWS hqW⟩
        exact ⟨m, by simpa using congrArg Subtype.val hm⟩
      refine eq_one_of_zpow_odd h2 (j := (orderOf q : ℤ)) ?_ ?_
      · exact_mod_cast hodd
      · rw [zpow_natCast, pow_orderOf_eq_one])
    (fun q hq => by
      have := (Subgroup.mem_normalizer_iff.mp hxQ q).mp hq
      simpa using this)
    (fun q hq => by
      have := (Subgroup.mem_normalizer_iff.mp haQ q).mp hq
      simpa using this)
    ha2 hsx
  have hqD : q ∈ D := oddCoreOf_le_self D hqQ
  have hqt : q * t = t * q := (Subgroup.mem_centralizer_iff.mp hqD.2 t d.late_t_mem_W).symm
  set c₁ : G := q * x with hc₁
  have hc₁z : c₁ * z * c₁⁻¹ = t := by
    calc c₁ * z * c₁⁻¹ = q * (x * z * x⁻¹) * q⁻¹ := by rw [hc₁]; group
      _ = q * t * q⁻¹ := by rw [hxz]
      _ = t := by rw [hqt]; group
  have hcoc : w₁ * (a * w₁ * a⁻¹) = 1 := by
    have e : a * (a * c₁ * a⁻¹) * a⁻¹ = c₁ := by
      have : a * (a * c₁ * a⁻¹) * a⁻¹ = (a * a) * c₁ * (a * a)⁻¹ := by group
      rw [this, ha2]
      group
    rw [hfix] at e
    have e' : a * (c₁ * w₁) * a⁻¹ = (a * c₁ * a⁻¹) * (a * w₁ * a⁻¹) := by group
    rw [e', hfix] at e
    have : c₁ * (w₁ * (a * w₁ * a⁻¹)) = c₁ * 1 := by
      rw [mul_one, ← mul_assoc]
      exact e
    exact mul_left_cancel this
  obtain ⟨w, hwW, hw⟩ := T3V.cocycle_cob hk hκ hWgen huv₀ huo hv₀o hdis hα hw₁W hcoc
  refine ⟨c₁ * w, ?_, ?_⟩
  · have e : a * (c₁ * w) * a⁻¹ = c₁ * w := by
      calc a * (c₁ * w) * a⁻¹ = (a * c₁ * a⁻¹) * (a * w * a⁻¹) := by group
        _ = c₁ * (w₁ * (a * w * a⁻¹)) := by rw [hfix]; group
        _ = c₁ * w := by rw [hw]
    calc c₁ * w * a = (a * (c₁ * w) * a⁻¹) * a := by rw [e]
      _ = a * (c₁ * w) := by group
  · have hwz : w * z = z * w := d.late_hWc w hwW z d.late_z_mem_W
    calc c₁ * w * z * (c₁ * w)⁻¹ = c₁ * (w * z * w⁻¹) * c₁⁻¹ := by group
      _ = c₁ * z * c₁⁻¹ := by rw [hwz]; group
      _ = t := hc₁z

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
