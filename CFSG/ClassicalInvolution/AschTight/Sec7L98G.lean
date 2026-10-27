module

public import CFSG.ClassicalInvolution.AschTight.Sec7L98F

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem odd_orderOf_pow_four_pow [Finite G] (g : G) : Odd (orderOf (g ^ 4 ^ orderOf g)) := by
  obtain ⟨e, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have he : e ≤ 2 * orderOf g := by
    have h1 : 2 ^ e ≤ orderOf g := by
      rw [hN]
      exact Nat.le_mul_of_pos_right _ hm.pos
    have h2 := Nat.lt_two_pow_self (n := e)
    omega
  have h1 : (g ^ 4 ^ orderOf g) ^ m = 1 := by
    rw [← pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.mp
    have h4 : (4 : ℕ) ^ orderOf g = 2 ^ (2 * orderOf g) := by rw [pow_mul]; norm_num
    rw [h4]
    nth_rewrite 1 [hN]
    exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 he) m
  exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)

theorem conj_pow_three_mul_add_one {ρ a : G} (h3 : ρ ^ 3 * a * (ρ ^ 3)⁻¹ = a) (m : ℕ) :
    ρ ^ (3 * m + 1) * a * (ρ ^ (3 * m + 1))⁻¹ = ρ * a * ρ⁻¹ := by
  have key : ∀ m : ℕ, ρ ^ (3 * m) * a * (ρ ^ (3 * m))⁻¹ = a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 3 * (m + 1) = 3 * m + 3 by ring, pow_add]
      calc ρ ^ (3 * m) * ρ ^ 3 * a * (ρ ^ (3 * m) * ρ ^ 3)⁻¹
          = ρ ^ (3 * m) * (ρ ^ 3 * a * (ρ ^ 3)⁻¹) * (ρ ^ (3 * m))⁻¹ := by group
        _ = a := by rw [h3, ih]
  rw [pow_succ']
  calc ρ * ρ ^ (3 * m) * a * (ρ * ρ ^ (3 * m))⁻¹
      = ρ * (ρ ^ (3 * m) * a * (ρ ^ (3 * m))⁻¹) * ρ⁻¹ := by group
    _ = ρ * a * ρ⁻¹ := by rw [key m]

theorem four_pow_eq (N : ℕ) : 4 ^ N = 3 * (4 ^ N / 3) + 1 := by
  have h1 : 4 ^ N % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 := Nat.div_add_mod (4 ^ N) 3
  omega

namespace Tor98

variable {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {z j u v : G} {R R' T : Subgroup G}
  (t : Tor98 Ω K J K' z j u v R R' T)
include t

theorem exists_b [Finite G] {r t₀ : G} (hr : r ∈ R) (hru : r ∉ Subgroup.zpowers u) (ht : t₀ ∈ T)
    (htv : t₀ ∉ Subgroup.zpowers v) :
    Odd (orderOf ((r * t₀) ^ 4 ^ orderOf (r * t₀))) ∧
      (r * t₀) ^ 4 ^ orderOf (r * t₀) * z * ((r * t₀) ^ 4 ^ orderOf (r * t₀))⁻¹ = j ∧
      (r * t₀) ^ 4 ^ orderOf (r * t₀) * j * ((r * t₀) ^ 4 ^ orderOf (r * t₀))⁻¹ = z * j ∧
      (r * t₀) ^ 4 ^ orderOf (r * t₀) * (z * j) * ((r * t₀) ^ 4 ^ orderOf (r * t₀))⁻¹ = z := by
  obtain ⟨h1, h2, h3⟩ := t.rho_conj hr hru ht htv
  set ρ := r * t₀ with hρ
  have hz3 : ρ ^ 3 * z * (ρ ^ 3)⁻¹ = z := by
    calc ρ ^ 3 * z * (ρ ^ 3)⁻¹ = ρ * (ρ * (ρ * z * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ := by
          rw [pow_three]; group
      _ = z := by rw [h1, h2, h3]
  have hj3 : ρ ^ 3 * j * (ρ ^ 3)⁻¹ = j := by
    calc ρ ^ 3 * j * (ρ ^ 3)⁻¹ = ρ * (ρ * (ρ * j * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ := by
          rw [pow_three]; group
      _ = j := by rw [h2, h3, h1]
  have hzj3 : ρ ^ 3 * (z * j) * (ρ ^ 3)⁻¹ = z * j := by
    calc ρ ^ 3 * (z * j) * (ρ ^ 3)⁻¹ = (ρ ^ 3 * z * (ρ ^ 3)⁻¹) * (ρ ^ 3 * j * (ρ ^ 3)⁻¹) := by
          group
      _ = z * j := by rw [hz3, hj3]
  have e := four_pow_eq (orderOf ρ)
  refine ⟨odd_orderOf_pow_four_pow ρ, ?_, ?_, ?_⟩
  · rw [e, conj_pow_three_mul_add_one hz3]; exact h1
  · rw [e, conj_pow_three_mul_add_one hj3]; exact h2
  · rw [e, conj_pow_three_mul_add_one hzj3]; exact h3

theorem fpf [Finite G] {b : G} (hbz : b * z * b⁻¹ = j) (hbj : b * j * b⁻¹ = z * j)
    (hbzj : b * (z * j) * b⁻¹ = z) :
    ∀ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, b * w * b⁻¹ = w → w = 1 := by
  intro w hw hbw
  by_contra hw1
  obtain ⟨n, hn⟩ := t.UV_isPGroup ⟨w, hw⟩
  have hord : orderOf w ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  obtain ⟨y, hy, hy2, hy1⟩ := AscL62.exists_involution_pow hw1 hi
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hyfix : b * w ^ k * b⁻¹ = w ^ k := by rw [← conj_zpow, hbw]
  have hyUV : w ^ k ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v := Subgroup.zpow_mem _ hw k
  have hyZ := t.mem_Z_of_sq hyUV hy2
  rcases (Sec71.mem_closure_pair_iff t.hz.sq t.hj.sq t.zj_comm).mp hyZ with h | h | h | h
  · exact hy1 h
  · rw [h, hbz] at hyfix
    exact t.hzj hyfix.symm
  · rw [h, hbj] at hyfix
    apply t.hz.ne_one
    calc z = z * j * j⁻¹ := by group
      _ = j * j⁻¹ := by rw [hyfix]
      _ = 1 := mul_inv_cancel j
  · rw [h, hbzj] at hyfix
    apply t.hj.ne_one
    calc j = z⁻¹ * (z * j) := by group
      _ = z⁻¹ * z := by rw [← hyfix]
      _ = 1 := inv_mul_cancel z

end Tor98

namespace Cfg98

variable {Ω : Set (Subgroup G)} {K J K' X P : Subgroup G} {z j : G} {S : Sylow 2 G}
  {W : Subgroup G} (c : Cfg98 Ω K J K' X P z j S W)
include c

theorem card_U_eq_V [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T) :
    Nat.card (Subgroup.zpowers u) = Nat.card (Subgroup.zpowers v) := by
  have h1 := t.card_sylow_eq t.hK t.hU t.hUK t.hR
  have h2 := t.card_sylow_eq t.hJ t.hV t.hVJ t.hT
  have h3 := Sec6Gen.natCard_isSylow2In_eq c.hΩ c.hK c.hJ t.hR t.hT
  omega

theorem part2 [Finite G] {u v : G} {T : Subgroup G}
    (t : Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T)
    (hu : Subgroup.zpowers u = K ⊓ W) (hv : Subgroup.zpowers v = J ⊓ W)
    (hXU : ∀ x ∈ X, ∀ w ∈ W ⊓ K, x * w = w * x) :
    ∀ x ∈ X, ∀ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, x * w * x⁻¹ = w := by
  obtain ⟨r, hrR, hru⟩ := t.exists_r
  obtain ⟨t₀, ht₀T, ht₀v⟩ := t.exists_t
  obtain ⟨hbo, hbz, hbj, hbzj⟩ := t.exists_b hrR hru ht₀T ht₀v
  set b := (r * t₀) ^ 4 ^ orderOf (r * t₀) with hb
  have hρL : r * t₀ ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j :=
    Subgroup.mul_mem _ (c.R_le_L t hrR) (c.T_le_L t ht₀T)
  have hbL : b ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j := Subgroup.pow_mem _ hρL _
  have hbY : b ∈ pairNormalizers K J z j := c.L_le_Y t hu hv hbL
  have hbN := L98_le_normalizer Ω _ z j hbL
  intro x hx
  have hxL := c.X_le_N_L t hv hx
  have hxZ := c.X_le_C_Z t hx
  have hxN := c.X_le_N_UV t hv hx
  set cc := x⁻¹ * b⁻¹ * x * b with hcc
  have hcL : cc ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j := by
    have h1 : x⁻¹ * b⁻¹ * x⁻¹⁻¹ ∈ L98 Ω (Subgroup.zpowers u ⊔ Subgroup.zpowers v) z j :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxL) b⁻¹).mp (Subgroup.inv_mem _ hbL)
    rw [inv_inv] at h1
    exact Subgroup.mul_mem _ h1 hbL
  have hcZ : cc ∈
      Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) := by
    have hbN' : b⁻¹ ∈ Subgroup.normalizer
        ((Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) :
          Subgroup G) : Set G) :=
      normalizer_le_normalizer_centralizer _ (Subgroup.inv_mem _ (t.hYZ hbY))
    have h1 : b⁻¹ * x * b⁻¹⁻¹ ∈
        Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hbN' x).mp hxZ
    rw [inv_inv] at h1
    rw [hcc, show x⁻¹ * b⁻¹ * x * b = x⁻¹ * (b⁻¹ * x * b) by group]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxZ) h1
  have hcN : cc ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) :=
    L98_le_normalizer Ω _ z j hcL
  have hxc : b⁻¹ * x * b = x * cc := by rw [hcc]; group
  have hctriv : ∀ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, cc * w * cc⁻¹ = w := by
    rcases t.sign (c.L_le_Y t hu hv hcL) hcZ hcN with h | h
    · exact h
    · exfalso
      have h1 := eq_inv_of_conj_mul hbN hbo hxc h u (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
      apply t.u_sq_ne
      calc u * u = u * u⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel u
  have hxU : ∀ w ∈ Subgroup.zpowers u, x * w * x⁻¹ = w := by
    intro w hw
    have hw' : w ∈ W ⊓ K := by
      rw [inf_comm, ← hu]
      exact hw
    rw [hXU x hx w hw']
    group
  have hxUb : ∀ w ∈ Subgroup.zpowers u, x * (b * w * b⁻¹) * x⁻¹ = b * w * b⁻¹ := by
    intro w hw
    have hwUV : w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v := Subgroup.mem_sup_left hw
    calc x * (b * w * b⁻¹) * x⁻¹ = b * ((b⁻¹ * x * b) * w * (b⁻¹ * x * b)⁻¹) * b⁻¹ := by group
      _ = b * (x * (cc * w * cc⁻¹) * x⁻¹) * b⁻¹ := by rw [hxc]; group
      _ = b * w * b⁻¹ := by rw [hctriv w hwUV, hxU w hw]
  have hUb : conjSub b (Subgroup.zpowers u) ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
    have := conjSub_mono (n := b) (le_sup_left : Subgroup.zpowers u ≤
      Subgroup.zpowers u ⊔ Subgroup.zpowers v)
    rwa [mem_normalizer_iff_conjSub_eq.mp hbN] at this
  have hinf : Subgroup.zpowers u ⊓ conjSub b (Subgroup.zpowers u) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    by_contra hy1
    have h2 : IsPGroup 2 ↥(Subgroup.zpowers u ⊓ conjSub b (Subgroup.zpowers u)) :=
      t.U_data.1.to_le inf_le_left
    have hcard : 2 ≤ Nat.card ↥(Subgroup.zpowers u ⊓ conjSub b (Subgroup.zpowers u)) := by
      have h1 : 1 < Nat.card ↥(Subgroup.zpowers u ⊓ conjSub b (Subgroup.zpowers u)) := by
        rw [Subgroup.one_lt_card_iff_ne_bot]
        intro hb'
        apply hy1
        rw [hb'] at hy
        exact hy
      omega
    have hzm := t.hz.mem_of_le (inf_le_left.trans t.hUK) h2 hcard
    have hjb := t.hz.conj b
    rw [hbz] at hjb
    have hjm := hjb.mem_of_le (inf_le_right.trans (conjSub_mono t.hUK)) h2 hcard
    have hz2 := (hjb.unique z (inf_le_right.trans (conjSub_mono t.hUK) hzm) t.hz.sq).resolve_left
      t.hz.ne_one
    exact t.hzj hz2
  have hcomm : conjSub b (Subgroup.zpowers u) ≤
      Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) := fun y hy =>
    (Subgroup.centralizer_le_normalizer (Subgroup.zpowers u : Set G))
      (Subgroup.mem_centralizer_iff.mpr fun a ha =>
        t.UV_comm a (Subgroup.mem_sup_left ha) y (hUb hy))
  have e1 := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer hcomm
  have e2 := Sec6Gen.card_sup_mul_card_inf_of_le_normalizer t.v_le_N_u
  rw [sup_comm, inf_comm, hinf] at e1
  rw [sup_comm, inf_comm, t.U_inf_V] at e2
  have hcb : Nat.card ↥(conjSub b (Subgroup.zpowers u)) = Nat.card (Subgroup.zpowers u) :=
    natCard_conjSub _ b
  have heq : Subgroup.zpowers u ⊔ conjSub b (Subgroup.zpowers u) =
      Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hUb) ?_
    have h1 : Nat.card ↥(Subgroup.zpowers u ⊔ conjSub b (Subgroup.zpowers u)) =
        Nat.card (Subgroup.zpowers u) * Nat.card (Subgroup.zpowers u) := by
      simpa [hcb, mul_comm] using e1
    have h2 : Nat.card ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) =
        Nat.card (Subgroup.zpowers u) * Nat.card (Subgroup.zpowers v) := by
      simpa [mul_comm] using e2
    rw [h1, h2, c.card_U_eq_V t]
  have hle : Subgroup.zpowers u ⊔ conjSub b (Subgroup.zpowers u) ≤
      Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun w hw => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have := hxU w hw
      calc w * x = x * w * x⁻¹ * x := by rw [this]
        _ = x * w := by group
    · obtain ⟨w, hw, rfl⟩ := hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hxUb w hw
      change (MulAut.conj b) w * x = x * (MulAut.conj b) w
      simp only [MulAut.conj_apply]
      calc b * w * b⁻¹ * x = x * (b * w * b⁻¹) * x⁻¹ * x := by rw [this]
        _ = x * (b * w * b⁻¹) := by group
  intro w hw
  rw [← heq] at hw
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  calc x * w * x⁻¹ = w * x * x⁻¹ := by rw [h1]
    _ = w := by group

end Cfg98

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
