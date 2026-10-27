module

public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoTools
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoTwoGroup

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

section Constrained

variable {X : Type*} [Group X] [Finite X] {t u : X}

omit [Finite X] in
theorem SecTwoHyp.z_mem_center_of_R_eq (h : SecTwoHyp X t u) {Q : Subgroup X} (hQn : Q.Normal)
    (hQ2 : IsPGroup 2 Q) (hCQ : centralizer (Q : Set X) ≤ Q) (S : Sylow 2 X)
    (hRS : secTwoR t u = S) : u ^ 2 ∈ center X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQS : Q ≤ secTwoR t u := hRS ▸ hQ2.le_sylow_of_normal S
  have hRQ : secTwoR t u ≤ Q := by
    intro r hr
    apply hCQ
    rw [mem_centralizer_iff]
    intro q hq
    exact h.mul_comm_of_mem_R (hQS hq) hr
  have huQ : u ∈ Q := hRQ SecTwoHyp.u_mem_R
  rw [mem_center_iff]
  intro g
  have hgu : g * u * g⁻¹ ∈ secTwoR t u := hQS (hQn.conj_mem u huQ g)
  rcases h.sq_of_mem_R hgu with h1 | h1
  · exfalso; apply h.z_ne_one
    have : g * u ^ 2 * g⁻¹ = 1 := by rw [← conj_pow, h1]
    calc u ^ 2 = g⁻¹ * (g * u ^ 2 * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group
  · have : g * u ^ 2 * g⁻¹ = u ^ 2 := by rw [← conj_pow, h1]
    calc g * u ^ 2 = g * u ^ 2 * g⁻¹ * g := by group
      _ = u ^ 2 * g := by rw [this]

structure SecTwoCData (h : SecTwoHyp X t u) (Q : Subgroup X) where
  S : Sylow 2 X
  hRS : secTwoR t u ≤ S
  hRS' : secTwoR t u ≠ S
  w : X
  hzW : u ^ 2 ∈ secTwoOmegaZ Q
  hwW : w ∈ secTwoOmegaZ Q
  hw1 : w ≠ 1
  hwz : w ≠ u ^ 2
  hW : ∀ a ∈ secTwoOmegaZ Q, a = 1 ∨ a = u ^ 2 ∨ a = w ∨ a = w * u ^ 2
  g : X
  hg : g * u ^ 2 * g⁻¹ = w
  htw : t * w * t⁻¹ = w * u ^ 2
  v : X
  hvR : v ∈ secTwoR t u
  hvw : v * w = w * v
  hvsq : v ^ 2 = u ^ 2
  hCQt : ∀ c ∈ Q, c * t = t * c → c = 1 ∨ c = v ∨ c = u ^ 2 ∨ c = v * u ^ 2
  x : X
  hx3 : IsPGroup 3 (zpowers x)
  htx : t * x * t⁻¹ = x⁻¹
  hxW : ∀ a ∈ secTwoOmegaZ Q, x * a * x⁻¹ = a → a = 1
  g₂ : X
  hg₂ : g₂ * u ^ 2 * g₂⁻¹ = w * u ^ 2

theorem SecTwoHyp.constrained_setup (h : SecTwoHyp X t u) {Q : Subgroup X} (hQn : Q.Normal)
    (hQ2 : IsPGroup 2 Q) (hCQ : centralizer (Q : Set X) ≤ Q) :
    u ^ 2 ∈ center X ∨ Nonempty (SecTwoCData h Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hRS⟩ := h.exists_sylow_ge
  by_cases hRS' : secTwoR t u = S
  · exact Or.inl (h.z_mem_center_of_R_eq hQn hQ2 hCQ S hRS')
  by_cases hzc : u ^ 2 ∈ center X
  · exact Or.inl hzc
  right
  have hS2 : IsPGroup 2 (S : Subgroup X) := S.isPGroup'
  have hQS : Q ≤ S := hQ2.le_sylow_of_normal S
  have hzQ : u ^ 2 ∈ Q := hCQ (mem_centralizer_iff.mpr fun q hq =>
    (h.z_mem_center hS2 hRS (hQS hq)))
  have hzW : u ^ 2 ∈ secTwoOmegaZ Q :=
    mem_secTwoOmegaZ.mpr ⟨hzQ, fun q hq => h.z_mem_center hS2 hRS (hQS hq), h.z_sq⟩
  rw [mem_center_iff] at hzc
  push Not at hzc
  obtain ⟨g, hgz⟩ := hzc
  have hgz' : g * u ^ 2 * g⁻¹ ≠ u ^ 2 := fun h' => hgz (by
    calc g * u ^ 2 = g * u ^ 2 * g⁻¹ * g := by group
      _ = u ^ 2 * g := by rw [h'])
  set w := g * u ^ 2 * g⁻¹ with hwdef
  have hwW : w ∈ secTwoOmegaZ Q := secTwoOmegaZ_conj hQn hzW g
  have hw1 : w ≠ 1 := fun h' => h.z_ne_one (by
    calc u ^ 2 = g⁻¹ * w * g := by rw [hwdef]; group
      _ = 1 := by rw [h']; group)
  have hWcard : Nat.card (secTwoOmegaZ Q) ≤ 4 :=
    h.card_le_four (fun a ha => secTwoOmegaZ_sq ha) (fun a ha => secTwoOmegaZ_conj hQn ha t)
  have hwzW : w * u ^ 2 ∈ secTwoOmegaZ Q := mul_mem hwW hzW
  have hzinv := h.z_inv
  have hd3 : (1 : X) ≠ w * u ^ 2 := by
    intro h'; apply hgz'
    calc w = w * u ^ 2 * (u ^ 2)⁻¹ := by group
      _ = u ^ 2 := by rw [← h', one_mul, hzinv]
  have hd5 : u ^ 2 ≠ w * u ^ 2 := by
    intro h'; apply hw1
    calc w = w * u ^ 2 * (u ^ 2)⁻¹ := by group
      _ = 1 := by rw [← h', mul_inv_cancel]
  have hd6 : w ≠ w * u ^ 2 := by
    intro h'; apply h.z_ne_one
    calc u ^ 2 = w⁻¹ * (w * u ^ 2) := by group
      _ = 1 := by rw [← h', inv_mul_cancel]
  have hW : ∀ a ∈ secTwoOmegaZ Q, a = 1 ∨ a = u ^ 2 ∨ a = w ∨ a = w * u ^ 2 :=
    fun a ha => secTwo_eq_of_card_le_four hWcard (one_mem _) hzW hwW hwzW h.z_ne_one.symm
      hw1.symm hd3 hgz'.symm hd5 hd6 ha
  have htz : t * u ^ 2 * t⁻¹ = u ^ 2 := by
    rw [(h.commute_tu.pow_right 2).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hconjW : ∀ (k a : X), a ∈ secTwoOmegaZ Q → k * a * k⁻¹ ∈ secTwoOmegaZ Q :=
    fun k a ha => secTwoOmegaZ_conj hQn ha k
  have htwz : t ≠ w * u ^ 2 := by
    intro htw'
    apply hRS'
    have htW' : t ∈ secTwoOmegaZ Q := htw' ▸ hwzW
    have hcent : ∀ k : X, k * t = t * k := by
      intro k
      have hk := hW _ (hconjW k t htW')
      have hkt : k * t * k⁻¹ = t := by
        rcases hk with hk | hk | hk | hk
        · exfalso; apply h.t_ne_one
          calc t = k⁻¹ * (k * t * k⁻¹) * k := by group
            _ = 1 := by rw [hk]; group
        · exfalso; apply h.conj_z_ne_t k⁻¹
          rw [← hk]; group
        · exfalso; apply h.conj_z_ne_t (k⁻¹ * g)
          rw [show k⁻¹ * g * u ^ 2 * (k⁻¹ * g)⁻¹ = k⁻¹ * w * k by rw [hwdef]; group, ← hk]
          group
        · rw [hk, htw']
      calc k * t = k * t * k⁻¹ * k := by group
        _ = t * k := by rw [hkt]
    have hSC : (S : Subgroup X) ≤ centralizer ({t} : Set X) := fun s _ =>
      mem_centralizer_singleton_iff.mpr (hcent s)
    have := h.inf_centralizer_eq hS2 hRS
    rw [inf_eq_left.mpr hSC] at this
    exact this.symm
  have htW : t ∉ secTwoOmegaZ Q := by
    intro htW'
    rcases hW t htW' with h1 | h1 | h1 | h1
    · exact h.t_ne_one h1
    · exact h.sq_ne h1.symm
    · exact h.conj_z_ne_t g h1.symm
    · exact htwz h1
  have htw : t * w * t⁻¹ = w * u ^ 2 := by
    rcases hW _ (hconjW t w hwW) with h1 | h1 | h1 | h1
    · exfalso; apply hw1
      calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
        _ = 1 := by rw [h1]; group
    · exfalso; apply hgz'
      calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
        _ = t⁻¹ * (t * u ^ 2 * t⁻¹) * t := by rw [h1, htz]
        _ = u ^ 2 := by group
    · exfalso
      have hWt : secTwoOmegaZ Q ≤ centralizer ({t} : Set X) := by
        intro a ha
        rw [mem_centralizer_singleton_iff]
        have hta : t * a * t⁻¹ = a := by
          rcases hW a ha with ha' | ha' | ha' | ha'
          · rw [ha']; group
          · rw [ha', htz]
          · rw [ha', h1]
          · rw [ha', show t * (w * u ^ 2) * t⁻¹ = (t * w * t⁻¹) * (t * u ^ 2 * t⁻¹) by group,
              h1, htz]
        calc a * t = t * a * t⁻¹ * t := by rw [hta]
          _ = t * a := by group
      obtain ⟨c, hc, hcR⟩ := secTwo_exists_conj_le h.sylow hWt
        (isPGroup_of_sq_eq_one fun a ha => secTwoOmegaZ_sq ha)
      have hct : c * t * c⁻¹ = t := by
        rw [mem_centralizer_singleton_iff] at hc
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      have himg : ∀ a ∈ secTwoOmegaZ Q, a ≠ 1 →
          c * a * c⁻¹ = u ^ 2 ∨ c * a * c⁻¹ = t * u ^ 2 := by
        intro a ha ha1
        have hsq : (c * a * c⁻¹) ^ 2 = 1 := by rw [conj_pow, secTwoOmegaZ_sq ha]; group
        rcases h.eq_of_mem_R_of_sq_eq_one (hcR a ha) hsq with h2 | h2 | h2 | h2
        · exfalso; apply ha1
          calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
            _ = 1 := by rw [h2]; group
        · exfalso; apply htW
          have : a = t := by
            calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
              _ = c⁻¹ * (c * t * c⁻¹) * c := by rw [h2, hct]
              _ = t := by group
          exact this ▸ ha
        · exact Or.inl h2
        · exact Or.inr h2
      have hinj : ∀ a b : X, c * a * c⁻¹ = c * b * c⁻¹ → a = b := by
        intro a b hab
        calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
          _ = c⁻¹ * (c * b * c⁻¹) * c := by rw [hab]
          _ = b := by group
      rcases himg _ hzW h.z_ne_one with e1 | e1 <;>
        rcases himg _ hwW hw1 with e2 | e2 <;>
        rcases himg _ hwzW hd3.symm with e3 | e3
      · exact hgz' (hinj _ _ (e2.trans e1.symm))
      · exact hgz' (hinj _ _ (e2.trans e1.symm))
      · exact hd5 (hinj _ _ (e1.trans e3.symm))
      · exact hd6 (hinj _ _ (e2.trans e3.symm))
      · exact hd6 (hinj _ _ (e2.trans e3.symm))
      · exact hd5 (hinj _ _ (e1.trans e3.symm))
      · exact hgz' (hinj _ _ (e2.trans e1.symm))
      · exact hgz' (hinj _ _ (e2.trans e1.symm))
    · exact h1
  have huz : u * u ^ 2 * u⁻¹ = u ^ 2 := by
    rw [show u * u ^ 2 = u ^ 2 * u by rw [← pow_succ', ← pow_succ], mul_assoc, mul_inv_cancel,
      mul_one]
  obtain ⟨v, hvu, hvw, hvsq⟩ : ∃ v : X, (v = u ∨ v = t * u) ∧ v * w = w * v ∧ v ^ 2 = u ^ 2 := by
    rcases hW _ (hconjW u w hwW) with h1 | h1 | h1 | h1
    · exfalso; apply hw1
      calc w = u⁻¹ * (u * w * u⁻¹) * u := by group
        _ = 1 := by rw [h1]; group
    · exfalso; apply hgz'
      calc w = u⁻¹ * (u * w * u⁻¹) * u := by group
        _ = u⁻¹ * (u * u ^ 2 * u⁻¹) * u := by rw [h1, huz]
        _ = u ^ 2 := by group
    · refine ⟨u, Or.inl rfl, ?_, rfl⟩
      calc u * w = u * w * u⁻¹ * u := by group
        _ = w * u := by rw [h1]
    · refine ⟨t * u, Or.inr rfl, ?_, ?_⟩
      · have : t * u * w * (t * u)⁻¹ = w := by
          rw [show t * u * w * (t * u)⁻¹ = t * (u * w * u⁻¹) * t⁻¹ by group, h1,
            show t * (w * u ^ 2) * t⁻¹ = (t * w * t⁻¹) * (t * u ^ 2 * t⁻¹) by group, htw, htz,
            mul_assoc, ← sq, h.z_sq, mul_one]
        calc t * u * w = t * u * w * (t * u)⁻¹ * (t * u) := by group
          _ = w * (t * u) := by rw [this]
      · rw [h.commute_tu.mul_pow, h.t_sq, one_mul]
  have hvR : v ∈ secTwoR t u := by
    rcases hvu with rfl | rfl
    · exact SecTwoHyp.u_mem_R
    · exact mul_mem SecTwoHyp.t_mem_R SecTwoHyp.u_mem_R
  have hRv : ∀ r ∈ secTwoR t u, ∃ a b : ℕ, r = t ^ a * v ^ b := by
    intro r hr
    obtain ⟨a, b, rfl⟩ := h.exists_pow_of_mem_R hr
    rcases hvu with rfl | rfl
    · exact ⟨a, b, rfl⟩
    · refine ⟨a + b, b, ?_⟩
      rw [h.commute_tu.mul_pow, ← mul_assoc, ← pow_add, show a + b + b = a + 2 * b by ring,
        pow_add, pow_mul, h.t_sq, one_pow, mul_one]
  have hv4 : v ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hvsq, h.z_sq]
  have hCQt : ∀ c ∈ Q, c * t = t * c → c = 1 ∨ c = v ∨ c = u ^ 2 ∨ c = v * u ^ 2 := by
    intro c hcQ hct
    have hcR : c ∈ secTwoR t u := by
      refine h.le_R_of_normalized (N := Q ⊓ centralizer ({t} : Set X)) inf_le_right
        hQ2.to_inf_left ?_ ⟨hcQ, mem_centralizer_singleton_iff.mpr hct⟩
      intro k hk n hn
      refine Subgroup.mem_inf.mpr ⟨hQn.conj_mem n hn.1 k, ?_⟩
      rw [mem_centralizer_singleton_iff] at hk ⊢
      have hn' := mem_centralizer_singleton_iff.mp hn.2
      calc k * n * k⁻¹ * t = k * n * (k⁻¹ * t * k) * k⁻¹ := by group
        _ = k * n * t * k⁻¹ := by
          rw [show k⁻¹ * t * k = t by
            calc k⁻¹ * t * k = k⁻¹ * (t * k) := by group
              _ = k⁻¹ * (k * t) := by rw [hk]
              _ = t := by group]
        _ = k * (t * n) * k⁻¹ := by rw [mul_assoc k n t, hn']
        _ = (k * t) * n * k⁻¹ := by group
        _ = (t * k) * n * k⁻¹ := by rw [hk]
        _ = t * (k * n * k⁻¹) := by group
    obtain ⟨a, b, rfl⟩ := hRv _ hcR
    have hcw : t ^ a * v ^ b * w = w * (t ^ a * v ^ b) := secTwoOmegaZ_comm hwW hcQ
    have hvbw : v ^ b * w = w * v ^ b := ((Commute.pow_left hvw b) : Commute (v ^ b) w).eq
    have hta : t ^ a * w = w * t ^ a := by
      calc t ^ a * w = t ^ a * (w * v ^ b) * (v ^ b)⁻¹ := by group
        _ = t ^ a * (v ^ b * w) * (v ^ b)⁻¹ := by rw [hvbw]
        _ = (t ^ a * v ^ b * w) * (v ^ b)⁻¹ := by group
        _ = (w * (t ^ a * v ^ b)) * (v ^ b)⁻¹ := by rw [hcw]
        _ = w * t ^ a := by group
    have ha : t ^ a = 1 := by
      rw [← pow_mod_orderOf t a, h.orderOf_t] at hta ⊢
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha
      · rw [ha, pow_zero]
      · exfalso; rw [ha, pow_one] at hta
        apply hd6
        rw [← htw, hta, mul_assoc, mul_inv_cancel, mul_one]
    rw [ha, one_mul, ← pow_mod_orderOf v b] at *
    have hb : b % orderOf v < 4 := by
      have hdvd : orderOf v ∣ 4 := orderOf_dvd_of_pow_eq_one hv4
      have := Nat.mod_lt b (orderOf_pos v)
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    interval_cases (b % orderOf v)
    · left; rw [pow_zero]
    · right; left; rw [pow_one]
    · right; right; left; exact hvsq
    · right; right; right; rw [pow_succ', hvsq]
  have hwg : g⁻¹ * w * g = u ^ 2 := by rw [hwdef]; group
  have hzw : u ^ 2 * w = w * u ^ 2 := secTwoOmegaZ_comm hwW hzQ
  set T := g * t * g⁻¹ with hTdef
  have hTw : T * w * T⁻¹ = w := by
    calc T * w * T⁻¹ = g * (t * (g⁻¹ * w * g) * t⁻¹) * g⁻¹ := by rw [hTdef]; group
      _ = w := by rw [hwg, htz, hwdef]
  have hTz : T * u ^ 2 * T⁻¹ = w * u ^ 2 := by
    rcases hW _ (hconjW T _ hzW) with h1 | h1 | h1 | h1
    · exfalso; apply h.z_ne_one
      calc u ^ 2 = T⁻¹ * (T * u ^ 2 * T⁻¹) * T := by group
        _ = 1 := by rw [h1]; group
    · exfalso
      have hTW : ∀ a ∈ secTwoOmegaZ Q, T * a * T⁻¹ = a := by
        intro a ha
        rcases hW a ha with ha' | ha' | ha' | ha'
        · rw [ha']; group
        · rw [ha', h1]
        · rw [ha', hTw]
        · rw [ha', show T * (w * u ^ 2) * T⁻¹ = (T * w * T⁻¹) * (T * u ^ 2 * T⁻¹) by group,
            hTw, h1]
      have := hTW _ (hconjW g w hwW)
      apply hd6
      calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
        _ = g⁻¹ * (T * (g * w * g⁻¹) * T⁻¹) * g := by rw [this]
        _ = t * w * t⁻¹ := by rw [hTdef]; group
        _ = w * u ^ 2 := htw
    · exfalso; apply hgz'
      calc w = T⁻¹ * (T * w * T⁻¹) * T := by group
        _ = T⁻¹ * (T * u ^ 2 * T⁻¹) * T := by rw [hTw, h1]
        _ = u ^ 2 := by group
    · exact h1
  set y := t * T with hydef
  have hyz : y * u ^ 2 * y⁻¹ = w := by
    calc y * u ^ 2 * y⁻¹ = t * (T * u ^ 2 * T⁻¹) * t⁻¹ := by rw [hydef]; group
      _ = (t * w * t⁻¹) * (t * u ^ 2 * t⁻¹) := by rw [hTz]; group
      _ = w := by rw [htw, htz, mul_assoc, ← sq, h.z_sq, mul_one]
  have hyw : y * w * y⁻¹ = w * u ^ 2 := by
    calc y * w * y⁻¹ = t * (T * w * T⁻¹) * t⁻¹ := by rw [hydef]; group
      _ = w * u ^ 2 := by rw [hTw, htw]
  have hT2 : T * T = 1 := by
    calc T * T = g * (t * t) * g⁻¹ := by rw [hTdef]; group
      _ = 1 := by rw [h.t_mul_t]; group
  have hty : t * y * t⁻¹ = y⁻¹ := by
    rw [hydef, h.t_inv, show t * (t * T) * t = (t * t) * T * t by group, h.t_mul_t, one_mul,
      mul_inv_rev, h.t_inv, inv_eq_of_mul_eq_one_right hT2]
  have hywz : y * (w * u ^ 2) * y⁻¹ = u ^ 2 := by
    rw [show y * (w * u ^ 2) * y⁻¹ = (y * w * y⁻¹) * (y * u ^ 2 * y⁻¹) by group, hyw, hyz,
      mul_assoc, hzw, ← mul_assoc, ← sq, secTwoOmegaZ_sq hwW, one_mul]
  let f : ℕ → X := fun k => if k % 3 = 0 then u ^ 2 else if k % 3 = 1 then w else w * u ^ 2
  have hfstep : ∀ k, y * f k * y⁻¹ = f (k + 1) := by
    intro k
    have hk : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hk1 : (k + 1) % 3 = (k % 3 + 1) % 3 := by omega
    simp only [f, hk1]
    interval_cases (k % 3) <;> simp [hyz, hyw, hywz]
  have hfpow : ∀ n k, y ^ n * f k * (y ^ n)⁻¹ = f (k + n) := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      rw [show y ^ (n + 1) * f k * (y ^ (n + 1))⁻¹ = y * (y ^ n * f k * (y ^ n)⁻¹) * y⁻¹ by
        rw [pow_succ']; group, ih, hfstep, show k + n + 1 = k + (n + 1) by ring]
  have hf0 : f 0 = u ^ 2 := rfl
  have hf1 : f 1 = w := rfl
  have hf2 : f 2 = w * u ^ 2 := rfl
  obtain ⟨e, m, hm3, hym⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3
    (by norm_num)
  set x := y ^ m with hxdef
  have hmpos : m ≠ 0 := by
    rintro rfl; rw [mul_zero] at hym; exact (orderOf_pos y).ne' hym
  have hxord : orderOf x = 3 ^ e := by
    rw [hxdef, orderOf_pow_of_dvd hmpos ⟨3 ^ e, by rw [hym, mul_comm]⟩, hym,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hmpos)]
  have hx3 : IsPGroup 3 (zpowers x) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hxord]
    exact ⟨e, rfl⟩
  have htx : t * x * t⁻¹ = x⁻¹ := by
    rw [hxdef, ← conj_pow, hty, inv_pow]
  have hfinj : ∀ a b, f a = f b → a % 3 = b % 3 := by
    intro a b hab
    simp only [f] at hab
    split_ifs at hab with h1 h2 h3 h4 h3 h4 <;> first | omega | (exfalso; first
      | exact hgz' hab | exact hgz' hab.symm | exact hd5 hab | exact hd5 hab.symm
      | exact hd6 hab | exact hd6 hab.symm)
  have hxf : ∀ k, x * f k * x⁻¹ ≠ f k := by
    intro k hk
    rw [hxdef, hfpow] at hk
    have := hfinj _ _ hk
    omega
  have hxW : ∀ a ∈ secTwoOmegaZ Q, x * a * x⁻¹ = a → a = 1 := by
    intro a ha hxa
    rcases hW a ha with h1 | h1 | h1 | h1
    · exact h1
    · exfalso; apply hxf 0; rw [hf0]; rw [h1] at hxa; exact hxa
    · exfalso; apply hxf 1; rw [hf1]; rw [h1] at hxa; exact hxa
    · exfalso; apply hxf 2; rw [hf2]; rw [h1] at hxa; exact hxa
  have hg₂ : (y * g) * u ^ 2 * (y * g)⁻¹ = w * u ^ 2 := by
    rw [show (y * g) * u ^ 2 * (y * g)⁻¹ = y * (g * u ^ 2 * g⁻¹) * y⁻¹ by group, ← hwdef, hyw]
  exact ⟨⟨S, hRS, hRS', w, hzW, hwW, hw1, hgz', hW, g, hwdef.symm, htw, v, hvR, hvw, hvsq,
    hCQt, x, hx3, htx, hxW, y * g, hg₂⟩⟩

end Constrained

end CFSG.LocalAnalysis.EvenBN.Tits
