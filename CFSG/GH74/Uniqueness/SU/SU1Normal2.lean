module

public import CFSG.GH74.Uniqueness.SU.SU1Normal1

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

variable {P : Type} [Group P] [Finite P]

theorem dvd_sub_one_of_pow_mod {p k u : ℕ} (hp : p.Prime) (hodd : Odd p) (hk : 1 ≤ k)
    (h : u ^ p % p ^ k = 1) : p ∣ u - 1 ∧ p ^ (k - 1) ∣ u - 1 := by
  have := Fact.mk hp
  have hpk : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
  have hu0 : 1 ≤ u := by
    by_contra hcon
    have : u = 0 := by omega
    subst this
    rw [zero_pow hp.ne_zero, Nat.zero_mod] at h
    omega
  have hup1 : 1 ≤ u ^ p := Nat.one_le_pow _ _ hu0
  have hdvd : p ^ k ∣ u ^ p - 1 := by
    have h1 : u ^ p ≡ 1 [MOD p ^ k] := by
      rw [Nat.ModEq, h, Nat.mod_eq_of_lt hpk]
    exact (Nat.modEq_iff_dvd' hup1).mp h1.symm
  have hpu : p ∣ u - 1 := by
    have hdvd' : p ∣ u ^ p - 1 := (dvd_pow_self p (by omega : k ≠ 0)).trans hdvd
    have h2 : ((u ^ p : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact ((Nat.modEq_iff_dvd' hup1).mpr hdvd').symm
    have h3 : (u : ZMod p) = 1 := by
      have h4 := ZMod.pow_card (u : ZMod p)
      push_cast at h2
      rw [h2] at h4
      exact h4.symm
    have h5 : u ≡ 1 [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa using h3
    exact (Nat.modEq_iff_dvd' hu0).mp h5.symm
  refine ⟨hpu, ?_⟩
  rcases Nat.eq_or_lt_of_le hu0 with rfl | hu2
  · simp
  · have hnpu : ¬ p ∣ u := by
      intro hpu'
      have : p ∣ 1 := by
        have h1 : p ∣ u - (u - 1) := Nat.dvd_sub hpu' hpu
        rwa [Nat.sub_sub_self hu0] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hlte := padicValNat.pow_sub_pow (p := p) (x := u) (y := 1) hodd hu2 hpu hnpu
      (n := p) hp.ne_zero
    rw [one_pow, padicValNat_self] at hlte
    have hne1 : u ^ p - 1 ≠ 0 := by
      have : 1 < u ^ p := Nat.one_lt_pow hp.ne_zero hu2
      omega
    have hk' : k ≤ padicValNat p (u ^ p - 1) := (padicValNat_dvd_iff_le hne1).mp hdvd
    have hne2 : u - 1 ≠ 0 := by omega
    exact (padicValNat_dvd_iff_le hne2).mpr (by omega)

omit [Finite P] in
theorem mul_pow_of_mem_center {g h c : P} (hc : c ∈ center P) (hgh : h * g = c * (g * h))
    (n : ℕ) : (g * h) ^ n = c ^ (n.choose 2) * (g ^ n * h ^ n) := by
  have hcn : ∀ (m : ℕ) (x : P), c ^ m * x = x * c ^ m := fun m x =>
    (Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hc m) x).symm
  have hmv : ∀ (m : ℕ) (x y : P), x * (c ^ m * y) = c ^ m * (x * y) := fun m x y => by
    rw [← mul_assoc, ← hcn m x, mul_assoc]
  have key : ∀ n : ℕ, h ^ n * g = c ^ n * (g * h ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc h ^ (n + 1) * g = h * (h ^ n * g) := by rw [pow_succ', mul_assoc]
        _ = h * (c ^ n * (g * h ^ n)) := by rw [ih]
        _ = c ^ n * (h * (g * h ^ n)) := hmv n h _
        _ = c ^ n * ((h * g) * h ^ n) := by simp only [mul_assoc]
        _ = c ^ n * ((c * (g * h)) * h ^ n) := by rw [hgh]
        _ = c ^ n * (c * ((g * h) * h ^ n)) := by simp only [mul_assoc]
        _ = c ^ (n + 1) * ((g * h) * h ^ n) := by rw [← mul_assoc, ← pow_succ]
        _ = c ^ (n + 1) * (g * h ^ (n + 1)) := by rw [pow_succ' h n]; simp only [mul_assoc]
  induction n with
  | zero => simp
  | succ n ih =>
    have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    calc (g * h) ^ (n + 1) = (g * h) ^ n * (g * h) := by rw [pow_succ]
      _ = (c ^ (n.choose 2) * (g ^ n * h ^ n)) * (g * h) := by rw [ih]
      _ = c ^ (n.choose 2) * (g ^ n * ((h ^ n * g) * h)) := by simp only [mul_assoc]
      _ = c ^ (n.choose 2) * (g ^ n * ((c ^ n * (g * h ^ n)) * h)) := by rw [key n]
      _ = c ^ (n.choose 2) * (g ^ n * (c ^ n * ((g * h ^ n) * h))) := by simp only [mul_assoc]
      _ = c ^ (n.choose 2) * (c ^ n * (g ^ n * ((g * h ^ n) * h))) := by rw [hmv n]
      _ = (c ^ (n.choose 2) * c ^ n) * (g ^ n * ((g * h ^ n) * h)) := by rw [← mul_assoc]
      _ = c ^ ((n + 1).choose 2) * (g ^ (n + 1) * h ^ (n + 1)) := by
          rw [hchoose, pow_add, pow_succ g n, pow_succ h n]
          simp only [mul_assoc]

omit [Finite P] in
theorem dvd_choose_two {p : ℕ} (hodd : Odd p) : p ∣ p.choose 2 := by
  obtain ⟨m, hm⟩ := hodd
  have h2 : p.choose 2 * 2 = p * (p - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd
  have hp1 : p - 1 = 2 * m := by omega
  have h3 : p.choose 2 * 2 = (p * m) * 2 := by rw [h2, hp1]; ring
  exact ⟨m, Nat.eq_of_mul_eq_mul_right two_pos h3⟩

omit [Finite P] in
theorem conj_of_mem_zpowers {y a b : P} {u : ℕ} (hy : y * a * y⁻¹ = a ^ u) (hb : b ∈ zpowers a) :
    y * b * y⁻¹ = b ^ u := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← conj_zpow, hy]
  calc (a ^ u) ^ m = a ^ ((u : ℤ) * m) := by rw [← zpow_natCast, ← zpow_mul]
    _ = a ^ (m * (u : ℤ)) := by rw [mul_comm]
    _ = (a ^ m) ^ u := by rw [zpow_mul, zpow_natCast]

omit [Finite P] in
theorem mem_zpowers_z_of_pow_eq_one {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {a c : P}
    (hord : orderOf a = p ^ k) (hc : c ∈ zpowers a) (hcp : c ^ p = 1) :
    c ∈ zpowers (a ^ (p ^ (k - 1))) := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h1 : (a ^ m) ^ p = a ^ (m * p) := by rw [← zpow_natCast, ← zpow_mul]
  rw [h1] at hcp
  have h2 : ((p ^ k : ℕ) : ℤ) ∣ m * p := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hcp
  have h3 : p ^ k = p ^ (k - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [h3] at h2
  push_cast at h2
  have h4 : ((p ^ (k - 1) : ℕ) : ℤ) ∣ m := by
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (p : ℤ) ^ (k - 1) * p ∣ m * p := by simpa using h2
    exact_mod_cast (mul_dvd_mul_iff_right hp0).mp this
  obtain ⟨m', hm'⟩ := h4
  refine Subgroup.mem_zpowers_iff.mpr ⟨m', ?_⟩
  rw [hm', zpow_mul, zpow_natCast]

omit [Finite P] in
theorem comm_mem_zpowers_z {p k u : ℕ} {y a : P} (hy : y * a * y⁻¹ = a ^ u) (hu : 1 ≤ u)
    (hdvd : p ^ (k - 1) ∣ u - 1) {b : P} (hb : b ∈ zpowers a) :
    b⁻¹ * (y * b * y⁻¹) ∈ zpowers (a ^ (p ^ (k - 1))) := by
  rw [conj_of_mem_zpowers hy hb]
  obtain ⟨t, ht⟩ := hdvd
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h1 : (a ^ m) ^ u = (a ^ m) * (a ^ m) ^ (u - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hu]
  rw [h1, ← mul_assoc, inv_mul_cancel, one_mul]
  refine Subgroup.mem_zpowers_iff.mpr ⟨m * t, ?_⟩
  rw [ht, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  push_cast
  congr 1
  ring

theorem false_of_odd {p k : ℕ} (hp : p.Prime) (hodd : Odd p) (hP : IsPGroup p P)
    {Q : Subgroup P} {a : P} (h : NSetting Q a) (hord : orderOf a = p ^ k) (hk : 1 ≤ k)
    (hne : zpowers a ≠ Q)
    (hstar : ∀ E : Subgroup P, E.Normal → E ≤ Q → Open.IsElemAbelian p E →
      Nat.card E = p ^ 2 → False) : False := by
  have := Fact.mk hp
  have hAn := h.normalA
  have hpk : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
  have hapk : a ^ (p ^ k) = 1 := by rw [← hord]; exact pow_orderOf_eq_one a
  have hlt : zpowers a < Q := lt_of_le_of_ne h.le (Ne.symm hne |>.symm)
  obtain ⟨y, hyQ, hyA, hyp⟩ := exists_mem_pow_mem hp hP hlt
  obtain ⟨u, hu⟩ := h.exists_conj_pow y
  have hup : u ^ p % p ^ k = 1 := by
    obtain ⟨m, hm⟩ := exists_pow_eq_of_mem_zpowers hyp
    have hcomm : y ^ p * a = a * y ^ p := by
      rw [← hm]
      exact ((Commute.refl a).pow_left m).eq
    have h1 : y ^ p * a * (y ^ p)⁻¹ = a := by
      rw [hcomm]
      group
    have h2 := conj_npow hu p
    have h3 : a ^ (u ^ p) = a ^ 1 := by rw [← h2, h1, pow_one]
    have h4 := pow_inj_mod.mp h3
    rw [hord, Nat.mod_eq_of_lt hpk] at h4
    exact h4
  have hu1 : u % p ^ k ≠ 1 := by
    intro hcon
    have h1 : y * a * y⁻¹ = a := by rw [hu, pow_eq_pow_mod u hapk, hcon, pow_one]
    apply hyA
    apply h.centralizer y hyQ
    calc y * a = (y * a * y⁻¹) * y := by group
      _ = a * y := by rw [h1]
  have hu0 : 1 ≤ u := by
    by_contra hcon
    have : u = 0 := by omega
    subst this
    rw [zero_pow hp.ne_zero] at hup
    simp at hup
  obtain ⟨hpu, hpku⟩ := dvd_sub_one_of_pow_mod hp hodd hk hup
  have hmodk : ∀ w : ℕ, p ^ k ∣ w - 1 → 1 ≤ w → w % p ^ k = 1 := by
    intro w hw hw1
    have : 1 ≡ w [MOD p ^ k] := (Nat.modEq_iff_dvd' hw1).mpr hw
    rw [Nat.ModEq, Nat.mod_eq_of_lt hpk] at this
    exact this.symm
  have hk2 : 2 ≤ k := by
    by_contra hcon
    have hk1 : k = 1 := by omega
    subst hk1
    exact hu1 (hmodk u (by simpa using hpu) hu0)
  obtain ⟨t, ht⟩ := hpku
  have hpt : ¬ p ∣ t := by
    rintro ⟨s, hs⟩
    apply hu1
    refine hmodk u ⟨s, ?_⟩ hu0
    rw [ht, hs, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hk]
  set z : P := a ^ (p ^ (k - 1)) with hz
  have hzA : z ∈ zpowers a := Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _
  have hpk1 : p ^ k = p ^ (k - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hk]
  have hzp : z ^ p = 1 := by
    rw [hz, ← pow_mul, ← hpk1, hapk]
  have hz1 : z ≠ 1 := by
    intro hz1
    have : orderOf a ∣ p ^ (k - 1) := orderOf_dvd_of_pow_eq_one hz1
    rw [hord] at this
    have h1 := Nat.le_of_dvd (pow_pos hp.pos _) this
    have h2 : p ^ (k - 1) < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  have hzc : z ∈ center P :=
    mem_center_of_normal_prime hp hP hz1 hzp (h.normal_zpowers_pow _)
  have hZc : zpowers z ≤ center P := Subgroup.zpowers_le.mpr hzc
  obtain ⟨j, hj⟩ := exists_pow_eq_of_mem_zpowers hyp
  have hj0 : p ∣ j := by
    have h1 : y * y ^ p * y⁻¹ = y ^ p := by group
    rw [← hj] at h1
    have h2 := conj_of_mem_zpowers hu (b := a ^ j) (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) j)
    rw [h2] at h1
    have h3 : (a ^ j) ^ (u - 1) = 1 := by
      have : (a ^ j) ^ u = (a ^ j) * (a ^ j) ^ (u - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hu0]
      rw [this] at h1
      exact mul_eq_left.mp h1
    rw [← pow_mul] at h3
    have h4 : p ^ k ∣ j * (u - 1) := hord ▸ orderOf_dvd_of_pow_eq_one h3
    rw [ht] at h4
    have h5 : p ^ (k - 1) * p ∣ p ^ (k - 1) * (j * t) := by
      rw [← hpk1]
      convert h4 using 1
      ring
    have h6 : p ∣ j * t := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h5
    exact (hp.dvd_mul.mp h6).resolve_right hpt
  obtain ⟨j', rfl⟩ := hj0
  set b : P := a ^ j' with hb
  have hbA : b ∈ zpowers a := Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _
  have hbp : b ^ p = y ^ p := by rw [hb, ← pow_mul, mul_comm, hj]
  set y' : P := y * b⁻¹ with hy'
  have hy'Q : y' ∈ Q := Q.mul_mem hyQ (Q.inv_mem (h.le hbA))
  have hy'A : y' ∉ zpowers a := by
    intro hmem
    apply hyA
    have := (zpowers a).mul_mem hmem hbA
    simpa [hy'] using this
  have hu' : y' * a * y'⁻¹ = a ^ u := by
    have hba : b * a = a * b := ((Commute.refl a).pow_left j').eq
    calc y' * a * y'⁻¹ = y * (b⁻¹ * a * b) * y⁻¹ := by rw [hy']; group
      _ = y * a * y⁻¹ := by
          congr 2
          calc b⁻¹ * a * b = b⁻¹ * (a * b) := by group
            _ = b⁻¹ * (b * a) := by rw [hba]
            _ = a := by group
      _ = a ^ u := hu
  have hcomm' : ∀ {y₀ : P} {c₀ : P}, y₀ * a * y₀⁻¹ = a ^ u → c₀ ∈ zpowers a →
      c₀⁻¹ * (y₀ * c₀ * y₀⁻¹) ∈ zpowers z := fun hy₀ hc₀ =>
    comm_mem_zpowers_z hy₀ hu0 ⟨t, ht⟩ hc₀
  have hy'p : y' ^ p = 1 := by
    set c : P := b⁻¹ * (y * b * y⁻¹) with hc
    have hcZ : c ∈ center P := hZc (hcomm' hu hbA)
    have hgh : b⁻¹ * y = c * (y * b⁻¹) := by rw [hc]; group
    have hform := mul_pow_of_mem_center hcZ hgh p
    have hcp : c ^ p = 1 := by
      have hcz := hcomm' hu hbA
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hcz
      rw [← hc] at hm
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzp, one_zpow]
    have hc2 : c ^ p.choose 2 = 1 := by
      obtain ⟨m', hm'⟩ := dvd_choose_two hodd
      rw [hm', pow_mul, hcp, one_pow]
    rw [hy', hform, hc2, one_mul, inv_pow, ← hbp]
    group
  have hzpowp : ∀ x ∈ zpowers z, x ^ p = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzp, one_zpow]
  have hy'z : y' ∉ zpowers z := fun hmem => hy'A (Subgroup.zpowers_le.mpr hzA hmem)
  obtain ⟨hel, hcard⟩ := isElemAbelian_card_sup_zpowers hp hzp hy'p hz1 hy'z
    ((Subgroup.mem_center_iff.mp hzc y').symm)
  have hEQ : zpowers z ⊔ zpowers y' ≤ Q :=
    sup_le ((Subgroup.zpowers_le.mpr hzA).trans h.le) (Subgroup.zpowers_le.mpr hy'Q)
  have hEn : (zpowers z ⊔ zpowers y').Normal := by
    have hle : ∀ g : P, (zpowers z ⊔ zpowers y').map (MulAut.conj g).toMonoidHom ≤
        zpowers z ⊔ zpowers y' := by
      intro g
      rw [Subgroup.map_le_iff_le_comap]
      refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
      · intro x hx
        rw [Subgroup.mem_comap]
        change g * x * g⁻¹ ∈ _
        have hxc : x ∈ center P := hZc hx
        have : g * x * g⁻¹ = x := by
          rw [Subgroup.mem_center_iff.mp hxc g]
          group
        rw [this]
        exact Subgroup.mem_sup_left hx
      · rw [Subgroup.mem_comap]
        change g * y' * g⁻¹ ∈ _
        obtain ⟨c₀, hc₀, hgy⟩ := h.conj_mem_coset hy'Q g
        rw [hgy]
        have hc₀z : c₀ ∈ zpowers z := by
          apply mem_zpowers_z_of_pow_eq_one hp hk hord hc₀
          set c₁ : P := c₀ * y' * c₀⁻¹ * y'⁻¹ with hc₁
          have hc₁z : c₁ ∈ zpowers z := by
            have := hcomm' hu' (Subgroup.inv_mem _ hc₀)
            rw [inv_inv] at this
            have e : c₁ = c₀ * (y' * c₀⁻¹ * y'⁻¹) := by rw [hc₁]; group
            rw [e]
            exact this
          have hc₁Z : c₁ ∈ center P := hZc hc₁z
          have hgh : c₀ * y' = c₁ * (y' * c₀) := by rw [hc₁]; group
          have hform := mul_pow_of_mem_center hc₁Z hgh p
          have hconj : (y' * c₀) ^ p = 1 := by
            have h1 : (g * y' * g⁻¹) ^ p = 1 := by rw [conj_pow, hy'p]; group
            rw [hgy] at h1
            exact h1
          have hc₁2 : c₁ ^ p.choose 2 = 1 := by
            obtain ⟨m', hm'⟩ := dvd_choose_two hodd
            rw [hm', pow_mul, hzpowp c₁ hc₁z, one_pow]
          rw [hform, hc₁2, hy'p, one_mul, one_mul] at hconj
          exact hconj
        exact (zpowers z ⊔ zpowers y').mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers y'))
          (Subgroup.mem_sup_left hc₀z)
    exact ⟨fun x hx g => hle g ⟨x, hx, rfl⟩⟩
  exact hstar _ hEn hEQ hel hcard

end CFSG.GH74.Uniqueness.SU.SU1
