module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueLocal

public section

namespace CFSG.Semidihedral.UnitaryDValue

section General

variable {G : Type*} [Group G]

theorem zpow_mul_zpow_eq_one_iff {r : ℕ} {a b : G} (ha : orderOf a = r) (hb : orderOf b = r)
    (hdisj : ∀ i j : ℤ, a ^ i = b ^ j → a ^ i = 1) (i j : ℤ) :
    a ^ i * b ^ j = 1 ↔ (r : ℤ) ∣ i ∧ (r : ℤ) ∣ j := by
  constructor
  · intro h
    have h1 : a ^ i = b ^ (-j) := by
      rw [zpow_neg]
      exact eq_inv_of_mul_eq_one_left h
    have hai : a ^ i = 1 := hdisj i (-j) h1
    have hbj : b ^ j = 1 := by rw [hai, one_mul] at h; exact h
    exact ⟨ha ▸ orderOf_dvd_iff_zpow_eq_one.mpr hai, hb ▸ orderOf_dvd_iff_zpow_eq_one.mpr hbj⟩
  · rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    have h1 : a ^ (r : ℤ) = 1 := by rw [zpow_natCast, ← ha, pow_orderOf_eq_one]
    have h2 : b ^ (r : ℤ) = 1 := by rw [zpow_natCast, ← hb, pow_orderOf_eq_one]
    rw [zpow_mul, zpow_mul, h1, h2, one_zpow, one_zpow, mul_one]

theorem zpow_mul_zpow_mul_zpow_mul_zpow {a b : G} (hab : Commute a b) (i j k l : ℤ) :
    a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ (i + k) * b ^ (j + l) := by
  have h : Commute (b ^ j) (a ^ k) := (hab.symm.zpow_zpow j k)
  rw [zpow_add, zpow_add, mul_assoc, ← mul_assoc (b ^ j), h.eq, mul_assoc, mul_assoc]

theorem zpow_mul_zpow_zpow {a b : G} (hab : Commute a b) (i j n : ℤ) :
    (a ^ i * b ^ j) ^ n = a ^ (i * n) * b ^ (j * n) := by
  rw [(hab.zpow_zpow i j).mul_zpow, zpow_mul, zpow_mul]

theorem conj_zpow_mul_zpow {g a b : G} (hab : Commute a b) {α₁ β₁ α₂ β₂ : ℤ}
    (h1 : g * a * g⁻¹ = a ^ α₁ * b ^ β₁) (h2 : g * b * g⁻¹ = a ^ α₂ * b ^ β₂) (i j : ℤ) :
    g * (a ^ i * b ^ j) * g⁻¹ = a ^ (α₁ * i + α₂ * j) * b ^ (β₁ * i + β₂ * j) := by
  have hc : ∀ x : G, g * x * g⁻¹ = MulAut.conj g x := fun x => (MulAut.conj_apply g x).symm
  rw [hc, map_mul, map_zpow, map_zpow, ← hc, ← hc, h1, h2, zpow_mul_zpow_zpow hab,
    zpow_mul_zpow_zpow hab, zpow_mul_zpow_mul_zpow_mul_zpow hab]

theorem isCyclic_of_le_of_isCyclic {H K : Subgroup G} (h : H ≤ K) (hK : IsCyclic K) :
    IsCyclic H :=
  (Subgroup.subgroupOfEquivOfLe h).isCyclic.mp inferInstance

theorem exists_eq_zpowers_of_isCyclic' (H : Subgroup G) (hH : IsCyclic H) :
    ∃ u : G, H = Subgroup.zpowers u := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  refine ⟨g, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Subgroup.zpow_mem _ g.2 k

theorem mem_zpowers_of_pow_eq_one {r : ℕ} [Fact r.Prime] {w₀ x : G} {h : ℕ} (hh : 1 ≤ h)
    (hw₀ : orderOf w₀ = r ^ h) (hx : x ∈ Subgroup.zpowers w₀) (hxr : x ^ r = 1) :
    ∃ i : ℤ, x = (w₀ ^ (r ^ (h - 1))) ^ i := by
  have hr : r.Prime := Fact.out
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hdvd : (orderOf w₀ : ℤ) ∣ n * r := by
    apply orderOf_dvd_iff_zpow_eq_one.mpr
    rw [zpow_mul, zpow_natCast]
    exact hxr
  rw [hw₀] at hdvd
  have hsplit : ((r ^ h : ℕ) : ℤ) = (r ^ (h - 1) : ℕ) * r := by
    rw [← Nat.cast_mul, ← pow_succ, Nat.sub_add_cancel hh]
  rw [hsplit] at hdvd
  obtain ⟨c, hc⟩ := (mul_dvd_mul_iff_right (by exact_mod_cast hr.ne_zero)).mp hdvd
  refine ⟨c, ?_⟩
  rw [hc, ← zpow_natCast, ← zpow_mul]

theorem dvd_of_line_congr {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) {l μ ν : ℤ}
    (h1 : (r : ℤ) ∣ l ^ 2 - 1) (h2 : (r : ℤ) ∣ l ^ 3 - 1) (h3 : (r : ℤ) ∣ ν ^ 2 - 1)
    (h4 : (r : ℤ) ∣ ν ^ 3 - 1) (h5 : (r : ℤ) ∣ μ * (l ^ 2 + l * ν + ν ^ 2)) :
    (r : ℤ) ∣ μ ∧ (r : ℤ) ∣ ν - 1 := by
  have hl : (r : ℤ) ∣ l - 1 := by
    have := dvd_sub h2 (dvd_mul_of_dvd_right h1 l)
    convert this using 1
    ring
  have hν : (r : ℤ) ∣ ν - 1 := by
    have := dvd_sub h4 (dvd_mul_of_dvd_right h3 ν)
    convert this using 1
    ring
  have h6 : (r : ℤ) ∣ l ^ 2 + l * ν + ν ^ 2 - 3 := by
    have := dvd_add (dvd_mul_of_dvd_left hl (l + ν + 1)) (dvd_mul_of_dvd_left hν (ν + 2))
    convert this using 1
    ring
  have h7 : (r : ℤ) ∣ 3 * μ := by
    have := dvd_sub h5 (dvd_mul_of_dvd_right h6 μ)
    convert this using 1
    ring
  refine ⟨?_, hν⟩
  rcases (Nat.prime_iff_prime_int.mp hr).dvd_or_dvd h7 with h | h
  · exfalso
    have h' : r ∣ 3 := by exact_mod_cast h
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h')
  · exact h

end General

namespace DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

variable {r : ℕ} [Fact r.Prime]

theorem exists_generator_PW (hr2 : r ≠ 2) :
    ∃ w₀ : G, D.PW r = Subgroup.zpowers w₀ ∧ orderOf w₀ = r ^ (D.q + 1).factorization r := by
  obtain ⟨w₀, hw₀⟩ := D.exists_eq_zpowers_of_le_W (D.PW_le_W (r := r))
  refine ⟨w₀, hw₀, ?_⟩
  rw [← Nat.card_zpowers, ← hw₀, D.card_PW hr2]

theorem exists_generator_PA :
    ∃ c₀ : G, D.PA r = Subgroup.zpowers c₀ ∧ orderOf c₀ = r ^ (Nat.card D.A).factorization r := by
  obtain ⟨c₀, hc₀⟩ := exists_eq_zpowers_of_isCyclic' (D.PA r)
    (isCyclic_of_le_of_isCyclic (D.PA_le_A (r := r)) D.A_cyclic)
  refine ⟨c₀, hc₀, ?_⟩
  rw [← Nat.card_zpowers, ← hc₀, D.card_PA]

theorem factorization_card_A_eq_of_dvd (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hrA : r ∣ Nat.card D.A) :
    (Nat.card D.A).factorization r = (D.q + 1).factorization r := by
  have hr : r.Prime := Fact.out
  set k := (Nat.card D.A).factorization r with hkdef
  set h := (D.q + 1).factorization r with hhdef
  have hk1 : 1 ≤ k := (hr.dvd_iff_one_le_factorization D.card_A_pos.ne').mp hrA
  have hkh : k ≤ h :=
    (Nat.factorization_le_iff_dvd D.card_A_pos.ne' (by omega)).mpr D.card_A_dvd r
  by_contra hne
  have hlt : k < h := lt_of_le_of_ne hkh hne
  obtain ⟨w₀, hw₀, hw₀o⟩ := D.exists_generator_PW (r := r) hr2
  obtain ⟨c₀, hc₀, hc₀o⟩ := D.exists_generator_PA (r := r)
  rw [← hhdef] at hw₀o
  rw [← hkdef] at hc₀o
  set a := w₀ ^ (r ^ (h - 1)) with ha
  set b := c₀ ^ (r ^ (k - 1)) with hb
  have hao : orderOf a = r := by
    rw [ha, orderOf_pow' _ (pow_ne_zero _ hr.ne_zero), hw₀o,
      Nat.gcd_eq_right (Nat.pow_dvd_pow r (Nat.sub_le h 1)),
      show h = h - 1 + 1 by omega, pow_succ, Nat.add_sub_cancel,
      Nat.mul_div_cancel_left _ (pow_pos hr.pos _)]
  have hbo : orderOf b = r := by
    rw [hb, orderOf_pow' _ (pow_ne_zero _ hr.ne_zero), hc₀o,
      Nat.gcd_eq_right (Nat.pow_dvd_pow r (Nat.sub_le k 1)),
      show k = k - 1 + 1 by omega, pow_succ, Nat.add_sub_cancel,
      Nat.mul_div_cancel_left _ (pow_pos hr.pos _)]
  have hw₀P : w₀ ∈ D.PW r := hw₀ ▸ Subgroup.mem_zpowers w₀
  have hc₀P : c₀ ∈ D.PA r := hc₀ ▸ Subgroup.mem_zpowers c₀
  have haW : a ∈ D.PW r := (D.PW r).pow_mem hw₀P _
  have hbA : b ∈ D.PA r := (D.PA r).pow_mem hc₀P _
  have haP : a ∈ D.primaryPart r := D.PW_le haW
  have hbP : b ∈ D.primaryPart r := D.PA_le hbA
  have hPC : ∀ u ∈ D.primaryPart r, u ∈ D.C := fun u hu => D.primaryPart_le_C r hu
  have hab : Commute a b := D.C_comm a (hPC a haP) b (hPC b hbP)
  have hdisj : ∀ i j : ℤ, a ^ i = b ^ j → a ^ i = 1 := by
    intro i j hij
    have h1 : a ^ i ∈ D.PW r ⊓ D.PA r := ⟨(D.PW r).zpow_mem haW i, hij ▸ (D.PA r).zpow_mem hbA j⟩
    rw [D.disjoint_PW_PA.eq_bot] at h1
    exact h1
  have hcoord := zpow_mul_zpow_eq_one_iff hao hbo hdisj
  have hOmega : ∀ u ∈ D.primaryPart r, u ^ r = 1 → ∃ i j : ℤ, u = a ^ i * b ^ j := by
    intro u hu hur
    obtain ⟨w, hw, c, hc, rfl⟩ := D.exists_mul_eq hr2 hu
    have hwc : Commute w c := D.C_comm w (hPC w (D.PW_le hw)) c (hPC c (D.PA_le hc))
    rw [hwc.mul_pow] at hur
    have hwr : w ^ r = 1 := by
      have h1 : w ^ r ∈ D.PW r ⊓ D.PA r := by
        refine ⟨(D.PW r).pow_mem hw r, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hur]
        exact (D.PA r).inv_mem ((D.PA r).pow_mem hc r)
      rw [D.disjoint_PW_PA.eq_bot] at h1
      exact h1
    have hcr : c ^ r = 1 := by rw [hwr, one_mul] at hur; exact hur
    obtain ⟨i, hi⟩ := mem_zpowers_of_pow_eq_one (by omega) hw₀o (hw₀ ▸ hw) hwr
    obtain ⟨j, hj⟩ := mem_zpowers_of_pow_eq_one hk1 hc₀o (hc₀ ▸ hc) hcr
    exact ⟨i, j, by rw [hi, hj]⟩
  have hta : ∃ l : ℤ, D.t * a * D.t⁻¹ = a ^ l := by
    set v := w₀ ^ (r ^ (h - 1 - k)) with hv
    have hva : v ^ (r ^ k) = a := by
      rw [hv, ← pow_mul, ← pow_add, ha, show h - 1 - k + k = h - 1 by omega]
    have hvP : v ∈ D.primaryPart r := D.PW_le ((D.PW r).pow_mem hw₀P _)
    obtain ⟨w', hw', c', hc', hwc'⟩ := D.exists_mul_eq hr2 (D.t_conj_primaryPart hvP)
    have hc'k : c' ^ (r ^ k) = 1 := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hc₀ ▸ hc')
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hc₀o,
        pow_orderOf_eq_one, one_zpow]
    have hcomm' : Commute w' c' := D.C_comm w' (hPC w' (D.PW_le hw')) c' (hPC c' (D.PA_le hc'))
    have htaW : D.t * a * D.t⁻¹ = w' ^ (r ^ k) := by
      rw [← hva, ← conj_pow, hwc', hcomm'.mul_pow, hc'k, mul_one]
    have htaP : D.t * a * D.t⁻¹ ∈ D.PW r := htaW ▸ (D.PW r).pow_mem hw' _
    have htar : (D.t * a * D.t⁻¹) ^ r = 1 := by
      rw [conj_pow, ← hao, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
    obtain ⟨i, hi⟩ := mem_zpowers_of_pow_eq_one (by omega) hw₀o (hw₀ ▸ htaP) htar
    exact ⟨i, by rw [hi]⟩
  obtain ⟨l, hl⟩ := hta
  obtain ⟨μ, ν, hbt⟩ := hOmega _ (D.t_conj_primaryPart hbP)
    (by rw [conj_pow, ← hbo, pow_orderOf_eq_one, mul_one, mul_inv_cancel])
  have hTa : D.t * a * D.t⁻¹ = a ^ l * b ^ (0 : ℤ) := by rw [hl, zpow_zero, mul_one]
  have hTb : D.t * b * D.t⁻¹ = a ^ μ * b ^ ν := hbt
  have hYa : D.y * a * D.y⁻¹ = a ^ (-1 : ℤ) * b ^ (0 : ℤ) := by
    rw [D.y_W a (D.PW_le_W haW), zpow_zero, mul_one, zpow_neg_one]
  have hYb : D.y * b * D.y⁻¹ = a ^ (0 : ℤ) * b ^ (1 : ℤ) := by
    rw [D.y_conj_A (D.PA_le_A hbA), zpow_zero, one_mul, zpow_one]
  have hYia : D.y⁻¹ * a * D.y⁻¹⁻¹ = a ^ (-1 : ℤ) * b ^ (0 : ℤ) := by
    rw [inv_inv, D.y_inv_conj_W (D.PW_le_W haW), zpow_zero, mul_one, zpow_neg_one]
  have hYib : D.y⁻¹ * b * D.y⁻¹⁻¹ = a ^ (0 : ℤ) * b ^ (1 : ℤ) := by
    have hyA : D.y⁻¹ ∈ D.N := D.N.inv_mem D.y_mem_N
    rw [conj_eq_of_comm (D.A_central b (D.PA_le_A hbA) _ hyA), zpow_zero, one_mul, zpow_one]
  have hcoords : ∀ i j i' j' : ℤ, a ^ i * b ^ j = a ^ i' * b ^ j' →
      (r : ℤ) ∣ i - i' ∧ (r : ℤ) ∣ j - j' := by
    intro i j i' j' hij
    apply (hcoord (i - i') (j - j')).mp
    calc a ^ (i - i') * b ^ (j - j') = a ^ i * b ^ j * (a ^ (-i') * b ^ (-j')) := by
          rw [zpow_mul_zpow_mul_zpow_mul_zpow hab, sub_eq_add_neg, sub_eq_add_neg]
      _ = a ^ i' * b ^ j' * (a ^ (-i') * b ^ (-j')) := by rw [hij]
      _ = 1 := by rw [zpow_mul_zpow_mul_zpow_mul_zpow hab, add_neg_cancel, add_neg_cancel,
          zpow_zero, zpow_zero, mul_one]
  have he : D.y * D.t * D.y⁻¹ * D.t = D.y * (D.t * (D.y⁻¹ * D.t)) := by group
  have ht3 : D.t ^ 3 = D.t * (D.t * D.t) := pow_three D.t
  have hea := D.C_conj D.y_t_y_inv_t_mem_C (hPC a haP)
  have heb := D.C_conj D.y_t_y_inv_t_mem_C (hPC b hbP)
  have hta3 := D.C_conj D.t_cube_mem_C (hPC a haP)
  have htb3 := D.C_conj D.t_cube_mem_C (hPC b hbP)
  rw [he, conj_mul_eq, conj_mul_eq, conj_mul_eq, hTa, conj_zpow_mul_zpow hab hYia hYib,
    conj_zpow_mul_zpow hab hTa hTb, conj_zpow_mul_zpow hab hYa hYb] at hea
  rw [he, conj_mul_eq, conj_mul_eq, conj_mul_eq, hTb, conj_zpow_mul_zpow hab hYia hYib,
    conj_zpow_mul_zpow hab hTa hTb, conj_zpow_mul_zpow hab hYa hYb] at heb
  rw [ht3, conj_mul_eq, conj_mul_eq, hTa, conj_zpow_mul_zpow hab hTa hTb,
    conj_zpow_mul_zpow hab hTa hTb] at hta3
  rw [ht3, conj_mul_eq, conj_mul_eq, hTb, conj_zpow_mul_zpow hab hTa hTb,
    conj_zpow_mul_zpow hab hTa hTb] at htb3
  have hA1 : a = a ^ (1 : ℤ) * b ^ (0 : ℤ) := by rw [zpow_one, zpow_zero, mul_one]
  have hB1 : b = a ^ (0 : ℤ) * b ^ (1 : ℤ) := by rw [zpow_zero, zpow_one, one_mul]
  have c1 := (hcoords _ _ _ _ (hea.trans hA1)).1
  have c2 := (hcoords _ _ _ _ (hta3.trans hA1)).1
  have c3 := (hcoords _ _ _ _ (heb.trans hB1)).2
  have c4 := hcoords _ _ _ _ (htb3.trans hB1)
  obtain ⟨hμ, hν⟩ := dvd_of_line_congr hr hr3 (l := l) (μ := μ) (ν := ν)
    (by convert c1 using 1; ring) (by convert c2 using 1; ring) (by convert c3 using 1; ring)
    (by convert c4.2 using 1; ring) (by convert c4.1 using 1; ring)
  have htb : D.t * b * D.t⁻¹ = b := by
    have h1 : a ^ μ * b ^ (ν - 1) = 1 := (hcoord μ (ν - 1)).mpr ⟨hμ, hν⟩
    rw [hTb]
    calc a ^ μ * b ^ ν = a ^ μ * b ^ (ν - 1) * b := by
          rw [mul_assoc, ← zpow_add_one, sub_add_cancel]
      _ = b := by rw [h1, one_mul]
  have hb1 : b ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hbo
    exact hr.one_lt.ne hbo
  apply D.t_not_mem_N
  apply D.A_confine b (D.PA_le_A hbA) hb1
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact comm_of_conj_eq htb

end DValueData

end CFSG.Semidihedral.UnitaryDValue
