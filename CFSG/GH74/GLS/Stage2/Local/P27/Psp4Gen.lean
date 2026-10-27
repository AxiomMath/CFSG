module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Canon

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G] {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ}

namespace Data

theorem gen_z_mul_ne (h : Data S P₁ P₂ z t a) (x : G) : z * x ≠ x := by
  intro hx
  apply h.z_ne_one
  exact mul_right_cancel (b := x) (by rw [hx, one_mul])

theorem gen_eq_one_or_z_of_sq (h : Data S P₁ P₂ z t a) {p : G} (hp : p ∈ P₁) (hp2 : p * p = 1) :
    p = 1 ∨ p = z := by
  obtain ⟨a₀, b₀, M, ha, hb, hM, hN, hqg, hspan⟩ := h.exists_gens
  by_cases h1 : p = 1
  · exact Or.inl h1
  · right
    have e1 : p = a₀ ^ (2 * M) := hqg.eq_aN_of_involution (P := P₁) (by omega) hspan hp hp2 h1
    have e2 : z = a₀ ^ (2 * M) :=
      hqg.eq_aN_of_involution (P := P₁) (by omega) hspan h.z_mem₁ h.z_sq h.z_ne_one
    rw [e1, e2]

theorem gen_conj_rr₁ (h : Data S P₁ P₂ z t a) {g p q : G} (hg : g ∈ P₁) (hq : q ∈ P₁) :
    g * rr t p q * g⁻¹ = rr t (g * p * g⁻¹) q := by
  have hc := h.comm_σ hg hq
  unfold rr
  generalize t * q * t⁻¹ = w at hc ⊢
  have hw : w * g⁻¹ = g⁻¹ * w := by
    calc w * g⁻¹ = g⁻¹ * (g * w) * g⁻¹ := by group
      _ = g⁻¹ * (w * g) * g⁻¹ := by rw [hc]
      _ = g⁻¹ * w := by group
  calc g * (p * w) * g⁻¹ = g * p * (w * g⁻¹) := by group
    _ = g * p * (g⁻¹ * w) := by rw [hw]
    _ = g * p * g⁻¹ * w := by group

theorem gen_rr_mem_S (h : Data S P₁ P₂ z t a) {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) : rr t p q ∈ S :=
  mul_mem (h.P₁_le hp) (h.P₂_le (h.swap q hq))

theorem gen_rr_mul_z_left (h : Data S P₁ P₂ z t a) {p q : G} (hp : p ∈ P₁) (hq : q ∈ P₁) :
    rr t p q * z = rr t (z * p) q := by
  rw [← h.z_cent' (h.gen_rr_mem_S hp hq), z_mul_rr_left]

theorem gen_conj_t_σ (h : Data S P₁ P₂ z t a) {g q : G} (hg : g ∈ P₁) (hq : q ∈ P₁) :
    (g * t * g⁻¹) * q * (g * t * g⁻¹)⁻¹ = t * (g⁻¹ * q * g) * t⁻¹ := by
  have hw : t * (g⁻¹ * q * g) * t⁻¹ ∈ P₂ := h.swap _ (mul_mem (mul_mem (inv_mem hg) hq) hg)
  have hc := h.comm g hg _ hw
  have key : g * (t * (g⁻¹ * q * g) * t⁻¹) * g⁻¹ = t * (g⁻¹ * q * g) * t⁻¹ := by
    generalize t * (g⁻¹ * q * g) * t⁻¹ = w at hc ⊢
    rw [hc]
    group
  rw [← key]
  group

theorem gen_rr_conj_t (h : Data S P₁ P₂ z t a) {g p q : G} (hg : g ∈ P₁) (hq : q ∈ P₁) :
    rr (g * t * g⁻¹) p q = rr t p (g⁻¹ * q * g) := by
  unfold rr
  rw [h.gen_conj_t_σ hg hq]

theorem gen_conj_t (h : Data S P₁ P₂ z t a) {g : G} (hg : g ∈ P₁) : Data S P₁ P₂ z (g * t * g⁻¹) a where
  z_mem := h.z_mem
  z_ord := h.z_ord
  z_cent := h.z_cent
  P₁_le := h.P₁_le
  P₂_le := h.P₂_le
  P₁_quat := h.P₁_quat
  P₂_quat := h.P₂_quat
  inter := h.inter
  comm := h.comm
  t_mem := mul_mem (mul_mem (h.P₁_le hg) h.t_mem) (inv_mem (h.P₁_le hg))
  t_inv := by
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [h.t_inv]; group
  t_not := by
    intro hmem
    apply h.t_not
    have hgR : g ∈ P₁ ⊔ P₂ := mem_sup_left hg
    have e : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hgR) hmem) hgR
  idx := h.idx
  swap := by
    intro p hp
    rw [h.gen_conj_t_σ hg hp]
    exact h.swap _ (mul_mem (mul_mem (inv_mem hg) hp) hg)

end Data

theorem gen_conj_class_eq {R : Subgroup G} {g : G} (hg : g ∈ R) (w : G) :
    {y | ∃ r ∈ R, y = r * (g * w * g⁻¹) * r⁻¹} = {y | ∃ r ∈ R, y = r * w * r⁻¹} := by
  refine Set.ext fun y => ⟨?_, ?_⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r * g, mul_mem hr hg, by group⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r * g⁻¹, mul_mem hr (inv_mem hg), by group⟩

theorem gen_Zc_conj_t {R : Subgroup G} {g : G} (hg : g ∈ R) :
    Zc R z (g * t * g⁻¹) = Zc R z t := by
  unfold Zc
  rw [gen_conj_class_eq hg]

namespace Data

theorem gen_Xc_conj_t (h : Data S P₁ P₂ z t a) {g : G} (hg : g ∈ P₁) :
    Xc (P₁ ⊔ P₂) z (g * t * g⁻¹) = Xc (P₁ ⊔ P₂) z t := by
  unfold Xc
  have e : g * t * g⁻¹ * z = g * (t * z) * g⁻¹ := by
    have hz : z * g⁻¹ = g⁻¹ * z := h.z_cent' (inv_mem (h.P₁_le hg))
    calc g * t * g⁻¹ * z = g * t * (g⁻¹ * z) := by group
      _ = g * t * (z * g⁻¹) := by rw [hz]
      _ = g * (t * z) * g⁻¹ := by group
  rw [e, gen_conj_class_eq (mem_sup_left hg)]

end Data

theorem Data.gen_rr_one_or_z (h : Data S P₁ P₂ z t a) {p q : G} (hp : p = 1 ∨ p = z) (hq : q = 1 ∨ q = z) :
    rr t p q = 1 ∨ rr t p q = z := by
  have hzz : z * z = 1 := h.z_sq
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rw [hp, hq]
  · left; exact Data.rr_one t
  · right; simp [rr, h.σ_z]
  · right; simp [rr]
  · left; simp [rr, h.σ_z, hzz]

theorem UHyp.exists_c [Finite G] (h : Data S P₁ P₂ z t a) {u : G} (hu : UHyp S P₁ P₂ z u) :
    ∃ c ∈ P₁, c * c = z ∧ (∀ g ∈ P₁, g * c * g⁻¹ = c ∨ g * c * g⁻¹ = z * c) ∧
      (u = rr t c c⁻¹ ∨ u = rr t c c⁻¹ * z) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := h.mem_R_iff.1 hu.mem
  have hzz : z * z = 1 := h.z_sq
  have hu2 : rr t (p * p) (q * q) = rr t 1 1 := by
    have e := hu.sq
    rw [h.rr_mul hq hp] at e
    rw [Data.rr_one]
    exact e
  have hsq := (h.rr_eq_iff (mul_mem hp hp) (mul_mem hq hq) (one_mem P₁) (one_mem P₁)).1 hu2
  have hcomm : ∀ g ∈ P₁, g * p * g⁻¹ = p ∨ g * p * g⁻¹ = z * p := by
    intro g hg
    have hn := hu.norm g (h.P₁_le hg)
    rw [h.gen_conj_rr₁ hg hq, h.gen_rr_mul_z_left hp hq] at hn
    have hgp : g * p * g⁻¹ ∈ P₁ := mul_mem (mul_mem hg hp) (inv_mem hg)
    rcases hn with e | e
    · left
      rcases (h.rr_eq_iff hgp hq hp hq).1 e with ⟨e1, -⟩ | ⟨-, e2⟩
      · exact e1.symm
      · exact absurd e2.symm (h.gen_z_mul_ne q)
    · right
      rcases (h.rr_eq_iff hgp hq (mul_mem h.z_mem₁ hp) hq).1 e with ⟨e1, -⟩ | ⟨-, e2⟩
      · exact e1.symm
      · exact absurd e2.symm (h.gen_z_mul_ne q)
  have hq' : q = p ∨ q = z * p := by
    have hn := hu.norm t h.t_mem
    rw [h.σ_rr hp hq, h.gen_rr_mul_z_left hp hq] at hn
    rcases hn with e | e
    · rcases (h.rr_eq_iff hq hp hp hq).1 e with ⟨e1, -⟩ | ⟨-, e2⟩
      · exact Or.inl e1.symm
      · exact Or.inr e2
    · exfalso
      rcases (h.rr_eq_iff hq hp (mul_mem h.z_mem₁ hp) hq).1 e with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact h.gen_z_mul_ne p (e1.trans e2)
      · exact h.gen_z_mul_ne p (e2.symm.trans (mul_left_cancel e1).symm)
  have hpp : p * p = z := by
    rcases hsq with ⟨e1, -⟩ | ⟨e1, -⟩
    · exfalso
      have hp1 : p * p = 1 := e1.symm
      have hpz := h.gen_eq_one_or_z_of_sq hp hp1
      have hqz : q = 1 ∨ q = z := by
        rcases hq' with hq1 | hq1 <;> rcases hpz with hpz | hpz
        · left; rw [hq1, hpz]
        · right; rw [hq1, hpz]
        · right; rw [hq1, hpz, mul_one]
        · left; rw [hq1, hpz, hzz]
      rcases h.gen_rr_one_or_z hpz hqz with e | e
      · exact hu.ne_one e
      · exact hu.ne_z e
    · calc p * p = z * (z * (p * p)) := by rw [← mul_assoc, hzz, one_mul]
        _ = z := by rw [← e1, mul_one]
  refine ⟨p, hp, hpp, hcomm, ?_⟩
  have hci : p⁻¹ = z * p := by
    apply inv_eq_of_mul_eq_one_left
    rw [mul_assoc, hpp, hzz]
  rcases hq' with hq1 | hq1
  · right
    rw [hq1, hci, ← h.z_cent' (h.gen_rr_mem_S hp (mul_mem h.z_mem₁ hp)), h.z_mul_rr_right hp,
      ← mul_assoc, hzz, one_mul]
  · left
    rw [hq1, hci]

theorem gen_qg_inv_a {a b : G} {N : ℕ} (h : QG a b N) : QG a⁻¹ b N where
  ord := by rw [orderOf_inv]; exact h.ord
  bsq := by rw [inv_pow, h.aN_inv]; exact h.bsq
  bcomm := by
    calc b * a⁻¹ = a * (a⁻¹ * b) * a⁻¹ := by group
      _ = a * (b * a) * a⁻¹ := by rw [h.bcomm]
      _ = a⁻¹⁻¹ * b := by group

theorem gen_span_inv_a {a b : G} {N : ℕ} (h : QG a b N) (hN : 1 ≤ N) {P : Subgroup G}
    (hspan : ∀ x ∈ P, ∃ k : ℕ, x = a ^ k ∨ x = a ^ k * b) :
    ∀ x ∈ P, ∃ k : ℕ, x = a⁻¹ ^ k ∨ x = a⁻¹ ^ k * b := by
  have hk : ∀ k : ℕ, a ^ k = a⁻¹ ^ (k * (2 * N - 1)) := by
    intro k
    rw [inv_pow]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add]
    obtain ⟨m, hm⟩ : ∃ m, m + 1 = 2 * N := ⟨2 * N - 1, by omega⟩
    have hm' : 2 * N - 1 = m := by omega
    rw [hm']
    calc a ^ (k + k * m) = a ^ (2 * N * k) := by
          congr 1
          calc k + k * m = k * (m + 1) := by ring
            _ = 2 * N * k := by rw [hm]; ring
      _ = 1 := by rw [pow_mul, h.a2N, one_pow]
  intro x hx
  obtain ⟨k, hk' | hk'⟩ := hspan x hx
  · exact ⟨k * (2 * N - 1), Or.inl (by rw [hk', hk k])⟩
  · exact ⟨k * (2 * N - 1), Or.inr (by rw [hk', hk k])⟩

theorem gen_q8_aux : ∀ c : QuaternionGroup 2, c * c ≠ 1 →
    ∃ b : QuaternionGroup 2, c ^ 4 = 1 ∧ b * b = c ^ 2 ∧ b * c = c⁻¹ * b ∧
      ∀ x : QuaternionGroup 2, ∃ k : Fin 4, x = c ^ (k : ℕ) ∨ x = c ^ (k : ℕ) * b := by
  decide

theorem gen_q8_gens {P : Subgroup G} (e : ↥P ≃* QuaternionGroup 2) {c : G} (hc : c ∈ P)
    (hc2 : c * c ≠ 1) :
    ∃ b : G, b ∈ P ∧ c ^ 4 = 1 ∧ b * b = c ^ 2 ∧ b * c = c⁻¹ * b ∧
      ∀ x ∈ P, ∃ k : ℕ, x = c ^ k ∨ x = c ^ k * b := by
  obtain ⟨b', h4, hb2, hbc, hspan⟩ := gen_q8_aux (e ⟨c, hc⟩) (by
    intro h1
    apply hc2
    have : (⟨c, hc⟩ : ↥P) * ⟨c, hc⟩ = 1 := by
      apply e.injective
      rw [map_mul, h1, map_one]
    exact congrArg Subtype.val this)
  have he : e (e.symm b') = b' := e.apply_symm_apply b'
  refine ⟨((e.symm b' : ↥P) : G), (e.symm b').2, ?_, ?_, ?_, ?_⟩
  · have : (⟨c, hc⟩ : ↥P) ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, h4, map_one]
    exact congrArg Subtype.val this
  · have : e.symm b' * e.symm b' = (⟨c, hc⟩ : ↥P) ^ 2 := by
      apply e.injective
      rw [map_mul, map_pow, he, hb2]
    exact congrArg Subtype.val this
  · have : e.symm b' * ⟨c, hc⟩ = (⟨c, hc⟩ : ↥P)⁻¹ * e.symm b' := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, he, hbc]
    exact congrArg Subtype.val this
  · intro x hx
    obtain ⟨k, hk | hk⟩ := hspan (e ⟨x, hx⟩)
    · refine ⟨k, Or.inl ?_⟩
      have : (⟨x, hx⟩ : ↥P) = (⟨c, hc⟩ : ↥P) ^ (k : ℕ) := by
        apply e.injective
        rw [map_pow]
        exact hk
      exact congrArg Subtype.val this
    · refine ⟨k, Or.inr ?_⟩
      have : (⟨x, hx⟩ : ↥P) = (⟨c, hc⟩ : ↥P) ^ (k : ℕ) * e.symm b' := by
        apply e.injective
        rw [map_mul, map_pow, he]
        exact hk
      exact congrArg Subtype.val this

theorem Data.exists_gens_of_c [Finite G] (h : Data S P₁ P₂ z t a) {c : G} (hc : c ∈ P₁)
    (hc2 : c * c = z) (hcomm : ∀ g ∈ P₁, g * c * g⁻¹ = c ∨ g * c * g⁻¹ = z * c) :
    ∃ (a₀ b₀ : G) (M : ℕ), a₀ ∈ P₁ ∧ b₀ ∈ P₁ ∧ 1 ≤ M ∧ 2 * M = 2 ^ (a - 2) ∧ QG a₀ b₀ (2 * M) ∧
      (∀ x ∈ P₁, ∃ k : ℕ, x = a₀ ^ k ∨ x = a₀ ^ k * b₀) ∧ a₀ ^ M = c := by
  obtain ⟨a₁, b₁, M, ha, hb, hM, hN, hqg, hspan⟩ := h.exists_gens
  have hz : z = a₁ ^ (2 * M) := (h.rel_of_gens ha hb hM hqg hspan).1
  have hzz : z * z = 1 := h.z_sq
  obtain ⟨k, hk | hk⟩ := hspan c hc
  ·
    have hcc : Commute c (a₁ ^ M) := by rw [hk]; exact (Commute.refl a₁).pow_pow k M
    have hMM : a₁ ^ M * a₁ ^ M = z := by rw [← pow_add, ← two_mul, hz]
    obtain ⟨d, hd⟩ : ∃ d, d = c * (a₁ ^ M)⁻¹ := ⟨_, rfl⟩
    have hcd : c = d * a₁ ^ M := by rw [hd]; group
    have hdd : d * d = 1 := by
      have hxc : (a₁ ^ M)⁻¹ * c = c * (a₁ ^ M)⁻¹ := hcc.inv_right.eq.symm
      have hxx : (a₁ ^ M)⁻¹ * (a₁ ^ M)⁻¹ = z := by
        rw [← mul_inv_rev, hMM, h.z_inv]
      calc d * d = c * (a₁ ^ M)⁻¹ * (c * (a₁ ^ M)⁻¹) := by rw [hd]
        _ = c * ((a₁ ^ M)⁻¹ * c) * (a₁ ^ M)⁻¹ := by simp only [mul_assoc]
        _ = c * (c * (a₁ ^ M)⁻¹) * (a₁ ^ M)⁻¹ := by rw [hxc]
        _ = (c * c) * ((a₁ ^ M)⁻¹ * (a₁ ^ M)⁻¹) := by simp only [mul_assoc]
        _ = 1 := by rw [hc2, hxx, hzz]
    have hdP : d ∈ P₁ := by rw [hd]; exact mul_mem hc (inv_mem (pow_mem ha M))
    rcases h.gen_eq_one_or_z_of_sq hdP hdd with hd1 | hdz
    · refine ⟨a₁, b₁, M, ha, hb, hM, hN, hqg, hspan, ?_⟩
      rw [hcd, hd1, one_mul]
    · refine ⟨a₁⁻¹, b₁, M, inv_mem ha, hb, hM, hN, gen_qg_inv_a hqg,
        gen_span_inv_a hqg (by omega) hspan, ?_⟩
      have hinv : (a₁ ^ M)⁻¹ = z * a₁ ^ M := by
        apply inv_eq_of_mul_eq_one_left
        rw [mul_assoc, hMM, hzz]
      rw [inv_pow, hinv, hcd, hdz]
  ·
    have hbinv : b₁ * a₁⁻¹ = a₁ * b₁ := by
      have := (gen_qg_inv_a hqg).bcomm
      rwa [inv_inv] at this
    have hconj : a₁ * c * a₁⁻¹ = a₁ ^ 2 * c := by
      rw [hk]
      calc a₁ * (a₁ ^ k * b₁) * a₁⁻¹ = a₁ * a₁ ^ k * (b₁ * a₁⁻¹) := by group
        _ = a₁ * a₁ ^ k * (a₁ * b₁) := by rw [hbinv]
        _ = a₁ ^ 2 * (a₁ ^ k * b₁) := by group
    have hM1 : M = 1 := by
      rcases hcomm a₁ ha with e | e
      · exfalso
        rw [hconj] at e
        have h1 : a₁ ^ 2 = 1 := mul_right_cancel (b := c) (by rw [e, one_mul])
        have h2 := Nat.le_of_dvd (by norm_num) (hqg.ord ▸ orderOf_dvd_of_pow_eq_one h1)
        omega
      · rw [hconj] at e
        have h1 : a₁ ^ 2 = a₁ ^ (2 * M) := by rw [← hz]; exact mul_right_cancel e
        have h2 : 2 * M < orderOf a₁ := by rw [hqg.ord]; omega
        have h3 : 2 < orderOf a₁ := by rw [hqg.ord]; omega
        have := pow_injOn_Iio_orderOf h3 h2 h1
        omega
    subst hM1
    have hn : 2 ^ (a - 2) = 2 := by simpa using hN.symm
    obtain ⟨-, ⟨e⟩⟩ := h.P₁_quat
    rw [hn] at e
    have hc2' : c * c ≠ 1 := by rw [hc2]; exact h.z_ne_one
    obtain ⟨b₀, hb₀, h4, hb2, hbc, hspan'⟩ := gen_q8_gens e hc hc2'
    refine ⟨c, b₀, 1, hc, hb₀, le_refl 1, hN, ⟨?_, hb2, hbc⟩, hspan', pow_one c⟩
    have h1 : ¬ c ^ 2 ^ 1 = 1 := by simpa [pow_two] using hc2'
    have h2 : c ^ 2 ^ (1 + 1) = 1 := by simpa using h4
    simpa using orderOf_eq_prime_pow h1 h2

theorem exists_canon_of_uhyp [Finite G] (h : Data S P₁ P₂ z t a) {u : G} (hu : UHyp S P₁ P₂ z u) :
    ∃ (t' a₀ b₀ : G) (M : ℕ), Canon S P₁ P₂ z t' a a₀ b₀ M ∧ u = xx t' a₀ M ∧
      Zc (P₁ ⊔ P₂) z t' = Zc (P₁ ⊔ P₂) z t ∧ Xc (P₁ ⊔ P₂) z t' = Xc (P₁ ⊔ P₂) z t := by
  obtain ⟨c, hc, hc2, hcomm, hu'⟩ := UHyp.exists_c h hu
  obtain ⟨a₀, b₀, M, ha, hb, hM1, hN, hqg, hspan, rfl⟩ := h.exists_gens_of_c hc hc2 hcomm
  have hC : Canon S P₁ P₂ z t a a₀ b₀ M := ⟨h, ha, hb, hM1, hN, hqg, hspan⟩
  rcases hu' with rfl | rfl
  · exact ⟨t, a₀, b₀, M, hC, hC.xx_eq_rr.symm, rfl, rfl⟩
  · have hg : b₀⁻¹ ∈ P₁ := inv_mem hb
    have hC' : Canon S P₁ P₂ z (b₀⁻¹ * t * b₀⁻¹⁻¹) a a₀ b₀ M :=
      ⟨h.gen_conj_t hg, ha, hb, hM1, hN, hqg, hspan⟩
    refine ⟨b₀⁻¹ * t * b₀⁻¹⁻¹, a₀, b₀, M, hC', ?_, gen_Zc_conj_t (mem_sup_left hg),
      h.gen_Xc_conj_t hg⟩
    have hcP : a₀ ^ M ∈ P₁ := hC.c_mem
    have e1 : b₀ * (a₀ ^ M)⁻¹ * b₀⁻¹ = z * (a₀ ^ M)⁻¹ := by
      calc b₀ * (a₀ ^ M)⁻¹ * b₀⁻¹ = (b₀ * a₀ ^ M * b₀⁻¹)⁻¹ := by group
        _ = ((a₀ ^ M)⁻¹)⁻¹ := by rw [hqg.b_conj M]
        _ = a₀ ^ M := inv_inv _
        _ = z * (a₀ ^ M)⁻¹ := by rw [hC.c_inv, ← mul_assoc, h.z_sq, one_mul]
    rw [hC'.xx_eq_rr, h.gen_rr_conj_t hg (inv_mem hcP), inv_inv, e1, ← h.z_mul_rr_right hcP]
    exact (h.z_cent' (h.gen_rr_mem_S hcP (inv_mem hcP))).symm

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
