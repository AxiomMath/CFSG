module

public import CFSG.GH74.GLS.C3.Layer1.St1P89Basic
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.St1Thm4
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.Uniqueness.SU.SU1

section Tools

variable {G : Type} [Group G]

variable {G : Type} [Group G]

theorem card_sup_of_commute {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  rw [← Nat.card_prod]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun p : ↥A × ↥B => (⟨(p.1 : G) * p.2, ?_⟩ : ↥(A ⊔ B))) ⟨?_, ?_⟩
  · exact Subgroup.mul_mem_sup p.1.2 p.2.2
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h1 : a * b = a' * b' := congrArg Subtype.val h
    have h2 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    have hmem : a'⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem ha') ha, h2 ▸ B.mul_mem hb' (B.inv_mem hb)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have : a = a' := by
      calc a = a' * (a'⁻¹ * a) := by group
        _ = a' := by rw [hmem, mul_one]
    have hb2 : b = b' := by
      have : b' * b⁻¹ = 1 := by rw [← h2, hmem]
      calc b = (b' * b⁻¹)⁻¹ * b' := by group
        _ = b' := by rw [this]; group
    subst this; subst hb2; rfl
  · rintro ⟨g, hg⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hAB hg
    exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩

theorem mem_zpowers_of_sq {a g : G} (ha : a ^ 2 = 1) (hg : g ∈ zpowers a) : g = 1 ∨ g = a := by
  obtain ⟨n, rfl⟩ := hg
  have h2 : a ^ (2 : ℤ) = 1 := by exact_mod_cast ha
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    show a ^ (2 * k) = 1
    rw [zpow_mul, h2, one_zpow]
  · right
    show a ^ (2 * k + 1) = a
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem card_zpowers_two {a : G} (ha : a ^ 2 = 1) (h1 : a ≠ 1) : Nat.card ↥(zpowers a) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime ha h1

theorem isElemAbelian_pair {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a) :
    Open.IsElemAbelian 2 (zpowers a ⊔ zpowers b) := by
  refine IsElemAbelian.sup (isElemAbelian_zpowers ha) (isElemAbelian_zpowers hb) ?_
  intro x hx y hy
  rcases mem_zpowers_of_sq ha hx with rfl | rfl <;> rcases mem_zpowers_of_sq hb hy with rfl | rfl <;>
    simp [hab]

theorem card_klein {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hne : a ≠ b) : Nat.card ↥(zpowers a ⊔ zpowers b) = 4 := by
  have hcomm : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
    intro x hx y hy
    rcases mem_zpowers_of_sq ha hx with rfl | rfl <;> rcases mem_zpowers_of_sq hb hy with rfl | rfl <;>
      simp [hab]
  have hinf : zpowers a ⊓ zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro g ⟨hga, hgb⟩
    rcases mem_zpowers_of_sq ha hga with rfl | rfl
    · exact Subgroup.one_mem _
    · rcases mem_zpowers_of_sq hb hgb with h | h
      · exact absurd h ha1
      · exact absurd h hne
  rw [card_sup_of_commute hcomm hinf, card_zpowers_two ha ha1, card_zpowers_two hb hb1]

end Tools

section Star2

variable {G : Type} [Group G] [Finite G]

theorem isStar2_of_elem16 (hr : pRank 2 G = 4) {E : Subgroup G} (hE : Open.IsElemAbelian 2 E)
    (hcard : Nat.card ↥E = 16) {t : G} (htE : t ∈ E) (ht1 : t ≠ 1) : IsStar2 t := by
  have hcomm := (isElemAbelian_iff.mp hE).1
  have hsq := (isElemAbelian_iff.mp hE).2
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by simpa using hsq t htE) ht1
  refine ⟨ht2, le_antisymm (Bg.pRank_subgroup_le one_lt_two _) ?_⟩
  have hEC : E ≤ centralizer ({t} : Set G) := by
    intro e he
    rw [mem_centralizer_singleton_iff]
    exact (hcomm e he t htE)
  have hEA : CFSG.IsElementaryAbelian 2 ↥E := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mpr hE
  have := le_pRank_of_elem hEC hEA (k := 4) (by rw [hcard]; norm_num)
  rw [hr]
  exact this

end Star2

section PD8

variable {G : Type} [Group G] [Finite G] {T P Q : Subgroup G} {u z x f r s : G}

theorem Cfg89T.s_r2 (c : Cfg89T G T P Q u z x f r s) : s * r ^ 2 = r ^ 2 * s := by
  have h := c.z_comm_s
  rw [c.z_eq] at h
  exact h.symm

theorem Cfg89T.s_r3 (c : Cfg89T G T P Q u z x f r s) : s * r ^ 3 = r * s := by
  calc s * r ^ 3 = s * r ^ 2 * r := by group
    _ = r ^ 2 * s * r := by rw [c.s_r2]
    _ = r ^ 2 * (s * r) := by group
    _ = r ^ 2 * (r ^ 3 * s) := by rw [c.s_r]
    _ = r ^ 5 * s := by group
    _ = r * s := by
      have : r ^ 5 = r ^ 4 * r := by group
      rw [this, c.r4, one_mul]

theorem Cfg89T.P_inv (c : Cfg89T G T P Q u z x f r s) {p : G} (hp : p ∈ P) (hp2 : p ^ 2 = 1) :
    p = 1 ∨ p = z ∨ p = s ∨ p = z * s ∨ p = r * s ∨ p = z * (r * s) := by
  obtain ⟨i, j, rfl⟩ := c.P_gen p hp
  have hz : z = r ^ 2 := c.z_eq
  rw [pow_eq_pow_mod i c.r4, pow_eq_pow_mod j c.s2] at hp2 ⊢
  have hi : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hj : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize i % 4 = a at hi hp2 ⊢
  generalize j % 2 = b at hj hp2 ⊢
  interval_cases a <;> interval_cases b <;> simp at hp2 ⊢
  · exact absurd hp2 c.r2_ne
  · exact Or.inr (Or.inl hz.symm)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hz.symm)))
  · exfalso
    apply c.r2_ne
    have : (r ^ 3) ^ 2 = r ^ 2 := by
      calc (r ^ 3) ^ 2 = r ^ 4 * r ^ 2 := by group
        _ = r ^ 2 := by rw [c.r4, one_mul]
    rw [← this]; exact hp2
  · right; right; right; right; right
    rw [hz]; group

theorem Cfg89T.r_ne_inv (c : Cfg89T G T P Q u z x f r s) : r ≠ r⁻¹ := by
  intro h
  apply c.r2_ne
  calc r ^ 2 = r * r := sq r
    _ = r * r⁻¹ := by rw [← h]
    _ = 1 := mul_inv_cancel r

theorem Cfg89T.s_ne_one (c : Cfg89T G T P Q u z x f r s) : s ≠ 1 := by
  intro h
  apply c.r_ne_inv
  have := c.srs
  rwa [h, inv_one, one_mul, mul_one] at this

theorem Cfg89T.s_ne_z (c : Cfg89T G T P Q u z x f r s) : s ≠ z := by
  intro h
  apply c.r_ne_inv
  have hzr : z * r = r * z := by rw [c.z_eq]; group
  have := c.srs
  rw [h] at this
  calc r = z * r * z⁻¹ := by rw [hzr]; group
    _ = r⁻¹ := this

theorem Cfg89T.rs_sq (c : Cfg89T G T P Q u z x f r s) : (r * s) ^ 2 = 1 := by
  have h : s * r * s⁻¹ = r⁻¹ := c.srs
  calc (r * s) ^ 2 = r * s * (r * s) := sq _
    _ = r * (s * r * s⁻¹) * (s * s) := by group
    _ = r * r⁻¹ * (s * s) := by rw [h]
    _ = 1 := by rw [mul_inv_cancel, one_mul, ← sq, c.s2]

theorem Cfg89T.rs_ne_one (c : Cfg89T G T P Q u z x f r s) : r * s ≠ 1 := by
  intro h
  have hs : s = r⁻¹ := by
    calc s = r⁻¹ * (r * s) := by group
      _ = r⁻¹ := by rw [h, mul_one]
  apply c.r_ne_inv
  have := c.srs
  rw [hs] at this
  calc r = r⁻¹ * r * r⁻¹⁻¹ := by group
    _ = r⁻¹ := this

theorem Cfg89T.rs_ne_z (c : Cfg89T G T P Q u z x f r s) : r * s ≠ z := by
  intro h
  have hs : s = r := by
    rw [c.z_eq] at h
    have : r * s = r * r := by rw [h, sq]
    exact mul_left_cancel this
  apply c.r_ne_inv
  have := c.srs
  rw [hs] at this
  calc r = r * r * r⁻¹ := by group
    _ = r⁻¹ := this

theorem Cfg89T.key_r2 (c : Cfg89T G T P Q u z x f r s) {k : ℕ} (h : r ^ k * s = r ^ (k + 2) * s) : False := by
  have h1 : r ^ k = r ^ (k + 2) := mul_right_cancel h
  apply c.r2_ne
  have : r ^ k * 1 = r ^ k * r ^ 2 := by rw [mul_one, ← pow_add]; exact h1
  exact (mul_left_cancel this).symm

theorem Cfg89T.s_comm_r_false (c : Cfg89T G T P Q u z x f r s) (h : s * r = r * s) : False := by
  apply c.key_r2 (k := 1)
  calc r ^ 1 * s = s * r := by rw [pow_one, h]
    _ = r ^ 3 * s := c.s_r
    _ = r ^ (1 + 2) * s := rfl

theorem Cfg89T.P_center (c : Cfg89T G T P Q u z x f r s) {p : G} (hp : p ∈ P)
    (hc : ∀ p' ∈ P, p * p' = p' * p) : p = 1 ∨ p = z := by
  obtain ⟨i, j, rfl⟩ := c.P_gen p hp
  have h1 := hc r c.r_mem
  have h2 := hc s c.s_mem
  rw [pow_eq_pow_mod i c.r4, pow_eq_pow_mod j c.s2] at h1 h2 ⊢
  have hi : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hj : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize i % 4 = a at hi h1 h2 ⊢
  generalize j % 2 = b at hj h1 h2 ⊢
  have hz : z = r ^ 2 := c.z_eq
  have hsr := c.s_r
  have hsr3 := c.s_r3
  have hr4 := c.r4
  interval_cases a <;> interval_cases b <;> simp at h1 h2 ⊢
  · exact (c.s_comm_r_false h1).elim
  · exact (c.s_comm_r_false h2.symm).elim
  · apply (c.s_comm_r_false _).elim
    have h3 : r * (s * r) = r * (r * s) := by rw [← mul_assoc]; exact h1
    exact mul_left_cancel h3
  · exact Or.inr hz.symm
  · exfalso
    apply c.key_r2 (k := 1)
    calc r ^ 1 * s = r ^ 5 * s := by
          have : r ^ 5 = r ^ 4 * r := by group
          rw [this, hr4, one_mul, pow_one]
      _ = r ^ 2 * (r ^ 3 * s) := by group
      _ = r ^ 2 * (s * r) := by rw [hsr]
      _ = r ^ 2 * s * r := by group
      _ = r * (r ^ 2 * s) := h1
      _ = r ^ 3 * s := by group
      _ = r ^ (1 + 2) * s := rfl
  · exfalso
    apply c.key_r2 (k := 1)
    calc r ^ 1 * s = s * r ^ 3 := by rw [pow_one, hsr3]
      _ = r ^ 3 * s := h2.symm
      _ = r ^ (1 + 2) * s := rfl
  · exfalso
    apply c.key_r2 (k := 0)
    calc r ^ 0 * s = r * (r ^ 3 * s) := by
          have : r * r ^ 3 = r ^ 4 := by group
          rw [← mul_assoc, this, hr4]; simp
      _ = r ^ 3 * s * r := h1.symm
      _ = r ^ 3 * (s * r) := by group
      _ = r ^ 3 * (r ^ 3 * s) := by rw [hsr]
      _ = r ^ 6 * s := by group
      _ = r ^ (0 + 2) * s := by
          have : r ^ 6 = r ^ 4 * r ^ 2 := by group
          rw [this, hr4, one_mul]

end PD8

end CFSG.GH74.GLS.C3.Layer1.P89
