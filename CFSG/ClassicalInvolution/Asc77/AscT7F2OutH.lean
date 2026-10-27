module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Quat

public section

namespace CFSG.ClassicalInvolution.Asc77.T7F2

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace Out

variable {G : Type} [Group G] {R N : Subgroup G} {a b : G} {n : ℕ}

structure Setting (R N : Subgroup G) (a b : G) (n : ℕ) : Prop where
  coord : QuatCoord R a b n
  hRN : R ≤ N
  hNR : ∀ y ∈ N, conjSub y R = R
  hNa : ∀ y ∈ N, conjSub y (Subgroup.zpowers a) = Subgroup.zpowers a

variable (s : Setting R N a b n)

include s

theorem Setting.conj_mem_R {m : G} (hm : m ∈ N) {r : G} (hr : r ∈ R) : m * r * m⁻¹ ∈ R := by
  have := conj_mem_conjSub (n := m) hr
  rwa [s.hNR m hm] at this

theorem Setting.conj_mem_a {m : G} (hm : m ∈ N) {x : G} (hx : x ∈ Subgroup.zpowers a) :
    m * x * m⁻¹ ∈ Subgroup.zpowers a := by
  have := conj_mem_conjSub (n := m) hx
  rwa [s.hNa m hm] at this

theorem Setting.conj_mem_a' {m : G} (hm : m ∈ N) {x : G} (hx : x ∈ Subgroup.zpowers a) :
    m⁻¹ * x * m ∈ Subgroup.zpowers a := by
  have hx' : x ∈ conjSub m (Subgroup.zpowers a) := by rw [s.hNa m hm]; exact hx
  rwa [mem_conjSub_iff] at hx'

theorem Setting.coord_of_mem {m : G} (hm : m ∈ N) :
    ∃ i j : ℤ, Odd i ∧ m * a * m⁻¹ = a ^ i ∧ m * b * m⁻¹ = b * a ^ j := by
  have c := s.coord
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (s.conj_mem_a hm (Subgroup.mem_zpowers a))
  have hodd : Odd i := by
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    obtain ⟨t, ht⟩ := hev
    have h1 : (a ^ i) ^ (2 ^ n) = 1 := by
      rw [← zpow_natCast, ← zpow_mul, ht]
      have : (t + t) * ((2 ^ n : ℕ) : ℤ) = ((2 ^ (n + 1) : ℕ) : ℤ) * t := by push_cast; ring
      rw [this, zpow_mul, zpow_natCast, c.pow_card, one_zpow]
    have h2 : orderOf (a ^ i) = 2 ^ (n + 1) := by
      rw [hi]
      have := MulEquiv.orderOf_eq (MulAut.conj m) a
      simp only [MulAut.conj_apply] at this
      rw [this, c.hord]
    have := orderOf_dvd_of_pow_eq_one h1
    rw [h2] at this
    have h3 := Nat.le_of_dvd (by positivity) this
    have h4 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hbR : m * b * m⁻¹ ∈ R := s.conj_mem_R hm c.hb
  rcases c.cover _ hbR with ⟨k, hk⟩ | ⟨j, hj⟩
  · exfalso
    apply c.b_not_mem
    have h1 : b = m⁻¹ * (m * b * m⁻¹) * m := by group
    have h2 : m⁻¹ * a ^ k * m = (m⁻¹ * a * m) ^ k := by
      have := (conj_zpow (a := m⁻¹) (b := a) (i := k)).symm
      simpa using this
    rw [h1, hk, h2]
    exact Subgroup.zpow_mem _ (s.conj_mem_a' hm (Subgroup.mem_zpowers a)) k
  · exact ⟨i, j, hodd, hi.symm, hj⟩


omit s in
theorem coord_mul_a {m₁ m₂ : G} {i₁ i₂ : ℤ} (h₁a : m₁ * a * m₁⁻¹ = a ^ i₁)
    (h₂a : m₂ * a * m₂⁻¹ = a ^ i₂) : (m₁ * m₂) * a * (m₁ * m₂)⁻¹ = a ^ (i₁ * i₂) := by
  calc (m₁ * m₂) * a * (m₁ * m₂)⁻¹ = m₁ * (m₂ * a * m₂⁻¹) * m₁⁻¹ := by group
    _ = m₁ * a ^ i₂ * m₁⁻¹ := by rw [h₂a]
    _ = (m₁ * a * m₁⁻¹) ^ i₂ := (conj_zpow).symm
    _ = a ^ (i₁ * i₂) := by rw [h₁a, ← zpow_mul]

omit s in
theorem coord_mul_b {m₁ m₂ : G} {i₁ j₁ j₂ : ℤ} (h₁a : m₁ * a * m₁⁻¹ = a ^ i₁)
    (h₁b : m₁ * b * m₁⁻¹ = b * a ^ j₁) (h₂b : m₂ * b * m₂⁻¹ = b * a ^ j₂) :
    (m₁ * m₂) * b * (m₁ * m₂)⁻¹ = b * a ^ (j₁ + i₁ * j₂) := by
  calc (m₁ * m₂) * b * (m₁ * m₂)⁻¹ = m₁ * (m₂ * b * m₂⁻¹) * m₁⁻¹ := by group
    _ = m₁ * (b * a ^ j₂) * m₁⁻¹ := by rw [h₂b]
    _ = (m₁ * b * m₁⁻¹) * (m₁ * a ^ j₂ * m₁⁻¹) := by group
    _ = (b * a ^ j₁) * (m₁ * a * m₁⁻¹) ^ j₂ := by rw [h₁b, conj_zpow]
    _ = b * a ^ (j₁ + i₁ * j₂) := by rw [h₁a, ← zpow_mul, mul_assoc, ← zpow_add]

omit s in
theorem even_of_zpow_eq_one' (c : QuatCoord R a b n) {t : ℤ} (h : a ^ t = 1) :
    Even t := by
  have h0 : a ^ t = a ^ (0 : ℤ) := by rw [h, zpow_zero]
  rw [c.zpow_eq_iff, sub_zero] at h0
  have h2 : (2 : ℤ) ∣ t := (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans h0
  exact even_iff_two_dvd.mpr h2

@[expose] def Hsub : Subgroup G where
  carrier := {m | m ∈ N ∧ ∃ j : ℤ, Even j ∧ m * b * m⁻¹ = b * a ^ j}
  one_mem' := ⟨N.one_mem, 0, ⟨0, rfl⟩, by simp⟩
  mul_mem' := by
    rintro m₁ m₂ ⟨hm₁, j₁, hj₁, h₁b⟩ ⟨hm₂, j₂, hj₂, h₂b⟩
    obtain ⟨i₁, -, hi₁, h₁a, -⟩ := s.coord_of_mem hm₁
    refine ⟨N.mul_mem hm₁ hm₂, j₁ + i₁ * j₂, ?_, coord_mul_b h₁a h₁b h₂b⟩
    exact hj₁.add (hj₂.mul_left i₁)
  inv_mem' := by
    rintro m ⟨hm, j, hj, hb⟩
    have hm' : m⁻¹ ∈ N := N.inv_mem hm
    obtain ⟨i', j', hodd', ha', hb'⟩ := s.coord_of_mem hm'
    simp only [inv_inv] at ha' hb'
    refine ⟨hm', j', ?_, by simpa using hb'⟩
    have h1 : a ^ (j' + i' * j) = 1 := by
      have e : b = m⁻¹ * (b * a ^ j) * m := by rw [← hb]; group
      have e2 : m⁻¹ * (b * a ^ j) * m = (m⁻¹ * b * m) * (m⁻¹ * a * m) ^ j := by
        have := (conj_zpow (a := m⁻¹) (b := a) (i := j)).symm
        simp only [inv_inv] at this
        calc m⁻¹ * (b * a ^ j) * m = (m⁻¹ * b * m) * (m⁻¹ * a ^ j * m) := by group
          _ = (m⁻¹ * b * m) * (m⁻¹ * a * m) ^ j := by rw [this]
      rw [e2, hb', ha', ← zpow_mul, mul_assoc, ← zpow_add] at e
      have e3 : b * a ^ (j' + i' * j) = b * 1 := by rw [mul_one]; exact e.symm
      exact mul_left_cancel e3
    have h2 : Even (j' + i' * j) := even_of_zpow_eq_one' s.coord h1
    have h3 : Even (i' * j) := hj.mul_left i'
    exact (Int.even_add.mp h2).mpr h3

theorem mem_Hsub {m : G} : m ∈ Hsub s ↔ m ∈ N ∧ ∃ j : ℤ, Even j ∧ m * b * m⁻¹ = b * a ^ j :=
  Iff.rfl


theorem R_le_Hsub : R ≤ Hsub s := by
  have c := s.coord
  intro r hr
  refine ⟨s.hRN hr, ?_⟩
  rcases c.cover r hr with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · refine ⟨-2 * k, ⟨-k, by ring⟩, ?_⟩
    calc a ^ k * b * (a ^ k)⁻¹ = (a ^ k * b) * (a ^ k)⁻¹ := rfl
      _ = (b * a ^ (-k)) * (a ^ k)⁻¹ := by rw [c.zpow_a_mul_b]
      _ = b * (a ^ (-k) * a ^ (-k)) := by group
      _ = b * a ^ (-2 * k) := by rw [← zpow_add]; ring_nf
  · refine ⟨2 * k, ⟨k, by ring⟩, ?_⟩
    calc b * a ^ k * b * (b * a ^ k)⁻¹ = b * (a ^ k * b) * a ^ (-k) * b⁻¹ := by group
      _ = b * (b * a ^ (-k)) * a ^ (-k) * b⁻¹ := by rw [c.zpow_a_mul_b]
      _ = b * (b * a ^ (-k + -k) * b⁻¹) := by rw [zpow_add]; group
      _ = b * a ^ (2 * k) := by
        rw [c.conj_zpow]; congr 1; congr 1; ring

theorem centralizer_le_Hsub : N ⊓ Subgroup.centralizer (R : Set G) ≤ Hsub s := by
  rintro m ⟨hm, hmc⟩
  refine ⟨hm, 0, ⟨0, rfl⟩, ?_⟩
  have := (Subgroup.mem_centralizer_iff.mp hmc) b s.coord.hb
  rw [zpow_zero, mul_one, ← this]
  group

theorem sup_le_Hsub : R ⊔ (N ⊓ Subgroup.centralizer (R : Set G)) ≤ Hsub s :=
  sup_le (R_le_Hsub s) (centralizer_le_Hsub s)

theorem mul_mem_Hsub_of_not_mem {m₁ m₂ : G} (hm₁ : m₁ ∈ N) (hm₂ : m₂ ∈ N) (h₁ : m₁ ∉ Hsub s)
    (h₂ : m₂ ∉ Hsub s) : m₁ * m₂ ∈ Hsub s := by
  obtain ⟨i₁, j₁, hi₁, h₁a, h₁b⟩ := s.coord_of_mem hm₁
  obtain ⟨i₂, j₂, hi₂, h₂a, h₂b⟩ := s.coord_of_mem hm₂
  have hj₁ : ¬ Even j₁ := fun h => h₁ ⟨hm₁, j₁, h, h₁b⟩
  have hj₂ : ¬ Even j₂ := fun h => h₂ ⟨hm₂, j₂, h, h₂b⟩
  refine ⟨N.mul_mem hm₁ hm₂, j₁ + i₁ * j₂, ?_, coord_mul_b h₁a h₁b h₂b⟩
  rw [Int.not_even_iff_odd] at hj₁ hj₂
  exact hj₁.add_odd (hi₁.mul hj₂)

theorem Hsub_relIndex_le : (Hsub s).relIndex N ≤ 2 := by
  by_cases hH : N ≤ Hsub s
  · rw [Subgroup.relIndex_eq_one.mpr hH]; norm_num
  · obtain ⟨x₀, hx₀N, hx₀H⟩ := Set.not_subset.mp hH
    have h2 : (Hsub s).relIndex N = 2 := by
      unfold Subgroup.relIndex
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨x₀, hx₀N⟩, fun y => ?_⟩
      obtain ⟨m, hm⟩ := y
      by_cases hmH : m ∈ Hsub s
      · have h1 : (⟨m, hm⟩ : ↥N) ∈ (Hsub s).subgroupOf N := hmH
        have h2 : (⟨m, hm⟩ * ⟨x₀, hx₀N⟩ : ↥N) ∉ (Hsub s).subgroupOf N := by
          intro h
          have h' : m * x₀ ∈ Hsub s := h
          exact hx₀H (by simpa using (Hsub s).mul_mem ((Hsub s).inv_mem hmH) h')
        exact Or.inr ⟨h1, h2⟩
      · have h1 : (⟨m, hm⟩ : ↥N) ∉ (Hsub s).subgroupOf N := hmH
        have h2 : (⟨m, hm⟩ * ⟨x₀, hx₀N⟩ : ↥N) ∈ (Hsub s).subgroupOf N :=
          mul_mem_Hsub_of_not_mem s hm hx₀N hmH hx₀H
        exact Or.inl ⟨h2, h1⟩
    rw [h2]


omit s in
theorem adjust (c : QuatCoord R a b n) {m : G} {i j : ℤ} (hi : Odd i) (hj : Even j)
    (ha : m * a * m⁻¹ = a ^ i) (hb : m * b * m⁻¹ = b * a ^ j) :
    ∃ k : ℤ, (m * a ^ k) * a * (m * a ^ k)⁻¹ = a ^ i ∧ (m * a ^ k) * b * (m * a ^ k)⁻¹ = b := by
  obtain ⟨j₀, hj₀⟩ := hj
  have hcop : IsCoprime i ((2 : ℤ) ^ (n + 1)) :=
    (Int.isCoprime_two_right.mpr hi).pow_right
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨j₀ * u, ?_, ?_⟩
  · calc (m * a ^ (j₀ * u)) * a * (m * a ^ (j₀ * u))⁻¹
        = m * (a ^ (j₀ * u) * a * (a ^ (j₀ * u))⁻¹) * m⁻¹ := by group
      _ = m * a * m⁻¹ := by
        rw [(Commute.zpow_left (Commute.refl a) (j₀ * u)).eq]; group
      _ = a ^ i := ha
  · have hk : a ^ (j - 2 * (j₀ * u) * i) = 1 := by
      have h0 : a ^ (j - 2 * (j₀ * u) * i) = a ^ (0 : ℤ) := by
        rw [c.zpow_eq_iff, sub_zero]
        refine ⟨2 * j₀ * v, ?_⟩
        have : j = 2 * j₀ := by rw [hj₀]; ring
        rw [this]
        linear_combination (-(2 * j₀)) * huv
      rwa [zpow_zero] at h0
    calc (m * a ^ (j₀ * u)) * b * (m * a ^ (j₀ * u))⁻¹
        = m * (a ^ (j₀ * u) * b * (a ^ (j₀ * u))⁻¹) * m⁻¹ := by group
      _ = m * (b * a ^ (-2 * (j₀ * u))) * m⁻¹ := by
        congr 2
        calc a ^ (j₀ * u) * b * (a ^ (j₀ * u))⁻¹
            = (a ^ (j₀ * u) * b) * (a ^ (j₀ * u))⁻¹ := rfl
          _ = (b * a ^ (-(j₀ * u))) * (a ^ (j₀ * u))⁻¹ := by rw [c.zpow_a_mul_b]
          _ = b * (a ^ (-(j₀ * u)) * a ^ (-(j₀ * u))) := by group
          _ = b * a ^ (-2 * (j₀ * u)) := by rw [← zpow_add]; ring_nf
      _ = (m * b * m⁻¹) * (m * a * m⁻¹) ^ (-2 * (j₀ * u)) := by
        rw [conj_zpow]; group
      _ = b * a ^ (j - 2 * (j₀ * u) * i) := by
        rw [hb, ha, ← zpow_mul, mul_assoc, ← zpow_add]
        congr 2
        ring
      _ = b := by rw [hk, mul_one]

omit s in
theorem centralizes_of_fixes (c : QuatCoord R a b n) {m : G} (ha : m * a * m⁻¹ = a)
    (hb : m * b * m⁻¹ = b) : ∀ r ∈ R, r * m = m * r := by
  intro r hr
  have hma : m * a = a * m := by
    have := congrArg (· * m) ha; simpa [mul_assoc] using this
  have hmb : m * b = b * m := by
    have := congrArg (· * m) hb; simpa [mul_assoc] using this
  have hma' : ∀ i : ℤ, m * a ^ i = a ^ i * m := fun i =>
    (Commute.zpow_right (show Commute m a from hma) i).eq
  rcases c.cover r hr with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact (hma' i).symm
  · calc b * a ^ i * m = b * (a ^ i * m) := by group
      _ = b * (m * a ^ i) := by rw [hma']
      _ = (b * m) * a ^ i := by group
      _ = (m * b) * a ^ i := by rw [hmb]
      _ = m * (b * a ^ i) := by group


theorem mem_sup_of_cong {m : G} (hm : m ∈ N) {i j : ℤ} (hi : Odd i) (hj : Even j)
    (ha : m * a * m⁻¹ = a ^ i) (hb : m * b * m⁻¹ = b * a ^ j)
    (hcong : a ^ i = a ∨ a ^ i = a⁻¹) :
    m ∈ R ⊔ (N ⊓ Subgroup.centralizer (R : Set G)) := by
  have c := s.coord
  obtain ⟨k, hka, hkb⟩ := adjust c hi hj ha hb
  have hak : a ^ k ∈ R := R.zpow_mem c.ha k
  have hm₁ : m * a ^ k ∈ N := N.mul_mem hm (s.hRN hak)
  have hmk : m = (m * a ^ k) * (a ^ k)⁻¹ := by group
  rcases hcong with h | h
  · rw [h] at hka
    have hcent : m * a ^ k ∈ N ⊓ Subgroup.centralizer (R : Set G) :=
      ⟨hm₁, Subgroup.mem_centralizer_iff.mpr (centralizes_of_fixes c hka hkb)⟩
    have := Subgroup.mul_mem_sup hcent (R.inv_mem hak)
    rw [sup_comm] at this
    rw [hmk]
    exact this
  · have hm₂ : m * a ^ k * b ∈ N := N.mul_mem hm₁ (s.hRN c.hb)
    have hka2 : (m * a ^ k * b) * a * (m * a ^ k * b)⁻¹ = a := by
      calc (m * a ^ k * b) * a * (m * a ^ k * b)⁻¹
          = (m * a ^ k) * (b * a * b⁻¹) * (m * a ^ k)⁻¹ := by group
        _ = (m * a ^ k) * a⁻¹ * (m * a ^ k)⁻¹ := by rw [c.hbab]
        _ = ((m * a ^ k) * a * (m * a ^ k)⁻¹)⁻¹ := by group
        _ = a := by rw [hka, h]; group
    have hkb2 : (m * a ^ k * b) * b * (m * a ^ k * b)⁻¹ = b := by
      calc (m * a ^ k * b) * b * (m * a ^ k * b)⁻¹
          = (m * a ^ k) * b * (m * a ^ k)⁻¹ := by group
        _ = b := hkb
    have hcent : m * a ^ k * b ∈ N ⊓ Subgroup.centralizer (R : Set G) :=
      ⟨hm₂, Subgroup.mem_centralizer_iff.mpr (centralizes_of_fixes c hka2 hkb2)⟩
    have hbk : (b * a ^ k)⁻¹ ∈ R := R.inv_mem (R.mul_mem c.hb hak) |> fun h => by
      simpa using h
    have h3 : m = (m * a ^ k * b) * (b⁻¹ * (a ^ k)⁻¹) := by group
    have := Subgroup.mul_mem_sup hcent (R.mul_mem (R.inv_mem c.hb) (R.inv_mem hak))
    rw [sup_comm] at this
    rw [h3]
    exact this

end Out

end CFSG.ClassicalInvolution.Asc77.T7F2
