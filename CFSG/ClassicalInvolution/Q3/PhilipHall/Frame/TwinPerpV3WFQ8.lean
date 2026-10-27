module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG.ClassicalInvolution.Generic QuaternionGroup

section Decide

private theorem q8_exists_noncomm : ∀ k : QuaternionGroup 2, k ≠ 1 → k ≠ a 2 →
    ∃ m : QuaternionGroup 2, k * m ≠ m * k := by
  decide +kernel

private theorem q8_comm_eq : ∀ k m : QuaternionGroup 2, k * m ≠ m * k → k * m * k⁻¹ * m⁻¹ = a 2 := by
  decide +kernel

private theorem q8_cent_cyc : ∀ k d : QuaternionGroup 2, k * k = a 2 → d * k = k * d →
    d = 1 ∨ d = k ∨ d = a 2 ∨ d = k * a 2 := by
  decide +kernel

private theorem q8_gen : ∀ k m g : QuaternionGroup 2, k * m ≠ m * k →
    ∃ i : Fin 4, ∃ j : Fin 2, g = k ^ (i : ℕ) * m ^ (j : ℕ) := by
  decide +kernel

private theorem q8_sq_cases : ∀ q : QuaternionGroup 2, q * q = 1 ∨ q * q = a 2 := by decide +kernel

private theorem q8_inv : ∀ q : QuaternionGroup 2, q * q = 1 → q ≠ 1 → q = a 2 := by decide +kernel

private theorem q8_prod3 : ∀ k₁ k₂ k₃ : QuaternionGroup 2, k₁ * k₁ = a 2 → k₂ * k₂ = a 2 →
    k₃ * k₃ = a 2 → k₂ ≠ k₁ → k₂ ≠ k₁ * a 2 → k₃ ≠ k₁ → k₃ ≠ k₁ * a 2 → k₃ ≠ k₂ → k₃ ≠ k₂ * a 2 →
    k₁ * k₂ * k₃ = 1 ∨ k₁ * k₂ * k₃ = a 2 := by
  decide +kernel

private theorem q8_central : ∀ q : QuaternionGroup 2, (∀ g : QuaternionGroup 2, q * g = g * q) →
    q = 1 ∨ q = a 2 := by
  decide +kernel

private theorem q8_a2_central : ∀ q : QuaternionGroup 2, a 2 * q = q * a 2 := by decide +kernel

private theorem q8_exists_ord4 : ∃ q : QuaternionGroup 2, q * q = a 2 := ⟨a 1, by decide +kernel⟩

end Decide

structure Q8Facts {Y : Type*} [Group Y] (M : Subgroup Y) (z : Y) : Prop where
  z_mem : z ∈ M
  z_ne : z ≠ 1
  z_sq : z * z = 1
  z_central : ∀ m ∈ M, z * m = m * z
  sq_cases : ∀ m ∈ M, m * m = 1 ∨ m * m = z
  sq_one : ∀ m ∈ M, m * m = 1 → m = 1 ∨ m = z
  center : ∀ m ∈ M, (∀ g ∈ M, m * g = g * m) → m = 1 ∨ m = z
  exists_noncomm : ∀ k ∈ M, k ≠ 1 → k ≠ z → ∃ m ∈ M, k * m ≠ m * k
  comm_eq : ∀ k ∈ M, ∀ m ∈ M, k * m ≠ m * k → k * m * k⁻¹ * m⁻¹ = z
  cent_cyc : ∀ k ∈ M, k * k = z → ∀ d ∈ M, d * k = k * d → d = 1 ∨ d = k ∨ d = z ∨ d = k * z
  gen : ∀ k ∈ M, ∀ m ∈ M, k * m ≠ m * k → ∀ g ∈ M,
    ∃ i : ℕ, i < 4 ∧ ∃ j : ℕ, j < 2 ∧ g = k ^ i * m ^ j
  prod3 : ∀ k₁ ∈ M, ∀ k₂ ∈ M, ∀ k₃ ∈ M, k₁ * k₁ = z → k₂ * k₂ = z → k₃ * k₃ = z →
    k₂ ≠ k₁ → k₂ ≠ k₁ * z → k₃ ≠ k₁ → k₃ ≠ k₁ * z → k₃ ≠ k₂ → k₃ ≠ k₂ * z →
    k₁ * k₂ * k₃ = 1 ∨ k₁ * k₂ * k₃ = z
  exists_ord4 : ∃ k ∈ M, k * k = z

theorem q8Facts_of_iso {Y : Type*} [Group Y] {M : Subgroup Y} {z : Y}
    (hz : IsUniqueInvolution M z) (e : ↥M ≃* QuaternionGroup 2) : Q8Facts M z := by
  classical
  let φ : QuaternionGroup 2 →* Y := M.subtype.comp e.symm.toMonoidHom
  have hφinj : Function.Injective φ := M.subtype_injective.comp e.symm.injective
  have hmem : ∀ m ∈ M, ∃ q, φ q = m := fun m hm => ⟨e ⟨m, hm⟩, by simp [φ]⟩
  have hφM : ∀ q, φ q ∈ M := fun q => (e.symm q).2
  have hz2 : φ (a 2) = z := by
    obtain ⟨q₀, hq₀⟩ := hmem z hz.mem
    have h1 : q₀ * q₀ = 1 := by
      apply hφinj
      rw [map_mul, hq₀, hz.sq, map_one]
    have h2 : q₀ ≠ 1 := by
      rintro rfl
      exact hz.ne_one (by rw [← hq₀, map_one])
    rw [← hq₀, q8_inv q₀ h1 h2]
  have hφmul : ∀ q r, φ q * φ r = φ (q * r) := fun q r => (map_mul φ q r).symm
  refine ⟨hz.mem, hz.ne_one, hz.sq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨q, rfl⟩ := hmem m hm
    rw [← hz2, hφmul, hφmul, q8_a2_central]
  · intro m hm
    obtain ⟨q, rfl⟩ := hmem m hm
    rw [hφmul]
    rcases q8_sq_cases q with h | h
    · left; rw [h, map_one]
    · right; rw [h, hz2]
  · intro m hm hm2
    obtain ⟨q, rfl⟩ := hmem m hm
    rw [hφmul] at hm2
    have h1 : q * q = 1 := hφinj (by rw [hm2, map_one])
    by_cases hq : q = 1
    · left; rw [hq, map_one]
    · right; rw [q8_inv q h1 hq, hz2]
  · intro m hm hc
    obtain ⟨q, rfl⟩ := hmem m hm
    have hq : ∀ g : QuaternionGroup 2, q * g = g * q := fun g => by
      apply hφinj
      rw [← hφmul, ← hφmul]
      exact hc _ (hφM g)
    rcases q8_central q hq with h | h
    · left; rw [h, map_one]
    · right; rw [h, hz2]
  · intro k hk hk1 hkz
    obtain ⟨q, rfl⟩ := hmem k hk
    have h1 : q ≠ 1 := fun h => hk1 (by rw [h, map_one])
    have h2 : q ≠ a 2 := fun h => hkz (by rw [h, hz2])
    obtain ⟨r, hr⟩ := q8_exists_noncomm q h1 h2
    refine ⟨φ r, hφM r, fun h => hr ?_⟩
    apply hφinj
    rw [← hφmul, ← hφmul]
    exact h
  · intro k hk m hm hkm
    obtain ⟨q, rfl⟩ := hmem k hk
    obtain ⟨r, rfl⟩ := hmem m hm
    have h1 : q * r ≠ r * q := fun h => hkm (by rw [hφmul, hφmul, h])
    rw [← hz2, ← map_inv, ← map_inv, hφmul, hφmul, hφmul, q8_comm_eq q r h1]
  · intro k hk hk2 d hd hdk
    obtain ⟨q, rfl⟩ := hmem k hk
    obtain ⟨r, rfl⟩ := hmem d hd
    have h1 : q * q = a 2 := hφinj (by rw [← hφmul, hk2, hz2])
    have h2 : r * q = q * r := hφinj (by rw [← hφmul, ← hφmul, hdk])
    rcases q8_cent_cyc q r h1 h2 with h | h | h | h
    · left; rw [h, map_one]
    · right; left; rw [h]
    · right; right; left; rw [h, hz2]
    · right; right; right; rw [h, ← hz2, hφmul]
  · intro k hk m hm hkm g hg
    obtain ⟨q, rfl⟩ := hmem k hk
    obtain ⟨r, rfl⟩ := hmem m hm
    obtain ⟨s, rfl⟩ := hmem g hg
    have h1 : q * r ≠ r * q := fun h => hkm (by rw [hφmul, hφmul, h])
    obtain ⟨i, j, hij⟩ := q8_gen q r s h1
    exact ⟨i, i.2, j, j.2, by rw [hij, map_mul, map_pow, map_pow]⟩
  · intro k₁ hk₁ k₂ hk₂ k₃ hk₃ h1 h2 h3 h12 h12' h13 h13' h23 h23'
    obtain ⟨q₁, rfl⟩ := hmem k₁ hk₁
    obtain ⟨q₂, rfl⟩ := hmem k₂ hk₂
    obtain ⟨q₃, rfl⟩ := hmem k₃ hk₃
    have e1 : q₁ * q₁ = a 2 := hφinj (by rw [← hφmul, h1, hz2])
    have e2 : q₂ * q₂ = a 2 := hφinj (by rw [← hφmul, h2, hz2])
    have e3 : q₃ * q₃ = a 2 := hφinj (by rw [← hφmul, h3, hz2])
    have n12 : q₂ ≠ q₁ := fun h => h12 (by rw [h])
    have n12' : q₂ ≠ q₁ * a 2 := fun h => h12' (by rw [h, ← hz2, hφmul])
    have n13 : q₃ ≠ q₁ := fun h => h13 (by rw [h])
    have n13' : q₃ ≠ q₁ * a 2 := fun h => h13' (by rw [h, ← hz2, hφmul])
    have n23 : q₃ ≠ q₂ := fun h => h23 (by rw [h])
    have n23' : q₃ ≠ q₂ * a 2 := fun h => h23' (by rw [h, ← hz2, hφmul])
    rw [hφmul, hφmul]
    rcases q8_prod3 q₁ q₂ q₃ e1 e2 e3 n12 n12' n13 n13' n23 n23' with h | h
    · left; rw [h, map_one]
    · right; rw [h, hz2]
  · obtain ⟨q, hq⟩ := q8_exists_ord4
    exact ⟨φ q, hφM q, by rw [hφmul, hq, hz2]⟩


section Action

variable {Y : Type*} [Group Y] {M : Subgroup Y} {z : Y}

@[expose] def ZFix (g z m : Y) : Prop := g * m * g⁻¹ = m ∨ g * m * g⁻¹ = m * z

theorem ZFix.mul {g m m' : Y} (hz2 : z * z = 1) (hzm : z * m' = m' * z)
    (h : ZFix g z m) (h' : ZFix g z m') : ZFix g z (m * m') := by
  have e : g * (m * m') * g⁻¹ = (g * m * g⁻¹) * (g * m' * g⁻¹) := by group
  unfold ZFix at *
  rw [e]
  rcases h with h | h <;> rcases h' with h' | h' <;> rw [h, h']
  · left; rfl
  · right; exact (mul_assoc _ _ _).symm
  · right
    calc m * z * m' = m * (z * m') := mul_assoc _ _ _
      _ = m * (m' * z) := by rw [hzm]
      _ = m * m' * z := (mul_assoc _ _ _).symm
  · left
    calc m * z * (m' * z) = m * (z * m') * z := by group
      _ = m * (m' * z) * z := by rw [hzm]
      _ = m * m' * (z * z) := by group
      _ = m * m' := by rw [hz2, mul_one]

theorem ZFix.inv {g m : Y} (hz2 : z * z = 1) (hzm : z * m = m * z) (h : ZFix g z m) :
    ZFix g z m⁻¹ := by
  have e : g * m⁻¹ * g⁻¹ = (g * m * g⁻¹)⁻¹ := by group
  unfold ZFix at *
  rw [e]
  rcases h with h | h
  · left; rw [h]
  · right
    rw [h, mul_inv_rev, inv_eq_of_mul_eq_one_right hz2]
    exact (Commute.inv_right (show Commute z m from hzm)).eq

theorem zfix_one (g : Y) (z : Y) : ZFix g z 1 := Or.inl (by group)

theorem zfix_z {g : Y} (hgz : g * z = z * g) : ZFix g z z := Or.inl (by
  rw [hgz]; group)

theorem ZFix.sq {g m : Y} (hz2 : z * z = 1) (hgz : g * z = z * g) (h : ZFix g z m) :
    (g * g) * m * (g * g)⁻¹ = m := by
  have e : (g * g) * m * (g * g)⁻¹ = g * (g * m * g⁻¹) * g⁻¹ := by group
  rw [e]
  rcases h with h | h
  · rw [h, h]
  · rw [h]
    have e2 : g * (m * z) * g⁻¹ = (g * m * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e2, h, hgz]
    calc m * z * (z * g * g⁻¹) = m * (z * z) := by group
      _ = m := by rw [hz2, mul_one]

end Action


section Odd

variable {Y : Type*} [Group Y] {M : Subgroup Y} {z : Y}

theorem exists_eq_pow_sq {x : Y} (hxo : Odd (orderOf x)) : ∃ r : ℕ, x = (x * x) ^ r := by
  obtain ⟨j, hj⟩ := hxo
  refine ⟨j + 1, ?_⟩
  have h1 : x ^ (orderOf x) = 1 := pow_orderOf_eq_one x
  rw [hj] at h1
  calc x = x ^ (2 * j + 1) * x := by rw [h1, one_mul]
    _ = x ^ (2 * (j + 1)) := by rw [← pow_succ]; ring_nf
    _ = (x * x) ^ (j + 1) := by rw [pow_mul, sq]

theorem odd_orderOf_mul_self {x : Y} (hxo : Odd (orderOf x)) : Odd (orderOf (x * x)) := by
  refine Odd.of_dvd_nat hxo (orderOf_dvd_of_pow_eq_one ?_)
  rw [← sq, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]

theorem Q8Facts.cent_of_comm_mem (h : Q8Facts M z) {x : Y} (hxo : Odd (orderOf x))
    (hxz : x * z = z * x)
    (hc : ∀ m ∈ M, x * m * x⁻¹ * m⁻¹ = 1 ∨ x * m * x⁻¹ * m⁻¹ = z) : ∀ m ∈ M, x * m = m * x := by
  intro m hm
  obtain ⟨c, hcdef⟩ : ∃ c, c = x * m * x⁻¹ * m⁻¹ := ⟨_, rfl⟩
  have hc' : c = 1 ∨ c = z := by rw [hcdef]; exact hc m hm
  have hxc : x * c = c * x := by
    rcases hc' with rfl | rfl
    · simp
    · exact hxz
  have hxm : x * m * x⁻¹ = c * m := by rw [hcdef]; group
  have key : ∀ n : ℕ, x ^ n * m * (x ^ n)⁻¹ = c ^ n * m := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have hxck : x * c ^ k = c ^ k * x := (Commute.pow_right (show Commute x c from hxc) k).eq
      calc x ^ (k + 1) * m * (x ^ (k + 1))⁻¹
          = x * (x ^ k * m * (x ^ k)⁻¹) * x⁻¹ := by rw [pow_succ']; group
        _ = x * (c ^ k * m) * x⁻¹ := by rw [ih]
        _ = (x * c ^ k * x⁻¹) * (x * m * x⁻¹) := by group
        _ = c ^ k * (c * m) := by rw [hxm, mul_inv_eq_iff_eq_mul.mpr hxck]
        _ = c ^ (k + 1) * m := by rw [pow_succ, mul_assoc]
  have hn := key (orderOf x)
  rw [pow_orderOf_eq_one] at hn
  have hcn : c ^ (orderOf x) = 1 := by
    have h2 : c ^ (orderOf x) * m = 1 * m := by rw [← hn]; simp
    exact mul_right_cancel h2
  have hcc : c * c = 1 := by
    rcases hc' with rfl | rfl
    · simp
    · exact h.z_sq
  obtain ⟨j, hj⟩ := hxo
  have hc1 : c = 1 := by
    have e : c ^ (2 * j + 1) = c := by rw [pow_succ, pow_mul, sq, hcc, one_pow, one_mul]
    rw [← e, ← hj, hcn]
  have : x * m * x⁻¹ = m := by rw [hxm, hc1, one_mul]
  exact mul_inv_eq_iff_eq_mul.mp this

theorem Q8Facts.cent_of_fix (h : Q8Facts M z) {x : Y} (hxo : Odd (orderOf x)) (hxz : x * z = z * x)
    (hxM : ∀ m ∈ M, x * m * x⁻¹ ∈ M) {k : Y} (hk : k ∈ M) (hk2 : k * k = z) (hfix : ZFix x z k) :
    ∀ m ∈ M, x * m = m * x := by
  have hz2 := h.z_sq
  have hzc := h.z_central
  let S : Subgroup Y :=
    { carrier := {m | m ∈ M ∧ ZFix (x * x) z m}
      mul_mem' := fun {a b} ha hb => ⟨M.mul_mem ha.1 hb.1, ZFix.mul hz2 (hzc b hb.1) ha.2 hb.2⟩
      one_mem' := ⟨M.one_mem, zfix_one _ _⟩
      inv_mem' := fun {a} ha => ⟨M.inv_mem ha.1, ZFix.inv hz2 (hzc a ha.1) ha.2⟩ }
  have hkS : k ∈ S := ⟨hk, Or.inl (hfix.sq hz2 hxz)⟩
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact h.z_ne (by rw [← hk2, one_mul])
  have hkz : k ≠ z := by
    rintro rfl
    exact h.z_ne (by rw [← hk2, hz2])
  obtain ⟨m₀, hm₀, hkm₀⟩ := h.exists_noncomm k hk hk1 hkz
  obtain ⟨m₁, hm₁def⟩ : ∃ m₁, m₁ = x * m₀ * x⁻¹ := ⟨_, rfl⟩
  have hm₁ : m₁ ∈ M := hm₁def ▸ hxM m₀ hm₀
  have hcomm := h.comm_eq k hk m₀ hm₀ hkm₀
  have hconj : (x * k * x⁻¹) * m₁ * (x * k * x⁻¹)⁻¹ * m₁⁻¹ = z := by
    have e : x * (k * m₀ * k⁻¹ * m₀⁻¹) * x⁻¹ =
        (x * k * x⁻¹) * m₁ * (x * k * x⁻¹)⁻¹ * m₁⁻¹ := by rw [hm₁def]; group
    rw [← e, hcomm, hxz]
    group
  have hkm₁ : k * m₁ * k⁻¹ * m₁⁻¹ = z := by
    rcases hfix with h1 | h1
    · rw [h1] at hconj; exact hconj
    · rw [h1] at hconj
      have e : (k * z) * m₁ * (k * z)⁻¹ = k * m₁ * k⁻¹ := by
        calc (k * z) * m₁ * (k * z)⁻¹
            = k * (z * m₁ * z⁻¹) * k⁻¹ := by group
          _ = k * m₁ * k⁻¹ := by rw [hzc _ hm₁]; group
      rw [e] at hconj
      exact hconj
  have e1 : k * m₀ * k⁻¹ = z * m₀ := by
    calc k * m₀ * k⁻¹ = (k * m₀ * k⁻¹ * m₀⁻¹) * m₀ := by group
      _ = z * m₀ := by rw [hcomm]
  have e2 : k * m₁ * k⁻¹ = z * m₁ := by
    calc k * m₁ * k⁻¹ = (k * m₁ * k⁻¹ * m₁⁻¹) * m₁ := by group
      _ = z * m₁ := by rw [hkm₁]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hdk : k * (m₀⁻¹ * m₁) * k⁻¹ = m₀⁻¹ * m₁ := by
    calc k * (m₀⁻¹ * m₁) * k⁻¹ = (k * m₀ * k⁻¹)⁻¹ * (k * m₁ * k⁻¹) := by group
      _ = (z * m₀)⁻¹ * (z * m₁) := by rw [e1, e2]
      _ = m₀⁻¹ * (z⁻¹ * z) * m₁ := by group
      _ = m₀⁻¹ * m₁ := by group
  have hd : m₀⁻¹ * m₁ ∈ M := M.mul_mem (M.inv_mem hm₀) hm₁
  have hdk' : (m₀⁻¹ * m₁) * k = k * (m₀⁻¹ * m₁) := (mul_inv_eq_iff_eq_mul.mp hdk).symm
  have hdZ : ZFix x z (m₀⁻¹ * m₁) := by
    rcases h.cent_cyc k hk hk2 _ hd hdk' with e | e | e | e <;> rw [e]
    · exact zfix_one _ _
    · exact hfix
    · exact zfix_z hxz
    · exact ZFix.mul hz2 rfl hfix (zfix_z hxz)
  have hm₀S : m₀ ∈ S := by
    refine ⟨hm₀, ?_⟩
    obtain ⟨d, hdd0⟩ : ∃ d, d = m₀⁻¹ * m₁ := ⟨_, rfl⟩
    rw [← hdd0] at hd hdZ
    have hm₁eq : m₁ = m₀ * d := by rw [hdd0]; group
    have e : (x * x) * m₀ * (x * x)⁻¹ = m₀ * d * (x * d * x⁻¹) := by
      calc (x * x) * m₀ * (x * x)⁻¹ = x * (x * m₀ * x⁻¹) * x⁻¹ := by group
        _ = x * m₁ * x⁻¹ := by rw [hm₁def]
        _ = x * (m₀ * d) * x⁻¹ := by rw [hm₁eq]
        _ = (x * m₀ * x⁻¹) * (x * d * x⁻¹) := by group
        _ = m₁ * (x * d * x⁻¹) := by rw [hm₁def]
        _ = m₀ * d * (x * d * x⁻¹) := by rw [hm₁eq]
    have hdd := h.sq_cases _ hd
    unfold ZFix
    rw [e]
    rcases hdZ with e1 | e1 <;> rw [e1] <;> rcases hdd with e2 | e2
    · left; rw [mul_assoc, e2, mul_one]
    · right; rw [mul_assoc, e2]
    · right; rw [show m₀ * d * (d * z) = m₀ * (d * d) * z by group, e2, mul_one]
    · left; rw [show m₀ * d * (d * z) = m₀ * (d * d) * z by group, e2, mul_assoc, hz2, mul_one]
  have hgenS : ∀ g ∈ M, g ∈ S := by
    intro g hg
    obtain ⟨i, -, j, -, rfl⟩ := h.gen k hk m₀ hm₀ hkm₀ g hg
    exact S.mul_mem (S.pow_mem hkS _) (S.pow_mem hm₀S _)
  have hcomm2 : ∀ m ∈ M, (x * x) * m * (x * x)⁻¹ * m⁻¹ = 1 ∨ (x * x) * m * (x * x)⁻¹ * m⁻¹ = z := by
    intro m hm
    rcases (hgenS m hm).2 with e | e
    · left; rw [e]; group
    · right; rw [e]
      calc m * z * m⁻¹ = (m * z) * m⁻¹ := rfl
        _ = z * m * m⁻¹ := by rw [← hzc m hm]
        _ = z := by group
  have hxxz : (x * x) * z = z * (x * x) := by
    calc (x * x) * z = x * (x * z) := mul_assoc _ _ _
      _ = x * (z * x) := by rw [hxz]
      _ = (x * z) * x := (mul_assoc _ _ _).symm
      _ = (z * x) * x := by rw [hxz]
      _ = z * (x * x) := mul_assoc _ _ _
  have hxx : ∀ m ∈ M, (x * x) * m = m * (x * x) :=
    h.cent_of_comm_mem (odd_orderOf_mul_self hxo) hxxz hcomm2
  obtain ⟨r, hr⟩ := exists_eq_pow_sq hxo
  intro m hm
  have := (Commute.pow_left (show Commute (x * x) m from hxx m hm) r).eq
  rw [← hr] at this
  exact this


theorem cent_of_sq_cent {x : Y} (hxo : Odd (orderOf x)) {M : Subgroup Y}
    (hxx : ∀ m ∈ M, (x * x) * m = m * (x * x)) : ∀ m ∈ M, x * m = m * x := by
  obtain ⟨r, hr⟩ := exists_eq_pow_sq hxo
  intro m hm
  have := (Commute.pow_left (show Commute (x * x) m from hxx m hm) r).eq
  rw [← hr] at this
  exact this

theorem sq_normalizes {x : Y} (hxM : ∀ m ∈ M, x * m * x⁻¹ ∈ M) :
    ∀ m ∈ M, (x * x) * m * (x * x)⁻¹ ∈ M := by
  intro m hm
  have e : (x * x) * m * (x * x)⁻¹ = x * (x * m * x⁻¹) * x⁻¹ := by group
  rw [e]
  exact hxM _ (hxM m hm)

theorem Q8Facts.not_zfix_of_not_cent (h : Q8Facts M z) {x : Y} (hxo : Odd (orderOf x))
    (hxz : x * z = z * x) (hxM : ∀ m ∈ M, x * m * x⁻¹ ∈ M) (hnc : ¬ ∀ m ∈ M, x * m = m * x)
    {k : Y} (hk : k ∈ M) (hk2 : k * k = z) : ¬ ZFix x z k :=
  fun hf => hnc (h.cent_of_fix hxo hxz hxM hk hk2 hf)

theorem Q8Facts.cycle3 (h : Q8Facts M z) {x : Y} (hxo : Odd (orderOf x)) (hxz : x * z = z * x)
    (hxM : ∀ m ∈ M, x * m * x⁻¹ ∈ M) (hnc : ¬ ∀ m ∈ M, x * m = m * x) {k : Y} (hk : k ∈ M)
    (hk2 : k * k = z) :
    k * (x * k * x⁻¹) * ((x * x) * k * (x * x)⁻¹) = 1 ∨
      k * (x * k * x⁻¹) * ((x * x) * k * (x * x)⁻¹) = z := by
  have hk₂ : x * k * x⁻¹ ∈ M := hxM k hk
  have hk₃ : (x * x) * k * (x * x)⁻¹ ∈ M := sq_normalizes hxM k hk
  have e3 : (x * x) * k * (x * x)⁻¹ = x * (x * k * x⁻¹) * x⁻¹ := by group
  have hxxz : (x * x) * z = z * (x * x) := by
    calc (x * x) * z = x * (x * z) := mul_assoc _ _ _
      _ = x * (z * x) := by rw [hxz]
      _ = (x * z) * x := (mul_assoc _ _ _).symm
      _ = (z * x) * x := by rw [hxz]
      _ = z * (x * x) := mul_assoc _ _ _
  have hsq : ∀ g : Y, g * z = z * g → g * k * g⁻¹ * (g * k * g⁻¹) = z := by
    intro g hg
    calc g * k * g⁻¹ * (g * k * g⁻¹) = g * (k * k) * g⁻¹ := by group
      _ = z := by rw [hk2, hg]; group
  have hs2 : x * k * x⁻¹ * (x * k * x⁻¹) = z := hsq x hxz
  have hs3 : (x * x) * k * (x * x)⁻¹ * ((x * x) * k * (x * x)⁻¹) = z := hsq (x * x) hxxz
  have hnc2 : ¬ ∀ m ∈ M, (x * x) * m = m * (x * x) := fun hc => hnc (cent_of_sq_cent hxo hc)
  have n1 := h.not_zfix_of_not_cent hxo hxz hxM hnc hk hk2
  have n2 := h.not_zfix_of_not_cent hxo hxz hxM hnc hk₂ hs2
  have n3 := h.not_zfix_of_not_cent (odd_orderOf_mul_self hxo) hxxz (sq_normalizes hxM) hnc2 hk hk2
  unfold ZFix at n1 n2 n3
  push Not at n1 n2 n3
  refine h.prod3 k hk _ hk₂ _ hk₃ hk2 hs2 hs3 n1.1 n1.2 n3.1 n3.2 ?_ ?_
  · rw [e3]; exact n2.1
  · rw [e3]; exact n2.2

end Odd

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
