module

public import CFSG.CGT.Foote81L6.Fusion3.Zab
public import CFSG.CGT.Foote81L6.Normalizer.GLemma1
public import CFSG.CGT.Foote81L6.Normalizer.GBasic

public section

namespace CFSG.CGT.Foote81L6.Fusion3

open Subgroup

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

private def conjOn {H : Subgroup G} {p : G} (hp : p ∈ normalizer (H : Set G)) : MulAut ↥H where
  toFun x := ⟨p * x * p⁻¹, (mem_normalizer_iff.1 hp x).1 x.2⟩
  invFun x := ⟨p⁻¹ * x * p, by
    have := (mem_normalizer_iff.1 (inv_mem hp) x).1 x.2
    rwa [inv_inv] at this⟩
  left_inv x := Subtype.ext (by show p⁻¹ * (p * (x : G) * p⁻¹) * p = x; group)
  right_inv x := Subtype.ext (by show p * (p⁻¹ * (x : G) * p) * p⁻¹ = x; group)
  map_mul' x y := Subtype.ext (by
    show p * ((x : G) * y) * p⁻¹ = (p * x * p⁻¹) * (p * y * p⁻¹); group)

private theorem conjOn_pow {H : Subgroup G} {p : G} (hp : p ∈ normalizer (H : Set G)) (k : ℕ)
    (x : ↥H) : (((conjOn hp) ^ k) x : G) = p ^ k * x * (p ^ k)⁻¹ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, pow_succ]
    show p ^ k * (p * (x : G) * p⁻¹) * (p ^ k)⁻¹ = p ^ k * p * x * (p ^ k * p)⁻¹
    group

theorem conj_eq_of_odd_of_three_le (hm : 3 ≤ m) {d : G} (hd : d ∈ normalizer (D.T₁ : Set G))
    (hodd : Odd (orderOf d)) {w : G} (hw : w ∈ D.T₁) : d * w * d⁻¹ = w := by
  by_contra hne
  obtain ⟨ψ⟩ := Normalizer.nonempty_T₁_equiv D
  set y := conjOn hd with hy
  have hyval : ∀ x : ↥D.T₁, (y x : G) = d * x * d⁻¹ := fun x => rfl
  have hy1 : y ≠ 1 := by
    intro h
    apply hne
    have := congrArg (fun f : MulAut ↥D.T₁ => (f ⟨w, hw⟩ : G)) h
    simpa [hyval] using this
  have hyodd : Odd (orderOf y) := by
    refine hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [conjOn_pow, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
    rfl
  have hy'1 : MulAut.congr ψ y ≠ 1 := fun h =>
    hy1 ((MulAut.congr ψ).injective (h.trans (map_one _).symm))
  have hy'odd : Odd (orderOf (MulAut.congr ψ y)) := by
    rw [MulEquiv.orderOf_eq]
    exact hyodd
  have h2 := (lemma1_one D.two_le_m D.m_lt_n le_rfl _ hy'1 hy'odd).1
  omega

theorem mem_B_of_Bz {w : G} (hw : w = 1 ∨ w = D.b₀ ∨ w = D.b₁ ∨ w = D.b) : w ∈ D.B := by
  rcases hw with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact D.b₀_mem_B
  · exact D.b₁_mem_B
  · exact D.b_mem_B

theorem mem_Zab_of_Bz {w : G} (hw : w = 1 ∨ w = D.b₀ ∨ w = D.b₁ ∨ w = D.b) : w ∈ D.Zab :=
  (mem_Zab_iff D).2 ⟨1, w, Or.inl rfl, hw, (one_mul w).symm⟩

theorem mul_self_of_Bz {w : G} (hw : w = 1 ∨ w = D.b₀ ∨ w = D.b₁ ∨ w = D.b) : w * w = 1 := by
  rcases hw with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact D.b₀_mul_b₀
  · exact D.b₁_mul_b₁
  · exact D.b_mul_b

section Four

variable {G : Type*} [Group G] {T : Subgroup G} {n : ℕ} (D : FooteCore G T 2 n)

private theorem conj_sq_of_comm {d : G}
    (hcomm : ∀ x ∈ D.T₁, d * x * d⁻¹ * x⁻¹ ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁)) {y : G}
    (hy : y ∈ D.T₁) : d * (y * y) * d⁻¹ = y * y := by
  set z := d * y * d⁻¹ * y⁻¹ with hz_def
  have hz : z ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) := hcomm y hy
  have hzy : y * z = z * y := Normalizer.comm_of_mem_T₁_of_mem_Z D hy hz
  have hzz : z * z = 1 :=
    (D.isE64_Frep 0 0).mul_self z (Normalizer.Z_le_E64 D (D.isE64_Frep 0 0) hz)
  have e : d * y * d⁻¹ = z * y := by rw [hz_def]; group
  calc d * (y * y) * d⁻¹ = (d * y * d⁻¹) * (d * y * d⁻¹) := by group
    _ = z * y * (z * y) := by rw [e]
    _ = z * (y * z) * y := by group
    _ = z * (z * y) * y := by rw [hzy]
    _ = (z * z) * (y * y) := by group
    _ = y * y := by rw [hzz, one_mul]

theorem conj_b₀_b₁_of_odd {d : G} (hd : d ∈ normalizer (D.T₁ : Set G)) (hodd : Odd (orderOf d)) :
    d * D.b₀ * d⁻¹ = D.b₀ ∧ d * D.b₁ * d⁻¹ = D.b₁ := by
  by_cases hmove : ∃ x ∈ D.T₁, d * x * d⁻¹ ≠ x
  · obtain ⟨-, hcomm⟩ := Normalizer.lemma1_T₁ D (Normalizer.nonempty_T₁_equiv D) hd hodd hmove
    obtain ⟨y₀, hy₀, hy₀2⟩ := D.exists_mul_self_eq_b₀
    have hy₁ : D.s * y₀ * D.s⁻¹ ∈ D.B₁ := D.conj_s_mem_B₁ hy₀
    have hy₁2 : (D.s * y₀ * D.s⁻¹) * (D.s * y₀ * D.s⁻¹) = D.b₁ := by
      rw [← D.conj_s_b₀, ← hy₀2]
      group
    refine ⟨?_, ?_⟩
    · rw [← hy₀2]
      exact conj_sq_of_comm D hcomm (D.B₀_le_T₁ hy₀)
    · rw [← hy₁2]
      exact conj_sq_of_comm D hcomm (D.B₁_le_T₁ hy₁)
  · push Not at hmove
    exact ⟨hmove _ (D.B₀_le_T₁ D.b₀_mem), hmove _ (D.B₁_le_T₁ D.b₁_mem)⟩

private theorem comm_of_Bz {w : G} (hw : w = 1 ∨ w = D.b₀ ∨ w = D.b₁ ∨ w = D.b) {x : G}
    (hx : x ∈ D.T₁) : x * w = w * x :=
  comm_of_mem_Zab D (mem_Zab_of_Bz D hw) hx

theorem conj_mem_Bz {g : G} (hg : g ∈ normalizer (D.T₁ : Set G)) {w : G}
    (hw : w = 1 ∨ w = D.b₀ ∨ w = D.b₁ ∨ w = D.b) :
    g * w * g⁻¹ = 1 ∨ g * w * g⁻¹ = D.b₀ ∨ g * w * g⁻¹ = D.b₁ ∨ g * w * g⁻¹ = D.b := by
  have hsq : ∃ y ∈ D.B₀ ⊔ D.B₁, y * y = w := by
    obtain ⟨y₀, hy₀, hy₀2⟩ := D.exists_mul_self_eq_b₀
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, mul_one 1⟩
    · exact ⟨y₀, mem_sup_left hy₀, hy₀2⟩
    · refine ⟨D.s * y₀ * D.s⁻¹, mem_sup_right (D.conj_s_mem_B₁ hy₀), ?_⟩
      rw [← D.conj_s_b₀, ← hy₀2]
      group
    · exact D.exists_mul_self_eq_b
  obtain ⟨y, hy, rfl⟩ := hsq
  have hgy : g * y * g⁻¹ ∈ D.T₁ := (mem_normalizer_iff.1 hg y).1 (D.B₀B₁_le_T₁ hy)
  obtain ⟨α, hα, v, hv, hαv⟩ := D.mem_T₁_iff.1 hgy
  have e : g * (y * y) * g⁻¹ = v * v := by
    calc g * (y * y) * g⁻¹ = (g * y * g⁻¹) * (g * y * g⁻¹) := by group
      _ = α * v * (α * v) := by rw [hαv]
      _ = (α * α) * (v * v) := by
          rw [mul_assoc α v, ← mul_assoc v α, ← D.A_comm_B₀B₁ α hα v hv]
          group
      _ = v * v := by rw [D.mul_self_of_two hα, one_mul]
  have hcomm : ∀ w' ∈ D.B₀ ⊔ D.B₁, w' * (v * v) = (v * v) * w' := by
    intro w' hw'
    have hw'' : g⁻¹ * w' * g ∈ D.T₁ := by
      have := (mem_normalizer_iff.1 (inv_mem hg) w').1 (D.B₀B₁_le_T₁ hw')
      rwa [inv_inv] at this
    have hc := comm_of_Bz D hw hw''
    rw [← e]
    calc w' * (g * (y * y) * g⁻¹) = g * ((g⁻¹ * w' * g) * (y * y)) * g⁻¹ := by group
      _ = g * ((y * y) * (g⁻¹ * w' * g)) * g⁻¹ := by rw [hc]
      _ = g * (y * y) * g⁻¹ * w' := by group
  rw [e]
  exact D.eq_of_comm_B₀B₁ (mul_mem hv hv) hcomm

theorem conj_a_of_odd {d : G} (hd : d ∈ normalizer (D.T₁ : Set G)) (hodd : Odd (orderOf d))
    (hda : d * D.a * d⁻¹ ∈ D.Zab) : d * D.a * d⁻¹ = D.a := by
  obtain ⟨h₀, h₁⟩ := conj_b₀_b₁_of_odd D hd hodd
  have hfix : ∀ w, (w = 1 ∨ w = D.b₀ ∨ w = D.b₁ ∨ w = D.b) → d * w * d⁻¹ = w := by
    rintro w (rfl | rfl | rfl | rfl)
    · group
    · exact h₀
    · exact h₁
    · show d * (D.b₀ * D.b₁) * d⁻¹ = D.b₀ * D.b₁
      calc d * (D.b₀ * D.b₁) * d⁻¹ = (d * D.b₀ * d⁻¹) * (d * D.b₁ * d⁻¹) := by group
        _ = D.b₀ * D.b₁ := by rw [h₀, h₁]
  obtain ⟨α, w, hα, hw, hαw⟩ := (mem_Zab_iff D).1 hda
  have hdw := hfix w hw
  rcases hα with rfl | rfl
  · exfalso
    rw [one_mul] at hαw
    have haw : D.a = w := by
      have h' : d * D.a * d⁻¹ = d * w * d⁻¹ := by rw [hαw, hdw]
      exact mul_left_cancel (mul_right_cancel h')
    have hmem : D.a ∈ D.A ⊓ D.B := mem_inf.2 ⟨D.a_mem, haw ▸ mem_B_of_Bz D hw⟩
    rw [D.A_inf_B, mem_bot] at hmem
    exact D.a_ne_one hmem
  · have hcw : Commute d w := comm_of_conj_eq hdw |>.symm
    have hpow : ∀ k : ℕ, d ^ k * D.a * (d ^ k)⁻¹ = D.a * w ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hk : d ^ k * w * (d ^ k)⁻¹ = w := by
          rw [(hcw.pow_left k).eq, mul_inv_cancel_right]
        calc d ^ (k + 1) * D.a * (d ^ (k + 1))⁻¹ = d ^ k * (d * D.a * d⁻¹) * (d ^ k)⁻¹ := by
              group
          _ = (d ^ k * D.a * (d ^ k)⁻¹) * (d ^ k * w * (d ^ k)⁻¹) := by rw [hαw]; group
          _ = D.a * w ^ (k + 1) := by rw [ih, hk, pow_succ, mul_assoc]
    have h1 := hpow (orderOf d)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
    have hwk : w ^ orderOf d = 1 := by
      have := congrArg (fun z => D.a⁻¹ * z) h1
      simpa using this.symm
    obtain ⟨j, hj⟩ := hodd
    have hw2 : w ^ 2 = 1 := by rw [sq]; exact mul_self_of_Bz D hw
    rw [hj, pow_succ, pow_mul, hw2, one_pow, one_mul] at hwk
    rw [hαw, hwk, mul_one]

end Four

end CFSG.CGT.Foote81L6.Fusion3
