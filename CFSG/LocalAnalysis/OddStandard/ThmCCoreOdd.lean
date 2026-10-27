module

public import CFSG.LocalAnalysis.OddStandard.ThmCTAmbient

public section

namespace CFSG.OddStandard.ThmC.Core

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23 CFSG.OddStandard.ThmC.T

theorem add_bij_odd_aux : ∀ l : F4c → F4c, (∀ a b, l (a + b) = l a + l b) → Function.Injective l →
    ∀ a, l^[6] a = a := by
  decide +kernel

theorem add_bij_three : ∀ l : F4c → F4c, (∀ a b, l (a + b) = l a + l b) → Function.Injective l →
    (∀ a, l^[3] a = a) → ∃ c : F4c, c ≠ 0 ∧ ∀ a, l a = c * a := by
  decide +kernel

theorem gcd_six_odd {j : ℕ} (hj : Odd j) : Nat.gcd 6 j = 1 ∨ Nat.gcd 6 j = 3 := by
  have hodd : Odd (Nat.gcd 6 j) := Odd.of_dvd_nat hj (Nat.gcd_dvd_right 6 j)
  have hdvd : Nat.gcd 6 j ∣ 6 := Nat.gcd_dvd_left 6 j
  generalize Nat.gcd 6 j = d at hodd hdvd ⊢
  have hle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases d
  · exact absurd hodd (by decide)
  · left; rfl
  · exact absurd hodd (by decide)
  · right; rfl
  · exact absurd hdvd (by decide)
  · exact absurd hdvd (by decide)
  · exact absurd hodd (by decide)

theorem add_bij_odd (l : F4c → F4c) (hadd : ∀ a b, l (a + b) = l a + l b) {j : ℕ} (hj : Odd j)
    (hl : ∀ a, l^[j] a = a) : ∃ c : F4c, c ≠ 0 ∧ ∀ a, l a = c * a := by
  have hinj : Function.Injective l := by
    intro a b hab
    obtain ⟨k, rfl⟩ := hj
    have h1 : ∀ x, l^[2 * k] (l x) = x := fun x => by
      rw [← Function.iterate_succ_apply]
      exact hl x
    have := congrArg (l^[2 * k]) hab
    rwa [h1, h1] at this
  have h6 := add_bij_odd_aux l hadd hinj
  have hg : ∀ a, Function.IsPeriodicPt l (Nat.gcd 6 j) a := fun a =>
    Function.IsPeriodicPt.gcd (h6 a) (hl a)
  have h3 : ∀ a, l^[3] a = a := by
    intro a
    have h1 := hg a
    rcases gcd_six_odd hj with h | h
    · rw [h] at h1
      have hfix : l a = a := h1
      show l (l (l a)) = a
      rw [hfix, hfix, hfix]
    · rw [h] at h1
      exact h1
  exact add_bij_three l hadd hinj h3

section Coord

@[expose] def lc (ψ : Tc ≃* Tc) (a : F4c) : F4c := (ψ ⟨a, 0, 0⟩).a
@[expose] def mc (ψ : Tc ≃* Tc) (b : F4c) : F4c := (ψ ⟨0, b, 0⟩).b
@[expose] def uc (ψ : Tc ≃* Tc) (a : F4c) : F4c := (ψ ⟨a, 0, 0⟩).c
@[expose] def vc (ψ : Tc ≃* Tc) (b : F4c) : F4c := (ψ ⟨0, b, 0⟩).c
@[expose] def gc (ψ : Tc ≃* Tc) (c : F4c) : F4c := (ψ ⟨0, 0, c⟩).c

variable {ψ : Tc ≃* Tc}

theorem psi_A (hA : ∀ x ∈ A, ψ x ∈ A) (a : F4c) : ψ ⟨a, 0, 0⟩ = ⟨lc ψ a, 0, uc ψ a⟩ :=
  UT3.ext rfl (hA _ rfl) rfl

theorem psi_B (hB : ∀ x ∈ B, ψ x ∈ B) (b : F4c) : ψ ⟨0, b, 0⟩ = ⟨0, mc ψ b, vc ψ b⟩ :=
  UT3.ext (hB _ rfl) rfl rfl

theorem psi_Z (c : F4c) : ψ ⟨0, 0, c⟩ = ⟨0, 0, gc ψ c⟩ := by
  have h : (⟨0, 0, c⟩ : Tc) ∈ Subgroup.center Tc := (mem_center_iff _).2 ⟨rfl, rfl⟩
  have := (mem_center_iff _).1 ((mem_center_equiv_iff ψ _).1 h)
  exact UT3.ext this.1 this.2 rfl

theorem psi_gen (hA : ∀ x ∈ A, ψ x ∈ A) (hB : ∀ x ∈ B, ψ x ∈ B) (x : Tc) :
    ψ x = ⟨lc ψ x.a, mc ψ x.b, uc ψ x.a + vc ψ x.b + lc ψ x.a * mc ψ x.b +
      gc ψ (x.c + x.a * x.b)⟩ := by
  conv_lhs => rw [decomp x]
  rw [map_mul, map_mul, psi_A hA, psi_B hB, psi_Z]
  refine UT3.ext ?_ ?_ ?_ <;> simp only [UT3.mul_def] <;> ring

theorem lc_add (hA : ∀ x ∈ A, ψ x ∈ A) (a a' : F4c) : lc ψ (a + a') = lc ψ a + lc ψ a' := by
  have h : (⟨a, 0, 0⟩ : Tc) * ⟨a', 0, 0⟩ = ⟨a + a', 0, 0⟩ :=
    UT3.ext rfl (by simp [UT3.mul_def]) (by simp [UT3.mul_def])
  have h' : ψ (⟨a, 0, 0⟩ * ⟨a', 0, 0⟩ : Tc) = ψ ⟨a + a', 0, 0⟩ := by rw [h]
  rw [map_mul, psi_A hA, psi_A hA, psi_A hA] at h'
  have := congrArg UT3.a h'
  exact this.symm

theorem mc_add (hB : ∀ x ∈ B, ψ x ∈ B) (b b' : F4c) : mc ψ (b + b') = mc ψ b + mc ψ b' := by
  have h : (⟨0, b, 0⟩ : Tc) * ⟨0, b', 0⟩ = ⟨0, b + b', 0⟩ :=
    UT3.ext (by simp [UT3.mul_def]) rfl (by simp [UT3.mul_def])
  have h' : ψ (⟨0, b, 0⟩ * ⟨0, b', 0⟩ : Tc) = ψ ⟨0, b + b', 0⟩ := by rw [h]
  rw [map_mul, psi_B hB, psi_B hB, psi_B hB] at h'
  have := congrArg UT3.b h'
  exact this.symm

theorem gc_mul (hA : ∀ x ∈ A, ψ x ∈ A) (hB : ∀ x ∈ B, ψ x ∈ B) (a b : F4c) :
    gc ψ (a * b) = lc ψ a * mc ψ b := by
  have h1 : (⟨a, 0, 0⟩ : Tc) * ⟨0, b, 0⟩ = ⟨a, b, 0⟩ * ⟨0, 0, a * b⟩ :=
    UT3.ext (by simp [UT3.mul_def]) (by simp [UT3.mul_def]) (by simp [UT3.mul_def])
  have h2 : (⟨0, b, 0⟩ : Tc) * ⟨a, 0, 0⟩ = ⟨a, b, 0⟩ :=
    UT3.ext (by simp [UT3.mul_def]) (by simp [UT3.mul_def]) (by simp [UT3.mul_def])
  have h3 : ψ ⟨a, b, 0⟩ * ψ ⟨0, 0, a * b⟩ = ψ ⟨a, 0, 0⟩ * ψ ⟨0, b, 0⟩ := by
    rw [← map_mul, ← map_mul, ← h1]
  have h4 : ψ ⟨a, b, 0⟩ = ψ ⟨0, b, 0⟩ * ψ ⟨a, 0, 0⟩ := by rw [← map_mul, h2]
  rw [h4, psi_A hA, psi_B hB, psi_Z] at h3
  have := congrArg UT3.c h3
  simp only [UT3.mul_def] at this
  linear_combination this

theorem preserves_of_odd {ψ : Tc ≃* Tc} {j : ℕ} (hj : Odd j) (hψ : ∀ x, ψ^[j] x = x) :
    (∀ x ∈ A, ψ x ∈ A) ∧ (∀ x ∈ B, ψ x ∈ B) := by
  have hE : ∀ E : Subgroup Tc, (∀ x ∈ E, x * x = 1) → Nat.card E = 16 →
      E.map ψ.toMonoidHom = A ∨ E.map ψ.toMonoidHom = B := by
    intro E hE1 hE2
    apply eq_A_or_B
    · rintro _ ⟨x, hx, rfl⟩
      show ψ x * ψ x = 1
      rw [← map_mul, hE1 x hx, map_one]
    · rw [Subgroup.card_map_of_injective ψ.injective, hE2]
  have hAm := hE A (fun x hx => sq_eq_one_of_mem_A hx) card_A
  have hBm := hE B (fun x hx => sq_eq_one_of_mem_B hx) card_B
  have hmapmem : ∀ (E : Subgroup Tc) (F : Subgroup Tc), E.map ψ.toMonoidHom = F →
      ∀ x ∈ E, ψ x ∈ F := fun E F h x hx => by
    rw [← h]
    exact ⟨x, hx, rfl⟩
  rcases hAm with hA | hA <;> rcases hBm with hB | hB
  · exfalso
    exact A_ne_B (Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective (hA.trans hB.symm))
  · exact ⟨hmapmem _ _ hA, hmapmem _ _ hB⟩
  ·
    exfalso
    have hSA := hmapmem _ _ hA
    have hSB := hmapmem _ _ hB
    have key : ∀ k : ℕ, (ψ^[2 * k + 1] ⟨1, 0, 0⟩ ∈ B) := by
      intro k
      induction k with
      | zero => exact hSA _ rfl
      | succ k ih =>
        have h1 : ψ^[2 * k + 2] ⟨1, 0, 0⟩ ∈ A := by
          rw [Function.iterate_succ_apply']
          exact hSB _ ih
        have h2 : ψ^[2 * (k + 1) + 1] ⟨1, 0, 0⟩ ∈ B := by
          rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by ring, Function.iterate_succ_apply']
          exact hSA _ h1
        exact h2
    obtain ⟨k, rfl⟩ := hj
    have := key k
    rw [hψ] at this
    have h1 : (⟨1, 0, 0⟩ : Tc).a = 0 := this
    exact one_ne_zero h1
  · exfalso
    exact A_ne_B (Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective (hA.trans hB.symm))

theorem psi_a (hA : ∀ x ∈ A, ψ x ∈ A) (hB : ∀ x ∈ B, ψ x ∈ B) (y : Tc) :
    (ψ y).a = lc ψ y.a := by
  rw [psi_gen hA hB y]

theorem psi_b (hA : ∀ x ∈ A, ψ x ∈ A) (hB : ∀ x ∈ B, ψ x ∈ B) (y : Tc) :
    (ψ y).b = mc ψ y.b := by
  rw [psi_gen hA hB y]

theorem iterate_a (hA : ∀ x ∈ A, ψ x ∈ A) (hB : ∀ x ∈ B, ψ x ∈ B) (k : ℕ) (x : Tc) :
    (ψ^[k] x).a = (lc ψ)^[k] x.a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', psi_a hA hB, ih]

theorem iterate_b (hA : ∀ x ∈ A, ψ x ∈ A) (hB : ∀ x ∈ B, ψ x ∈ B) (k : ℕ) (x : Tc) :
    (ψ^[k] x).b = (mc ψ)^[k] x.b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', psi_b hA hB, ih]

theorem exists_scalars (hA : ∀ x ∈ A, ψ x ∈ A) (hB : ∀ x ∈ B, ψ x ∈ B) {j : ℕ} (hj : Odd j)
    (hψ : ∀ x, ψ^[j] x = x) :
    ∃ c₁ c₂ : F4c, c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ (∀ a, lc ψ a = c₁ * a) ∧ (∀ b, mc ψ b = c₂ * b) ∧
      (∀ c, gc ψ c = c₁ * c₂ * c) := by
  have hl : ∀ a, (lc ψ)^[j] a = a := fun a => by
    have := iterate_a hA hB j ⟨a, 0, 0⟩
    rw [hψ] at this
    exact this.symm
  have hm : ∀ b, (mc ψ)^[j] b = b := fun b => by
    have := iterate_b hA hB j ⟨0, b, 0⟩
    rw [hψ] at this
    exact this.symm
  obtain ⟨c₁, hc₁, hl'⟩ := add_bij_odd (lc ψ) (lc_add hA) hj hl
  obtain ⟨c₂, hc₂, hm'⟩ := add_bij_odd (mc ψ) (mc_add hB) hj hm
  refine ⟨c₁, c₂, hc₁, hc₂, hl', hm', fun c => ?_⟩
  have := gc_mul hA hB c 1
  rw [mul_one, hl', hm'] at this
  rw [this]
  ring

theorem inv_tc (x : Tc) : x⁻¹ = ⟨x.a, x.b, x.c + x.a * x.b⟩ := rfl

theorem two_eq_zero_F4c : (2 : F4c) = 0 := by decide

theorem add_one_ne_zero {c : F4c} (hc : c ≠ 1) : c + 1 ≠ 0 := by
  intro h
  apply hc
  have h1 := F4c_add_self (1 : F4c)
  have : c = c + 1 + 1 := by
    rw [add_assoc, h1, add_zero]
  rw [this, h, zero_add]

theorem scalar_eq_one_A {ψ : Tc ≃* Tc} (hA : ∀ x ∈ A, ψ x ∈ A) {D : Subgroup Tc}
    (hZ : Subgroup.center Tc ≤ D) (hAD : ¬ A ≤ D) (hD : ∀ x, ψ x * x⁻¹ ∈ D) {c₁ : F4c}
    (hl : ∀ a, lc ψ a = c₁ * a) : c₁ = 1 := by
  by_contra hc
  apply hAD
  intro x hx
  have hxb : x.b = 0 := hx
  have hne := add_one_ne_zero hc
  set a₀ : F4c := x.a * (c₁ + 1)⁻¹ with ha₀
  have hmul : (c₁ + 1) * a₀ = x.a := by
    rw [ha₀]; field_simp
  have hy := hD ⟨a₀, 0, 0⟩
  rw [psi_A hA, inv_tc, hl] at hy
  have hy' : (⟨x.a, 0, uc ψ a₀⟩ : Tc) ∈ D := by
    have : (⟨c₁ * a₀, 0, uc ψ a₀⟩ : Tc) * ⟨a₀, 0, 0 + a₀ * 0⟩ = ⟨x.a, 0, uc ψ a₀⟩ :=
      UT3.ext (by simp only [UT3.mul_def]; rw [← hmul]; ring) (by simp [UT3.mul_def])
        (by simp [UT3.mul_def])
    rwa [this] at hy
  have hz : (⟨0, 0, x.c + uc ψ a₀⟩ : Tc) ∈ D := hZ ((mem_center_iff _).2 ⟨rfl, rfl⟩)
  have hxeq : x = ⟨x.a, 0, uc ψ a₀⟩ * ⟨0, 0, x.c + uc ψ a₀⟩ := by
    refine UT3.ext (by simp [UT3.mul_def]) (by simp [UT3.mul_def, hxb]) ?_
    simp only [UT3.mul_def]
    have := F4c_add_self (uc ψ a₀)
    linear_combination (-1 : F4c) * this
  rw [hxeq]
  exact D.mul_mem hy' hz

theorem scalar_eq_one_B {ψ : Tc ≃* Tc} (hB : ∀ x ∈ B, ψ x ∈ B) {D : Subgroup Tc}
    (hZ : Subgroup.center Tc ≤ D) (hBD : ¬ B ≤ D) (hD : ∀ x, ψ x * x⁻¹ ∈ D) {c₂ : F4c}
    (hm : ∀ b, mc ψ b = c₂ * b) : c₂ = 1 := by
  by_contra hc
  apply hBD
  intro x hx
  have hxa : x.a = 0 := hx
  have hne := add_one_ne_zero hc
  set b₀ : F4c := x.b * (c₂ + 1)⁻¹ with hb₀
  have hmul : (c₂ + 1) * b₀ = x.b := by
    rw [hb₀]; field_simp
  have hy := hD ⟨0, b₀, 0⟩
  rw [psi_B hB, inv_tc, hm] at hy
  have hy' : (⟨0, x.b, vc ψ b₀⟩ : Tc) ∈ D := by
    have : (⟨0, c₂ * b₀, vc ψ b₀⟩ : Tc) * ⟨0, b₀, 0 + 0 * b₀⟩ = ⟨0, x.b, vc ψ b₀⟩ :=
      UT3.ext (by simp [UT3.mul_def]) (by simp only [UT3.mul_def]; rw [← hmul]; ring)
        (by simp [UT3.mul_def])
    rwa [this] at hy
  have hz : (⟨0, 0, x.c + vc ψ b₀⟩ : Tc) ∈ D := hZ ((mem_center_iff _).2 ⟨rfl, rfl⟩)
  have hxeq : x = ⟨0, x.b, vc ψ b₀⟩ * ⟨0, 0, x.c + vc ψ b₀⟩ := by
    refine UT3.ext (by simp [UT3.mul_def, hxa]) (by simp [UT3.mul_def]) ?_
    simp only [UT3.mul_def]
    have := F4c_add_self (vc ψ b₀)
    linear_combination (-1 : F4c) * this
  rw [hxeq]
  exact D.mul_mem hy' hz

theorem psi_one (hA : ∀ x ∈ A, ψ x ∈ A) (hB : ∀ x ∈ B, ψ x ∈ B) (h1 : ∀ a, lc ψ a = a)
    (h2 : ∀ b, mc ψ b = b) (h3 : ∀ c, gc ψ c = c) (x : Tc) :
    ψ x = ⟨x.a, x.b, uc ψ x.a + vc ψ x.b + x.c⟩ := by
  rw [psi_gen hA hB x, h1, h2, h3]
  refine UT3.ext rfl rfl ?_
  show uc ψ x.a + vc ψ x.b + x.a * x.b + (x.c + x.a * x.b) = uc ψ x.a + vc ψ x.b + x.c
  linear_combination (x.a * x.b) * two_eq_zero_F4c

theorem eq_self_of_scalars_one (hA : ∀ x ∈ A, ψ x ∈ A) (hB : ∀ x ∈ B, ψ x ∈ B) {j : ℕ}
    (hj : Odd j) (hψ : ∀ x, ψ^[j] x = x) (h1 : ∀ a, lc ψ a = a) (h2 : ∀ b, mc ψ b = b)
    (h3 : ∀ c, gc ψ c = c) (x : Tc) : ψ x = x := by
  have hinv : Function.Involutive (ψ : Tc → Tc) := by
    intro y
    have e1 := psi_one hA hB h1 h2 h3 y
    have e2 := psi_one hA hB h1 h2 h3 (ψ y)
    rw [e2]
    refine UT3.ext ?_ ?_ ?_
    · rw [e1]
    · rw [e1]
    · rw [e1]
      show uc ψ y.a + vc ψ y.b + (uc ψ y.a + vc ψ y.b + y.c) = y.c
      linear_combination (uc ψ y.a + vc ψ y.b) * two_eq_zero_F4c
  have := hψ x
  rwa [hinv.iterate_odd hj] at this

theorem oa_trivial_tc {ψ : Tc ≃* Tc} {j : ℕ} (hj : Odd j) (hψ : ∀ x, ψ^[j] x = x)
    {D : Subgroup Tc} (hZ : Subgroup.center Tc ≤ D) (hAD : ¬ A ≤ D) (hBD : ¬ B ≤ D)
    (hD : ∀ x, ψ x * x⁻¹ ∈ D) (x : Tc) : ψ x = x := by
  obtain ⟨hA, hB⟩ := preserves_of_odd hj hψ
  obtain ⟨c₁, c₂, -, -, hl, hm, hg⟩ := exists_scalars hA hB hj hψ
  have e1 := scalar_eq_one_A hA hZ hAD hD hl
  have e2 := scalar_eq_one_B hB hZ hBD hD hm
  subst e1
  subst e2
  exact eq_self_of_scalars_one hA hB hj hψ (fun a => by rw [hl, one_mul])
    (fun b => by rw [hm, one_mul]) (fun c => by rw [hg]; ring) x

theorem uc_zero (ψ : Tc ≃* Tc) : uc ψ 0 = 0 := by
  have : ψ (⟨0, 0, 0⟩ : Tc) = 1 := by rw [show (⟨0, 0, 0⟩ : Tc) = 1 from rfl, map_one]
  unfold uc
  rw [this]
  rfl

theorem vc_zero (ψ : Tc ≃* Tc) : vc ψ 0 = 0 := by
  have : ψ (⟨0, 0, 0⟩ : Tc) = 1 := by rw [show (⟨0, 0, 0⟩ : Tc) = 1 from rfl, map_one]
  unfold vc
  rw [this]
  rfl

theorem cube_eq_id {ψ : Tc ≃* Tc} {j : ℕ} (hj : Odd j) (hψ : ∀ x, ψ^[j] x = x) (x : Tc) :
    ψ (ψ (ψ x)) = x := by
  obtain ⟨hA, hB⟩ := preserves_of_odd hj hψ
  obtain ⟨c₁, c₂, hc₁, hc₂, hl, hm, hg⟩ := exists_scalars hA hB hj hψ
  set φ : Tc ≃* Tc := ψ.trans (ψ.trans ψ) with hφ
  have hφx : ∀ y, φ y = ψ (ψ (ψ y)) := fun y => rfl
  have hAφ : ∀ x ∈ A, φ x ∈ A := fun x hx => hA _ (hA _ (hA _ hx))
  have hBφ : ∀ x ∈ B, φ x ∈ B := fun x hx => hB _ (hB _ (hB _ hx))
  have hφj : ∀ y, φ^[j] y = y := by
    intro y
    have h3 : (φ : Tc → Tc) = ψ^[3] := rfl
    rw [h3, ← Function.iterate_mul, mul_comm, Function.iterate_mul]
    exact Function.IsFixedPt.iterate (hψ y) 3
  have hc1 := F4c_cube c₁ hc₁
  have hc2 := F4c_cube c₂ hc₂
  have h1 : ∀ a, lc φ a = a := by
    intro a
    show (φ ⟨a, 0, 0⟩).a = a
    rw [hφx, psi_a hA hB, psi_a hA hB, psi_a hA hB]
    show lc ψ (lc ψ (lc ψ a)) = a
    rw [hl, hl, hl]
    linear_combination a * hc1
  have h2 : ∀ b, mc φ b = b := by
    intro b
    show (φ ⟨0, b, 0⟩).b = b
    rw [hφx, psi_b hA hB, psi_b hA hB, psi_b hA hB]
    show mc ψ (mc ψ (mc ψ b)) = b
    rw [hm, hm, hm]
    linear_combination b * hc2
  have h3 : ∀ c, gc φ c = c := by
    intro c
    show (φ ⟨0, 0, c⟩).c = c
    rw [hφx, psi_Z, psi_Z, psi_Z]
    show gc ψ (gc ψ (gc ψ c)) = c
    rw [hg, hg, hg]
    linear_combination (c₂ * c₂ * c₂ * c) * hc1 + c * hc2
  exact eq_self_of_scalars_one hAφ hBφ hj hφj h1 h2 h3 x

theorem oa_cube_tc {ψ : Tc ≃* Tc} {j : ℕ} (hj : Odd j) (hψ : ∀ x, ψ^[j] x = x)
    (hD : ∀ x, ψ x * x⁻¹ ∈ A) :
    (∀ a ∈ A, ψ a = a) ∨ (∀ a ∈ A, ψ a = a → a = 1) := by
  obtain ⟨hA, hB⟩ := preserves_of_odd hj hψ
  obtain ⟨c₁, c₂, hc₁, hc₂, hl, hm, hg⟩ := exists_scalars hA hB hj hψ
  have hc₂1 : c₂ = 1 := by
    have h := hD ⟨0, 1, 0⟩
    rw [psi_B hB, inv_tc, hm] at h
    have hb : c₂ * 1 + 1 = 0 := h
    have h1 := F4c_add_self (1 : F4c)
    rw [mul_one] at hb
    calc c₂ = c₂ + 1 + 1 := by rw [add_assoc, h1, add_zero]
      _ = 1 := by rw [hb, zero_add]
  subst hc₂1
  by_cases hc : c₁ = 1
  · left
    subst hc
    intro a _
    exact eq_self_of_scalars_one hA hB hj hψ (fun a => by rw [hl, one_mul])
      (fun b => by rw [hm, one_mul]) (fun c => by rw [hg]; ring) a
  · right
    have hne := add_one_ne_zero hc
    intro a ha hψa
    have hab : a.b = 0 := ha
    have e1 := psi_gen hA hB a
    rw [hψa] at e1
    have ea : a.a = lc ψ a.a := by
      have h := congrArg UT3.a e1
      exact h
    have ec : a.c = uc ψ a.a + vc ψ a.b + lc ψ a.a * mc ψ a.b + gc ψ (a.c + a.a * a.b) := by
      have h := congrArg UT3.c e1
      exact h
    have ha0 : a.a = 0 := by
      rw [hl] at ea
      have : (c₁ + 1) * a.a = 0 := by
        linear_combination (-1 : F4c) * ea + a.a * two_eq_zero_F4c
      exact (mul_eq_zero.1 this).resolve_left hne
    have hc0 : a.c = 0 := by
      rw [ha0, hab, uc_zero, vc_zero, hl, hm, hg] at ec
      have : (c₁ + 1) * a.c = 0 := by
        linear_combination (-1 : F4c) * ec + a.c * two_eq_zero_F4c
      exact (mul_eq_zero.1 this).resolve_left hne
    exact UT3.ext ha0 hab hc0

end Coord

abbrev Ac : Subgroup Tc := CFSG.OddStandard.ThmC.T.A

abbrev Bc : Subgroup Tc := CFSG.OddStandard.ThmC.T.B

section Ambient

variable {G : Type*} [Group G]

theorem map_equiv_E16 {P : Type*} [Group P] (e : P ≃* Tc) {E : Subgroup P}
    (hsq : ∀ x ∈ E, x * x = 1) (hc : Nat.card E = 16) :
    E.map e.toMonoidHom = Ac ∨ E.map e.toMonoidHom = Bc := by
  apply eq_A_or_B
  · rintro _ ⟨x, hx, rfl⟩
    show e x * e x = 1
    rw [← map_mul, hsq x hx, map_one]
  · rw [Subgroup.card_map_of_injective e.injective, hc]

theorem exists_coordinates {S Z A B : Subgroup G} (hS : IsT S) (hTA : TAmbient S Z A B) :
    ∃ e : S ≃* Tc, (∀ s : S, (s : G) ∈ A ↔ (e s).b = 0) ∧ (∀ s : S, (s : G) ∈ B ↔ (e s).a = 0) := by
  obtain ⟨e₀⟩ := hS.nonempty_equiv
  set A' : Subgroup S := A.subgroupOf S with hA'
  set B' : Subgroup S := B.subgroupOf S with hB'
  have hA'sq : ∀ x ∈ A', x * x = 1 := fun x hx => by
    apply Subtype.ext
    have := hTA.A_sq x.1 hx
    exact this
  have hB'sq : ∀ x ∈ B', x * x = 1 := fun x hx => by
    apply Subtype.ext
    have := hTA.B_sq x.1 hx
    exact this
  have hA'c : Nat.card A' = 16 := by
    rw [← hTA.card_A]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA.A_le_S).toEquiv
  have hB'c : Nat.card B' = 16 := by
    rw [← hTA.card_B]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA.B_le_S).toEquiv
  have hAB' : A' ≠ B' := fun h => hTA.A_ne_B (by
    have := congrArg (Subgroup.map S.subtype) h
    rwa [hA', hB', Subgroup.map_subgroupOf_eq_of_le hTA.A_le_S,
      Subgroup.map_subgroupOf_eq_of_le hTA.B_le_S] at this)
  have hmem : ∀ (F : Subgroup S) (E : Subgroup Tc), F.map e₀.toMonoidHom = E →
      ∀ s : S, s ∈ F ↔ e₀ s ∈ E := fun F E h s => by
    rw [← h, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rcases map_equiv_E16 e₀ hA'sq hA'c with hA | hA
  · have hB : B'.map e₀.toMonoidHom = Bc := by
      rcases map_equiv_E16 e₀ hB'sq hB'c with hB | hB
      · exact absurd (Subgroup.map_injective (f := e₀.toMonoidHom) e₀.injective
          (hA.trans hB.symm)) hAB'
      · exact hB
    refine ⟨e₀, fun s => ?_, fun s => ?_⟩
    · exact (hmem A' Ac hA s).trans Iff.rfl
    · exact (hmem B' Bc hB s).trans Iff.rfl
  · have hB : B'.map e₀.toMonoidHom = Ac := by
      rcases map_equiv_E16 e₀ hB'sq hB'c with hB | hB
      · exact hB
      · exact absurd (Subgroup.map_injective (f := e₀.toMonoidHom) e₀.injective
          (hA.trans hB.symm)) hAB'
    refine ⟨e₀.trans swap, fun s => ?_, fun s => ?_⟩
    · have h1 := (hmem A' Bc hA s)
      show (s : G) ∈ A ↔ (swap (e₀ s)).b = 0
      exact h1.trans Iff.rfl
    · have h1 := (hmem B' Ac hB s)
      show (s : G) ∈ B ↔ (swap (e₀ s)).a = 0
      exact h1.trans Iff.rfl

theorem conj_iterate {S : Subgroup G} {m : G} (hm : m ∈ Subgroup.normalizer (S : Set G)) (k : ℕ)
    (s : S) : (((conjEquiv S hm)^[k] s : S) : G) = m ^ k * s * (m ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', coe_conjEquiv, ih]
    rw [pow_succ']
    group

@[expose] def inducedAut {S : Subgroup G} (e : S ≃* Tc) {m : G}
    (hm : m ∈ Subgroup.normalizer (S : Set G)) : Tc ≃* Tc :=
  e.symm.trans ((conjEquiv S hm).trans e)

theorem inducedAut_apply {S : Subgroup G} (e : S ≃* Tc) {m : G}
    (hm : m ∈ Subgroup.normalizer (S : Set G)) (x : Tc) :
    inducedAut e hm x = e (conjEquiv S hm (e.symm x)) := rfl

theorem inducedAut_iterate {S : Subgroup G} (e : S ≃* Tc) {m : G}
    (hm : m ∈ Subgroup.normalizer (S : Set G)) (k : ℕ) (x : Tc) :
    (inducedAut e hm)^[k] x = e ((conjEquiv S hm)^[k] (e.symm x)) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, inducedAut_apply, ih,
      e.symm_apply_apply]

theorem inducedAut_iterate_eq {S : Subgroup G} (e : S ≃* Tc) {m : G}
    (hm : m ∈ Subgroup.normalizer (S : Set G)) (k : ℕ) (s : S) :
    (inducedAut e hm)^[k] (e s) = e ((conjEquiv S hm)^[k] s) := by
  rw [inducedAut_iterate, e.symm_apply_apply]

theorem inducedAut_iterate_id {S : Subgroup G} (e : S ≃* Tc) {m : G}
    (hm : m ∈ Subgroup.normalizer (S : Set G)) {j : ℕ} (hmj : ∀ s ∈ S, m ^ j * s * (m ^ j)⁻¹ = s)
    (x : Tc) : (inducedAut e hm)^[j] x = x := by
  rw [inducedAut_iterate]
  have : (conjEquiv S hm)^[j] (e.symm x) = e.symm x :=
    Subtype.ext (by rw [conj_iterate]; exact hmj _ (e.symm x).2)
  rw [this, e.apply_symm_apply]

theorem oa_trivial {S Z A B : Subgroup G} (hS : IsT S) (hTA : TAmbient S Z A B) {m : G}
    (hm : m ∈ Subgroup.normalizer (S : Set G)) {j : ℕ} (hj : Odd j)
    (hmj : ∀ s ∈ S, m ^ j * s * (m ^ j)⁻¹ = s) {D : Subgroup G} (hZD : Z ≤ D) (hAD : ¬ A ≤ D)
    (hBD : ¬ B ≤ D) (hD : ∀ s ∈ S, m * s * m⁻¹ * s⁻¹ ∈ D) :
    ∀ s ∈ S, m * s * m⁻¹ = s := by
  obtain ⟨e, heA, heB⟩ := exists_coordinates hS hTA
  set ψ := inducedAut e hm with hψ
  have hψj := inducedAut_iterate_id e hm hmj
  set D' : Subgroup Tc := (D.subgroupOf S).map e.toMonoidHom with hD'
  have hmemD' : ∀ s : S, e s ∈ D' ↔ (s : G) ∈ D := fun s => by
    rw [hD', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]
  have hZ : Subgroup.center Tc ≤ D' := by
    intro z hz
    have hz' : e.symm z ∈ Subgroup.center S := (mem_center_equiv_iff e.symm z).1 hz
    have hZmem : ((e.symm z : S) : G) ∈ Z := by
      rw [hTA.mem_Z]
      refine ⟨(e.symm z).2, fun t ht => ?_⟩
      have := Subgroup.mem_center_iff.1 hz' ⟨t, ht⟩
      exact (congrArg Subtype.val this).symm
    have := (hmemD' (e.symm z)).2 (hZD hZmem)
    rwa [MulEquiv.apply_symm_apply] at this
  have hAD' : ¬ Ac ≤ D' := fun h => hAD (fun g hg => by
    have hgS : g ∈ S := hTA.A_le_S hg
    have h1 : e ⟨g, hgS⟩ ∈ Ac := (heA ⟨g, hgS⟩).1 hg
    exact (hmemD' ⟨g, hgS⟩).1 (h h1))
  have hBD' : ¬ Bc ≤ D' := fun h => hBD (fun g hg => by
    have hgS : g ∈ S := hTA.B_le_S hg
    have h1 : e ⟨g, hgS⟩ ∈ Bc := (heB ⟨g, hgS⟩).1 hg
    exact (hmemD' ⟨g, hgS⟩).1 (h h1))
  have hD'' : ∀ x, ψ x * x⁻¹ ∈ D' := by
    intro x
    obtain ⟨t, rfl⟩ := e.surjective x
    rw [hψ, inducedAut_apply, e.symm_apply_apply, ← map_inv, ← map_mul, hmemD']
    have := hD t t.2
    simpa [coe_conjEquiv] using this
  have key := oa_trivial_tc hj hψj hZ hAD' hBD' hD''
  intro s hs
  have h1 := key (e ⟨s, hs⟩)
  rw [inducedAut_apply, e.symm_apply_apply] at h1
  have h2 := e.injective h1
  have := congrArg Subtype.val h2
  simpa [coe_conjEquiv] using this

theorem oa_cube {S Z A B : Subgroup G} (hS : IsT S) (hTA : TAmbient S Z A B) {m : G}
    (hm : m ∈ Subgroup.normalizer (S : Set G)) {j : ℕ} (hj : Odd j)
    (hmj : ∀ s ∈ S, m ^ j * s * (m ^ j)⁻¹ = s) (hD : ∀ s ∈ S, m * s * m⁻¹ * s⁻¹ ∈ A) :
    ((∀ a ∈ A, m * a * m⁻¹ = a) ∨ (∀ a ∈ A, m * a * m⁻¹ = a → a = 1)) ∧
      ∀ s ∈ S, m ^ 3 * s * (m ^ 3)⁻¹ = s := by
  obtain ⟨e, heA, heB⟩ := exists_coordinates hS hTA
  set ψ := inducedAut e hm with hψ
  have hψj := inducedAut_iterate_id e hm hmj
  have hD'' : ∀ x, ψ x * x⁻¹ ∈ Ac := by
    intro x
    obtain ⟨t, rfl⟩ := e.surjective x
    rw [hψ, inducedAut_apply, e.symm_apply_apply, ← map_inv, ← map_mul]
    have h1 := hD t t.2
    have h2 : ((conjEquiv S hm t * t⁻¹ : S) : G) ∈ A := by
      simpa [coe_conjEquiv] using h1
    exact (heA _).1 h2
  refine ⟨?_, fun s hs => ?_⟩
  · rcases oa_cube_tc hj hψj hD'' with h | h
    · left
      intro a ha
      have hgS : a ∈ S := hTA.A_le_S ha
      have h1 := h (e ⟨a, hgS⟩) ((heA ⟨a, hgS⟩).1 ha)
      rw [inducedAut_apply, e.symm_apply_apply] at h1
      have := congrArg Subtype.val (e.injective h1)
      simpa [coe_conjEquiv] using this
    · right
      intro a ha hma
      have hgS : a ∈ S := hTA.A_le_S ha
      have h1 := h (e ⟨a, hgS⟩) ((heA ⟨a, hgS⟩).1 ha)
      rw [inducedAut_apply, e.symm_apply_apply] at h1
      have h2 : e (conjEquiv S hm ⟨a, hgS⟩) = e ⟨a, hgS⟩ := by
        apply congrArg e
        apply Subtype.ext
        simpa [coe_conjEquiv] using hma
      have h3 := h1 h2
      have h4 : (⟨a, hgS⟩ : S) = 1 := e.injective (by rw [h3, map_one])
      exact congrArg Subtype.val h4
  · have h1 := cube_eq_id hj hψj (e ⟨s, hs⟩)
    have h3 : ψ (ψ (ψ (e ⟨s, hs⟩))) = (ψ^[3]) (e ⟨s, hs⟩) := rfl
    rw [h3, inducedAut_iterate_eq] at h1
    have := congrArg Subtype.val (e.injective h1)
    rw [conj_iterate] at this
    exact this

end Ambient

end CFSG.OddStandard.ThmC.Core
