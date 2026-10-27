module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NQ0

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem M12C_one_fix : ∀ a b : Fin 2,
    lin (comp (pw (M2C 1) b) (pw (M1C 1) a)) (1, 0, 0, 0) = (1, 0, 0, 0) →
    lin (comp (pw (M2C 1) b) (pw (M1C 1) a)) (0, 1, 0, 0) = (0, 1, 0, 0) → a = 0 ∧ b = 0 := by
  decide

theorem M1C_two_fix : ∀ e : V4, e.2.2.1 = 0 → lin (M1C 1) e = e → lin (M2C 1) e = e →
    e.1 = 0 ∧ e.2.1 = 0 := by
  decide

theorem M1C_two_ki : lin (M1C 1) (0, 0, 0, 1) = (0, 0, 0, 1) := by decide

theorem M2C_two_ki : lin (M2C 1) (0, 0, 0, 1) = (0, 0, 0, 1) := by decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Inst

variable {I : S.Inst}

theorem commute_of_fix {n : X} {c : Fin 4 → V4} (hn : I.Mat n c) {p : V4} (hp : lin c p = p) :
    n * I.wV p = I.wV p * n := by
  have h := hn.conj p
  rw [hp] at h
  calc n * I.wV p = n * I.wV p * n⁻¹ * n := by group
    _ = I.wV p * n := by rw [h]

theorem mem_closure_ki_iff {a : X} : a ∈ closure {I.ki} ↔ a = 1 ∨ a = I.ki := by
  rw [← zpowers_eq_closure, mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have h2 : I.ki ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, I.ki_sq]
    obtain ⟨j, hj⟩ : ∃ j : ℤ, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩
    rcases hj with rfl | rfl
    · left; rw [zpow_mul, h2, one_zpow]
    · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem ki_ne_one (I : S.Inst) : I.ki ≠ 1 := by
  intro h
  have := I.wV_injective ((show I.wV (0, 0, 0, 1) = I.ki by simp [wV]).trans
    (h.trans I.wV_zero.symm))
  simp at this

namespace QRel

variable {ε : Fin 2} {w₁ w₂ : X} {s1 s4 : Fin 2} {γ : V4} (R : I.QRel ε w₁ w₂ s1 s4 γ)
include R

theorem central_of_gens {x : X} (hz : x * S.z = S.z * x) (hy : x * I.yi = I.yi * x)
    (hk : x * I.ki = I.ki * x) (h1 : x * w₁ = w₁ * x) (h2 : x * w₂ = w₂ * x) :
    ∀ b ∈ S.Q0 I.yi I.ki w₁ w₂, x * b = b * x := by
  intro b hb
  have hC : closure {S.z, I.yi, I.ki, w₁, w₂} ≤ centralizer ({x} : Set X) := by
    rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hz.symm
    · exact hy.symm
    · exact hk.symm
    · exact h1.symm
    · exact h2.symm
  exact (mem_centralizer_singleton_iff.mp (hC (I.Q0_le_closure w₁ w₂ hb))).symm

theorem E0_central_one (hε : ε = 0) {e : X} (he : e ∈ S.E0 I.yi I.ki) :
    ∀ b ∈ S.Q0 I.yi I.ki w₁ w₂, e * b = b * e := by
  subst hε
  obtain ⟨a, b', d, rfl⟩ := (I.mem_E0_iff).mp he
  have hcomm : ∀ g ∈ I.E, I.wV (a, b', 0, d) * g = g * I.wV (a, b', 0, d) :=
    fun g hg => I.comm (I.wV_mem _) hg
  refine R.central_of_gens (hcomm _ I.z_mem_E) (hcomm _ I.yi_mem_E) (hcomm _ I.ki_mem_E) ?_ ?_
  · exact (commute_of_fix R.m1 (M1C_fix_one a b' d)).symm
  · exact (commute_of_fix R.m2 (M2C_fix_one a b' d)).symm

theorem comm_one (hε : ε = 0) (hγ : γ = (0, 0, 0, 0)) :
    ∀ a ∈ S.Q0 I.yi I.ki w₁ w₂, ∀ b ∈ S.Q0 I.yi I.ki w₁ w₂, a * b = b * a := by
  intro a ha b hb
  refine comm_of_mem_closure ?_ (I.Q0_le_closure w₁ w₂ ha) (I.Q0_le_closure w₁ w₂ hb)
  have h12 : w₁ * w₂ = w₂ * w₁ := by
    have e := R.comm
    rw [hγ, I.wV_zero] at e
    calc w₁ * w₂ = (w₁ * w₂ * w₁⁻¹ * w₂⁻¹) * w₂ * w₁ := by group
      _ = w₂ * w₁ := by rw [e, one_mul]
  have hE : ∀ g ∈ ({S.z, I.yi, I.ki} : Set X), g ∈ S.E0 I.yi I.ki := fun g hg =>
    subset_closure hg
  intro x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  have hxE : x = w₁ ∨ x = w₂ ∨ x ∈ S.E0 I.yi I.ki := by
    rcases hx with h | h | h | h | h
    · exact Or.inr (Or.inr (by rw [h]; exact hE _ (by simp)))
    · exact Or.inr (Or.inr (by rw [h]; exact hE _ (by simp)))
    · exact Or.inr (Or.inr (by rw [h]; exact hE _ (by simp)))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hyQ : y ∈ S.Q0 I.yi I.ki w₁ w₂ := by
    rcases hy with h | h | h | h | h <;> rw [h]
    · exact I.E0_le_Q0 w₁ w₂ (hE _ (by simp))
    · exact I.E0_le_Q0 w₁ w₂ (hE _ (by simp))
    · exact I.E0_le_Q0 w₁ w₂ (hE _ (by simp))
    · exact I.w₁_mem_Q0 w₁ w₂
    · exact I.w₂_mem_Q0 w₁ w₂
  rcases hxE with hx | hx | hxE
  · rw [hx]
    rcases hy with h | h | h | h | h <;> rw [h]
    · exact (R.E0_central_one hε (hE _ (by simp)) _ (I.w₁_mem_Q0 _ _)).symm
    · exact (R.E0_central_one hε (hE _ (by simp)) _ (I.w₁_mem_Q0 _ _)).symm
    · exact (R.E0_central_one hε (hE _ (by simp)) _ (I.w₁_mem_Q0 _ _)).symm
    · exact h12
  · rw [hx]
    rcases hy with h | h | h | h | h <;> rw [h]
    · exact (R.E0_central_one hε (hE _ (by simp)) _ (I.w₂_mem_Q0 _ _)).symm
    · exact (R.E0_central_one hε (hE _ (by simp)) _ (I.w₂_mem_Q0 _ _)).symm
    · exact (R.E0_central_one hε (hE _ (by simp)) _ (I.w₂_mem_Q0 _ _)).symm
    · exact h12.symm
  · exact R.E0_central_one hε hxE y hyQ

theorem sq_one (hε : ε = 0) (hγ : γ = (0, 0, 0, 0)) (hs1 : s1 = 0) (hs4 : s4 = 0) :
    ∀ a ∈ S.Q0 I.yi I.ki w₁ w₂, a ^ 2 = 1 := by
  intro x hx
  obtain ⟨a, b, e, he, rfl⟩ := R.mem_Q0_iff.mp hx
  have hcomm := R.comm_one hε hγ
  have hw₁ : w₁ ^ 2 = 1 := by rw [R.sq1, hs1, hs4, I.wV_zero]
  have hw₂ : w₂ ^ 2 = 1 := by
    rw [R.sq2, hs1, hs4, show lin dCols (0, 0, 0, 0) = (0, 0, 0, 0) by decide, I.wV_zero]
  have he2 : e ^ 2 = 1 := I.sq_eq_one (I.E0_le_E he)
  have h1 : Commute (w₂ ^ (b : ℕ)) (w₁ ^ (a : ℕ)) :=
    hcomm _ (pow_mem (I.w₂_mem_Q0 _ _) _) _ (pow_mem (I.w₁_mem_Q0 _ _) _)
  have h2 : Commute (w₂ ^ (b : ℕ) * w₁ ^ (a : ℕ)) e :=
    hcomm _ (mul_mem (pow_mem (I.w₂_mem_Q0 _ _) _) (pow_mem (I.w₁_mem_Q0 _ _) _)) _
      (I.E0_le_Q0 _ _ he)
  rw [h2.mul_pow, h1.mul_pow, he2, ← pow_mul, ← pow_mul, mul_comm (b : ℕ), mul_comm (a : ℕ),
    pow_mul, pow_mul, hw₁, hw₂]
  simp

theorem center_one (hε : ε = 0) (hγ : γ = (0, 0, 0, 1)) :
    CenterEq (S.Q0 I.yi I.ki w₁ w₂) (S.E0 I.yi I.ki) := by
  intro x hx
  refine ⟨fun hc => ?_, fun he => R.E0_central_one hε he⟩
  obtain ⟨a, b, e, he, rfl⟩ := R.mem_Q0_iff.mp hx
  have hγ' : w₁ * w₂ * w₁⁻¹ * w₂⁻¹ = I.ki := by rw [R.comm, hγ]; simp [wV]
  have hk : w₂ * w₁ * w₂⁻¹ * w₁⁻¹ = I.ki := by
    have e1 : w₂ * w₁ * w₂⁻¹ * w₁⁻¹ = (w₁ * w₂ * w₁⁻¹ * w₂⁻¹)⁻¹ := by group
    rw [e1, hγ']
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact I.ki_sq)
  have hew₁ : e * w₁ * e⁻¹ = w₁ := by
    rw [R.E0_central_one hε he w₁ (I.w₁_mem_Q0 _ _)]; group
  have hew₂ : e * w₂ * e⁻¹ = w₂ := by
    rw [R.E0_central_one hε he w₂ (I.w₂_mem_Q0 _ _)]; group
  have hx₁ : (w₂ ^ (b : ℕ) * w₁ ^ (a : ℕ) * e) * w₁ * (w₂ ^ (b : ℕ) * w₁ ^ (a : ℕ) * e)⁻¹ = w₁ := by
    rw [hc w₁ (I.w₁_mem_Q0 _ _)]; group
  have hx₂ : (w₂ ^ (b : ℕ) * w₁ ^ (a : ℕ) * e) * w₂ * (w₂ ^ (b : ℕ) * w₁ ^ (a : ℕ) * e)⁻¹ = w₂ := by
    rw [hc w₂ (I.w₂_mem_Q0 _ _)]; group
  have hc₁ : (w₂ ^ (b : ℕ) * w₁ ^ (a : ℕ) * e) * w₁ * (w₂ ^ (b : ℕ) * w₁ ^ (a : ℕ) * e)⁻¹ =
      w₂ ^ (b : ℕ) * w₁ * (w₂ ^ (b : ℕ))⁻¹ := by
    calc _ = w₂ ^ (b : ℕ) * w₁ ^ (a : ℕ) * (e * w₁ * e⁻¹) * (w₁ ^ (a : ℕ))⁻¹ *
          (w₂ ^ (b : ℕ))⁻¹ := by group
      _ = _ := by rw [hew₁]; group
  have hc₂ : (w₂ ^ (b : ℕ) * w₁ ^ (a : ℕ) * e) * w₂ * (w₂ ^ (b : ℕ) * w₁ ^ (a : ℕ) * e)⁻¹ =
      w₂ ^ (b : ℕ) * (w₁ ^ (a : ℕ) * w₂ * (w₁ ^ (a : ℕ))⁻¹) * (w₂ ^ (b : ℕ))⁻¹ := by
    calc _ = w₂ ^ (b : ℕ) * w₁ ^ (a : ℕ) * (e * w₂ * e⁻¹) * (w₁ ^ (a : ℕ))⁻¹ *
          (w₂ ^ (b : ℕ))⁻¹ := by group
      _ = _ := by rw [hew₂]; group
  rw [hc₁] at hx₁
  rw [hc₂] at hx₂
  fin_cases b
  · fin_cases a
    · simpa using he
    · exfalso
      apply I.ki_ne_one
      simp only [pow_zero, one_mul, inv_one, mul_one, pow_one] at hx₂
      rw [← hγ', hx₂]; group
  · exfalso
    apply I.ki_ne_one
    simp only [pow_one] at hx₁
    rw [← hk, hx₁]; group

theorem center_two (hε : ε = 1) : CenterEq (S.Q0 I.yi I.ki w₁ w₂) (closure {I.ki}) := by
  subst hε
  have hk1 : w₁ * I.ki = I.ki * w₁ := by
    have := commute_of_fix R.m1 M1C_two_ki
    simpa [wV] using this
  have hk2 : w₂ * I.ki = I.ki * w₂ := by
    have := commute_of_fix R.m2 M2C_two_ki
    simpa [wV] using this
  intro x hx
  constructor
  · intro hc
    obtain ⟨a, b, e, he, rfl⟩ := R.mem_Q0_iff.mp hx
    obtain ⟨p1, p2, p4, rfl⟩ := (I.mem_E0_iff).mp he
    have hxM : I.Mat (w₂ ^ (b : ℕ) * w₁ ^ (a : ℕ) * I.wV (p1, p2, 0, p4))
        (comp (pw (M2C 1) b) (pw (M1C 1) a)) :=
      ((R.m2.pw b).mul (R.m1.pw a)).mul_central (I.E_le_centralizer (I.wV_mem _))
    have hfix : ∀ q : V4, I.wV q ∈ S.Q0 I.yi I.ki w₁ w₂ →
        lin (comp (pw (M2C 1) b) (pw (M1C 1) a)) q = q := by
      intro q hq
      apply I.wV_injective
      rw [← hxM.conj q, hc _ hq]; group
    obtain ⟨ha, hb⟩ := M12C_one_fix a b (hfix _ (I.E0_le_Q0 _ _ (I.wV_mem_E0 1 0 0)))
      (hfix _ (I.E0_le_Q0 _ _ (I.wV_mem_E0 0 1 0)))
    subst ha hb
    simp only [Fin.val_zero, pow_zero, one_mul] at hc ⊢
    have h1 : lin (M1C 1) (p1, p2, 0, p4) = (p1, p2, 0, p4) := by
      have e1 := hc w₁ (I.w₁_mem_Q0 _ _)
      have e2 := R.m1.conj (p1, p2, 0, p4)
      apply I.wV_injective
      rw [← e2]
      calc w₁ * I.wV (p1, p2, 0, p4) * w₁⁻¹ = I.wV (p1, p2, 0, p4) * w₁ * w₁⁻¹ := by rw [← e1]
        _ = I.wV (p1, p2, 0, p4) := by group
    have h2 : lin (M2C 1) (p1, p2, 0, p4) = (p1, p2, 0, p4) := by
      have e1 := hc w₂ (I.w₂_mem_Q0 _ _)
      have e2 := R.m2.conj (p1, p2, 0, p4)
      apply I.wV_injective
      rw [← e2]
      calc w₂ * I.wV (p1, p2, 0, p4) * w₂⁻¹ = I.wV (p1, p2, 0, p4) * w₂ * w₂⁻¹ := by rw [← e1]
        _ = I.wV (p1, p2, 0, p4) := by group
    obtain ⟨hp1, hp2⟩ := M1C_two_fix (p1, p2, 0, p4) rfl h1 h2
    simp only at hp1 hp2
    subst hp1 hp2
    rw [mem_closure_ki_iff]
    rcases Fin.exists_fin_two.mp ⟨p4, rfl⟩ with rfl | rfl
    · left; simp [wV]
    · right; simp [wV]
  · intro hx'
    rcases (mem_closure_ki_iff.mp hx') with rfl | rfl
    · intro b _; simp
    · refine R.central_of_gens ?_ ?_ ?_ hk1.symm hk2.symm
      · exact I.comm I.ki_mem_E I.z_mem_E
      · exact I.comm I.ki_mem_E I.yi_mem_E
      · rfl

end QRel

end Inst

end A7Base

end CFSG.ComponentClassification.HSFLit
