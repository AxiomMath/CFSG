module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NMu
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46NInst

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C}

namespace Inst

variable (I : Inst S)

theorem wV_lin (c : Fin 4 → V4) (w : V4) :
    I.wV (lin c w) = I.wV (c 0) ^ (w.1 : ℕ) * I.wV (c 1) ^ (w.2.1 : ℕ) *
      I.wV (c 2) ^ (w.2.2.1 : ℕ) * I.wV (c 3) ^ (w.2.2.2 : ℕ) := by
  rw [lin, I.wV_add, I.wV_add, I.wV_add, I.wV_smul, I.wV_smul, I.wV_smul, I.wV_smul]

theorem wV_eq_prod (w : V4) :
    I.wV w = I.wV (bas 0) ^ (w.1 : ℕ) * I.wV (bas 1) ^ (w.2.1 : ℕ) *
      I.wV (bas 2) ^ (w.2.2.1 : ℕ) * I.wV (bas 3) ^ (w.2.2.2 : ℕ) := by
  have : lin bas w = w := by
    obtain ⟨a, b, c, d⟩ := w
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> rfl
  rw [← I.wV_lin, this]

theorem conj_wV_mem {n : X} (hn : n ∈ normalizer (I.E : Set X)) (w : V4) :
    n * I.wV w * n⁻¹ ∈ I.E :=
  (mem_normalizer_iff.mp hn _).mp (I.wV_mem w)

noncomputable def μ (n : normalizer (I.E : Set X)) (w : V4) : V4 :=
  Classical.choose (I.eq_wV (I.conj_wV_mem n.2 w))

theorem conj_wV (n : normalizer (I.E : Set X)) (w : V4) :
    (n : X) * I.wV w * (n : X)⁻¹ = I.wV (I.μ n w) :=
  Classical.choose_spec (I.eq_wV (I.conj_wV_mem n.2 w))

theorem μ_eq_of {n : normalizer (I.E : Set X)} {w v : V4}
    (h : (n : X) * I.wV w * (n : X)⁻¹ = I.wV v) : I.μ n w = v :=
  I.wV_injective ((I.conj_wV n w).symm.trans h)

theorem μ_eq_lin (n : normalizer (I.E : Set X)) (w : V4) :
    I.μ n w = lin (fun i => I.μ n (bas i)) w := by
  apply I.μ_eq_of
  rw [I.wV_lin, I.wV_eq_prod w]
  simp only [← I.conj_wV]
  have hc : ∀ g : X, (n : X) * g * (n : X)⁻¹ = MulAut.conj (n : X) g := fun g => rfl
  simp only [hc, map_mul, map_pow]

theorem μ_mul (n m : normalizer (I.E : Set X)) (w : V4) : I.μ (n * m) w = I.μ n (I.μ m w) := by
  apply I.μ_eq_of
  rw [← I.conj_wV, ← I.conj_wV]
  simp only [Subgroup.coe_mul, mul_inv_rev]
  group

theorem μ_one (w : V4) : I.μ 1 w = w := I.μ_eq_of (by simp)

theorem μ_eq_id_iff (n : normalizer (I.E : Set X)) :
    (∀ i, I.μ n (bas i) = bas i) ↔ (n : X) ∈ centralizer (I.E : Set X) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨w, rfl⟩ := I.eq_wV hg
    have h1 : I.μ n w = w := by
      rw [I.μ_eq_lin]
      simp only [h]
      obtain ⟨a, b, c, d⟩ := w
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> rfl
    have h2 := I.conj_wV n w
    rw [h1] at h2
    calc I.wV w * (n : X) = (n : X) * I.wV w * (n : X)⁻¹ * (n : X) := by rw [h2]
      _ = (n : X) * I.wV w := by group
  · intro h i
    apply I.μ_eq_of
    rw [mem_centralizer_iff] at h
    rw [← h _ (I.wV_mem _)]
    group

theorem wV_bas_zero : I.wV (bas 0) = S.z := by simp [wV, bas]

theorem wV_bas_one : I.wV (bas 1) = I.yi := by simp [wV, bas]

theorem wV_bas_two : I.wV (bas 2) = t := by simp [wV, bas]

theorem wV_bas_three : I.wV (bas 3) = I.ki := by simp [wV, bas]

theorem μ_bas_of {n : normalizer (I.E : Set X)} {c : Fin 4 → V4}
    (h0 : (n : X) * S.z * (n : X)⁻¹ = I.wV (c 0)) (h1 : (n : X) * I.yi * (n : X)⁻¹ = I.wV (c 1))
    (h2 : (n : X) * t * (n : X)⁻¹ = I.wV (c 2)) (h3 : (n : X) * I.ki * (n : X)⁻¹ = I.wV (c 3))
    (i : Fin 4) : I.μ n (bas i) = c i := by
  apply I.μ_eq_of
  fin_cases i
  · show (n : X) * I.wV (bas 0) * (n : X)⁻¹ = I.wV (c 0)
    rw [I.wV_bas_zero]; exact h0
  · show (n : X) * I.wV (bas 1) * (n : X)⁻¹ = I.wV (c 1)
    rw [I.wV_bas_one]; exact h1
  · show (n : X) * I.wV (bas 2) * (n : X)⁻¹ = I.wV (c 2)
    rw [I.wV_bas_two]; exact h2
  · show (n : X) * I.wV (bas 3) * (n : X)⁻¹ = I.wV (c 3)
    rw [I.wV_bas_three]; exact h3

end Inst

end CFSG.ComponentClassification.HSFLit.KD46
