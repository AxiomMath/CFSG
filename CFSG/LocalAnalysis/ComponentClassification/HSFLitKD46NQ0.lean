module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46NW1
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NQ0

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C}

namespace Inst

variable (I : Inst S)

theorem wV_mem_E0 (a b d : Fin 2) : I.wV (a, b, 0, d) ∈ S.E0 I.yi I.ki :=
  (I.mem_E0_iff).mpr ⟨a, b, d, rfl⟩

theorem wV_mem_E0' {p : V4} (hp : p.2.2.1 = 0) : I.wV p ∈ S.E0 I.yi I.ki := by
  obtain ⟨a, b, c, d⟩ := p
  simp only at hp
  subst hp
  exact I.wV_mem_E0 a b d

theorem E0_le_centralizer : S.E0 I.yi I.ki ≤ centralizer (I.E : Set X) :=
  I.E0_le_E.trans I.E_le_centralizer

theorem card_E0 : Nat.card (S.E0 I.yi I.ki) = 8 := by
  let f : Fin 2 × Fin 2 × Fin 2 → S.E0 I.yi I.ki :=
    fun p => ⟨I.wV (p.1, p.2.1, 0, p.2.2), I.wV_mem_E0 _ _ _⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => ?_, fun e => ?_⟩
    · have := I.wV_injective (congrArg Subtype.val h)
      simp only [Prod.mk.injEq] at this
      obtain ⟨h1, h2, -, h4⟩ := this
      exact Prod.ext h1 (Prod.ext h2 h4)
    · obtain ⟨a, b, d, hd⟩ := (I.mem_E0_iff).mp e.2
      exact ⟨(a, b, d), Subtype.ext hd.symm⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

theorem mem_normalizer_E0 {n : X} {c : Fin 4 → V4} (hn : I.Mat n c)
    (hc : ∀ a b d : Fin 2, (lin c (a, b, 0, d)).2.2.1 = 0) :
    n ∈ normalizer (S.E0 I.yi I.ki : Set X) :=
  mem_normalizer_of_conj_mem fun e he => by
    obtain ⟨a, b, d, rfl⟩ := (I.mem_E0_iff).mp he
    rw [hn.conj]
    exact I.wV_mem_E0' (hc a b d)

theorem E0_le_Q0 (w₁ w₂ : X) : S.E0 I.yi I.ki ≤ S.Q0 I.yi I.ki w₁ w₂ :=
  le_sup_left.trans le_sup_left

theorem w₁_mem_Q0 (w₁ w₂ : X) : w₁ ∈ S.Q0 I.yi I.ki w₁ w₂ :=
  mem_sup_left (mem_sup_right (mem_zpowers w₁))

theorem w₂_mem_Q0 (w₁ w₂ : X) : w₂ ∈ S.Q0 I.yi I.ki w₁ w₂ := mem_sup_right (mem_zpowers w₂)

theorem Q0_le_closure (w₁ w₂ : X) : S.Q0 I.yi I.ki w₁ w₂ ≤ closure {S.z, I.yi, I.ki, w₁, w₂} := by
  refine sup_le (sup_le (closure_mono ?_) (zpowers_le.mpr (subset_closure (by simp))))
    (zpowers_le.mpr (subset_closure (by simp)))
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with h | h | h <;> simp [h]

structure QRel (ε : Fin 2) (w₁ w₂ : X) (s1 s4 : Fin 2) (γ : V4) : Prop where
  m1 : I.Mat w₁ (M1C ε)
  m2 : I.Mat w₂ (M2C ε)
  sq1 : w₁ ^ 2 = I.wV (s1, 0, 0, s4)
  sq2 : w₂ ^ 2 = I.wV (lin dCols (s1, 0, 0, s4))
  comm : w₁ * w₂ * w₁⁻¹ * w₂⁻¹ = I.wV γ
  γ_E0 : γ.2.2.1 = 0

variable {I}

namespace QRel

variable {ε : Fin 2} {w₁ w₂ : X} {s1 s4 : Fin 2} {γ : V4} (R : I.QRel ε w₁ w₂ s1 s4 γ)
include R

theorem w₁_normalizer : w₁ ∈ normalizer (S.E0 I.yi I.ki : Set X) :=
  I.mem_normalizer_E0 R.m1 (M1C_E0 ε)

theorem w₂_normalizer : w₂ ∈ normalizer (S.E0 I.yi I.ki : Set X) :=
  I.mem_normalizer_E0 R.m2 (M2C_E0 ε)

theorem w₁_sq_mem : w₁ ^ 2 ∈ S.E0 I.yi I.ki := by rw [R.sq1]; exact I.wV_mem_E0 _ _ _

theorem w₂_sq_mem : w₂ ^ 2 ∈ S.E0 I.yi I.ki := by rw [R.sq2]; exact I.wV_mem_E0' (dCols_E0 _ _)

theorem mem_M₁_iff {x : X} :
    x ∈ S.E0 I.yi I.ki ⊔ zpowers w₁ ↔ x ∈ S.E0 I.yi I.ki ∨ w₁⁻¹ * x ∈ S.E0 I.yi I.ki :=
  mem_sup_zpowers_iff R.w₁_normalizer R.w₁_sq_mem

theorem w₂_normalizer_M₁ :
    w₂ ∈ normalizer ((S.E0 I.yi I.ki ⊔ zpowers w₁ : Subgroup X) : Set X) := by
  refine mem_normalizer_of_conj_mem fun m hm => ?_
  rcases R.mem_M₁_iff.mp hm with h | h
  · exact mem_sup_left ((mem_normalizer_iff.mp R.w₂_normalizer m).mp h)
  · rw [R.mem_M₁_iff]
    right
    have hγ : w₂ * w₁ * w₂⁻¹ = I.wV γ * w₁ := by
      have e := R.comm
      calc w₂ * w₁ * w₂⁻¹ = (w₁ * w₂ * w₁⁻¹ * w₂⁻¹)⁻¹ * w₁ := by group
        _ = I.wV γ * w₁ := by rw [e, I.wV_inv]
    have e : w₁⁻¹ * (w₂ * m * w₂⁻¹) = w₁⁻¹ * (w₂ * w₁ * w₂⁻¹) * (w₂ * (w₁⁻¹ * m) * w₂⁻¹) := by
      group
    rw [e, hγ]
    have h1 : w₁⁻¹ * (I.wV γ * w₁) ∈ S.E0 I.yi I.ki := by
      have := (mem_normalizer_iff.mp (inv_mem R.w₁_normalizer) _).mp (I.wV_mem_E0' R.γ_E0)
      simpa [mul_assoc] using this
    exact mul_mem h1 ((mem_normalizer_iff.mp R.w₂_normalizer _).mp h)

theorem mem_Q0_iff {x : X} : x ∈ S.Q0 I.yi I.ki w₁ w₂ ↔
    ∃ a b : Fin 2, ∃ e ∈ S.E0 I.yi I.ki, x = w₂ ^ (b : ℕ) * w₁ ^ (a : ℕ) * e := by
  have hQ : S.Q0 I.yi I.ki w₁ w₂ = (S.E0 I.yi I.ki ⊔ zpowers w₁) ⊔ zpowers w₂ := rfl
  rw [hQ, mem_sup_zpowers_iff R.w₂_normalizer_M₁ (mem_sup_left R.w₂_sq_mem)]
  constructor
  · rintro (h | h) <;> rcases R.mem_M₁_iff.mp h with h' | h'
    · exact ⟨0, 0, x, h', by simp⟩
    · exact ⟨1, 0, w₁⁻¹ * x, h', by simp⟩
    · exact ⟨0, 1, w₂⁻¹ * x, h', by simp⟩
    · exact ⟨1, 1, w₁⁻¹ * (w₂⁻¹ * x), h', by simp⟩
  · rintro ⟨a, b, e, he, rfl⟩
    fin_cases a <;> fin_cases b
    · left; exact mem_sup_left (by simpa using he)
    · right; exact mem_sup_left (by simpa using he)
    · left; exact R.mem_M₁_iff.mpr (Or.inr (by simpa using he))
    · right; exact R.mem_M₁_iff.mpr (Or.inr (by simpa [mul_assoc] using he))

theorem w₁_not_mem : w₁ ∉ S.E0 I.yi I.ki := fun h =>
  M1C_ne_bas ε (R.m1.unique (Mat.of_mem_centralizer (I.E0_le_centralizer h)))

theorem w₂_not_mem : w₂ ∉ S.E0 I.yi I.ki ⊔ zpowers w₁ := by
  intro h
  rcases R.mem_M₁_iff.mp h with h' | h'
  · exact M2C_ne_bas ε (R.m2.unique (Mat.of_mem_centralizer (I.E0_le_centralizer h')))
  · have := R.m1.mul_central (I.E0_le_centralizer h')
    rw [mul_inv_cancel_left] at this
    exact M2C_ne_M1C ε (R.m2.unique this)

theorem card_Q0 : Nat.card (S.Q0 I.yi I.ki w₁ w₂) = 32 := by
  have hQ : S.Q0 I.yi I.ki w₁ w₂ = (S.E0 I.yi I.ki ⊔ zpowers w₁) ⊔ zpowers w₂ := rfl
  rw [hQ, card_sup_zpowers R.w₂_normalizer_M₁ (mem_sup_left R.w₂_sq_mem) R.w₂_not_mem,
    card_sup_zpowers R.w₁_normalizer R.w₁_sq_mem R.w₁_not_mem, I.card_E0]

end QRel

end Inst

end CFSG.ComponentClassification.HSFLit.KD46
