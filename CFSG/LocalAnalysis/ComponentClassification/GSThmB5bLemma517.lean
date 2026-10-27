module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma55

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

@[expose] def Elim513 : Prop :=
  conjugate h.K h.a = h.K → ¬ (Nonempty (OddBar h.K ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (OddBar h.K ≃* alternatingGroup (Fin 9)) ∨
    Nonempty (OddBar h.K ≃* alternatingGroup (Fin 11)))

@[expose] def Elim514 : Prop := ¬ Blueprint.LieModel (ZStarBar h.K) .PSL 3 2 2

@[expose] def Elim515 : Prop := ¬ Nonempty (OddBar h.K ≃* alternatingGroup (Fin 10))

@[expose] def Elim516 : Prop :=
  ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ (Blueprint.LieModel (ZStarBar h.K) .PSL 4 p f ∨
    Blueprint.LieModel (ZStarBar h.K) .PSU 4 p f ∨
    Blueprint.LieModel (ZStarBar h.K) .POmegaMinus 4 p f)

theorem table517_of_eliminations (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (h13 : h.Elim513) (h14 : h.Elim514)
    (h15 : h.Elim515) (h16 : h.Elim516) : h.Table517 := by
  rcases h.table hB1 hCF23 with ⟨n, hn, hJ, (⟨hKa, hK | hK⟩ | ⟨hKa, hZ, hK⟩)⟩ |
      ⟨-, -, -, hK⟩ | h3 | ⟨p, f, hp, hp2, hf, -, -, hK⟩ | h5 | h6 | h7
  ·
    rcases hn with rfl | rfl | rfl
    · exact absurd (Or.inl hK) (h13 hKa)
    · exact Or.inr (Or.inr (Or.inl ⟨hJ, hKa, hK⟩))
    · exact absurd (Or.inr (Or.inl hK)) (h13 hKa)
  ·
    rcases hn with rfl | rfl | rfl
    · exact absurd (Or.inr (Or.inl hK)) (h13 hKa)
    · exact absurd hK h15
    · exact absurd (Or.inr (Or.inr hK)) (h13 hKa)
  ·
    exact Or.inl ⟨hKa, hZ, Or.inl ⟨n, hn, hJ, hK⟩⟩
  ·
    exact absurd hK h14
  ·
    exact absurd h3 (h.not_suz hB6 hCF24)
  ·
    rcases hK with hK | hK | ⟨e, rfl, hK⟩
    · exact absurd ⟨p, f, hp, hp2, hf, Or.inl hK⟩ h16
    · exact absurd ⟨p, f, hp, hp2, hf, Or.inr (Or.inl hK)⟩ h16
    · exact absurd ⟨p, e, hp, hp2, by omega, Or.inr (Or.inr hK)⟩ h16
  ·
    exact Or.inr (Or.inl h5)
  ·
    obtain ⟨p, f, hp, hp2, hf, h5f, hJ, hKa, hZ, hK⟩ := h6
    exact Or.inl ⟨hKa, hZ, Or.inr ⟨p, f, hp, hp2, hf, h5f, hJ, hK⟩⟩
  ·
    exact Or.inr (Or.inr (Or.inr h7))

theorem comm_a_B {b : H} (hb : b ∈ h.B) : b * h.a = h.a * b := h.comm_a (h.B_le_S hb)

theorem a_not_mem_B : h.a ∉ h.B := by
  intro haB
  have hax : h.a ∈ conjugate h.B h.x := by
    rw [mem_conjugate_iff, h.x_comm_a, mul_inv_cancel_right]
    exact haB
  have := h.inf_conjugate_x ▸ mem_inf.mpr ⟨haB, hax⟩
  have h1 : h.a = 1 := mem_bot.mp this
  have h2 := h.orderOf_a
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem normalizer_P_eq (hCF : CFProp23IndexReduced) (hT : h.Table517) :
    h.T = h.B ⊔ zpowers h.a ∧ h.B ⊓ zpowers h.a = ⊥ ∧ ∀ b ∈ h.B, b * h.a = h.a * b := by
  have haT : h.a ∈ h.T :=
    mem_inf.mpr ⟨mem_inf.mpr ⟨h.a_mem_S, h.a_mem_normalizer⟩, h.a_mem_P⟩
  refine ⟨le_antisymm ?_ (sup_le h.B_le_T (zpowers_le.mpr haT)), ?_, fun b hb => h.comm_a_B hb⟩
  · rw [sup_comm]
    exact hCF H h hT
  · rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyB, hya⟩ := mem_inf.mp hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hya
    have ha2 : h.a ^ (2 : ℤ) = 1 := by
      rw [zpow_two, ← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [show m + m = 2 * m by ring, zpow_mul, ha2, one_zpow]
      exact one_mem _
    · exfalso
      apply h.a_not_mem_B
      have : h.a ^ (2 * m + 1) = h.a := by
        rw [zpow_add_one, zpow_mul, ha2, one_zpow, one_mul]
      rwa [this] at hyB

end Hyp52

end CFSG.ComponentClassification.GSThmB
