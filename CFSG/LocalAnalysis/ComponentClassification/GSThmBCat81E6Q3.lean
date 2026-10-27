module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Conf
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Conf

public section

namespace CFSG.ComponentClassification.GSThmB.Cat81Q3

open CFSG Subgroup CFSG.ComponentClassification.CatFactsSmall

variable {K₀ : Type} [Group K₀]

theorem isAdm_of_isAdmQ {q : ℕ} (hq : q = 3) {α : MulAut K₀} (h : Cat8.IsAdmQ K₀ q α) :
    Cat8.IsAdm K₀ α := by
  subst hq
  have h360 : Cat8.ordL2 (3 ^ 2) = 360 := by decide
  exact ⟨h.sq, h.out, h360 ▸ h.dvd⟩

variable [Finite K₀]

theorem innA_eq_top
    (hS : IsSec8Socle K₀ 3 1) {q : ℕ} (hq : q = 3) {α : MulAut K₀} (h : Cat8.IsAdmQ K₀ q α) :
    Cat8.innA K₀ α = ⊤ :=
  cfQ3Out K₀ hS α (isAdm_of_isAdmQ hq h)

theorem exists_q3Conf
    (hS : IsSec8Socle K₀ 3 1) {q : ℕ} (hq : q = 3) (c : Cat8.QConf K₀ q) :
    ∃ c' : Cat8.Q3Conf K₀, c'.a = c.a ∧ c'.Q = c.Q ∧ c'.g = c.g ∧ c'.z = c.z := by
  have hQs := c.Q_sylow
  rw [innA_eq_top hS hq c.adm, top_inf_eq] at hQs
  have hQle : c.Q ≤ centralizer ({c.a} : Set (MulAut K₀)) := c.Q_le.trans inf_le_right
  have hQ2 : IsPGroup 2 c.Q := by
    obtain ⟨T, hT⟩ := hQs
    have h := T.isPGroup'
    rw [hT] at h
    exact h.of_equiv (subgroupOfEquivOfLe hQle)
  have hg2 : IsPGroup 2 (zpowers c.g) := by
    obtain ⟨k, hk⟩ := hQ2 ⟨c.g * c.g, c.g_sq⟩
    have hk' : c.g ^ 2 ^ (k + 1) = 1 := by
      have h := congrArg Subtype.val hk
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
      rw [pow_succ', pow_mul, sq]
      exact h
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨R, hR⟩ := (hQ2.to_sup_of_normal_left' hg2 (zpowers_le.2 c.g_norm)).exists_le_sylow
  exact ⟨⟨c.a, c.Q, c.g, R, c.z, isAdm_of_isAdmQ hq c.adm, hQle, hQs, c.g_inn, c.g_norm,
    c.g_not_mem, c.g_sq, c.tau_inn, le_sup_left.trans hR, hR (mem_sup_right (mem_zpowers c.g)),
    ⟨R, rfl⟩, c.z_mem, c.z_comm, c.z_sq, c.z_ne⟩, rfl, rfl, rfl, rfl⟩

theorem cls_three
    (hS : IsSec8Socle K₀ 3 1) {q : ℕ} (hq : q = 3) (c : Cat8.QConf K₀ q) :
    ∀ w ∈ Cat8.innA K₀ c.a, w * w = 1 → w ≠ 1 → ∃ n ∈ Cat8.innA K₀ c.a,
      n⁻¹ * w * n = c.a ∨ n⁻¹ * w * n = c.z ∨ n⁻¹ * w * n = c.a * c.z * c.tau ∨
        n⁻¹ * w * n = c.z * c.tau := by
  intro w _ hw hw1
  have hN : ∀ n : MulAut K₀, n ∈ Cat8.innA K₀ c.a := fun n =>
    (innA_eq_top hS hq c.adm).symm ▸ mem_top n
  obtain ⟨c', ha, -, hg, hz⟩ := exists_q3Conf hS hq c
  have hP := cfQ3Conf K₀ hS c'
  have hτ : c'.tau = c.tau := by
    show c'.a * (c'.g⁻¹ * c'.a * c'.g) = c.a * (c.g⁻¹ * c.a * c.g)
    rw [ha, hg]
  by_cases hin : w ∈ Cat8.Inn K₀
  · rcases hP.inner_classes w hin hw hw1 with ⟨k, -, hk⟩ | ⟨k, -, hk⟩
    · refine ⟨k⁻¹, hN _, Or.inr (Or.inl ?_)⟩
      rw [← hk, ← hz]
      group
    · refine ⟨k⁻¹, hN _, Or.inr (Or.inr (Or.inr ?_))⟩
      rw [← hk, ← hz, ← hτ]
      group
  · rcases hP.outer_classes w hw hin with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨k⁻¹, hN _, Or.inl ?_⟩
      rw [← hk, ← ha]
      group
    · refine ⟨k⁻¹, hN _, Or.inr (Or.inr (Or.inl ?_))⟩
      rw [← hk, ← ha, ← hz, ← hτ]
      group

theorem out_three
    (hS : IsSec8Socle K₀ 3 1) {q : ℕ} (hq : q = 3) {α : MulAut K₀} (h : Cat8.IsAdmQ K₀ q α) :
    (Cat8.innA K₀ α).Normal ∧
      ∃ φ : MulAut K₀, ∀ ψ : MulAut K₀, ∃ k : ℤ, (φ ^ k)⁻¹ * ψ ∈ Cat8.innA K₀ α := by
  rw [innA_eq_top hS hq h]
  exact ⟨⟨fun _ _ _ => mem_top _⟩, 1, fun _ => ⟨0, mem_top _⟩⟩

theorem card_D_three
    (hS : IsSec8Socle K₀ 3 1) {q : ℕ} (hq : q = 3) (c : Cat8.QConf K₀ q) : Nat.card c.D = 8 := by
  obtain ⟨c', ha, hQ, -, -⟩ := exists_q3Conf hS hq c
  have hD : c'.D = c.D := by
    show c'.Q ⊓ Cat8.L0 K₀ c'.a = c.Q ⊓ Cat8.L0 K₀ c.a
    rw [ha, hQ]
  exact hD ▸ (cfQ3Conf K₀ hS c').card_D.1

end CFSG.ComponentClassification.GSThmB.Cat81Q3
