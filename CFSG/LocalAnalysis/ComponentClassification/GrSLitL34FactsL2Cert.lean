module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL2Balance
public import Certificates.Certificate22208

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.GH74.KGroups Equiv

structure L2ModelFacts {n : ℕ} (P A : Subgroup (Perm (Fin n))) : Prop where
  le : P ≤ A
  inner : ∀ x ∈ P, x * x = 1 → x ≠ 1 → ∀ y ∈ A, y * x = x * y → y ^ 16 = 1
  outer3 : ∀ r ∈ A, r * r = 1 → r ≠ 1 → r ∉ P → ∃ y ∈ P, y ^ 3 = 1 ∧ y ≠ 1 ∧
    y * r = r * y ∧ ∀ g ∈ P, g * r = r * g → g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y * y
  outer2 : ∀ r ∈ A, r * r = 1 → r ≠ 1 → r ∉ P → ∀ y ∈ A, y * r = r * y → y ^ 16 = 1 →
    y * y = 1
  two : ∀ y ∈ A, ∀ k : ℕ, y ^ 2 ^ k = 1 → y ^ 16 = 1
  ntriv : ∃ y ∈ P, y ≠ 1

theorem two_of_card {n : ℕ} {A : Subgroup (Perm (Fin n))} {m : ℕ} (hA : Nat.card A ∣ 16 * m)
    (hm : Odd m) {y : Perm (Fin n)} (hy : y ∈ A) {k : ℕ} (hk : y ^ 2 ^ k = 1) : y ^ 16 = 1 := by
  have h1 : orderOf (⟨y, hy⟩ : A) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hk))
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : orderOf (⟨y, hy⟩ : A) ∣ 16 * m := (_root_.orderOf_dvd_natCard _).trans hA
  rw [hj] at h2
  have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hm)
  have h3 : 2 ^ j ∣ 16 := hcop.dvd_of_dvd_mul_right h2
  rw [Subgroup.orderOf_mk] at hj
  exact orderOf_dvd_iff_pow_eq_one.1 (hj ▸ h3)

theorem l27Outer_eq :
    (elemsT L27.QA).all (fun r => !(decide (r * r = 1)) || decide (r = 1) || L27.QP.sift r 0 ||
      (((elemsT L27.QP).any fun y => decide (y ^ 3 = 1) && !(decide (y = 1)) &&
          decide (y * r = r * y) && (elemsT L27.QP).all fun g => !(decide (g * r = r * g)) ||
            decide (g * y * g⁻¹ = y) || decide (g * y * g⁻¹ = y * y)) &&
        (elemsT L27.QA).all fun y => !(decide (y * r = r * y)) || !(decide (y ^ 16 = 1)) ||
          decide (y * y = 1))) = true := by
  have h := Certificates.certificate22208
  rw [l2OuterOK, Bool.and_eq_true, l27OuterOK] at h
  exact h.1

theorem a5Outer_prop :
    ∀ r : Perm (Fin 5), Perm.sign r = -1 → r * r = 1 →
      (∃ y : Perm (Fin 5), Perm.sign y = 1 ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ y * r = r * y ∧
        ∀ g : Perm (Fin 5), Perm.sign g = 1 → g * r = r * g →
          g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y * y) ∧
      ∀ y : Perm (Fin 5), y * r = r * y → y ^ 16 = 1 → y * y = 1 := by
  have h := Certificates.certificate22208
  have h2 : a5OuterOK = true := by
    rw [l2OuterOK, Bool.and_eq_true] at h
    exact h.2
  unfold a5OuterOK at h2
  exact of_decide_eq_true h2

theorem l27Facts :
    L2ModelFacts L27.QP.originalSubgroup L27.QA.originalSubgroup := by
  have hout := l27Outer_eq
  refine ⟨fun x hx => (mem_iff_sift _ L27.QA_ok x).2 (forall_of_all _ L27.QP_ok l27_sub_check x hx),
    ?_, ?_, ?_, ?_, ⟨L27.pa, by rw [L27.QP_closure]; exact subset_closure (by simp), by decide⟩⟩
  · intro x hx hx2 hx1 y hy hyx
    have h1 := forall_of_all _ L27.QP_ok l27_inv_check x hx
    simp only [hx2, hx1, decide_true, decide_false, Bool.not_true, Bool.false_or] at h1
    have h2 := List.all_eq_true.1 h1 y ((mem_elemsT _ L27.QA_ok y).2 hy)
    simpa [hyx] using h2
  · intro r hr hr2 hr1 hrP
    have h1 := forall_of_all _ L27.QA_ok hout r hr
    have hs : L27.QP.sift r 0 = false := by
      cases h : L27.QP.sift r 0
      · rfl
      · exact absurd ((mem_iff_sift _ L27.QP_ok r).2 h) hrP
    simp only [hr2, hr1, hs, decide_true, decide_false, Bool.not_true, Bool.false_or,
      Bool.and_eq_true] at h1
    obtain ⟨y, hy, hy'⟩ := List.any_eq_true.1 h1.1
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at hy'
    obtain ⟨⟨⟨hy3, hy1⟩, hyr⟩, hyn⟩ := hy'
    refine ⟨y, (mem_elemsT _ L27.QP_ok y).1 hy, hy3, hy1, hyr, fun g hg hgr => ?_⟩
    have := List.all_eq_true.1 hyn g ((mem_elemsT _ L27.QP_ok g).2 hg)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not] at this
    rcases this with (h | h) | h
    · exact absurd hgr h
    · exact Or.inl h
    · exact Or.inr h
  · intro r hr hr2 hr1 hrP y hy hyr hy16
    have h1 := forall_of_all _ L27.QA_ok hout r hr
    have hs : L27.QP.sift r 0 = false := by
      cases h : L27.QP.sift r 0
      · rfl
      · exact absurd ((mem_iff_sift _ L27.QP_ok r).2 h) hrP
    simp only [hr2, hr1, hs, decide_true, decide_false, Bool.not_true, Bool.false_or,
      Bool.and_eq_true] at h1
    have := List.all_eq_true.1 h1.2 y ((mem_elemsT _ L27.QA_ok y).2 hy)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not] at this
    rcases this with (h | h) | h
    · exact absurd hyr h
    · exact absurd hy16 h
    · exact h
  · intro y hy k hk
    refine two_of_card (m := 21) ?_ (by decide) hy hk
    rw [card_group _ L27.QA_ok, L27.QA_valid.2]

theorem a5Facts :
    L2ModelFacts (alternatingGroup (Fin 5)) ⊤ := by
  have hout := a5Outer_prop
  have hsign : ∀ r : Perm (Fin 5), r ∉ alternatingGroup (Fin 5) → Perm.sign r = -1 := by
    intro r hr
    rcases Int.units_eq_one_or (Perm.sign r) with h | h
    · exact absurd (Perm.mem_alternatingGroup.mpr h) hr
    · exact h
  refine ⟨le_top, fun x hx hx2 hx1 y _ hyx =>
    a5_inv_check x y (Perm.mem_alternatingGroup.mp hx) hx2 hx1 hyx, ?_, ?_, ?_, ?_⟩
  · intro r _ hr2 _ hrP
    obtain ⟨y, hy1, hy3, hyne, hyr, hyn⟩ := (hout r (hsign r hrP) hr2).1
    exact ⟨y, Perm.mem_alternatingGroup.mpr hy1, hy3, hyne, hyr, fun g hg hgr =>
      hyn g (Perm.mem_alternatingGroup.mp hg) hgr⟩
  · intro r _ hr2 _ hrP y _ hyr hy16
    exact (hout r (hsign r hrP) hr2).2 y hyr hy16
  · intro y hy k hk
    refine two_of_card (m := 15) ?_ (by decide) hy hk
    rw [card_top, Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  · obtain ⟨y, hy1, -, hyne, -, -⟩ := (hout (swap 0 1) (Perm.sign_swap (by decide))
      (swap_mul_self 0 1)).1
    exact ⟨y, Perm.mem_alternatingGroup.mpr hy1, hyne⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
