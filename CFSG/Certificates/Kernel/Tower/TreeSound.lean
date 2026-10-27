module

public import Certificates.Data.Kernel.Tower.Tree
public import CFSG.Certificates.Kernel.Tower.WSound

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower

variable {X : Type*} [Group X] {n k : Nat} {mul : Nat → Nat → Nat} {dec : Nat → X}
  {GS PT IM FT : Nat}

theorem treeB_get (h : treeB n k mul GS PT = true) {c : Nat} (hc : c < n) (h0 : c ≠ 0) :
    ptGi PT c < k ∧ ptPar PT c < n ∧ ptDep PT (ptPar PT c) < ptDep PT c ∧
      mul (l16 GS (ptGi PT c)) (ptPar PT c) = c := by
  rw [treeB, Bool.and_eq_true] at h
  have h1 := allB_eq_true.1 h.2 c hc
  have hc0 : Nat.beq c 0 = false := by
    exact Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  rw [hc0, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1
  exact ⟨Nat.le_of_ble_eq_true h1.1.1.1, Nat.le_of_ble_eq_true h1.1.1.2,
    Nat.le_of_ble_eq_true h1.1.2, Nat.eq_of_beq_eq_true h1.2⟩

theorem treeB_gen (h : treeB n k mul GS PT = true) {i : Nat} (hi : i < k) : l16 GS i < n := by
  rw [treeB, Bool.and_eq_true] at h
  exact Nat.le_of_ble_eq_true (allB_eq_true.1 h.1 i hi)

theorem recB_img (h : recB n k mul PT IM FT = true) {i : Nat} (hi : i < k) : l16 IM i < n := by
  rw [recB, Bool.and_eq_true, Bool.and_eq_true] at h
  exact Nat.le_of_ble_eq_true (allB_eq_true.1 h.1.1 i hi)

theorem recB_zero (h : recB n k mul PT IM FT = true) : l16 FT 0 = 0 := by
  rw [recB, Bool.and_eq_true, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1.2

theorem recB_get (h : recB n k mul PT IM FT = true) {c : Nat} (hc : c < n) (h0 : c ≠ 0) :
    l16 FT c = mul (l16 IM (ptGi PT c)) (l16 FT (ptPar PT c)) := by
  rw [recB, Bool.and_eq_true] at h
  have h1 := allB_eq_true.1 h.2 c hc
  have hc0 : Nat.beq c 0 = false := by
    exact Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  rw [hc0, Bool.false_or] at h1
  exact Nat.eq_of_beq_eq_true h1

theorem recB_sound (M : IsModel (⊤ : Subgroup X) n mul dec) (hT : treeB n k mul GS PT = true)
    (hR : recB n k mul PT IM FT = true) (α : X →* X)
    (hα : ∀ i < k, α (dec (l16 GS i)) = dec (l16 IM i)) :
    ∀ c < n, l16 FT c < n ∧ α (dec c) = dec (l16 FT c) := by
  suffices H : ∀ d, ∀ c < n, ptDep PT c = d → l16 FT c < n ∧ α (dec c) = dec (l16 FT c) from
    fun c hc => H _ c hc rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro c hc hd
    by_cases h0 : c = 0
    · subst h0
      rw [recB_zero hR, M.dec_zero, map_one]
      exact ⟨M.zero_lt, rfl⟩
    · obtain ⟨hgi, hpar, hdep, hmul⟩ := treeB_get hT hc h0
      obtain ⟨ih1, ih2⟩ := ih _ (hd ▸ hdep) _ hpar rfl
      have hg := treeB_gen hT hgi
      have hi := recB_img hR hgi
      rw [recB_get hR hc h0]
      refine ⟨M.mul_lt _ hi _ ih1, ?_⟩
      have e1 : dec c = dec (l16 GS (ptGi PT c)) * dec (ptPar PT c) := by
        rw [← M.dec_mul _ hg _ hpar, hmul]
      rw [e1, map_mul, hα _ hgi, ih2, M.dec_mul _ hi _ ih1]

end Certificates.KernelTower
