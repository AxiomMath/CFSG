module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XGY
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XW

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

theorem member_rank_le_two [Finite X] (hS : PlaneSys V W) (hpar : PlaneParity V W)
    (hC : ∀ y ∈ normalizer (V : Set X), y * y = 1 → y ∈ centralizer (V : Set X) → y ∈ V)
    (h518 : ∀ (E : Subgroup X) (n : ℕ), ActsElemAb V E →
      (centralizer (V : Set X)).relIndex E = 2 ^ n → n ≤ 3)
    {T : Subgroup X} (hT : IsSylow2Of T (⊤ : Subgroup X)) (hVT : V ≤ T)
    (hTN : T ≤ normalizer (V : Set X)) {Xm : Subgroup X} (hXm : IsMember T V Xm) {k : ℕ}
    (hk : (Xm ⊓ V).relIndex Xm = 2 ^ k) : k ≤ 2 := by
  classical
  have hVC : V ≤ centralizer (V : Set X) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => hS.comm w hw v hv
  have hweak : ∀ k : X, CFSG.conjugate V k ≤ T → CFSG.conjugate V k = V := fun k hk =>
    conjugate_eq_of_le_normalizer hS hpar hC (hk.trans hTN)
  let S : Set ℕ := {k | ∃ Xm' : Subgroup X, IsMember T V Xm' ∧ (Xm' ⊓ V).relIndex Xm' = 2 ^ k}
  have hkS : k ∈ S := ⟨Xm, hXm, hk⟩
  have hbdd : BddAbove S := by
    refine ⟨Nat.card X, ?_⟩
    rintro k' ⟨Xm', -, hk'⟩
    have h1 : 2 ^ k' ∣ Nat.card X := by
      rw [← hk']
      exact dvd_trans (Subgroup.relIndex_dvd_card _ _) (Subgroup.card_subgroup_dvd_card Xm')
    exact (Nat.lt_two_pow_self (n := k')).le.trans (Nat.le_of_dvd Nat.card_pos h1)
  obtain ⟨r, ⟨Xs, hXs, hrs⟩, hle⟩ : ∃ r ∈ S, ∀ k' ∈ S, k' ≤ r :=
    ⟨sSup S, Nat.sSup_mem ⟨k, hkS⟩ hbdd, fun k' hk' => le_csSup hbdd hk'⟩
  obtain ⟨hXsT, hXsV, g, hXsg⟩ := hXs
  have hcomm : ∀ a ∈ Xs, ∀ b ∈ Xs, a * b = b * a := fun a ha b hb =>
    hS.conjugate_comm (hXsg ha) (hXsg hb)
  have hsq : ∀ a ∈ Xs, a * a = 1 := fun a ha => hS.conjugate_sq (hXsg ha)
  have hF : ActsElemAb V Xs := ActsElemAb.of_exact (hXsT.trans hTN) hcomm hsq
  have hCV : Xs ⊓ centralizer (V : Set X) = Xs ⊓ V := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx1, hC x (hTN (hXsT hx1)) (hsq x hx1) hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx1, hVC hx2⟩
  have hrk : (centralizer (V : Set X)).relIndex Xs = 2 ^ r := by
    rw [← hrs, ← Subgroup.inf_relIndex_right (centralizer (V : Set X)) Xs, inf_comm, hCV]
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      have h1 : (Xs ⊓ V).relIndex Xs = 1 := by rw [hrs, h0, pow_zero]
      exact hXsV ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right)
    · exact h0
  have hr3 : r ≤ 3 := h518 Xs r hF hrk
  have hcard : ∀ u ∈ Xs, u ∉ centralizer (V : Set X) →
      2 ^ (8 - r) ≤ Nat.card {v : V // u * (v : X) * u⁻¹ = v} := by
    intro s hs hsC
    have hsV : s ∉ V := fun h => hsC (hVC h)
    obtain ⟨Xm', k', hXm', -, hrk', hcs, -⟩ :=
      exists_member_of_conj hS hT hVT hweak (hXsT hs) hsV ⟨g, hXsg hs⟩
    have hk'r : k' ≤ r := hle k' ⟨Xm', hXm', hrk'⟩
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hcs
  have h2 : r = 2 := rank_eq_two hS hpar hF hr1 hr3 hrk hcard
  exact h2 ▸ hle k hkS

end CFSG.OddStandard.SmallF3.Omega
