module

public import CFSG.CGT.PushingUpLit.A78.Sp4Transport
public import CFSG.CGT.PushingUpLit.A78.Sp4SL2

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.Timmesfeld.ARS

variable {G : Type} [Group G] {Z : Subgroup G} {e : ℕ}

section Members

theorem Sp4Local.card_member (h : Sp4Local G Z e) {A : Subgroup G} (hA : A ∈ zClass Z) :
    Nat.card A = 2 ^ e :=
  (h.at_member hA).card

theorem Sp4Local.sq_member (h : Sp4Local G Z e) {A : Subgroup G} (hA : A ∈ zClass Z) :
    ∀ x ∈ A, x * x = 1 :=
  (h.at_member hA).sq

theorem Sp4Local.ne_bot_member (h : Sp4Local G Z e) {A : Subgroup G} (hA : A ∈ zClass Z) :
    A ≠ ⊥ := by
  intro hbot
  have h1 := h.card_member hA
  rw [hbot, Subgroup.card_bot] at h1
  have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h.two_le
  omega

theorem Sp4Local.commuting_self_member (h : Sp4Local G Z e) {A : Subgroup G}
    (hA : A ∈ zClass Z) : Commuting A A :=
  fun _ ha _ hb => commute_of_mul_self (h.sq_member hA) ha hb

theorem Sp4Local.four_le_card_member (h : Sp4Local G Z e) {A : Subgroup G}
    (hA : A ∈ zClass Z) : 4 ≤ Nat.card A := by
  rw [h.card_member hA]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h.two_le

theorem Sp4Local.ne_of_not_commuting (h : Sp4Local G Z e) {A B : Subgroup G}
    (hA : A ∈ zClass Z) (hnc : ¬ Commuting A B) : A ≠ B := by
  rintro rfl
  exact hnc (h.commuting_self_member hA)

end Members

section Opposite

theorem Sp4Local.opposite_of_not_commuting (h : Sp4Local G Z e) (hL1 : SylowOppositeSL2)
    {A B : Subgroup G} (hA : A ∈ zClass Z) (hB : B ∈ zClass Z) (hnc : ¬ Commuting A B) :
    Opposite A B := by
  obtain ⟨I, ⟨φ⟩, -⟩ := h.dual_at hA B hB hnc
  exact hL1 h.two_le φ le_sup_left le_sup_right (h.card_member hA) (h.card_member hB)
    (h.ne_of_not_commuting hA hnc)

end Opposite

section Common

variable [Finite G]

omit [Finite G] in
theorem Sp4Local.commonNbrs_ncard (h : Sp4Local G Z e) (hS1 : SylowCountSL2) {B C : Subgroup G}
    (hB : B ∈ zClass Z) (hC : C ∈ zClass Z) (hnc : ¬ Commuting B C) :
    {X : Subgroup G | X ∈ zClass Z ∧ Commuting X B ∧ Commuting X C}.ncard = 2 ^ e + 1 := by
  obtain ⟨I, -, ⟨φ⟩, h3, h4, h5, -⟩ := h.dual_at hB C hC hnc
  have hset : {X : Subgroup G | X ∈ zClass Z ∧ Commuting X B ∧ Commuting X C} =
      {P : Subgroup G | P ≤ I ∧ Nat.card P = 2 ^ e} := by
    ext X
    constructor
    · rintro ⟨hX, hXB, hXC⟩
      exact ⟨h5 X hX hXB hXC, h.card_member hX⟩
    · rintro ⟨hXI, hXc⟩
      have hX : X ∈ zClass Z := h4 X hXI hXc
      exact ⟨hX, (h3.mono le_sup_left hXI).symm, (h3.mono le_sup_right hXI).symm⟩
  rw [hset]
  exact hS1 h.two_le φ

theorem Sp4Local.exists_common (h : Sp4Local G Z e) (hS1 : SylowCountSL2) {B C : Subgroup G}
    (hB : B ∈ zClass Z) (hC : C ∈ zClass Z) (hnc : ¬ Commuting B C) :
    ∀ D ∈ sigmaSet (zClass Z) B,
      ∃ X ∈ zClass Z, Commuting X B ∧ Commuting X C ∧ Commuting X D := by
  classical
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  set q := 2 ^ e with hq
  set S : Finset (Subgroup G) := Finset.univ.filter (· ∈ sigmaSet (zClass Z) B) with hS
  set N : Finset (Subgroup G) :=
    Finset.univ.filter (fun X => X ∈ zClass Z ∧ Commuting X B ∧ Commuting X C) with hN
  set T : Subgroup G → Finset (Subgroup G) := fun X =>
    Finset.univ.filter (fun D => D ∈ sigmaSet (zClass Z) B ∧ Commuting X D) with hT
  have hScoe : (S : Set (Subgroup G)) = sigmaSet (zClass Z) B := by
    ext D
    simp [hS]
  have hNcoe : (N : Set (Subgroup G)) =
      {X | X ∈ zClass Z ∧ Commuting X B ∧ Commuting X C} := by
    ext D
    simp [hN]
  have hScard : S.card = q * (q + 1) := by
    rw [← Set.ncard_coe_finset, hScoe, ← Nat.card_coe_set_eq]
    exact h.sigma_card_at hB
  have hNcard : N.card = q + 1 := by
    rw [← Set.ncard_coe_finset, hNcoe]
    exact h.commonNbrs_ncard hS1 hB hC hnc
  have hNmem : ∀ X ∈ N, X ∈ zClass Z ∧ Commuting X B ∧ Commuting X C := by
    intro X hX
    simpa [hN] using hX
  have hNS : ∀ X ∈ N, X ∈ sigmaSet (zClass Z) B := by
    intro X hX
    obtain ⟨hXΔ, hXB, hXC⟩ := hNmem X hX
    refine ⟨hXΔ, ?_, hXB.symm⟩
    rintro rfl
    exact hnc hXC
  have hTcoe : ∀ X, (T X : Set (Subgroup G)) =
      {D | D ∈ sigmaSet (zClass Z) B ∧ Commuting X D} := by
    intro X
    ext D
    simp [hT]
  have hTcard : ∀ X ∈ N, (T X).card = q := by
    intro X hX
    have h1 : Nat.card {C : Subgroup G // C ∈ sigmaSet (zClass Z) B ∧ Commuting X C} = q :=
      h.sigma_clique_at hB X (hNS X hX)
    rw [← h1, ← Set.ncard_coe_finset, hTcoe X, ← Nat.card_coe_set_eq]
    rfl
  have hNeq : ∀ X ∈ N, ∀ Y ∈ N, Commuting X Y → X = Y := by
    intro X hX Y hY hXY
    by_contra hne
    obtain ⟨hXΔ, hXB, hXC⟩ := hNmem X hX
    obtain ⟨hYΔ, hYB, hYC⟩ := hNmem Y hY
    have hBX : B ≠ X := by
      rintro rfl
      exact hnc hXC
    have hCX : C ≠ X := by
      rintro rfl
      exact hnc hXB.symm
    have hBs : B ∈ sigmaSet (zClass Z) X := ⟨hB, hBX, hXB⟩
    have hCs : C ∈ sigmaSet (zClass Z) X := ⟨hC, hCX, hXC⟩
    have hYs : Y ∈ sigmaSet (zClass Z) X := ⟨hYΔ, fun e => hne e.symm, hXY⟩
    exact hnc (h.sigma_trans_at hXΔ B hBs Y hYs C hCs hYB.symm hYC)
  have hdisj : ∀ X ∈ N, ∀ Y ∈ N, X ≠ Y → Disjoint (T X) (T Y) := by
    intro X hX Y hY hXY
    rw [Finset.disjoint_left]
    intro D hDX hDY
    have hDX' : D ∈ sigmaSet (zClass Z) B ∧ Commuting X D := by simpa [hT] using hDX
    have hDY' : D ∈ sigmaSet (zClass Z) B ∧ Commuting Y D := by simpa [hT] using hDY
    exact hXY (hNeq X hX Y hY
      (h.sigma_trans_at hB X (hNS X hX) D hDX'.1 Y (hNS Y hY) hDX'.2 hDY'.2.symm))
  have hsub : N.biUnion T ⊆ S := by
    intro D hD
    obtain ⟨X, -, hDX⟩ := Finset.mem_biUnion.1 hD
    have : D ∈ sigmaSet (zClass Z) B ∧ Commuting X D := by simpa [hT] using hDX
    simpa [hS] using this.1
  have hcard : (N.biUnion T).card = (q + 1) * q := by
    rw [Finset.card_biUnion hdisj, Finset.sum_const_nat hTcard, hNcard]
  have heq : N.biUnion T = S :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hScard]; exact (mul_comm _ _).le)
  intro D hD
  have hDS : D ∈ S := by simpa [hS] using hD
  rw [← heq] at hDS
  obtain ⟨X, hXN, hDX⟩ := Finset.mem_biUnion.1 hDS
  obtain ⟨hXΔ, hXB, hXC⟩ := hNmem X hXN
  have : D ∈ sigmaSet (zClass Z) B ∧ Commuting X D := by simpa [hT] using hDX
  exact ⟨X, hXΔ, hXB, hXC, this.2⟩

end Common

end CFSG.CGT.PushingUpLit.A78
