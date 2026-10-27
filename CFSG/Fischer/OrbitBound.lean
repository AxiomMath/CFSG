module

public import CFSG.Perm.ChainSpec

public section

namespace CFSG.Fischer

variable {G α : Type*} [Group G] [MulAction G α]

@[expose] def fixFirst (pts : List α) (i : ℕ) : Subgroup G :=
  ⨅ j : Fin (min i pts.length), MulAction.stabilizer G (pts[j.val]'(by omega))

theorem mem_fixFirst {pts : List α} {i : ℕ} {g : G} :
    g ∈ fixFirst pts i ↔
      ∀ j (hj : j < min i pts.length), g • pts[j]'(by omega) = pts[j]'(by omega) := by
  unfold fixFirst
  rw [Subgroup.mem_iInf]
  constructor
  · intro h j hj
    exact MulAction.mem_stabilizer_iff.1 (h ⟨j, hj⟩)
  · intro h j
    exact MulAction.mem_stabilizer_iff.2 (h j.val j.isLt)

theorem fixFirst_succ_le (pts : List α) (i : ℕ) :
    fixFirst (G := G) pts (i + 1) ≤ fixFirst pts i := by
  intro g hg
  rw [mem_fixFirst] at hg ⊢
  intro j hj
  exact hg j (by omega)

theorem card_le_prod_of_candidates [Finite G] (pts : List α)
    (hfix : ∀ g : G, (∀ p ∈ pts, g • p = p) → g = 1) (C : ℕ → Finset α)
    (hC : ∀ i (hi : i < pts.length), ∀ g ∈ fixFirst (G := G) pts i, g • pts[i] ∈ C i) :
    Nat.card G ≤ ∏ i ∈ Finset.range pts.length, (C i).card := by
  classical
  have key : ∀ d i, pts.length - i = d → i ≤ pts.length →
      Nat.card (fixFirst (G := G) pts i) ≤ ∏ k ∈ Finset.Ico i pts.length, (C k).card := by
    intro d
    induction d with
    | zero =>
      intro i hd hi
      have hi' : i = pts.length := by omega
      subst hi'
      rw [Finset.Ico_self, Finset.prod_empty]
      have hbot : fixFirst (G := G) pts pts.length = ⊥ := by
        rw [eq_bot_iff]
        intro g hg
        rw [Subgroup.mem_bot]
        apply hfix
        intro p hp
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hp
        rw [mem_fixFirst] at hg
        exact hg j (by omega)
      rw [hbot, Subgroup.card_bot]
    | succ d ih =>
      intro i hd hi
      have hlt : i < pts.length := by omega
      have h1 := CFSG.Perm.card_eq_orbit_mul (fixFirst (G := G) pts i) (fixFirst pts (i + 1)) pts[i]
        (fixFirst_succ_le pts i)
        (fun g hg => by
          rw [mem_fixFirst] at hg
          exact hg i (by omega))
        (fun g hg hgi => by
          rw [mem_fixFirst] at hg ⊢
          intro j hj
          rcases Nat.lt_or_ge j i with h | h
          · exact hg j (by omega)
          · obtain rfl : j = i := by omega
            exact hgi)
      rw [h1, Finset.prod_eq_prod_Ico_succ_bot hlt]
      apply Nat.mul_le_mul
      ·
        have hsub : MulAction.orbit (fixFirst (G := G) pts i) pts[i] ⊆ ↑(C i) := by
          rintro _ ⟨⟨g, hg⟩, rfl⟩
          exact hC i hlt g hg
        rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsub (C i).finite_toSet
      · exact ih (i + 1) (by omega) (by omega)
  have h := key pts.length 0 (by omega) (Nat.zero_le _)
  have htop : fixFirst (G := G) pts 0 = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [mem_fixFirst]
    intro j hj
    omega
  rw [htop, Subgroup.card_top] at h
  rwa [Finset.range_eq_Ico]

end CFSG.Fischer
