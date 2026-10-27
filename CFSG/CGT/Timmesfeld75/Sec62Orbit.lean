module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIComm
public import CFSG.CGT.Timmesfeld75.Config

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G]

@[expose] def conjSet (H Q : Subgroup G) : Set (Subgroup G) := {R | ∃ h ∈ H, R = conjSubgroup h Q}

theorem ncard_conjSet_mul_card [Finite G] (H Q : Subgroup G) :
    (conjSet H Q).ncard * Nat.card ↥(normIn H Q) = Nat.card ↥H := by
  let _ : MulAction ↥H (Subgroup G) :=
    { smul := fun h R => conjSubgroup (h : G) R
      one_smul := fun R => conjSubgroup_one R
      mul_smul := fun a b R => (conjSubgroup_conjSubgroup (a : G) (b : G) R).symm }
  have hstab : MulAction.stabilizer ↥H Q = (normIn H Q).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_normIn]
    exact ⟨fun e => ⟨h.2, mem_normalizer_iff_conjSubgroup_eq.2 e⟩,
      fun e => mem_normalizer_iff_conjSubgroup_eq.1 e.2⟩
  have horb : conjSet H Q = MulAction.orbit ↥H Q := by
    ext R
    rw [MulAction.mem_orbit_iff]
    exact ⟨fun ⟨h, hh, e⟩ => ⟨⟨h, hh⟩, e.symm⟩, fun ⟨h, e⟩ => ⟨h, h.2, e.symm⟩⟩
  have hcard : Nat.card ↥(normIn H Q) = Nat.card ↥(MulAction.stabilizer ↥H Q) := by
    rw [hstab]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (normIn_le H Q)).toEquiv).symm
  rw [← Nat.card_coe_set_eq, horb, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥H Q),
    ← Subgroup.index_eq_card, hcard]
  exact Subgroup.index_mul_card _

theorem ncard_biUnion_const {ι α : Type*} [Finite α] {t : Set ι} (ht : t.Finite)
    {s : ι → Set α} (hd : t.PairwiseDisjoint s) {m : ℕ} (hm : ∀ i ∈ t, (s i).ncard = m) :
    (⋃ i ∈ t, s i).ncard = t.ncard * m := by
  rw [ht.ncard_biUnion (fun _ _ => Set.toFinite _) hd, finsum_mem_congr rfl hm,
    finsum_mem_eq_finite_toFinset_sum _ ht, Finset.sum_const, smul_eq_mul,
    ← Set.ncard_eq_toFinset_card t ht]

theorem ncard_mul_pred_add_one_le {G : Type*} [Group G] [Finite G] (J : Subgroup G) {s : Set (Subgroup G)}
    (hs : ∀ A ∈ s, ∀ B ∈ s, A ≠ B → A ⊓ B = ⊥) {c : ℕ}
    (hc : ∀ A ∈ s, Nat.card ↥(A ⊓ J) = c) : s.ncard * (c - 1) + 1 ≤ Nat.card J := by
  have hfin : s.Finite := Set.toFinite s
  have h := card_ge_of_pairwise_inf_eq_bot J hfin.toFinset (fun A => A ⊓ J)
    (fun _ _ => inf_le_right)
    (fun A hA B hB hAB => le_bot_iff.1 ((inf_le_inf inf_le_left inf_le_left).trans
      (hs A (hfin.mem_toFinset.1 hA) B (hfin.mem_toFinset.1 hB) hAB).le))
    (fun A hA => hc A (hfin.mem_toFinset.1 hA))
  rwa [← Set.ncard_eq_toFinset_card s hfin] at h

end CFSG.CGT.Timmesfeld75
