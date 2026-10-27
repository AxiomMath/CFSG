module

public import CFSG.LieType.SeitzGeneration.HyperEx
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ}

theorem card_closure_pair_of_not_mem (hp : p.Prime) {E : Subgroup Y} (hE : IsElemAbelian p E)
    {f x : Y} (hfE : f ∈ E) (hxE : x ∈ E) (hf1 : f ≠ 1) (hx : x ∉ Subgroup.zpowers f) :
    Nat.card (Subgroup.closure ({f, x} : Set Y)) = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := fun h => hx (h ▸ Subgroup.one_mem _)
  have hof : orderOf f = p := orderOf_eq_prime (hE.2 f hfE) hf1
  have hox : orderOf x = p := orderOf_eq_prime (hE.2 x hxE) hx1
  have hxf : Commute x f := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hxE⟩ ⟨f, hfE⟩)
  have hcl : Subgroup.closure ({f, x} : Set Y) = Subgroup.zpowers f ⊔ Subgroup.zpowers x := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers f : Set Y) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact (hxf.zpow_right n).eq.symm
  have hdisj : Disjoint (Subgroup.zpowers f) (Subgroup.zpowers x) := by
    rw [disjoint_iff]
    have hdvd : Nat.card (Subgroup.zpowers f ⊓ Subgroup.zpowers x : Subgroup Y) ∣ p := by
      rw [← hox, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | hpc
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have heq : (Subgroup.zpowers f ⊓ Subgroup.zpowers x : Subgroup Y) = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hpc, Nat.card_zpowers, hox])
      exact hx ((heq ▸ inf_le_left : Subgroup.zpowers x ≤ _) (Subgroup.mem_zpowers x))
  rw [hcl, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    Nat.card_zpowers, Nat.card_zpowers, hof, hox, sq]

theorem relIndex_closure_pair_of_not_mem (hp : p.Prime) {E : Subgroup Y} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) {f x : Y} (hfE : f ∈ E) (hxE : x ∈ E) (hf1 : f ≠ 1)
    (hx : x ∉ Subgroup.zpowers f) :
    (Subgroup.closure ({f, x} : Set Y)).relIndex E = p := by
  have hFE : Subgroup.closure ({f, x} : Set Y) ≤ E :=
    (Subgroup.closure_le E).2 (Set.insert_subset_iff.2 ⟨hfE, Set.singleton_subset_iff.2 hxE⟩)
  have h1 : Nat.card ((Subgroup.closure ({f, x} : Set Y)).subgroupOf E) *
      (Subgroup.closure ({f, x} : Set Y)).relIndex E = Nat.card E :=
    Subgroup.card_mul_index _
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv,
    card_closure_pair_of_not_mem hp hE hfE hxE hf1 hx, hcard] at h1
  refine Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) ?_
  rw [h1]
  ring

theorem le_hyperClosure_of_plane (hp : p.Prime) {K E L : Subgroup Y} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) {f : Y} (hfE : f ∈ E) (hf1 : f ≠ 1) (hLK : L ≤ K)
    (hLf : ∀ l ∈ L, f * l = l * f)
    (hL : L ≤ Subgroup.closure
      {l | l ∈ L ∧ ∃ x ∈ E, x ∉ Subgroup.zpowers f ∧ x * l = l * x}) :
    L ≤ hyperClosure p K E := by
  refine hL.trans ((Subgroup.closure_le _).2 ?_)
  rintro l ⟨hl, x, hxE, hx, hxl⟩
  have hcent : Subgroup.closure ({f, x} : Set Y) ≤ Subgroup.centralizer {l} := by
    rw [Subgroup.closure_le]
    refine Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hLf l hl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hxl
  refine Subgroup.subset_closure ⟨hLK hl, Subgroup.closure ({f, x} : Set Y),
    (Subgroup.closure_le E).2 (Set.insert_subset_iff.2 ⟨hfE, Set.singleton_subset_iff.2 hxE⟩),
    relIndex_closure_pair_of_not_mem hp hE hcard hfE hxE hf1 hx, fun z hz => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hz)

end CFSG.LieType.SeitzGeneration
