module

public import CFSG.LieType.Chevalley.ConnectedSubsystemQuasisimple

public section

namespace CFSG.LieType.Chevalley.SubsysComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ConnSubsys

variable {τ : Tag} {K : Type} [Field K]

theorem card_sup_dvd_mul_of_commute {G : Type*} [Group G] {H N : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ N, Commute x y) :
    Nat.card ↥(H ⊔ N) ∣ Nat.card ↥H * Nat.card ↥N := by
  have hr := MonoidHom.noncommCoprod_range H.subtype N.subtype fun a b => hc a a.2 b b.2
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  rw [← hr, ← Nat.card_prod]
  exact Subgroup.card_range_dvd _

section Generators


theorem subsystemGroup_empty : subsystemGroup τ K (∅ : Set (Fin τ.rank)) = ⊥ := by
  rw [subsystemGroup, eq_bot_iff, Subgroup.closure_le]
  rintro g ⟨i, hi, -⟩
  exact absurd hi (Set.notMem_empty i)

theorem subsystemGroup_union (A B : Set (Fin τ.rank)) :
    subsystemGroup τ K (A ∪ B) = subsystemGroup τ K A ⊔ subsystemGroup τ K B := by
  rw [subsystemGroup, subsystemGroup, subsystemGroup, ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hi | hi, c, hg⟩
    · exact Or.inl ⟨i, hi, c, hg⟩
    · exact Or.inr ⟨i, hi, c, hg⟩
  · rintro (⟨i, hi, c, hg⟩ | ⟨i, hi, c, hg⟩)
    · exact ⟨i, Or.inl hi, c, hg⟩
    · exact ⟨i, Or.inr hi, c, hg⟩

end Generators

section Certified


theorem commute_xUnit_xUnit_of_cartan_eq_zero {i j : Fin τ.rank} (hij : i ≠ j)
    (h0 : τ.cartan i j = 0) (c d : K) : Commute (xUnit τ K i c) (xUnit τ K j d) := by
  have hne : (Pi.single i 1 : Fin τ.rank → ℤ) ≠ Pi.single j 1 := fun h => by
    have := congrFun h i
    simp [hij] at this
  have hne' : (Pi.single i 1 : Fin τ.rank → ℤ) ≠ -Pi.single j 1 := fun h => by
    have := congrFun h i
    simp [hij] at this
  have hcomm := commute_of_forall_not_isRoot (isRoot_single τ i) (isRoot_single τ j) hne hne'
    (fun a b ha hb => not_isRoot_nsmul_single_add_nsmul_single hij h0 ha hb) K
  rw [← pinnedX_single, ← pinnedX_single]
  exact hcomm _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem commute_yUnit_yUnit_of_cartan_eq_zero {i j : Fin τ.rank} (hij : i ≠ j)
    (h0 : τ.cartan i j = 0) (c d : K) : Commute (yUnit τ K i c) (yUnit τ K j d) := by
  have hne : (-Pi.single i 1 : Fin τ.rank → ℤ) ≠ -Pi.single j 1 := fun h => by
    have := congrFun h i
    simp [hij] at this
  have hne' : (-Pi.single i 1 : Fin τ.rank → ℤ) ≠ -(-Pi.single j 1) := fun h => by
    have := congrFun h i
    simp [hij] at this
  have hcomm := commute_of_forall_not_isRoot (isRoot_neg_single τ i) (isRoot_neg_single τ j) hne
    hne' (fun a b ha hb h => by
      have e : a • (-Pi.single i 1 : Fin τ.rank → ℤ) + b • (-Pi.single j 1) =
          -(a • Pi.single i 1 + b • Pi.single j 1) := by
        rw [smul_neg, smul_neg, neg_add]
      rw [e, isRoot_neg_iff] at h
      exact not_isRoot_nsmul_single_add_nsmul_single hij h0 ha hb h) K
  rw [← pinnedX_neg_single, ← pinnedX_neg_single]
  exact hcomm _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem commute_of_cartan_eq_zero {A B : Set (Fin τ.rank)} (hAB : Disjoint A B)
    (h0 : ∀ i ∈ A, ∀ j ∈ B, τ.cartan i j = 0) :
    ∀ x ∈ subsystemGroup τ K A, ∀ y ∈ subsystemGroup τ K B, Commute x y := by
  have hgen : ∀ g ∈ {g : ModGL τ K | ∃ i ∈ A, ∃ c : K, g = xUnit τ K i c ∨ g = yUnit τ K i c},
      ∀ h ∈ {g : ModGL τ K | ∃ i ∈ B, ∃ c : K, g = xUnit τ K i c ∨ g = yUnit τ K i c},
        Commute g h := by
    rintro g ⟨i, hi, c, rfl | rfl⟩ h ⟨j, hj, d, rfl | rfl⟩ <;>
      have hij : i ≠ j := fun e => Set.disjoint_left.1 hAB hi (e ▸ hj)
    · exact commute_xUnit_xUnit_of_cartan_eq_zero hij (h0 i hi j hj) c d
    · exact commute_xUnit_yUnit_of_ne' hij c d
    · exact (commute_xUnit_yUnit_of_ne' hij.symm d c).symm
    · exact commute_yUnit_yUnit_of_cartan_eq_zero hij (h0 i hi j hj) c d
  have step1 : ∀ h ∈ {g : ModGL τ K | ∃ i ∈ B, ∃ c : K, g = xUnit τ K i c ∨ g = yUnit τ K i c},
      ∀ x ∈ subsystemGroup τ K A, Commute x h := by
    intro h hh
    have hle : subsystemGroup τ K A ≤ Subgroup.centralizer {h} := by
      rw [subsystemGroup, Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hgen g hg h hh).eq
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  intro x hx
  have hle : subsystemGroup τ K B ≤ Subgroup.centralizer {x} := by
    rw [subsystemGroup, Subgroup.closure_le]
    intro h hh
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (step1 h hh x hx).eq.symm
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem exists_connected_dvd_card_subsystemGroup [Finite K] {J : Set (Fin τ.rank)} {p : ℕ}
    (hp : p.Prime) (h : p ∣ Nat.card (subsystemGroup τ K J)) :
    ∃ C ⊆ J, C.Nonempty ∧ IsDynkinConnected τ C ∧ p ∣ Nat.card (subsystemGroup τ K C) := by
  classical
  suffices key : ∀ n : ℕ, ∀ J : Set (Fin τ.rank), J.ncard = n →
      p ∣ Nat.card (subsystemGroup τ K J) →
      ∃ C ⊆ J, C.Nonempty ∧ IsDynkinConnected τ C ∧ p ∣ Nat.card (subsystemGroup τ K C) from
    key _ J rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro J hn h
    have hJne : J.Nonempty := by
      by_contra hJ
      rw [Set.not_nonempty_iff_eq_empty] at hJ
      subst hJ
      rw [subsystemGroup_empty, Subgroup.card_bot] at h
      exact hp.one_lt.ne' (Nat.dvd_one.1 h)
    by_cases hconn : IsDynkinConnected τ J
    · exact ⟨J, subset_rfl, hJne, hconn, h⟩
    obtain ⟨S, ⟨i₀, hi₀, hi₀S⟩, hcl, hJS⟩ : ∃ S : Set (Fin τ.rank), (∃ i ∈ J, i ∈ S) ∧
        (∀ i ∈ J, ∀ j ∈ J, i ∈ S → i ≠ j → τ.cartan i j ≠ 0 → j ∈ S) ∧ ¬ J ⊆ S := by
      by_contra hno
      exact hconn fun S hS hcl => by_contra fun hJS => hno ⟨S, hS, hcl, hJS⟩
    have h0 : ∀ i ∈ J ∩ S, ∀ j ∈ J \ S, τ.cartan i j = 0 := by
      intro i hi j hj
      by_contra hc
      exact hj.2 (hcl i hi.1 j hj.1 hi.2 (fun e => hj.2 (e ▸ hi.2)) hc)
    have hdisj : Disjoint (J ∩ S) (J \ S) := Set.disjoint_left.2 fun a ha hb => hb.2 ha.2
    have hcard : Nat.card (subsystemGroup τ K J) ∣
        Nat.card (subsystemGroup τ K (J ∩ S)) * Nat.card (subsystemGroup τ K (J \ S)) := by
      conv_lhs => rw [← Set.inter_union_sdiff J S, subsystemGroup_union]
      exact card_sup_dvd_mul_of_commute (commute_of_cartan_eq_zero hdisj h0)
    have hss₁ : J ∩ S ⊂ J := Set.inter_subset_left.ssubset_of_not_subset fun hsub =>
      hJS fun a ha => (hsub ha).2
    have hss₂ : J \ S ⊂ J := Set.diff_subset.ssubset_of_not_subset fun hsub =>
      (hsub hi₀).2 hi₀S
    rcases (Nat.Prime.dvd_mul hp).1 (h.trans hcard) with h₁ | h₂
    · obtain ⟨C, hCJ, hCne, hCconn, hCdvd⟩ := ih (J ∩ S).ncard
        (hn ▸ Set.ncard_lt_ncard hss₁) (J ∩ S) rfl h₁
      exact ⟨C, hCJ.trans Set.inter_subset_left, hCne, hCconn, hCdvd⟩
    · obtain ⟨C, hCJ, hCne, hCconn, hCdvd⟩ := ih (J \ S).ncard
        (hn ▸ Set.ncard_lt_ncard hss₂) (J \ S) rfl h₂
      exact ⟨C, hCJ.trans Set.diff_subset, hCne, hCconn, hCdvd⟩

end Certified

end CFSG.LieType.Chevalley.SubsysComp
