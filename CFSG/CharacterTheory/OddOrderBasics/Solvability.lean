module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.OddOrderBasics

theorem derived_series_transport {G K : Type*} [Group G] [Group K] (f : G →* K)
    (H : Subgroup G) (r : ℕ) :
    (derivedSeries G r).map f = (derivedSeries f.range r).map f.range.subtype ∧
    (derivedSeries H r).map H.subtype ≤ derivedSeries G r ∧
    (Group.IsSolvable G → Group.IsSolvable H ∧ Group.IsSolvable f.range) := by
  refine ⟨?_, map_derivedSeries_le_derivedSeries H.subtype r, fun _ =>
    ⟨inferInstance, Group.isSolvable_of_surjective f.rangeRestrict_surjective⟩⟩
  rw [← map_derivedSeries_eq f.rangeRestrict_surjective r, Subgroup.map_map,
    MonoidHom.subtype_comp_rangeRestrict]

theorem derivedSeries_add_le_map {G : Type*} [Group G] (N : Subgroup G) {b : ℕ}
    (hb : derivedSeries G b ≤ N) (a : ℕ) :
    derivedSeries G (b + a) ≤ (derivedSeries N a).map N.subtype := by
  induction a with
  | zero =>
    rw [add_zero, derivedSeries_zero, Subgroup.map_top, Subgroup.range_subtype]
    exact hb
  | succ a ih =>
    rw [← add_assoc, derivedSeries_succ, derivedSeries_succ, Subgroup.map_commutator]
    exact Subgroup.commutator_mono ih ih

theorem solvability_extensions {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    (Group.IsSolvable G ↔ Group.IsSolvable N ∧ Group.IsSolvable (G ⧸ N)) ∧
    ∀ a b : ℕ, derivedSeries N a = ⊥ → derivedSeries (G ⧸ N) b = ⊥ →
      derivedSeries G (a + b) = ⊥ := by
  refine ⟨Group.isSolvable_iff_subgroup_quotient N, fun a b ha hb => ?_⟩
  have hGb : derivedSeries G b ≤ N := by
    have h := map_derivedSeries_eq (QuotientGroup.mk'_surjective N) b
    rw [hb, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  have hle := derivedSeries_add_le_map N hGb a
  rw [ha, Subgroup.map_bot] at hle
  rw [add_comm]
  exact le_bot_iff.mp hle

theorem p_group_maximal_index {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (M : Subgroup P) (hM : IsCoatom M) : M.Normal ∧ M.index = p := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnorm : M.Normal := by
    have hlt := Group.normalizerCondition_of_isNilpotent (G := P) M hM.lt_top
    have htop : Subgroup.normalizer (M : Set P) = ⊤ := hM.2 _ hlt
    exact Subgroup.normalizer_eq_top_iff.mp htop
  refine ⟨hnorm, ?_⟩
  have hQ : IsPGroup p (P ⧸ M) := hP.to_quotient M
  have hnt : Nontrivial (P ⧸ M) := QuotientGroup.nontrivial_iff.mpr hM.1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P ⧸ M) p (by
    obtain ⟨n, hn⟩ := hQ.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hn
    rw [hn]
    exact dvd_pow_self p hn0)
  set X := (Subgroup.zpowers x).comap (QuotientGroup.mk' M) with hXdef
  have hMX : M ≤ X := by
    intro m hm
    change ((m : P ⧸ M)) ∈ Subgroup.zpowers x
    rw [(QuotientGroup.eq_one_iff m).mpr hm]
    exact Subgroup.one_mem _
  have hXM : X ≠ M := by
    intro h
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective M x
    have hy : y ∈ X := Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)
    rw [h] at hy
    have : (QuotientGroup.mk' M y : P ⧸ M) = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    rw [this, orderOf_one] at hx
    exact hp.out.one_lt.ne hx
  have hXtop : X = ⊤ := hM.2 X (lt_of_le_of_ne hMX hXM.symm)
  have hzp : Subgroup.zpowers x = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective M y
    have hz : z ∈ X := by rw [hXtop]; exact Subgroup.mem_top z
    exact hz
  change Nat.card (P ⧸ M) = p
  rw [← hx, ← Nat.card_zpowers, hzp, Subgroup.card_top]

theorem p_group_cyclic_abelianization {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (hcyc : IsCyclic (P ⧸ commutator P)) : IsCyclic P := by
  obtain ⟨c, hc⟩ := hcyc.exists_generator
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator P) c
  have hdecomp : ∀ y : P, ∃ k : ℤ, g ^ (-k) * y ∈ commutator P := by
    intro y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hc (QuotientGroup.mk' (commutator P) y))
    simp only [QuotientGroup.mk'_apply] at hk
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, ← hk, zpow_neg,
      inv_mul_cancel]
  refine ⟨⟨g, fun y => ?_⟩⟩
  by_contra hy
  have hy' : y ∉ Subgroup.zpowers g := hy
  have hlt : Subgroup.zpowers g ≠ ⊤ := fun htop => hy' (by rw [htop]; exact Subgroup.mem_top y)
  obtain ⟨M, hM, hgM⟩ := (eq_top_or_exists_le_coatom (Subgroup.zpowers g)).resolve_left hlt
  obtain ⟨hMn, hMi⟩ := p_group_maximal_index hP M hM
  have hcomm : commutator P ≤ M := by
    have hcard : Nat.card (P ⧸ M) = p := hMi
    have : IsCyclic (P ⧸ M) := isCyclic_of_prime_card hcard
    have : IsMulCommutative (P ⧸ M) := IsCyclic.isMulCommutative
    rw [← QuotientGroup.ker_mk' M]
    exact Abelianization.commutator_subset_ker (QuotientGroup.mk' M)
  have hall : ∀ z : P, z ∈ M := by
    intro z
    obtain ⟨k, hk⟩ := hdecomp z
    have h1 : g ^ (-k) * z ∈ M := hcomm hk
    have h2 : g ^ k ∈ M := hgM (Subgroup.zpow_mem_zpowers g k)
    have := M.mul_mem h2 h1
    rwa [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul] at this
  exact hM.1 (eq_top_iff.mpr fun z _ => hall z)

end CFSG.OddOrderBasics
