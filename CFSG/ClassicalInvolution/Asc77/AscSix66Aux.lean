module

public import CFSG.ClassicalInvolution.Asc77.AscSixBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

theorem IsQuatSub.exists_orderOf_four {R : Subgroup G} (h : IsQuatSub R) :
    ∃ x ∈ R, orderOf x = 4 := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  refine ⟨((e.symm (QuaternionGroup.xa 0) : ↥R) : G), (e.symm (QuaternionGroup.xa 0)).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]

theorem IsQuatSub.sq_eq_one_of_central {R : Subgroup G} (h : IsQuatSub R) {x : G} (hx : x ∈ R)
    (hc : ∀ y ∈ R, x * y = y * x) : x * x = 1 := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hcq : ∀ y : QuaternionGroup (2 ^ k), e ⟨x, hx⟩ * y = y * e ⟨x, hx⟩ := by
    intro y
    have h1 := hc (e.symm y : ↥R) (e.symm y).2
    have h' : (⟨x, hx⟩ : ↥R) * e.symm y = e.symm y * ⟨x, hx⟩ := Subtype.ext h1
    have := congrArg e h'
    simpa [map_mul] using this
  have hsq : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 := by
    generalize e ⟨x, hx⟩ = q at hcq
    cases q with
    | a i =>
      have h3 := hcq (QuaternionGroup.xa 0)
      rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h3
      have h4 : (0 : ZMod (2 * 2 ^ k)) - i = 0 + i := QuaternionGroup.xa.inj h3
      have h5 : i + i = 0 := by linear_combination -h4
      rw [QuaternionGroup.a_mul_a, h5, QuaternionGroup.one_def]
    | xa j =>
      exfalso
      have h3 := hcq (QuaternionGroup.a 1)
      rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa] at h3
      have h4 : j + 1 = j - 1 := QuaternionGroup.xa.inj h3
      have h5 : ((2 : ℕ) : ZMod (2 * 2 ^ k)) = 0 := by
        push_cast
        linear_combination h4
      rw [ZMod.natCast_eq_zero_iff] at h5
      have := Nat.le_of_dvd (by norm_num) h5
      omega
  have : e (⟨x, hx⟩ * ⟨x, hx⟩) = e 1 := by rw [map_mul, hsq, map_one]
  have h6 := e.injective this
  exact congrArg Subtype.val h6

theorem exists_normal_lt_of_lt [Finite G] {S A : Subgroup G} (hS : IsPGroup 2 S) (hA : A < S) :
    ∃ M : Subgroup G, A ≤ M ∧ M < S ∧ ∀ s ∈ S, ∀ y ∈ M, s * y * s⁻¹ ∈ M := by
  have hnil : Group.IsNilpotent ↥S := hS.isNilpotent
  have hA'top : A.subgroupOf S ≠ ⊤ := by
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact hA.not_ge h
  obtain ⟨M', hM'coatom, hA'M'⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (A.subgroupOf S)).resolve_left hA'top
  have hnormal : M'.Normal := by
    have h1 := Group.normalizerCondition_of_isNilpotent (G := ↥S) M'
      (lt_top_iff_ne_top.mpr hM'coatom.1)
    have h2 : Subgroup.normalizer (M' : Set ↥S) = ⊤ := hM'coatom.2 _ h1
    exact Subgroup.normalizer_eq_top_iff.mp h2
  refine ⟨M'.map S.subtype, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : (⟨x, hA.le hx⟩ : ↥S) ∈ A.subgroupOf S := hx
    exact ⟨⟨x, hA.le hx⟩, hA'M' hx', rfl⟩
  · refine lt_of_le_of_ne (Subgroup.map_subtype_le M') ?_
    intro h
    apply hM'coatom.1
    have htop : (⊤ : Subgroup ↥S).map S.subtype = S := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have : M'.map S.subtype = (⊤ : Subgroup ↥S).map S.subtype := by rw [htop]; exact h
    exact Subgroup.map_injective S.subtype_injective this
  · rintro s hs _ ⟨y, hy, rfl⟩
    exact ⟨⟨s, hs⟩ * y * ⟨s, hs⟩⁻¹, hnormal.conj_mem y hy ⟨s, hs⟩, rfl⟩

theorem conjSub_iSup {ι : Sort*} (t : G) (p : ι → Subgroup G) :
    conjSub t (⨆ i, p i) = ⨆ i, conjSub t (p i) :=
  Subgroup.map_iSup _ _

theorem conjSub_biSup_conj_le {S A : Subgroup G} {t : G} (ht : t ∈ S) :
    conjSub t (⨆ s ∈ S, conjSub s A) ≤ ⨆ s ∈ S, conjSub s A := by
  rw [conjSub_iSup]
  refine iSup_le fun s => ?_
  rw [conjSub_iSup]
  refine iSup_le fun hs => ?_
  rw [← conjSub_mul]
  exact le_iSup₂_of_le (t * s) (S.mul_mem ht hs) le_rfl

theorem commute_of_isCyclic {A : Subgroup G} (h : IsCyclic ↥A) {x y : G} (hx : x ∈ A)
    (hy : y ∈ A) : x * y = y * x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥A)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  have hx' : x = (g : G) ^ m := by simpa using (congrArg Subtype.val hm).symm
  have hy' : y = (g : G) ^ n := by simpa using (congrArg Subtype.val hn).symm
  rw [hx', hy']
  exact (Commute.zpow_zpow_self (g : G) m n).eq

end CFSG.ClassicalInvolution.Asc77
