module

public import CFSG.Holt.H78.Dihedral

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

section Count

theorem iUnion_longInvSwap (α : Ω) : ⋃ β : Ω, longInvSwap G Ω α β = longInv G Ω :=
  Set.Subset.antisymm (Set.iUnion_subset fun β => longInvSwap_subset_longInv α β)
    fun t ht => Set.mem_iUnion.mpr ⟨t • α, ht, rfl⟩

theorem pairwise_disjoint_longInvSwap (α : Ω) :
    Pairwise (Function.onFun Disjoint (longInvSwap G Ω α)) :=
  fun _ _ h => Set.disjoint_left.mpr fun _ h₁ h₂ => h (h₁.2.symm.trans h₂.2)

theorem card_longInvAt_smul (g : G) (α : Ω) :
    Nat.card (longInvAt G Ω (g • α)) = Nat.card (longInvAt G Ω α) := by
  rw [← conj_longInvAt]
  exact Nat.card_image_of_injective (fun x y hxy => by simpa using hxy) _

theorem card_longInvAt_eq [IsPretransitive G Ω] (α β : Ω) :
    Nat.card (longInvAt G Ω α) = Nat.card (longInvAt G Ω β) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G β α
  exact card_longInvAt_smul g β

theorem IsStarGroup.card_longInvAt_eq [Finite G] (hG : IsStarGroup G Ω) (α β : Ω) :
    Nat.card (longInvAt G Ω α) = Nat.card (longInvAt G Ω β) :=
  haveI := hG.isPretransitive
  CFSG.Holt.H78.card_longInvAt_eq α β

variable [Finite G]

theorem card_longInv_eq_sum_card_longInvAt [Fintype Ω] :
    Nat.card (longInv G Ω) = ∑ γ : Ω, Nat.card (longInvAt G Ω γ) := by
  rw [← iUnion_longInvAt, Nat.card_coe_set_eq,
    Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _) pairwise_disjoint_longInvAt,
    finsum_eq_sum_of_fintype]
  simp only [Nat.card_coe_set_eq]

theorem card_longInv_eq_sum_card_longInvSwap [Fintype Ω] (α : Ω) :
    Nat.card (longInv G Ω) = ∑ β : Ω, Nat.card (longInvSwap G Ω α β) := by
  rw [← iUnion_longInvSwap α, Nat.card_coe_set_eq,
    Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _) (pairwise_disjoint_longInvSwap α),
    finsum_eq_sum_of_fintype]
  simp only [Nat.card_coe_set_eq]

theorem card_longInv_eq_mul [Fintype Ω] [IsPretransitive G Ω] (α : Ω) :
    Nat.card (longInv G Ω) = Fintype.card Ω * Nat.card (longInvAt G Ω α) := by
  rw [card_longInv_eq_sum_card_longInvAt,
    Finset.sum_congr rfl fun γ _ => card_longInvAt_eq γ α, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]

theorem sum_card_longInvSwap_of_isPretransitive [Fintype Ω] [DecidableEq Ω]
    [IsPretransitive G Ω] (α : Ω) :
    ∑ β ∈ Finset.univ.erase α, Nat.card (longInvSwap G Ω α β) =
      Nat.card (longInvAt G Ω α) * (Fintype.card Ω - 1) := by
  have h := (card_longInv_eq_sum_card_longInvSwap (G := G) α).symm.trans (card_longInv_eq_mul α)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ α), longInvSwap_self] at h
  rw [Nat.mul_sub_one, mul_comm]
  omega

theorem sum_card_longInvSwap [Fintype Ω] [DecidableEq Ω] (hG : IsStarGroup G Ω) (α : Ω) :
    ∑ β ∈ Finset.univ.erase α, Nat.card (longInvSwap G Ω α β) =
      Nat.card (longInvAt G Ω α) * (Fintype.card Ω - 1) :=
  haveI := hG.isPretransitive
  sum_card_longInvSwap_of_isPretransitive α

end Count

section Delta

theorem holtDelta_comm (α β : Ω) : holtDelta G Ω α β = holtDelta G Ω β α :=
  Set.ext fun _ => by rw [mem_holtDelta, mem_holtDelta, longInvSwap_comm]

theorem smul_holtDelta (g : G) (α β : Ω) :
    g • holtDelta G Ω α β = holtDelta G Ω (g • α) (g • β) := by
  ext γ
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_holtDelta, mem_holtDelta]
  constructor
  · rintro ⟨t, ht, htγ⟩
    refine ⟨g * t * g⁻¹, conj_mem_longInvSwap ht g, ?_⟩
    rw [mul_smul, mul_smul, htγ, smul_inv_smul]
  · rintro ⟨t, ht, htγ⟩
    have h := conj_mem_longInvSwap ht g⁻¹
    rw [inv_smul_smul, inv_smul_smul] at h
    refine ⟨g⁻¹ * t * g⁻¹⁻¹, h, ?_⟩
    rw [inv_inv, mul_smul, mul_smul, smul_inv_smul, htγ]

theorem stabilizer_pair_le (α β : Ω) :
    stabilizer G ({α, β} : Set Ω) ≤ stabilizer G (holtDelta G Ω α β) := by
  intro g hg
  rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton,
    Set.pair_eq_pair_iff] at hg
  rw [mem_stabilizer_iff, smul_holtDelta]
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, holtDelta_comm]

theorem mem_stabilizer_holtDelta_of_mem_longInvSwap {t : G} {α β : Ω}
    (ht : t ∈ longInvSwap G Ω α β) : t ∈ stabilizer G (holtDelta G Ω α β) := by
  apply stabilizer_pair_le
  rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, ht.2,
    smul_eq_of_mem_longInvSwap ht, Set.pair_comm]

theorem closure_longInvSwap_le_stabilizer (α β : Ω) :
    Subgroup.closure (longInvSwap G Ω α β) ≤ stabilizer G (holtDelta G Ω α β) :=
  (Subgroup.closure_le _).mpr fun _ ht => mem_stabilizer_holtDelta_of_mem_longInvSwap ht

theorem mul_mem_stabilizer_inf_of_mem_longInvSwap {s s' : G} {α β : Ω}
    (hs : s ∈ longInvSwap G Ω α β) (hs' : s' ∈ longInvSwap G Ω α β) :
    s * s' ∈ stabilizer G α ⊓ stabilizer G β :=
  Subgroup.mem_inf.mpr
    ⟨by rw [mem_stabilizer_iff, mul_smul, hs'.2, smul_eq_of_mem_longInvSwap hs],
      by rw [mem_stabilizer_iff, mul_smul, smul_eq_of_mem_longInvSwap hs', hs.2]⟩

theorem holtDelta_nonempty_iff {α β : Ω} :
    (holtDelta G Ω α β).Nonempty ↔ (longInvSwap G Ω α β).Nonempty :=
  ⟨fun ⟨_, t, ht, _⟩ => ⟨t, ht⟩, fun ⟨t, ht⟩ =>
    let ⟨γ, hγ, _⟩ := ht.1.2
    ⟨γ, t, ht, hγ⟩⟩

theorem left_notMem_holtDelta {α β : Ω} (h : α ≠ β) : α ∉ holtDelta G Ω α β :=
  fun ⟨_, ht, htα⟩ => h (htα.symm.trans ht.2)

theorem right_notMem_holtDelta {α β : Ω} (h : α ≠ β) : β ∉ holtDelta G Ω α β := by
  rw [holtDelta_comm]
  exact left_notMem_holtDelta (Ne.symm h)

variable [Finite G]

theorem holtDelta_nonempty (hG : IsStarGroup G Ω) (α β : Ω) : (holtDelta G Ω α β).Nonempty :=
  holtDelta_nonempty_iff.mpr (longInvSwap_nonempty hG α β)

private theorem exists_pow_mul_smul_eq {s s' : G} {α β γ γ' : Ω} (hs : s ∈ longInvSwap G Ω α β)
    (hγ : s • γ = γ) (hs' : s' ∈ longInvSwap G Ω α β) (hγ' : s' • γ' = γ') :
    ∃ n : ℕ, (s * s') ^ n • γ = γ' :=
  ⟨_, pow_period_div_two_mul_smul_eq ⟨hs.1, hγ⟩ ⟨hs'.1, hγ'⟩⟩

theorem holtDelta_eq_orbit_closure {α β γ : Ω} (hγ : γ ∈ holtDelta G Ω α β) :
    holtDelta G Ω α β = orbit (Subgroup.closure (longInvSwap G Ω α β)) γ := by
  obtain ⟨s, hs, hsγ⟩ := hγ
  ext γ'
  constructor
  · rintro ⟨s', hs', hs'γ'⟩
    obtain ⟨n, hn⟩ := exists_pow_mul_smul_eq hs hsγ hs' hs'γ'
    exact ⟨⟨_, Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure hs)
      (Subgroup.subset_closure hs')) n⟩, hn⟩
  · rintro ⟨⟨g, hg⟩, rfl⟩
    show g • γ ∈ holtDelta G Ω α β
    rw [← mem_stabilizer_iff.mp (closure_longInvSwap_le_stabilizer α β hg)]
    exact Set.smul_mem_smul_set ⟨s, hs, hsγ⟩

theorem holtDelta_eq_orbit_of_mem {α β γ : Ω} (hγ : γ ∈ holtDelta G Ω α β) :
    holtDelta G Ω α β = orbit ↥(stabilizer G α ⊓ stabilizer G β) γ := by
  obtain ⟨s, hs, hsγ⟩ := hγ
  ext γ'
  constructor
  · rintro ⟨s', hs', hs'γ'⟩
    obtain ⟨n, hn⟩ := exists_pow_mul_smul_eq hs hsγ hs' hs'γ'
    exact ⟨⟨_, Subgroup.pow_mem _ (mul_mem_stabilizer_inf_of_mem_longInvSwap hs hs') n⟩, hn⟩
  · rintro ⟨⟨g, hg⟩, rfl⟩
    show g • γ ∈ holtDelta G Ω α β
    have h : g • γ ∈ g • holtDelta G Ω α β := Set.smul_mem_smul_set ⟨s, hs, hsγ⟩
    rwa [smul_holtDelta, mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hg).1,
      mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hg).2] at h

@[nolint unusedArguments]
theorem holtDelta_eq_orbit (_hG : IsStarGroup G Ω) {α β γ : Ω} (_hαβ : α ≠ β)
    (hγ : γ ∈ holtDelta G Ω α β) :
    holtDelta G Ω α β = orbit ↥(stabilizer G α ⊓ stabilizer G β) γ :=
  holtDelta_eq_orbit_of_mem hγ

end Delta

section Odd

variable [Finite Ω]

private theorem card_orbit_closure_modEq {s : G} {α β : Ω} (hs : s ∈ longInvSwap G Ω α β)
    (δ : Ω) : Nat.card (orbit (Subgroup.closure (longInvSwap G Ω α β)) δ) ≡
      Nat.card ↥({ω | s • ω = ω} ∩ orbit (Subgroup.closure (longInvSwap G Ω α β)) δ)
      [MOD 2] := by
  have hsL : s ∈ Subgroup.closure (longInvSwap G Ω α β) := Subgroup.subset_closure hs
  have hP := isPGroup_zpowers_of_orderOf_eq_two
    (x := (⟨s, hsL⟩ : Subgroup.closure (longInvSwap G Ω α β)))
    (by rw [Subgroup.orderOf_mk]; exact hs.1.1)
  have h := card_orbit_modEq_card_fixSet_inter (Ω := Ω) hP δ
  rwa [fixSet_zpowers] at h

variable [Finite G]

theorem odd_card_holtDelta {α β : Ω} (hne : (longInvSwap G Ω α β).Nonempty) :
    Odd (Nat.card (holtDelta G Ω α β)) := by
  obtain ⟨s, hs⟩ := hne
  obtain ⟨γ, hγ, -⟩ := hs.1.2
  have hγΔ : γ ∈ holtDelta G Ω α β := ⟨s, hs, hγ⟩
  have hmod := card_orbit_closure_modEq hs γ
  have hF : {ω | s • ω = ω} ∩ orbit (Subgroup.closure (longInvSwap G Ω α β)) γ = {γ} :=
    Set.ext fun ω => ⟨fun h => (smul_eq_iff_of_mem_longInvAt ⟨hs.1, hγ⟩ ω).mp h.1,
      fun h => by rw [Set.mem_singleton_iff.mp h]; exact ⟨hγ, mem_orbit_self γ⟩⟩
  have h1 : Nat.card ({γ} : Set Ω) = 1 := Nat.card_unique
  rw [hF, h1, ← holtDelta_eq_orbit_closure hγΔ] at hmod
  exact Nat.odd_iff.mpr hmod

theorem IsStarGroup.odd_card_holtDelta (hG : IsStarGroup G Ω) (α β : Ω) :
    Odd (Nat.card (holtDelta G Ω α β)) :=
  CFSG.Holt.H78.odd_card_holtDelta (longInvSwap_nonempty hG α β)

end Odd

section DeltaPrime

theorem mem_holtDelta'_iff {α β γ : Ω} : γ ∈ holtDelta' G Ω α β ↔ α ∈ holtDelta G Ω β γ :=
  ⟨fun ⟨s, ⟨hs, hsα⟩, hsβ⟩ => ⟨s, ⟨hs, hsβ⟩, hsα⟩,
    fun ⟨s, ⟨hs, hsβ⟩, hsα⟩ => ⟨s, ⟨hs, hsα⟩, hsβ⟩⟩

theorem smul_holtDelta' (g : G) (α β : Ω) :
    g • holtDelta' G Ω α β = holtDelta' G Ω (g • α) (g • β) := by
  ext γ
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_holtDelta', mem_holtDelta']
  constructor
  · rintro ⟨s, hs, hsβ⟩
    refine ⟨g * s * g⁻¹, conj_mem_longInvAt hs g, ?_⟩
    rw [mul_smul, mul_smul, inv_smul_smul, hsβ, smul_inv_smul]
  · rintro ⟨s, hs, hsβ⟩
    have h := conj_mem_longInvAt hs g⁻¹
    rw [inv_smul_smul] at h
    refine ⟨g⁻¹ * s * g⁻¹⁻¹, h, ?_⟩
    rw [inv_inv, mul_smul, mul_smul, hsβ]

theorem stabilizer_inf_le_stabilizer_holtDelta' (α β : Ω) :
    stabilizer G α ⊓ stabilizer G β ≤ stabilizer G (holtDelta' G Ω α β) := fun g hg => by
  rw [mem_stabilizer_iff, smul_holtDelta', mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hg).1,
    mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hg).2]

theorem notMem_holtDelta' {α β : Ω} (h : β ≠ α) : α ∉ holtDelta' G Ω α β := by
  rw [mem_holtDelta'_iff]
  exact right_notMem_holtDelta h

theorem holtDelta'_nonempty (hG : IsStarGroup G Ω) (α β : Ω) :
    (holtDelta' G Ω α β).Nonempty :=
  let ⟨s, hs⟩ := hG.longInvAt_nonempty α
  ⟨s • β, s, hs, rfl⟩

end DeltaPrime

end CFSG.Holt.H78
