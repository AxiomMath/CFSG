module

public import CFSG.CGT.Timmesfeld75.PlaneCount
public import CFSG.CGT.Timmesfeld75.L2Sylow
public import CFSG.CGT.Timmesfeld75.Sec3Conj

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

section Plane

variable {𝒯 : Set (Subgroup G)} {q c : ℕ}

theorem exists_mem_of_traces {a : ℕ} (ha : 2 ≤ a) {Q : Subgroup G}
    (hTI : ∀ R ∈ 𝒯, ∀ S ∈ 𝒯, R ≠ S → R ⊓ S = ⊥) (hQ : Nat.card ↥Q ≤ a ^ 3)
    (htr : ∀ R ∈ 𝒯, Nat.card ↥(R ⊓ Q) = a) (hpts : a ^ 2 + a + 1 ≤ 𝒯.ncard) :
    ∀ z ∈ Q, z ≠ 1 → ∃ R ∈ 𝒯, z ∈ R := by
  intro z hzQ hz1
  by_contra hno
  push Not at hno
  set W : Set G := ⋃ R ∈ 𝒯, (((R ⊓ Q : Subgroup G) : Set G) \ {1}) with hW
  have hone : ∀ R ∈ 𝒯, (1 : G) ∈ ((R ⊓ Q : Subgroup G) : Set G) := fun R _ =>
    (R ⊓ Q).one_mem
  have hWcard : W.ncard = 𝒯.ncard * (a - 1) := by
    refine ncard_biUnion_const (Set.toFinite 𝒯)
      (s := fun R => ((R ⊓ Q : Subgroup G) : Set G) \ {1}) (m := a - 1) ?_ ?_
    · intro R hR S hS hRS
      refine Set.disjoint_left.2 fun x hx hx' => ?_
      have hxRS : x ∈ R ⊓ S := ⟨hx.1.1, hx'.1.1⟩
      rw [hTI R hR S hS hRS, Subgroup.mem_bot] at hxRS
      exact hx.2 hxRS
    · intro R hR
      rw [Set.ncard_sdiff_singleton_of_mem (hone R hR), ← Nat.card_coe_set_eq]
      have := htr R hR
      rw [← this]
      rfl
  have hzW : z ∉ W := by
    intro hz
    simp only [hW, Set.mem_iUnion] at hz
    obtain ⟨R, hR, hzR, -⟩ := hz
    exact hno R hR hzR.1
  have hsub : insert z W ⊆ ((Q : Set G) \ {1}) := by
    refine Set.insert_subset ⟨hzQ, hz1⟩ (Set.iUnion₂_subset fun R _ => ?_)
    exact Set.sdiff_subset_sdiff_left (fun x hx => hx.2)
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : (Q : Set G).ncard = Nat.card ↥Q := (Nat.card_coe_set_eq (Q : Set G)).symm
  rw [Set.ncard_insert_of_notMem hzW (Set.toFinite _), hWcard,
    Set.ncard_sdiff_singleton_of_mem Q.one_mem, h2] at h
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  have h3 : (a' ^ 2 + 3 * a' + 3) * a' ≤ 𝒯.ncard * a' := Nat.mul_le_mul_right a' (by nlinarith)
  have hq' : 1 ≤ a' := by omega
  have h4 : (a' + 1) ^ 3 = a' ^ 3 + 3 * a' ^ 2 + 3 * a' + 1 := by ring
  have h5 : 𝒯.ncard * a' + 2 ≤ Nat.card ↥Q := by omega
  nlinarith [h5, hQ, h3, h4]

omit [Finite G] in
theorem PlaneData.of_two_trans {J U V : Subgroup G} {q : ℕ} (hUJ : U ≤ J)
    (htrans : ∀ {a₁ a₂ b₁ b₂ : G}, a₁ ∈ J → a₂ ∈ J → b₁ ∈ J → b₂ ∈ J →
      conjSubgroup a₁ U ≠ conjSubgroup a₂ U → conjSubgroup b₁ U ≠ conjSubgroup b₂ U →
      ∃ r ∈ J, conjSubgroup r (conjSubgroup a₁ U) = conjSubgroup b₁ U ∧
        conjSubgroup r (conjSubgroup a₂ U) = conjSubgroup b₂ U)
    {s : G} (hs : s ∈ J) (hV : V = conjSubgroup s U) (hUV : U ≠ V)
    (hq : Nat.card ↥U = q * Nat.card ↥(normIn U V)) :
    PlaneData {S | ∃ j ∈ J, S = conjSubgroup j U} q (Nat.card ↥(U ⊔ V)) := by
  have key : ∀ {R S : Subgroup G}, (∃ j ∈ J, R = conjSubgroup j U) →
      (∃ j ∈ J, S = conjSubgroup j U) → R ≠ S → ∃ r : G,
        conjSubgroup r R = U ∧ conjSubgroup r S = V := by
    rintro R S ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hne
    obtain ⟨r, hr, h1, h2⟩ := htrans ha hb J.one_mem hs hne (by
      rw [conjSubgroup_one, ← hV]
      exact hUV)
    exact ⟨r, by rw [h1, conjSubgroup_one], by rw [h2, ← hV]⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro R ⟨a, ha, rfl⟩ S ⟨b, hb, rfl⟩ t ht
    have htJ : t ∈ J := conjSubgroup_le_of_le_of_mem hUJ ha ht
    exact ⟨t * b, J.mul_mem htJ hb, conjSubgroup_conjSubgroup t b U⟩
  · intro R hR S hS hne
    obtain ⟨r, h1, h2⟩ := key hR hS hne
    have h3 : Nat.card ↥(normIn R S) = Nat.card ↥(normIn U V) := by
      rw [← h1, ← h2, normIn_conj, card_conjSubgroup]
    have h4 : Nat.card ↥R = Nat.card ↥U := by
      rw [← h1, card_conjSubgroup]
    rw [h4, h3]
    exact hq
  · intro R hR S hS hne
    obtain ⟨r, h1, h2⟩ := key hR hS hne
    rw [← h1, ← h2, ← conjSubgroup_sup_eq_sup, card_conjSubgroup]

end Plane

end CFSG.CGT.Timmesfeld75
