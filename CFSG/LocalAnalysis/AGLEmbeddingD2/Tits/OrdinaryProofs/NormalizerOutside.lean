module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

theorem eq_of_two_group_between {G : Type*} [Group G] [Finite G] {B T R : Subgroup G}
    (hTR : T ≤ R) (hRB : R ≤ B) (hR : IsPGroup 2 R) (hodd : ¬ 2 ∣ (T.subgroupOf B).index) :
    R = T := by
  have hrel : T.relIndex R * R.relIndex B = T.relIndex B :=
    Subgroup.relIndex_mul_relIndex T R B hTR hRB
  have hodd' : ¬ 2 ∣ T.relIndex R := by
    intro h
    apply (show ¬ 2 ∣ T.relIndex B from hodd)
    rw [← hrel]
    exact Dvd.dvd.mul_right h _
  have hidx : T.relIndex R = 1 := by
    show (T.subgroupOf R).index = 1
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := R)).mp hR
    have hc := Subgroup.card_mul_index (T.subgroupOf R)
    have hdvd : (T.subgroupOf R).index ∣ 2 ^ n := by
      rw [← hn, ← hc]
      exact Dvd.intro_left _ rfl
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases k with _ | k
    · simpa using hk
    · exfalso
      apply hodd'
      show 2 ∣ (T.subgroupOf R).index
      rw [hk]
      exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hidx) hTR

theorem exists_normalizer_not_mem_of_two_group {G : Type*} [Group G] [Finite G]
    {S A : Subgroup G} (hS : IsPGroup 2 S) (hAS : A ≤ S) (hne : A ≠ S) :
    ∃ y ∈ S, y ∈ Subgroup.normalizer (A : Set G) ∧ y ∉ A ∧ ∃ k : ℕ, y ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have htop : A.subgroupOf S ≠ ⊤ := by
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact hne (le_antisymm hAS h)
  have hlt : A.subgroupOf S < ⊤ := lt_top_iff_ne_top.mpr htop
  have hmem := Group.normalizerCondition_of_isNilpotent (A.subgroupOf S) hlt
  obtain ⟨-, y, hy, hyA⟩ := IsConcreteLE.lt_iff_le_and_exists.mp hmem
  have hyA' : (y : G) ∉ A := fun h => hyA (Subgroup.mem_subgroupOf.mpr h)
  refine ⟨(y : G), y.2, ?_, hyA', ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    by_cases hh : h ∈ S
    · have := Subgroup.mem_normalizer_iff.mp hy ⟨h, hh⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · have hconj : (y : G) * h * (y : G)⁻¹ ∉ S := by
        intro hc
        apply hh
        have := S.mul_mem (S.mul_mem (S.inv_mem y.2) hc) y.2
        simpa [mul_assoc] using this
      exact ⟨fun h' => (hh (hAS h')).elim, fun h' => (hconj (hAS h')).elim⟩
  · obtain ⟨k, hk⟩ := hS y
    refine ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this

theorem exists_mem_normalizer_not_mem_of_two_dvd_index
    {G : Type*} [Group G] [Finite G] {H B T : Subgroup G} (hBH : B ≤ H)
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T B) (h2 : 2 ∣ (B.subgroupOf H).index) :
    ∃ x ∈ H, x ∈ Subgroup.normalizer (T : Set G) ∧ x ∉ B ∧ ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨hTB, hTp, hTodd⟩ := hT
  have hTH : T ≤ H := hTB.trans hBH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsub : IsPGroup 2 (T.subgroupOf H) :=
    hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hTsub
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup G, S = (Q : Subgroup H).map H.subtype := ⟨_, rfl⟩
  have hSle : S ≤ H := by
    rw [hSdef]
    exact Subgroup.map_subtype_le _
  have hSp : IsPGroup 2 S := by
    rw [hSdef]
    exact (Sylow.isPGroup' Q).of_equiv
      (Subgroup.equivMapOfInjective _ H.subtype Subtype.val_injective)
  have hTS : T ≤ S := by
    rw [hSdef]
    intro t ht
    have hmem : (⟨t, hTH ht⟩ : H) ∈ T.subgroupOf H := Subgroup.mem_subgroupOf.mpr ht
    exact Subgroup.mem_map.mpr ⟨⟨t, hTH ht⟩, hQ hmem, rfl⟩
  have hcomp : S.subgroupOf H = (Q : Subgroup H) := by
    rw [hSdef]
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hSodd : ¬ 2 ∣ (S.subgroupOf H).index := by
    rw [hcomp]
    exact Sylow.not_dvd_index Q
  have hTne : T ≠ S := by
    intro hEq
    apply hSodd
    rw [← hEq]
    show 2 ∣ T.relIndex H
    rw [← Subgroup.relIndex_mul_relIndex T B H hTB hBH]
    exact Dvd.dvd.mul_left h2 _
  obtain ⟨x, hxS, hxN, hxT, k, hk⟩ := exists_normalizer_not_mem_of_two_group hSp hTS hTne
  refine ⟨x, hSle hxS, hxN, ?_, k, hk⟩
  intro hxB
  have hRp : IsPGroup 2 (S ⊓ B : Subgroup G) := IsPGroup.to_le hSp inf_le_left
  have hTR : T ≤ S ⊓ B := le_inf hTS hTB
  have hRT : S ⊓ B = T := eq_of_two_group_between hTR inf_le_right hRp hTodd
  have hxmem : x ∈ S ⊓ B := ⟨hxS, hxB⟩
  rw [hRT] at hxmem
  exact hxT hxmem

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

end
