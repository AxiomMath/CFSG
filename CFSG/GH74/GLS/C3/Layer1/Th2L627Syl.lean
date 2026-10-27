module

public import CFSG.GH74.GLS.C3.Layer1.BkS4Wr
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Th2.L627

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Bk

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowOf_ge {B K : Subgroup G} (hB : IsPGroup 2 ↥B) (hBK : B ≤ K) :
    ∃ T : Subgroup G, IsSylowOf 2 T K ∧ B ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB' : IsPGroup 2 ↥(B.subgroupOf K) := hB.comap_subtype
  obtain ⟨Q, hQ⟩ := hB'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥K).map K.subtype, ⟨Q, rfl⟩, fun b hb => ?_⟩
  exact ⟨⟨b, hBK hb⟩, hQ (Subgroup.mem_subgroupOf.2 hb), rfl⟩

theorem card_le_twoPartCard {A X : Subgroup G} (hA : IsPGroup 2 ↥A) (hAX : A ≤ X) :
    Nat.card ↥A ≤ twoPartCard X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hAT⟩ := exists_isSylowOf_ge hA hAX
  have h1 := hT.card_eq
  exact (Subgroup.card_le_of_le hAT).trans (by rw [h1]; rfl)

theorem exists_involution_of_ne_bot {W : Subgroup G} (hW : IsPGroup 2 ↥W) (hne : W ≠ ⊥) :
    ∃ w ∈ W, orderOf w = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hW.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero] at hk
    exact Subgroup.card_eq_one.1 hk
  have h2 : 2 ∣ Nat.card ↥W := by rw [hk]; exact dvd_pow_self 2 hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem exists_normalizer_sq_mem {S T : Subgroup G} (hS : IsPGroup 2 ↥S) (hTS : T ≤ S)
    (hne : T ≠ S) :
    ∃ a ∈ S, a ∈ normalizer (T : Set G) ∧ a ∉ T ∧ a * a ∈ T := by
  obtain ⟨n, hnS, hnT, hnn⟩ := Sec4Core.exists_mem_normalizer_not_mem hS hTS hne
  have hnN : n ∈ normalizer (T : Set G) :=
    mem_normalizer_of_two_sided (fun y hy => (hnn y hy).1) (fun y hy => (hnn y hy).2)
  obtain ⟨e, he⟩ := hS ⟨n, hnS⟩
  have hn1 : n ^ (2 ^ e) = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  have hex : ∃ f : ℕ, n ^ (2 ^ f) ∈ T := ⟨e, by rw [hn1]; exact T.one_mem⟩
  classical
  have hf : n ^ (2 ^ Nat.find hex) ∈ T := Nat.find_spec hex
  have hf0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hf
    exact hnT hf
  obtain ⟨g, hg⟩ : ∃ g, Nat.find hex = g + 1 := Nat.exists_eq_succ_of_ne_zero hf0
  have hg' : n ^ (2 ^ g) ∉ T := Nat.find_min hex (by omega)
  refine ⟨n ^ (2 ^ g), S.pow_mem hnS _, (normalizer (T : Set G)).pow_mem hnN _, hg', ?_⟩
  have : n ^ (2 ^ g) * n ^ (2 ^ g) = n ^ (2 ^ Nat.find hex) := by
    rw [← pow_add, hg, pow_succ, ← two_mul, mul_comm]
  rwa [this]

omit [Finite G] in
theorem sup_zpowers_le {S T : Subgroup G} {a : G} (hTS : T ≤ S) (ha : a ∈ S) :
    T ⊔ zpowers a ≤ S := sup_le hTS (zpowers_le.2 ha)

theorem card_le_of_subset_union {S T : Subgroup G} {a : G}
    (h : ∀ s ∈ S, s ∈ T ∨ a⁻¹ * s ∈ T) : Nat.card ↥S ≤ 2 * Nat.card ↥T := by
  have hsub : (S : Set G) ⊆ (T : Set G) ∪ ((fun τ => a * τ) '' (T : Set G)) := by
    intro s hs
    rcases h s hs with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨a⁻¹ * s, h1, by group⟩
  have h1 : Nat.card ↥S = (S : Set G).ncard := Nat.card_coe_set_eq (S : Set G)
  have h2 : Nat.card ↥T = (T : Set G).ncard := Nat.card_coe_set_eq (T : Set G)
  have h3 : (S : Set G).ncard ≤ ((T : Set G) ∪ ((fun τ => a * τ) '' (T : Set G))).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h4 := Set.ncard_union_le (T : Set G) ((fun τ => a * τ) '' (T : Set G))
  have h5 : ((fun τ => a * τ) '' (T : Set G)).ncard ≤ (T : Set G).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  omega

theorem two_mul_card_le {S T : Subgroup G} (hS : IsPGroup 2 ↥S) (hTS : T ≤ S) (hne : T ≠ S) :
    2 * Nat.card ↥T ≤ Nat.card ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hTp : IsPGroup 2 ↥T := hS.to_le hTS
  obtain ⟨j, hj⟩ := hTp.exists_card_eq
  have hlt : Nat.card ↥T < Nat.card ↥S := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hTS) fun h => hne ?_
    exact Subgroup.eq_of_le_of_card_ge hTS h.symm.le
  rw [hj, hk] at hlt
  have hjk : j < k := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  rw [hj, hk, ← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) hjk

end CFSG.GH74.GLS.Th2.L627
