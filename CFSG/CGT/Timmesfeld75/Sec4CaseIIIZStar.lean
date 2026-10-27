module

public import CFSG.CGT.Timmesfeld75.Sec4TwoStruct
public import CFSG.CGT.Timmesfeld75.Core214Proof

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Odd

variable {G : Type} [Group G]

theorem odd_orderOf_mul_of_sec3 [Finite G] {T T' N : Subgroup G} (hS : Sec3 T T')
    (hM : cfgM T T' ≤ N) (hne : T' ≠ T) {t c : G} (ht : t ∈ T) (htN : t ∉ N) (hc : c ∈ T')
    (hcN : c ∉ N) : Odd (orderOf (t * c)) := by
  obtain ⟨y, hyX, hy⟩ := hS.conj
  refine hS.odd_orderOf_mul (x := 1) (y := y) (Subgroup.one_mem _) hyX ?_
    (by rw [conjSubgroup_one]; exact ht) ?_ ?_ ?_
  · rw [conjSubgroup_one, ← hy]
    exact hne.symm
  · exact fun htM => htN (hM htM)
  · rw [← hy]
    exact hc
  · exact fun hcM => hcN (hM hcM)

theorem eq_pow_sq_of_odd_orderOf {g : G} (hg : Odd (orderOf g)) :
    ∃ k : ℕ, g = (g ^ 2) ^ k := by
  obtain ⟨e, he⟩ := hg
  refine ⟨e + 1, ?_⟩
  have h1 : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  rw [← pow_mul]
  have h2 : g ^ (2 * (e + 1)) = g ^ (orderOf g) * g := by
    rw [← pow_succ, he]
    congr 1
  rw [h2, h1, one_mul]

theorem mul_mem_of_sq_mem_of_odd_orderOf {Y P : Subgroup G}
    (hsq : ∀ x ∈ Y, ∀ y ∈ Y, x * x = 1 → y * y = 1 → (x * y) ^ 2 ∈ P)
    {x y : G} (hx : x ∈ Y) (hy : y ∈ Y) (hxx : x * x = 1)
    (hyy : y * y = 1) (hodd : Odd (orderOf (x * y))) : x * y ∈ P := by
  obtain ⟨k, hk⟩ := eq_pow_sq_of_odd_orderOf hodd
  have := P.pow_mem (hsq x hx y hy hxx hyy) k
  rwa [← hk] at this

end Odd

section ZStar

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.exists_odd_subgroup (h : Sec4Hyp T T₁ a T₂)
    (hq : Nat.card T = 2 * Nat.card (normIn T T₁)) :
    ∃ P : Subgroup G, P ≤ sec4Y T T₁ T₂ ∧
      (∀ x ∈ sec4Y T T₁ T₂, ∀ y ∈ sec4Y T T₁ T₂, x * x = 1 → y * y = 1 → (x * y) ^ 2 ∈ P) ∧
      ∀ p ∈ P, ∃ m : ℕ, Odd m ∧ p ^ m ∈ sec4N T T₁ T₂ := by
  have hN : ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)).Normal := h.normal_sec4N
  have hstrong := h.strongWC_img_of_le (K := sec4Y T T₁ T₂) h.sec4Y_le_normalizer
    left_le_sec4Y
  have hWC := hstrong.isWC
  have hcard : Nat.card ((T.subgroupOf (sec4Y T T₁ T₂)).map
      (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))) = 2 := by
    have h1 := card_img_mul_card_inf (K := sec4Y T T₁ T₂) (N := sec4N T T₁ T₂) (T := T)
      left_le_sec4Y
    rw [h.inf_sec4N_eq, hq] at h1
    have hLpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hLpos h1
  have hcl := normalClosure_img_eq_top (K := sec4Y T T₁ T₂) (N := sec4N T T₁ T₂) (T := T)
    h.normalClosure_sec4Y
  have key : ∀ S : Subgroup (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)),
      S = ⊤ → ZStarCase ↥S →
        ZStarCase (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) := by
    rintro S rfl hz
    exact zStarCase_of_mulEquiv Subgroup.topEquiv hz
  have hZ := key _ hcl (zStarCase_normalClosure_of_card_two hWC hcard)
  refine ⟨((fusionOddCore (↥(sec4Y T T₁ T₂) ⧸
    (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))).comap
      (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))).map
        (sec4Y T T₁ T₂).subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro x hx y hy hxx hyy
    have hmem := (zStarCase_iff.1 hZ) (QuotientGroup.mk ⟨x, hx⟩) (QuotientGroup.mk ⟨y, hy⟩)
    refine ⟨(⟨y, hy⟩ * ⟨x, hx⟩ : ↥(sec4Y T T₁ T₂))⁻¹ * (⟨x, hx⟩ * ⟨y, hy⟩), hmem, ?_⟩
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
    show (y * x)⁻¹ * (x * y) = (x * y) ^ 2
    rw [mul_inv_rev, hxi, hyi, pow_two]
  · rintro _ ⟨w, hw, rfl⟩
    have hodd := odd_card_fusionOddCore (↥(sec4Y T T₁ T₂) ⧸
      (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))
    refine ⟨Nat.card (fusionOddCore (↥(sec4Y T T₁ T₂) ⧸
      (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))), hodd, ?_⟩
    have h1 := pow_card_eq_one' (G := ↥(fusionOddCore (↥(sec4Y T T₁ T₂) ⧸
      (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))) (x := ⟨_, hw⟩)
    have h2 : (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) w) ^
        Nat.card (fusionOddCore (↥(sec4Y T T₁ T₂) ⧸
          (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))) = 1 :=
      congrArg Subtype.val h1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact Subgroup.mem_subgroupOf.1 h2

end ZStar

end CFSG.CGT.Timmesfeld75
