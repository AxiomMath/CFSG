module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup
open scoped Pointwise

section SylowInf

variable {G : Type*} [Group G] [Finite G]

theorem exists_pGroup_inf_sylow (p : ℕ) [Fact p.Prime] (M A Z : Subgroup G) (hAM : A ≤ M)
    (hZM : Z ≤ M) (hnorm : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A) (hZ : IsPGroup p ↥Z) :
    ∃ Q : Subgroup G, Q ≤ M ∧ Z ≤ Q ∧ IsPGroup p ↥Q ∧
      Nat.card ↥(Q ⊓ A) = p ^ (Nat.card ↥A).factorization p := by
  have hAn : (A.subgroupOf M).Normal := by
    refine ⟨fun a ha m => ?_⟩
    exact hnorm m m.2 a ha
  have hZ' : IsPGroup p ↥(Z.subgroupOf M) :=
    hZ.of_equiv (Subgroup.subgroupOfEquivOfLe hZM).symm
  obtain ⟨Q', hQ'⟩ := hZ'.exists_le_sylow
  obtain ⟨P', hP'⟩ := CFSG.Glauberman.sylow_inf_normal Q' (N := A.subgroupOf M)
  refine ⟨(Q' : Subgroup ↥M).map M.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨⟨z, hZM hz⟩, hQ' hz, rfl⟩
  · exact Q'.isPGroup'.map M.subtype
  · have e1 : (Q' : Subgroup ↥M).map M.subtype ⊓ A =
        ((Q' : Subgroup ↥M) ⊓ A.subgroupOf M).map M.subtype := by
      rw [Subgroup.map_inf_eq _ _ M.subtype M.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hAM]
    rw [e1, Subgroup.card_map_of_injective M.subtype_injective]
    have e2 : Nat.card ↥((Q' : Subgroup ↥M) ⊓ A.subgroupOf M) =
        Nat.card ↥(((Q' : Subgroup ↥M) ⊓ A.subgroupOf M).subgroupOf (A.subgroupOf M)) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
    rw [e2, ← hP']
    have e3 := Sylow.card_eq_multiplicity P'
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv] at e3
    exact e3

end SylowInf

section CardSup

variable {G : Type*} [Group G]

theorem card_sup_of_le_normalizer (S Z : Subgroup G) (hZ : Z ≤ normalizer (S : Set G))
    (hd : Disjoint S Z) : Nat.card ↥(S ⊔ Z) = Nat.card ↥S * Nat.card ↥Z := by
  have hcoe : ((S ⊔ Z : Subgroup G) : Set G) = (S : Set G) * (Z : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left S Z hZ
  have hc : (S.subgroupOf (S ⊔ Z)).IsComplement' (Z.subgroupOf (S ⊔ Z)) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [Subgroup.disjoint_def]
      intro x hx hx'
      exact Subtype.ext (Subgroup.disjoint_def.mp hd hx hx')
    · apply Set.eq_univ_of_forall
      intro x
      have hx : (x : G) ∈ ((S ⊔ Z : Subgroup G) : Set G) := x.2
      rw [hcoe] at hx
      obtain ⟨s, hs, z, hz, hsz⟩ := hx
      exact ⟨⟨s, Subgroup.mem_sup_left hs⟩, hs, ⟨z, Subgroup.mem_sup_right hz⟩, hz, Subtype.ext hsz⟩
  have h := hc.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at h
  exact h.symm

end CardSup

section CardLemmas

variable {G : Type*} [Group G] [Finite G]

theorem card_sylow_inf_normal (p : ℕ) [Fact p.Prime] (S : Sylow p G) (N : Subgroup G) [N.Normal] :
    Nat.card ↥((S : Subgroup G) ⊓ N) = p ^ (Nat.card ↥N).factorization p := by
  obtain ⟨P', hP'⟩ := CFSG.Glauberman.sylow_inf_normal S (N := N)
  have e2 : Nat.card ↥((S : Subgroup G) ⊓ N) =
      Nat.card ↥(((S : Subgroup G) ⊓ N).subgroupOf N) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  rw [e2, ← hP']
  exact Sylow.card_eq_multiplicity P'

theorem card_le_pow_factorization (p : ℕ) [Fact p.Prime] {P B : Subgroup G} (hP : IsPGroup p ↥P)
    (hPB : P ≤ B) : Nat.card ↥P ≤ p ^ (Nat.card ↥B).factorization p := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
  have hd : p ^ k ∣ Nat.card ↥B := hk ▸ Subgroup.card_dvd_of_le hPB
  have hk' : k ≤ (Nat.card ↥B).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out : p.Prime) Nat.card_pos.ne').mp hd
  rw [hk]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hk'

end CardLemmas

end CFSG.GH74.GLS.IVK
