module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem aqt_exists_psi {K1 K2 : Subgroup G} (hc : ⁅K1, K2⁆ = ⊥) (e1 : ↥K1 ≃* SL23)
    (e2 : ↥K2 ≃* SL23) :
    ∃ Ψ : SL23 × SL23 →* G, (∀ A B : SL23, Ψ (A, B) = (e1.symm A : G) * (e2.symm B : G)) ∧
      Ψ.range = K1 ⊔ K2 := by
  have hle : K1 ≤ centralizer (K2 : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hcomm : ∀ A B : SL23, Commute ((K1.subtype.comp e1.symm.toMonoidHom) A)
      ((K2.subtype.comp e2.symm.toMonoidHom) B) := by
    intro A B
    exact (Subgroup.mem_centralizer_iff.mp (hle (e1.symm A).2) (e2.symm B) (e2.symm B).2).symm
  have hr1 : (K1.subtype.comp e1.symm.toMonoidHom).range = K1 := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact (e1.symm A).2
    · intro hx
      exact ⟨e1 ⟨x, hx⟩, by simp⟩
  have hr2 : (K2.subtype.comp e2.symm.toMonoidHom).range = K2 := by
    ext x
    constructor
    · rintro ⟨B, rfl⟩
      exact (e2.symm B).2
    · intro hx
      exact ⟨e2 ⟨x, hx⟩, by simp⟩
  refine ⟨MonoidHom.noncommCoprod _ _ hcomm, fun A B => rfl, ?_⟩
  rw [MonoidHom.noncommCoprod_range, hr1, hr2]

theorem aqt_card_sl23 : Nat.card SL23 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem aqt_ker_iff {K1 K2 : Subgroup G} (e1 : ↥K1 ≃* SL23) (e2 : ↥K2 ≃* SL23)
    (hcard : Nat.card ↥(K1 ⊔ K2) = 288) {Ψ : SL23 × SL23 →* G}
    (hΨ : ∀ A B : SL23, Ψ (A, B) = (e1.symm A : G) * (e2.symm B : G))
    (hrange : Ψ.range = K1 ⊔ K2) (A B : SL23) :
    Ψ (A, B) = 1 ↔ (A = 1 ∧ B = 1) ∨ (A = -1 ∧ B = -1) := by
  have hker : Nat.card Ψ.ker = 2 := by
    have h1 := Ψ.ker.card_mul_index
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card Ψ.range = 288 := by rw [hrange]; exact hcard
    have h3 : Nat.card (SL23 × SL23) = 576 := by rw [Nat.card_prod, aqt_card_sl23]
    rw [h2, h3] at h1
    omega
  have hL : ∀ A : SL23, Ψ (A, 1) = 1 → A = 1 := by
    intro A h
    rw [hΨ, map_one, Subgroup.coe_one, mul_one] at h
    exact e1.symm.injective ((Subtype.ext h).trans (map_one e1.symm).symm)
  have hR : ∀ B : SL23, Ψ (1, B) = 1 → B = 1 := by
    intro B h
    rw [hΨ, map_one, Subgroup.coe_one, one_mul] at h
    exact e2.symm.injective ((Subtype.ext h).trans (map_one e2.symm).symm)
  have hneg : (-1 : SL23) ≠ 1 := by decide
  have key : ∀ u : SL23 × SL23, Ψ u = 1 → u ≠ 1 → u = (-1, -1) := by
    intro u hu hu1
    have hord : orderOf u ∣ 2 := by
      have h := Subgroup.orderOf_dvd_natCard Ψ.ker (show u ∈ Ψ.ker from hu)
      rwa [hker] at h
    have hsq : u * u = 1 := by
      have h := orderOf_dvd_iff_pow_eq_one.mp hord
      simpa [pow_two] using h
    obtain ⟨s, t⟩ := u
    have hs : s * s = 1 := by simpa using congrArg Prod.fst hsq
    have ht : t * t = 1 := by simpa using congrArg Prod.snd hsq
    rcases sl23_unique_involution s hs with rfl | rfl <;>
      rcases sl23_unique_involution t ht with rfl | rfl
    · exact absurd rfl hu1
    · exact absurd (hR _ hu) hneg
    · exact absurd (hL _ hu) hneg
    · rfl
  constructor
  · intro h
    by_cases hu1 : (A, B) = 1
    · exact Or.inl (Prod.mk_eq_one.mp hu1)
    · right
      have h' := key (A, B) h hu1
      exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact map_one Ψ
    · haveI : Nontrivial ↥Ψ.ker := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨⟨u, hu⟩, hne⟩ := exists_ne (1 : ↥Ψ.ker)
      have hu1 : u ≠ 1 := fun h => hne (Subtype.ext h)
      have h := key u hu hu1
      rw [h] at hu
      exact hu

end CFSG.OddStandard.SmallF3.Omega
