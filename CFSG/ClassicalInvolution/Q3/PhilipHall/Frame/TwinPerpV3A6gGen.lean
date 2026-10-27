module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ePkg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e (aeBar8 E8Pkg)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1
  (ae6Img mem_ae6Img ae6Img_mono ae6Img_le_iff ae6Img_inj card_ae6Img ae6Img_self ae6Img_le_range
    ae6Img_conjSub)

section Preim

variable {Y : Type} [Group Y] {I D : Subgroup Y} (P : E8Pkg I D)

@[expose] def preim (X : Subgroup (AEQ 8)) : Subgroup Y := (X.comap P.φ).map I.subtype

theorem mem_preim {X : Subgroup (AEQ 8)} {g : Y} : g ∈ preim P X ↔ ∃ hg : g ∈ I, P.φ ⟨g, hg⟩ ∈ X := by
  constructor
  · rintro ⟨⟨g', hg'⟩, hx, rfl⟩
    exact ⟨hg', hx⟩
  · rintro ⟨hg, hx⟩
    exact ⟨⟨g, hg⟩, hx, rfl⟩

theorem preim_le_I (X : Subgroup (AEQ 8)) : preim P X ≤ I := by
  rintro g hg
  exact (mem_preim P |>.mp hg).1

theorem preim_mono {X X' : Subgroup (AEQ 8)} (h : X ≤ X') : preim P X ≤ preim P X' := by
  intro g hg
  obtain ⟨hgI, hx⟩ := (mem_preim P).mp hg
  exact (mem_preim P).mpr ⟨hgI, h hx⟩

theorem mem_preim_of_mem {X : Subgroup (AEQ 8)} {g : Y} (hg : g ∈ I) (h : P.φ ⟨g, hg⟩ ∈ X) :
    g ∈ preim P X := (mem_preim P).mpr ⟨hg, h⟩

theorem ae6Img_preim {X : Subgroup (AEQ 8)} (hX : X ≤ aeBar8) : ae6Img P.φ (preim P X) = X := by
  ext e
  rw [mem_ae6Img]
  constructor
  · rintro ⟨g, hg, hgX, rfl⟩
    exact ((mem_preim P).mp hgX).2
  · intro he
    have : e ∈ P.φ.range := P.range_eq ▸ hX he
    obtain ⟨⟨g, hg⟩, rfl⟩ := this
    exact ⟨g, hg, mem_preim_of_mem P hg he, rfl⟩

theorem preim_inj {X X' : Subgroup (AEQ 8)} (hX : X ≤ aeBar8) (hX' : X' ≤ aeBar8)
    (h : preim P X = preim P X') : X = X' := by
  rw [← ae6Img_preim P hX, ← ae6Img_preim P hX', h]

theorem card_preim {X : Subgroup (AEQ 8)} (hX : X ≤ aeBar8) : Nat.card (preim P X) = Nat.card X := by
  rw [← card_ae6Img P.inj (preim_le_I P X), ae6Img_preim P hX]

end Preim

theorem not_sup_eq_of_isPGroup_seven {G : Type*} [Group G] [Finite G] {V E Q : Subgroup G}
    (hEV : E ≤ V) (hQV : Q ≤ V) (hQN : V ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsPGroup 2 ↥Q)
    (hcard : Nat.card V = 7 * Nat.card E) : E ⊔ Q ≠ V := by
  intro hsup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLE : E ≤ Subgroup.normalizer (Q : Set G) := hEV.trans hQN
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  have he : Q.relIndex E = Q.relIndex (E ⊔ Q) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient E Q hLE).toEquiv
  rw [hsup] at he
  have h1 := Subgroup.relIndex_mul_card Q E
  have h2 := Subgroup.relIndex_mul_card Q V
  rw [inf_eq_left.mpr hQV, ← he] at h2
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have h3 : Nat.card ↥Q = 7 * Nat.card ↥(Q ⊓ E) := by
    have hr : 0 < Q.relIndex E := by
      rcases Nat.eq_zero_or_pos (Q.relIndex E) with h0 | h0
      · rw [h0, zero_mul] at h2
        exact absurd h2.symm Nat.card_pos.ne'
      · exact h0
    apply Nat.eq_of_mul_eq_mul_left hr
    rw [h2, hcard, ← h1]
    ring
  have h4 : 7 ∣ 2 ^ k := hk ▸ h3 ▸ Dvd.dvd.mul_right (by norm_num : 7 ∣ 7) _
  have h5 := (by norm_num : Nat.Prime 7).dvd_of_dvd_pow h4
  omega

theorem le_of_normal_isPGroup_index_seven {G : Type*} [Group G] [Finite G] {V E Q : Subgroup G}
    (hEV : E ≤ V) (hQV : Q ≤ V) (hQN : V ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsPGroup 2 ↥Q)
    (hcard : Nat.card V = 7 * Nat.card E) : Q ≤ E := by
  have hS : E ⊔ Q ≤ V := sup_le hEV hQV
  have hpos : 0 < Nat.card E := Nat.card_pos
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le (le_sup_left : E ≤ E ⊔ Q)
  have hdvd : Nat.card (E ⊔ Q : Subgroup G) ∣ Nat.card V := Subgroup.card_dvd_of_le hS
  rw [hc, hcard, mul_comm (Nat.card E) c] at hdvd
  have hc7 : c ∣ 7 := Nat.dvd_of_mul_dvd_mul_right hpos hdvd
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hc7 with h1 | h7
  · have : E ⊔ Q = E := by
      refine (Subgroup.eq_of_le_of_card_ge (le_sup_left : E ≤ E ⊔ Q) ?_).symm
      rw [hc, h1, mul_one]
    exact this ▸ le_sup_right
  · exfalso
    refine not_sup_eq_of_isPGroup_seven hEV hQV hQN hQ hcard ?_
    refine Subgroup.eq_of_le_of_card_ge hS ?_
    rw [hc, h7, hcard]
    exact le_of_eq (mul_comm _ _)

theorem eq_of_four {G : Type*} [Group G] [Finite G] {F : Subgroup G} {a b c d : G}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) (hd : d ∈ F) (hcard : Nat.card F ≤ 4) :
    ∀ z ∈ F, z = a ∨ z = b ∨ z = c ∨ z = d := by
  classical
  have hsub : (({a, b, c, d} : Finset G) : Set G) ⊆ (F : Set G) := by
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have hS : ({a, b, c, d} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
  have hcard' : (F : Set G).ncard ≤ ((({a, b, c, d} : Finset G)) : Set G).ncard := by
    rw [Set.ncard_coe_finset, hS, ← Nat.card_coe_set_eq]
    exact hcard
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard' (Set.toFinite _)
  intro z hz
  have : z ∈ (({a, b, c, d} : Finset G) : Set G) := heq ▸ hz
  simpa using this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
