module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Lift
public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataSylow

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup CFSG.Open

variable {n : ℕ} {K : Type} [Group K]

theorem CoverSetup.isElemAbelian_comap_iso (C : CoverSetup n K) (hn : 8 ≤ n)
    {E : Subgroup (Perm (Fin n))}
    (hE : ∀ σ ∈ E, σ = 1 ∨ (σ * σ = 1 ∧ 8 ∣ σ.support.card)) :
    IsElemAbelian 2 (E.comap C.ρ) := by
  refine isElemAbelian_of_sq fun e he => ?_
  rcases hE _ he with h1 | ⟨h2, h8⟩
  · exact C.sq_of_mem_center ((C.ρ_eq_one_iff).1 h1)
  · exact (C.sq_eq_one_iff_dvd hn h2).2 h8

theorem CoverSetup.isElemAbelian_comap_pairSub (C : CoverSetup n K) (hn : 8 ≤ n)
    {a : Perm (Fin n)} (ha : a * a = 1) (h8 : 8 ∣ a.support.card) :
    IsElemAbelian 2 ((pairSub a ha).comap C.ρ) :=
  C.isElemAbelian_comap_iso hn fun σ hσ => by
    rcases hσ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨ha, h8⟩

theorem CoverSetup.card_comap_pairSub (C : CoverSetup n K) {a : Perm (Fin n)} (ha : a * a = 1)
    (ha1 : a ≠ 1) (hs : sign a = 1) : Nat.card ((pairSub a ha).comap C.ρ) = 4 := by
  have hle : pairSub a ha ≤ alternatingGroup (Fin n) := by
    rintro σ (rfl | rfl)
    · exact one_mem _
    · exact Perm.mem_alternatingGroup.2 hs
  rw [C.card_comap hle, card_pairSub ha ha1]

theorem CoverSetup.two_le_pRank_comap_pairSub [Finite K] (C : CoverSetup n K) (hn : 8 ≤ n)
    {a : Perm (Fin n)} (ha : a * a = 1) (ha1 : a ≠ 1) (hs : sign a = 1) (h8 : 8 ∣ a.support.card) :
    2 ≤ Open.pRank 2 ((pairSub a ha).comap C.ρ) :=
  CFSG.SectionRank.le_pRank (k := 2) (by norm_num) le_rfl (C.isElemAbelian_comap_pairSub hn ha h8)
    (by rw [C.card_comap_pairSub ha ha1 hs]; norm_num)

theorem CoverSetup.mem_normalizer_comap_pairSub (C : CoverSetup n K) {a : Perm (Fin n)}
    (ha : a * a = 1) {x : K} (hx : C.ρ x * a = a * C.ρ x) :
    x ∈ normalizer (((pairSub a ha).comap C.ρ : Subgroup K) : Set K) := by
  rw [mem_normalizer_iff]
  intro y
  have hconj : ∀ q : Perm (Fin n), (q = 1 ∨ q = a) ↔
      (C.ρ x * q * (C.ρ x)⁻¹ = 1 ∨ C.ρ x * q * (C.ρ x)⁻¹ = a) := by
    intro q
    constructor
    · rintro (rfl | rfl)
      · left; group
      · right
        calc C.ρ x * q * (C.ρ x)⁻¹ = (C.ρ x * q) * (C.ρ x)⁻¹ := rfl
          _ = (q * C.ρ x) * (C.ρ x)⁻¹ := by rw [hx]
          _ = q := by group
    · rintro (h | h)
      · left
        have : q = (C.ρ x)⁻¹ * (C.ρ x * q * (C.ρ x)⁻¹) * C.ρ x := by group
        rw [this, h]
        group
      · right
        have : q = (C.ρ x)⁻¹ * (C.ρ x * q * (C.ρ x)⁻¹) * C.ρ x := by group
        rw [this, h]
        calc (C.ρ x)⁻¹ * a * C.ρ x = (C.ρ x)⁻¹ * (a * C.ρ x) := by group
          _ = (C.ρ x)⁻¹ * (C.ρ x * a) := by rw [hx]
          _ = a := by group
  show (C.ρ y = 1 ∨ C.ρ y = a) ↔ (C.ρ (x * y * x⁻¹) = 1 ∨ C.ρ (x * y * x⁻¹) = a)
  rw [map_mul, map_mul, map_inv]
  exact hconj _

theorem CoverSetup.exists_involution_of_two_le_pRank [Finite K] (C : CoverSetup n K)
    (hn : 8 ≤ n) {T : Subgroup K} (hT : 2 ≤ Open.pRank 2 T) :
    ∃ x ∈ T, C.ρ x ≠ 1 ∧ C.ρ x * C.ρ x = 1 ∧ 8 ∣ (C.ρ x).support.card := by
  obtain ⟨E, hET, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hT
  have h4 : 4 ≤ Nat.card E := by rw [hcard]; norm_num
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, C.ρ x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ center K := fun x hx => (C.ρ_eq_one_iff).1 (hcon x hx)
    have := Subgroup.card_le_of_le hle
    rw [C.center_card] at this
    omega
  have hsq : x * x = 1 := by rw [← pow_two]; exact hE.2 x hxE
  have hρ2 : C.ρ x * C.ρ x = 1 := by rw [← map_mul, hsq, map_one]
  exact ⟨x, hET hxE, hx1, hρ2, (C.sq_eq_one_iff_dvd hn hρ2).1 hsq⟩

end CFSG.OddStandard.Solomon75.AhatData
