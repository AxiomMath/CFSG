module

public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig

open Subgroup CFSG CFSG.GH74.GLS CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

theorem comm_of_card_nine {X : Type*} [Group X] (E : Subgroup X) (hE : Nat.card E = 9) :
    ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
  intro a ha b hb
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : Nat.card E = 3 ^ 2 := by rw [hE]; norm_num
  have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq h9).is_comm.comm
  exact congrArg Subtype.val (this (⟨a, ha⟩ : E) ⟨b, hb⟩)

theorem card_centralizer_singleton_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (v : X) :
    Nat.card (centralizer ({φ v} : Set Y)) = Nat.card (centralizer ({v} : Set X)) := by
  refine Nat.card_congr
    { toFun := fun a => ⟨φ.symm a.1, ?_⟩
      invFun := fun a => ⟨φ a.1, ?_⟩
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun a => Subtype.ext (by simp) }
  · have h := mem_centralizer_singleton_iff.mp a.2
    rw [mem_centralizer_singleton_iff]
    apply φ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact h
  · have h := mem_centralizer_singleton_iff.mp a.2
    rw [mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, h]

theorem sSup_cores_eq {X : Type*} [Group X] [Finite X] (E K : Subgroup X)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEK : E ≤ normalizer (K : Set X))
    (hKle : K ≤ ⨆ (x : X) (_ : x ∈ E) (_ : x ≠ 1), pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set X))) :
    ∃ F : Set (Subgroup X), F ⊆ invariantPiSubgroups ⊤ E (piCompl 3) ∧
      (∀ Z ∈ F, ∃ x ∈ E, x ≠ 1 ∧ Z ≤ centralizer ({x} : Set X)) ∧ sSup F = K := by
  have hpi : ∀ Y : Subgroup X, IsPiSubgroup (piCompl 3) (pPrimeCoreOf 3 Y) := fun Y =>
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
         coprime_card_pPrimeCoreOf 3 Y))
  refine ⟨{Z | ∃ x ∈ E, x ≠ 1 ∧ Z = pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set X))}, ?_, ?_, ?_⟩
  · rintro Z ⟨x, hx, -, rfl⟩
    refine ⟨le_top, hpi _, fun e he => ?_⟩
    have hN : e ∈ normalizer ((K ⊓ centralizer ({x} : Set X) : Subgroup X) : Set X) := by
      rw [mem_normalizer_iff]
      intro h
      have hK := mem_normalizer_iff.mp (hEK he) h
      have hec : e * x = x * e := hcomm e he x hx
      have hex : e * x * e⁻¹ = x := by rw [hec]; group
      have hiff : h ∈ centralizer ({x} : Set X) ↔ e * h * e⁻¹ ∈ centralizer ({x} : Set X) := by
        rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
        have e1 : e * h * e⁻¹ * x = e * (h * x) * e⁻¹ := by
          calc e * h * e⁻¹ * x = e * h * e⁻¹ * (e * x * e⁻¹) := by rw [hex]
            _ = e * (h * x) * e⁻¹ := by group
        have e2 : x * (e * h * e⁻¹) = e * (x * h) * e⁻¹ := by
          calc x * (e * h * e⁻¹) = (e * x * e⁻¹) * (e * h * e⁻¹) := by rw [hex]
            _ = e * (x * h) * e⁻¹ := by group
        rw [e1, e2]
        constructor
        · intro hh; rw [hh]
        · intro hh
          have := mul_right_cancel hh
          exact mul_left_cancel this
      constructor
      · rintro ⟨hhK, hhC⟩
        exact ⟨hK.mp hhK, hiff.mp hhC⟩
      · rintro ⟨hhK, hhC⟩
        exact ⟨hK.mpr hhK, hiff.mpr hhC⟩
    exact normalizer_le_normalizer_pPrimeCoreOf 3 _ hN
  · rintro Z ⟨x, hx, hx1, rfl⟩
    exact ⟨x, hx, hx1, (pPrimeCoreOf_le 3 _).trans inf_le_right⟩
  · apply le_antisymm
    · refine sSup_le ?_
      rintro Z ⟨x, hx, -, rfl⟩
      exact (pPrimeCoreOf_le 3 _).trans inf_le_left
    · refine hKle.trans ?_
      refine iSup₂_le fun x hx => iSup_le fun hx1 => ?_
      exact le_sSup ⟨x, hx, hx1, rfl⟩

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig
