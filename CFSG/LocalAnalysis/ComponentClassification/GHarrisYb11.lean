module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb10

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem SCert.SE.ut_sq_of_b : ∀ u : UT3 F4c, u.b = 0 → u * u = 1 := by decide +kernel

theorem SCert.SE.ut_comm_of_b : ∀ u v : UT3 F4c, u.b = 0 → v.b = 0 → u * v = v * u := by
  decide +kernel

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

theorem Et_sq (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    ∀ e ∈ D.Et, e * e = 1 := by
  intro e he
  have heT := D.Et_le hO hz he
  have h := (D.mem_Et_iff_tUT hO hz heT).mp he
  have h2 : D.tUT hO hz (⟨e, heT⟩ * ⟨e, heT⟩) = 1 := by
    rw [map_mul]
    exact SE.ut_sq_of_b _ h
  exact congrArg Subtype.val ((D.tUT hO hz).injective (h2.trans (map_one _).symm))

theorem Et_comm (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    ∀ e ∈ D.Et, ∀ f ∈ D.Et, e * f = f * e := by
  intro e he f hf
  have heT := D.Et_le hO hz he
  have hfT := D.Et_le hO hz hf
  have h1 := (D.mem_Et_iff_tUT hO hz heT).mp he
  have h2 := (D.mem_Et_iff_tUT hO hz hfT).mp hf
  have h3 : D.tUT hO hz (⟨e, heT⟩ * ⟨f, hfT⟩) = D.tUT hO hz (⟨f, hfT⟩ * ⟨e, heT⟩) := by
    rw [map_mul, map_mul]
    exact SE.ut_comm_of_b _ _ h1 h2
  exact congrArg Subtype.val ((D.tUT hO hz).injective h3)

theorem prop38_Xt
    (hC : GorensteinHaradaThmCInput) (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) :
    letI : (pCore 2 D.Xt).Normal := pCore_normal
    (pCore 2 D.Xt = ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) ∧
        (((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt).index = 1 ∨
          ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt).index = 3) ∧
        D.Et.Normal ∧ D.Ft.Normal ∧
        centralizer (((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) : Set D.Xt) ≤
          ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) ∨
      (pCore 2 D.Xt = D.Et ∧ centralizer (D.Et : Set D.Xt) ≤ D.Et ∧
        Nonempty (D.Xt ⧸ pCore 2 D.Xt ≃* alternatingGroup (Fin 5)) ∧
        ∀ u ∈ D.Et, ∀ v ∈ D.Et, u ≠ 1 → v ≠ 1 → ∃ g : D.Xt, g⁻¹ * u * g = v) := by
  let _ : (pCore 2 D.Xt).Normal := pCore_normal
  obtain ⟨hC0, hcase⟩ := D.thmC_Xt hC hO hz
  rcases hcase with ⟨hT, hidx, hnorm⟩ | ⟨hle, h16, h2, hc, hiso, htr⟩
  · left
    have hE : D.Et.Normal := hnorm D.Et (D.Et_le hO hz) (D.Et_sq hO hz) (D.Et_comm hO hz)
      (D.card_Et_Ft hO hz).1
    have hF : D.Ft.Normal := hnorm D.Ft (D.Ft_le hO hz) (D.Ft_sq hO hz) (D.Ft_comm hO hz)
      (D.card_Et_Ft hO hz).2
    have hCT : centralizer (((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) : Set D.Xt) ≤
        ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) := by
      rw [← hT]
      exact hC0
    refine ⟨hT, ?_, hE, hF, hCT⟩
    have h9 := D.index_ne_nine hO hz hE hF hCT
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt).index ∣ 3 ^ 2 from hidx)
    interval_cases k
    · exact Or.inl hk'
    · exact Or.inr hk'
    · exact absurd hk' h9
  · right
    have hEt := D.pCore_eq_Et hO hz hle h16 h2 hc htr
    refine ⟨hEt, ?_, ?_, ?_⟩
    · rw [← hEt]
      exact hC0
    · rcases hiso with h | h
      · exact h
      · obtain ⟨e⟩ := h
        exact ((D.not_iso_Z3A5 hO hz hEt hC0).false e).elim
    · rw [← hEt]
      exact htr

end GHSylow

end CFSG.ComponentClassification.GHarris
