module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAltCover
public import CFSG.GH74.E2.ComponentsShape

public section

namespace CFSG.ComponentClassification.HarrisLit.L33

open CFSG Subgroup Equiv

theorem not_isPGroup_alt {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 8 ≤ n)
    (e : Y ≃* alternatingGroup (Fin n)) (a : MulAut Y) (ha : orderOf a = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) := by
  have hbij :=
    GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n (by omega) (by omega)
  set κ : MulAut (alternatingGroup (Fin n)) := MulAut.congr e a with hκ
  obtain ⟨π, hπ⟩ := hbij.2 κ
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hππ : π * π = 1 := hbij.1 (by rw [map_mul, hπ, hκ, ← map_mul, haa, map_one, map_one])
  have hfix : ∀ z : alternatingGroup (Fin n), π * (z : Perm (Fin n)) = z * π →
      e.symm z ∈ fixedPoints a := by
    intro z hz
    rw [mem_fixedPoints]
    have h1 : κ z = z := by
      rw [← hπ]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hz, mul_inv_cancel_right]
    have h2 : e (a (e.symm z)) = z := h1
    calc a (e.symm z) = e.symm (e (a (e.symm z))) := (e.symm_apply_apply _).symm
      _ = e.symm z := by rw [h2]
  obtain ⟨y, v, hy, hv, hπy, hπv, hy3, hc2, hc1⟩ := AltCover.exists_witness hn π hππ
  set y' : alternatingGroup (Fin n) := ⟨y, hy⟩ with hy'
  set v' : alternatingGroup (Fin n) := ⟨v, hv⟩ with hv'
  have hy'3 : y' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hy3)
  have hw3 : (v' * y'⁻¹ * v'⁻¹) ^ 3 = 1 := by
    rw [conj_pow, inv_pow, hy'3, inv_one, mul_one, mul_inv_cancel]
  have hπw : π * ((v' * y'⁻¹ * v'⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) =
      ((v' * y'⁻¹ * v'⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) * π := by
    have hc : Commute π (v * y⁻¹ * v⁻¹) :=
      ((Commute.mul_right hπv (Commute.inv_right hπy)).mul_right (Commute.inv_right hπv))
    exact hc
  have hodd : ∀ z : alternatingGroup (Fin n), z ^ 3 = 1 → Odd (orderOf (e.symm z)) := by
    intro z hz
    rw [MulEquiv.orderOf_eq]
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hz)
  refine not_isPGroup_of_closure_odd (T := {e.symm y', e.symm (v' * y'⁻¹ * v'⁻¹)}) ?_ ?_ ?_
  · intro t ht
    rcases ht with rfl | rfl
    · exact hfix y' hπy
    · exact hfix _ hπw
  · intro t ht
    rcases ht with rfl | rfl
    · exact hodd y' hy'3
    · exact hodd _ hw3
  · have hmem : e.symm y' * e.symm (v' * y'⁻¹ * v'⁻¹) ∈
        closure ({e.symm y', e.symm (v' * y'⁻¹ * v'⁻¹)} : Set Y) :=
      mul_mem (subset_closure (Set.mem_insert _ _))
        (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hord : orderOf (e.symm y' * e.symm (v' * y'⁻¹ * v'⁻¹)) = 2 := by
      rw [← map_mul, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      have h1 : ((y' * (v' * y'⁻¹ * v'⁻¹) : alternatingGroup (Fin n)) : Perm (Fin n)) =
          y * v * y⁻¹ * v⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy', hv', mul_assoc]
      rw [h1]
      exact orderOf_eq_prime hc2 hc1
    have := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [hord] at this

theorem twoNilpFor_alt :
    TwoNilpFor fun Y _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (Y ≃* alternatingGroup (Fin n)) := by
  intro Y _ _ hY _ _ a ha hP
  obtain ⟨n, hn, ⟨e⟩⟩ := hY
  by_cases h8 : 8 ≤ n
  · exact absurd hP (not_isPGroup_alt h8 e a ha)
  · interval_cases n
    · exact Or.inl ⟨5, 1, GH74.E2.lieModel_psl_two_five_of_alt ⟨e⟩⟩
    · exact Or.inl ⟨3, 2, GH74.E2.lieModel_psl_two_nine_of_alt_six ⟨e⟩⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))

end CFSG.ComponentClassification.HarrisLit.L33
