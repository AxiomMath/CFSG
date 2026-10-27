module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2PairOrd
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Tr2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG L2Ord L2Dick

section Step

variable {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Module.Finite (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ}
  {K : Subgroup Γ} {a : Γ}


theorem l2_trace_contra (hf : Hyp89 p ρ K a) {r f : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (hrp : r ≠ p) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = r ^ f)
    (e0 : (↥K ⧸ center ↥K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀)
    {y : ↥K ⧸ center ↥K} (hy : bAutN K a hf.norm = MulAut.conj y)
    (hno : ∀ E : Subgroup (↥K ⧸ center ↥K), IsPGroup r ↥E →
      (∀ x ∈ E, bAutN K a hf.norm x ∈ E) → E = ⊥)
    (hp35 : p = 3 ∨ p = 5) (hy1 : e0 y ≠ 1) (hyp : (e0 y) ^ p = 1) (t : F₀)
    (hbad : ∀ Mh : Matrix.SpecialLinearGroup (Fin 2) F₀,
      (QuotientGroup.mk Mh : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀) = e0 y →
        ordPoly (2 + t ^ 2) ≠ 0 ∨
          ordPoly ((Mh : Matrix (Fin 2) (Fin 2) F₀).trace ^ 2 - 2 - t ^ 2) ≠ 0) :
    False := by
  classical
  obtain ⟨G, Mh, hMh, htr1, htr2⟩ := exists_conj_traces (e0 y) hy1 t
  obtain ⟨k₁, hk₁⟩ := QuotientGroup.mk_surjective (e0.symm (QuotientGroup.mk G))
  have hk : (k₁ : Γ) ∈ K := k₁.2
  have hg : e0 (QuotientGroup.mk (⟨(k₁ : Γ), hk⟩ : ↥K)) = QuotientGroup.mk G := by
    show e0 (QuotientGroup.mk k₁) = _
    rw [hk₁, MulEquiv.apply_symm_apply]
  have hz1 : (QuotientGroup.mk (Mh⁻¹ * (G * Mh * G⁻¹)) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀) =
      (e0 y)⁻¹ * (QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹) := by
    rw [← hMh]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hz2 : (QuotientGroup.mk (Mh * (G * Mh * G⁻¹)) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀) =
      e0 y * (QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹) := by
    rw [← hMh]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hpk : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 5 := by omega
  have hpk' : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F₀, ∀ z : Matrix.ProjectiveSpecialLinearGroup
      (Fin 2) F₀, (QuotientGroup.mk M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀) = z →
      z ^ p = 1 → ordPoly (M : Matrix (Fin 2) (Fin 2) F₀).trace = 0 := by
    intro M z hz hzp
    refine ordPoly_of_psl_pow (by omega) ?_
    rw [hz]
    exact hzp
  by_cases hJ : IsPGroup p ↥(Subgroup.closure ({a, (k₁ : Γ) * a * (k₁ : Γ)⁻¹} : Set Γ))
  · have hc := pair_comm_of_pgroup hf hr2 hrp hF₀ e0 hy hk hJ
    rw [hg] at hc
    have hcomm : Commute (e0 y) (QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹) := hc
    have hw : (QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹ :
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀) ^ p = 1 := by
      rw [conj_pow, hyp, mul_one, mul_inv_cancel]
    rcases hbad Mh hMh with hb | hb
    · have hz : ((e0 y)⁻¹ * (QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹)) ^ p = 1 := by
        rw [hcomm.inv_left.mul_pow, inv_pow, hyp, inv_one, hw, mul_one]
      have := hpk' _ _ hz1 hz
      rw [htr1] at this
      exact hb this
    · have hz : (e0 y * (QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹)) ^ p = 1 := by
        rw [hcomm.mul_pow, hyp, hw, mul_one]
      have := hpk' _ _ hz2 hz
      rw [htr2] at this
      exact hb this
  · obtain ⟨-, -, -, -, -, -, -, hord, -⟩ := pair_orders hf hr2 hrp hF₀ e0 hy hno hk hJ
    rw [hg] at hord
    have hmem1 : (e0 y)⁻¹ * (QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹) ∈
        Subgroup.closure ({e0 y, QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹} :
          Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hmem2 : e0 y * (QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹) ∈
        Subgroup.closure ({e0 y, QuotientGroup.mk G * e0 y * (QuotientGroup.mk G)⁻¹} :
          Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀)) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    rcases hbad Mh hMh with hb | hb
    · apply hb
      rw [← htr1]
      rcases hord _ hmem1 with h | h | h
      · exact ordPoly_of_psl_pow (k := 2) (by simp) (by rw [hz1]; exact h)
      · exact ordPoly_of_psl_pow (k := 3) (by simp) (by rw [hz1]; exact h)
      · exact ordPoly_of_psl_pow (k := 5) (by simp) (by rw [hz1]; exact h)
    · apply hb
      rw [← htr2]
      rcases hord _ hmem2 with h | h | h
      · exact ordPoly_of_psl_pow (k := 2) (by simp) (by rw [hz2]; exact h)
      · exact ordPoly_of_psl_pow (k := 3) (by simp) (by rw [hz2]; exact h)
      · exact ordPoly_of_psl_pow (k := 5) (by simp) (by rw [hz2]; exact h)

end Step

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
