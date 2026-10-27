module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabNorm

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

theorem qTwo_normQuad_eq_one (hK : Nat.card K = 4) {a : K} (ha : a ≠ 0) :
    normQuad E a = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hpow : a ^ 3 = 1 := by
    simpa [← Nat.card_eq_fintype_card, hK] using
      FiniteField.pow_card_sub_one_eq_one a ha
  apply (algebraMap F K).injective
  rw [algebraMap_normQuad, map_one, unitaryInvolution_apply]
  simpa [pow_succ, mul_comm] using hpow

theorem qTwo_Qn_two_eq_one_iff (hK : Nat.card K = 4) (v : Fin 2 → K) :
    Qn E 2 v = 1 ↔ (v 0 ≠ 0 ∧ v 1 = 0) ∨ (v 0 = 0 ∧ v 1 ≠ 0) := by
  letI : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  rw [Qn_apply, Fin.sum_univ_two]
  by_cases h0 : v 0 = 0 <;> by_cases h1 : v 1 = 0
  · simp [h0, h1]
  · simp [h0, h1]
    exact qTwo_normQuad_eq_one E hK h1
  · simp [h0, h1]
    exact qTwo_normQuad_eq_one E hK h0
  · rw [qTwo_normQuad_eq_one E hK h0, qTwo_normQuad_eq_one E hK h1]
    have htwo : (1 : F) + 1 = 0 := by
      calc (1 : F) + 1 = 2 := by norm_num
           _ = 0 := CharP.cast_eq_zero F 2
    simp [h0, h1, htwo]

theorem qTwo_same_axis_of_Qn_add_eq_one (hK : Nat.card K = 4) {u v : Fin 2 → K}
    (hu : Qn E 2 u = 1) (hv : Qn E 2 v = 1) (huv : Qn E 2 (u + v) = 1) :
    (u 0 = 0 ↔ v 0 = 0) ∧ (u 1 = 0 ↔ v 1 = 0) := by
  rw [qTwo_Qn_two_eq_one_iff E hK] at hu hv huv
  simp only [Pi.add_apply] at huv
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> simp_all

theorem qTwo_axis_image_zero (hK : Nat.card K = 4)
    {g : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E 2)) (i j : Fin 2)
    (hij : g (Pi.single i 1) j = 0) (a : K) : g (Pi.single i a) j = 0 := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases ha1 : a = 1
  · simpa [ha1] using hij
  have htwo : (1 : K) + 1 = 0 := by
    calc (1 : K) + 1 = 2 := by norm_num
         _ = 0 := CharP.cast_eq_zero K 2
  have haadd : a + 1 ≠ 0 := by
    intro h
    exact ha1 (add_right_cancel (h.trans htwo.symm))
  have hsingle (b : K) : Qn E 2 (Pi.single i b) = normQuad E b := by
    fin_cases i <;> simp [Qn_apply, Fin.sum_univ_two]
  have hnorm (b : K) (hb : b ≠ 0) : Qn E 2 (g (Pi.single i b)) = 1 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg, hsingle]
    exact qTwo_normQuad_eq_one E hK hb
  have hsum := hnorm (a + 1) haadd
  rw [Pi.single_add, map_add] at hsum
  have haxis := qTwo_same_axis_of_Qn_add_eq_one E hK (hnorm a ha) (hnorm 1 one_ne_zero) hsum
  fin_cases j
  · exact haxis.1.mpr hij
  · exact haxis.2.mpr hij

theorem qTwo_isometry_permutes_axes (hK : Nat.card K = 4)
    {g : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E 2)) :
    ((∀ a : K, g (Pi.single 0 a) 1 = 0) ∧ (∀ a : K, g (Pi.single 1 a) 0 = 0)) ∨
      ((∀ a : K, g (Pi.single 0 a) 0 = 0) ∧ (∀ a : K, g (Pi.single 1 a) 1 = 0)) := by
  have hnorm (i : Fin 2) : Qn E 2 (g (Pi.single i 1)) = 1 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg, Qn_single_one]
  have hnot (j : Fin 2) (h0 : g (Pi.single 0 1) j = 0)
      (h1 : g (Pi.single 1 1) j = 0) : False := by
    obtain ⟨w, hw⟩ := g.surjective (Pi.single j 1)
    have hsplit : w = Pi.single 0 (w 0) + Pi.single 1 (w 1) := by
      ext i
      fin_cases i <;> simp
    have hzero : g w j = 0 := by
      rw [hsplit, map_add, Pi.add_apply,
        qTwo_axis_image_zero E hK hg 0 j h0,
        qTwo_axis_image_zero E hK hg 1 j h1, zero_add]
    rw [hw, Pi.single_eq_same] at hzero
    exact one_ne_zero hzero
  rcases (qTwo_Qn_two_eq_one_iff E hK _).mp (hnorm 0) with h0 | h0 <;>
    rcases (qTwo_Qn_two_eq_one_iff E hK _).mp (hnorm 1) with h1 | h1
  · exact (hnot 1 h0.2 h1.2).elim
  · exact Or.inl ⟨qTwo_axis_image_zero E hK hg 0 1 h0.2,
      qTwo_axis_image_zero E hK hg 1 0 h1.1⟩
  · exact Or.inr ⟨qTwo_axis_image_zero E hK hg 0 0 h0.1,
      qTwo_axis_image_zero E hK hg 1 1 h1.2⟩
  · exact (hnot 0 h0.1 h1.1).elim

theorem qTwo_axis_preserving_form
    {g : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E 2))
    (h0 : ∀ a : K, g (Pi.single 0 a) 1 = 0)
    (h1 : ∀ a : K, g (Pi.single 1 a) 0 = 0) :
    ∃ u v : K, u * unitaryInvolution K 2 1 u = 1 ∧
      v * unitaryInvolution K 2 1 v = 1 ∧
      ((∀ x, g x 0 = u * x 0) ∨ (∀ x, g x 0 = u * unitaryInvolution K 2 1 (x 0))) ∧
      ((∀ x, g x 1 = v * x 1) ∨ (∀ x, g x 1 = v * unitaryInvolution K 2 1 (x 1))) := by
  let f0 : K →ₗ[F] K := (LinearMap.proj 0).comp
    (g.toLinearMap.comp (LinearMap.single F (fun _ : Fin 2 => K) 0))
  let f1 : K →ₗ[F] K := (LinearMap.proj 1).comp
    (g.toLinearMap.comp (LinearMap.single F (fun _ : Fin 2 => K) 1))
  have hN0 (a : K) : normQuad E (f0 a) = normQuad E a := by
    have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg (Pi.single 0 a)
    simpa [Qn_apply, Fin.sum_univ_two, h0, f0] using h
  have hN1 (a : K) : normQuad E (f1 a) = normQuad E a := by
    have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg (Pi.single 1 a)
    simpa [Qn_apply, Fin.sum_univ_two, h1, f1] using h
  have hcoord (x : Fin 2 → K) : g x 0 = f0 (x 0) ∧ g x 1 = f1 (x 1) := by
    have hsplit : x = Pi.single 0 (x 0) + Pi.single 1 (x 1) := by
      ext i
      fin_cases i <;> simp
    have hgx := congrArg g hsplit
    rw [map_add] at hgx
    constructor
    · simpa [f0, h1] using congrFun hgx 0
    · simpa [f1, h0] using congrFun hgx 1
  obtain ⟨u, hu, hfu⟩ := normQuad_preserver_eq_mul_or_mul_bar E f0 hN0
  obtain ⟨v, hv, hfv⟩ := normQuad_preserver_eq_mul_or_mul_bar E f1 hN1
  refine ⟨u, v, hu, hv, ?_, ?_⟩
  · rcases hfu with h | h
    · exact Or.inl fun x => (hcoord x).1.trans (h (x 0))
    · exact Or.inr fun x => (hcoord x).1.trans (h (x 0))
  · rcases hfv with h | h
    · exact Or.inl fun x => (hcoord x).2.trans (h (x 1))
    · exact Or.inr fun x => (hcoord x).2.trans (h (x 1))

end CFSG.ClassicalInvolution.PhanDn.QTwo
