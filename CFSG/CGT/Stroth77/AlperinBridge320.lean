module

public import CFSG.CGT.Stroth77.AlperinBridge

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.ONan76

@[expose] def type320Basis (G : ℤ) : IntMat :=
  ofCols ![1, 0, 1] ![2176 * G ^ 2 + 10040 * G + 11579, -56 * G - 131, -16 * G - 37]
    ![-437760 * G ^ 3 - 3044160 * G ^ 2 - 7055976 * G - 5451359,
      8832 * G ^ 2 + 41176 * G + 47991, 5568 * G ^ 2 + 26024 * G + 30408]

theorem matEq_s_type320 {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (Type320.k m) (Type320.uM F * Type320.tM i F G * type320Basis G)
      (type320Basis G * alpS) := by
  have hs := Type32x.dvd_three_mul_add_seven h
  obtain ⟨-, hi, hF, -, -⟩ := h
  subst hi hF
  refine MatEq.of_dvd (3 * G + 7) hs (P := !![0, 0, 27996160 * G ^ 3 + 194785280 * G ^ 2 +
    451718336 * G + 349166808; 0, 0, -584192 * G ^ 2 - 2727808 * G - 3184248; 0, 0,
    -340480 * G ^ 2 - 1591616 * G - 1860016]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff, Type320.tM, Type320.uM,
      Type320.ρM, Type320.uvA, uMat, ofCols_apply, alpS, type320Basis, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct] <;> ring1

theorem matEq_u_type320 {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    MatEq (Type320.k m) (Type320.uM F * type320Basis G) (type320Basis G * alpT) := by
  have hs := Type32x.dvd_three_mul_add_seven h
  obtain ⟨-, hi, hF, -, -⟩ := h
  subst hi hF
  refine MatEq.of_dvd (3 * G + 7) hs (P := !![-145920 * G ^ 2 - 674240 * G - 778776,
    768 * G + 1728, -7680 * G ^ 2 - 29760 * G - 27624; 2944 * G + 6856, -24, 1856 * G + 4344;
    1856 * G + 4344, -24, 2944 * G + 6856]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff, Type320.uM, uMat,
      ofCols_apply, alpT, type320Basis, Matrix.mul_apply, Fin.sum_univ_three] <;> ring1

theorem odd_det_type320Basis (G : ℤ) : Odd (Matrix.det (type320Basis G)) := by
  refine ⟨-2648064 * G ^ 4 - 24858880 * G ^ 3 - 87509792 * G ^ 2 - 136911520 * G - 80324011, ?_⟩
  rw [Matrix.det_fin_three]
  simp [type320Basis, ofCols_apply]
  ring

variable {G : Type} [Group G] {D : Subgroup G} {uv t u : G}

theorem exists_alperinFrame_of_type320 {m : ℕ} (hm : 3 ≤ m)
    (e : Additive D ≃+ Torus (Type320.k m))
    (ht : t ∈ Subgroup.normalizer (D : Set G)) (hu : u ∈ Subgroup.normalizer (D : Set G))
    (ht_conj : ∀ x : D,
      e (Additive.ofMul (conjBy ht x)) = (Type320.actionPaper m hm).φt (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D,
      e (Additive.ofMul (conjBy hu x)) = (Type320.actionPaper m hm).φu (e (Additive.ofMul x)))
    (ht2 : t * t = 1) (hu2 : u * u = 1) (huv2 : uv * uv = 1) (htu : t * u = u * uv * t) :
    ∃ v₁ v₂ v₃ s r : G, AlperinFrame m v₁ v₂ v₃ s r ∧ s ^ 4 = 1 ∧
      Subgroup.closure ({v₁, v₂, v₃, s, r} : Set G) = D ⊔ Subgroup.closure {uv, t, u} := by
  have hk : ∀ i, Type320.k m i = m := fun i => by fin_cases i <;> rfl
  have hdata := Type32x.data m (Nat.le_trans (by norm_num) hm)
  exact exists_alperinFrame_of_matEq hk e
    (Mt := Type320.tM (Type120.iV m) (Type120.FV m) (Type120.GV m))
    (Mu := Type320.uM (Type120.FV m)) ht hu ht_conj hu_conj ht2 hu2 huv2 htu
    (matEq_s_type320 hdata) (matEq_u_type320 hdata) (odd_det_type320Basis _)

end CFSG.CGT.Stroth77
