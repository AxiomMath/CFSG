module

public import CFSG.LieType.Universal.Unitary.BinaryModel.FixedLine
public import CFSG.LieType.SpecialLinear.ExteriorModel.Fundamental
public import CFSG.LieType.SpecialLinear.ExteriorModel.Reversal
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WittTransport
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.GraphSwitch
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.QuadraticDescent

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Module CFSG.Open CFSG.HardMathSupport.GuralnickMalle CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.SpecialLinear.ExteriorModel Matrix

section Minors

variable {k : Type} [Field k] {m : ℕ}

theorem minorMatrix_one_submatrix (g : Matrix (Fin m) (Fin m) k) :
    (minorMatrix 1 g).submatrix powersetCardOneEquiv.symm powersetCardOneEquiv.symm = g := by
  ext a b
  rw [submatrix_apply, minorMatrix, of_apply, minor_powersetCardOneEquiv_symm]

theorem minorMatrix_sub_one_submatrix [CharP k 2] (hm : 1 ≤ m) {g : Matrix (Fin m) (Fin m) k}
    (hg : g.det = 1) :
    (minorMatrix (m - 1) g).submatrix (powersetCardOneEquiv.symm.trans (complEquiv hm))
      (powersetCardOneEquiv.symm.trans (complEquiv hm)) = (g⁻¹)ᵀ := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hu : IsUnit g.det := by rw [hg]; exact isUnit_one
  have hdet : ((g⁻¹)ᵀ).det = 1 := by rw [det_transpose, det_nonsing_inv, hg, Ring.inverse_one]
  have hinv : (((g⁻¹)ᵀ)⁻¹)ᵀ = g := by
    rw [transpose_nonsing_inv, transpose_transpose, nonsing_inv_nonsing_inv _ hu]
  ext a b
  have h := minor_inv_transpose_compl h2 ((g⁻¹)ᵀ) hdet hm (powersetCardOneEquiv.symm a)
    (powersetCardOneEquiv.symm b)
  rw [hinv] at h
  rw [submatrix_apply, minorMatrix, of_apply, Equiv.trans_apply, Equiv.trans_apply, h,
    minor_powersetCardOneEquiv_symm]

end Minors

theorem mem_fixSubGen_iff_of_enum {G k V : Type*} [Group G] [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) {P : Subgroup G} {r : ℕ} {xs : Fin r → G}
    (hxs : ∀ i, xs i ∈ P) (hsurj : ∀ x ∈ P, ∃ i, xs i = x) (v : V) :
    v ∈ fixSubGen ρ P ↔ ∀ i, ρ (xs i) v = v := by
  refine ⟨fun hv i => hv _ (hxs i), fun h a ha => ?_⟩
  obtain ⟨i, rfl⟩ := hsurj a ha
  exact h i

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {k : Type} [Field k] [CharP k 2]

theorem finrank_matFix_minorMatrix_of_mem_SU (ψ : K →+* k) {m r : ℕ} (hm : 2 ≤ m)
    (g : Fin r → GL (Fin m) K) (hg : ∀ i, g i ∈ SU (unitaryInvolution K 2 f) m) {j : ℕ}
    (hj : j = 1 ∨ j = m - 1) :
    finrank k (matFix fun i => minorMatrix j (((g i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ)) =
      finrank K (matFix fun i => ((g i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
  rcases hj with rfl | rfl
  · have h := finrank_matFix_submatrix (k := k) (powersetCardOneEquiv (n := m)).symm
      (fun i => minorMatrix 1 (((g i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ))
    have hfun : (fun i => (minorMatrix 1 (((g i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ)).submatrix
        (powersetCardOneEquiv (n := m)).symm (powersetCardOneEquiv (n := m)).symm) =
        fun i => ((g i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ :=
      funext fun i => minorMatrix_one_submatrix _
    rw [hfun] at h
    rw [← h]
    exact finrank_matFix_map ψ _
  · have hdet : ∀ i, (((g i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ).det = 1 := fun i => by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, (hg i).1, map_one]
    have hinv : ∀ i, (((g i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ)⁻¹ =
        (((g i)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ := fun i => by
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ ψ.map_zero ψ.map_one]
    have h := finrank_matFix_submatrix (k := k)
      ((powersetCardOneEquiv (n := m)).symm.trans (complEquiv (by omega : 1 ≤ m)))
      (fun i => minorMatrix (m - 1) (((g i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ))
    have hfun : (fun i => (minorMatrix (m - 1) (((g i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ)).submatrix
        ((powersetCardOneEquiv (n := m)).symm.trans (complEquiv (by omega : 1 ≤ m)))
        ((powersetCardOneEquiv (n := m)).symm.trans (complEquiv (by omega : 1 ≤ m)))) =
        fun i => ((((g i)⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)ᵀ).map ψ :=
      funext fun i => by
        rw [minorMatrix_sub_one_submatrix (by omega : 1 ≤ m) (hdet i), hinv, Matrix.transpose_map]
    rw [hfun] at h
    rw [← h]
    exact finrank_matFix_inv_transpose_map_of_mem_SU ψ g hg

theorem card_powersetCard_of_eq_one_or {m j : ℕ} (hm : 1 ≤ m) (hj : j = 1 ∨ j = m - 1) :
    Fintype.card (Set.powersetCard (Fin m) j) = m := by
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card, Fintype.card_fin]
  rcases hj with rfl | rfl
  · exact Nat.choose_one_right m
  · rw [Nat.choose_symm hm, Nat.choose_one_right]

theorem mul_natCodim_le_codim (φ₀ : K →+* k) {m : ℕ} (hm : 2 ≤ m)
    (ε : Fin f → Finset (Fin m)) {P : Subgroup (SU (unitaryInvolution K 2 f) m)}
    (hPel : IsElemAbelian 2 P) (htwo : (Finset.univ.filter fun i => ε i ≠ ∅).card = 2)
    (hnat : ∀ i, ε i ≠ ∅ → ε i = {⟨1, by omega⟩} ∨ ε i = {⟨m - 1, by omega⟩}) :
    m * (m - finrank k (fixSubGen (suNaturalRep φ₀ (unitaryInvolution K 2 f) m) P)) ≤
      finrank k (BModel k ε) - finrank k (fixSubGen (suRep φ₀ m ε) P) := by
  classical
  obtain ⟨i₁, i₂, hi, hT⟩ := Finset.card_eq_two.mp htwo
  have hmem : ∀ i, ε i ≠ ∅ ↔ i = i₁ ∨ i = i₂ := fun i => by
    have h := congrArg (i ∈ ·) hT
    simpa using h
  have hε' : ∀ r, r ≠ i₁ → r ≠ i₂ → ε r = ∅ := fun r h1 h2 => by
    by_contra h
    rcases (hmem r).mp h with h | h
    · exact h1 h
    · exact h2 h
  have hlab : ∀ i, ε i ≠ ∅ → ∃ j : Fin m, ((j : ℕ) = 1 ∨ (j : ℕ) = m - 1) ∧ ε i = {j} :=
    fun i hi => by
      rcases hnat i hi with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
  obtain ⟨j₁, hj₁, h₁⟩ := hlab i₁ ((hmem i₁).mpr (Or.inl rfl))
  obtain ⟨j₂, hj₂, h₂⟩ := hlab i₂ ((hmem i₂).mpr (Or.inr rfl))
  have hcard : ∀ r, (ε r).card ≤ 1 := fun r => by
    by_cases hr1 : r = i₁
    · rw [hr1, h₁, Finset.card_singleton]
    by_cases hr2 : r = i₂
    · rw [hr2, h₂, Finset.card_singleton]
    rw [hε' r hr1 hr2, Finset.card_empty]
    exact Nat.zero_le 1
  let E := bModelEquivOfCardLeOne (k := k) ε hcard
  let e₂ := bIdxEquivPair ε hi j₁ j₂ h₁ h₂ hε'
  let eP : P ≃ Fin (Nat.card P) := Finite.equivFin P
  let xs : Fin (Nat.card P) → SU (unitaryInvolution K 2 f) m := fun i => (eP.symm i : P)
  have hxs : ∀ i, xs i ∈ P := fun i => (eP.symm i).2
  have hsurj : ∀ x ∈ P, ∃ i, xs i = x := fun x hx => ⟨eP ⟨x, hx⟩, by simp [xs]⟩
  let A : Fin (Nat.card P) → GL (Fin m) K := fun i => (xs i : GL (Fin m) K)
  have hA : ∀ i, A i ∈ SU (unitaryInvolution K 2 f) m := fun i => (xs i).2
  let T : Fin (Nat.card P) → Matrix _ _ k := fun i =>
    minorMatrix j₁ (((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map (suFrob φ₀ f i₁))
  let U : Fin (Nat.card P) → Matrix _ _ k := fun i =>
    minorMatrix j₂ (((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map (suFrob φ₀ f i₂))
  have hbMat : ∀ i, bMat ε (fun r => (suTwist φ₀ f m (xs i) r : Matrix (Fin m) (Fin m) k)) =
      (kroneckerMap (· * ·) (T i) (U i)).submatrix e₂ e₂ := fun i => by
    ext s t
    rw [bMat_apply_of_pair ε hi j₁ j₂ h₁ h₂ hε', submatrix_apply, kroneckerMap_apply,
      coe_suTwist_apply, coe_suTwist_apply]
    rfl
  have hmapfix : (fixSubGen (suRep φ₀ m ε) P).map (E : BModel k ε →ₗ[k] (BIdx ε → k)) =
      matFix fun i => bMat ε (fun r => (suTwist φ₀ f m (xs i) r : Matrix (Fin m) (Fin m) k)) := by
    ext w
    rw [Submodule.mem_map, mem_matFix]
    constructor
    · rintro ⟨v, hv, rfl⟩ i
      rw [LinearEquiv.coe_coe, ← bModelEquivOfCardLeOne_bRep]
      exact congrArg E ((mem_fixSubGen_iff_of_enum _ hxs hsurj v).mp hv i)
    · intro h
      refine ⟨E.symm w, (mem_fixSubGen_iff_of_enum _ hxs hsurj _).mpr fun i => ?_, by simp⟩
      apply E.injective
      change E (bRep ε (suTwist φ₀ f m (xs i)) (E.symm w)) = E (E.symm w)
      rw [bModelEquivOfCardLeOne_bRep, LinearEquiv.apply_symm_apply, h i]
  have hfix : finrank k (fixSubGen (suRep φ₀ m ε) P) =
      finrank k (matFix fun i => kroneckerMap (· * ·) (T i) (U i)) := by
    rw [← finrank_matFix_submatrix e₂, ← E.finrank_map_eq, hmapfix, funext hbMat]
  have hnatfix : finrank k (fixSubGen (suNaturalRep φ₀ (unitaryInvolution K 2 f) m) P) =
      finrank K (matFix fun i => ((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
    rw [← finrank_matFix_map φ₀]
    have hsub : fixSubGen (suNaturalRep φ₀ (unitaryInvolution K 2 f) m) P =
        matFix fun i => ((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map φ₀ := by
      ext v
      rw [mem_matFix, mem_fixSubGen_iff_of_enum _ hxs hsurj]
      simp only [suNaturalRep_apply, SUExtras.mat_apply]
      rfl
    rw [hsub]
  have hinvol : ∀ i, ((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
      ((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 := fun i => by
    have h : xs i * xs i = 1 := by rw [← sq]; exact hPel.2 _ (hxs i)
    rw [← Units.val_mul]
    exact congrArg (fun z : SU (unitaryInvolution K 2 f) m =>
      ((z : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) h
  have hcomm : ∀ i i', ((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
      ((A i' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      ((A i' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
        ((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := fun i i' => by
    have h : (eP.symm i : P) * eP.symm i' = eP.symm i' * eP.symm i := hPel.1.is_comm.comm _ _
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg (fun z : P => (((z : SU (unitaryInvolution K 2 f) m) : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K)) h
  have hmapsq : ∀ (ψ : K →+* k) (j : ℕ) (i : Fin (Nat.card P)),
      minorMatrix j (((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ) *
        minorMatrix j (((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ) = 1 :=
    fun ψ j i => by
      rw [← minorMatrix_mul, ← Matrix.map_mul, hinvol, Matrix.map_one _ ψ.map_zero ψ.map_one,
        minorMatrix_one]
  have hmapcomm : ∀ (ψ : K →+* k) (j : ℕ) (i i' : Fin (Nat.card P)),
      minorMatrix j (((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ) *
        minorMatrix j (((A i' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ) =
      minorMatrix j (((A i' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ) *
        minorMatrix j (((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map ψ) :=
    fun ψ j i i' => by
      rw [← minorMatrix_mul, ← minorMatrix_mul, ← Matrix.map_mul, ← Matrix.map_mul, hcomm]
  have hT : finrank k (matFix T) =
      finrank K (matFix fun i => ((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :=
    finrank_matFix_minorMatrix_of_mem_SU _ hm A hA hj₁
  have hkron : finrank k (matFix fun i => kroneckerMap (· * ·) (T i) (U i)) ≤
      finrank K (matFix fun i => ((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) * m := by
    have h := finrank_matFix_kronecker_le T U (fun i => hmapsq _ _ i)
      (fun i i' => hmapcomm _ _ i i') (fun i => hmapsq _ _ i) (fun i i' => hmapcomm _ _ i i')
    rwa [hT, card_powersetCard_of_eq_one_or (by omega) hj₂] at h
  have hdimM : finrank k (BModel k ε) = m * m := by
    rw [E.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_congr e₂,
      Fintype.card_prod, card_powersetCard_of_eq_one_or (by omega) hj₁,
      card_powersetCard_of_eq_one_or (by omega) hj₂]
  rw [hfix, hdimM, hnatfix]
  calc m * (m - finrank K (matFix fun i => ((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)))
      = m * m - finrank K (matFix fun i => ((A i : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) * m := by
        rw [Nat.mul_sub, Nat.mul_comm m (finrank K _)]
    _ ≤ m * m - finrank k (matFix fun i => kroneckerMap (· * ·) (T i) (U i)) :=
        Nat.sub_le_sub_left hkron _

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
