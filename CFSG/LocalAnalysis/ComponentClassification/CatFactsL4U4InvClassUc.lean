module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassUb

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace InvClassU

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

variable {p f : ℕ} {K : Type} [Field K]

theorem hypProj_eq_one_iff (h : UnitaryFieldData p f K) (g : hypSU h 2 0) :
    hypProj h 2 0 g = 1 ↔
      ∃ c : K, ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = c • 1 := by
  constructor
  · intro h1
    rw [← MonoidHom.mem_ker, ker_hypProj] at h1
    exact exists_eq_smul_one_of_mem_hypScalars h1
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact (Matrix.isUnits_det_units (g : GL (HypIndex 2 0) K)).ne_zero (by rw [hc, det_zero])
    have hdet := (mem_hypSU.mp g.2).2
    rw [hc, det_smul, det_one, mul_one, card_hypIndex_two_zero] at hdet
    rw [← MonoidHom.mem_ker, ker_hypProj]
    refine ⟨Units.mk0 c hc0, norm_eq_one_of_smul h (by norm_num)
      (mem_hypUnitary.mpr (mem_hypSU.mp g.2).1) hc, Units.ext ?_, Units.ext ?_⟩
    · rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact hdet
    · rw [hc, GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_apply, smul_one_eq_diagonal]

theorem suppMat_smul_one {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {E : Matrix ι κ K} {F : Matrix κ ι K} (hEF : E * F = 1) (c : K) :
    suppMat E F (c • 1) = c • 1 := by
  rw [suppMat, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
    hEF]
  abel

theorem exists_frameHom (h : UnitaryFieldData p f K) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (hκ : Fintype.card κ = 4) {v : κ → HypIndex 2 0 → K} {G Gi : Matrix κ κ K}
    (hG : (Matrix.of fun i j => hypForm h 2 0 (v i) (v j)) = G) (hGi : Gi * G = 1)
    {H : Type*} [Group H] (Y : H →* Matrix κ κ K)
    (hY : ∀ x, ((Y x).map h.bar)ᵀ * G * Y x = G) (hYd : ∀ x, (Y x).det = 1) :
    ∃ ψ : H →* hypSU h 2 0,
      (∀ x (c : K),
        ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = c • 1 ↔
          Y x = c • 1) ∧
      ∀ {A : GL (HypIndex 2 0) K}, A ∈ hypUnitary h 2 0 → ∀ {d : κ → K},
        (∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i = d i • v i) →
        (∀ x, diagonal d * Y x = Y x * diagonal d) →
        ∀ x, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
            ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
              (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
  have hgram : ((colMat v).map h.bar)ᵀ * hypGram 2 0 K * colMat v = G := by
    rw [gram_colMat_eq_hypForm, hG]
  have hGi' : G * Gi = 1 := mul_eq_one_comm.mp hGi
  have h1 : Gi * (((colMat v).map h.bar)ᵀ * hypGram 2 0 K * colMat v) = 1 := by rw [hgram, hGi]
  have h2 : (((colMat v).map h.bar)ᵀ * hypGram 2 0 K * colMat v) * Gi = 1 := by
    rw [hgram, hGi']
  obtain ⟨ψ, hψ⟩ := exists_hypSU_hom h (E := colMat v) h1 h2 Y
    (fun x => by rw [hgram]; exact hY x) hYd
  have hFE : Gi * ((colMat v).map h.bar)ᵀ * hypGram 2 0 K * colMat v = 1 := by
    rw [← h1]
    simp only [Matrix.mul_assoc]
  have hEF := mul_eq_one_comm_of_card (by rw [hκ, card_hypIndex_two_zero]) hFE
  refine ⟨ψ, fun x c => ?_, fun {A} hA {d} hAv hDY x => ?_⟩
  · rw [hψ x]
    exact ⟨eq_smul_one_of_suppMat hFE, fun hc => by rw [hc]; exact suppMat_smul_one hEF c⟩
  · have hAE := mul_colMat_of_eigen hAv
    have hFA := suppF_mul_of_isometry (mem_hypUnitary.mp hA) hAE h1 h2
    rw [hψ x]
    exact mul_suppMat hAE hFA (hDY x)

section Image

variable {H P : Type*} [Group H] [Group P] {κ : Type*} [Fintype κ] [DecidableEq κ]
  {ρ : H →* P} {Y : H →* Matrix κ κ K} (hρ : ∀ x, ρ x = 1 ↔ ∃ c : K, Y x = c • 1)

include hρ

theorem eq_smul_of_eq {a b : H} (hab : ρ a = ρ b) : ∃ c : K, Y a = c • Y b := by
  obtain ⟨c, hc⟩ := (hρ (b⁻¹ * a)).mp (by rw [map_mul, map_inv, hab, inv_mul_cancel])
  refine ⟨c, ?_⟩
  rw [show a = b * (b⁻¹ * a) by group, map_mul, hc, Matrix.mul_smul, Matrix.mul_one]

theorem orderOf_eq_four_of {x : H} (hx4 : x ^ 4 = 1) (hx2 : ¬ ∃ c : K, Y (x ^ 2) = c • 1) :
    orderOf (ρ x) = 4 := by
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [pow_one, ← map_pow]
    exact fun h1 => hx2 ((hρ _).mp h1)
  · rw [← map_pow, show 2 ^ (1 + 1) = 4 from rfl, hx4, map_one]

theorem orderOf_eq_two_of {x : H} (hx2 : ∃ c : K, Y (x ^ 2) = c • 1)
    (hx : ¬ ∃ c : K, Y x = c • 1) : orderOf (ρ x) = 2 :=
  orderOf_eq_prime (by rw [← map_pow]; exact (hρ _).mpr hx2) fun h1 => hx ((hρ _).mp h1)

end Image

@[expose] def symPair (c t : K) (v : Fin 2 → HypIndex 2 0 → K) : Fin 2 → HypIndex 2 0 → K :=
  ![v 0 + c • v 1, t • (v 0 - c • v 1)]

variable (h : UnitaryFieldData p f K)

theorem symPair_gram {c t : K} (hc : h.norm c = -1) (ht : h.bar t = -t)
    {v : Fin 2 → HypIndex 2 0 → K}
    (hv : ∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0) (i j : Fin 2) :
    hypForm h 2 0 (symPair c t v i) (symPair c t v j) = ((2 * t) • quatI K) i j := by
  have h11 : hypForm h 2 0 (v 0) (v 0) = 1 := by simpa using hv 0 0
  have h22 : hypForm h 2 0 (v 1) (v 1) = 1 := by simpa using hv 1 1
  have h12 : hypForm h 2 0 (v 0) (v 1) = 0 := by simpa using hv 0 1
  have h21 : hypForm h 2 0 (v 1) (v 0) = 0 := by simpa using hv 1 0
  have hcN : c * h.bar c = -1 := hc
  have hUU : hypForm h 2 0 (v 0 + c • v 1) (v 0 + c • v 1) = 0 := by
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
      h11, h22, h12, h21]
    linear_combination hcN
  have hUW : hypForm h 2 0 (v 0 + c • v 1) (t • (v 0 - c • v 1)) = 2 * t := by
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul,
      smul_eq_mul, h11, h22, h12, h21]
    linear_combination (-t) * hcN
  have hWU : hypForm h 2 0 (t • (v 0 - c • v 1)) (v 0 + c • v 1) = -(2 * t) := by
    simp only [map_add, map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, map_smul,
      smul_eq_mul, h11, h22, h12, h21]
    linear_combination (1 - h.bar c * c) * ht + t * hcN
  have hWW : hypForm h 2 0 (t • (v 0 - c • v 1)) (t • (v 0 - c • v 1)) = 0 := by
    simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
      h11, h22, h12, h21]
    linear_combination (h.bar t * t) * hcN
  fin_cases i <;> fin_cases j
  · change hypForm h 2 0 (v 0 + c • v 1) (v 0 + c • v 1) = _
    rw [hUU]
    simp [quatI]
  · change hypForm h 2 0 (v 0 + c • v 1) (t • (v 0 - c • v 1)) = _
    rw [hUW]
    simp [quatI]
  · change hypForm h 2 0 (t • (v 0 - c • v 1)) (v 0 + c • v 1) = _
    rw [hWU]
    simp [quatI]
  · change hypForm h 2 0 (t • (v 0 - c • v 1)) (t • (v 0 - c • v 1)) = _
    rw [hWW]
    simp [quatI]

theorem symPair_orth (c t : K) {v v' : Fin 2 → HypIndex 2 0 → K}
    (hvv : ∀ i j, hypForm h 2 0 (v i) (v' j) = 0) (i j : Fin 2) :
    hypForm h 2 0 (symPair c t v i) (symPair c t v' j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [symPair, map_add, map_sub, hvv]

omit h in
theorem symPair_eigen (c t : K) {A : Matrix (HypIndex 2 0) (HypIndex 2 0) K} {d : K}
    {v : Fin 2 → HypIndex 2 0 → K} (hv : ∀ i, A *ᵥ v i = d • v i) (i : Fin 2) :
    A *ᵥ symPair c t v i = d • symPair c t v i := by
  fin_cases i
  · simp only [symPair, Fin.zero_eta, Matrix.cons_val_zero, mulVec_add, mulVec_smul, hv,
      smul_add, smul_comm c d]
  · simp only [symPair, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, mulVec_smul,
      mulVec_sub, hv, smul_sub, smul_comm c d, smul_comm t d]

@[expose] noncomputable def bdPlane :
    SpecialLinearGroup (Fin 2) h.fixedField × SpecialLinearGroup (Fin 2) h.fixedField →*
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K where
  toFun x := fromBlocks (planeHom h x.1) 0 0 (planeHom h x.2)
  map_one' := by simp [fromBlocks_one]
  map_mul' x y := by simp [fromBlocks_multiply]

theorem bdPlane_apply (x : SpecialLinearGroup (Fin 2) h.fixedField ×
    SpecialLinearGroup (Fin 2) h.fixedField) :
    bdPlane h x = fromBlocks (planeHom h x.1) 0 0 (planeHom h x.2) := rfl

theorem bdPlane_isometry (s : K) (x : SpecialLinearGroup (Fin 2) h.fixedField ×
    SpecialLinearGroup (Fin 2) h.fixedField) :
    ((bdPlane h x).map h.bar)ᵀ * fromBlocks (s • quatI K) 0 0 (s • quatI K) * bdPlane h x =
      fromBlocks (s • quatI K) 0 0 (s • quatI K) := by
  have h1 : ∀ B : SpecialLinearGroup (Fin 2) h.fixedField,
      ((planeHom h B).map h.bar)ᵀ * quatI K * planeHom h B = quatI K := fun B => by
    simpa using planeHom_isometry h 1 B
  rw [bdPlane_apply, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply,
    fromBlocks_multiply]
  simp [h1]

theorem det_bdPlane (x : SpecialLinearGroup (Fin 2) h.fixedField ×
    SpecialLinearGroup (Fin 2) h.fixedField) : (bdPlane h x).det = 1 := by
  rw [bdPlane_apply, det_fromBlocks_zero₂₁, det_planeHom, det_planeHom, mul_one]

omit h in
theorem diagonal_elim_comm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (a b : K) (M : Matrix m m K) (N : Matrix n n K) :
    diagonal (Sum.elim (fun _ => a) (fun _ => b)) * fromBlocks M 0 0 N =
      fromBlocks M 0 0 N * diagonal (Sum.elim (fun _ => a) (fun _ => b)) := by
  rw [← fromBlocks_diagonal, fromBlocks_multiply, fromBlocks_multiply, ← smul_one_eq_diagonal,
    ← smul_one_eq_diagonal]
  simp

theorem exists_t2Hom (hp : p ≠ 2) {A : GL (HypIndex 2 0) K} (hA : A ∈ hypUnitary h 2 0) {l : K}
    {v : Fin 2 ⊕ Fin 2 → HypIndex 2 0 → K}
    (hv : ∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0)
    (hAv : ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
      Sum.elim (fun _ => l) (fun _ => -l) i • v i) :
    ∃ ψ : SpecialLinearGroup (Fin 2) h.fixedField × SpecialLinearGroup (Fin 2) h.fixedField →*
        hypSU h 2 0,
      (∀ x, hypProj h 2 0 (ψ x) = 1 ↔ ∃ c : K, bdPlane h x = c • 1) ∧
      ∀ x, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
          ((ψ x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
            (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
  obtain ⟨c, hc⟩ := exists_norm_eq_neg_one h
  obtain ⟨t, ht0, ht⟩ := exists_bar_eq_neg h
  have h2t : 2 * t ≠ 0 := mul_ne_zero (two_ne_zero_of_odd h hp) ht0
  have ha : ∀ i j, hypForm h 2 0 ((v ∘ Sum.inl) i) ((v ∘ Sum.inl) j) =
      if i = j then 1 else 0 := fun i j => by simpa using hv (Sum.inl i) (Sum.inl j)
  have hb : ∀ i j, hypForm h 2 0 ((v ∘ Sum.inr) i) ((v ∘ Sum.inr) j) =
      if i = j then 1 else 0 := fun i j => by simpa using hv (Sum.inr i) (Sum.inr j)
  have hab : ∀ i j, hypForm h 2 0 ((v ∘ Sum.inl) i) ((v ∘ Sum.inr) j) = 0 := fun i j => by
    simpa using hv (Sum.inl i) (Sum.inr j)
  have hba : ∀ i j, hypForm h 2 0 ((v ∘ Sum.inr) i) ((v ∘ Sum.inl) j) = 0 := fun i j => by
    simpa using hv (Sum.inr i) (Sum.inl j)
  have hG : (Matrix.of fun i j => hypForm h 2 0
      (Sum.elim (symPair c t (v ∘ Sum.inl)) (symPair c t (v ∘ Sum.inr)) i)
      (Sum.elim (symPair c t (v ∘ Sum.inl)) (symPair c t (v ∘ Sum.inr)) j)) =
      fromBlocks ((2 * t) • quatI K) 0 0 ((2 * t) • quatI K) := by
    ext (i | i) (j | j)
    · simp only [Matrix.of_apply, Sum.elim_inl, fromBlocks_apply₁₁]
      exact symPair_gram h hc ht ha i j
    · simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₂,
        Matrix.zero_apply]
      exact symPair_orth h c t hab i j
    · simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₂₁,
        Matrix.zero_apply]
      exact symPair_orth h c t hba i j
    · simp only [Matrix.of_apply, Sum.elim_inr, fromBlocks_apply₂₂]
      exact symPair_gram h hc ht hb i j
  have hGi : fromBlocks ((-(2 * t)⁻¹) • quatI K) 0 0 ((-(2 * t)⁻¹) • quatI K) *
      fromBlocks ((2 * t) • quatI K) 0 0 ((2 * t) • quatI K) = 1 := by
    have h1 : ((-(2 * t)⁻¹) • quatI K) * ((2 * t) • quatI K) = 1 := by
      rw [smul_mul_smul_comm, quatI_mul_self, neg_mul, inv_mul_cancel₀ h2t, neg_smul, one_smul,
        neg_neg]
    rw [fromBlocks_multiply, h1]
    simp [fromBlocks_one]
  obtain ⟨ψ, hψs, hψA⟩ := exists_frameHom h (by simp) hG hGi (bdPlane h)
    (bdPlane_isometry h (2 * t)) (det_bdPlane h)
  refine ⟨ψ, fun x => (hypProj_eq_one_iff h (ψ x)).trans (exists_congr fun c => hψs x c),
    hψA hA (d := Sum.elim (fun _ => l) (fun _ => -l)) ?_ fun x => diagonal_elim_comm _ _ _ _⟩
  rintro (i | i)
  · exact symPair_eigen c t (fun i => hAv (Sum.inl i)) i
  · exact symPair_eigen c t (fun i => hAv (Sum.inr i)) i

theorem t2_z4z2 (hp : p ≠ 2) {P : Type*} [Group P]
    {ρ : SpecialLinearGroup (Fin 2) h.fixedField × SpecialLinearGroup (Fin 2) h.fixedField →* P}
    (hρ : ∀ x, ρ x = 1 ↔ ∃ c : K, bdPlane h x = c • 1) :
    orderOf (ρ (slQuatI h.fixedField, 1)) = 4 ∧
      orderOf (ρ (slQuatI h.fixedField, slQuatI h.fixedField)) = 2 ∧
      Commute (ρ (slQuatI h.fixedField, 1)) (ρ (slQuatI h.fixedField, slQuatI h.fixedField)) ∧
      ρ (slQuatI h.fixedField, slQuatI h.fixedField) ≠ ρ (slQuatI h.fixedField, 1) ^ 2 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp
  have hj2 : planeHom h (slQuatI h.fixedField ^ 2) = -1 := by
    rw [map_pow, planeHom_slQuatI, pow_two, quatI_mul_self]
  have hx2 : bdPlane h ((slQuatI h.fixedField, 1) ^ 2) = fromBlocks (-1) 0 0 1 := by
    rw [Prod.pow_mk, bdPlane_apply, hj2, one_pow, map_one]
  have hw2 : bdPlane h ((slQuatI h.fixedField, slQuatI h.fixedField) ^ 2) = (-1 : K) • 1 := by
    rw [Prod.pow_mk, bdPlane_apply, hj2, neg_one_smul, ← fromBlocks_one, fromBlocks_neg]
    simp
  have hw : bdPlane h (slQuatI h.fixedField, slQuatI h.fixedField) =
      fromBlocks (quatI K) 0 0 (quatI K) := by
    rw [bdPlane_apply, planeHom_slQuatI]
  refine ⟨orderOf_eq_four_of hρ ?_ ?_, orderOf_eq_two_of hρ ⟨-1, hw2⟩ ?_, ?_, ?_⟩
  · rw [Prod.pow_mk, slQuatI_pow_four, one_pow, Prod.mk_one_one]
  · rintro ⟨c, hc⟩
    rw [hx2] at hc
    have h00 := congrFun (congrFun hc (Sum.inl 0)) (Sum.inl 0)
    have h11 := congrFun (congrFun hc (Sum.inr 0)) (Sum.inr 0)
    simp at h00 h11
    exact h2 (by linear_combination h11 - h00)
  · rintro ⟨c, hc⟩
    rw [hw] at hc
    have h01 := congrFun (congrFun hc (Sum.inl 0)) (Sum.inl 1)
    simp [quatI] at h01
  · rw [Commute, SemiconjBy, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul,
      mul_one]
  · intro he
    rw [← map_pow] at he
    obtain ⟨c, hc⟩ := eq_smul_of_eq hρ he
    rw [hw, hx2] at hc
    have h01 := congrFun (congrFun hc (Sum.inl 0)) (Sum.inl 1)
    simp [quatI] at h01

end InvClassU

end CFSG.ComponentClassification.CatFactsL4U4
