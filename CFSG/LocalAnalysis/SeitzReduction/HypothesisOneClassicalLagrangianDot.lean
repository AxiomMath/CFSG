module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLagrangianForms
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSULinearRadical

public section

namespace CFSG.SeitzReduction

namespace ClassicalLagrangian

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.NonalternatingRadical
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

theorem onesVec_dotProduct_onesVec_of_odd (hn : Odd n) :
    (onesVec : Fin n → K) ⬝ᵥ onesVec = 1 := by
  obtain ⟨m, rfl⟩ := hn
  simp only [dotProduct, onesVec, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul, zero_add,
    Nat.cast_one]

theorem exists_eq_smul_one_of_commute_odd (hn : Odd n) {M : Matrix (Fin n) (Fin n) K}
    (hT : ∀ u : Fin n → K, onesVec ⬝ᵥ u = 0 → Commute M (1 + vecMulVec u u))
    {h : Fin n → K} (hh : onesVec ⬝ᵥ h = 0) (hh0 : h ≠ 0)
    (hτ : Commute M (vecMulVec h onesVec + vecMulVec onesVec h)) : ∃ c : K, M = c • 1 :=
  exists_eq_smul_one_of_commute_dotProduct (onesVec_dotProduct_onesVec_of_odd hn) hT hh hh0 hτ

theorem exists_eq_smul_one_of_commute_odd_mul (hn : Odd n) {M : Matrix (Fin n) (Fin n) K}
    (hg : ∀ u v : Fin n → K, onesVec ⬝ᵥ u = 0 → onesVec ⬝ᵥ v = 0 → u ⬝ᵥ v = 1 →
      Commute M ((1 + vecMulVec u u) * (1 + vecMulVec v v)))
    {h : Fin n → K} (hh : onesVec ⬝ᵥ h = 0) (hh0 : h ≠ 0)
    (hτ : Commute M (vecMulVec h onesVec + vecMulVec onesVec h)) : ∃ c : K, M = c • 1 :=
  exists_eq_smul_one_of_commute_dotProduct_mul (onesVec_dotProduct_onesVec_of_odd hn)
    (fun x hx => by rw [dotProduct_self_eq_sq, hx, zero_pow two_ne_zero]) hg hh hh0 hτ

theorem eq_zero_of_forall_dotProduct_radicalW (hn : Even n) {i : Fin n} {w : Fin n → K}
    (hw : w ∈ radicalW i) (h : ∀ v ∈ radicalW i, v ⬝ᵥ w = 0) : w = 0 := by
  obtain ⟨hw1, hw2⟩ := mem_radicalW.mp hw
  refine dotProduct_separating fun x => ?_
  rw [eq_decomp i x, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
    dotProduct_comm w onesVec, hw1, dotProduct_single_one, hw2, smul_zero, smul_zero, add_zero,
    zero_add, dotProduct_comm w]
  exact h _ (decomp_mem_radicalW hn i x)

theorem exists_eq_of_forall_dotProduct_radicalW (hn : Even n) {i : Fin n} {x : Fin n → K}
    (hx : ∀ u ∈ radicalW i, x ⬝ᵥ u = 0) :
    ∃ a b : K, x = a • onesVec + b • Pi.single i 1 := by
  have hw := decomp_mem_radicalW hn i x
  have h0 := eq_zero_of_forall_dotProduct_radicalW hn hw fun v hv => by
    obtain ⟨hv1, hv2⟩ := mem_radicalW.mp hv
    rw [dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_comm v x,
      hx v hv, dotProduct_comm v onesVec, hv1, dotProduct_single_one, hv2, smul_zero, smul_zero,
      sub_zero, sub_zero]
  refine ⟨x i - onesVec ⬝ᵥ x, onesVec ⬝ᵥ x, ?_⟩
  rw [sub_sub, sub_eq_zero] at h0
  exact h0

theorem exists_dotProduct_eq_one_of_mem_radicalW (hn : Even n) {i : Fin n} {w : Fin n → K}
    (hw : w ∈ radicalW i) (hw0 : w ≠ 0) : ∃ v ∈ radicalW i, w ⬝ᵥ v = 1 := by
  have : ∃ v ∈ radicalW i, w ⬝ᵥ v ≠ 0 := by
    by_contra hcon
    exact hw0 (eq_zero_of_forall_dotProduct_radicalW hn hw fun v hv => by
      rw [dotProduct_comm]
      exact not_not.mp fun hne => hcon ⟨v, hv, hne⟩)
  obtain ⟨v, hv, hwv⟩ := this
  exact ⟨(w ⬝ᵥ v)⁻¹ • v, Submodule.smul_mem _ _ hv, by
    rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hwv]⟩

theorem conj_radicalMatrix_mul_radicalMatrix (hn : Even n) {g : GL (Fin n) K}
    (hg : g ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K)) {w : Fin n → K}
    (hw : onesVec ⬝ᵥ w = 0) (c : K) :
    (g : Matrix (Fin n) (Fin n) K) * radicalMatrix w c *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * radicalMatrix w c =
      radicalMatrix ((g : Matrix (Fin n) (Fin n) K) *ᵥ w + w)
        (((g : Matrix (Fin n) (Fin n) K) *ᵥ w) ⬝ᵥ w) := by
  rw [conj_radicalMatrix hg, radicalMatrix_mul c c (onesVec_dotProduct_onesVec hn)
    (by rw [onesVec_dotProduct_mulVec_of_mem hg, hw]) hw, CharTwo.add_self_eq_zero, zero_add]

theorem commute_radicalMatrix_add (hn : Even n) {M : Matrix (Fin n) (Fin n) K}
    {v v' : Fin n → K} (hv : onesVec ⬝ᵥ v = 0) (hv' : onesVec ⬝ᵥ v' = 0) {c c' : K}
    (h : Commute M (radicalMatrix v c)) (h' : Commute M (radicalMatrix v' c')) :
    Commute M (radicalMatrix (v + v') (c + c' + v ⬝ᵥ v')) := by
  rw [← radicalMatrix_mul c c' (onesVec_dotProduct_onesVec hn) hv hv']
  exact h.mul_right h'

theorem exists_eq_smul_one_of_commute_radicalMatrix (hn : Even n) {i : Fin n}
    {M : Matrix (Fin n) (Fin n) K} (hW : ∀ w ∈ radicalW i, M *ᵥ w ∈ radicalW i)
    (hd : ∀ u ∈ radicalW i, (M *ᵥ onesVec) ⬝ᵥ u = 0)
    (he : ∀ u ∈ radicalW i, (M *ᵥ Pi.single i 1) ⬝ᵥ u = 0)
    (hR : ∀ v ∈ radicalW i, ∃ c : K, Commute M (radicalMatrix v c))
    {h : Fin n → K} (hh : h ∈ radicalW i) (hh0 : h ≠ 0)
    (hτ : Commute M (vecMulVec h (Pi.single i 1) + vecMulVec (Pi.single i 1) h)) :
    ∃ c : K, M = c • 1 := by
  have hde : (onesVec : Fin n → K) ⬝ᵥ Pi.single i 1 = 1 := onesVec_dotProduct_single i
  have hed : (Pi.single i 1 : Fin n → K) ⬝ᵥ onesVec = 1 := by rw [dotProduct_comm, hde]
  have hee : (Pi.single i 1 : Fin n → K) ⬝ᵥ Pi.single i 1 = 1 := by
    rw [dotProduct_single_one, Pi.single_eq_same]
  have hW1 : ∀ u ∈ radicalW i, (onesVec : Fin n → K) ⬝ᵥ u = 0 := fun u hu =>
    (mem_radicalW.mp hu).1
  have hW2 : ∀ u ∈ radicalW i, (Pi.single i 1 : Fin n → K) ⬝ᵥ u = 0 := fun u hu => by
    rw [single_one_dotProduct, (mem_radicalW.mp hu).2]
  have hhe : h ⬝ᵥ (Pi.single i 1 : Fin n → K) = 0 := by
    rw [dotProduct_comm]
    exact hW2 h hh
  obtain ⟨h', hh', hhh'⟩ := exists_dotProduct_eq_one_of_mem_radicalW hn hh hh0
  have hcomm : ∀ {X : Matrix (Fin n) (Fin n) K}, Commute M X →
      ∀ x, M *ᵥ (X *ᵥ x) = X *ᵥ (M *ᵥ x) := by
    intro X hX x
    rw [mulVec_mulVec, hX.eq, ← mulVec_mulVec]
  obtain ⟨α, γ, hMd⟩ := exists_eq_of_forall_dotProduct_radicalW hn hd
  obtain ⟨δ, ε, hMe⟩ := exists_eq_of_forall_dotProduct_radicalW hn he
  obtain ⟨c₀, hc₀⟩ := hR h hh
  have hγ : γ = 0 := by
    have e := hcomm hc₀ onesVec
    simp only [radicalMatrix_mulVec_onesVec hn hh, hMd, mulVec_add, mulVec_smul,
      radicalMatrix_mulVec_single hh] at e
    have e' := congrArg (· ⬝ᵥ h') e
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, hW1 h' hh', hW2 h' hh', hhh'] at e'
    linear_combination -e'
  rw [hγ, zero_smul, add_zero] at hMd
  have hMW : ∀ w ∈ radicalW i, M *ᵥ w = α • w := by
    intro w hw
    have hw' := hW w hw
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_dotProduct_radicalW hn (sub_mem hw' (Submodule.smul_mem _ α hw))
      fun v hv => ?_
    obtain ⟨cv, hcv⟩ := hR v hv
    have e := hcomm hcv w
    rw [radicalMatrix_mulVec_of_mem hw, mulVec_add, mulVec_smul, hMd,
      radicalMatrix_mulVec_of_mem hw'] at e
    have e' := congrArg (· ⬝ᵥ Pi.single i 1) e
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, hde] at e'
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    linear_combination -e'
  have hε : ε = α := by
    have e := hcomm hc₀ (Pi.single i 1)
    simp only [radicalMatrix_mulVec_single hh, mulVec_add, mulVec_smul, hMe, hMW h hh, hMd,
      radicalMatrix_mulVec_onesVec hn hh] at e
    have e' := congrArg (· ⬝ᵥ h') e
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, hW1 h' hh', hW2 h' hh', hhh'] at e'
    linear_combination -e'
  have hτx : ∀ x, (vecMulVec h (Pi.single i 1) + vecMulVec (Pi.single i 1) h) *ᵥ x =
      ((Pi.single i 1 : Fin n → K) ⬝ᵥ x) • h + (h ⬝ᵥ x) • Pi.single i 1 := by
    intro x
    rw [add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul]
  have hδ : δ = 0 := by
    have e := hcomm hτ (Pi.single i 1)
    rw [hτx, hτx, hee, hhe, zero_smul, add_zero, one_smul, hMW h hh, hMe] at e
    have e' := congrArg (· ⬝ᵥ h') e
    simp only [add_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul, hed,
      hee, hW2 h' hh', hhh'] at e'
    linear_combination -e' - hε
  refine ⟨α, matrix_eq_of_decomp hn (i := i) ?_ ?_ ?_⟩
  · rw [hMd, smul_mulVec, one_mulVec]
  · intro w hw
    rw [hMW w hw, smul_mulVec, one_mulVec]
  · rw [hMe, hδ, hε, zero_smul, zero_add, smul_mulVec, one_mulVec]

omit [CharP K 2] in
theorem preserves_of_commute_transvection_radicalW {i : Fin n} {M : Matrix (Fin n) (Fin n) K}
    (hT : ∀ u ∈ radicalW i, Commute M (1 + vecMulVec u u)) :
    (∀ w ∈ radicalW i, M *ᵥ w ∈ radicalW i) ∧
      ∀ x, (∀ u ∈ radicalW i, x ⬝ᵥ u = 0) → ∀ u ∈ radicalW i, (M *ᵥ x) ⬝ᵥ u = 0 := by
  have hc : ∀ u ∈ radicalW i, Commute (Matrix.toLinAlgEquiv' M)
      (LinearMap.transvection ((Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K)).flip u) u) :=
    fun u hu => by
      rw [← toLinAlgEquiv'_transvection_one]
      exact commute_toLinAlgEquiv' (hT u hu)
  refine ⟨fun w hw => ?_, fun x hx u hu => ?_⟩
  · by_cases hw0 : w = 0
    · rw [hw0, mulVec_zero]
      exact zero_mem _
    have : ∃ x : Fin n → K, Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K) x w ≠ 0 := by
      by_contra hcon
      exact hw0 (dotProduct_separating fun y => by
        rw [dotProduct_comm, ← toBilin'_one_apply_eq]
        exact not_not.mp fun hne => hcon ⟨y, hne⟩)
    obtain ⟨x, hx⟩ := this
    obtain ⟨a, ha⟩ := exists_apply_eq_smul_of_commute_transvection (hc w hw) hx
    rw [Matrix.toLinAlgEquiv'_apply] at ha
    rw [ha]
    exact Submodule.smul_mem _ a hw
  · by_cases hu0 : u = 0
    · rw [hu0, dotProduct_zero]
    have := apply_eq_zero_of_commute_transvection (hc u hu) hu0
      (x := x) (by rw [toBilin'_one_apply_eq]; exact hx u hu)
    rwa [toBilin'_one_apply_eq, Matrix.toLinAlgEquiv'_apply] at this

theorem preserves_of_commute_transvection_mul_radicalW (hn : Even n) {i : Fin n}
    {M : Matrix (Fin n) (Fin n) K}
    (hg : ∀ u ∈ radicalW i, ∀ v ∈ radicalW i, u ⬝ᵥ v = 1 →
      Commute M ((1 + vecMulVec u u) * (1 + vecMulVec v v))) :
    (∀ w ∈ radicalW i, M *ᵥ w ∈ radicalW i) ∧
      ∀ x, (∀ u ∈ radicalW i, x ⬝ᵥ u = 0) → ∀ u ∈ radicalW i, (M *ᵥ x) ⬝ᵥ u = 0 := by
  have hc : ∀ u ∈ radicalW i, ∀ v ∈ radicalW i, u ⬝ᵥ v = 1 → Commute (Matrix.toLinAlgEquiv' M)
      (LinearMap.transvection ((Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K)).flip u) u *
        LinearMap.transvection ((Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K)).flip v) v) :=
    fun u hu v hv huv => by
      rw [← toLinAlgEquiv'_transvection_one, ← toLinAlgEquiv'_transvection_one, ← map_mul]
      exact commute_toLinAlgEquiv' (hg u hu v hv huv)
  have hself : ∀ v ∈ radicalW (K := K) i, v ⬝ᵥ v = 0 := fun v hv => by
    rw [dotProduct_self_eq_sq, (mem_radicalW.mp hv).1, zero_pow two_ne_zero]
  refine ⟨fun w hw => ?_, fun x hx u hu => ?_⟩
  · by_cases hw0 : w = 0
    · rw [hw0, mulVec_zero]
      exact zero_mem _
    obtain ⟨v, hv, hwv⟩ := exists_dotProduct_eq_one_of_mem_radicalW hn hw hw0
    have key := apply_eq_of_commute_transvection_mul (hc w hw v hv hwv) (x := v)
      (by rw [toBilin'_one_apply_eq, hself v hv]) (by rw [toBilin'_one_apply_eq, dotProduct_comm,
        hwv])
    rw [Matrix.toLinAlgEquiv'_apply] at key
    rw [key]
    exact add_mem (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hv)
  · by_cases hu0 : u = 0
    · rw [hu0, dotProduct_zero]
    obtain ⟨v, hv, huv⟩ := exists_dotProduct_eq_one_of_mem_radicalW hn hu hu0
    have hli : LinearIndependent K ![u, v] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have e := congrArg (u ⬝ᵥ ·) hst
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hself u hu, huv,
        dotProduct_zero] at e
      have ht : t = 0 := by linear_combination e
      subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right hu0, rfl⟩
    have := (apply_eq_zero_of_commute_transvection_mul (hc u hu v hv huv) hli (x := x)
      (by rw [toBilin'_one_apply_eq]; exact hx u hu)
      (by rw [toBilin'_one_apply_eq]; exact hx v hv)).1
    rwa [toBilin'_one_apply_eq, Matrix.toLinAlgEquiv'_apply] at this

theorem exists_eq_smul_one_of_commute_even (hn : Even n) {i : Fin n}
    {M : Matrix (Fin n) (Fin n) K} (hT : ∀ u ∈ radicalW i, Commute M (1 + vecMulVec u u))
    (hR : ∀ v ∈ radicalW i, ∃ c : K, Commute M (radicalMatrix v c))
    {h : Fin n → K} (hh : h ∈ radicalW i) (hh0 : h ≠ 0)
    (hτ : Commute M (vecMulVec h (Pi.single i 1) + vecMulVec (Pi.single i 1) h)) :
    ∃ c : K, M = c • 1 := by
  obtain ⟨hW, hperp⟩ := preserves_of_commute_transvection_radicalW hT
  exact exists_eq_smul_one_of_commute_radicalMatrix hn hW
    (hperp _ fun u hu => (mem_radicalW.mp hu).1)
    (hperp _ fun u hu => by rw [single_one_dotProduct, (mem_radicalW.mp hu).2]) hR hh hh0 hτ

theorem exists_eq_smul_one_of_commute_even_mul (hn : Even n) {i : Fin n}
    {M : Matrix (Fin n) (Fin n) K}
    (hg : ∀ u ∈ radicalW i, ∀ v ∈ radicalW i, u ⬝ᵥ v = 1 →
      Commute M ((1 + vecMulVec u u) * (1 + vecMulVec v v)))
    (hR : ∀ v ∈ radicalW i, ∃ c : K, Commute M (radicalMatrix v c))
    {h : Fin n → K} (hh : h ∈ radicalW i) (hh0 : h ≠ 0)
    (hτ : Commute M (vecMulVec h (Pi.single i 1) + vecMulVec (Pi.single i 1) h)) :
    ∃ c : K, M = c • 1 := by
  obtain ⟨hW, hperp⟩ := preserves_of_commute_transvection_mul_radicalW hn hg
  exact exists_eq_smul_one_of_commute_radicalMatrix hn hW
    (hperp _ fun u hu => (mem_radicalW.mp hu).1)
    (hperp _ fun u hu => by rw [single_one_dotProduct, (mem_radicalW.mp hu).2]) hR hh hh0 hτ

end ClassicalLagrangian

end CFSG.SeitzReduction
