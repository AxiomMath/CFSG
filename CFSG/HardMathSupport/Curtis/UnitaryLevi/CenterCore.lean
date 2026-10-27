module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryPrimary
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.DualPoly

public section

namespace CFSG.AGLEmbedding.UnitaryLevi

open CFSG.AGLEmbedding CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LinearGroups CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary Matrix Polynomial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

omit [Finite K] [CharP K 2] in
theorem selfDual_comp_eq_bot (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (t : StatedSU n (2 ^ f) K)
    (hsq : Squarefree (minpoly K (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    {a : K[X]} (ha : a ∈ primaryFactors (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hself : dualPoly (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf).bar a = a)
    {W : Submodule K (Fin n → K)} (hW : IsTotallyIsotropicSU (2 ^ f) W)
    (hle : primaryComponent
      (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a ≤ W) :
    primaryComponent (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a = ⊥ := by
  have h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  set x : LinearMap.GeneralLinearGroup K (Fin n → K) :=
    GeneralLinearGroup.toLin (t : GL (Fin n) K) with hxdef
  have hxSU : x ∈ sesqSpecialUnitaryGroup (stdHermForm h n) := by
    rw [stdHermForm_eq_gramForm, hxdef, toLin_mem_sesqSpecialUnitaryGroup_iff,
      ← unitarySU_eq_gramSU h]
    exact t.2
  have hx : (x : Module.End K (Fin n → K)) =
      mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    GeneralLinearGroup.coe_toLin _
  rw [← hx] at hsq ha hle ⊢
  have H : UnitaryPrimaryData h.bar (stdHermForm h n) x :=
    ⟨fun c => h.bar_bar c, stdHermForm_isSymm h n, stdHermForm_separatingLeft h n,
      sesqSpecialUnitaryGroup_le _ hxSU, hsq⟩
  have hsep := separatingLeft_primaryComponent_selfDual H ha hself
  have hWt := (ToralCensus.isTotallyIsotropicSU_iff h W).mp hW
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  have := hsep ⟨w, hw⟩ (fun u => hWt _ (hle hw) _ (hle u.2))
  exact congrArg Subtype.val this

omit [Finite K] [CharP K 2] in
theorem mulVecLin_pow' (M : Matrix (Fin n) (Fin n) K) (m : ℕ) :
    (mulVecLin M) ^ m = mulVecLin (M ^ m) := by
  induction m with
  | zero => ext v; simp
  | succ m ih => rw [pow_succ, ih, pow_succ, Matrix.mulVecLin_mul]; rfl

omit [Finite K] in
theorem squarefree_minpoly_of_pow_scalar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0)
    (hM : M ^ p = Matrix.scalar (Fin n) c) :
    Squarefree (minpoly K (mulVecLin M)) := by
  have hp0 : (p : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    intro h
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 h) with h | h
    · omega
    · exact hp2 h.symm
  have hsep := Polynomial.separable_X_pow_sub_C c hp0 hc
  have hdvd : minpoly K (mulVecLin M) ∣ X ^ p - C c := by
    apply minpoly.dvd
    rw [map_sub, map_pow, aeval_X, aeval_C, mulVecLin_pow', hM]
    refine LinearMap.ext fun v => ?_
    ext i
    simp [Matrix.scalar_apply, Module.algebraMap_end_apply]
  exact hsep.squarefree.squarefree_of_dvd hdvd

omit [Finite K] [CharP K 2] in
theorem exists_unit_of_pow_mem_scalars (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 1 ≤ n) {p : ℕ}
    (t : StatedSU n (2 ^ f) K) (ht : ((t : GL (Fin n) K)) ^ p ∈ StatedScalars (Fin n) K) :
    ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c = (t : GL (Fin n) K) ^ p ∧
      c ^ (2 ^ f + 1) = 1 := by
  obtain ⟨c, hc⟩ := ht
  refine ⟨c, hc, ?_⟩
  have hsc : GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (2 ^ f) K := by
    rw [hc]; exact Subgroup.pow_mem _ t.2 p
  exact ((scalar_mem_statedSU_iff Nat.prime_two hK hn c).mp hsc).2

theorem false_of_pow_mem_scalars (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 1 ≤ n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1)
    {J : Subgroup (StatedSU n (2 ^ f) K)} {S₀ : Sylow 2 (StatedSU n (2 ^ f) K)}
    (hNJ : Subgroup.normalizer ((S₀ : Subgroup (StatedSU n (2 ^ f) K)) :
      Set (StatedSU n (2 ^ f) K)) ≤ J) (hJ : J ≠ ⊤) (t : StatedSU n (2 ^ f) K)
    (ht : ((t : GL (Fin n) K)) ^ p ∈ StatedScalars (Fin n) K)
    (htJ : ∀ g : StatedSU n (2 ^ f) K, Commute g t → g ∈ J) : False := by
  classical
  have h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  obtain ⟨c, hc, hcn⟩ := exists_unit_of_pow_mem_scalars hK hn t ht
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hM : ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p =
      Matrix.scalar (Fin n) (c : K) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
    simpa [GeneralLinearGroup.coe_scalar] using this.symm
  have hsq := squarefree_minpoly_of_pow_scalar hp hp2 _ hc0 hM
  obtain ⟨W, hW0, hWt, -, hWeq⟩ :=
    exists_eq_iSup_primaryComponent_of_normalizer_le hK hNJ hJ t hsq htJ
  obtain ⟨a, ha, hale, hane⟩ : ∃ a ∈ primaryFactors
      (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      primaryComponent (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a ≤ W ∧
      primaryComponent (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hW0
    rw [eq_bot_iff]
    conv_lhs => rw [hWeq]
    exact iSup₂_le fun a ha => iSup_le fun hle => (hcon a ha hle).le
  obtain ⟨hai, ham, hadvd⟩ := mem_primaryFactors.mp ha
  have hdvd : a ∣ X ^ p - C (c : K) := by
    refine hadvd.trans (minpoly.dvd K _ ?_)
    rw [map_sub, map_pow, aeval_X, aeval_C, mulVecLin_pow', hM]
    refine LinearMap.ext fun v => ?_
    ext i
    simp [Matrix.scalar_apply, Module.algebraMap_end_apply]
  have hcn' : (c : K) ^ (2 ^ f + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hcn, Units.val_one]
  have hself := dualPoly_eq_self hp hp2 hpq hK h.bar (fun c => h.bar_apply c) hcn' hai ham hdvd
  exact hane (selfDual_comp_eq_bot hK hf t hsq ha hself
    hWt hale)

end CFSG.AGLEmbedding.UnitaryLevi
