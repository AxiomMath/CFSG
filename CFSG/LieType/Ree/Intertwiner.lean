module

public import CFSG.Blueprint.ChevalleySimpleRoots
public import CFSG.LieType.Ree.Mirror
public import CFSG.LieType.Ree.ShortModule
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley

namespace ReeTag

variable (t : ReeTag)

@[expose] def exponent (i : Fin t.tag.rank) : ℕ :=
  if i ∈ t.longSet then 1 else t.prime

theorem exponent_eq (i : Fin t.tag.rank) :
    t.exponent i = 1 ∨ t.exponent i = 2 ∨ t.exponent i = 3 := by
  unfold exponent
  split_ifs
  · exact Or.inl rfl
  · cases t
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

@[expose] def lengthCol : Idx t.tag.rootCertificate → Col t.tag.rootCertificate
  | .inl j => if j ∈ t.longSet then some (.inl (t.perm j), 1) else none
  | .inr m =>
    if t.quadForm (t.tag.rootCertificate.root m) = 2 * t.prime then
      scaleCol _ (t.sign (t.tag.rootCertificate.root m))
        (rootCol _ t.tag.stringData (t.dualRoot (t.tag.rootCertificate.root m)))
    else none

variable {t} (R : Type*) [CommRing R]

theorem lengthMap_toLabel (b : Idx t.tag.rootCertificate) :
    t.lengthMap R (Finsupp.single (toLabel t.tag.rootCertificate_check b) 1) =
      toVec t.tag.rootCertificate_check R (t.lengthCol b) := by
  rcases b with j | m
  · rw [single_toLabel_inl]
    simp only [lengthCol]
    by_cases hj : j ∈ t.longSet
    · rw [lengthMap_hVec_of_mem hj, ite_eq_left hj, toVec_some, Int.cast_one, one_smul,
        single_toLabel_inl]
    · rw [lengthMap_hVec_of_notMem hj, ite_eq_right hj, toVec_none]
  · rw [single_toLabel_inr]
    simp only [lengthCol]
    have hα := RootCertificate.isRoot_root t.tag.rootCertificate_check m m.2
    by_cases hl : t.quadForm (t.tag.rootCertificate.root m) = 2 * t.prime
    · rw [lengthMap_rootVec_of_mem_longRoots ⟨hα, lengthParam_eq_prime_iff.2 hl⟩,
        ite_eq_left hl, toVec_scaleCol, toVec_rootCol _ R t.tag.stringData_check]
    · have hs : t.tag.rootCertificate.root m ∈ t.shortRoots :=
        ⟨hα, (lengthParam_eq_one_iff_ne hα).2 (mt lengthParam_eq_prime_iff.1 hl)⟩
      rw [lengthMap_rootVec_of_mem_shortRoots hs, ite_eq_right hl, toVec_none]

variable (t) in
@[expose] def coeffCheck
    (X : Fin t.tag.rank → ℕ → Idx t.tag.rootCertificate → Col t.tag.rootCertificate)
    (i : Fin t.tag.rank) : Bool :=
  [1, 2, 3].all (fun k => opEq _ t.prime (fun a => bindCol _ t.lengthCol (X i k a))
      (if t.exponent i ∣ k then
        fun a => bindCol _ (X (t.perm i) (k / t.exponent i)) (t.lengthCol a)
      else fun _ => none)) &&
    [1, 2, 3].all fun k => !decide (3 < t.exponent i * k) ||
      opEq _ t.prime (fun a => bindCol _ (X (t.perm i) k) (t.lengthCol a)) fun _ => none

variable (t) in
@[expose] def intertwinerCheck : Bool :=
  (List.finRange t.tag.rank).all fun i =>
    t.coeffCheck (xCol t.tag.rootCertificate t.tag.stringData) i &&
      t.coeffCheck (yCol t.tag.rootCertificate t.tag.stringData) i

theorem intertwinerCheck_eq_true (t : ReeTag) : t.intertwinerCheck = true := by
  cases t <;> decide +kernel

theorem coeffCheck_xCol (t : ReeTag) (i : Fin t.tag.rank) :
    t.coeffCheck (xCol t.tag.rootCertificate t.tag.stringData) i = true := by
  have h := t.intertwinerCheck_eq_true
  simp only [intertwinerCheck, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.and_eq_true] at h
  exact (h i).1

theorem coeffCheck_yCol (t : ReeTag) (i : Fin t.tag.rank) :
    t.coeffCheck (yCol t.tag.rootCertificate t.tag.stringData) i = true := by
  have h := t.intertwinerCheck_eq_true
  simp only [intertwinerCheck, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.and_eq_true] at h
  exact (h i).2

theorem lengthMap_mul_eq_of_coeffCheck
    {X : Fin t.tag.rank → ℕ → Idx t.tag.rootCertificate → Col t.tag.rootCertificate}
    {Xop : Fin t.tag.rank → ℕ → Module.End R (RootModule t.tag R)}
    (hX : ∀ i k a, Xop i k (Finsupp.single (toLabel t.tag.rootCertificate_check a) 1) =
      toVec t.tag.rootCertificate_check R (X i k a))
    (hp : (t.prime : R) = 0) {i : Fin t.tag.rank} (h : t.coeffCheck X i = true) :
    (∀ k ∈ [1, 2, 3], t.lengthMap R * Xop i k =
      if t.exponent i ∣ k then Xop (t.perm i) (k / t.exponent i) * t.lengthMap R else 0) ∧
    ∀ k ∈ [1, 2, 3], 3 < t.exponent i * k → Xop (t.perm i) k * t.lengthMap R = 0 := by
  have hC := t.tag.rootCertificate_check
  have hP := lengthMap_toLabel (t := t) R
  simp only [coeffCheck, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, not_lt] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun k hk => ?_, fun k hk hbk => ?_⟩
  · have h1k := h1 k hk
    split_ifs at h1k ⊢
    · exact ext_of_opEq hC R hp
        (fun a => by rw [Module.End.mul_apply, hX, map_toVec hC R hP])
        (fun a => by rw [Module.End.mul_apply, hP, map_toVec hC R (hX _ _)]) h1k
    · exact ext_of_opEq hC R hp
        (fun a => by rw [Module.End.mul_apply, hX, map_toVec hC R hP])
        (fun a => by rw [LinearMap.zero_apply, toVec_none]) h1k
  · rcases h2 k hk with h | h
    · omega
    · exact ext_of_opEq hC R hp
        (fun a => by rw [Module.End.mul_apply, hP, map_toVec hC R (hX _ _)])
        (fun a => by rw [LinearMap.zero_apply, toVec_none]) h

theorem sum_range_four_smul_eq {M : Type*} [AddCommMonoid M] [Module R M]
    {a b : ℕ → M} {e : ℕ} (he : e = 1 ∨ e = 2 ∨ e = 3) (h0 : a 0 = b 0)
    (ha : ∀ k ∈ [1, 2, 3], a k = if e ∣ k then b (k / e) else 0)
    (hb : ∀ k ∈ [1, 2, 3], 3 < e * k → b k = 0) (c : R) :
    ∑ k ∈ Finset.range 4, c ^ k • a k = ∑ k ∈ Finset.range 4, (c ^ e) ^ k • b k := by
  have h1 := ha 1 (by simp)
  have h2 := ha 2 (by simp)
  have h3 := ha 3 (by simp)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, h0]
  rcases he with rfl | rfl | rfl
  · simp only [one_dvd, ite_true, Nat.div_one] at h1 h2 h3
    simp only [pow_one, h1, h2, h3]
  · have hb2 := hb 2 (by simp) (by norm_num)
    have hb3 := hb 3 (by simp) (by norm_num)
    norm_num at h1 h2 h3
    rw [h1, h2, h3, hb2, hb3]
    simp [← pow_mul]
  · have hb2 := hb 2 (by simp) (by norm_num)
    have hb3 := hb 3 (by simp) (by norm_num)
    norm_num at h1 h2 h3
    rw [h1, h2, h3, hb2, hb3]
    simp [← pow_mul]

theorem lengthMap_mul_xOp (hp : (t.prime : R) = 0) (i : Fin t.tag.rank) (c : R) :
    t.lengthMap R * xOp t.tag R i c =
      xOp t.tag R (t.perm i) (c ^ t.exponent i) * t.lengthMap R := by
  obtain ⟨ha, hb⟩ := lengthMap_mul_eq_of_coeffCheck R
    (xCoeff_toLabel t.tag.rootCertificate_check R t.tag.stringData_check) hp
    (t.coeffCheck_xCol i)
  rw [xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_smul_comm, smul_mul_assoc]
  exact sum_range_four_smul_eq R (t.exponent_eq i)
    (by rw [xCoeff_zero, xCoeff_zero, mul_one, one_mul]) ha hb c

theorem lengthMap_mul_yOp (hp : (t.prime : R) = 0) (i : Fin t.tag.rank) (c : R) :
    t.lengthMap R * yOp t.tag R i c =
      yOp t.tag R (t.perm i) (c ^ t.exponent i) * t.lengthMap R := by
  obtain ⟨ha, hb⟩ := lengthMap_mul_eq_of_coeffCheck R
    (yCoeff_toLabel t.tag.rootCertificate_check R t.tag.stringData_check) hp
    (t.coeffCheck_yCol i)
  rw [yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_smul_comm, smul_mul_assoc]
  exact sum_range_four_smul_eq R (t.exponent_eq i)
    (by rw [yCoeff_zero, yCoeff_zero, mul_one, one_mul]) ha hb c

theorem ker_lengthMap : LinearMap.ker (t.lengthMap R) = t.shortModule R := by
  rw [lengthMap_eq_signedSwap,
    ker_signedSwap fun b => IsUnit.of_mul_eq_one _ (labelSign_mul_self b),
    shortModule_eq_supported]
  rfl

theorem range_lengthMap : LinearMap.range (t.lengthMap R) = t.shortModule R := by
  rw [lengthMap_eq_signedSwap, range_signedSwap isShortLabel_dualLabel labelSign_mul_self,
    shortModule_eq_supported]
  rfl

theorem lengthMap_mul_self : t.lengthMap R * t.lengthMap R = 0 := by
  rw [lengthMap_eq_signedSwap]
  exact signedSwap_mul_self isShortLabel_dualLabel labelSign_mul_self

theorem exists_shortModule_equiv :
    ∃ (f : Fin t.shortDim ≃ t.shortLabels) (e : t.shortModule R ≃ₗ[R] (Fin t.shortDim → R)),
      ∀ k, (e.symm (Pi.single k 1) : RootModule t.tag R) = Finsupp.single (f k).1 1 := by
  let f : Fin t.shortDim ≃ t.shortLabels :=
    (finCongr (card_shortLabels t).symm).trans (Finite.equivFin _).symm
  refine ⟨f, ((t.shortBasis R).reindex f.symm).equivFun, fun k => ?_⟩
  rw [Module.Basis.equivFun_symm_apply]
  simp [Pi.single_apply, coe_shortBasis]

theorem xOp_mem_shortModule (hp : (t.prime : R) = 0) (i : Fin t.tag.rank) (c : R)
    {v : RootModule t.tag R} (hv : v ∈ t.shortModule R) :
    xOp t.tag R i c v ∈ t.shortModule R := by
  rw [← ker_lengthMap, LinearMap.mem_ker] at hv ⊢
  rw [← Module.End.mul_apply, lengthMap_mul_xOp R hp, Module.End.mul_apply, hv, map_zero]

theorem yOp_mem_shortModule (hp : (t.prime : R) = 0) (i : Fin t.tag.rank) (c : R)
    {v : RootModule t.tag R} (hv : v ∈ t.shortModule R) :
    yOp t.tag R i c v ∈ t.shortModule R := by
  rw [← ker_lengthMap, LinearMap.mem_ker] at hv ⊢
  rw [← Module.End.mul_apply, lengthMap_mul_yOp R hp, Module.End.mul_apply, hv, map_zero]

theorem map_xOp_shortModule (hp : (t.prime : R) = 0) (i : Fin t.tag.rank) (c : R) :
    (t.shortModule R).map (xOp t.tag R i c) = t.shortModule R := by
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact xOp_mem_shortModule R hp i c hv
  · refine ⟨xOp t.tag R i (-c) v, xOp_mem_shortModule R hp i (-c) hv, ?_⟩
    rw [← Module.End.mul_apply,
      ((simple_root_parameter_addition_of_tag t.tag R i).2.2.2.2.1 c).1, Module.End.one_apply]

theorem map_yOp_shortModule (hp : (t.prime : R) = 0) (i : Fin t.tag.rank) (c : R) :
    (t.shortModule R).map (yOp t.tag R i c) = t.shortModule R := by
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact yOp_mem_shortModule R hp i c hv
  · refine ⟨yOp t.tag R i (-c) v, yOp_mem_shortModule R hp i (-c) hv, ?_⟩
    rw [← Module.End.mul_apply,
      ((simple_root_parameter_addition_of_tag t.tag R i).2.2.2.2.2.1 c).1, Module.End.one_apply]

end ReeTag

open ReeTag

theorem exceptional_polynomial_intertwiner (t : ReeTag) (R : Type*) [CommRing R]
    (hp : (t.prime : R) = 0) :
    (∃ (f : Fin t.shortDim ≃ t.shortLabels) (e : t.shortModule R ≃ₗ[R] (Fin t.shortDim → R)),
      ∀ k, (e.symm (Pi.single k 1) : RootModule t.tag R) = Finsupp.single (f k).1 1) ∧
    LinearMap.ker (t.lengthMap R) = t.shortModule R ∧
    LinearMap.range (t.lengthMap R) = t.shortModule R ∧
    t.lengthMap R * t.lengthMap R = 0 ∧
    (∀ (i : Fin t.tag.rank) (c : R),
      (t.shortModule R).map (xOp t.tag R i c) = t.shortModule R ∧
        (t.shortModule R).map (yOp t.tag R i c) = t.shortModule R) ∧
    ∀ (i : Fin t.tag.rank) (c : R),
      t.lengthMap R * xOp t.tag R i c =
          xOp t.tag R (t.perm i) (c ^ t.exponent i) * t.lengthMap R ∧
        t.lengthMap R * yOp t.tag R i c =
          yOp t.tag R (t.perm i) (c ^ t.exponent i) * t.lengthMap R :=
  ⟨exists_shortModule_equiv R, ker_lengthMap R, range_lengthMap R, lengthMap_mul_self R,
    fun i c => ⟨map_xOp_shortModule R hp i c, map_yOp_shortModule R hp i c⟩,
    fun i c => ⟨lengthMap_mul_xOp R hp i c, lengthMap_mul_yOp R hp i c⟩⟩

end CFSG.LieType.Ree
