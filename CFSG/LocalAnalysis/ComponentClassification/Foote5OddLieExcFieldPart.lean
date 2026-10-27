module

public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Polynomial CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem exists_lt_apply_eq_pow {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (φ : K ≃+* K) : ∃ m < f, ∀ s, φ s = s ^ (p ^ m) := by
  obtain ⟨σ, hσ, hord, htop, -, -⟩ :=
    LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hf hK
  have hφ : φ ∈ Subgroup.zpowers σ := htop ▸ Subgroup.mem_top φ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
  have hf0 : (0 : ℤ) < (f : ℤ) := by omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = k % (f : ℤ) :=
    ⟨(k % (f : ℤ)).toNat, Int.toNat_of_nonneg (Int.emod_nonneg k hf0.ne')⟩
  refine ⟨m, ?_, fun s => ?_⟩
  · have h1 := Int.emod_lt_of_pos k hf0
    omega
  · rw [← zpow_mod_orderOf, hord, ← hm, zpow_natCast, ringAut_pow_apply_of_frobenius hσ]

theorem infE_ne_zero
    (i : Fin τ.rank) : infE τ K i ≠ 0 := by
  intro h
  have h1 := infE_rootVec_neg_single (τ := τ) (R := K) i
  rw [h, LinearMap.zero_apply] at h1
  have h2 : hVec τ K i ≠ 0 := by
    change Finsupp.single (Sum.inl i) (1 : K) ≠ 0
    exact Finsupp.single_ne_zero.2 one_ne_zero
  exact h2 h1.symm

theorem eq_zero_of_entries {M : Module.End K (RootModule τ K)}
    (h : ∀ a b, M (Finsupp.single b 1) a = 0) : M = 0 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  rw [LinearMap.comp_apply, Finsupp.lsingle_apply, h a b]
  simp

theorem eq_one_of_conj_xUnit
    [Finite K] (hD : entryDegreeBound τ < ringChar K) {y : ModGL τ K} {φ : K ≃+* K}
    (i : Fin τ.rank) (h : ∀ s : K, y * xUnit τ K i (φ s) * y⁻¹ = xUnit τ K i s) : φ = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨m, hmf, hφ⟩ := exists_lt_apply_eq_pow hp f.pos hK φ
  by_cases hm : m = 0
  · subst hm
    refine RingEquiv.ext fun s => ?_
    rw [hφ, pow_zero, pow_one, RingAut.one_apply]
  exfalso
  have hyX : ∀ s : K, (y : Module.End K (RootModule τ K)) *
      (xUnit τ K i (φ s) : Module.End K (RootModule τ K)) =
        (xUnit τ K i s : Module.End K (RootModule τ K)) * y := fun s => by
    have h1 : y * xUnit τ K i (φ s) = xUnit τ K i s * y := by
      calc y * xUnit τ K i (φ s) = (y * xUnit τ K i (φ s) * y⁻¹) * y := by group
        _ = xUnit τ K i s * y := by rw [h s]
    exact congrArg Units.val h1
  have hX : ∀ s : K, (xUnit τ K i s : Module.End K (RootModule τ K)) =
      ∑ k ∈ Finset.range (entryDegreeBound τ + 1), s ^ k • xCoeff τ K i k := fun s => by
    rw [coe_xUnit, xOp_eq_sum_xCoeff_entryDegreeBound]
  have hD1 : 1 ≤ entryDegreeBound τ := by
    unfold entryDegreeBound
    split_ifs <;> omega
  have hp3 : 3 ≤ ringChar K := by
    unfold entryDegreeBound at hD
    split_ifs at hD <;> omega
  have hpm : 3 ≤ ringChar K ^ m :=
    hp3.trans (Nat.le_self_pow hm (ringChar K))
  have hdeg : entryDegreeBound τ * ringChar K ^ m < Fintype.card K := by
    rw [hcard]
    calc entryDegreeBound τ * ringChar K ^ m < ringChar K * ringChar K ^ m :=
          Nat.mul_lt_mul_of_pos_right hD (pow_pos hp.pos m)
      _ = ringChar K ^ (m + 1) := by ring
      _ ≤ ringChar K ^ (f : ℕ) := Nat.pow_le_pow_right hp.pos hmf
  have hent : ∀ a b, (xCoeff τ K i 1 * (y : Module.End K (RootModule τ K)))
      (Finsupp.single b 1) a = 0 := by
    intro a b
    let ε : Module.End K (RootModule τ K) →ₗ[K] K :=
      (Finsupp.lapply a).comp (LinearMap.applyₗ (Finsupp.single b 1))
    set P : K[X] := ∑ k ∈ Finset.range (entryDegreeBound τ + 1),
      (C (ε ((y : Module.End K (RootModule τ K)) * xCoeff τ K i k)) * X ^ (k * ringChar K ^ m) -
        C (ε (xCoeff τ K i k * (y : Module.End K (RootModule τ K)))) * X ^ k) with hP
    have hPeval : ∀ s : K, P.eval s = 0 := by
      intro s
      have h1 := congrArg ε (hyX s)
      rw [hX, hX, Finset.mul_sum, Finset.sum_mul, map_sum, map_sum] at h1
      simp only [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul, hφ] at h1
      rw [hP, eval_finsetSum]
      simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
      rw [Finset.sum_sub_distrib, sub_eq_zero]
      refine (Finset.sum_congr rfl fun k _ => ?_).trans (h1.trans (Finset.sum_congr rfl
        fun k _ => mul_comm _ _))
      rw [mul_comm, ← pow_mul, mul_comm (ringChar K ^ m) k]
    have hPdeg : P.natDegree < Fintype.card K := by
      refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun k hk => ?_) hdeg
      have hk' : k ≤ entryDegreeBound τ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.mul_le_mul_right _ hk')
      · refine (natDegree_C_mul_X_pow_le _ _).trans ?_
        calc k ≤ entryDegreeBound τ := hk'
          _ ≤ entryDegreeBound τ * ringChar K ^ m :=
            Nat.le_mul_of_pos_right _ (pow_pos hp.pos m)
    have hP0 : P = 0 :=
      eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := id) Function.injective_id
        (fun s => hPeval s) hPdeg
    have h1 := congrArg (fun Q : K[X] => Q.coeff 1) hP0
    simp only [hP, finsetSum_coeff, coeff_sub, coeff_C_mul_X_pow, coeff_zero] at h1
    rw [Finset.sum_sub_distrib] at h1
    have h2 : ∑ k ∈ Finset.range (entryDegreeBound τ + 1),
        (if 1 = k * ringChar K ^ m then
          ε ((y : Module.End K (RootModule τ K)) * xCoeff τ K i k) else 0) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ite_eq_right fun hk => ?_
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · omega
      · have : ringChar K ^ m ≤ k * ringChar K ^ m := Nat.le_mul_of_pos_left _ hk0
        omega
    rw [h2, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.2 (by omega)), zero_sub,
      neg_eq_zero] at h1
    exact h1
  have h3 : xCoeff τ K i 1 * (y : Module.End K (RootModule τ K)) = 0 := eq_zero_of_entries hent
  have h4 : xCoeff τ K i 1 = 0 := by
    have := congrArg (· * ((y⁻¹ : ModGL τ K) : Module.End K (RootModule τ K))) h3
    simpa [mul_assoc] using this
  rw [xCoeff_one] at h4
  exact infE_ne_zero i h4

theorem eq_one_of_conj_pinnedX
    [Finite K] (hD : entryDegreeBound τ < ringChar K) {y : ModGL τ K} {φ : K ≃+* K}
    (β : Fin τ.rank → ℤ) (h : ∀ t : K, y * pinnedX τ K β (φ t) * y⁻¹ = pinnedX τ K β t) :
    φ = 1 := by
  have hεε : ∀ s : K, (pinnedData τ β).2.2 • ((pinnedData τ β).2.2 • s) = s := fun s => by
    rcases pinnedSign_eq τ β with he | he <;> rw [he] <;> simp
  have hX : ∀ c : K, pinnedX τ K β c = pinnedWeyl τ K β *
      xUnit τ K (pinnedData τ β).1 ((pinnedData τ β).2.2 • c) * (pinnedWeyl τ K β)⁻¹ :=
    fun c => rfl
  refine eq_one_of_conj_xUnit hD (y := (pinnedWeyl τ K β)⁻¹ * y * pinnedWeyl τ K β)
    (pinnedData τ β).1 fun s => ?_
  have h1 := h ((pinnedData τ β).2.2 • s)
  rw [hX, hX, map_zsmul, hεε, hεε] at h1
  calc (pinnedWeyl τ K β)⁻¹ * y * pinnedWeyl τ K β * xUnit τ K (pinnedData τ β).1 (φ s) *
        ((pinnedWeyl τ K β)⁻¹ * y * pinnedWeyl τ K β)⁻¹ =
      (pinnedWeyl τ K β)⁻¹ * (y * (pinnedWeyl τ K β * xUnit τ K (pinnedData τ β).1 (φ s) *
        (pinnedWeyl τ K β)⁻¹) * y⁻¹) * pinnedWeyl τ K β := by group
    _ = (pinnedWeyl τ K β)⁻¹ * (pinnedWeyl τ K β * xUnit τ K (pinnedData τ β).1 s *
        (pinnedWeyl τ K β)⁻¹) * pinnedWeyl τ K β := by rw [h1]
    _ = xUnit τ K (pinnedData τ β).1 s := by group

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
