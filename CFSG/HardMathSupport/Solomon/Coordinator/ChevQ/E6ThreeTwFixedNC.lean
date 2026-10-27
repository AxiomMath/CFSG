module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnerHeis
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSingerU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartTwo.KFacts CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec4 (PiField ModThree glPi slPi qSubPi piCard mem_glPi_false
  card_centralizer_glPi_false card_centralizer_slPi_mul)

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem twFixedNC_norm_of_cube (h : UnitaryFieldData ℓ f K) (γ : unitaryIsom3 h) {c : K}
    (hc : ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = c • 1) : h.bar c * c = 1 := by
  have h1 := mem_unitaryIsom3.1 (γ ^ 3).2
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hc] at h1
  have h2 := congrFun (congrFun h1 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h2
  linear_combination h2

theorem twFixedNC_isDiag_comm_hD {Y : Matrix (Fin 3) (Fin 3) K} (hY : Y.IsDiag) (ω : K) :
    Y * hD ω = hD ω * Y := by
  have hD' : hD ω = diagonal ![1, ω, ω ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hD]
  rw [← (isDiag_iff_diagonal_diag Y).1 hY, hD', diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

theorem twFixedNC_commute_conj {Pm Pi X D : Matrix (Fin 3) (Fin 3) K} (hPPi : Pm * Pi = 1)
    (hXD : Pi * X * Pm * D = D * (Pi * X * Pm)) :
    X * (Pm * D * Pi) = Pm * D * Pi * X := by
  calc X * (Pm * D * Pi) = Pm * (Pi * X * Pm * D) * Pi := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Pm Pi, hPPi, Matrix.one_mul]
    _ = Pm * (D * (Pi * X * Pm)) * Pi := by rw [hXD]
    _ = Pm * D * Pi * X := by
        simp only [Matrix.mul_assoc]
        rw [hPPi, Matrix.mul_one]

theorem twFixedNC_eq_smul_of_conj {Pm Pi M : Matrix (Fin 3) (Fin 3) K} (hPiP : Pi * Pm = 1)
    {c : K} (hM : Pm * M * Pi = c • 1) : M = c • 1 := by
  calc M = Pi * (Pm * M * Pi) * Pm := by
        simp only [Matrix.mul_assoc]
        rw [hPiP, Matrix.mul_one, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
    _ = c • 1 := by rw [hM, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPiP]

theorem twFixedNC_commute_conj_hD {P x : GL (Fin 3) K} (ω : K)
    (hx : ((P⁻¹ * x * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    (x : Matrix (Fin 3) (Fin 3) K) * ((P : Matrix (Fin 3) (Fin 3) K) * hD ω *
      ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      (P : Matrix (Fin 3) (Fin 3) K) * hD ω * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (x : Matrix (Fin 3) (Fin 3) K) := by
  rw [Units.val_mul, Units.val_mul] at hx
  exact twFixedNC_commute_conj (Units.mul_inv P) (twFixedNC_isDiag_comm_hD hx ω)

theorem twFixedNC_toral (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) (hq : 2 < ℓ ^ f)
    (γ : unitaryIsom3 h) {μ : K} (hμ0 : μ ≠ 0) (hμN : h.bar μ * μ = 1)
    (hγ3 : ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = μ ^ 3 • 1) :
    ∃ k : unitarySU ℓ f K 3, k ∉ Subgroup.center (unitarySU ℓ f K 3) ∧ suConj h γ k = k := by
  have hμi0 : μ⁻¹ ≠ 0 := inv_ne_zero hμ0
  have hμiN : h.bar μ⁻¹ * μ⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, hμN, inv_one]
  obtain ⟨x, hx⟩ : ∃ x : primeFormUnitary h (idGram K 3), (x : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ⁻¹ hμi0) * (γ : GL (Fin 3) K) :=
    ⟨⟨_, smul_mem_primeFormUnitary h (mem_primeFormUnitary_one γ.2) hμi0 hμiN⟩, rfl⟩
  have hxm : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      μ⁻¹ • ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hx, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  have hγx : ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      μ • ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hxm, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hxm, smul_pow, hγ3, smul_smul, ← mul_pow,
      inv_mul_cancel₀ hμ0, one_pow, one_smul, Subgroup.coe_one, Units.val_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h Nat.prime_three hq3 (Subgroup.zpowers x)
    (fun a ha b hb => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact zpow_mul_comm x i j)
    (fun a ha => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx3,
        _root_.one_zpow])
  have hy := hP x (Subgroup.mem_zpowers x)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hy
  obtain ⟨ω, hω⟩ := exists_isPrimitiveRoot h Nat.prime_three hq3
  obtain ⟨d, hd⟩ := twInnerHeis_exists_su_hD h hq3 hω.pow_eq_one
  refine ⟨conjSU h P d, fun hk => ?_, ?_⟩
  · rw [center_unitarySU_three (h := h) hq] at hk
    obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.1 hk
    have hm := congrArg Units.val hc
    rw [coe_conjSU, Units.val_mul, Units.val_mul, hd, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal] at hm
    have hD1 := twFixedNC_eq_smul_of_conj (Units.inv_mul _) hm
    have hω1 : ω = 1 := by
      have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 1 - M 0 0) hD1
      simpa [hD, sub_eq_zero] using h11
    exact hω.ne_one (by norm_num) hω1
  · apply Subtype.ext
    rw [coe_suConj, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_conjSU, Units.val_mul, Units.val_mul, hd, hγx,
      Matrix.smul_mul, Matrix.mul_smul, twFixedNC_commute_conj_hD ω hy]

theorem twFixedNC_singer (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) (hq : 5 ≤ ℓ ^ f)
    (γ : unitaryIsom3 h) {c : K} (hc : ∀ μ : K, μ ^ 3 ≠ c)
    (hγ3 : ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = c • 1) :
    ∃ k : unitarySU ℓ f K 3, k ∉ Subgroup.center (unitarySU ℓ f K 3) ∧ suConj h γ k = k := by
  have hK : PiField false ℓ f K :=
    ⟨h.prime, h.one_le, by rw [h.card, piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩
  have hmod : ModThree false (ℓ ^ f) := by
    change ℓ ^ f % 3 = 2
    omega
  have hyH : (γ : GL (Fin 3) K) ∈ glPi false 3 (ℓ ^ f) K :=
    (mem_glPi_false h).2 (mem_unitaryIsom3.1 γ.2)
  have hcard := card_centralizer_slPi_mul hK hmod hyH hc hγ3
  rw [card_centralizer_glPi_false hK hmod hyH hc hγ3] at hcard
  change Nat.card _ * (ℓ ^ f + 1) = _ at hcard
  by_contra hall
  haveI := h.finite
  haveI : Finite (GL (Fin 3) K) :=
    Finite.of_injective (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) Units.val_injective
  let φ : ↥(slPi false 3 (ℓ ^ f) K ⊓ Subgroup.centralizer {(γ : GL (Fin 3) K)}) →
      Subgroup.center (unitarySU ℓ f K 3) := fun g =>
    ⟨⟨(g : GL (Fin 3) K), (Subgroup.mem_inf.1 g.2).1⟩, by
      by_contra hg
      refine hall ⟨⟨(g : GL (Fin 3) K), (Subgroup.mem_inf.1 g.2).1⟩, hg, Subtype.ext ?_⟩
      rw [coe_suConj, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2).symm⟩
  have hinj : Function.Injective φ := fun a b hab => by
    apply Subtype.ext
    exact congrArg (fun z : Subgroup.center (unitarySU ℓ f K 3) =>
      ((z : unitarySU ℓ f K 3) : GL (Fin 3) K)) hab
  have hle : Nat.card ↥(slPi false 3 (ℓ ^ f) K ⊓
      Subgroup.centralizer {(γ : GL (Fin 3) K)}) ≤ 3 := by
    calc _ ≤ Nat.card (Subgroup.center (unitarySU ℓ f K 3)) :=
          Nat.card_le_card_of_injective φ hinj
      _ = Nat.card (unitaryScalars h 3) := by rw [center_unitarySU_three (h := h) (by omega)]
      _ = 3 := by rw [card_unitaryScalars h (n := 3) (by norm_num)]; exact Nat.gcd_eq_left hq3
  have h1 : (ℓ ^ f) ^ 3 + 1 ≤ 3 * (ℓ ^ f + 1) := by
    rw [← hcard]
    exact Nat.mul_le_mul hle le_rfl
  have h2 : 25 * ℓ ^ f ≤ (ℓ ^ f) ^ 3 := by
    have h5 : 5 * 5 ≤ ℓ ^ f * ℓ ^ f := Nat.mul_le_mul hq hq
    calc 25 * ℓ ^ f ≤ ℓ ^ f * ℓ ^ f * ℓ ^ f := Nat.mul_le_mul h5 le_rfl
      _ = (ℓ ^ f) ^ 3 := by ring
  omega

theorem twFixedNonCentral_holds : TwFixedNonCentral := by
  intro ℓ f K _ h hq3 hq γ hγ3
  have hq5 : 5 ≤ ℓ ^ f := by omega
  obtain ⟨c, hc⟩ := twInnerHeis_smul_one_of_suConj_eq_one (A := γ ^ 3) (by rw [map_pow, hγ3])
  have hc' : ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = c • 1 := by
    rw [← hc, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  by_cases hcube : ∃ μ : K, μ ^ 3 = c
  · obtain ⟨μ, rfl⟩ := hcube
    have hN := twFixedNC_norm_of_cube h γ hc'
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      simp at hN
    have hμN := bar_mul_eq_one_of_cube h hq3 hμ0 rfl (by rwa [h.bar_apply, ← pow_succ] at hN)
    exact twFixedNC_toral h hq3 (by omega) γ hμ0 hμN hc'
  · exact twFixedNC_singer h hq3 hq5 γ (fun μ hμ => hcube ⟨μ, hμ⟩) hc'

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
