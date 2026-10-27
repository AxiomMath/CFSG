module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwPlaneStmt
public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreMain
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartTwo.KFacts CFSG.LieType.SeitzGeneration

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem twInnerHeis_suConj_su (h : UnitaryFieldData ℓ f K) (x : unitarySU ℓ f K 3) :
    suConj h ⟨x, unitarySU_le_unitaryIsom3 (h := h) x.2⟩ = MulAut.conj x :=
  MulEquiv.ext fun _ => Subtype.ext rfl

theorem twInnerHeis_smul_one_of_suConj_eq_one {h : UnitaryFieldData ℓ f K} {A : unitaryIsom3 h}
    (hA : suConj h A = 1) :
    ∃ c : K, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
  have hpsu : psuConj h A = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g => rw [psuConj_mk, hA]; rfl
  obtain ⟨-, c, -, hc⟩ :=
    eq_one_of_psuConj_mul_psuField_eq_one A 1 (by rw [map_one, mul_one]; exact hpsu)
  refine ⟨(c : K), ?_⟩
  rw [hc]
  simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem twInnerHeis_smul_of_suConj_eq_conj {h : UnitaryFieldData ℓ f K} {γ : unitaryIsom3 h}
    {x : unitarySU ℓ f K 3} (hγ : suConj h γ = MulAut.conj x) :
    ∃ c : K, ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  set y : unitaryIsom3 h := ⟨x, unitarySU_le_unitaryIsom3 (h := h) x.2⟩ with hy
  obtain ⟨c, hc⟩ := twInnerHeis_smul_one_of_suConj_eq_one (A := γ * y⁻¹)
    (by rw [map_mul, map_inv, hy, twInnerHeis_suConj_su, hγ, mul_inv_cancel])
  refine ⟨c, ?_⟩
  have h1 : (γ : GL (Fin 3) K) = ((γ * y⁻¹ : unitaryIsom3 h) : GL (Fin 3) K) * x := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hy, inv_mul_cancel_right]
  rw [h1, Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul]

theorem twInnerHeis_smul_of_conj_eq_conj (h : UnitaryFieldData ℓ f K) {u v : unitarySU ℓ f K 3}
    (huv : MulAut.conj u = MulAut.conj v) :
    ∃ c : K, ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • ((v : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  twInnerHeis_smul_of_suConj_eq_conj (h := h) (γ := ⟨u, unitarySU_le_unitaryIsom3 (h := h) u.2⟩)
    (by rw [twInnerHeis_suConj_su, huv])

theorem twInnerHeis_exists_su_hD (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) {ω : K}
    (hω3 : ω ^ 3 = 1) :
    ∃ g : unitarySU ℓ f K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hD ω := by
  have hbω : h.bar ω = ω ^ 2 := bar_eq_sq_of_cube h hq3 hω3
  have hU : ((hD ω).map h.bar)ᵀ * hD ω = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hD, Matrix.mul_apply, Fin.sum_univ_three, hbω] <;> grind
  have hd : (hD ω).det = 1 := by
    simp [hD, Matrix.det_fin_three]
    grind
  exact ⟨⟨⟨hD ω, ((hD ω).map h.bar)ᵀ, mul_eq_one_comm.2 hU, hU⟩,
    (mem_unitarySU_iff h).2 ⟨hd, hU⟩⟩, rfl⟩

theorem twInnerHeis_hS_hD {ω : K} (hω3 : ω ^ 3 = 1) :
    (hS : Matrix (Fin 3) (Fin 3) K) * hD ω = ω ^ 2 • (hD ω * hS) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hS, hD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem twInnerHeis_hD_hS {ω : K} (hω3 : ω ^ 3 = 1) :
    hD ω * (hS : Matrix (Fin 3) (Fin 3) K) = ω • (hS * hD ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hS, hD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem twInnerHeis_hD_hDhS {ω : K} (hω3 : ω ^ 3 = 1) :
    hD ω * (hD ω * (hS : Matrix (Fin 3) (Fin 3) K)) = ω • (hD ω * hS * hD ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hS, hD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem twInnerHeis_hD_hDhShS {ω : K} (hω3 : ω ^ 3 = 1) :
    hD ω * (hD ω * (hS : Matrix (Fin 3) (Fin 3) K) * hS) = ω ^ 2 • (hD ω * hS * hS * hD ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hS, hD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem twInnerHeis_mul_smul_comm {A G M : Matrix (Fin 3) (Fin 3) K} {α β : K}
    (hA : A * M = α • (M * A)) (hG : G * M = β • (M * G)) :
    A * G * M = (α * β) • (M * (A * G)) := by
  rw [Matrix.mul_assoc, hG, Matrix.mul_smul, ← Matrix.mul_assoc, hA, Matrix.smul_mul, smul_smul,
    Matrix.mul_assoc, mul_comm β α]

theorem twInnerHeis_cube_eq_one (h : UnitaryFieldData ℓ f K) {g m : unitarySU ℓ f K 3}
    {M : Matrix (Fin 3) (Fin 3) K} (hm : ((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = M)
    {c : K} (hc : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
      c • (M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) : c ^ 3 = 1 := by
  have hg1 := ((mem_unitarySU_iff h).1 g.2).1
  have hm1 := ((mem_unitarySU_iff h).1 m.2).1
  rw [hm] at hm1
  have h1 := congrArg Matrix.det hc
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, hg1, hm1, Fintype.card_fin] at h1
  simpa using h1.symm

theorem twInnerHeis_mem_of_mul_eq_smul {M : Matrix (Fin 3) (Fin 3) K} {μ : K}
    (hμ : IsPrimitiveRoot μ 3) {a : unitarySU ℓ f K 3}
    (haM : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
      μ • (M * ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
    {H : Subgroup (unitarySU ℓ f K 3)} (hH : ∀ g : unitarySU ℓ f K 3,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
        M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → g ∈ H)
    (ha : a ∈ H) {g : unitarySU ℓ f K 3} {c : K} (hc : c ^ 3 = 1)
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
      c • (M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) : g ∈ H := by
  obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one hc
  have hpow : ∀ n : ℕ, (((a ^ n : unitarySU ℓ f K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) * M = μ ^ n • (M * (((a ^ n : unitarySU ℓ f K 3) :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Subgroup.coe_mul, Units.val_mul, pow_succ']
      exact twInnerHeis_mul_smul_comm haM ih
  have hμi : μ ^ (2 * i) * μ ^ i = 1 := by
    rw [← pow_add, show 2 * i + i = 3 * i by ring, pow_mul, hμ.pow_eq_one, one_pow]
  have h1 : a ^ (2 * i) * g ∈ H := by
    apply hH
    rw [Subgroup.coe_mul, Units.val_mul, twInnerHeis_mul_smul_comm (hpow (2 * i)) hg, hμi,
      one_smul]
  have h2 := H.mul_mem (H.inv_mem (H.pow_mem ha (2 * i))) h1
  rwa [inv_mul_cancel_left] at h2

theorem twInnerHeis_closure_exact (hcore : UnitaryHeisCore) (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) {ω : K} (hω : IsPrimitiveRoot ω 3) :
    Subgroup.closure {g : unitarySU ℓ f K 3 | ∃ M ∈ heisLines ω,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
        M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)} = ⊤ := by
  set H := Subgroup.closure {g : unitarySU ℓ f K 3 | ∃ M ∈ heisLines ω,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
        M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)} with hH
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hex : ∀ M ∈ heisLines ω, ∀ g : unitarySU ℓ f K 3,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
        M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → g ∈ H :=
    fun M hM g hg => Subgroup.subset_closure ⟨M, hM, hg⟩
  have hmD : hD ω ∈ heisLines ω := Set.mem_insert _ _
  have hmS : hS ∈ heisLines ω := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hmDS : hD ω * hS ∈ heisLines ω :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hmDSS : hD ω * hS * hS ∈ heisLines ω :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  obtain ⟨s, hs⟩ := exists_shift_su h
  obtain ⟨d, hd⟩ := twInnerHeis_exists_su_hD h hq3 hω3
  have hsH : s ∈ H := hex hS hmS s (by rw [hs])
  have hdH : d ∈ H := hex (hD ω) hmD d (by rw [hd])
  have hω2 : IsPrimitiveRoot (ω ^ 2) 3 := hω.pow_of_coprime 2 (by norm_num)
  have hds : (((d * s : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      hD ω * hS := by
    rw [Subgroup.coe_mul, Units.val_mul, hd, hs]
  have hdss : (((d * s * s : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      hD ω * hS * hS := by
    rw [Subgroup.coe_mul, Units.val_mul, hds, hs]
  rw [eq_top_iff, ← hcore ℓ f K h hq3 hq ω hω, Subgroup.closure_le]
  rintro g ⟨M, hM, c, hc⟩
  simp only [heisLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · exact twInnerHeis_mem_of_mul_eq_smul hω2 (by rw [hs]; exact twInnerHeis_hS_hD hω3)
      (hex _ hmD) hsH (twInnerHeis_cube_eq_one h hd hc) hc
  · exact twInnerHeis_mem_of_mul_eq_smul hω (by rw [hd]; exact twInnerHeis_hD_hS hω3)
      (hex _ hmS) hdH (twInnerHeis_cube_eq_one h hs hc) hc
  · exact twInnerHeis_mem_of_mul_eq_smul hω (by rw [hd]; exact twInnerHeis_hD_hDhS hω3)
      (hex _ hmDS) hdH (twInnerHeis_cube_eq_one h hds hc) hc
  · exact twInnerHeis_mem_of_mul_eq_smul hω2 (by rw [hd]; exact twInnerHeis_hD_hDhShS hω3)
      (hex _ hmDSS) hdH (twInnerHeis_cube_eq_one h hdss hc) hc

theorem twInnerHeis_commute_conj {Pm Pi M G : Matrix (Fin 3) (Fin 3) K} (hPiP : Pi * Pm = 1)
    {r : K} (hG : G * M = M * G) :
    Pm * G * Pi * (r • (Pm * M * Pi)) = r • (Pm * M * Pi) * (Pm * G * Pi) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc Pm * G * Pi * (Pm * M * Pi) = Pm * G * (Pi * Pm) * M * Pi := by
        simp only [Matrix.mul_assoc]
    _ = Pm * (M * G) * Pi := by rw [hPiP, Matrix.mul_one, Matrix.mul_assoc Pm G M, hG]
    _ = Pm * M * (Pi * Pm) * G * Pi := by
        rw [hPiP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = Pm * M * Pi * (Pm * G * Pi) := by simp only [Matrix.mul_assoc]

theorem twInnerHeisPlane_of_core (hcore : UnitaryHeisCore) : TwInnerHeisPlane := by
  intro ℓ f K _ h hq3 hq γ₁ γ₂ hne hcomm h13 h23 hind hin
  set a := suConj h γ₁ with ha
  set b := suConj h γ₂ with hb
  set E := Subgroup.closure ({a, b} : Set (MulAut (unitarySU ℓ f K 3))) with hE
  have haE : a ∈ E := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbE : b ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨x₁, hx₁⟩ := hin haE
  obtain ⟨x₂, hx₂⟩ := hin hbE
  have hyx : ∃ c : K, ((x₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((x₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • (((x₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((x₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    obtain ⟨c, hc⟩ := twInnerHeis_smul_of_conj_eq_conj h (u := x₂ * x₁) (v := x₁ * x₂)
      (by rw [map_mul, map_mul, hx₁, hx₂, hcomm])
    exact ⟨c, by simpa using hc⟩
  have hx3 : ∃ c : K, ((x₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    obtain ⟨c, hc⟩ := twInnerHeis_smul_of_conj_eq_conj h (u := x₁ ^ 3) (v := 1)
      (by rw [map_pow, hx₁, h13, map_one])
    exact ⟨c, by simpa using hc⟩
  have hxy : ((x₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((x₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
      ((x₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((x₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro hXY
    obtain ⟨c₁, hc₁⟩ := twInnerHeis_smul_of_suConj_eq_conj (γ := γ₁) hx₁.symm
    obtain ⟨c₂, hc₂⟩ := twInnerHeis_smul_of_suConj_eq_conj (γ := γ₂) hx₂.symm
    apply hne
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hc₁, hc₂,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, hXY, smul_smul,
      smul_smul, mul_comm c₁ c₂]
  obtain ⟨P, ω, ξ, hPmem, hprim, hξ3, hXP, hYP⟩ :=
    exists_unitary_heisenberg_basis h hq3 x₁.2 x₂.2 hyx hxy hx3
  set X : Matrix (Fin 3) (Fin 3) K := ((x₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hX
  set Y : Matrix (Fin 3) (Fin 3) K := ((x₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hY
  set Pm : Matrix (Fin 3) (Fin 3) K := (P : Matrix (Fin 3) (Fin 3) K) with hPm
  set Pi : Matrix (Fin 3) (Fin 3) K := ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hPi
  have hPPi : Pm * Pi = 1 := by rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hconjS : X = (1 : K) • (Pm * hS * Pi) := by
    rw [one_smul, ← hXP, Matrix.mul_assoc, hPPi, Matrix.mul_one]
  have hdiag : diagonal ![ξ, ξ * ω, ξ * ω ^ 2] = ξ • hD ω := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hD]
  have hconjD : Y = ξ • (Pm * hD ω * Pi) := by
    have h1 : Y * Pm = ξ • (Pm * hD ω) := by rw [hYP, hdiag, Matrix.mul_smul]
    calc Y = Y * Pm * Pi := by rw [Matrix.mul_assoc, hPPi, Matrix.mul_one]
      _ = ξ • (Pm * hD ω * Pi) := by rw [h1, Matrix.smul_mul]
  have hconjmul : ∀ A B : Matrix (Fin 3) (Fin 3) K,
      Pm * (A * B) * Pi = (Pm * A * Pi) * (Pm * B * Pi) := by
    intro A B
    calc Pm * (A * B) * Pi = Pm * A * (Pi * Pm) * B * Pi := by
          rw [hPiP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = (Pm * A * Pi) * (Pm * B * Pi) := by simp only [Matrix.mul_assoc]
  have hconjDS : Y * X = ξ • (Pm * (hD ω * hS) * Pi) := by
    rw [hconjmul, hconjD, hconjS, one_smul, Matrix.smul_mul]
  have hconjDSS : Y * X * X = ξ • (Pm * (hD ω * hS * hS) * Pi) := by
    rw [hconjmul, hconjmul, hconjD, hconjS, one_smul, Matrix.smul_mul, Matrix.smul_mul]
  have ha1 : a ≠ 1 := fun h1 => by
    obtain ⟨h3, -⟩ := hind 1 0 (by rw [pow_one, pow_zero, mul_one]; exact h1)
    omega
  have hb1 : b ≠ 1 := fun h1 => by
    obtain ⟨-, h3⟩ := hind 0 1 (by rw [pow_zero, one_mul, pow_one]; exact h1)
    omega
  have hba1 : b * a ≠ 1 := fun h1 => by
    obtain ⟨h3, -⟩ := hind 1 1 (by rw [pow_one, pow_one, hcomm]; exact h1)
    omega
  have hbaa1 : b * a * a ≠ 1 := fun h1 => by
    obtain ⟨-, h3⟩ := hind 2 1 (by
      rw [pow_one, pow_two, mul_assoc, hcomm, ← mul_assoc, hcomm]; exact h1)
    omega
  have hlines : ∀ M ∈ heisLines ω, ∃ (z : unitarySU ℓ f K 3) (r : K), MulAut.conj z ∈ E ∧
      MulAut.conj z ≠ 1 ∧ ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = r • (Pm * M * Pi) := by
    intro M hM
    simp only [heisLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl | rfl
    · exact ⟨x₂, ξ, by rw [hx₂]; exact hbE, by rw [hx₂]; exact hb1, hconjD⟩
    · exact ⟨x₁, 1, by rw [hx₁]; exact haE, by rw [hx₁]; exact ha1, hconjS⟩
    · refine ⟨x₂ * x₁, ξ, ?_, ?_, ?_⟩
      · rw [map_mul, hx₁, hx₂]; exact E.mul_mem hbE haE
      · rw [map_mul, hx₁, hx₂]; exact hba1
      · rw [Subgroup.coe_mul, Units.val_mul]; exact hconjDS
    · refine ⟨x₂ * x₁ * x₁, ξ, ?_, ?_, ?_⟩
      · rw [map_mul, map_mul, hx₁, hx₂]; exact E.mul_mem (E.mul_mem hbE haE) haE
      · rw [map_mul, map_mul, hx₁, hx₂]; exact hbaa1
      · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]; exact hconjDSS
  set φ := conjSU h (⟨P, hPmem⟩ : primeFormUnitary h (idGram K 3)) with hφ
  have hG' : ∀ g : unitarySU ℓ f K 3, (((φ g : unitarySU ℓ f K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = Pm * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Pi :=
    fun g => by rw [hφ, coe_conjSU, Units.val_mul, Units.val_mul]
  have hmain : ∀ g : unitarySU ℓ f K 3, (∃ M ∈ heisLines ω,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
        M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) → φ g ∈ planeClosure E := by
    rintro g ⟨M, hM, hgM⟩
    obtain ⟨z, r, hzE, hz1, hz⟩ := hlines M hM
    refine mem_planeClosure_of_fixed hzE hz1 ?_
    have hc : φ g * z = z * φ g := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hG', hz]
      exact twInnerHeis_commute_conj hPiP hgM
    rw [MulAut.conj_apply, ← hc, mul_inv_cancel_right]
  have hmap : Subgroup.map (φ : unitarySU ℓ f K 3 →* unitarySU ℓ f K 3)
      (Subgroup.closure {g : unitarySU ℓ f K 3 | ∃ M ∈ heisLines ω,
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
          M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)}) ≤ planeClosure E := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact hmain g hg
  rw [twInnerHeis_closure_exact hcore h hq3 hq hprim,
    Subgroup.map_top_of_surjective _ φ.surjective] at hmap
  exact eq_top_iff.2 hmap

theorem twInnerHeisPlane_holds :
    TwInnerHeisPlane :=
  twInnerHeisPlane_of_core unitaryHeisCore

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
