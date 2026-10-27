module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTorus
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthCoordBlock
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallOdd
public import CFSG.GH74.Uniqueness.Bender.FrameTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.LinearPilot (blockDiagSL mem_blockDiagSL blockSpecialLinear
  mem_blockSpecialLinear commutator_blockDiagSL_le)
open Matrix

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

@[expose] def unitaryBlockDiag (I : Finset (Fin n)) : Subgroup (unitarySU p f K n) :=
  (blockDiagSL (K := K) I).comap (toSL h n)

theorem mem_unitaryBlockDiag {I : Finset (Fin n)} {A : unitarySU p f K n} :
    A ∈ unitaryBlockDiag h I ↔ ∀ i j, (i ∈ I ↔ j ∉ I) →
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := by
  rw [unitaryBlockDiag, Subgroup.mem_comap, mem_blockDiagSL, coe_toSL]

theorem unitaryBlock_le_unitaryBlockDiag (I : Finset (Fin n)) :
    unitaryBlock h I ≤ unitaryBlockDiag h I := by
  intro A hA
  rw [mem_unitaryBlockDiag]
  intro i j hij
  rw [mem_unitaryBlock] at hA
  have h1 : (i ∉ I ∨ j ∉ I) := by tauto
  rw [hA i j h1]
  by_cases h : i = j
  · subst h
    exact absurd hij (by simp)
  · rw [one_apply_ne h]

theorem centralizer_diagSU_eq_unitaryBlockDiag {I : Finset (Fin n)} {l ν : K}
    (hlν : l ≠ ν) {d : Fin n → K} (hv : ∀ i, d i = if i ∈ I then l else ν)
    (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1) :
    Subgroup.centralizer ({diagSU h d hd hdet} : Set (unitarySU p f K n)) =
      unitaryBlockDiag h I := by
  ext A
  rw [Subgroup.mem_centralizer_singleton_iff, mem_unitaryBlockDiag]
  constructor
  ·
    intro hAx i j hij
    set MA : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMA
    have hmat : MA * diagonal d = diagonal d * MA := by
      have h := congrArg
        (fun g : unitarySU p f K n => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hAx
      simpa only [Subgroup.coe_mul, Units.val_mul, coe_diagSU, hMA] using h
    have hentry : MA i j * d j = d i * MA i j := by
      calc MA i j * d j = (MA * diagonal d) i j := by simp
        _ = (diagonal d * MA) i j := by rw [hmat]
        _ = d i * MA i j := by simp
    have hdi : d i = if i ∈ I then l else ν := hv i
    have hdj : d j = if j ∈ I then l else ν := hv j
    have hdiff : d j - d i ≠ 0 := by
      rw [hdi, hdj]
      by_cases hi : i ∈ I <;> by_cases hj : j ∈ I
      · exact absurd hij (by simp [hi, hj])
      · simp only [hi, hj, if_true, if_false]
        exact sub_ne_zero.2 (Ne.symm hlν)
      · simp only [hi, hj, if_true, if_false]
        exact sub_ne_zero.2 hlν
      · exact absurd hij (by simp [hi, hj])
    have h2 : MA i j * (d j - d i) = 0 := by
      linear_combination hentry
    exact (mul_eq_zero.1 h2).resolve_right hdiff
  ·
    intro hA
    set MA : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMA
    have hmat : MA * diagonal d = diagonal d * MA := by
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hij : (i ∈ I ↔ j ∉ I)
      · rw [hA i j hij, zero_mul, mul_zero]
      · have hdij : d i = d j := by
          rw [hv i, hv j]
          by_cases hi : i ∈ I <;> by_cases hj : j ∈ I <;> simp_all
        rw [hdij, mul_comm]
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, coe_diagSU, hMA]
    exact hmat


theorem mul_eq_mul_of_unitaryProj_commute_diagSU {I : Finset (Fin n)} (hI : n < 2 * I.card)
    {l ν : K} (hlν : l ≠ ν) {d : Fin n → K} (hv : ∀ i, d i = if i ∈ I then l else ν)
    (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1) {A : unitarySU p f K n}
    (hAx : unitaryProj h n A * unitaryProj h n (diagSU h d hd hdet) =
      unitaryProj h n (diagSU h d hd hdet) * unitaryProj h n A) :
    A * diagSU h d hd hdet = diagSU h d hd hdet * A := by
  set x := diagSU h d hd hdet with hx
  set MA : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMA
  rw [← map_mul, ← map_mul] at hAx
  obtain ⟨c, -, -, hc⟩ :=
    mem_unitaryScalars.mp ((QuotientGroup.eq (s := unitaryScalars h n)).mp hAx)
  have h1 : ((x * A : unitarySU p f K n) : GL (Fin n) K) =
      ((A * x : unitarySU p f K n) : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c := by
    rw [← hc, ← Subgroup.coe_mul, mul_inv_cancel_left]
  have hl0 : l ≠ 0 := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < I.card)
    have hli : h.norm l = 1 := by
      have := hd i
      rwa [hv i, if_pos hi] at this
    rintro rfl
    rw [show h.norm (0 : K) = 0 by simp [UnitaryFieldData.norm]] at hli
    exact zero_ne_one hli
  by_cases hc1 : (c : K) = 1
  · have h1' : ((x * A : unitarySU p f K n) : GL (Fin n) K) =
        ((A * x : unitarySU p f K n) : GL (Fin n) K) := by
      have hc1u : c = 1 := by ext; exact hc1
      simpa [hc1u] using h1
    exact Subtype.ext h1'.symm
  · exfalso
    have h2 : diagonal d * MA = (MA * diagonal d) * diagonal (fun _ : Fin n => (c : K)) := by
      have h := congrArg
        (fun g : GL (Fin n) K => ((g : Matrix (Fin n) (Fin n) K))) h1
      simpa only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, coe_diagSU, hMA, hx] using h
    have hentry : ∀ i j, d i * MA i j = MA i j * d j * (c : K) := by
      intro i j
      have h := congrFun (congrFun h2 i) j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.mul_diagonal] at h
      simpa [mul_assoc] using h
    have hzero : ∀ i ∈ I, ∀ j ∈ I, MA i j = 0 := by
      intro i hi j hj
      have hdi : d i = l := by rw [hv i, if_pos hi]
      have hdj : d j = l := by rw [hv j, if_pos hj]
      have h := hentry i j
      rw [hdi, hdj] at h
      have h' : MA i j * (l * ((c : K) - 1)) = 0 := by
        have h2 : MA i j * l * (c : K) = l * MA i j := h.symm
        calc MA i j * (l * ((c : K) - 1)) = MA i j * l * (c : K) - MA i j * l := by ring
          _ = l * MA i j - MA i j * l := by rw [h2]
          _ = 0 := by rw [mul_comm l (MA i j), sub_self]
      refine (mul_eq_zero.1 h').resolve_right ?_
      exact mul_ne_zero hl0 (sub_ne_zero.2 hc1)
    have hdet0 : MA.det = 0 := det_eq_zero_of_apply_eq_zero_of_lt hI hzero
    have hdet1 : MA.det = 1 := ((mem_unitarySU_iff h).1 A.2).1
    rw [hdet1] at hdet0
    exact one_ne_zero hdet0

theorem centralizer_unitaryProj_diagSU_eq_unitaryBlockDiag {I : Finset (Fin n)}
    (hI : n < 2 * I.card) {l ν : K} (hlν : l ≠ ν) {d : Fin n → K}
    (hv : ∀ i, d i = if i ∈ I then l else ν) (hd : ∀ i, h.norm (d i) = 1)
    (hdet : ∏ i, d i = 1) :
    Subgroup.centralizer
        ({unitaryProj h n (diagSU h d hd hdet)} : Set (unitaryPSU h n)) =
      (unitaryBlockDiag h I).map (unitaryProj h n) := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    obtain ⟨A, rfl⟩ := unitaryProj_surjective h n g
    refine Subgroup.mem_map.2 ⟨A, ?_, rfl⟩
    have hmem := mul_eq_mul_of_unitaryProj_commute_diagSU h hI hlν hv hd hdet hg
    rw [← centralizer_diagSU_eq_unitaryBlockDiag h hlν hv hd hdet]
    exact Subgroup.mem_centralizer_singleton_iff.2 hmem
  · rintro ⟨A, hA, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : A * diagSU h d hd hdet = diagSU h d hd hdet * A :=
      Subgroup.mem_centralizer_singleton_iff.1
        ((centralizer_diagSU_eq_unitaryBlockDiag h hlν hv hd hdet).ge hA)
    rw [← map_mul, ← map_mul, hcomm]

theorem commutator_unitaryBlockDiag_le_unitaryBlock {I : Finset (Fin n)} {j₀ : Fin n}
    (hI : Iᶜ = {j₀}) :
    ⁅unitaryBlockDiag h I, unitaryBlockDiag h I⁆ ≤ unitaryBlock h I := by
  rw [Subgroup.commutator_le]
  intro A hA B hB
  rw [mem_unitaryBlock_iff_toSL]
  have hA' : toSL h n A ∈ blockDiagSL (K := K) I := hA
  have hB' : toSL h n B ∈ blockDiagSL (K := K) I := hB
  have hmem := commutator_blockDiagSL_le (K := K) I
    (Subgroup.commutator_mem_commutator hA' hB')
  have hbot : blockSpecialLinear (K := K) Iᶜ = ⊥ := by
    rw [hI]
    exact CFSG.SeitzReduction.LinearPilot.blockSpecialLinear_eq_bot_of_card_le_one (by simp)
  rw [hbot, sup_bot_eq] at hmem
  simpa only [commutatorElement_def, map_mul, map_inv] using hmem

theorem inSubgroup_layer_eq_unitaryBlock {I : Finset (Fin n)} {j₀ : Fin n} (hI : Iᶜ = {j₀})
    {l ν : K} (hlν : l ≠ ν) {d : Fin n → K} (hv : ∀ i, d i = if i ∈ I then l else ν)
    (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1) (h3 : 3 ≤ I.card)
    (hq : (I.card, p ^ f) ≠ (3, 2)) :
    CFSG.inSubgroup CFSG.layer
        (Subgroup.centralizer ({diagSU h d hd hdet} : Set (unitarySU p f K n))) =
      unitaryBlock h I := by
  have hDH : unitaryBlock h I ≤
      Subgroup.centralizer ({diagSU h d hd hdet} : Set (unitarySU p f K n)) := by
    intro A hA
    rw [centralizer_diagSU_eq_unitaryBlockDiag h hlν hv hd hdet]
    exact unitaryBlock_le_unitaryBlockDiag h I hA
  have hcomm : ∀ g ∈ Subgroup.centralizer ({diagSU h d hd hdet} : Set (unitarySU p f K n)),
      ∀ k ∈ Subgroup.centralizer ({diagSU h d hd hdet} : Set (unitarySU p f K n)),
      g * k * g⁻¹ * k⁻¹ ∈ unitaryBlock h I := by
    intro g hg k hk
    rw [centralizer_diagSU_eq_unitaryBlockDiag h hlν hv hd hdet] at hg hk
    exact commutator_unitaryBlockDiag_le_unitaryBlock h hI
      (Subgroup.commutator_mem_commutator hg hk)
  have hQ : CFSG.IsQuasisimple ↥(unitaryBlock h I) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (unitaryBlockEquiv h I)
      (isQuasisimple_unitarySU h h3 hq)
  exact CFSG.SeitzReduction.LinearPilot.inSubgroup_layer_eq_of_commutator_mem hDH hcomm hQ

theorem inSubgroup_layer_centralizer_unitaryProj_diagSU {I : Finset (Fin n)}
    (hI2 : n < 2 * I.card) {j₀ : Fin n} (hI : Iᶜ = {j₀}) {l ν : K} (hlν : l ≠ ν)
    {d : Fin n → K} (hv : ∀ i, d i = if i ∈ I then l else ν) (hd : ∀ i, h.norm (d i) = 1)
    (hdet : ∏ i, d i = 1) (h3 : 3 ≤ I.card) (hq : (I.card, p ^ f) ≠ (3, 2)) :
    CFSG.inSubgroup CFSG.layer
        (Subgroup.centralizer
          ({unitaryProj h n (diagSU h d hd hdet)} : Set (unitaryPSU h n))) =
      blockSU h I := by
  have hC := centralizer_unitaryProj_diagSU_eq_unitaryBlockDiag h hI2 hlν hv hd hdet
  have hDH : blockSU h I ≤ Subgroup.centralizer
      ({unitaryProj h n (diagSU h d hd hdet)} : Set (unitaryPSU h n)) := by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := (mem_blockSU h).1 hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : A * diagSU h d hd hdet = diagSU h d hd hdet * A :=
      Subgroup.mem_centralizer_singleton_iff.1
        ((centralizer_diagSU_eq_unitaryBlockDiag h hlν hv hd hdet).ge
          (unitaryBlock_le_unitaryBlockDiag h I hA))
    rw [← map_mul, ← map_mul, hcomm]
  have hcomm : ∀ g ∈ Subgroup.centralizer
        ({unitaryProj h n (diagSU h d hd hdet)} : Set (unitaryPSU h n)),
      ∀ k ∈ Subgroup.centralizer
        ({unitaryProj h n (diagSU h d hd hdet)} : Set (unitaryPSU h n)),
      g * k * g⁻¹ * k⁻¹ ∈ blockSU h I := by
    intro g hg k hk
    rw [hC] at hg hk
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.1 hk
    have hAB : A * B * A⁻¹ * B⁻¹ ∈ unitaryBlock h I :=
      commutator_unitaryBlockDiag_le_unitaryBlock h hI
        (Subgroup.commutator_mem_commutator hA hB)
    have hpi : (unitaryProj h n) (A * B * A⁻¹ * B⁻¹) =
        (unitaryProj h n) A * (unitaryProj h n) B * ((unitaryProj h n) A)⁻¹ *
          ((unitaryProj h n) B)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [← hpi]
    exact unitaryProj_mem_blockSU h hAB
  have hIn : I.card < n := by
    have h := Finset.card_compl (s := I)
    rw [hI, Finset.card_singleton, Fintype.card_fin] at h
    omega
  have hQ : CFSG.IsQuasisimple ↥(blockSU h I) :=
    isQuasisimple_blockSU_of_three_le h h3 hq hIn
  exact CFSG.SeitzReduction.LinearPilot.inSubgroup_layer_eq_of_commutator_mem hDH hcomm hQ

theorem glaLayer_centralizer_unitaryProj_diagSU {I : Finset (Fin n)}
    (hI2 : n < 2 * I.card) {j₀ : Fin n} (hI : Iᶜ = {j₀}) {l ν : K} (hlν : l ≠ ν)
    {d : Fin n → K} (hv : ∀ i, d i = if i ∈ I then l else ν) (hd : ∀ i, h.norm (d i) = 1)
    (hdet : ∏ i, d i = 1) (h3 : 3 ≤ I.card) (hq : (I.card, p ^ f) ≠ (3, 2)) :
    CFSG.Open.GLALayer
        (Subgroup.centralizer
          ({unitaryProj h n (diagSU h d hd hdet)} : Set (unitaryPSU h n))) =
      blockSU h I := by
  have hbridge : CFSG.inSubgroup CFSG.layer
      (Subgroup.centralizer
        ({unitaryProj h n (diagSU h d hd hdet)} : Set (unitaryPSU h n))) =
      CFSG.Open.GLALayer (Subgroup.centralizer
        ({unitaryProj h n (diagSU h d hd hdet)} : Set (unitaryPSU h n))) :=
    le_antisymm
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.map_layer_le_glaLayer _)
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.glaLayer_le_map_layer _)
  rw [← hbridge]
  exact inSubgroup_layer_centralizer_unitaryProj_diagSU h hI2 hI hlν hv hd hdet h3 hq


theorem unitaryNorm_pow_eq_one {ζ : K} (hζ : h.norm ζ = 1) (k : ℕ) : h.norm (ζ ^ k) = 1 := by
  induction k with
  | zero => simp [UnitaryFieldData.norm]
  | succ k ih => rw [pow_succ, norm_mul_eq, ih, one_mul]; exact hζ

@[expose] def diagFiveLastEntries (ζ : K) : Fin 6 → K :=
  fun i => if i = (5 : Fin 6) then (ζ ^ 5)⁻¹ else ζ

theorem diagFiveLastEntries_norm {ζ : K} (hζ : h.norm ζ = 1) :
    ∀ i, h.norm (diagFiveLastEntries ζ i) = 1 := by
  intro i
  by_cases hi : i = (5 : Fin 6)
  · rw [diagFiveLastEntries, if_pos hi, norm_inv_eq, unitaryNorm_pow_eq_one h hζ 5, inv_one]
  · rw [diagFiveLastEntries, if_neg hi]; exact hζ

theorem diagFiveLastEntries_prod {ζ : K} (hζ : h.norm ζ = 1) :
    ∏ i, diagFiveLastEntries ζ i = 1 := by
  rw [Fin.prod_univ_six]
  simp only [diagFiveLastEntries, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  rw [show ζ * ζ * ζ * ζ * ζ = ζ ^ 5 by ring,
    mul_inv_cancel₀ (pow_ne_zero 5 (CFSG.GH74.Uniqueness.Bender.Frame.ne_zero_of_norm_eq_one hζ))]

@[expose] noncomputable def diagFiveLast (ζ : K) (hζ : h.norm ζ = 1) : unitarySU p f K 6 :=
  diagSU h (diagFiveLastEntries ζ) (diagFiveLastEntries_norm h hζ)
    (diagFiveLastEntries_prod h hζ)

@[simp]
theorem coe_diagFiveLast (ζ : K) (hζ : h.norm ζ = 1) :
    (((diagFiveLast h ζ hζ : unitarySU p f K 6) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal (diagFiveLastEntries ζ) :=
  rfl

private theorem compl_erase_five : ((Finset.univ : Finset (Fin 6)).erase 5)ᶜ = {5} := by
  ext i
  simp [Finset.mem_erase, eq_comm]

private theorem diagFiveLast_ne_inv {ζ : K} (hζ : h.norm ζ = 1) (hζ6 : ζ ^ 6 ≠ 1) :
    ζ ≠ (ζ ^ 5)⁻¹ := by
  intro hζeq
  apply hζ6
  have h1 : ζ * ζ ^ 5 = 1 := by
    nth_rewrite 1 [hζeq]
    exact inv_mul_cancel₀ (pow_ne_zero 5
      (CFSG.GH74.Uniqueness.Bender.Frame.ne_zero_of_norm_eq_one hζ))
  calc ζ ^ 6 = ζ * ζ ^ 5 := by ring
    _ = 1 := h1

private theorem diagFiveLastEntries_eq {ζ : K} :
    ∀ i : Fin 6, diagFiveLastEntries ζ i =
      if i ∈ (Finset.univ : Finset (Fin 6)).erase 5 then ζ else (ζ ^ 5)⁻¹ := by
  intro i
  rw [diagFiveLastEntries]
  by_cases hi : i = (5 : Fin 6)
  · rw [if_pos hi, if_neg]
    simp [hi]
  · rw [if_neg hi, if_pos]
    simp [Finset.mem_erase, hi]

theorem centralizer_diagFiveLast {ζ : K} (hζ : h.norm ζ = 1) (hζ6 : ζ ^ 6 ≠ 1) :
    Subgroup.centralizer ({diagFiveLast h ζ hζ} : Set (unitarySU p f K 6)) =
      unitaryBlockDiag h ((Finset.univ : Finset (Fin 6)).erase 5) := by
  have hlν := diagFiveLast_ne_inv h hζ hζ6
  have hv := diagFiveLastEntries_eq (ζ := ζ)
  have hmain := centralizer_diagSU_eq_unitaryBlockDiag h (l := ζ) (ν := (ζ ^ 5)⁻¹) hlν hv
    (diagFiveLastEntries_norm h hζ) (diagFiveLastEntries_prod h hζ)
  rwa [show diagSU h (diagFiveLastEntries ζ) (diagFiveLastEntries_norm h hζ)
      (diagFiveLastEntries_prod h hζ) = diagFiveLast h ζ hζ from rfl] at hmain

theorem centralizer_unitaryProj_diagFiveLast {ζ : K} (hζ : h.norm ζ = 1)
    (hζ6 : ζ ^ 6 ≠ 1) :
    Subgroup.centralizer
        ({unitaryProj h 6 (diagFiveLast h ζ hζ)} : Set (unitaryPSU h 6)) =
      (unitaryBlockDiag h ((Finset.univ : Finset (Fin 6)).erase 5)).map (unitaryProj h 6) := by
  have hlν := diagFiveLast_ne_inv h hζ hζ6
  have hv := diagFiveLastEntries_eq (ζ := ζ)
  have hI2 : 6 < 2 * ((Finset.univ : Finset (Fin 6)).erase 5).card := by
    simp [Finset.card_erase_of_mem]
  have hmain := centralizer_unitaryProj_diagSU_eq_unitaryBlockDiag h hI2 (l := ζ)
    (ν := (ζ ^ 5)⁻¹) hlν hv (diagFiveLastEntries_norm h hζ) (diagFiveLastEntries_prod h hζ)
  rwa [show diagSU h (diagFiveLastEntries ζ) (diagFiveLastEntries_norm h hζ)
      (diagFiveLastEntries_prod h hζ) = diagFiveLast h ζ hζ from rfl] at hmain

theorem glaLayer_centralizer_unitaryProj_diagFiveLast {ζ : K} (hζ : h.norm ζ = 1)
    (hζ6 : ζ ^ 6 ≠ 1) :
    CFSG.Open.GLALayer (Subgroup.centralizer
        ({unitaryProj h 6 (diagFiveLast h ζ hζ)} : Set (unitaryPSU h 6))) =
      blockSU h ((Finset.univ : Finset (Fin 6)).erase 5) := by
  have hlν := diagFiveLast_ne_inv h hζ hζ6
  have hv := diagFiveLastEntries_eq (ζ := ζ)
  have hI2 : 6 < 2 * ((Finset.univ : Finset (Fin 6)).erase 5).card := by
    simp [Finset.card_erase_of_mem]
  have h3 : 3 ≤ ((Finset.univ : Finset (Fin 6)).erase 5).card := by
    simp [Finset.card_erase_of_mem]
  have hq : (((Finset.univ : Finset (Fin 6)).erase 5).card, p ^ f) ≠ (3, 2) := by
    simp [Finset.card_erase_of_mem]
  have hmain := glaLayer_centralizer_unitaryProj_diagSU h hI2 compl_erase_five (l := ζ)
    (ν := (ζ ^ 5)⁻¹) hlν hv (diagFiveLastEntries_norm h hζ) (diagFiveLastEntries_prod h hζ)
    h3 hq
  rwa [show diagSU h (diagFiveLastEntries ζ) (diagFiveLastEntries_norm h hζ)
      (diagFiveLastEntries_prod h hζ) = diagFiveLast h ζ hζ from rfl] at hmain


theorem inSubgroup_layer_eq_diagFiveLast {ζ : K} (hζ : h.norm ζ = 1) (hζ6 : ζ ^ 6 ≠ 1) :
    CFSG.inSubgroup CFSG.layer
        (Subgroup.centralizer ({diagFiveLast h ζ hζ} : Set (unitarySU p f K 6))) =
      unitaryBlock h ((Finset.univ : Finset (Fin 6)).erase 5) := by
  have h3 : 3 ≤ ((Finset.univ : Finset (Fin 6)).erase 5).card := by
    simp [Finset.card_erase_of_mem]
  have hq : (((Finset.univ : Finset (Fin 6)).erase 5).card, p ^ f) ≠ (3, 2) := by
    simp [Finset.card_erase_of_mem]
  have hmain := inSubgroup_layer_eq_unitaryBlock h compl_erase_five (l := ζ)
    (ν := (ζ ^ 5)⁻¹) (diagFiveLast_ne_inv h hζ hζ6) (diagFiveLastEntries_eq (ζ := ζ))
    (diagFiveLastEntries_norm h hζ) (diagFiveLastEntries_prod h hζ) h3 hq
  rwa [show diagSU h (diagFiveLastEntries ζ) (diagFiveLastEntries_norm h hζ)
      (diagFiveLastEntries_prod h hζ) = diagFiveLast h ζ hζ from rfl] at hmain

theorem inSubgroup_layer_centralizer_unitaryProj_diagFiveLast {ζ : K} (hζ : h.norm ζ = 1)
    (hζ6 : ζ ^ 6 ≠ 1) :
    CFSG.inSubgroup CFSG.layer (Subgroup.centralizer
        ({unitaryProj h 6 (diagFiveLast h ζ hζ)} : Set (unitaryPSU h 6))) =
      blockSU h ((Finset.univ : Finset (Fin 6)).erase 5) := by
  have hI2 : 6 < 2 * ((Finset.univ : Finset (Fin 6)).erase 5).card := by
    simp [Finset.card_erase_of_mem]
  have h3 : 3 ≤ ((Finset.univ : Finset (Fin 6)).erase 5).card := by
    simp [Finset.card_erase_of_mem]
  have hq : (((Finset.univ : Finset (Fin 6)).erase 5).card, p ^ f) ≠ (3, 2) := by
    simp [Finset.card_erase_of_mem]
  have hmain := inSubgroup_layer_centralizer_unitaryProj_diagSU h hI2 compl_erase_five
    (l := ζ) (ν := (ζ ^ 5)⁻¹) (diagFiveLast_ne_inv h hζ hζ6) (diagFiveLastEntries_eq (ζ := ζ))
    (diagFiveLastEntries_norm h hζ) (diagFiveLastEntries_prod h hζ) h3 hq
  rwa [show diagSU h (diagFiveLastEntries ζ) (diagFiveLastEntries_norm h hζ)
      (diagFiveLastEntries_prod h hζ) = diagFiveLast h ζ hζ from rfl] at hmain

end CFSG.LocalAnalysis.GLTheoremA.Y10F
