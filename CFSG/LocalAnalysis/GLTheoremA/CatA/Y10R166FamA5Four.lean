module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootTorus
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129W
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace A5Four

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot
open Matrix

variable {F : Type} [Field F] [Finite F]


private theorem card_units_eq_three (hF : Nat.card F = 4) : Nat.card Fˣ = 3 := by
  rw [Nat.card_units, hF]

theorem units_pow_three (hF : Nat.card F = 4) (u : Fˣ) : u ^ 3 = 1 := by
  have h : u ^ Nat.card Fˣ = 1 := pow_card_eq_one'
  rwa [card_units_eq_three hF] at h

private theorem units_eq_one_of_pow_four (hF : Nat.card F = 4) {u : Fˣ} (hu : u ^ 4 = 1) :
    u = 1 := by
  have h3 := units_pow_three hF u
  have h4 : u ^ 4 = u := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, h3, one_mul]
  rw [← h4]
  exact hu

theorem exists_units_order_three (hF : Nat.card F = 4) :
    ∃ ω : Fˣ, orderOf ω = 3 := by
  have h3 : Nat.card Fˣ = 3 := card_units_eq_three hF
  have hdvd : 3 ∣ Nat.card Fˣ := by rw [h3]
  exact exists_prime_orderOf_dvd_card' 3 hdvd

@[expose]
noncomputable def diagSL {n : ℕ} (d : Fin n → F) (h : ∏ i, d i = 1) :
    SpecialLinearGroup (Fin n) F :=
  ⟨Matrix.diagonal d, by rw [Matrix.det_diagonal]; exact h⟩

@[simp]
private theorem coe_diagSL {n : ℕ} (d : Fin n → F) (h : ∏ i, d i = 1) :
    (diagSL d h : Matrix (Fin n) (Fin n) F) = Matrix.diagonal d := rfl

private theorem diagSL_mul {n : ℕ} (d d' : Fin n → F) (h : ∏ i, d i = 1)
    (h' : ∏ i, d' i = 1) :
    diagSL d h * diagSL d' h' =
      diagSL (d * d') (by rw [show (d * d') = (fun i => d i * d' i) from rfl,
        Finset.prod_mul_distrib, h, h', one_mul]) := by
  apply Subtype.ext
  change (Matrix.diagonal d) * (Matrix.diagonal d') = Matrix.diagonal (d * d')
  rw [Matrix.diagonal_mul_diagonal, show (d * d') = (fun i => d i * d' i) from rfl]

@[expose]
def phiUnits (a u v w : Fˣ) : Fin 6 → Fˣ :=
  ![a, a ^ 2, u, v, w, (u * v * w)⁻¹]

@[simp]
theorem phiUnits_zero (a u v w : Fˣ) : phiUnits a u v w 0 = a := rfl
@[simp]
theorem phiUnits_one (a u v w : Fˣ) : phiUnits a u v w 1 = a ^ 2 := rfl
@[simp]
theorem phiUnits_two (a u v w : Fˣ) : phiUnits a u v w 2 = u := rfl
@[simp]
theorem phiUnits_three (a u v w : Fˣ) : phiUnits a u v w 3 = v := rfl
@[simp]
theorem phiUnits_four (a u v w : Fˣ) : phiUnits a u v w 4 = w := rfl
@[simp]
theorem phiUnits_five (a u v w : Fˣ) :
    phiUnits a u v w 5 = (u * v * w)⁻¹ := rfl

theorem prod_phiUnits (hF : Nat.card F = 4) (a u v w : Fˣ) :
    ∏ i, (phiUnits a u v w i : F) = 1 := by
  rw [← Units.coe_prod]
  suffices h : (∏ i, phiUnits a u v w i : Fˣ) = 1 by rw [h, Units.val_one]
  rw [Fin.prod_univ_six]
  simp only [phiUnits_zero, phiUnits_one, phiUnits_two, phiUnits_three, phiUnits_four,
    phiUnits_five]
  have ha : a * a ^ 2 = 1 := by
    rw [mul_comm, ← pow_succ, show (2 + 1 : ℕ) = 3 by norm_num, units_pow_three hF]
  calc a * a ^ 2 * u * v * w * (u * v * w)⁻¹
      = (a * a ^ 2) * ((u * v * w) * (u * v * w)⁻¹) := by ac_rfl
    _ = 1 := by rw [ha, mul_inv_cancel, mul_one]

@[expose]
noncomputable def phi (hF : Nat.card F = 4) (a u v w : Fˣ) :
    SpecialLinearGroup (Fin 6) F :=
  diagSL (fun i => (phiUnits a u v w i : F)) (prod_phiUnits hF a u v w)

@[simp]
theorem coe_phi (hF : Nat.card F = 4) (a u v w : Fˣ) :
    (phi hF a u v w : Matrix (Fin 6) (Fin 6) F) =
      Matrix.diagonal fun i => (phiUnits a u v w i : F) := rfl

theorem phi_one (hF : Nat.card F = 4) : phi hF 1 1 1 1 = 1 := by
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [phi, diagSL, phiUnits]
  · simp [phi, diagSL, phiUnits, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem phi_mul (hF : Nat.card F = 4) (a u v w a' u' v' w' : Fˣ) :
    phi hF a u v w * phi hF a' u' v' w' = phi hF (a * a') (u * u') (v * v') (w * w') := by
  apply Subtype.ext
  change (Matrix.diagonal fun i => (phiUnits a u v w i : F)) *
      (Matrix.diagonal fun i => (phiUnits a' u' v' w' i : F)) =
    (Matrix.diagonal fun i => (phiUnits (a * a') (u * u') (v * v') (w * w') i : F))
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    fin_cases i <;>
      simp [phiUnits, Units.val_mul, Units.val_inv_eq_inv_val, mul_pow, mul_assoc, mul_comm,
        mul_left_comm]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]

private theorem phi_inv (hF : Nat.card F = 4) (a u v w : Fˣ) :
    (phi hF a u v w)⁻¹ = phi hF a⁻¹ u⁻¹ v⁻¹ w⁻¹ := by
  have h : phi hF a u v w * phi hF a⁻¹ u⁻¹ v⁻¹ w⁻¹ = 1 := by
    rw [phi_mul]
    rw [show a * a⁻¹ = 1 from mul_inv_cancel a, show u * u⁻¹ = 1 from mul_inv_cancel u,
      show v * v⁻¹ = 1 from mul_inv_cancel v, show w * w⁻¹ = 1 from mul_inv_cancel w,
      phi_one]
  calc (phi hF a u v w)⁻¹ = (phi hF a u v w)⁻¹ * 1 := (mul_one _).symm
    _ = (phi hF a u v w)⁻¹ * (phi hF a u v w * phi hF a⁻¹ u⁻¹ v⁻¹ w⁻¹) := by rw [h]
    _ = phi hF a⁻¹ u⁻¹ v⁻¹ w⁻¹ := by group

private theorem phi_pow (hF : Nat.card F = 4) (a u v w : Fˣ) (n : ℕ) :
    phi hF a u v w ^ n = phi hF (a ^ n) (u ^ n) (v ^ n) (w ^ n) := by
  induction n with
  | zero => simpa using (phi_one hF).symm
  | succ n ih =>
    rw [pow_succ, ih, phi_mul]
    congr 1
    all_goals rw [pow_succ]

@[expose]
noncomputable def psi (hF : Nat.card F = 4) :
    (Fˣ × Fˣ × Fˣ × Fˣ) →* LinearFlag.projectiveSL 6 F where
  toFun p := LinearFlag.proj 6 F (phi hF p.1 p.2.1 p.2.2.1 p.2.2.2)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, phi_one, map_one]
  map_mul' p q := by
    obtain ⟨a, u, v, w⟩ := p
    obtain ⟨a', u', v', w'⟩ := q
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [← map_mul, phi_mul]

@[expose]
noncomputable def Bs (hF : Nat.card F = 4) : Subgroup (LinearFlag.projectiveSL 6 F) :=
  (psi hF).range

@[expose]
noncomputable def xw (hF : Nat.card F = 4) (ω : Fˣ) :
    LinearFlag.projectiveSL 6 F :=
  psi hF (ω, 1, 1, 1)

theorem phi_mem_scalars_iff (hF : Nat.card F = 4) (a u v w : Fˣ) :
    phi hF a u v w ∈ LinearFlag.scalars 6 F ↔ a = 1 ∧ u = 1 ∧ v = 1 ∧ w = 1 := by
  constructor
  · intro h
    rw [LinearFlag.mem_scalars] at h
    obtain ⟨c, -, hc⟩ := h
    have hmat : (phi hF a u v w : Matrix (Fin 6) (Fin 6) F) =
        Matrix.scalar (Fin 6) (c : F) := hc
    have h0 : (a : F) = (c : F) := by
      have h := congrFun (congrFun hmat 0) 0
      simpa [phiUnits, Matrix.scalar_apply] using h
    have h1 : (a : F) ^ 2 = (c : F) := by
      have h := congrFun (congrFun hmat 1) 1
      simpa [phiUnits, Matrix.scalar_apply] using h
    have ha1 : a = 1 := by
      have hsqF : (a : F) = (a : F) * (a : F) := by
        have h2 : (a : F) = (a : F) ^ 2 := by rw [h1, ← h0]
        rwa [pow_two] at h2
      have hsq : a = a * a := by
        apply Units.ext
        rw [Units.val_mul]
        exact hsqF
      exact mul_right_cancel (by rw [one_mul]; exact hsq.symm)
    have hc1 : c = 1 := by
      apply Units.ext
      rw [← h0, ha1, Units.val_one]
    have hu : u = 1 := by
      have h := congrFun (congrFun hmat 2) 2
      simp only [coe_phi, phiUnits_two, Matrix.diagonal_apply_eq, Matrix.scalar_apply] at h
      apply Units.ext
      rw [h, hc1, Units.val_one]
    have hv : v = 1 := by
      have h := congrFun (congrFun hmat 3) 3
      simp only [coe_phi, phiUnits_three, Matrix.diagonal_apply_eq, Matrix.scalar_apply] at h
      apply Units.ext
      rw [h, hc1, Units.val_one]
    have hwv : w = 1 := by
      have h := congrFun (congrFun hmat 4) 4
      simp only [coe_phi, phiUnits_four, Matrix.diagonal_apply_eq, Matrix.scalar_apply] at h
      apply Units.ext
      rw [h, hc1, Units.val_one]
    exact ⟨ha1, hu, hv, hwv⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rw [phi_one]
    exact Subgroup.one_mem _

theorem psi_injective (hF : Nat.card F = 4) : Function.Injective (psi hF) := by
  intro p q hpq
  obtain ⟨a, u, v, w⟩ := p
  obtain ⟨a', u', v', w'⟩ := q
  simp only [psi, MonoidHom.coe_mk, OneHom.coe_mk] at hpq
  have hmem : (phi hF a u v w) * (phi hF a' u' v' w')⁻¹ ∈ LinearFlag.scalars 6 F := by
    rw [← LinearFlag.proj_eq_one_iff, map_mul, map_inv, hpq, mul_inv_cancel]
  have hmem' : phi hF (a * a'⁻¹) (u * u'⁻¹) (v * v'⁻¹) (w * w'⁻¹) ∈ LinearFlag.scalars 6 F := by
    simpa only [phi_mul, phi_inv] using hmem
  rw [phi_mem_scalars_iff] at hmem'
  obtain ⟨ha, hu, hv, hw⟩ := hmem'
  have ha' : a = a' := by
    have h := congrArg (· * a') ha
    simpa using h
  have hu' : u = u' := by
    have h := congrArg (· * u') hu
    simpa using h
  have hv' : v = v' := by
    have h := congrArg (· * v') hv
    simpa using h
  have hw' : w = w' := by
    have h := congrArg (· * w') hw
    simpa using h
  rw [ha', hu', hv', hw']

theorem card_Bs (hF : Nat.card F = 4) : Nat.card (Bs hF) = 81 := by
  haveI : Finite (Fˣ × Fˣ × Fˣ × Fˣ) := inferInstance
  rw [Bs, MonoidHom.range_eq_map, Subgroup.card_map_of_injective (psi_injective hF),
    Subgroup.card_top, Nat.card_prod, Nat.card_prod, Nat.card_prod, card_units_eq_three hF]

theorem isElemAbelian_Bs (hF : Nat.card F = 4) : CFSG.Open.IsElemAbelian 3 (Bs hF) := by
  constructor
  · rw [isMulCommutative_iff]
    rintro ⟨p, hp⟩ ⟨q, hq⟩
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hp
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hq
    apply Subtype.ext
    change psi hF r * psi hF s = psi hF s * psi hF r
    rw [← map_mul, ← map_mul, mul_comm r s]
  · rintro x hx
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨a, u, v, w⟩ := p
    change (psi hF (a, u, v, w)) ^ 3 = 1
    rw [← map_pow]
    have hp : ((a, u, v, w) : Fˣ × Fˣ × Fˣ × Fˣ) ^ 3 = 1 := by
      rw [show ((a, u, v, w) : Fˣ × Fˣ × Fˣ × Fˣ) = (a, (u, (v, w))) from rfl]
      rw [Prod.pow_def, Prod.pow_def, Prod.pow_def]
      simp [units_pow_three hF]
    rw [hp, map_one]

theorem mem_Bs (hF : Nat.card F = 4) (p : Fˣ × Fˣ × Fˣ × Fˣ) : psi hF p ∈ Bs hF :=
  MonoidHom.mem_range.mpr ⟨p, rfl⟩

theorem xw_mem_Bs (hF : Nat.card F = 4) (ω : Fˣ) : xw hF ω ∈ Bs hF :=
  mem_Bs hF (ω, 1, 1, 1)

theorem xw_ne_one (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    xw hF ω ≠ 1 := by
  intro h
  have hmem : phi hF ω 1 1 1 ∈ LinearFlag.scalars 6 F := by
    rw [← LinearFlag.proj_eq_one_iff]
    exact h
  rw [phi_mem_scalars_iff] at hmem
  have h1 : ω = 1 := hmem.1
  rw [h1, orderOf_one] at hω
  omega


theorem omega_pow_three {ω : Fˣ} (hω : orderOf ω = 3) : ω ^ 3 = 1 := by
  rw [← hω]
  exact pow_orderOf_eq_one ω

theorem omega_ne_one {ω : Fˣ} (hω : orderOf ω = 3) : ω ≠ 1 := by
  intro h
  rw [h, orderOf_one] at hω
  omega

theorem omega_sq_ne_one {ω : Fˣ} (hω : orderOf ω = 3) : ω ^ 2 ≠ 1 := by
  intro h
  have h2 : orderOf ω ∣ 2 := orderOf_dvd_of_pow_eq_one h
  rw [hω] at h2
  omega

private theorem omega_ne_sq {ω : Fˣ} (hω : orderOf ω = 3) : ω ≠ ω ^ 2 := by
  intro h
  have h1 : ω ^ 2 * ω⁻¹ = ω := by rw [pow_two, mul_assoc, mul_inv_cancel, mul_one]
  have h4 : ω = 1 := by
    calc ω = ω ^ 2 * ω⁻¹ := h1.symm
      _ = ω * ω⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel ω
  exact omega_ne_one hω h4

private theorem zpowers_omega_eq_top (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    Subgroup.zpowers ω = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, hω, card_units_eq_three hF]

theorem exists_zpow_eq_omega (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3)
    (a : Fˣ) : ∃ k : ℤ, ω ^ k = a := by
  have hmem : a ∈ Subgroup.zpowers ω := by
    rw [zpowers_omega_eq_top hF hω]
    exact Subgroup.mem_top a
  exact Subgroup.mem_zpowers_iff.mp hmem

@[expose]
noncomputable def hsplit (hF : Nat.card F = 4) (ω : Fˣ) :
    SpecialLinearGroup (Fin 6) F :=
  phi hF ω 1 1 1

theorem xw_eq_proj_hsplit (hF : Nat.card F = 4) (ω : Fˣ) :
    xw hF ω = LinearFlag.proj 6 F (hsplit hF ω) := rfl

@[expose]
def I01 : Finset (Fin 6) := {0, 1}

private theorem hsplit_mem_block (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    hsplit hF ω ∈ blockSpecialLinear I01 := by
  rw [mem_blockSpecialLinear]
  intro i j hij
  have hmat : (hsplit hF ω : Matrix (Fin 6) (Fin 6) F) =
      Matrix.diagonal fun k => (phiUnits ω 1 1 1 k : F) := rfl
  rw [hmat]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    fin_cases i <;> simp_all [I01, phiUnits]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem hsplit_isRootSplit (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    IsRootSplit (0 : Fin 6) 1 (hsplit hF ω) := by
  refine ⟨hsplit_mem_block hF hω, ?_, ?_⟩
  · intro i j hij
    have hmat : (hsplit hF ω : Matrix (Fin 6) (Fin 6) F) =
        Matrix.diagonal fun k => (phiUnits ω 1 1 1 k : F) := rfl
    rw [hmat, Matrix.diagonal_apply_ne _ hij]
  · change (phiUnits ω 1 1 1 (0 : Fin 6) : F) ≠ (phiUnits ω 1 1 1 (1 : Fin 6) : F)
    rw [phiUnits_zero, phiUnits_one]
    exact fun h => omega_ne_sq hω (Units.ext h)

@[expose]
noncomputable def J : Subgroup (LinearFlag.projectiveSL 6 F) :=
  blockSL I01ᶜ

theorem J_le_centralizer_xw (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    J (F := F) ≤ Subgroup.centralizer ({xw hF ω} : Set (LinearFlag.projectiveSL 6 F)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨A, hA, rfl⟩ := mem_blockSL.mp hg
  have hcomm : Commute A (hsplit hF ω) :=
    commute_blockSpecialLinear_of_disjoint
      (by
        rw [Finset.disjoint_left]
        intro x hx hx'
        exact (Finset.mem_compl.1 hx) hx') hA (hsplit_mem_block hF hω)
  exact hcomm.map (LinearFlag.proj 6 F)


private theorem matrix_diag_single {d : Fin 6 → F} (hd : ∀ k, d k ≠ 0) {i j : Fin 6}
    (hij : i ≠ j) (c : F) :
    Matrix.diagonal d * (1 + Matrix.single i j c) =
      (1 + Matrix.single i j (d i * c * (d j)⁻¹)) * Matrix.diagonal d := by
  ext k l
  by_cases hkl : k = l
  · subst hkl
    by_cases hki : k = i
    · subst hki
      simp [Matrix.mul_apply, Matrix.single_apply, Matrix.diagonal_apply, Finset.sum_ite_eq,
        Finset.mem_univ, hij.symm]
    · simp [Matrix.mul_apply, Matrix.single_apply, Matrix.diagonal_apply, Finset.sum_ite_eq,
        Finset.mem_univ, hki, Ne.symm hki]
  · by_cases hki : k = i <;> by_cases hlj : l = j
    · subst hki; subst hlj
      have hdl : d l ≠ 0 := hd l
      simp [Matrix.mul_apply, Matrix.single_apply, Matrix.diagonal_apply, hkl]
      field_simp
    · subst hki
      simp [Matrix.mul_apply, Matrix.single_apply, Matrix.diagonal_apply, hkl, Ne.symm hlj]
    · subst hlj
      simp [Matrix.mul_apply, Matrix.single_apply, Matrix.diagonal_apply, hkl, Ne.symm hki]
    · simp [Matrix.mul_apply, Matrix.single_apply, Matrix.diagonal_apply, hkl, Ne.symm hki,
        Ne.symm hlj]

theorem diagSL_conj_transvection (hF : Nat.card F = 4) {e : Fin 6 → Fˣ}
    (h : ∏ i, (e i : F) = 1) {i j : Fin 6} (hij : i ≠ j) (c : F) :
    diagSL (fun k => (e k : F)) h * SpecialLinearGroup.transvection hij c *
        (diagSL (fun k => (e k : F)) h)⁻¹ =
      SpecialLinearGroup.transvection hij ((e i : F) * c * ((e j : F))⁻¹) := by
  have hd : ∀ k, (e k : F) ≠ 0 := fun k => Units.ne_zero (e k)
  have hmul : diagSL (fun k => (e k : F)) h * SpecialLinearGroup.transvection hij c =
      SpecialLinearGroup.transvection hij ((e i : F) * c * ((e j : F))⁻¹) *
        diagSL (fun k => (e k : F)) h := by
    apply Subtype.ext
    change Matrix.diagonal (fun k => (e k : F)) * (1 + Matrix.single i j c) =
      (1 + Matrix.single i j ((e i : F) * c * ((e j : F))⁻¹)) *
        Matrix.diagonal (fun k => (e k : F))
    exact matrix_diag_single hd hij c
  calc diagSL (fun k => (e k : F)) h * SpecialLinearGroup.transvection hij c *
        (diagSL (fun k => (e k : F)) h)⁻¹
      = (SpecialLinearGroup.transvection hij ((e i : F) * c * ((e j : F))⁻¹) *
          diagSL (fun k => (e k : F)) h) * (diagSL (fun k => (e k : F)) h)⁻¹ := by rw [hmul]
    _ = SpecialLinearGroup.transvection hij ((e i : F) * c * ((e j : F))⁻¹) := by group

end A5Four

end CFSG.LocalAnalysis.GLTheoremA.Y10F
