module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Sylow
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankTwoShapes CFSG.BenderSuzuki
  CFSG.BenderSuzuki.MatrixGroups
open scoped commutatorElement

noncomputable section

variable {K : Type} [Field K]

@[expose] def u34TauMatrix (ω : K) : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![ω, ω ^ 3, ω]

theorem u34TauMatrix_det (ω : K) : (u34TauMatrix ω).det = ω ^ 5 := by
  simp [u34TauMatrix, Matrix.det_diagonal, Fin.prod_univ_three]
  ring

@[expose] def u34Tau (ω : K) (hω : ω ^ 5 = 1) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (u34TauMatrix ω)
    (by rw [u34TauMatrix_det, hω]; exact one_ne_zero)

@[simp] theorem u34Tau_val (ω : K) (hω : ω ^ 5 = 1) :
    ((u34Tau ω hω : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = u34TauMatrix ω :=
  rfl

theorem u34Tau_pow_five (ω : K) (hω : ω ^ 5 = 1) : u34Tau ω hω ^ 5 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, u34Tau_val, u34TauMatrix, Matrix.diagonal_pow, Units.val_one,
    ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp <;> grind

theorem u34Tau_mem_specialSubgroup (ω : K) (hω : ω ^ 5 = 1) (σ : K ≃+* K)
    (hinv : Function.Involutive σ) (hσ : ∀ x, σ x = x ^ 4) :
    u34Tau ω hω ∈ (antidiagonalHermitianForm σ hinv).specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · rw [u34Tau_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianForm.conjTranspose, antidiagonalHermitianForm, u34TauMatrix,
        Matrix.mul_apply, Matrix.diagonal_apply, hσ] <;> grind
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, u34Tau_val, u34TauMatrix_det, hω]
    rfl

theorem u34TauMatrix_mul_unitaryFourMatrix (ω : K) (hω : ω ^ 5 = 1) (a b : K) :
    u34TauMatrix ω * unitaryFourMatrix a b =
      unitaryFourMatrix (ω ^ 2 * a) b * u34TauMatrix ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u34TauMatrix, unitaryFourMatrix, Matrix.mul_apply, Matrix.diagonal_apply] <;> grind

def u34Twist (hK : Nat.card K = 16) (ω : K) (hω : ω ^ 5 = 1) (x : unitaryFourW K hK) :
    unitaryFourW K hK :=
  UnitaryFourW.mk hK (ω ^ 2 * UnitaryFourW.fst x) (UnitaryFourW.snd x) (by
    rw [mul_pow, ← pow_mul, show 2 * 5 = 5 * 2 from rfl, pow_mul, hω, one_pow, one_mul]
    exact UnitaryFourW.snd_add_snd_pow_four x)

@[simp] theorem u34Twist_fst (hK : Nat.card K = 16) (ω : K) (hω : ω ^ 5 = 1)
    (x : unitaryFourW K hK) :
    UnitaryFourW.fst (u34Twist hK ω hω x) = ω ^ 2 * UnitaryFourW.fst x :=
  UnitaryFourW.fst_mk _ _ _

@[simp] theorem u34Twist_snd (hK : Nat.card K = 16) (ω : K) (hω : ω ^ 5 = 1)
    (x : unitaryFourW K hK) :
    UnitaryFourW.snd (u34Twist hK ω hω x) = UnitaryFourW.snd x :=
  UnitaryFourW.snd_mk _ _ _

theorem u34Twist_eq_self (hK : Nat.card K = 16) (ω : K) (hω : ω ^ 5 = 1)
    {x : unitaryFourW K hK} (hx : UnitaryFourW.fst x = 0) : u34Twist hK ω hω x = x :=
  UnitaryFourW.ext (by rw [u34Twist_fst, hx, mul_zero]) (u34Twist_snd _ _ _ _)

theorem u34Tau_conj (hK : Nat.card K = 16) (ω : K) (hω : ω ^ 5 = 1) (x : unitaryFourW K hK) :
    u34Tau ω hω * (x : GL (Fin 3) K) * (u34Tau ω hω)⁻¹ =
      ((u34Twist hK ω hω x : unitaryFourW K hK) : GL (Fin 3) K) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, u34Tau_val, UnitaryFourW.coe_eq x,
    u34TauMatrix_mul_unitaryFourMatrix ω hω, UnitaryFourW.coe_eq (u34Twist hK ω hω x),
    u34Twist_fst, u34Twist_snd]

theorem u34_mem_of_twist (hK : Nat.card K = 16) (ω : K) (hω : ω ^ 5 = 1) (hω1 : ω ≠ 1)
    (C : Subgroup (unitaryFourW K hK))
    (hc : ∀ y : unitaryFourW K hK, y * u34Twist hK ω hω y⁻¹ ∈ C) (y : unitaryFourW K hK) :
    y ∈ C := by
  have hchar := charP_two_of_natCard_eq_sixteen hK
  have h1 : (1 + ω ^ 2) ≠ 0 := by
    intro h
    apply hω1
    have h2 : ω ^ 2 = 1 := (CharTwo.add_eq_zero.mp h).symm
    calc ω = ω * (ω ^ 2) ^ 2 := by rw [h2]; ring
      _ = ω ^ 5 := by ring
      _ = 1 := hω
  have hfst : ∀ x : unitaryFourW K hK, ∃ c ∈ C, UnitaryFourW.fst c = UnitaryFourW.fst x := by
    intro x
    obtain ⟨y, hy⟩ := UnitaryFourW.exists_fst_eq (hK := hK)
      ((1 + ω ^ 2)⁻¹ * UnitaryFourW.fst x)
    refine ⟨y * u34Twist hK ω hω y⁻¹, hc y, ?_⟩
    rw [UnitaryFourW.fst_mul, u34Twist_fst, UnitaryFourW.fst_inv, hy]
    calc (1 + ω ^ 2)⁻¹ * UnitaryFourW.fst x + ω ^ 2 * ((1 + ω ^ 2)⁻¹ * UnitaryFourW.fst x)
        = (1 + ω ^ 2) * ((1 + ω ^ 2)⁻¹ * UnitaryFourW.fst x) := by ring
      _ = UnitaryFourW.fst x := mul_inv_cancel_left₀ h1 _
  have hcomm : _root_.commutator (unitaryFourW K hK) ≤ C := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro p _ q _
    obtain ⟨c₁, hc₁, hf₁⟩ := hfst p
    obtain ⟨c₂, hc₂, hf₂⟩ := hfst q
    have hpq : ⁅p, q⁆ = ⁅c₁, c₂⁆ := by
      apply UnitaryFourW.ext
      · rw [UnitaryFourW.fst_commutatorElement, UnitaryFourW.fst_commutatorElement]
      · rw [UnitaryFourW.snd_commutatorElement, UnitaryFourW.snd_commutatorElement, hf₁, hf₂]
    rw [hpq]
    exact C.mul_mem (C.mul_mem (C.mul_mem hc₁ hc₂) (C.inv_mem hc₁)) (C.inv_mem hc₂)
  have hker : (UnitaryFourW.firstCoord hK).ker ≤ C := by
    rw [← UnitaryFourW.commutator_eq_ker_firstCoord]
    exact hcomm
  obtain ⟨c, hcC, hf⟩ := hfst y
  have hk : y * c⁻¹ ∈ (UnitaryFourW.firstCoord hK).ker := by
    rw [UnitaryFourW.mem_ker_firstCoord, UnitaryFourW.fst_mul, UnitaryFourW.fst_inv, hf]
    exact CharTwo.add_self_eq_zero _
  have h := C.mul_mem (hker hk) hcC
  rwa [inv_mul_cancel_right] at h

theorem u34_data_aux (hK : Nat.card K = 16) (ω : K) (hω : ω ^ 5 = 1) (hω1 : ω ≠ 1)
    {Y : Type} [Group Y] [Finite Y] (φ : unitaryFourW K hK →* Y)
    (hφ : Function.Injective φ) (w : Y)
    (hconj : ∀ x, w * φ x * w⁻¹ = φ (u34Twist hK ω hω x)) :
    IsPGroup 2 φ.range ∧ Nat.card φ.range = 64 ∧ (∀ x ∈ φ.range, x ^ 4 = 1) ∧
      Nat.card (Subgroup.center ↥φ.range) = 4 ∧
      (∀ x : Y, x ∈ φ.range → (∀ y ∈ φ.range, x * y = y * x) → x * x = 1 ∧ w * x * w⁻¹ = x) ∧
      w ∈ Subgroup.normalizer (φ.range : Set Y) ∧ ⁅φ.range, Subgroup.zpowers w⁆ = φ.range := by
  have hfin : Finite (unitaryFourW K hK) := UnitaryFourW.finite_unitaryFourW
  let eP : unitaryFourW K hK ≃* φ.range := MonoidHom.ofInjective hφ
  have hcard : Nat.card φ.range = 64 := by
    rw [← Nat.card_congr eP.toEquiv]
    exact UnitaryFourW.natCard_unitaryFourW
  have hnorm : w ∈ Subgroup.normalizer (φ.range : Set Y) := by
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨y, rfl⟩
    exact ⟨_, (hconj y).symm⟩
  refine ⟨?_, hcard, ?_, ?_, ?_, hnorm, ?_⟩
  · exact IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)
  · rintro _ ⟨y, rfl⟩
    rw [← map_pow, UnitaryFourW.pow_four_eq_one, map_one]
  · rw [← Nat.card_congr (Subgroup.centerCongr eP).toEquiv]
    exact UnitaryFourW.natCard_center
  · rintro _ ⟨y, rfl⟩ hcomm
    have hy : y ∈ Subgroup.center (unitaryFourW K hK) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hφ
      rw [map_mul, map_mul]
      exact (hcomm (φ g) ⟨g, rfl⟩).symm
    have hy0 : UnitaryFourW.fst y = 0 := by
      have h := hy
      rw [UnitaryFourW.center_eq_ker_firstCoord (hK := hK)] at h
      exact UnitaryFourW.mem_ker_firstCoord.mp h
    refine ⟨?_, ?_⟩
    · rw [← map_mul, ← pow_two, UnitaryFourW.sq_eq_one_of_mem_center hy, map_one]
    · rw [hconj, u34Twist_eq_self hK ω hω hy0]
  · apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      have hg₂' : g₂ ∈ Subgroup.normalizer (φ.range : Set Y) :=
        Subgroup.zpowers_le.mpr hnorm hg₂
      have h := Subgroup.mul_mem _ hg₁
        ((Subgroup.mem_normalizer_iff.mp hg₂' g₁⁻¹).mp (Subgroup.inv_mem _ hg₁))
      simpa [commutatorElement_def, mul_assoc] using h
    · intro p hp
      obtain ⟨y, rfl⟩ := hp
      refine u34_mem_of_twist hK ω hω hω1 ((⁅φ.range, Subgroup.zpowers w⁆).comap φ) ?_ y
      intro y
      have h := Subgroup.commutator_mem_commutator (H₁ := φ.range)
        (H₂ := Subgroup.zpowers w) (g₁ := φ y) (g₂ := w) ⟨y, rfl⟩ (Subgroup.mem_zpowers w)
      rw [Subgroup.mem_comap, map_mul, ← hconj, map_inv]
      simpa [commutatorElement_def, mul_assoc] using h

theorem u34_exists_root_five (hK : Nat.card K = 16) : ∃ ω : K, ω ^ 5 = 1 ∧ ω ≠ 1 := by
  have hunits : Nat.card Kˣ = 15 := by
    rw [Nat.card_units, hK]
  have : Finite Kˣ := Nat.finite_of_card_ne_zero (by rw [hunits]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 5 (by rw [hunits]; norm_num)
  refine ⟨(u : K), ?_, ?_⟩
  · have h := pow_orderOf_eq_one u
    rw [hu] at h
    simpa using congrArg Units.val h
  · intro h
    have hu1 : u = 1 := Units.ext h
    rw [hu1, orderOf_one] at hu
    omega

theorem u34_data {Y : Type} [Group Y] [Finite Y] (h : LieModel Y .PSU 3 2 2) :
    ∃ (P : Subgroup Y) (w : Y),
      IsPGroup 2 P ∧ Nat.card P = 64 ∧ (∀ x ∈ P, x ^ 4 = 1) ∧
      Nat.card (Subgroup.center ↥P) = 4 ∧
      (∀ x : Y, x ∈ P → (∀ y ∈ P, x * y = y * x) → x * x = 1 ∧ w * x * w⁻¹ = x) ∧
      w ^ 5 = 1 ∧ w ∈ Subgroup.normalizer (P : Set Y) ∧ ⁅P, Subgroup.zpowers w⁆ = P := by
  have hst : StatedClassicalModel Y .PSU 3 2 2 := by
    rcases h with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨eY⟩ := (statedClassicalModel_PSU_three_two_iff Y 2 le_rfl).mp hst
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  obtain ⟨σ, hinv, hσ, -, -, ⟨eG⟩⟩ := exists_psu_antidiagonal hK
  obtain ⟨ω, hω, hω1⟩ := u34_exists_root_five hK
  let e : Y ≃* ProjectiveSpecialUnitaryMatrixGroup (antidiagonalHermitianForm σ hinv) :=
    eY.trans eG.symm
  let ι := unitaryFourWToPSU hK σ hinv hσ
  let w₀ : ProjectiveSpecialUnitaryMatrixGroup (antidiagonalHermitianForm σ hinv) :=
    ⟨Matrix.ProjGenLinGroup.mk (u34Tau ω hω),
      Subgroup.mem_map_of_mem _ (u34Tau_mem_specialSubgroup ω hω σ hinv hσ)⟩
  have hconj0 : ∀ x, w₀ * ι x * w₀⁻¹ = ι (u34Twist hK ω hω x) := by
    intro x
    apply Subtype.ext
    change Matrix.ProjGenLinGroup.mk (u34Tau ω hω) *
        Matrix.ProjGenLinGroup.mk (x : GL (Fin 3) (GaloisField 2 4)) *
        (Matrix.ProjGenLinGroup.mk (u34Tau ω hω))⁻¹ =
      Matrix.ProjGenLinGroup.mk ((u34Twist hK ω hω x : unitaryFourW _ hK) : GL (Fin 3) _)
    rw [← map_inv, ← map_mul, ← map_mul, u34Tau_conj]
  have hw0 : w₀ ^ 5 = 1 := by
    apply Subtype.ext
    change (Matrix.ProjGenLinGroup.mk (u34Tau ω hω)) ^ 5 = 1
    rw [← map_pow, u34Tau_pow_five, map_one]
  let φ : unitaryFourW (GaloisField 2 4) hK →* Y := e.symm.toMonoidHom.comp ι
  have hφ : Function.Injective φ :=
    e.symm.injective.comp (unitaryFourWToPSU_injective hK σ hinv hσ)
  have hconj : ∀ x, e.symm w₀ * φ x * (e.symm w₀)⁻¹ = φ (u34Twist hK ω hω x) := by
    intro x
    change e.symm w₀ * e.symm (ι x) * (e.symm w₀)⁻¹ = e.symm (ι (u34Twist hK ω hω x))
    rw [← map_inv, ← map_mul, ← map_mul, hconj0]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := u34_data_aux hK ω hω hω1 φ hφ (e.symm w₀) hconj
  refine ⟨φ.range, e.symm w₀, h1, h2, h3, h4, h5, ?_, h6, h7⟩
  rw [← map_pow, hw0, map_one]

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
