module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamA5Four
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.OmegaAux
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace A5Four

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot
open Matrix

variable {F : Type} [Field F] [Finite F]

private theorem i23 : (2 : Fin 6) ≠ 3 := by decide
private theorem i24 : (2 : Fin 6) ≠ 4 := by decide
private theorem i25 : (2 : Fin 6) ≠ 5 := by decide

private def sigmaMat (v : Fin 3 → F) : Matrix (Fin 6) (Fin 6) F :=
  1 + single 2 3 (v 0) + single 2 4 (v 1) + single 2 5 (v 2)

private theorem sigmaMat_eq_prod (v : Fin 3 → F) :
    sigmaMat v =
      (SpecialLinearGroup.transvection i23 (v 0) : Matrix (Fin 6) (Fin 6) F) *
        (SpecialLinearGroup.transvection i24 (v 1) : Matrix (Fin 6) (Fin 6) F) *
          (SpecialLinearGroup.transvection i25 (v 2) : Matrix (Fin 6) (Fin 6) F) := by
  rw [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaMat, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_six]

private theorem det_sigmaMat (v : Fin 3 → F) : (sigmaMat v).det = 1 := by
  rw [sigmaMat_eq_prod, Matrix.det_mul, Matrix.det_mul]
  simp

private noncomputable def sigmaFun (v : Fin 3 → F) : SpecialLinearGroup (Fin 6) F :=
  ⟨sigmaMat v, det_sigmaMat v⟩

@[simp]
private theorem coe_sigmaFun (v : Fin 3 → F) :
    (sigmaFun v : Matrix (Fin 6) (Fin 6) F) = sigmaMat v := rfl

private theorem sigmaFun_eq_prod (v : Fin 3 → F) :
    sigmaFun v = SpecialLinearGroup.transvection i23 (v 0) *
      SpecialLinearGroup.transvection i24 (v 1) * SpecialLinearGroup.transvection i25 (v 2) := by
  apply Subtype.ext
  change sigmaMat v =
    (SpecialLinearGroup.transvection i23 (v 0) : Matrix (Fin 6) (Fin 6) F) *
      (SpecialLinearGroup.transvection i24 (v 1) : Matrix (Fin 6) (Fin 6) F) *
        (SpecialLinearGroup.transvection i25 (v 2) : Matrix (Fin 6) (Fin 6) F)
  exact sigmaMat_eq_prod v

private theorem sigmaMat_zero : sigmaMat (0 : Fin 3 → F) = 1 := by
  simp [sigmaMat]

private theorem sigmaFun_zero : sigmaFun (0 : Fin 3 → F) = 1 := by
  apply Subtype.ext
  change sigmaMat (0 : Fin 3 → F) = (1 : Matrix (Fin 6) (Fin 6) F)
  exact sigmaMat_zero

private theorem sigmaMat_add (v w : Fin 3 → F) :
    sigmaMat (v + w) = sigmaMat v * sigmaMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaMat, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_six, Pi.add_apply]
    <;> ring

private theorem sigmaFun_add (v w : Fin 3 → F) :
    sigmaFun (v + w) = sigmaFun v * sigmaFun w := by
  apply Subtype.ext
  change sigmaMat (v + w) = sigmaMat v * sigmaMat w
  exact sigmaMat_add v w

private theorem sigmaFun_neg (v : Fin 3 → F) : sigmaFun (-v) = (sigmaFun v)⁻¹ := by
  have h : sigmaFun (-v) * sigmaFun v = 1 := by
    rw [← sigmaFun_add, neg_add_cancel, sigmaFun_zero]
  calc sigmaFun (-v) = sigmaFun (-v) * 1 := (mul_one _).symm
    _ = sigmaFun (-v) * (sigmaFun v * (sigmaFun v)⁻¹) := by rw [mul_inv_cancel]
    _ = (sigmaFun (-v) * sigmaFun v) * (sigmaFun v)⁻¹ := by group
    _ = (sigmaFun v)⁻¹ := by rw [h, one_mul]

private theorem sigmaFun_mem_block (v : Fin 3 → F) :
    sigmaFun v ∈ blockSpecialLinear I01ᶜ := by
  rw [mem_blockSpecialLinear]
  intro i j hij
  have hmat : (sigmaFun v : Matrix (Fin 6) (Fin 6) F) = sigmaMat v := rfl
  rw [hmat]
  fin_cases i <;> fin_cases j <;>
    simp_all [sigmaMat, I01, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

private theorem sigmaFun_injective : Function.Injective (sigmaFun (F := F)) := by
  intro v w h
  have hmat : sigmaMat v = sigmaMat w := by
    have h' : (sigmaFun v : Matrix (Fin 6) (Fin 6) F) = (sigmaFun w : Matrix (Fin 6) (Fin 6) F) := by
      rw [h]
    rwa [coe_sigmaFun, coe_sigmaFun] at h'
  funext i
  fin_cases i
  · have h' := congrFun (congrFun hmat 2) 3
    simpa [sigmaMat, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] using h'
  · have h' := congrFun (congrFun hmat 2) 4
    simpa [sigmaMat, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] using h'
  · have h' := congrFun (congrFun hmat 2) 5
    simpa [sigmaMat, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] using h'

private noncomputable def sigmaHom (hF : Nat.card F = 4) :
    Multiplicative (Fin 3 → F) →* SpecialLinearGroup (Fin 6) F where
  toFun v := sigmaFun v.toAdd
  map_one' := by
    simpa using sigmaFun_zero (F := F)
  map_mul' v w := by
    simpa using sigmaFun_add v.toAdd w.toAdd

noncomputable def sigmaProj (hF : Nat.card F = 4) :
    Multiplicative (Fin 3 → F) →* LinearFlag.projectiveSL 6 F :=
  (LinearFlag.proj 6 F).comp (sigmaHom hF)

private theorem sigmaProj_apply (hF : Nat.card F = 4) (v : Multiplicative (Fin 3 → F)) :
    sigmaProj hF v = LinearFlag.proj 6 F (sigmaFun v.toAdd) := rfl

private theorem sigmaProj_injective (hF : Nat.card F = 4) :
    Function.Injective (sigmaProj hF) := by
  intro x y hxy
  have h1 : LinearFlag.proj 6 F (sigmaFun x.toAdd) =
      LinearFlag.proj 6 F (sigmaFun y.toAdd) := hxy
  have hmem : sigmaFun x.toAdd * (sigmaFun y.toAdd)⁻¹ ∈ LinearFlag.scalars 6 F := by
    rw [← LinearFlag.proj_eq_one_iff, map_mul, map_inv, h1, mul_inv_cancel]
  have hmem' : sigmaFun (x.toAdd + -y.toAdd) ∈ LinearFlag.scalars 6 F := by
    rw [sigmaFun_add, sigmaFun_neg]
    exact hmem
  have hblock := sigmaFun_mem_block (x.toAdd + -y.toAdd)
  rw [LinearFlag.mem_scalars] at hmem'
  obtain ⟨c, -, hc⟩ := hmem'
  have h00 := (mem_blockSpecialLinear.1 hblock) 0 0 (Or.inl (by simp [I01]))
  have hc1 : c = 1 := by
    have hmat : (sigmaFun (x.toAdd + -y.toAdd) : Matrix (Fin 6) (Fin 6) F) =
        Matrix.scalar (Fin 6) (c : F) := hc
    have h' : (sigmaFun (x.toAdd + -y.toAdd) : Matrix (Fin 6) (Fin 6) F) 0 0 = (c : F) := by
      rw [hmat]
      simp [Matrix.scalar_apply]
    exact Units.ext (by rw [← h', h00]; rfl)
  have hone : sigmaFun (x.toAdd + -y.toAdd) = 1 := by
    apply Subtype.ext
    rw [hc, hc1]
    simp [Matrix.scalar]
  have hzero : x.toAdd + -y.toAdd = 0 := by
    apply sigmaFun_injective
    rw [hone, sigmaFun_zero]
  have hxy' : x.toAdd = y.toAdd := by
    have := congrArg (· + y.toAdd) hzero
    simpa using this
  exact Multiplicative.toAdd.injective hxy'

@[expose]
noncomputable def S (hF : Nat.card F = 4) :
    Subgroup (LinearFlag.projectiveSL 6 F) :=
  (sigmaProj hF).range

private theorem card_S (hF : Nat.card F = 4) : Nat.card (S hF) = 64 := by
  haveI : Finite (Multiplicative (Fin 3 → F)) := inferInstance
  rw [S, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (sigmaProj_injective hF), Subgroup.card_top]
  change Nat.card (Fin 3 → F) = 64
  rw [Nat.card_fun, hF]
  norm_num

theorem isPGroup_S (hF : Nat.card F = 4) : IsPGroup 2 (S hF) :=
  IsPGroup.of_card (n := 6) (by rw [card_S]; norm_num)

theorem S_le_J (hF : Nat.card F = 4) : S hF ≤ J (F := F) := by
  intro s hs
  obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hs
  exact Subgroup.mem_map_of_mem _ (sigmaFun_mem_block v.toAdd)

private theorem transvection_mem_S (hF : Nat.card F = 4) (j : Fin 6) (hj : j = 3 ∨ j = 4 ∨ j = 5) :
    LinearFlag.proj 6 F (SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ j by
      rcases hj with rfl | rfl | rfl <;> decide) 1) ∈ S hF := by
  classical
  rcases hj with rfl | rfl | rfl
  · refine MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (Pi.single 0 1), ?_⟩
    rw [sigmaProj_apply, sigmaFun_eq_prod]
    simp [Pi.single_eq_same, Pi.single_eq_of_ne, SpecialLinearGroup.transvection_coeff_zero]
  · refine MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (Pi.single 1 1), ?_⟩
    rw [sigmaProj_apply, sigmaFun_eq_prod]
    simp [Pi.single_eq_same, Pi.single_eq_of_ne, SpecialLinearGroup.transvection_coeff_zero]
  · refine MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (Pi.single 2 1), ?_⟩
    rw [sigmaProj_apply, sigmaFun_eq_prod]
    simp [Pi.single_eq_same, Pi.single_eq_of_ne, SpecialLinearGroup.transvection_coeff_zero]

private def sigmaScale (a u v w : Fˣ) (x : Fin 3 → F) : Fin 3 → F :=
  ![(phiUnits a u v w 2 : F) * x 0 * ((phiUnits a u v w 3 : F))⁻¹,
    (phiUnits a u v w 2 : F) * x 1 * ((phiUnits a u v w 4 : F))⁻¹,
    (phiUnits a u v w 2 : F) * x 2 * ((phiUnits a u v w 5 : F))⁻¹]

private theorem phi_conj_sigma (hF : Nat.card F = 4) (a u v w : Fˣ) (x : Fin 3 → F) :
    phi hF a u v w * sigmaFun x * (phi hF a u v w)⁻¹ = sigmaFun (sigmaScale a u v w x) := by
  have hD : phi hF a u v w =
      diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w) := rfl
  rw [sigmaFun_eq_prod, hD]
  have h1 : diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w) *
      SpecialLinearGroup.transvection i23 (x 0) *
        (diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w))⁻¹ =
      SpecialLinearGroup.transvection i23
        ((phiUnits a u v w 2 : F) * x 0 * ((phiUnits a u v w 3 : F))⁻¹) :=
    diagSL_conj_transvection hF (prod_phiUnits hF a u v w) i23 (x 0)
  have h2 : diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w) *
      SpecialLinearGroup.transvection i24 (x 1) *
        (diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w))⁻¹ =
      SpecialLinearGroup.transvection i24
        ((phiUnits a u v w 2 : F) * x 1 * ((phiUnits a u v w 4 : F))⁻¹) :=
    diagSL_conj_transvection hF (prod_phiUnits hF a u v w) i24 (x 1)
  have h3 : diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w) *
      SpecialLinearGroup.transvection i25 (x 2) *
        (diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w))⁻¹ =
      SpecialLinearGroup.transvection i25
        ((phiUnits a u v w 2 : F) * x 2 * ((phiUnits a u v w 5 : F))⁻¹) :=
    diagSL_conj_transvection hF (prod_phiUnits hF a u v w) i25 (x 2)
  calc diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w) *
        (SpecialLinearGroup.transvection i23 (x 0) * SpecialLinearGroup.transvection i24 (x 1) *
          SpecialLinearGroup.transvection i25 (x 2)) *
        (diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w))⁻¹
      = (diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w) *
            SpecialLinearGroup.transvection i23 (x 0) *
            (diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w))⁻¹) *
          (diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w) *
            SpecialLinearGroup.transvection i24 (x 1) *
            (diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w))⁻¹) *
          (diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w) *
            SpecialLinearGroup.transvection i25 (x 2) *
            (diagSL (fun k => (phiUnits a u v w k : F)) (prod_phiUnits hF a u v w))⁻¹) := by
        group
    _ = SpecialLinearGroup.transvection i23
          ((phiUnits a u v w 2 : F) * x 0 * ((phiUnits a u v w 3 : F))⁻¹) *
        SpecialLinearGroup.transvection i24
          ((phiUnits a u v w 2 : F) * x 1 * ((phiUnits a u v w 4 : F))⁻¹) *
        SpecialLinearGroup.transvection i25
          ((phiUnits a u v w 2 : F) * x 2 * ((phiUnits a u v w 5 : F))⁻¹) := by
        rw [h1, h2, h3]
    _ = sigmaFun (sigmaScale a u v w x) := by
        rw [sigmaFun_eq_prod]
        rfl

private theorem bs_conj_mem_S (hF : Nat.card F = 4) {b : LinearFlag.projectiveSL 6 F}
    (hb : b ∈ Bs hF) {s : LinearFlag.projectiveSL 6 F} (hs : s ∈ S hF) :
    b * s * b⁻¹ ∈ S hF := by
  obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hb
  obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hs
  obtain ⟨a, u, v', w⟩ := p
  refine MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (sigmaScale a u v' w v.toAdd), ?_⟩
  rw [sigmaProj_apply]
  show LinearFlag.proj 6 F (sigmaFun (sigmaScale a u v' w v.toAdd)) =
    psi hF (a, u, v', w) * LinearFlag.proj 6 F (sigmaFun v.toAdd) *
      (psi hF (a, u, v', w))⁻¹
  rw [show psi hF (a, u, v', w) = LinearFlag.proj 6 F (phi hF a u v' w) from rfl]
  rw [← map_inv, ← map_mul, ← map_mul, phi_conj_sigma]

theorem Bs_le_normalizer_S (hF : Nat.card F = 4) :
    Bs hF ≤ Subgroup.normalizer ((S hF) : Set (LinearFlag.projectiveSL 6 F)) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact bs_conj_mem_S hF hb
  · intro hs
    have h := bs_conj_mem_S hF (inv_mem hb) hs
    simpa [mul_assoc] using h

private theorem apply_eq_of_commute_transvection {u : SpecialLinearGroup (Fin 6) F}
    {i j : Fin 6} (hij : i ≠ j)
    (h : u * SpecialLinearGroup.transvection hij 1 =
      SpecialLinearGroup.transvection hij 1 * u) :
    (u : Matrix (Fin 6) (Fin 6) F) i i = (u : Matrix (Fin 6) (Fin 6) F) j j := by
  have h1 : (u : Matrix (Fin 6) (Fin 6) F) * (1 + Matrix.single i j 1) =
      (1 + Matrix.single i j 1) * (u : Matrix (Fin 6) (Fin 6) F) := by
    have h2 := congrArg (fun t : SpecialLinearGroup (Fin 6) F =>
      (t : Matrix (Fin 6) (Fin 6) F)) h
    simpa [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe] using h2
  have h2 := congrFun (congrFun h1 i) j
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply,
    Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, mul_one, one_mul] at h2
  exact add_left_cancel h2

theorem psi_eq_one_iff (hF : Nat.card F = 4) (p : Fˣ × Fˣ × Fˣ × Fˣ) :
    psi hF p = 1 ↔ p = 1 := by
  obtain ⟨a, u, v, w⟩ := p
  constructor
  · intro h
    have hmem : phi hF a u v w ∈ LinearFlag.scalars 6 F := by
      rw [← LinearFlag.proj_eq_one_iff]
      exact h
    rw [phi_mem_scalars_iff] at hmem
    obtain ⟨ha, hu, hv, hw⟩ := hmem
    rw [ha, hu, hv, hw]
    rfl
  · intro h
    rw [h]
    exact map_one _

theorem tuple_pow_three (a u v w : Fˣ) :
    ((a, u, v, w) : Fˣ × Fˣ × Fˣ × Fˣ) ^ 3 = (a ^ 3, u ^ 3, v ^ 3, w ^ 3) := by
  ext <;> simp

theorem tuple_omega_zpow (ω : Fˣ) (k : ℤ) :
    ((ω, 1, 1, 1) : Fˣ × Fˣ × Fˣ × Fˣ) ^ k = (ω ^ k, 1, 1, 1) := by
  ext <;> simp

theorem psi_one_mem_J (hF : Nat.card F = 4) (u v w : Fˣ) :
    psi hF (1, u, v, w) ∈ J (F := F) := by
  refine Subgroup.mem_map_of_mem (LinearFlag.proj 6 F) ?_
  rw [mem_blockSpecialLinear]
  intro i j hij
  have hmat : (phi hF 1 u v w : Matrix (Fin 6) (Fin 6) F) =
      Matrix.diagonal fun k => (phiUnits 1 u v w k : F) := rfl
  rw [hmat]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    fin_cases i <;> simp_all [I01, phiUnits]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem Bs_inf_centralizer_S (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    Bs hF ⊓ Subgroup.centralizer ((S hF) : Set (LinearFlag.projectiveSL 6 F)) =
      Subgroup.zpowers (xw hF ω) := by
  refine le_antisymm ?_ ?_
  · rintro b ⟨hb, hbS⟩
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hb
    obtain ⟨a, u, v, w⟩ := p
    have h23 : (u : F) = (v : F) := by
      have hmem := Subgroup.mem_centralizer_iff.mp hbS
        (LinearFlag.proj 6 F (SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 3 by decide) 1))
        (transvection_mem_S hF 3 (Or.inl rfl))
      have hc := commute_transvection_of_commute_proj (a := (2 : Fin 6)) (b := 3)
        (show (2 : Fin 6) ≠ 3 by decide) (show (0 : Fin 6) ≠ 2 by decide) (1 : F) hmem.symm
      have := apply_eq_of_commute_transvection (show (2 : Fin 6) ≠ 3 by decide) hc
      simpa [phiUnits] using this
    have h24 : (u : F) = (w : F) := by
      have hmem := Subgroup.mem_centralizer_iff.mp hbS
        (LinearFlag.proj 6 F (SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 4 by decide) 1))
        (transvection_mem_S hF 4 (Or.inr (Or.inl rfl)))
      have hc := commute_transvection_of_commute_proj (a := (2 : Fin 6)) (b := 4)
        (show (2 : Fin 6) ≠ 4 by decide) (show (0 : Fin 6) ≠ 2 by decide) (1 : F) hmem.symm
      have := apply_eq_of_commute_transvection (show (2 : Fin 6) ≠ 4 by decide) hc
      simpa [phiUnits] using this
    have h25 : (u : F) = (((u * v * w)⁻¹ : Fˣ) : F) := by
      have hmem := Subgroup.mem_centralizer_iff.mp hbS
        (LinearFlag.proj 6 F (SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 5 by decide) 1))
        (transvection_mem_S hF 5 (Or.inr (Or.inr rfl)))
      have hc := commute_transvection_of_commute_proj (a := (2 : Fin 6)) (b := 5)
        (show (2 : Fin 6) ≠ 5 by decide) (show (0 : Fin 6) ≠ 2 by decide) (1 : F) hmem.symm
      have := apply_eq_of_commute_transvection (show (2 : Fin 6) ≠ 5 by decide) hc
      simpa [phiUnits] using this
    have huv : u = v := Units.ext h23
    have huw : u = w := Units.ext h24
    have hu5 : u = (u * v * w)⁻¹ := Units.ext h25
    have hu1 : u = 1 := by
      have h3 : u * v * w = u ^ 3 := by
        rw [← huv, ← huw, pow_three, mul_assoc]
      have hu5' : u = (u ^ 3)⁻¹ := by rw [← h3]; exact hu5
      rw [units_pow_three hF u] at hu5'
      simpa using hu5'
    have hv1 : v = 1 := huv.symm.trans hu1
    have hw1 : w = 1 := huw.symm.trans hu1
    rw [hu1, hv1, hw1]
    obtain ⟨k, hk⟩ := exists_zpow_eq_omega hF hω a
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    rw [xw, ← map_zpow]
    have hpow : ((ω, 1, 1, 1) : Fˣ × Fˣ × Fˣ × Fˣ) ^ k = (a, 1, 1, 1) := by
      rw [tuple_omega_zpow, hk]
    rw [hpow]
  · rw [Subgroup.zpowers_le]
    refine ⟨xw_mem_Bs hF ω, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro s hs
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hs
    have hconj : xw hF ω * sigmaProj hF v * (xw hF ω)⁻¹ = sigmaProj hF v := by
      have hx : xw hF ω = LinearFlag.proj 6 F (phi hF ω 1 1 1) := rfl
      rw [hx]
      show LinearFlag.proj 6 F (phi hF ω 1 1 1) *
          LinearFlag.proj 6 F (sigmaFun v.toAdd) *
            (LinearFlag.proj 6 F (phi hF ω 1 1 1))⁻¹ =
        LinearFlag.proj 6 F (sigmaFun v.toAdd)
      rw [← map_inv, ← map_mul, ← map_mul, phi_conj_sigma]
      rw [show (sigmaScale ω 1 1 1 v.toAdd) = v.toAdd from by
        ext i
        fin_cases i <;> simp [sigmaScale, phiUnits]]
    have hcomm : xw hF ω * sigmaProj hF v = sigmaProj hF v * xw hF ω := by
      have h := congrArg (· * xw hF ω) hconj
      simpa [mul_assoc] using h
    exact hcomm.symm

theorem two_le_pRank_Bs_inf_J (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    2 ≤ CFSG.Open.pRank 3 (Bs hF ⊓ J (F := F)) := by
  set z : LinearFlag.projectiveSL 6 F := psi hF (1, ω, 1, 1) with hz
  set w : LinearFlag.projectiveSL 6 F := psi hF (1, 1, ω, 1) with hw
  have hz3 : z ^ 3 = 1 := by
    rw [hz, ← map_pow, tuple_pow_three, omega_pow_three hω]
    simp only [one_pow]
    exact map_one (psi hF)
  have hz1 : z ≠ 1 := by
    rw [hz]
    intro h
    have hp := (psi_eq_one_iff hF (1, ω, 1, 1)).1 h
    have h1 := congrArg (fun p : Fˣ × Fˣ × Fˣ × Fˣ => p.2.1) hp
    simp only [Prod.fst_one, Prod.snd_one] at h1
    exact omega_ne_one hω h1
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← map_pow, tuple_pow_three, omega_pow_three hω]
    simp only [one_pow]
    exact map_one (psi hF)
  have hzw : z * w = w * z := by
    rw [hz, hw, ← map_mul, ← map_mul, mul_comm]
  have hwz : w ∉ Subgroup.zpowers z := by
    rintro ⟨k, hk⟩
    have hk' : ((1, ω, 1, 1) : Fˣ × Fˣ × Fˣ × Fˣ) ^ k = (1, 1, ω, 1) := by
      apply psi_injective hF
      rw [map_zpow, ← hz, ← hw]
      exact hk
    have h1 := congrArg (fun p : Fˣ × Fˣ × Fˣ × Fˣ => p.2.2.1) hk'
    have h1' : (1 : Fˣ) = ω := by simpa using h1
    exact omega_ne_one hω h1'.symm
  obtain ⟨hE, hp⟩ := GL83.I243.isElemAbelian_zpowers_sup_zpowers_and_two_le_pRank
    Nat.prime_three hzord hw3 hzw hwz
  have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers w ≤ Bs hF ⊓ J (F := F) := by
    apply sup_le
    · refine Subgroup.zpowers_le.mpr ⟨?_, ?_⟩
      · rw [hz]; exact mem_Bs hF (1, ω, 1, 1)
      · rw [hz]; exact psi_one_mem_J hF ω 1 1
    · refine Subgroup.zpowers_le.mpr ⟨?_, ?_⟩
      · rw [hw]; exact mem_Bs hF (1, 1, ω, 1)
      · rw [hw]; exact psi_one_mem_J hF 1 ω 1
  exact hp.trans (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hle)

@[expose]
def I45 : Finset (Fin 6) := {4, 5}

@[expose]
noncomputable def scalarHom : (Fˣ × Fˣ × Fˣ × Fˣ) →* Fˣ where
  toFun p := p.2.1 * p.2.2.1 * p.2.2.2 ^ 2
  map_one' := by simp
  map_mul' p q := by
    obtain ⟨a, u, v, w⟩ := p
    obtain ⟨a', u', v', w'⟩ := q
    simp only [Prod.fst_mul, Prod.snd_mul, mul_pow, pow_two]
    ac_rfl

@[expose]
def x0 (ω : Fˣ) : Fˣ × Fˣ × Fˣ × Fˣ := (ω, 1, 1, 1)
@[expose]
def z1 (ω : Fˣ) : Fˣ × Fˣ × Fˣ × Fˣ := (1, ω, ω ^ 2, 1)
@[expose]
def z2 (ω : Fˣ) : Fˣ × Fˣ × Fˣ × Fˣ := (1, ω ^ 2, ω ^ 2, ω)

private theorem mem_scalarHom_ker {p : Fˣ × Fˣ × Fˣ × Fˣ} :
    p ∈ (scalarHom (F := F)).ker ↔ p.2.1 * p.2.2.1 * p.2.2.2 ^ 2 = 1 := Iff.rfl

private theorem x0_mem_scalarHom (ω : Fˣ) : x0 ω ∈ (scalarHom (F := F)).ker := by
  rw [MonoidHom.mem_ker]
  simp [scalarHom, x0]

private theorem z1_mem_scalarHom {ω : Fˣ} (hω : orderOf ω = 3) :
    z1 ω ∈ (scalarHom (F := F)).ker := by
  rw [mem_scalarHom_ker]
  change (ω : Fˣ) * ω ^ 2 * 1 ^ 2 = 1
  rw [one_pow, mul_one, mul_comm, ← pow_succ, show (2 + 1 : ℕ) = 3 by norm_num,
    omega_pow_three hω]

private theorem z2_mem_scalarHom {ω : Fˣ} (hω : orderOf ω = 3) :
    z2 ω ∈ (scalarHom (F := F)).ker := by
  rw [mem_scalarHom_ker]
  change (ω : Fˣ) ^ 2 * ω ^ 2 * ω ^ 2 = 1
  have h6 : ω ^ 2 * ω ^ 2 * ω ^ 2 = ω ^ 6 := by
    rw [← pow_add, ← pow_add]
  rw [h6, show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, omega_pow_three hω, one_pow]

@[expose]
noncomputable def E (hF : Nat.card F = 4) (ω : Fˣ) :
    Subgroup (LinearFlag.projectiveSL 6 F) :=
  (Subgroup.zpowers (x0 ω) ⊔ Subgroup.zpowers (z1 ω) ⊔ Subgroup.zpowers (z2 ω)).map (psi hF)

theorem E_le_Bs (hF : Nat.card F = 4) (ω : Fˣ) : E hF ω ≤ Bs hF :=
  Subgroup.map_le_range _ _

theorem isElemAbelian_E (hF : Nat.card F = 4) (ω : Fˣ) :
    CFSG.Open.IsElemAbelian 3 (E hF ω) :=
  CFSG.Open.IsElemAbelian.mono (isElemAbelian_Bs hF) (E_le_Bs hF ω)

theorem B2_le_scalarHom {ω : Fˣ} (hω : orderOf ω = 3) :
    Subgroup.zpowers (x0 ω) ⊔ Subgroup.zpowers (z1 ω) ⊔ Subgroup.zpowers (z2 ω) ≤
      (scalarHom (F := F)).ker := by
  refine sup_le (sup_le ?_ ?_) ?_
  · exact Subgroup.zpowers_le.mpr (x0_mem_scalarHom ω)
  · exact Subgroup.zpowers_le.mpr (z1_mem_scalarHom hω)
  · exact Subgroup.zpowers_le.mpr (z2_mem_scalarHom hω)

private theorem orderOf_x0 (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    orderOf (x0 ω) = 3 := by
  apply orderOf_eq_prime
  · rw [show x0 ω = (ω, 1, 1, 1) from rfl, tuple_pow_three, omega_pow_three hω]
    simp
  · intro h
    have h1 := congrArg (fun p : Fˣ × Fˣ × Fˣ × Fˣ => p.1) h
    have h1' : ω = 1 := by simpa [x0] using h1
    exact omega_ne_one hω h1'

theorem card_E (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    Nat.card (E hF ω) = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have htop : CFSG.Open.IsElemAbelian 3 (⊤ : Subgroup (Fˣ × Fˣ × Fˣ × Fˣ)) := by
    constructor
    · rw [isMulCommutative_iff]
      intro x y
      exact Subtype.ext (mul_comm x.1 y.1)
    · intro x _
      obtain ⟨a, u, v, w⟩ := x
      rw [show ((a, u, v, w) : Fˣ × Fˣ × Fˣ × Fˣ) ^ 3 = (a ^ 3, u ^ 3, v ^ 3, w ^ 3) from
        tuple_pow_three a u v w]
      ext <;> simp [units_pow_three hF]
  have hcard0 : Nat.card (Subgroup.zpowers (x0 ω)) = 3 := by
    rw [Nat.card_zpowers, orderOf_x0 hF hω]
  have hz1 : z1 ω ∉ Subgroup.zpowers (x0 ω) := by
    rintro ⟨k, hk⟩
    have h2 := congrArg (fun p : Fˣ × Fˣ × Fˣ × Fˣ => p.2.1) hk
    have h2' : (1 : Fˣ) = ω := by simpa [x0, z1] using h2
    exact omega_ne_one hω h2'.symm
  have hcard1 : Nat.card (Subgroup.zpowers (x0 ω) ⊔ Subgroup.zpowers (z1 ω) :
      Subgroup (Fˣ × Fˣ × Fˣ × Fˣ)) = 9 := by
    have h := GL83.CompFam.card_sup_zpowers (p := 3) htop
      (show Subgroup.zpowers (x0 ω) ≤ (⊤ : Subgroup (Fˣ × Fˣ × Fˣ × Fˣ)) from le_top)
      (z := z1 ω) (show z1 ω ∈ (⊤ : Subgroup (Fˣ × Fˣ × Fˣ × Fˣ)) from Subgroup.mem_top _) hz1
    rw [h, hcard0]
  have hz1' : Subgroup.zpowers (z1 ω) ≤ Subgroup.zpowers (x0 ω) ⊔ Subgroup.zpowers (z1 ω) :=
    le_sup_right
  have hz2 : z2 ω ∉ Subgroup.zpowers (x0 ω) ⊔ Subgroup.zpowers (z1 ω) := by
    intro hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hy' : y = (ω ^ i, 1, 1, 1) := by
      rw [← hi]; exact tuple_omega_zpow ω i
    have hy4 : y.2.2.2 = 1 := by rw [hy']
    have hz4 : z.2.2.2 = 1 := by
      rw [← hj]
      simp [z1]
    have h4 := congrArg (fun p : Fˣ × Fˣ × Fˣ × Fˣ => p.2.2.2) hyz
    change y.2.2.2 * z.2.2.2 = (z2 ω).2.2.2 at h4
    rw [hy4, hz4] at h4
    have h4' : (1 : Fˣ) = ω := by simpa [z2] using h4
    exact omega_ne_one hω h4'.symm
  have hcard2 : Nat.card (Subgroup.zpowers (x0 ω) ⊔ Subgroup.zpowers (z1 ω) ⊔
      Subgroup.zpowers (z2 ω) : Subgroup (Fˣ × Fˣ × Fˣ × Fˣ)) = 27 := by
    have h := GL83.CompFam.card_sup_zpowers (p := 3) htop
      (show Subgroup.zpowers (x0 ω) ⊔ Subgroup.zpowers (z1 ω) ≤
        (⊤ : Subgroup (Fˣ × Fˣ × Fˣ × Fˣ)) from le_top)
      (z := z2 ω) (show z2 ω ∈ (⊤ : Subgroup (Fˣ × Fˣ × Fˣ × Fˣ)) from Subgroup.mem_top _) hz2
    rw [h, hcard1]
  rw [E, Subgroup.card_map_of_injective (psi_injective hF), hcard2]

private theorem x0_mem_zpowers (ω : Fˣ) : x0 ω ∈ Subgroup.zpowers (x0 ω) :=
  Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩

private theorem z1_mem_zpowers (ω : Fˣ) : z1 ω ∈ Subgroup.zpowers (z1 ω) :=
  Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩

private theorem x0_mem_E (hF : Nat.card F = 4) (ω : Fˣ) : psi hF (x0 ω) ∈ E hF ω :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (x0_mem_zpowers ω)))

theorem z1_mem_E (hF : Nat.card F = 4) (ω : Fˣ) : psi hF (z1 ω) ∈ E hF ω :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right
    (z1_mem_zpowers ω)))

theorem xw_mem_E (hF : Nat.card F = 4) (ω : Fˣ) : xw hF ω ∈ E hF ω := by
  rw [xw]
  exact x0_mem_E hF ω

end A5Four

end CFSG.LocalAnalysis.GLTheoremA.Y10F
