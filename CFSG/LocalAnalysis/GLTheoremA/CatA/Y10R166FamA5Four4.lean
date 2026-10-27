module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamA5Four3
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2EUp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TablesHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Build
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace A5Four

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot
open Matrix

variable {F : Type} [Field F] [Finite F]

private theorem phi_one_mem_block (hF : Nat.card F = 4) (u v w : Fˣ) :
    phi hF 1 u v w ∈ blockSpecialLinear I01ᶜ := by
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

private theorem I45_subset (hF : Nat.card F = 4) : I45 ⊆ I01ᶜ := by
  intro x hx
  fin_cases x <;> simp_all [I45, I01]

private theorem blockSpecialLinear_commute_diag (hF : Nat.card F = 4) {d : Fin 6 → F}
    (hd : d 4 = d 5) (hprod : ∏ i, d i = 1) {A : SpecialLinearGroup (Fin 6) F}
    (hA : A ∈ blockSpecialLinear I45) : Commute A (diagSL d hprod) := by
  apply Subtype.ext
  change (A : Matrix (Fin 6) (Fin 6) F) * Matrix.diagonal d =
    Matrix.diagonal d * (A : Matrix (Fin 6) (Fin 6) F)
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i ∈ I45 <;> by_cases hj : j ∈ I45
  · have hmem : i = 4 ∨ i = 5 := by simpa [I45] using hi
    have hmem' : j = 4 ∨ j = 5 := by simpa [I45] using hj
    rcases hmem with rfl | rfl <;> rcases hmem' with rfl | rfl <;> simp [hd, mul_comm]
  · have hne : i ≠ j := fun h => hj (h ▸ hi)
    rw [mem_blockSpecialLinear.1 hA i j (Or.inr hj), Matrix.one_apply_ne hne]
    simp
  · have hne : i ≠ j := fun h => hi (h ▸ hj)
    rw [mem_blockSpecialLinear.1 hA i j (Or.inl hi), Matrix.one_apply_ne hne]
    simp
  · by_cases hij : i = j
    · subst hij
      rw [mem_blockSpecialLinear.1 hA i i (Or.inl hi)]
      simp
    · rw [mem_blockSpecialLinear.1 hA i j (Or.inl hi), Matrix.one_apply_ne hij]
      simp

private theorem scalarHom_val {p : Fˣ × Fˣ × Fˣ × Fˣ} (hp : p ∈ (scalarHom (F := F)).ker) :
    p.2.1 * p.2.2.1 * p.2.2.2 ^ 2 = 1 := hp

private theorem diag_phi_scalar (hF : Nat.card F = 4) {p : Fˣ × Fˣ × Fˣ × Fˣ}
    (hp : p ∈ (scalarHom (F := F)).ker) :
    (phiUnits p.1 p.2.1 p.2.2.1 p.2.2.2 (4 : Fin 6) : F) =
      (phiUnits p.1 p.2.1 p.2.2.1 p.2.2.2 (5 : Fin 6) : F) := by
  have hpv := scalarHom_val hp
  have hw : p.2.2.2 = (p.2.1 * p.2.2.1 * p.2.2.2)⁻¹ := by
    have h1 : p.2.1 * p.2.2.1 * p.2.2.2 = (p.2.2.2)⁻¹ := by
      calc p.2.1 * p.2.2.1 * p.2.2.2
          = (p.2.1 * p.2.2.1 * p.2.2.2 ^ 2) * (p.2.2.2)⁻¹ := by group
        _ = 1 * (p.2.2.2)⁻¹ := by rw [hpv]
        _ = (p.2.2.2)⁻¹ := one_mul _
    rw [h1, inv_inv]
  have hwF : (p.2.2.2 : F) = (((p.2.1 * p.2.2.1 * p.2.2.2)⁻¹ : Fˣ) : F) := by
    rw [← hw]
  simpa [phiUnits] using hwF

private theorem L_le_centralizer_E (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    blockSL I45 ≤ Subgroup.centralizer ((E hF ω) : Set (LinearFlag.projectiveSL 6 F)) := by
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  obtain ⟨A, hA, rfl⟩ := mem_blockSL.mp hl
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp he
  have hpK : p ∈ (scalarHom (F := F)).ker := B2_le_scalarHom hω hp
  have hprod : ∏ i, (phiUnits p.1 p.2.1 p.2.2.1 p.2.2.2 i : F) = 1 :=
    prod_phiUnits hF p.1 p.2.1 p.2.2.1 p.2.2.2
  have hd := diag_phi_scalar hF hpK
  have hcomm : Commute A (phi hF p.1 p.2.1 p.2.2.1 p.2.2.2) :=
    blockSpecialLinear_commute_diag hF hd hprod hA
  exact (hcomm.map (LinearFlag.proj 6 F)).symm

private theorem L_le_H (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    blockSL I45 ≤ J (F := F) ⊓
      Subgroup.centralizer ((E hF ω) : Set (LinearFlag.projectiveSL 6 F)) :=
  le_inf (blockSL_mono (I45_subset hF)) (L_le_centralizer_E hF hω)

private theorem blockDiag_of_commute_e2 (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3)
    {a : SpecialLinearGroup (Fin 6) F} (ha : a ∈ blockSpecialLinear I01ᶜ)
    (hcomm : LinearFlag.proj 6 F a * psi hF (1, ω, ω ^ 2, 1) =
      psi hF (1, ω, ω ^ 2, 1) * LinearFlag.proj 6 F a) :
    a ∈ blockDiagSL I45 := by
  set E2 : SpecialLinearGroup (Fin 6) F := phi hF 1 ω (ω ^ 2) 1 with hE2
  have hE2block : E2 ∈ blockSpecialLinear I01ᶜ := phi_one_mem_block hF ω (ω ^ 2) 1
  have hE2eq : psi hF (1, ω, ω ^ 2, 1) = LinearFlag.proj 6 F E2 := rfl
  have hcomm' : LinearFlag.proj 6 F a * LinearFlag.proj 6 F E2 =
      LinearFlag.proj 6 F E2 * LinearFlag.proj 6 F a := by
    rw [← hE2eq]
    exact hcomm
  have hmem : a * E2 * a⁻¹ * E2⁻¹ ∈ LinearFlag.scalars 6 F := by
    rw [← LinearFlag.proj_eq_one_iff]
    show LinearFlag.proj 6 F (a * E2 * a⁻¹ * E2⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hcomm']
    group
  rw [LinearFlag.mem_scalars] at hmem
  obtain ⟨c, -, hc⟩ := hmem
  have hblock : a * E2 * a⁻¹ * E2⁻¹ ∈ blockSpecialLinear I01ᶜ :=
    mul_mem (mul_mem (mul_mem ha hE2block) (inv_mem ha)) (inv_mem hE2block)
  have h00 := (mem_blockSpecialLinear.1 hblock) 0 0 (Or.inl (by simp [I01]))
  have hcF : (c : F) = 1 := by
    have hmat : (a * E2 * a⁻¹ * E2⁻¹ : SpecialLinearGroup (Fin 6) F) =
        Matrix.scalar (Fin 6) (c : F) := hc
    have h' : ((a * E2 * a⁻¹ * E2⁻¹ : SpecialLinearGroup (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) 0 0 = (c : F) := by
      rw [hmat]
      simp [Matrix.scalar_apply]
    rw [← h', h00]
    rfl
  have hone : a * E2 * a⁻¹ * E2⁻¹ = 1 := by
    apply Subtype.ext
    rw [hc, hcF]
    simp [Matrix.scalar]
  have h2 : a * E2 = E2 * a := by
    have h := congrArg (· * (E2 * a)) hone
    simpa [mul_assoc] using h
  have hmat : (a : Matrix (Fin 6) (Fin 6) F) *
      Matrix.diagonal (fun k => (phiUnits 1 ω (ω ^ 2) 1 k : F)) =
        Matrix.diagonal (fun k => (phiUnits 1 ω (ω ^ 2) 1 k : F)) *
          (a : Matrix (Fin 6) (Fin 6) F) := by
    have h := congrArg (fun t : SpecialLinearGroup (Fin 6) F =>
      (t : Matrix (Fin 6) (Fin 6) F)) h2
    have h' : (a : Matrix (Fin 6) (Fin 6) F) * (E2 : Matrix (Fin 6) (Fin 6) F) =
        (E2 : Matrix (Fin 6) (Fin 6) F) * (a : Matrix (Fin 6) (Fin 6) F) := by
      simpa using h
    rw [hE2] at h'
    simpa [coe_phi] using h'
  rw [mem_blockDiagSL]
  intro i j hij
  have key : ∀ i j : Fin 6, (phiUnits 1 ω (ω ^ 2) 1 i : F) ≠
      (phiUnits 1 ω (ω ^ 2) 1 j : F) → (a : Matrix (Fin 6) (Fin 6) F) i j = 0 :=
    fun i j hne => apply_eq_zero_of_mul_diagonal_eq hmat hne
  by_cases hi45 : i ∈ I45
  · have hj45 : j ∉ I45 := hij.1 hi45
    by_cases hj01 : j ∈ I01
    · have hj' : j ∉ I01ᶜ := by simpa using hj01
      have hzero := (mem_blockSpecialLinear.1 ha) i j (Or.inr hj')
      have hne : i ≠ j := by
        intro h
        exact hj45 (h ▸ hi45)
      rw [hzero, Matrix.one_apply_ne hne]
    · refine key i j ?_
      have hi' : i = 4 ∨ i = 5 := by simpa [I45] using hi45
      have hj' : j = 2 ∨ j = 3 := by
        fin_cases j <;> simp_all [I45, I01]
      have hd4 : (phiUnits 1 ω (ω ^ 2) 1 4 : F) = 1 := by rw [phiUnits_four]; exact Units.val_one
      have hd5 : (phiUnits 1 ω (ω ^ 2) 1 5 : F) = 1 := by
        have h : (ω * ω ^ 2 * 1 : Fˣ) = 1 := by
          rw [mul_one, mul_comm, ← pow_succ, show (2 + 1 : ℕ) = 3 by norm_num,
            omega_pow_three hω]
        rw [phiUnits_five, h]
        simp
      have h2 : (phiUnits 1 ω (ω ^ 2) 1 2 : F) = (ω : F) := by rw [phiUnits_two]
      have h3 : (phiUnits 1 ω (ω ^ 2) 1 3 : F) = ((ω ^ 2 : Fˣ) : F) := by
        rw [phiUnits_three]
      rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
      · rw [hd4, h2]; intro h; exact omega_ne_one hω (Units.ext h).symm
      · rw [hd4, h3]; intro h; exact omega_sq_ne_one hω (Units.ext h).symm
      · rw [hd5, h2]; intro h; exact omega_ne_one hω (Units.ext h).symm
      · rw [hd5, h3]; intro h; exact omega_sq_ne_one hω (Units.ext h).symm
  · have hj45 : j ∈ I45 := by
      by_contra h
      exact hi45 (hij.2 h)
    by_cases hi01 : i ∈ I01
    · have hi' : i ∉ I01ᶜ := by simpa using hi01
      have hzero := (mem_blockSpecialLinear.1 ha) i j (Or.inl hi')
      have hne : i ≠ j := by
        intro h
        exact hi45 (h ▸ hj45)
      rw [hzero, Matrix.one_apply_ne hne]
    · refine key i j ?_
      have hj' : j = 4 ∨ j = 5 := by simpa [I45] using hj45
      have hi' : i = 2 ∨ i = 3 := by
        fin_cases i <;> simp_all [I45, I01]
      have hd4 : (phiUnits 1 ω (ω ^ 2) 1 4 : F) = 1 := by rw [phiUnits_four]; exact Units.val_one
      have hd5 : (phiUnits 1 ω (ω ^ 2) 1 5 : F) = 1 := by
        have h : (ω * ω ^ 2 * 1 : Fˣ) = 1 := by
          rw [mul_one, mul_comm, ← pow_succ, show (2 + 1 : ℕ) = 3 by norm_num,
            omega_pow_three hω]
        rw [phiUnits_five, h]
        simp
      have h2 : (phiUnits 1 ω (ω ^ 2) 1 2 : F) = (ω : F) := by rw [phiUnits_two]
      have h3 : (phiUnits 1 ω (ω ^ 2) 1 3 : F) = ((ω ^ 2 : Fˣ) : F) := by
        rw [phiUnits_three]
      rcases hj' with rfl | rfl <;> rcases hi' with rfl | rfl
      · rw [h2, hd4]; intro h; exact omega_ne_one hω (Units.ext h)
      · rw [h3, hd4]; intro h; exact omega_sq_ne_one hω (Units.ext h)
      · rw [h2, hd5]; intro h; exact omega_ne_one hω (Units.ext h)
      · rw [h3, hd5]; intro h; exact omega_sq_ne_one hω (Units.ext h)

private theorem L_normal_in_H (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    ((blockSL I45).subgroupOf (J (F := F) ⊓
      Subgroup.centralizer ((E hF ω) : Set (LinearFlag.projectiveSL 6 F)))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (L_le_H hF hω)]
  intro l h hl hh
  obtain ⟨A, hA, rfl⟩ := mem_blockSL.mp hl
  obtain ⟨a, ha, rfl⟩ := mem_blockSL.mp (Subgroup.mem_inf.1 hh).1
  have hcent := (Subgroup.mem_inf.1 hh).2
  have he2 : psi hF (1, ω, ω ^ 2, 1) ∈ E hF ω := z1_mem_E hF ω
  have hcomm : LinearFlag.proj 6 F a * psi hF (1, ω, ω ^ 2, 1) =
      psi hF (1, ω, ω ^ 2, 1) * LinearFlag.proj 6 F a :=
    (Subgroup.mem_centralizer_iff.1 hcent _ he2).symm
  have haD : a ∈ blockDiagSL I45 := blockDiag_of_commute_e2 hF hω ha hcomm
  have hP : blockComplProj I45 * (a : Matrix (Fin 6) (Fin 6) F) =
      (a : Matrix (Fin 6) (Fin 6) F) * blockComplProj I45 := by
    have := (mem_blockDiagSL_iff_mul.1 haD).symm
    simpa using this
  have hmap := map_conj_blockSpecialLinear_of_mul_eq (I := I45) (J := I45) a hP
  have hconj : a * A * a⁻¹ ∈ blockSpecialLinear I45 := by
    have hmem : (MulAut.conj a) A ∈
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj a)) (blockSpecialLinear I45) :=
      Subgroup.mem_map_of_mem _ hA
    rwa [hmap] at hmem
  have hproj : LinearFlag.proj 6 F a * LinearFlag.proj 6 F A *
      (LinearFlag.proj 6 F a)⁻¹ ∈ blockSL I45 := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ hconj
  exact hproj

private theorem i45 : (4 : Fin 6) ≠ 5 := by decide

private theorem phi_one_one_one_mem_I45 (hF : Nat.card F = 4) (ω : Fˣ) :
    phi hF 1 1 1 ω ∈ blockSpecialLinear I45 := by
  rw [mem_blockSpecialLinear]
  intro i j hij
  have hmat : (phi hF 1 1 1 ω : Matrix (Fin 6) (Fin 6) F) =
      Matrix.diagonal fun k => (phiUnits 1 1 1 ω k : F) := rfl
  rw [hmat]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    fin_cases i <;> simp_all [I45, phiUnits]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

private theorem transvection_i45_mem (hF : Nat.card F = 4) :
    SpecialLinearGroup.transvection i45 (1 : F) ∈ blockSpecialLinear I45 := by
  rw [mem_blockSpecialLinear]
  intro i j hij
  rw [SpecialLinearGroup.transvection_coe]
  fin_cases i <;> fin_cases j <;>
    simp_all [I45, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

private theorem g_mem_L (hF : Nat.card F = 4) (ω : Fˣ) :
    psi hF (1, 1, 1, ω) ∈ blockSL (K := F) I45 := by
  show LinearFlag.proj 6 F (phi hF 1 1 1 ω) ∈ blockSL (K := F) I45
  exact Subgroup.mem_map_of_mem _ (phi_one_one_one_mem_I45 hF ω)

private theorem g_not_mem_center (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3)
    (hg : psi hF (1, 1, 1, ω) ∈ blockSL (K := F) I45) :
    (⟨psi hF (1, 1, 1, ω), hg⟩ : ↥(blockSL (K := F) I45)) ∉
      Subgroup.center ↥(blockSL (K := F) I45) := by
  intro hz
  have htL : LinearFlag.proj 6 F (SpecialLinearGroup.transvection i45 1) ∈ blockSL (K := F) I45 :=
    Subgroup.mem_map_of_mem _ (transvection_i45_mem hF)
  have hcommP : LinearFlag.proj 6 F (phi hF 1 1 1 ω) *
      LinearFlag.proj 6 F (SpecialLinearGroup.transvection i45 1) =
        LinearFlag.proj 6 F (SpecialLinearGroup.transvection i45 1) *
          LinearFlag.proj 6 F (phi hF 1 1 1 ω) := by
    have h := congrArg Subtype.val
      ((Subgroup.mem_center_iff.mp hz) ⟨LinearFlag.proj 6 F
        (SpecialLinearGroup.transvection i45 1), htL⟩)
    simpa [psi] using h.symm
  have hmem : phi hF 1 1 1 ω * SpecialLinearGroup.transvection i45 1 *
      (phi hF 1 1 1 ω)⁻¹ * (SpecialLinearGroup.transvection i45 1)⁻¹ ∈
        LinearFlag.scalars 6 F := by
    rw [← LinearFlag.proj_eq_one_iff]
    show LinearFlag.proj 6 F (phi hF 1 1 1 ω * SpecialLinearGroup.transvection i45 1 *
      (phi hF 1 1 1 ω)⁻¹ * (SpecialLinearGroup.transvection i45 1)⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hcommP]
    group
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.mp hmem
  have hconj : phi hF 1 1 1 ω * SpecialLinearGroup.transvection i45 1 *
      (phi hF 1 1 1 ω)⁻¹ = SpecialLinearGroup.transvection i45 ((ω : F) ^ 2) := by
    have h := diagSL_conj_transvection (F := F) hF (prod_phiUnits hF 1 1 1 ω) i45 (1 : F)
    rw [show phi hF 1 1 1 ω = diagSL (fun k => (phiUnits 1 1 1 ω k : F))
        (prod_phiUnits hF 1 1 1 ω) from rfl, h]
    congr 1
    have hcoe : (phiUnits 1 1 1 ω 4 : F) * 1 * ((phiUnits 1 1 1 ω 5 : F))⁻¹ =
        ((ω ^ 2 : Fˣ) : F) := by
      rw [phiUnits_four, phiUnits_five]
      rw [show (1 * 1 * ω : Fˣ) = ω by simp, Units.val_inv_eq_inv_val, inv_inv]
      rw [mul_one, ← Units.val_mul]
      congr 1
      rw [pow_two]
    exact hcoe
  have hprod : phi hF 1 1 1 ω * SpecialLinearGroup.transvection i45 1 *
      (phi hF 1 1 1 ω)⁻¹ * (SpecialLinearGroup.transvection i45 1)⁻¹ =
        SpecialLinearGroup.transvection i45 (((ω : F) ^ 2 - 1)) := by
    rw [hconj, Matrix.SpecialLinearGroup.transvection_inv i45 (1 : F), ← SpecialLinearGroup.transvection_add]
    congr 1
    ring
  have hentry : (((SpecialLinearGroup.transvection i45 (ω ^ 2 - 1) :
      SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) 4 5) =
        ((ω : F) ^ 2 - 1) := by
    rw [SpecialLinearGroup.transvection_coe]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, i45]
  have hcmat : (((phi hF 1 1 1 ω * SpecialLinearGroup.transvection i45 1 *
      (phi hF 1 1 1 ω)⁻¹ * (SpecialLinearGroup.transvection i45 1)⁻¹ :
        SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) 4 5) = 0 := by
    rw [hc]
    simp [Matrix.scalar_apply, i45]
  rw [hprod, hentry] at hcmat
  have hsq : ((ω : F) ^ 2) = 1 := sub_eq_zero.mp hcmat
  have h2 : (ω ^ 2 : Fˣ) = 1 := Units.ext (by simpa using hsq)
  exact omega_sq_ne_one hω h2

private theorem three_dvd_card_center_quotient_L (hF : Nat.card F = 4) {ω : Fˣ}
    (hω : orderOf ω = 3) :
    3 ∣ Nat.card (↥(blockSL (K := F) I45) ⧸
      Subgroup.center ↥(blockSL (K := F) I45)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hgmem : psi hF (1, 1, 1, ω) ∈ blockSL (K := F) I45 := g_mem_L hF ω
  have hg3 : (⟨psi hF (1, 1, 1, ω), hgmem⟩ : ↥(blockSL (K := F) I45)) ^ 3 = 1 := by
    apply Subtype.ext
    change (psi hF (1, 1, 1, ω)) ^ 3 = (1 : LinearFlag.projectiveSL 6 F)
    rw [← map_pow]
    rw [show ((1, 1, 1, ω) : Fˣ × Fˣ × Fˣ × Fˣ) ^ 3 =
      (1 ^ 3, 1 ^ 3, 1 ^ 3, ω ^ 3) from tuple_pow_three 1 1 1 ω]
    rw [omega_pow_three hω]
    simp only [one_pow]
    exact map_one (psi hF)
  have hg1 : (⟨psi hF (1, 1, 1, ω), hgmem⟩ : ↥(blockSL (K := F) I45)) ≠ 1 := by
    intro h
    have h' : psi hF (1, 1, 1, ω) = 1 := congrArg Subtype.val h
    have hp := (psi_eq_one_iff hF (1, 1, 1, ω)).1 h'
    have h4 := congrArg (fun p : Fˣ × Fˣ × Fˣ × Fˣ => p.2.2.2) hp
    have h4' : ω = 1 := by simpa using h4
    exact omega_ne_one hω h4'
  have hgcenter : (⟨psi hF (1, 1, 1, ω), hgmem⟩ : ↥(blockSL (K := F) I45)) ∉
      Subgroup.center ↥(blockSL (K := F) I45) :=
    g_not_mem_center hF hω hgmem
  have hq3 : (QuotientGroup.mk (⟨psi hF (1, 1, 1, ω), hgmem⟩ :
      ↥(blockSL (K := F) I45)) : (↥(blockSL (K := F) I45) ⧸
        Subgroup.center ↥(blockSL (K := F) I45))) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hg3]
    exact QuotientGroup.mk_one _
  have hq1 : (QuotientGroup.mk (⟨psi hF (1, 1, 1, ω), hgmem⟩ :
      ↥(blockSL (K := F) I45)) : (↥(blockSL (K := F) I45) ⧸
        Subgroup.center ↥(blockSL (K := F) I45))) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    exact hgcenter h
  have hord : orderOf (QuotientGroup.mk (⟨psi hF (1, 1, 1, ω), hgmem⟩ :
      ↥(blockSL (K := F) I45)) : (↥(blockSL (K := F) I45) ⧸
        Subgroup.center ↥(blockSL (K := F) I45))) = 3 :=
    orderOf_eq_prime hq3 hq1
  have hdvd := orderOf_dvd_natCard (QuotientGroup.mk (⟨psi hF (1, 1, 1, ω), hgmem⟩ :
    ↥(blockSL (K := F) I45)) : (↥(blockSL (K := F) I45) ⧸
      Subgroup.center ↥(blockSL (K := F) I45)))
  rwa [hord] at hdvd

private theorem L_quasisimple (hF : Nat.card F = 4) :
    CFSG.Open.IsQuasisimple ↥(blockSL (K := F) I45) := by
  have hcard : I45.card = 2 := by simp [I45]
  have hq := isQuasisimple_blockSL (K := F) (I := I45) (n := 6) (by rw [hcard]; norm_num)
    (by rw [hcard]) (Or.inr (by rw [hF]))
  exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩

private theorem e3_layer (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    CFSG.Open.GLAPLayer 3 (J (F := F) ⊓
      Subgroup.centralizer ((E hF ω) : Set (LinearFlag.projectiveSL 6 F))) ≠ ⊥ :=
  glaPLayer_ne_bot_of_normal_quasisimple (q := 3) Nat.prime_three
    (L_le_H hF hω) (L_normal_in_H hF hω) (L_quasisimple hF)
    (three_dvd_card_center_quotient_L hF hω)

private theorem center_P_eq_bot :
    Subgroup.center (LinearFlag.projectiveSL 6 F) = ⊥ :=
  CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)

private theorem quasisimple_P : CFSG.IsQuasisimple (LinearFlag.projectiveSL 6 F) :=
  isQuasisimple_projectiveSL (by norm_num)

private theorem P_statedClassicalModel (hF : Nat.card F = 4) :
    StatedClassicalModel (LinearFlag.projectiveSL 6 F ⧸
      Subgroup.center (LinearFlag.projectiveSL 6 F)) .PSL 6 2 2 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩,
    F, inferInstance, inferInstance, by rw [hF]; norm_num, ?_⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq center_P_eq_bot).trans
    (QuotientGroup.quotientBot.trans (CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj 6 F))⟩

private theorem hasLabel_P (hF : Nat.card F = 4) :
    HasLabel (LinearFlag.projectiveSL 6 F) (· = ⟨.A, 5, 2⟩) :=
  hasLabel_of_statedClassicalModel_PSL (J := LinearFlag.projectiveSL 6 F) (r := 5) (n := 2)
    quasisimple_P (P_statedClassicalModel hF)
private theorem I01c_card : I01ᶜ.card = 4 := by
  rw [Finset.card_compl]
  simp [I01]

private theorem quasisimple_J : CFSG.IsQuasisimple ↥(blockSL (K := F) I01ᶜ) :=
  isQuasisimple_blockSL (K := F) (I := I01ᶜ) (n := 6) (by rw [I01c_card]; norm_num)
    (by rw [I01c_card]; norm_num) (Or.inl (by rw [I01c_card]; norm_num))

private theorem J_statedClassicalModel (hF : Nat.card F = 4) :
    StatedClassicalModel (↥(blockSL (K := F) I01ᶜ) ⧸
      Subgroup.center ↥(blockSL (K := F) I01ᶜ)) .PSL 4 2 2 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩,
    F, inferInstance, inferInstance, by rw [hF]; norm_num, ?_⟩
  obtain ⟨e⟩ := blockSL_mulEquiv (K := F) (I := I01ᶜ) (n := 6)
    (by rw [I01c_card]; norm_num)
  let e4 : SpecialLinearGroup (Fin I01ᶜ.card) F ≃* SpecialLinearGroup (Fin 4) F :=
    reindexSpecialLinear (K := F) (finCongr I01c_card)
  refine ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
    ((QuotientGroup.congr _ _ e4 (Subgroup.map_center_eq e4)).trans ?_)⟩
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 F).trans
    (CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj 4 F)

private theorem hasLabel_J (hF : Nat.card F = 4) :
    HasLabel ↥(blockSL (K := F) I01ᶜ) (· = ⟨.A, 3, 2⟩) :=
  hasLabel_of_statedClassicalModel_PSL (J := ↥(blockSL (K := F) I01ᶜ)) (r := 3) (n := 2)
    (quasisimple_J (F := F)) (J_statedClassicalModel hF)

private theorem Bs_le_J_sup_x (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3) :
    Bs hF ≤ J (F := F) ⊔ Subgroup.zpowers (xw hF ω) := by
  rintro b ⟨p, rfl⟩
  obtain ⟨a, u, v, w⟩ := p
  obtain ⟨k, hk⟩ := exists_zpow_eq_omega hF hω a
  have hb : psi hF (a, u, v, w) = (xw hF ω) ^ k * psi hF (1, u, v, w) := by
    rw [xw, ← map_zpow, ← map_mul]
    congr 1
    rw [tuple_omega_zpow, hk]
    ext <;> simp
  rw [hb]
  exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩))
    (Subgroup.mem_sup_left (psi_one_mem_J hF u v w))

private theorem commutator_mem_J (hF : Nat.card F = 4) {ω : Fˣ} (hω : orderOf ω = 3)
    {g g' : LinearFlag.projectiveSL 6 F}
    (hg : g ∈ Subgroup.centralizer ({xw hF ω} : Set (LinearFlag.projectiveSL 6 F)))
    (hg' : g' ∈ Subgroup.centralizer ({xw hF ω} : Set (LinearFlag.projectiveSL 6 F))) :
    g * g' * g⁻¹ * g'⁻¹ ∈ J (F := F) := by
  have hhX : LinearFlag.proj 6 F (hsplit hF ω) ∈ Subgroup.zpowers (xw hF ω) := by
    rw [xw_eq_proj_hsplit]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  have hgX : g ∈ Subgroup.centralizer
      (↑(Subgroup.zpowers (xw hF ω)) : Set (LinearFlag.projectiveSL 6 F)) := by
    rw [centralizer_zpowers_eq_centralizer_singleton]
    exact hg
  have hg'X : g' ∈ Subgroup.centralizer
      (↑(Subgroup.zpowers (xw hF ω)) : Set (LinearFlag.projectiveSL 6 F)) := by
    rw [centralizer_zpowers_eq_centralizer_singleton]
    exact hg'
  have := commutator_mem_blockSL_of_mem_centralizer_split (n := 6) (a := 0) (b := 1)
    (K := F) (h := hsplit hF ω) (X := Subgroup.zpowers (xw hF ω))
    (by norm_num) (hsplit_isRootSplit hF hω) hhX hgX hg'X
  simpa [J, I01] using this

end A5Four

open A5Four
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot
open Matrix

variable {F : Type} [Field F] [Finite F]

section Certificates

private theorem evenRank_P (hF : Nat.card F = 4) :
    evenRank (LinearFlag.projectiveSL 6 F) = 4 := by
  have hL : Rk2IsLabel (LinearFlag.projectiveSL 6 F) ⟨.A, 5, 2⟩ := hasLabel_P hF
  have hle : evenRank (LinearFlag.projectiveSL 6 F) ≤ 4 :=
    (rk2_eUpAt_of_tables rk2KRank rk2Upper_holds hL).a5 rfl center_P_eq_bot
  have hge : 4 ≤ evenRank (LinearFlag.projectiveSL 6 F) := by
    have := (rk2Lower_holds (LinearFlag.projectiveSL 6 F) ⟨.A, 5, 2⟩ hL).a_ge rfl
      (by norm_num : 2 ≤ 2)
    simpa using this
  omega
private theorem JShape_witness (hF : Nat.card F = 4)
    (he : 4 ≤ evenRank (LinearFlag.projectiveSL 6 F)) {lab : GLALabel}
    (hlab : HasLabel (LinearFlag.projectiveSL 6 F) (· = lab)) :
    JShape lab (3 ∣ Nat.card (Subgroup.center (LinearFlag.projectiveSL 6 F))) ⟨.A, 3, 2⟩ := by
  have hP : HasLabel (LinearFlag.projectiveSL 6 F) (· = ⟨.A, 5, 2⟩) := hasLabel_P hF
  have heq : lab = ⟨.A, 5, 2⟩ := by
    rcases label_eq_or_BC he hlab hP with h | ⟨-, hb2, -, -⟩
    · exact h
    · rcases hb2 with h | h <;> cases h
  subst heq
  refine ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, rfl, rfl, rfl⟩)))))))))⟩

theorem exists_concl166S_projectiveSL_six (hF : Nat.card F = 4) :
    ∃ q B' x' J, Concl166S (LinearFlag.projectiveSL 6 F) 5 q B' x' J := by
  obtain ⟨ω, hω⟩ := exists_units_order_three hF
  have heP : evenRank (LinearFlag.projectiveSL 6 F) = 4 := evenRank_P hF
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
  obtain ⟨⟨hZJ, hTMJ⟩, hoddJ, hm2J, hdvdJ⟩ :=
    linearFourFour_mult (J := ↥(blockSL (K := F) I01ᶜ)) (hasLabel_J hF) hGA
  refine ⟨3, Bs hF, xw hF ω, J (F := F), ?_⟩
  refine concl166S_of_witness (K := LinearFlag.projectiveSL 6 F) (p := 5) (q := 3)
    (B := Bs hF) (x := xw hF ω) (J := J (F := F)) Nat.prime_three (by norm_num)
    (isElemAbelian_Bs hF) (xw_mem_Bs hF ω) (xw_ne_one hF hω) ?_ ?_
    (J_le_centralizer_xw hF hω) (quasisimple_J (F := F))
    (fun g hg g' hg' => commutator_mem_J hF hω hg hg')
    ⟨.A, 3, 2⟩ (hasLabel_J hF)
    (fun lab hlab => JShape_witness hF (by rw [heP]) hlab) ?_ hoddJ hdvdJ
    (Or.inl ⟨hZJ, hTMJ⟩) (E hF ω) (E_le_Bs hF ω) (isElemAbelian_E hF ω)
    (card_E hF hω) (xw_mem_E hF ω) (e3_layer hF hω) ?_ ?_
    (S hF) (S_le_J hF) (isPGroup_S hF) (Bs_le_normalizer_S hF) ?_ ?_
  · rw [card_Bs hF, heP]
    norm_num
  · rw [heP]
  · rw [heP]
    exact le_trans (by norm_num : 6 ≤ 8) hm2J
  · exact Bs_le_J_sup_x hF hω
  · rw [heP]
    have h := two_le_pRank_Bs_inf_J hF hω
    omega
  · calc (Bs hF ⊓ J (F := F)) ⊓ Subgroup.centralizer ((S hF) : Set (LinearFlag.projectiveSL 6 F))
        ≤ Bs hF ⊓ Subgroup.centralizer ((S hF) : Set (LinearFlag.projectiveSL 6 F)) :=
          inf_le_inf_right _ inf_le_left
      _ = Subgroup.zpowers (xw hF ω) := Bs_inf_centralizer_S hF hω
  · intro h3 _
    exact absurd h3 (by rw [center_P_eq_bot]; norm_num)

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.Y10F
