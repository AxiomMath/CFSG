module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292LFrame

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup Matrix
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open P614K292
open scoped Pointwise

namespace P614K292L

variable {K : Type} [Field K] {p f : ℕ}

theorem mulVec_ne_zero (a : GL (Fin 3) K) {u : Fin 3 → K} (hu : u ≠ 0) :
    (a : Matrix (Fin 3) (Fin 3) K) *ᵥ u ≠ 0 := by
  intro h
  apply hu
  have h' := congrArg (((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ·) h
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h'

theorem scalar_mulVec (c : Kˣ) (u : Fin 3 → K) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      u = (c : K) • u := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.smul_mulVec, Matrix.one_mulVec]

theorem exists_commute_mulVec_eq {y : GL (Fin 3) K} {ℓ : K} (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) {v w : Fin 3 → K} (hv : v ≠ 0)
    (hw : w ≠ 0) :
    ∃ g : GL (Fin 3) K, g * y = y * g ∧ (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = w := by
  have hP := isUnit_colMat_yFrame hℓ hy hv
  have hQ := isUnit_colMat_yFrame hℓ hy hw
  have hPC := mul_colMat_cyclic hy v
  have hQC := mul_colMat_cyclic hy w
  rw [← yFrame_eq] at hPC hQC
  have hinv : ∀ M : Matrix (Fin 3) (Fin 3) K, ((hP.unit⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) * (colMat (yFrame y v) * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hP.val_inv_mul, Matrix.one_mul]
  refine ⟨hQ.unit * hP.unit⁻¹, Units.ext ?_, ?_⟩
  · apply hP.mul_left_inj.mp
    simp only [Units.val_mul, hQ.unit_spec, Matrix.mul_assoc, hPC, hinv, hP.val_inv_mul,
      Matrix.mul_one, hQC]
  · have hv0 : colMat (yFrame y v) *ᵥ Pi.single 0 1 = v := by
      rw [colMat_mulVec_single, one_smul]
      simp [yFrame]
    have hw0 : colMat (yFrame y w) *ᵥ Pi.single 0 1 = w := by
      rw [colMat_mulVec_single, one_smul]
      simp [yFrame]
    calc ((hQ.unit * hP.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
        ((hQ.unit * hP.unit⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          (colMat (yFrame y v) *ᵥ Pi.single 0 1) := by rw [hv0]
      _ = w := by
        rw [Units.val_mul, hQ.unit_spec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
          hP.val_inv_mul, Matrix.mul_one, hw0]

theorem exists_mem_conj_smul_threeFrame_eq (hK : PiField true p f K)
    (hq : ModThree true (p ^ f)) {y : GL (Fin 3) K} (hT : IsTypeThree true (p ^ f) K y)
    {v w : Fin 3 → K} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ a ∈ slPi true 3 (p ^ f) K ⊓ centralizer {y},
      MulAut.conj a • threeFrame y v = threeFrame y w := by
  obtain ⟨ℓ, hy, hℓ⟩ := hT.not_cube hK hq
  obtain ⟨g, hgy, hgv⟩ := exists_commute_mulVec_eq hℓ hy hv hw
  have key : ∀ g' : GL (Fin 3) K, g' * y = y * g' →
      threeFrame y ((g' : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = threeFrame y w →
      IsInnerMat true (p ^ f) K g' → ∃ a ∈ slPi true 3 (p ^ f) K ⊓ centralizer {y},
        MulAut.conj a • threeFrame y v = threeFrame y w := by
    rintro g' hg'y hg'w ⟨l, hl, z, ⟨c, rfl⟩, rfl⟩
    have hzy := commute_of_mem_statedScalars (⟨c, rfl⟩ :
      Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ StatedScalars (Fin 3) K) y
    have hly : l * y = y * l := by
      have h1 : l * y * Matrix.GeneralLinearGroup.scalar (Fin 3) c =
          y * l * Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
        rw [mul_assoc l y, hzy, ← mul_assoc, hg'y, ← mul_assoc]
      exact mul_right_cancel h1
    refine ⟨l, Subgroup.mem_inf.mpr ⟨hl, Subgroup.mem_centralizer_singleton_iff.mpr hly⟩, ?_⟩
    rw [conj_smul_threeFrame hly, ← hg'w, Units.val_mul, ← Matrix.mulVec_mulVec, scalar_mulVec,
      Matrix.mulVec_smul, threeFrame_smul _ _ c.ne_zero]
  have hyw : ∀ u : Fin 3 → K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hgc : Commute g y := hgy
  rcases inner_or_of_det hK hq (mem_glPi_true _ y) (mem_glPi_true _ g)
      (hT.not_isInnerMat hK hq) with h | h | h
  · exact key g hgy (by rw [hgv]) h
  · refine key (g * y⁻¹) (by rw [inv_mul_cancel_right, ← mul_assoc, ← hgy,
      mul_inv_cancel_right]) ?_ h
    rw [hgc.inv_right.eq, Units.val_mul, ← Matrix.mulVec_mulVec, hgv]
    conv_rhs => rw [← hyw w]
    exact (threeFrame_mulVec_self ℓ.ne_zero hy _).symm
  · refine key (g * y) (by rw [hgy, mul_assoc, hgy]) ?_ h
    rw [hgy, Units.val_mul, ← Matrix.mulVec_mulVec, hgv]
    exact threeFrame_mulVec_self ℓ.ne_zero hy w

theorem odd_three_mul (t : ℕ) : Odd (3 * (3 * t ^ 2 + 3 * t + 1)) := by
  have he : Even (3 * t ^ 2 + 3 * t) := by
    rw [show 3 * t ^ 2 + 3 * t = 3 * (t * (t + 1)) by ring]
    exact (Nat.even_mul_succ_self t).mul_left 3
  exact Nat.odd_mul.mpr ⟨by decide, he.add_one⟩

end P614K292L

open P614K292L

theorem kD292ThreeFrameLin3_holds : KD292ThreeFrameLin3 := by
  intro p f K _ y hK hq _ hT
  refine ⟨fun E hE => eq_threeFrame_of_mem_frameCands hK hq hT hE, ?_⟩
  letI : MulAction ↥(slPi true 3 (p ^ f) K ⊓ centralizer {y}) (Subgroup (GL (Fin 3) K)) :=
    MulAction.compHom _ (MulAut.conj.comp (slPi true 3 (p ^ f) K ⊓ centralizer {y}).subtype)
  have hv₀ : (Pi.single 0 1 : Fin 3 → K) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have horb : frameCands true (p ^ f) y = MulAction.orbit
      ↥(slPi true 3 (p ^ f) K ⊓ centralizer {y}) (threeFrame y (Pi.single 0 1)) := by
    ext E
    constructor
    · intro hE
      obtain ⟨w, hw, rfl⟩ := eq_threeFrame_of_mem_frameCands hK hq hT hE
      obtain ⟨a, ha, hav⟩ := exists_mem_conj_smul_threeFrame_eq hK hq hT hv₀ hw
      exact ⟨⟨a, ha⟩, hav⟩
    · rintro ⟨⟨a, ha⟩, rfl⟩
      have hay : a * y = y * a :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ha).2
      change MulAut.conj a • threeFrame y (Pi.single 0 1) ∈ frameCands true (p ^ f) y
      rw [conj_smul_threeFrame hay]
      exact threeFrame_mem_frameCands hK hq hT (mulVec_ne_zero a hv₀)
  have := hK.finite
  have : Finite (GL (Fin 3) K) := Finite.of_injective Units.val Units.val_injective
  rw [Nat.card_coe_set_eq, horb, ← MulAction.index_stabilizer]
  refine Odd.of_dvd_nat ?_ (Subgroup.index_dvd_card _)
  rw [hT.card, qSubPi_cube_eq hq,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (qSubPi_ne_zero hK hq))]
  exact odd_three_mul _

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
