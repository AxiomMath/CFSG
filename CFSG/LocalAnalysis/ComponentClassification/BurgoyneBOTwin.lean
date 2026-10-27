module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOSliceR
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceProp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSlices
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBLift

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL compInd signMat
  signMat_mul_self commute_signMat_iff mul_conj_mul_inv)
open CFSG.ComponentClassification.Burgoyne.B (actsProperly_of_core)
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K] {d : ℕ}

theorem conjSL_neg (A : GL (Fin 2) K) (g : SL(2, K)) : conjSL (-A) g = conjSL A g := by
  apply Subtype.ext
  simp only [coe_conjSL, inv_neg, Units.val_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem qEquiv_single_two_mul_self (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    qEquiv h2 ha (Pi.single 2 1) * qEquiv h2 ha (Pi.single 2 1) = 1 := by
  rw [qEquiv_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qMat]

theorem rho_eq_one_of_fix_left (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) {z : equalDeterminants K}
    (hfix : ∀ g, conjSL z.val.1 g = g)
    (hY : (rho z).val (qEquiv h2 ha (Pi.single 2 1)) = qEquiv h2 ha (Pi.single 2 1)) :
    rho z = 1 := by
  obtain ⟨c, hc⟩ := eq_scalar_of_conjSL_eq hfix
  rw [rho_apply, hc] at hY
  set Y₀ := qEquiv h2 ha (Pi.single 2 1) with hY₀def
  have hYY : Y₀ * Y₀ = 1 := qEquiv_single_two_mul_self h2 ha
  have hz2 : (c : K) • (((z.val.2⁻¹ : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have e := congrArg (fun M => Y₀ * M) hY
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      ← Matrix.mul_assoc, hYY] at e
    simpa using e
  apply Subtype.ext
  apply LinearEquiv.ext
  intro M
  change (rho z).val M = M
  rw [rho_apply, hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
    ← Matrix.mul_smul, hz2, Matrix.mul_one]

theorem rho_eq_one_of_fix_right (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) {z : equalDeterminants K}
    (hfix : ∀ g, conjSL z.val.2 g = g)
    (hY : (rho z).val (qEquiv h2 ha (Pi.single 2 1)) = qEquiv h2 ha (Pi.single 2 1)) :
    rho z = 1 := by
  obtain ⟨c, hc⟩ := eq_scalar_of_conjSL_eq hfix
  rw [rho_apply, hc] at hY
  set Y₀ := qEquiv h2 ha (Pi.single 2 1) with hY₀def
  have hYY : Y₀ * Y₀ = 1 := qEquiv_single_two_mul_self h2 ha
  have hci : (((GeneralLinearGroup.scalar (Fin 2) c)⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = (c : K)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← map_inv, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Units.val_inv_eq_inv_val]
  rw [hci, Matrix.mul_smul, Matrix.mul_one] at hY
  have hz1 : (z.val.1 : Matrix (Fin 2) (Fin 2) K) = (c : K) • 1 := by
    have e := congrArg (fun M => ((c : K) • M) * Y₀) hY
    rw [smul_smul, mul_inv_cancel₀ c.ne_zero, one_smul, Matrix.mul_assoc, hYY, Matrix.mul_one,
      Matrix.smul_mul, hYY] at e
    exact e
  apply Subtype.ext
  apply LinearEquiv.ext
  intro M
  change (rho z).val M = M
  rw [rho_apply, hz1, hc, hci, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
    smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul]

variable [Finite K]

theorem slice_two_actsProperly_gen (hK : ringChar K ≠ 2) (hd : 5 ≤ d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {α a : K}
    (hW : OSliceW (by omega : 4 ≤ d) w α a) (hker : OKer (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hcore : ∀ y ∈ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)),
      ∃ (R : GL (Fin d) K) (hR : R ∈ matrixIsometries (oQ (diagGL hw))),
        R ∈ oIsoBlock K hw jSet ∧ y = oκ _ (linPair R hR))
    {Y : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)))
    (F : SL(2, K) →* matrixDerived (oQ (diagGL hw))) (hFinj : Function.Injective F)
    (hFm : ∀ x, ∃ M : Matrix (Fin 4) (Fin 4) K,
      (((F x : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        embed4 K (by omega) M)
    (side : equalDeterminants K → GL (Fin 2) K)
    (hconj : ∀ (X : oIsoBlock K hw wSet) (z : equalDeterminants K),
      qGamma (Ring.two_ne_zero hK) hW.ha (oBlkHom (Ring.two_ne_zero hK) (by omega) hw hW X) =
        rho z → ∀ g, (X : GL (Fin d) K) * F g * (X : GL (Fin d) K)⁻¹ =
          F (conjSL (side z) g))
    (hsign : conjSL (side (zSign hW.ha)) unipSL1 ≠ unipSL1)
    (hfix : ∀ z : equalDeterminants K, (∀ g, conjSL (side z) g = g) →
      (rho z).val (qEquiv (Ring.two_ne_zero hK) hW.ha (Pi.single 2 1)) =
        qEquiv (Ring.two_ne_zero hK) hW.ha (Pi.single 2 1) → rho z = 1) :
    ActsProperly (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)) Y (slice F.range) ⊥ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hd4 : 4 ≤ d := by omega
  have hLZ : ∀ g ∈ F.range, g ∈ (StatedScalars (Fin d) K).subgroupOf
      (matrixDerived (oQ (diagGL hw))) → g = 1 := by
    rintro _ ⟨x, rfl⟩ ⟨c, hc⟩
    have hc' : GeneralLinearGroup.scalar (Fin d) c =
        ((F x : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) := hc
    obtain ⟨M, hM⟩ := hFm x
    have e44 := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K)
      ⟨4, by omega⟩ ⟨4, by omega⟩) hc'
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at e44
    rw [hM, embed4_apply_of hd4 _ (Or.inl (by simp))] at e44
    simp only [↓reduceIte] at e44
    apply Subtype.ext
    rw [← hc', Subgroup.coe_one]
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, e44, Units.val_one, Matrix.scalar_apply, diagonal_one]
  have hconjL : ∀ (R : GL (Fin d) K) (hR : R ∈ matrixIsometries (oQ (diagGL hw)))
      (z : equalDeterminants K) (hRW : R ∈ oIsoBlock K hw wSet),
      qGamma h2 hW.ha (oBlkHom h2 hd4 hw hW ⟨R, hRW⟩) = rho z → ∀ x,
      oκ _ (linPair R hR) * conjProjH (matrixDerived (oQ (diagGL hw))) (F x) *
        (oκ _ (linPair R hR))⁻¹ =
          conjProjH (matrixDerived (oQ (diagGL hw))) (F (conjSL (side z) x)) := by
    intro R hR z hRW hz x
    rw [kappa_linPair_conj]
    congr 1
    apply Subtype.ext
    change ((matrixDerivedConjugation _ (linPair R hR) (F x) : matrixDerived _) :
      GL (Fin d) K) = _
    rw [coe_conj_linPair]
    exact hconj ⟨R, hRW⟩ z hz x
  have hSmem : signGL K (jSet : Finset (Fin d)) ∈ oIsoBlock K hw wSet := by
    rw [mem_oIsoBlock_iff]
    refine ⟨signGL_mem hw _, fun i j hij => ?_⟩
    change signMat K jSet i j = _
    simp only [signMat, diagonal_apply]
    by_cases hij' : i = j
    · subst hij'
      have hi : i ∉ (jSet : Finset (Fin d)) := by
        rcases hij with h | h <;> exact fun h' => h (jSet_subset_wSet h')
      simp [hi]
    · simp [hij']
  have hzS : qGamma h2 hW.ha (oBlkHom h2 hd4 hw hW ⟨signGL K jSet, hSmem⟩) =
      rho (zSign hW.ha) := qGamma_sign h2 hW.ha (by
        rw [coe_oBlkHom, coe_signGL]
        exact blk4_signMat_jSet hd4)
  set t := oκ (oQ (diagGL hw)) (sgnPair h2 hw jSet) with ht_def
  have htconj : ∀ x, t * conjProjH (matrixDerived (oQ (diagGL hw))) (F x) * t⁻¹ =
      conjProjH (matrixDerived (oQ (diagGL hw))) (F (conjSL (side (zSign hW.ha)) x)) :=
    fun x => hconjL _ _ (zSign hW.ha) hSmem hzS x
  have htt : t * t = 1 := by
    rw [ht_def, ← map_mul]
    have : sgnPair h2 hw (jSet : Finset (Fin d)) * sgnPair h2 hw jSet = 1 := by
      apply Subtype.ext
      apply SemidirectProduct.ext
      · change signGL K jSet * glFieldAut (Fin d) K 1 (signGL K jSet) = 1
        rw [map_one, MulAut.one_apply]
        exact Units.ext (signMat_mul_self _)
      · change (1 : K ≃+* K) * 1 = 1
        rw [mul_one]
    rw [this, map_one]
  have hord : orderOf t = 2 := by
    refine orderOf_eq_prime (by rw [pow_two, htt]) fun h1 => ?_
    obtain ⟨-, c, hc⟩ := hker _ h1
    have e0 := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K)
      ⟨0, by omega⟩ ⟨0, by omega⟩) hc
    have e4 := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K)
      ⟨4, by omega⟩ ⟨4, by omega⟩) hc
    change _ = signMat K jSet _ _ at e0 e4
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq, signMat,
      diagonal_apply_eq] at e0 e4
    have h0 : (⟨0, by omega⟩ : Fin d) ∈ (jSet : Finset (Fin d)) := by simp [mem_jSet]
    have h4 : (⟨4, by omega⟩ : Fin d) ∉ (jSet : Finset (Fin d)) := by simp [mem_jSet]
    simp only [h0, h4, ↓reduceIte] at e0 e4
    rw [e4] at e0
    exact h2 (by linear_combination e0)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hsl : ∀ b, b ∈ slice F.range ↔
      ∃ x, b = conjProjH (matrixDerived (oQ (diagGL hw))) (F x) := by
    intro b
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨F x, ⟨x, rfl⟩, rfl⟩
  have hinjS := conjProjH_injective_of_inf hinj hLZ
  have hfeq : ∀ x x', conjProjH (matrixDerived (oQ (diagGL hw))) (F x) =
      conjProjH (matrixDerived (oQ (diagGL hw))) (F x') → x = x' := by
    intro x x' h
    have := @hinjS ⟨F x, ⟨x, rfl⟩⟩ ⟨F x', ⟨x', rfl⟩⟩ h
    exact hFinj (congrArg Subtype.val this)
  have htN : t ∈ normalizer (slice F.range : Set (MulAut (StatedProj
      (matrixDerived (oQ (diagGL hw)))))) := by
    rw [mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      obtain ⟨x, rfl⟩ := (hsl b).1 hb
      rw [htconj]
      exact (hsl _).2 ⟨_, rfl⟩
    · intro hb
      obtain ⟨x, hx⟩ := (hsl _).1 hb
      have e : b = t * (t * b * t⁻¹) * t⁻¹ := by
        rw [htinv]
        calc b = (t * t) * b * (t * t) := by rw [htt, one_mul, mul_one]
          _ = _ := by group
      rw [e, hx, htconj]
      exact (hsl _).2 ⟨_, rfl⟩
  have htC : ∃ b ∈ slice F.range, t * b ≠ b * t := by
    refine ⟨_, (hsl _).2 ⟨unipSL1, rfl⟩, fun h => hsign (hfeq _ _ ?_)⟩
    rw [← htconj, h, mul_inv_cancel_right]
  have hO : ∀ y ∈ oddCoreIn B t, ∃ (R : GL (Fin d) K)
      (hR : R ∈ matrixIsometries (oQ (diagGL hw))) (hRW : R ∈ oIsoBlock K hw wSet)
      (z : equalDeterminants K), R ∈ oIsoBlock K hw jSet ∧ y = oκ _ (linPair R hR) ∧
        qGamma h2 hW.ha (oBlkHom h2 hd4 hw hW ⟨R, hRW⟩) = rho z := by
    intro y hy
    obtain ⟨R, hR, hRJ, rfl⟩ := hcore y hy
    have hRW := oIsoBlock_jSet_le hw hRJ
    have hodd := odd_orderOf_of_mem_oddCoreIn hy
    obtain ⟨-, c, hc⟩ := hker _ (by
      rw [map_pow]; exact pow_orderOf_eq_one (oκ _ (linPair R hR)))
    obtain ⟨hl, -⟩ := pow_left_of_right_eq_one (linPair_right R hR)
      (orderOf (oκ _ (linPair R hR)))
    rw [hl, linPair_left] at hc
    have hRm : R ^ orderOf (oκ _ (linPair R hR)) = 1 := by
      have e44 := oIsoBlock_jSet_apply_four hw hd (pow_mem hRJ (orderOf (oκ _ (linPair R hR))))
      rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at e44
      have hc1 : c = 1 := Units.ext e44
      rw [← hc, hc1, map_one]
    have hpow : (⟨R, hRW⟩ : oIsoBlock K hw wSet) ^ orderOf (oκ _ (linPair R hR)) = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hRm)
    obtain ⟨z, hz⟩ := exists_rho_of_odd h2 hd4 hw hW ⟨R, hRW⟩ hodd hpow
    exact ⟨R, hR, hRW, z, hRJ, rfl, hz⟩
  have hON : oddCoreIn B t ≤ normalizer (slice F.range : Set (MulAut (StatedProj
      (matrixDerived (oQ (diagGL hw)))))) := by
    have hfwd : ∀ y ∈ oddCoreIn B t, ∀ b ∈ slice F.range, y * b * y⁻¹ ∈ slice F.range := by
      intro y hy b hb
      obtain ⟨R, hR, hRW, z, -, rfl, hz⟩ := hO y hy
      obtain ⟨x, rfl⟩ := (hsl b).1 hb
      rw [hconjL R hR z hRW hz x]
      exact (hsl _).2 ⟨_, rfl⟩
    intro y hy
    rw [mem_normalizer_iff]
    intro b
    refine ⟨hfwd y hy b, fun hb => ?_⟩
    have := hfwd y⁻¹ (inv_mem hy) _ hb
    simpa [mul_assoc] using this
  have hOC : ∀ y ∈ oddCoreIn B t, (∀ b ∈ slice F.range, y * b = b * y) → y = 1 := by
    intro y hy hcomm
    obtain ⟨R, hR, hRW, z, hRJ, rfl, hz⟩ := hO y hy
    have hfx : ∀ x, conjSL (side z) x = x := by
      intro x
      apply hfeq
      rw [← hconjL R hR z hRW hz x, hcomm _ ((hsl _).2 ⟨x, rfl⟩), mul_inv_cancel_right]
    have hcol : blk4 hd4 (R : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single 2 1 = Pi.single 2 1 := by
      funext k
      have hRk := (mem_oIsoBlock_iff hw).1 hRJ |>.2 ⟨k, by omega⟩ ⟨((2 : Fin 4) : ℕ), by omega⟩
        (Or.inr (by simp [mem_jSet]))
      simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [blk4_apply, hRk]
      by_cases hk : k = 2
      · subst hk
        simp
      · have : (⟨k, by omega⟩ : Fin d) ≠ ⟨((2 : Fin 4) : ℕ), by omega⟩ := fun h =>
          hk (Fin.ext (by simpa using h))
        simp only [this, ↓reduceIte]
        simp [hk]
    have hY₀ := congrArg (fun γ : DeterminantIsometries K => γ.val (qEquiv h2 hW.ha
      (Pi.single 2 1))) hz
    rw [qGamma_apply, coe_oBlkHom, hcol] at hY₀
    have hrho : rho z = 1 := hfix z hfx hY₀.symm
    have hR1 : oBlkHom h2 hd4 hw hW ⟨R, hRW⟩ = 1 := by
      apply qGamma_injective h2 hW.ha
      rw [hz, hrho, map_one]
    have hR : R = 1 := by
      apply Units.ext
      ext i j
      rcases Nat.lt_or_ge (i : ℕ) 4 with hi | hi
      · rcases Nat.lt_or_ge (j : ℕ) 4 with hj | hj
        · have e := congrArg (fun X : CatalogueBGraphForm.isometryGroup 4 K
            (diagGL (qW_ne_zero hW.ha)) => ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
              ⟨i, hi⟩ ⟨j, hj⟩) hR1
          simp only [coe_oBlkHom, blk4_apply] at e
          rw [e]
          simp only [Subgroup.coe_one, Units.val_one, one_apply, Fin.mk.injEq]
          by_cases hij : i = j
          · subst hij
            simp
          · have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
            simp [hij, this]
        · rw [(mem_oIsoBlock_iff hw).1 hRW |>.2 i j (Or.inr (by simp [mem_wSet]; omega)),
            Units.val_one, one_apply]
      · rw [(mem_oIsoBlock_iff hw).1 hRW |>.2 i j (Or.inl (by simp [mem_wSet]; omega)),
          Units.val_one, one_apply]
    subst hR
    have : linPair (1 : GL (Fin d) K) hR = 1 := by
      apply Subtype.ext
      apply SemidirectProduct.ext <;> rfl
    rw [this, map_one]
  exact actsProperly_of_core hord hY hYO htN htC hON hOC

theorem slice_two_actsProperly_L (hK : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K)
    (hd : 5 ≤ d) {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K}
    (hW : OSliceW (by omega : 4 ≤ d) w α a) (hker : OKer (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hcore : ∀ y ∈ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)),
      ∃ (R : GL (Fin d) K) (hR : R ∈ matrixIsometries (oQ (diagGL hw))),
        R ∈ oIsoBlock K hw jSet ∧ y = oκ _ (linPair R hR))
    {Y : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet))) :
    ActsProperly (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)) Y
      (slice (oSliceH (Ring.two_ne_zero hK) (by omega) (by omega) hw hW).range) ⊥ :=
  slice_two_actsProperly_gen hK hd hw hW hker hinj hcore hY hYO _
    (oSliceH_injective _ _ _ hw hW) (fun _ => ⟨_, coe_oSlice _ _ _ _⟩) (fun z => z.val.1)
    (fun X _ hz g => conj_oSlice_of_mem _ _ hw hW X hz g) (conjSL_qX_ne hW.ha)
    (fun _ hfx hY₀ => rho_eq_one_of_fix_left _ hW.ha hfx hY₀)

theorem slice_two_actsProperly_R (hK : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K)
    (hd : 5 ≤ d) {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K}
    (hW : OSliceW (by omega : 4 ≤ d) w α a) (hker : OKer (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hcore : ∀ y ∈ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)),
      ∃ (R : GL (Fin d) K) (hR : R ∈ matrixIsometries (oQ (diagGL hw))),
        R ∈ oIsoBlock K hw jSet ∧ y = oκ _ (linPair R hR))
    {Y : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet))) :
    ActsProperly (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)) Y
      (slice (oSliceRH (Ring.two_ne_zero hK) (by omega) (by omega) hw hW).range) ⊥ :=
  slice_two_actsProperly_gen hK hd hw hW hker hinj hcore hY hYO _
    (oSliceRH_injective _ _ _ hw hW) (fun _ => ⟨_, coe_oSliceR _ _ _ _⟩) (fun z => z.val.2)
    (fun X _ hz g => conj_oSliceR_of_mem _ _ hw hW X hz g)
    (by
      change conjSL (-qXGL hW.ha) unipSL1 ≠ unipSL1
      rw [conjSL_neg]
      exact conjSL_qX_ne hW.ha)
    (fun _ hfx hY₀ => rho_eq_one_of_fix_right _ hW.ha hfx hY₀)

abbrev twinL (hK : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K) (hd : 5 ≤ d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW (by omega : 4 ≤ d) w α a) :
    Subgroup (matrixDerived (oQ (diagGL hw))) :=
  (oSliceH (Ring.two_ne_zero hK) (by omega) (by omega) hw hW).range

abbrev twinR (hK : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K) (hd : 5 ≤ d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW (by omega : 4 ≤ d) w α a) :
    Subgroup (matrixDerived (oQ (diagGL hw))) :=
  (oSliceRH (Ring.two_ne_zero hK) (by omega) (by omega) hw hW).range

abbrev twinU (hK : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K) (hd : 5 ≤ d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW (by omega : 4 ≤ d) w α a) :
    MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))) :=
  conjProjH (matrixDerived (oQ (diagGL hw)))
    (oSliceH (Ring.two_ne_zero hK) (by omega) (by omega) hw hW (-1))

theorem slice_twin_props (hK : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K) (hd : 5 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW (by omega : 4 ≤ d) w α a)
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B) :
    orderOf (twinU hK hK5 hd hw hW) = 2 ∧
      Nonempty (slice (twinL hK hK5 hd hw hW) ≃* SL(2, K)) ∧
      Nonempty (slice (twinR hK hK5 hd hw hW) ≃* SL(2, K)) ∧
      (∀ x ∈ slice (twinL hK hK5 hd hw hW), ∀ y ∈ slice (twinR hK hK5 hd hw hW),
        x * y = y * x) ∧
      twinU hK hK5 hd hw hW ∈ slice (twinL hK hK5 hd hw hW) ∧
      twinU hK hK5 hd hw hW ∈ slice (twinR hK hK5 hd hw hW) ∧
      (∀ x, x ∈ slice (twinL hK hK5 hd hw hW) → x ∈ slice (twinR hK hK5 hd hw hW) →
        x = 1 ∨ x = twinU hK hK5 hd hw hW) ∧
      slice (twinL hK hK5 hd hw hW) ≤ centralizer ({twinU hK hK5 hd hw hW} :
        Set (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))) ∧
      IsPComponent 2 ((slice (twinL hK hK5 hd hw hW)).subgroupOf
        (B ⊓ centralizer ({twinU hK hK5 hd hw hW} :
          Set (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))))) ∧
      slice (twinR hK hK5 hd hw hW) ≤ centralizer ({twinU hK hK5 hd hw hW} :
        Set (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))) ∧
      IsPComponent 2 ((slice (twinR hK hK5 hd hw hW)).subgroupOf
        (B ⊓ centralizer ({twinU hK hK5 hd hw hW} :
          Set (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))))) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hd4 : 4 ≤ d := by omega
  have hK4 : 4 ≤ Nat.card K := by omega
  have hHeq : matrixDerived (oQ (diagGL hw)) = ⁅CatalogueBGraphForm.isometryGroup d K (diagGL hw),
      CatalogueBGraphForm.isometryGroup d K (diagGL hw)⁆ :=
    matrixDerived_oQ h2 (diagGL hw) (diagGL_transpose hw)
  have hHI : ∀ h : matrixDerived (oQ (diagGL hw)),
      (h : GL (Fin d) K) ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) :=
    fun h => Subgroup.commutator_le_self _ (by rw [← hHeq]; exact h.2)
  set f := oSliceH h2 hK4 hd4 hw hW with hf
  set fR := oSliceRH h2 hK4 hd4 hw hW with hfR
  have hfinj := oSliceH_injective h2 hK4 hd4 hw hW
  have hfRinj := oSliceRH_injective h2 hK4 hd4 hw hW
  have hfm : ∀ x, ((f x : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) =
      oSlice K h2 hd4 hW.ha x := fun x => rfl
  have hfRm : ∀ x, ((fR x : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) =
      oSliceR K h2 hd4 hW.ha x := fun x => rfl
  set u₀ := f (-1) with hu₀
  have hu₀R : fR (-1) = u₀ := Subtype.ext (oSliceR_neg_one h2 hd4 hW.ha)
  have hu₀m : (((u₀ : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = embed4 K hd4 (-1) := by
    rw [hu₀, hfm, coe_oSlice]
    congr 1
    exact qLambda_neg_one h2 hW.ha
  set e₁ : f.range ≃* SL(2, K) := (MonoidHom.ofInjective hfinj).symm with he₁
  set e₂ : fR.range ≃* SL(2, K) := (MonoidHom.ofInjective hfRinj).symm with he₂
  have hu₁ : u₀ ∈ f.range := ⟨-1, rfl⟩
  have hu₂ : u₀ ∈ fR.range := ⟨-1, hu₀R⟩
  have hneg : ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := by simp
  have he1 : ((e₁ ⟨u₀, hu₁⟩ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := by
    have : e₁ ⟨u₀, hu₁⟩ = -1 := by
      rw [he₁, MulEquiv.symm_apply_eq]
      rfl
    rw [this, hneg]
  have he2 : ((e₂ ⟨u₀, hu₂⟩ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := by
    have : e₂ ⟨u₀, hu₂⟩ = -1 := by
      rw [he₂, MulEquiv.symm_apply_eq]
      exact Subtype.ext hu₀R.symm
    rw [this, hneg]
  have hLZgen : ∀ g : matrixDerived (oQ (diagGL hw)),
      (∃ M : Matrix (Fin 4) (Fin 4) K, (((g : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = embed4 K hd4 M) →
      g ∈ (StatedScalars (Fin d) K).subgroupOf (matrixDerived (oQ (diagGL hw))) → g = 1 := by
    rintro g ⟨M, hM⟩ ⟨c, hc⟩
    have hc' : GeneralLinearGroup.scalar (Fin d) c =
        ((g : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) := hc
    have e44 := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K)
      ⟨4, by omega⟩ ⟨4, by omega⟩) hc'
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at e44
    rw [hM, embed4_apply_of hd4 _ (Or.inl (by simp))] at e44
    simp only [↓reduceIte] at e44
    apply Subtype.ext
    rw [← hc', Subgroup.coe_one]
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, e44, Units.val_one, Matrix.scalar_apply, diagonal_one]
  have hLZ₁ : ∀ g ∈ f.range, g ∈ (StatedScalars (Fin d) K).subgroupOf
      (matrixDerived (oQ (diagGL hw))) → g = 1 := by
    rintro _ ⟨x, rfl⟩
    exact hLZgen _ ⟨_, coe_oSlice _ _ _ x⟩
  have hLZ₂ : ∀ g ∈ fR.range, g ∈ (StatedScalars (Fin d) K).subgroupOf
      (matrixDerived (oQ (diagGL hw))) → g = 1 := by
    rintro _ ⟨x, rfl⟩
    exact hLZgen _ ⟨_, coe_oSliceR _ _ _ x⟩
  have hcomm_u₀ : ∀ h : matrixDerived (oQ (diagGL hw)),
      (((h : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        embed4 K hd4 (-1) = embed4 K hd4 (-1) *
          (((h : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) →
      h * u₀ = u₀ * h := by
    intro h hh
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hu₀m]
    exact hh
  set M := (oBlock K hw wSet).subgroupOf (matrixDerived (oQ (diagGL hw))) with hM
  have hLM₁ : f.range ≤ M := by
    rintro _ ⟨x, rfl⟩
    exact mem_subgroupOf.2 (oSlice_mem_oBlock h2 hK4 hd4 hw hW x)
  have hLM₂ : fR.range ≤ M := by
    rintro _ ⟨x, rfl⟩
    exact mem_subgroupOf.2 (oSliceR_mem_oBlock h2 hK4 hd4 hw hW x)
  have hMu : ∀ g ∈ M, g * u₀ = u₀ * g := fun g hg => hcomm_u₀ g
    (commute_embed4_of_mem h2 hd4 hw (oBlock_le_oIsoBlock hw wSet (mem_subgroupOf.1 hg)))
  have hLu₁ : ∀ g ∈ f.range, g * u₀ = u₀ * g := fun g hg => hMu g (hLM₁ hg)
  have hLu₂ : ∀ g ∈ fR.range, g * u₀ = u₀ * g := fun g hg => hMu g (hLM₂ hg)
  have hLn₁ : ∀ m ∈ M, ∀ g ∈ f.range, m * g * m⁻¹ ∈ f.range := by
    rintro m hm _ ⟨x, rfl⟩
    have hnm := oBlock_le_normalizer h2 hd4 hw hW (mem_subgroupOf.1 hm)
    obtain ⟨x', hx'⟩ := (mem_normalizer_iff.1 hnm (oSlice K h2 hd4 hW.ha x)).1 ⟨x, rfl⟩
    exact ⟨x', Subtype.ext hx'⟩
  have hLn₂ : ∀ m ∈ M, ∀ g ∈ fR.range, m * g * m⁻¹ ∈ fR.range := by
    rintro m hm _ ⟨x, rfl⟩
    have hnm := oBlock_le_normalizer_R h2 hd4 hw hW (mem_subgroupOf.1 hm)
    obtain ⟨x', hx'⟩ := (mem_normalizer_iff.1 hnm (oSliceR K h2 hd4 hW.ha x)).1 ⟨x, rfl⟩
    exact ⟨x', Subtype.ext hx'⟩
  have hnorm : ∀ h : matrixDerived (oQ (diagGL hw)), h * u₀ = u₀ * h →
      ∀ m ∈ M, h * m * h⁻¹ ∈ M := by
    intro h hh m hm
    have hhm : (((h : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) * embed4 K hd4 (-1) = embed4 K hd4 (-1) *
          (((h : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      have := congrArg (fun g : matrixDerived (oQ (diagGL hw)) => ((g : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K)) hh
      simpa only [Subgroup.coe_mul, Units.val_mul, hu₀m] using this
    rw [embed4_neg_one] at hhm
    have hc := (commute_signMat_iff h2 _ _).1 hhm.symm
    exact mem_subgroupOf.2 (conj_mem_oBlock hw (hHI h) hc (mem_subgroupOf.1 hm))
  have hu2 : conjProjH (matrixDerived (oQ (diagGL hw))) u₀ ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    have : u₀ * u₀ = 1 := by
      rw [hu₀, ← map_mul]
      have : (-1 : SL(2, K)) * -1 = 1 := by simp
      rw [this, map_one]
    rw [this, map_one]
  have hcommS : ∀ x ∈ slice f.range, ∀ y ∈ slice fR.range, x * y = y * x := by
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩ _ ⟨_, ⟨g', rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hfm, hfRm]
    exact oSlice_mul_oSliceR h2 hd4 hW.ha g g'
  refine ⟨orderOf_sliceInv hinj hLZ₁ hK hu₁ e₁ he1, ⟨sliceEquivSL hinj hLZ₁ e₁⟩,
    ⟨sliceEquivSL hinj hLZ₂ e₂⟩, hcommS, ⟨u₀, hu₁, rfl⟩, ⟨u₀, hu₂, rfl⟩, ?_,
    slice_le_centralizer hLu₁,
    slice_isPComponent₂ hinj hB hLZ₁ hK hK4 hu₁ e₁ he1 hLu₁ hLM₁ hMu hLn₁ hnorm,
    slice_le_centralizer hLu₂,
    slice_isPComponent₂ hinj hB hLZ₂ hK hK4 hu₂ e₂ he2 hLu₂ hLM₂ hMu hLn₂ hnorm⟩
  intro x hx₁ hx₂
  have hZ := center_slice hinj hLZ₁ hu₁ e₁ he1
  have hxZ : x ∈ (center (slice f.range)).map (slice f.range).subtype := by
    refine ⟨⟨x, hx₁⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    rintro ⟨y, hy⟩
    exact Subtype.ext (hcommS y hy x hx₂)
  rw [hZ] at hxZ
  exact eq_one_or_eq_of_mem_zpowers hu2 hxZ

end CFSG.ComponentClassification.Burgoyne.O
