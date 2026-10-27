module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOLin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOCent

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat compInd)

section RingBlock

variable {A : Type*} [Ring A] {c : A}

theorem blkL_pow (hc : c * c = c) {B : A} (hB : B * c = c * B) (m : ℕ) :
    blkL c B ^ m = blkL c (B ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, blkL_one]
  | succ m ih => rw [pow_succ, ih, blkL_mul hc hB, ← pow_succ]

theorem blkL_sub_one (B : A) : blkL c B - 1 = (B - 1) * (1 - c) := by
  simp only [blkL, sub_mul, one_mul]
  abel

theorem eq_blkL_one_sub_of_blkL_eq_one (hc : c * c = c) {B : A} (hB : B * c = c * B)
    (h1 : blkL c B = 1) : B = blkL (1 - c) B := by
  have := blkL_mul_blkL_one_sub hc hB
  rw [h1, one_mul] at this
  exact this.symm

end RingBlock

variable {K : Type} [Field K] {d : ℕ}

theorem one_sub_compInd_mulVec_mem_suppOn (J : Finset (Fin d)) (z : Fin d → K) :
    (1 - compInd K J) *ᵥ z ∈ suppOn K J := by
  intro i hi
  simp [sub_mulVec, compInd, mulVec_diagonal, hi]

variable {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

theorem mem_oIsoBlock_compl_of_blkL_eq_one {J : Finset (Fin d)} {B : GL (Fin d) K}
    (hBI : B ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw))
    (hB : (B : Matrix (Fin d) (Fin d) K) * compInd K J = compInd K J * B)
    (h1 : blkL (compInd K J) (B : Matrix (Fin d) (Fin d) K) = 1) : B ∈ oIsoBlock K hw Jᶜ := by
  have hB' : (B : Matrix (Fin d) (Fin d) K) * compInd K Jᶜ = compInd K Jᶜ * B := by
    rw [compInd_compl, mul_sub, sub_mul, mul_one, one_mul, hB]
  have e : B = blkLGL (compInd_mul_self Jᶜ) B hB' := by
    apply Units.ext
    rw [coe_blkLGL, compInd_compl]
    exact eq_blkL_one_sub_of_blkL_eq_one (compInd_mul_self J) hB h1
  rw [e]
  exact blkLGL_mem_oIsoBlock hw Jᶜ hBI hB'

theorem oκ_linPair_fix_of_mem_oIsoBlock {J : Finset (Fin d)} {B : GL (Fin d) K}
    (hBJ : B ∈ oIsoBlock K hw Jᶜ) (hB : B ∈ matrixIsometries (oQ (diagGL hw)))
    {a : StatedProj (matrixDerived (oQ (diagGL hw)))} (ha : a ∈ blockP K hw J) :
    oκ _ (linPair B hB) a = a := by
  obtain ⟨g, hg, rfl⟩ := ha
  replace hg : (g : GL (Fin d) K) ∈ oBlock K hw J := hg
  rw [kappa_proj]
  congr 1
  apply Subtype.ext
  rw [coe_conj_linPair]
  have := commute_of_mem_oIsoBlock hw (oBlock_le_oIsoBlock hw J hg) hBJ
  rw [← this, mul_inv_cancel_right]

theorem b3_false (hK : ringChar K ≠ 2) (hker : OKer (oQ (diagGL hw))) {J I : Finset (Fin d)}
    (hJd : 2 * J.card ≠ d) (hI : I = J ∨ I = Jᶜ) (hIc : 2 ≤ Iᶜ.card)
    {U : Submodule K (Fin d → K)} (hU : Module.finrank K U ≤ 2) {B₁ B₂ : GL (Fin d) K}
    (hB₁ : B₁ ∈ matrixIsometries (oQ (diagGL hw))) (hB₂ : B₂ ∈ matrixIsometries (oQ (diagGL hw)))
    (hU₁ : ∀ v, ((B₁ : Matrix (Fin d) (Fin d) K) - 1) *ᵥ v ∈ U)
    (hU₂ : ∀ v, ((B₂ : Matrix (Fin d) (Fin d) K) - 1) *ᵥ v ∈ U)
    (hc₁ : oκ _ (linPair B₁ hB₁) * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * oκ _ (linPair B₁ hB₁))
    (hc₂ : oκ _ (linPair B₂ hB₂) * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * oκ _ (linPair B₂ hB₂))
    {m : ℕ} (hm : Odd m) (hm1 : oκ _ (linPair B₁ hB₁) ^ m = 1)
    (hmove₁ : ∃ a ∈ blockP K hw Iᶜ, oκ _ (linPair B₁ hB₁) a ≠ a)
    (hmove₂ : ∃ a ∈ blockP K hw I, oκ _ (linPair B₂ hB₂) a ≠ a) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hIso : ∀ {B : GL (Fin d) K}, B ∈ matrixIsometries (oQ (diagGL hw)) →
      B ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) := fun hB =>
    (mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw) _).1 hB
  have hS : ∀ {B : GL (Fin d) K} (hB : B ∈ matrixIsometries (oQ (diagGL hw))),
      oκ _ (linPair B hB) * oκ _ (sgnPair h2 hw J) =
        oκ _ (sgnPair h2 hw J) * oκ _ (linPair B hB) →
      B * signGL K J = signGL K J * B := by
    intro B hB hc
    have := commute_sign_of_commute h2 hw hker hJd hc
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_signGL]
    exact this.symm
  have hIc' : Iᶜ = J ∨ Iᶜ = Jᶜ := by
    rcases hI with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (compl_compl J)
  have hcI : ∀ {B : GL (Fin d) K}, B * signGL K J = signGL K J * B →
      (B : Matrix (Fin d) (Fin d) K) * compInd K I = compInd K I * B := fun h =>
    (commute_compInd_of_commute_sign hK J I hI h).symm
  have hcIc : ∀ {B : GL (Fin d) K}, B * signGL K J = signGL K J * B →
      (B : Matrix (Fin d) (Fin d) K) * compInd K Iᶜ = compInd K Iᶜ * B := fun h =>
    (commute_compInd_of_commute_sign hK J Iᶜ hIc' h).symm
  have hS₁ := hS hB₁ hc₁
  have hS₂ := hS hB₂ hc₂
  obtain ⟨a₂, ha₂, hne₂⟩ := hmove₂
  obtain ⟨a₁, ha₁, hne₁⟩ := hmove₁
  have hC₂ : blkL (compInd K I) (B₂ : Matrix (Fin d) (Fin d) K) ≠ 1 := fun h1 =>
    hne₂ (oκ_linPair_fix_of_mem_oIsoBlock hw
      (mem_oIsoBlock_compl_of_blkL_eq_one hw (hIso hB₂) (hcI hS₂) h1) hB₂ ha₂)
  have hC₁ : blkL (compInd K Iᶜ) (B₁ : Matrix (Fin d) (Fin d) K) ≠ 1 := fun h1 =>
    hne₁ (oκ_linPair_fix_of_mem_oIsoBlock hw
      (mem_oIsoBlock_compl_of_blkL_eq_one hw (hIso hB₁) (hcIc hS₁) h1) hB₁ ha₁)
  have hcol : ∀ {X : Finset (Fin d)} {B : GL (Fin d) K},
      (B : Matrix (Fin d) (Fin d) K) * compInd K X = compInd K X * B →
      (∀ v, ((B : Matrix (Fin d) (Fin d) K) - 1) *ᵥ v ∈ U) → ∀ v,
      (blkL (compInd K X) (B : Matrix (Fin d) (Fin d) K) - 1) *ᵥ v ∈ U ∧
      (blkL (compInd K X) (B : Matrix (Fin d) (Fin d) K) - 1) *ᵥ v ∈ suppOn K X := by
    intro X B hB hBU v
    rw [blkL_sub_one]
    constructor
    · rw [← mulVec_mulVec]
      exact hBU _
    · have e : ((B : Matrix (Fin d) (Fin d) K) - 1) * (1 - compInd K X) =
          (1 - compInd K X) * ((B : Matrix (Fin d) (Fin d) K) - 1) := by
        simp only [sub_mul, mul_sub, mul_one, one_mul, hB]
        abel
      rw [e, ← mulVec_mulVec]
      exact one_sub_compInd_mulVec_mem_suppOn X _
  have hex : ∀ {M : Matrix (Fin d) (Fin d) K}, M ≠ 1 → ∃ v, (M - 1) *ᵥ v ≠ 0 := by
    intro M hM
    by_contra h
    push Not at h
    apply hM
    rw [← sub_eq_zero]
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    simpa [mulVec_single_one] using this
  obtain ⟨v₂, hv₂⟩ := hex hC₂
  obtain ⟨v₁, hv₁⟩ := hex hC₁
  obtain ⟨hv₂U, hv₂I⟩ := hcol (hcI hS₂) hU₂ v₂
  obtain ⟨hv₁U, hv₁I⟩ := hcol (hcIc hS₁) hU₁ v₁
  obtain ⟨u, hu⟩ : ∃ u, u = (blkL (compInd K Iᶜ) (B₁ : Matrix (Fin d) (Fin d) K) - 1) *ᵥ v₁ :=
    ⟨_, rfl⟩
  rw [← hu] at hv₁ hv₁U hv₁I
  have hf : ∀ j, ∃ c : K,
      (blkL (compInd K Iᶜ) (B₁ : Matrix (Fin d) (Fin d) K) - 1) *ᵥ Pi.single j 1 = c • u := by
    intro j
    obtain ⟨hjU, hjI⟩ := hcol (hcIc hS₁) hU₁ (Pi.single j 1)
    exact exists_eq_smul_of_finrank_le_two hU hv₂U hv₂I hv₂ hv₁U hv₁I hv₁ hjU hjI
  choose f hf using hf
  have hrank : blkL (compInd K Iᶜ) (B₁ : Matrix (Fin d) (Fin d) K) = 1 + vecMulVec u f := by
    have e : blkL (compInd K Iᶜ) (B₁ : Matrix (Fin d) (Fin d) K) - 1 = vecMulVec u f := by
      ext i j
      have := congrFun (hf j) i
      rw [vecMulVec_apply, mul_comm]
      simpa [mulVec_single_one] using this
    rw [← e]
    abel
  have hC₁iso : (1 + vecMulVec u f)ᵀ * diagonal w * (1 + vecMulVec u f) = diagonal w := by
    have := (blkLGL_mem_oIsoBlock hw Iᶜ (hIso hB₁) (hcIc hS₁)).1
    rw [CatalogueBGraphForm.mem_isometryGroup, coe_diagGL, coe_blkLGL, hrank] at this
    exact this
  have hsq := mul_self_eq_one_of_isometry h2 (diagonal_transpose w) (fun v hv => by
    funext i
    have := congrFun hv i
    rw [mulVec_diagonal, Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left (hw i)) hC₁iso
  have hpow : oκ _ ((linPair B₁ hB₁) ^ m) = 1 := by rw [map_pow, hm1]
  obtain ⟨-, a, ha⟩ := hker _ hpow
  have hBm : (B₁ : Matrix (Fin d) (Fin d) K) ^ m = (a : K) • 1 := by
    obtain ⟨hl, -⟩ := pow_left_of_right_eq_one (linPair_right B₁ hB₁) m
    rw [hl, linPair_left] at ha
    rw [← Units.val_pow_eq_pow_val, ← ha, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
  have hCm : blkL (compInd K Iᶜ) (B₁ : Matrix (Fin d) (Fin d) K) ^ m =
      (a : K) • (1 - compInd K Iᶜ) + compInd K Iᶜ := by
    rw [blkL_pow (compInd_mul_self Iᶜ) (hcIc hS₁), hBm, blkL, Matrix.smul_mul, Matrix.one_mul]
  have hCodd : blkL (compInd K Iᶜ) (B₁ : Matrix (Fin d) (Fin d) K) ^ m =
      blkL (compInd K Iᶜ) (B₁ : Matrix (Fin d) (Fin d) K) := by
    obtain ⟨k, rfl⟩ := hm
    rw [pow_succ, pow_mul, sq, hrank, hsq, one_pow, one_mul]
  have hCa : 1 + vecMulVec u f = (a : K) • (1 - compInd K Iᶜ) + compInd K Iᶜ := by
    rw [← hrank, ← hCodd, hCm]
  have he : ∀ i j, (1 : Matrix (Fin d) (Fin d) K) i j + u i * f j =
      (a : K) * ((1 : Matrix (Fin d) (Fin d) K) i j - compInd K Iᶜ i j) + compInd K Iᶜ i j := by
    intro i j
    have := congrFun (congrFun hCa i) j
    simpa only [Matrix.add_apply, vecMulVec_apply, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul] using this
  have hck : ∀ i ∈ Iᶜ, compInd K Iᶜ i i = 0 := fun i hi => by
    rw [compInd, diagonal_apply_eq, ite_eq_left hi]
  have hcoff : ∀ i j, i ≠ j → compInd K Iᶜ i j = 0 := fun i j hij => by
    rw [compInd, diagonal_apply_ne _ hij]
  obtain ⟨k, hk, k', hk', hkk'⟩ := Finset.one_lt_card.1 (by omega : 1 < Iᶜ.card)
  have e1 := he k k
  have e2 := he k' k'
  have e3 := he k k'
  have e4 := he k' k
  rw [one_apply_eq, hck k hk] at e1
  rw [one_apply_eq, hck k' hk'] at e2
  rw [one_apply_ne hkk', hcoff k k' hkk'] at e3
  rw [one_apply_ne (Ne.symm hkk'), hcoff k' k (Ne.symm hkk')] at e4
  have hk1 : u k * f k = (a : K) - 1 := by linear_combination e1
  have hk2 : u k' * f k' = (a : K) - 1 := by linear_combination e2
  have hk3 : u k * f k' = 0 := by linear_combination e3
  have hk4 : u k' * f k = 0 := by linear_combination e4
  have ha1 : (a : K) = 1 := by
    have : ((a : K) - 1) * ((a : K) - 1) = 0 := by
      calc ((a : K) - 1) * ((a : K) - 1) = (u k * f k) * (u k' * f k') := by rw [hk1, hk2]
        _ = (u k * f k') * (u k' * f k) := by ring
        _ = 0 := by rw [hk3, zero_mul]
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  apply hC₁
  rw [hrank, hCa, ha1, one_smul, sub_add_cancel]

end CFSG.ComponentClassification.Burgoyne.C
