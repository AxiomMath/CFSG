module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QOPcF
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QF
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrthFam
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Props

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL)

variable {K : Type} [Field K]

theorem coe_eq_smul_of_projH_eq_one {d : ℕ} {H : Subgroup (GL (Fin d) K)} {s : H}
    (hs : projH H s = 1) : ∃ μ : K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = μ • 1 := by
  have h1 := (QuotientGroup.eq_one_iff _).1 hs
  rw [mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨(c : K), ?_⟩
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

variable [Finite K]

theorem exists_pc_model (hK : ringChar K ≠ 2) {n : ℕ} {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R) {T : GL (Fin (2 * n)) K}
    (hT : T ∈ matrixDerived (oQ R))
    (hT2 : (T : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * T = -1) :
    ∃ (R₁ : GL (Fin (2 * n)) K) (A : matrixDerived (oQ R₁))
      (θ : StatedProj (matrixDerived (oQ R)) ≃* StatedProj (matrixDerived (oQ R₁))),
      (R₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-(-1 : K))) ∧
        ((A : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
          blkDiag n (jMat (-1 : K)) ∧ θ (projH _ ⟨T, hT⟩) = projH _ A := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hTiso : T ∈ matrixIsometries (oQ R) := matrixDerived_le_isometries _ hT
  set Tm := (T : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hTm
  set Rm := (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hRm
  have hiso : Tmᵀ * Rm * Tm = Rm := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
    ((mem_matrixIsometries_oQ h2 R hR T).1 hTiso)
  have hTT' : Tm * (-Tm) = 1 := by rw [Matrix.mul_neg, hT2, neg_neg]
  have hε : Tmᵀ * Rm = (-1 : K) • (Rm * Tm) := by
    calc Tmᵀ * Rm = Tmᵀ * Rm * (Tm * (-Tm)) := by rw [hTT', Matrix.mul_one]
      _ = Tmᵀ * Rm * Tm * (-Tm) := by rw [Matrix.mul_assoc (Tmᵀ * Rm)]
      _ = Rm * (-Tm) := by rw [hiso]
      _ = (-1 : K) • (Rm * Tm) := by rw [Matrix.mul_neg, neg_one_smul]
  have hS2 : Tm * Tm = (-1 : K) • 1 := by rw [neg_one_smul]; exact hT2
  have hc0 : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  obtain ⟨H₁, hgram₁, hAH₁⟩ := exists_pc_basis hK hR hc0 hS2 hε (fun _ => 1)
    (fun _ => one_ne_zero)
  obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = CatalogueBGraphForm.glTranspose (2 * n) K H₁ * R * H₁ :=
    ⟨_, rfl⟩
  have hgramR₁ : (H₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * H₁ = R₁ := by
    rw [hR₁]
    simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
  have hR₁m : (R₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-(-1 : K))) := by
    rw [← hgramR₁, hgram₁]
    simp only [one_smul]
    rfl
  obtain ⟨hS, -, -⟩ := exists_transport_of_gram hgramR₁ (g := linPair T hTiso)
    (linPair_right T hTiso)
  refine ⟨R₁, derivedTransport H₁⁻¹ 1 hS ⟨T, hT⟩, oTransport H₁⁻¹ 1 hS, hR₁m, ?_,
    oTransport_proj _ _ _ _⟩
  rw [coe_derivedTransport, Units.val_mul, Units.val_mul, inv_inv]
  calc ((H₁⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * Tm * H₁ =
      ((H₁⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * (Tm * H₁) := by
        rw [Matrix.mul_assoc]
    _ = ((H₁⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
        ((H₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * blkDiag n (jMat (-1 : K))) := by
        rw [hAH₁]
    _ = blkDiag n (jMat (-1 : K)) := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem famF_concl_of_model (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime)
    (hKc : Nat.card K = p ^ f) (hK3 : Nat.card K ≠ 3) {d : ℕ} (hd : 7 ≤ d) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {X : Type} [Group X] [Finite X]
    (θ₀ : X ≃* StatedProj (matrixDerived (oQ R))) {z : X} (hz : orderOf z = 2)
    {P : Subgroup X} (h8 : Nat.card P = 8)
    (hP : ∀ L : Subgroup (centralizer ({z} : Set X)), IsComponent L → Even (Nat.card L) →
      ∀ k ∈ L, ∀ g ∈ P, (k : X) * g = g * k) :
    ¬ ((∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u) ∧ ∀ q ∈ P, q * q = 1 → q = 1 ∨ q = z) ∧
      ¬ ∀ q ∈ P, q * q = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hz2 : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hz'2 : θ₀ z * θ₀ z = 1 := by rw [← map_mul, hz2, map_one]
  have hz'1 : θ₀ z ≠ 1 := fun h => hz1 (θ₀.injective (by rw [h, map_one]))
  obtain ⟨T, hT, hzT, hT2 | hT2⟩ := P51e.Orth.exists_lift_sq h2 (by omega) hR hz'2
  ·
    obtain ⟨w, hw, J, hJ, θ, hJne, hJc, -, hθ⟩ :=
      P51e.Orth.exists_sign_frame hK hR hT hT2 (by rw [← hzT]; exact hz'1)
    set π := (θ₀.trans θ).symm.toMonoidHom.comp (projH (matrixDerived (oQ (diagGL hw))))
      with hπdef
    have hπ : Function.Surjective π :=
      (θ₀.trans θ).symm.surjective.comp projH_surjective
    have hzπ : π ⟨signGL K J, hJ⟩ = z := by
      rw [hπdef, MonoidHom.comp_apply, ← hθ, ← hzT]
      simp
    have hker : ∀ s, π s = 1 →
        ∃ μ : K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = μ • 1 := by
      intro s hs
      refine coe_eq_smul_of_projH_eq_one ?_
      have e : (θ₀.trans θ).symm (projH _ s) = 1 := hs
      rwa [MulEquiv.map_eq_one_iff] at e
    subst hzπ
    exact famF_concl_sign hK hK3 (by omega) hw hJne hJc hJ π hπ hker h8 hP
  ·
    have hε : (T : Matrix (Fin d) (Fin d) K)ᵀ * (R : Matrix (Fin d) (Fin d) K) =
        (-1 : K) • ((R : Matrix (Fin d) (Fin d) K) * T) := by
      set Tm := (T : Matrix (Fin d) (Fin d) K) with hTm
      set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
      have hiso : Tmᵀ * Rm * Tm = Rm := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
        ((mem_matrixIsometries_oQ h2 R hR T).1 (matrixDerived_le_isometries _ hT))
      have hTT' : Tm * (-Tm) = 1 := by rw [Matrix.mul_neg, hT2, neg_neg]
      calc Tmᵀ * Rm = Tmᵀ * Rm * (Tm * (-Tm)) := by rw [hTT', Matrix.mul_one]
        _ = Tmᵀ * Rm * Tm * (-Tm) := by rw [Matrix.mul_assoc (Tmᵀ * Rm)]
        _ = Rm * (-Tm) := by rw [hiso]
        _ = (-1 : K) • (Rm * Tm) := by rw [Matrix.mul_neg, neg_one_smul]
    obtain ⟨m, hm⟩ := P51e.Orth.even_of_skew' h2 hε
    obtain rfl : d = 2 * m := by omega
    obtain ⟨R₁, A, θ, hR₁, hA, hθ⟩ := exists_pc_model hK hR hT hT2
    set π := (θ₀.trans θ).symm.toMonoidHom.comp (projH (matrixDerived (oQ R₁))) with hπdef
    have hπ : Function.Surjective π := (θ₀.trans θ).symm.surjective.comp projH_surjective
    have hzπ : π A = z := by
      rw [hπdef, MonoidHom.comp_apply, ← hθ, ← hzT]
      simp
    have hker : ∀ s, π s = 1 → ∃ μ : K,
        ((s : GL (Fin (2 * m)) K) : Matrix (Fin (2 * m)) (Fin (2 * m)) K) = μ • 1 := by
      intro s hs
      refine coe_eq_smul_of_projH_eq_one ?_
      have e : (θ₀.trans θ).symm (projH _ s) = 1 := hs
      rwa [MulEquiv.map_eq_one_iff] at e
    subst hzπ
    exact famF_concl_pc hK hp hKc (by omega) hR₁ hA π hπ hker hz2 h8 hP

theorem famF_POmegaOdd : FamF .POmegaOdd := by
  intro X _ _ _ n p f hp hp2 hX hq z hz P _ _ h8 hP
  have hmod := P51e.Comp.statedClassicalModel_of_lieModel (by decide) hX
  obtain ⟨⟨-, -, hn, -⟩, F, _, _, hFc, ⟨e⟩⟩ := hmod
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n F)
    (regular_coordinateQuadOdd n F h2 hn).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) F) : Matrix _ _ F) *ᵥ v) =
      ((1 : Fˣ) : F) * coordinateQuadOdd n F v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  exact famF_concl_of_model hF hp hFc (by rwa [hFc]) (by omega) hR
    ((coordinateOddWitnessEquiv F e).trans (oTransport 1 1 hS₁)) hz h8 hP

theorem famF_POmegaPlus : FamF .POmegaPlus := by
  intro X _ _ _ n p f hp hp2 hX hq z hz P _ _ h8 hP
  have hmod := P51e.Comp.statedClassicalModel_of_lieModel (by decide) hX
  obtain ⟨⟨-, -, hn⟩, F, _, _, hFc, ⟨e⟩⟩ := hmod
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n F)
    (regular_coordinateQuadPlus n F (by omega)).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
      ((1 : Fˣ) : F) * coordinateQuadPlus n F v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  exact famF_concl_of_model hF hp hFc (by rwa [hFc]) (by omega) hR
    ((coordinatePlusWitnessEquiv F e).trans (oTransport 1 1 hS₁)) hz h8 hP

theorem famF_POmegaMinus : FamF .POmegaMinus := by
  intro X _ _ _ n p f hp hp2 hX hq z hz P _ _ h8 hP
  have hmod := P51e.Comp.statedClassicalModel_of_lieModel (by decide) hX
  obtain ⟨⟨-, -, hn⟩, F, _, _, hFc, b, c, hirr, ⟨e⟩⟩ := hmod
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hn1 : 1 ≤ n := by omega
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadMinus n F hn1 b c)
    (regular_coordinateQuadMinus n F b c hn hirr).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
      ((1 : Fˣ) : F) * coordinateQuadMinus n F hn1 b c v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  exact famF_concl_of_model hF hp hFc (by rwa [hFc]) (by omega) hR
    ((coordinateMinusWitnessEquiv F hn1 b c e).trans (oTransport 1 1 hS₁)) hz h8 hP

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
