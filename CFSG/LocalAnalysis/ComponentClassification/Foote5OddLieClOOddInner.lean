module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOSplitNF
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOPlane
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOOddInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOOddSlice
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieCore

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)

theorem ClO.conj_injective_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) :
    Function.Injective (MulAut.conj : T' →* MulAut T') := by
  have hZ : center T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    apply hinj
    rw [map_one]
    ext y
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [(mem_center_iff.1 hx y).symm, mul_inv_cancel_right]
  have hZ' : center T' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [mem_bot]
    have hz' : e.symm z ∈ center T := by
      rw [mem_center_iff]
      intro y
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact mem_center_iff.1 hz (e y)
    rw [hZ, mem_bot] at hz'
    simpa using congrArg e hz'
  exact conj_injective hZ'

variable {K : Type} [Field K] {d : ℕ} [Finite K]

omit [Finite K] in
theorem ClO.commute_of_frame (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hker : OKer (oQ R)) (hsurj : OSurj (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)}
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (A'' : GL (Fin d) K) (hA'' : A'' ∈ matrixIsometries (oQ R))
    (hκ'' : oκ _ g = oκ _ (linPair A'' hA'')) {a b : ℕ} (hab : a + b = d)
    (c : Fin a ⊕ Fin b → Fin d → K)
    (hcA : ∀ x, (A'' : Matrix (Fin d) (Fin d) K) *ᵥ c x =
      (if x.isLeft then (-1 : K) else 1) • c x)
    (horth : ∀ x y, x ≠ y → c x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c y = 0)
    (hdiag : ∀ x, c x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c x ≠ 0)
    (hcase : ∀ (hw : ∀ l, famW (R : Matrix (Fin d) (Fin d) K) hab c l ≠ 0),
      OKer (oQ (diagGL hw)) → OSurj (oQ (diagGL hw)) →
      Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
        MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))) →
      ∀ Ro' : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))),
        Odd (Nat.card Ro') →
        (∀ y ∈ Ro', y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw (famJ hab)) =
          oκ _ (sgnPair (Ring.two_ne_zero hK) hw (famJ hab)) * y) →
        (∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw (famJ hab)) s = s →
          Odd (orderOf s) → ∀ y ∈ Ro', MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro') →
        ∀ r₁ ∈ Ro', ∀ r₂ ∈ Ro', r₁ * r₂ = r₂ * r₁) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨hw, S, hS, heq⟩ := exists_transport_of_family h2 hA'' hab c hcA horth hdiag
  have hcg : MulAut.congr (oTransport S 1 hS) (oκ _ g) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw (famJ hab)) := by
    rw [hκ'', oTransport_kappa, heq]
  refine commute_of_congr (oTransport S 1 hS) (fun R' hR'odd hR'i hR'c => ?_) hRodd hRi hRc
  rw [hcg] at hR'i hR'c
  exact hcase hw (hker.transport S 1 hS) (hsurj.transport S 1 hS)
    (ClO.conj_injective_of_mulEquiv (oTransport S 1 hS) hinj) R' hR'odd hR'i hR'c

theorem ClO.commute_diag_odd (hK : ringChar K ≠ 2) (hd7 : 7 ≤ d) (hdodd : Odd d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hsurj : OSurj (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * y)
    (hRc : ∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hJ1 : 1 ≤ J.card) (hJc1 : 1 ≤ Jᶜ.card) (hNF : 3 ≤ J.card → BlockNF w J)
    (hNFc : 3 ≤ Jᶜ.card → BlockNF w Jᶜ) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hd := card_compl_add J
  have hsurj' : ∀ y ∈ Ro, ∃ g : similarityPairs (oQ (diagGL hw)), y = oκ _ g :=
    fun y _ => hsurj y
  have hodd2 : ∀ k : ℕ, 2 * k ≠ d := fun k h => by
    obtain ⟨m, hm⟩ := hdodd
    omega
  have hplane : ∀ I : Finset (Fin d), I.card = 2 → BlockOK K w Iᶜ →
      (∀ y ∈ Ro, y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw I) =
        oκ _ (sgnPair (Ring.two_ne_zero hK) hw I) * y) →
      (∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw I) s = s → Odd (orderOf s) →
        ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro) →
      ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
    intro I hI2 hIc hRi' hRc'
    have hI := card_compl_add I
    have hcore := fun y (hy : y ∈ Ro) => ClO.split_two_core hK hw hker hinj hRodd hRi' hRc'
      hsurj' (hodd2 _) hIc hy
    obtain ⟨j₀, j₁, hj, rfl⟩ := Finset.card_eq_two.1 hI2
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∈ ({j₀, j₁} : Finset (Fin d))ᶜ :=
      Finset.card_pos.1 (by omega)
    exact ClO.commute_of_plane hw h2 hker hj ⟨x₀, Finset.mem_compl.1 hx₀⟩ hRodd hcore
  by_cases hJ2 : J.card = 2
  · exact hplane J hJ2 ((hNFc (by omega)).blockOK (by omega) fun h => by omega) hRi hRc
  by_cases hJc2 : Jᶜ.card = 2
  · rw [← oκ_sgnPair_compl h2 hw J] at hRi hRc
    refine hplane Jᶜ hJc2 ?_ hRi hRc
    rw [compl_compl]
    exact (hNF (by omega)).blockOK (by omega) fun h => by omega
  have h1 := ClO.split_eq_one_of_nf hK hd7 hdodd hw hker hinj hRodd hRi hRc hsurj' hJ1 hJc1 hJ2
    hJc2 hNF hNFc
  intro r₁ h₁ r₂ h₂
  rw [h1 r₁ h₁, h1 r₂ h₂]

theorem ClO.commute_inner_odd (hK : ringChar K ≠ 2) (hd7 : 7 ≤ d) (hdodd : Odd d)
    {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R))
    (hsurj : OSurj (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1) (hi : orderOf (oκ _ g) = 2)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  have hκ1 : oκ (oQ R) g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hi
    exact absurd hi (by norm_num)
  have hgg : oκ (oQ R) (g * g) = 1 := by
    rw [map_mul, ← pow_two, ← hi, pow_orderOf_eq_one]
  obtain ⟨-, c, hc⟩ := hker _ hgg
  have hc' : g.val.left * g.val.left = GeneralLinearGroup.scalar (Fin d) c := by
    rw [hc]
    change _ = g.val.left * glFieldAut (Fin d) K g.val.right g.val.left
    rw [hg1, map_one, MulAut.one_apply]
  obtain ⟨μ, hμ⟩ := (mem_similarityPairs_oQ h2 R hR g.val).1 g.2
  rw [hg1, show (R : Matrix (Fin d) (Fin d) K).map ⇑(1 : K ≃+* K) = R from by ext; rfl] at hμ
  obtain ⟨m, hm0, hA'R, hA'2⟩ := exists_isometric_involution hdodd hμ hc'
  obtain ⟨A', hA'def⟩ : ∃ A' : GL (Fin d) K,
      A' = GeneralLinearGroup.scalar (Fin d) (Units.mk0 m hm0)⁻¹ * g.val.left := ⟨_, rfl⟩
  have hA'c : (A' : Matrix (Fin d) (Fin d) K) = m⁻¹ • (g.val.left : Matrix (Fin d) (Fin d) K) := by
    rw [hA'def, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0]
  obtain ⟨Am, hAm⟩ : ∃ Am : Matrix (Fin d) (Fin d) K, Am = A' := ⟨_, rfl⟩
  have hAR : Amᵀ * Rm * Am = Rm := by rw [hAm, hA'c]; exact hA'R
  have hA2 : Am * Am = 1 := by rw [hAm, hA'c]; exact hA'2
  have hA' : A' ∈ matrixIsometries (oQ R) :=
    (mem_matrixIsometries_oQ h2 R hR A').2 ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2
      (by rw [← hAm]; exact hAR))
  have hκ : oκ _ g = oκ _ (linPair A' hA') := by
    refine oκ_eq_of_left_eq (c := Units.mk0 m hm0) (by rw [hg1, linPair_right]) ?_
    rw [linPair_left, hA'def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hsum := finrank_eig_add h2 hA2
  have hM1 : 1 ≤ Module.finrank K (eigM Am) := by
    by_contra h0
    have hbot : eigM Am = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have htop : eigP Am = ⊤ := by
      have := (isCompl_eig h2 hA2).sup_eq_top
      rwa [hbot, sup_bot_eq] at this
    have h1 : Am = 1 := eq_one_of_forall_mulVec fun v => mem_eigP.1 (htop ▸ Submodule.mem_top)
    apply hκ1
    rw [hκ]
    have : linPair A' hA' = 1 := by
      apply Subtype.ext
      apply SemidirectProduct.ext
      · exact Units.ext (by rw [linPair_left, ← hAm]; exact h1)
      · rfl
    rw [this, map_one]
  have hP1 : 1 ≤ Module.finrank K (eigP Am) := by
    by_contra h0
    have hbot : eigP Am = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have htop : eigM Am = ⊤ := by
      have := (isCompl_eig h2 hA2).sup_eq_top
      rwa [hbot, bot_sup_eq] at this
    have hneg : -Am = 1 := eq_one_of_forall_mulVec fun v => by
      rw [neg_mulVec, mem_eigM.1 (htop ▸ Submodule.mem_top), neg_neg]
    have hm1 : (-1 : GL (Fin d) K) ∈ matrixIsometries (oQ R) := by
      rw [mem_matrixIsometries_oQ h2 R hR, CatalogueBGraphForm.mem_isometryGroup]
      simp
    have hscal : linPair A' hA' = linPair (-1 : GL (Fin d) K) hm1 := by
      apply Subtype.ext
      apply SemidirectProduct.ext
      · apply Units.ext
        rw [linPair_left, linPair_left, ← hAm, Units.val_neg, Units.val_one]
        rw [← hneg, neg_neg]
      · rfl
    have hone : oκ _ (linPair (-1 : GL (Fin d) K) hm1) = oκ _ (1 : similarityPairs (oQ R)) := by
      refine oκ_eq_of_left_eq (c := (-1 : Kˣ)) rfl ?_
      apply Units.ext
      rw [linPair_left]
      change (-1 : GL (Fin d) K).val = ((GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) *
        (1 : GL (Fin d) K) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_one, Matrix.mul_one,
        Matrix.scalar_apply, Units.val_neg, Units.val_neg, Units.val_one]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    apply hκ1
    rw [hκ, hscal, hone, map_one]
  obtain ⟨hab, c, hcA, horth, hdiag, hNF, hNFc⟩ := exists_split_nf hK hR hAR hA2
  refine ClO.commute_of_frame hK hker hsurj hinj hRodd hRi hRc A' hA' hκ hab c
    (by rw [← hAm]; exact hcA) horth hdiag fun hw hker' hsurj' hinj' Ro' hR'odd hR'i hR'c => ?_
  have hJcard : (famJ hab).card = Module.finrank K (eigM Am) := card_famJ hab
  have hJccard : (famJ hab)ᶜ.card = Module.finrank K (eigP Am) := by
    rw [Finset.card_compl, Fintype.card_fin, hJcard]
    omega
  exact ClO.commute_diag_odd hK hd7 hdodd hw hker' hsurj' hinj' hR'odd hR'i hR'c (by omega)
    (by omega) (fun h3 => hNF (by omega)) (fun h3 => hNFc (by omega))

end CFSG.ComponentClassification.Foote5.OddLieCore
