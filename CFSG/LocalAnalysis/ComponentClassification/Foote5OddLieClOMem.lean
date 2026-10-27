module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOGenCases
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOOddInner

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)

variable {K : Type} [Field K] {d : ℕ} [Finite K]

section Congr

variable {S T : Type} [Group S] [Group T]

theorem ClO.commute_of_congr_P (e : S ≃* T) {i : MulAut S} (P : MulAut T → Prop)
    {R : Subgroup (MulAut S)} (hP : ∀ r ∈ R, P (MulAut.congr e r))
    (h : ∀ R' : Subgroup (MulAut T), Odd (Nat.card R') →
      (∀ r ∈ R', r * MulAut.congr e i = MulAut.congr e i * r) →
      (∀ s : T, MulAut.congr e i s = s → Odd (orderOf s) → ∀ r ∈ R',
        MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R') → (∀ r ∈ R', P r) →
      ∀ r₁ ∈ R', ∀ r₂ ∈ R', r₁ * r₂ = r₂ * r₁)
    (hRodd : Odd (Nat.card R)) (hRi : ∀ r ∈ R, r * i = i * r)
    (hRc : ∀ s : S, i s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  set φ : MulAut S →* MulAut T := (MulAut.congr e).toMonoidHom with hφ
  have hinj : Function.Injective φ := (MulAut.congr e).injective
  have hφapp : ∀ x, φ x = MulAut.congr e x := fun x => rfl
  set R' := R.map φ with hR'
  have hR'odd : Odd (Nat.card R') := by
    rw [hR', Subgroup.card_map_of_injective hinj]
    exact hRodd
  have hR'i : ∀ r ∈ R', r * MulAut.congr e i = MulAut.congr e i * r := by
    rintro _ ⟨r, hr, rfl⟩
    rw [hφapp, ← map_mul, ← map_mul, hRi r hr]
  have hR'c : ∀ s : T, MulAut.congr e i s = s → Odd (orderOf s) → ∀ r ∈ R',
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R' := by
    rintro s hs hso _ ⟨r, hr, rfl⟩
    have hs' : i (e.symm s) = e.symm s := by
      have := congrArg e.symm hs
      simpa [MulAut.congr_apply] using this
    have hso' : Odd (orderOf (e.symm s)) := by rwa [MulEquiv.orderOf_eq]
    refine ⟨_, hRc _ hs' hso' r hr, ?_⟩
    rw [hφapp, map_mul, map_mul, map_inv, congr_conj, MulEquiv.apply_symm_apply, hφapp]
  have hR'P : ∀ r ∈ R', P r := by
    rintro _ ⟨r, hr, rfl⟩
    exact hP r hr
  intro r₁ h₁ r₂ h₂
  apply hinj
  have := h R' hR'odd hR'i hR'c hR'P (φ r₁) ⟨r₁, h₁, rfl⟩ (φ r₂) ⟨r₂, h₂, rfl⟩
  rw [map_mul, map_mul]
  exact this

end Congr

omit [Finite K] in
theorem ClO.commute_of_transport_mem {Q Q' : QuadraticForm K (Fin d → K)} (S : GL (Fin d) K)
    (ν : Kˣ) (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v)
    {g : similarityPairs Q} {Ro : Subgroup (MulAut (StatedProj (matrixDerived Q)))}
    (hRodd : Odd (Nat.card Ro)) (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj : ∀ y ∈ Ro, ∃ g' : similarityPairs Q, y = oκ _ g')
    (h : ∀ Ro' : Subgroup (MulAut (StatedProj (matrixDerived Q'))), Odd (Nat.card Ro') →
      (∀ y ∈ Ro', y * oκ _ (transPair S ν hS g) = oκ _ (transPair S ν hS g) * y) →
      (∀ s, oκ _ (transPair S ν hS g) s = s → Odd (orderOf s) → ∀ y ∈ Ro',
        MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro') →
      (∀ y ∈ Ro', ∃ g' : similarityPairs Q', y = oκ _ g') →
      ∀ r₁ ∈ Ro', ∀ r₂ ∈ Ro', r₁ * r₂ = r₂ * r₁) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  refine ClO.commute_of_congr_P (oTransport S ν hS)
    (fun y => ∃ g' : similarityPairs Q', y = oκ _ g') (fun r hr => ?_)
    (fun R' h1 h2 h3 h4 => ?_) hRodd hRi hRc
  · obtain ⟨g', rfl⟩ := hsurj r hr
    exact ⟨transPair S ν hS g', oTransport_kappa S ν hS g'⟩
  · rw [oTransport_kappa] at h2 h3
    exact h R' h1 h2 h3 h4

omit [Finite K] in
theorem ClO.commute_of_frame_mem (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hker : OKer (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)}
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj : ∀ y ∈ Ro, ∃ g' : similarityPairs (oQ R), y = oκ _ g')
    (A'' : GL (Fin d) K) (hA'' : A'' ∈ matrixIsometries (oQ R))
    (hκ'' : oκ _ g = oκ _ (linPair A'' hA'')) {a b : ℕ} (hab : a + b = d)
    (c : Fin a ⊕ Fin b → Fin d → K)
    (hcA : ∀ x, (A'' : Matrix (Fin d) (Fin d) K) *ᵥ c x =
      (if x.isLeft then (-1 : K) else 1) • c x)
    (horth : ∀ x y, x ≠ y → c x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c y = 0)
    (hdiag : ∀ x, c x ⬝ᵥ (R : Matrix (Fin d) (Fin d) K) *ᵥ c x ≠ 0)
    (hcase : ∀ (hw : ∀ l, famW (R : Matrix (Fin d) (Fin d) K) hab c l ≠ 0),
      OKer (oQ (diagGL hw)) →
      Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
        MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))) →
      ∀ Ro' : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))),
        Odd (Nat.card Ro') →
        (∀ y ∈ Ro', y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw (famJ hab)) =
          oκ _ (sgnPair (Ring.two_ne_zero hK) hw (famJ hab)) * y) →
        (∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw (famJ hab)) s = s →
          Odd (orderOf s) → ∀ y ∈ Ro', MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro') →
        (∀ y ∈ Ro', ∃ g' : similarityPairs (oQ (diagGL hw)), y = oκ _ g') →
        ∀ r₁ ∈ Ro', ∀ r₂ ∈ Ro', r₁ * r₂ = r₂ * r₁) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨hw, S, hS, heq⟩ := exists_transport_of_family h2 hA'' hab c hcA horth hdiag
  have hcg : oκ _ (transPair S 1 hS g) = oκ _ (sgnPair (Ring.two_ne_zero hK) hw (famJ hab)) := by
    rw [← oTransport_kappa, hκ'', oTransport_kappa, heq]
  refine ClO.commute_of_transport_mem S 1 hS hRodd hRi hRc hsurj
    (fun R' hR'odd hR'i hR'c hR's => ?_)
  rw [hcg] at hR'i hR'c
  exact hcase hw (hker.transport S 1 hS)
    (ClO.conj_injective_of_mulEquiv (oTransport S 1 hS) hinj) R' hR'odd hR'i hR'c hR's

theorem ClO.commute_diag_mem (hK : ringChar K ≠ 2) (hd7 : 7 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * y)
    (hRc : ∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj' : ∀ y ∈ Ro, ∃ g : similarityPairs (oQ (diagGL hw)), y = oκ _ g)
    (hJ1 : 1 ≤ J.card) (hJc1 : 1 ≤ Jᶜ.card) (hNF : 3 ≤ J.card → BlockNF w J)
    (hNFc : 3 ≤ Jᶜ.card → BlockNF w Jᶜ) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hd := card_compl_add J
  have hplane : ∀ I : Finset (Fin d), I.card = 2 → BlockOK K w Iᶜ →
      (∀ y ∈ Ro, y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw I) =
        oκ _ (sgnPair (Ring.two_ne_zero hK) hw I) * y) →
      (∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw I) s = s → Odd (orderOf s) →
        ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro) →
      ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
    intro I hI2 hIc hRi' hRc'
    have hI := card_compl_add I
    have hcore := fun y (hy : y ∈ Ro) => ClO.split_two_core hK hw hker hinj hRodd hRi' hRc'
      hsurj' (by omega) hIc hy
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
  have h1 := ClO.split_eq_one_of_nf_gen hK hd7 hw hker hinj hRodd hRi hRc hsurj' hJ1 hJc1 hJ2
    hJc2 hNF hNFc
  intro r₁ h₁ r₂ h₂
  rw [h1 r₁ h₁, h1 r₂ h₂]

theorem ClO.commute_split_mem (hK : ringChar K ≠ 2) (hd7 : 7 ≤ d)
    {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hi : orderOf (oκ _ g) = 2)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj : ∀ y ∈ Ro, ∃ g' : similarityPairs (oQ R), y = oκ _ g')
    {A' : GL (Fin d) K} (hA' : A' ∈ matrixIsometries (oQ R))
    (hκ : oκ _ g = oκ _ (linPair A' hA'))
    (hA'R : (A' : Matrix (Fin d) (Fin d) K)ᵀ * R * A' = R)
    (hA'2 : (A' : Matrix (Fin d) (Fin d) K) * A' = 1) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  have hκ1 : oκ (oQ R) g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hi
    exact absurd hi (by norm_num)
  obtain ⟨Am, hAm⟩ : ∃ Am : Matrix (Fin d) (Fin d) K, Am = A' := ⟨_, rfl⟩
  have hAR : Amᵀ * Rm * Am = Rm := by rw [hAm]; exact hA'R
  have hA2 : Am * Am = 1 := by rw [hAm]; exact hA'2
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
  refine ClO.commute_of_frame_mem hK hker hinj hRodd hRi hRc hsurj A' hA' hκ hab c
    (by rw [← hAm]; exact hcA) horth hdiag fun hw hker' hinj' Ro' hR'odd hR'i hR'c hR's => ?_
  have hJcard : (famJ hab).card = Module.finrank K (eigM Am) := card_famJ hab
  have hJccard : (famJ hab)ᶜ.card = Module.finrank K (eigP Am) := by
    rw [Finset.card_compl, Fintype.card_fin, hJcard]
    omega
  exact ClO.commute_diag_mem hK hd7 hw hker' hinj' hR'odd hR'i hR'c hR's (by omega)
    (by omega) (fun h3 => hNF (by omega)) (fun h3 => hNFc (by omega))

end CFSG.ComponentClassification.Foote5.OddLieCore
