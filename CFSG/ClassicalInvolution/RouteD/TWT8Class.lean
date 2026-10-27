module

public import CFSG.ClassicalInvolution.RouteD.TWT8Cls
public import CFSG.ClassicalInvolution.RouteD.TWT8V
public import CFSG.ClassicalInvolution.RouteD.TWEB4Class
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusOrth

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.RouteD.TWE.B4 (normalized_span eigen_planes_of_inverted
  polarNondegOn_span mem_negSpace_iff' mem_posSpace_iff' eq_self_of_perp_plane)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Class

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem negSpace_eq_plane_td5 (h2 : (2 : K) ≠ 0) (hd : Module.finrank K V = 10)
    {g h : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hh2 : h * h = 1) {WM WJ : Submodule K V} (hWM : Module.finrank K WM = 4)
    (hWMnd : PolarNondegOn Q WM) (hMJ : ∀ x ∈ WM, ∀ y ∈ WJ, polar Q x y = 0)
    (hgM : ∀ x ∈ WM, g x = x) (π ρ : HypPair Q) (hsup : hypPlane π ⊔ hypPlane ρ = WJ)
    (hgπ : ∀ x ∈ hypPlane π, g x = -x) (hgρ : ∀ x ∈ hypPlane ρ, g x = x)
    (hhneg : negSpace h ≤ WM) (hhdim : Module.finrank K (negSpace h) = 2)
    {W₁ W₂ : Submodule K V} (hW₁ : Module.finrank K W₁ = 4) (hW₂ : Module.finrank K W₂ = 4)
    (hF12 : Module.finrank K ↥(W₁ ⊓ W₂) = 2)
    (hnorth : ¬ ∀ x ∈ W₁, ∀ y ∈ W₂, polar Q x y = 0) {ε₁ ε₂ : K} (hε₁ : ε₁ = 1 ∨ ε₁ = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hg₁ : ∀ x ∈ W₁, g x = ε₁ • x) (hg₂ : ∀ x ∈ W₂, g x = ε₂ • x)
    (hh₁ : ∀ x ∈ W₁, h x = x) (hh₂ : ∀ x ∈ W₂, h x = x) :
    negSpace g = hypPlane π := by
  classical
  have hcompl := isCompl_pos_neg h2 hg2
  have hπle : hypPlane π ≤ negSpace g := fun x hx => mem_negSpace_iff'.mpr (hgπ x hx)
  have hρle : hypPlane ρ ≤ posSpace g := fun x hx => mem_posSpace_iff'.mpr (hgρ x hx)
  have hWMle : WM ≤ posSpace g := fun x hx => mem_posSpace_iff'.mpr (hgM x hx)
  have hρJ : hypPlane ρ ≤ WJ := hsup ▸ le_sup_right
  have hdisj : Disjoint WM (hypPlane ρ) := by
    rw [Submodule.disjoint_def]
    intro x hxM hxρ
    exact hWMnd x hxM fun w hw => by rw [polar_comm]; exact hMJ w hw x (hρJ hxρ)
  have hdimρ : Module.finrank K ↥(WM ⊔ hypPlane ρ) = 6 := by
    rw [Models.OrthogonalPairs.Frame.finrank_sup_of_disjoint hdisj, hWM, finrank_hypPlane]
  have hpos6 : 6 ≤ Module.finrank K (posSpace g) := by
    have := Submodule.finrank_mono (sup_le hWMle hρle)
    omega
  have hneg2 : 2 ≤ Module.finrank K (negSpace g) := by
    have := Submodule.finrank_mono hπle
    rw [finrank_hypPlane] at this
    exact this
  have hsign : ∀ (Wi : Submodule K V) (εi : K), (εi = 1 ∨ εi = -1) → (∀ x ∈ Wi, g x = εi • x) →
      Wi ≤ posSpace g ∨ Wi ≤ negSpace g := by
    intro Wi εi hεi hgi
    rcases hεi with rfl | rfl
    · exact Or.inl fun x hx => mem_posSpace_iff'.mpr (by rw [hgi x hx, one_smul])
    · exact Or.inr fun x hx => mem_negSpace_iff'.mpr (by rw [hgi x hx, neg_smul, one_smul])
  have hcls := finrank_negSpace_eq_two h2 hd hgO hg2 hh2 hhdim (hhneg.trans hWMle) hpos6 hneg2 hW₁
    hW₂ (hsign W₁ ε₁ hε₁ hg₁) (hsign W₂ ε₂ hε₂ hg₂)
    (fun x hx => mem_posSpace_iff'.mpr (hh₁ x hx)) (fun x hx => mem_posSpace_iff'.mpr (hh₂ x hx))
    hF12 hnorth
  exact (Submodule.eq_of_le_of_finrank_eq hπle (by rw [finrank_hypPlane, hcls])).symm

theorem eq_smul_of_perp_td5 (h2 : (2 : K) ≠ 0) (hd : Module.finrank K V = 10)
    {g h : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hh2 : h * h = 1) {WM WJ : Submodule K V} (hWM : Module.finrank K WM = 4)
    (hWMnd : PolarNondegOn Q WM) (hMJ : ∀ x ∈ WM, ∀ y ∈ WJ, polar Q x y = 0) {ε : K}
    (hε : ε = 1 ∨ ε = -1) (hgM : ∀ x ∈ WM, g x = ε • x) (π ρ : HypPair Q)
    (hsup : hypPlane π ⊔ hypPlane ρ = WJ) (hgπ : ∀ x ∈ hypPlane π, g x = (-ε) • x)
    (hgρ : ∀ x ∈ hypPlane ρ, g x = ε • x) (hhneg : negSpace h ≤ WM)
    (hhdim : Module.finrank K (negSpace h) = 2) {W₁ W₂ : Submodule K V}
    (hW₁ : Module.finrank K W₁ = 4) (hW₂ : Module.finrank K W₂ = 4)
    (hF12 : Module.finrank K ↥(W₁ ⊓ W₂) = 2)
    (hnorth : ¬ ∀ x ∈ W₁, ∀ y ∈ W₂, polar Q x y = 0) {ε₁ ε₂ : K} (hε₁ : ε₁ = 1 ∨ ε₁ = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hg₁ : ∀ x ∈ W₁, g x = ε₁ • x) (hg₂ : ∀ x ∈ W₂, g x = ε₂ • x)
    (hh₁ : ∀ x ∈ W₁, h x = x) (hh₂ : ∀ x ∈ W₂, h x = x) :
    ∀ y, y ∈ π.perp → g y = ε • y := by
  rcases hε with rfl | rfl
  · have hneg := negSpace_eq_plane_td5 h2 hd hgO hg2 hh2 hWM hWMnd hMJ (fun x hx => by
      simpa using hgM x hx) π ρ hsup (fun x hx => by simpa using hgπ x hx)
      (fun x hx => by simpa using hgρ x hx) hhneg hhdim hW₁ hW₂ hF12 hnorth hε₁ hε₂ hg₁ hg₂ hh₁
      hh₂
    intro y hy
    simpa using eq_self_of_perp_plane h2 hgO hg2 π hneg hy
  · let g' : V ≃ₗ[K] V := g.trans (LinearEquiv.neg K)
    have hg'x : ∀ x, g' x = -(g x) := fun x => rfl
    have hg'2 : g' * g' = 1 := by
      refine LinearEquiv.ext fun x => ?_
      have := LinearEquiv.congr_fun hg2 x
      simp only [LinearEquiv.mul_apply, hg'x, map_neg, neg_neg] at this ⊢
      simpa using this
    have hg'O : g' ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
      rw [hg'x, QuadraticMap.map_neg]
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO x
    have hneg := negSpace_eq_plane_td5 (g := g') h2 hd hg'O hg'2 hh2 hWM hWMnd hMJ (fun x hx => by
      rw [hg'x, hgM x hx]; simp) π ρ hsup (fun x hx => by
        rw [hg'x, hgπ x hx]; simp) (fun x hx => by
        rw [hg'x, hgρ x hx]; simp) hhneg hhdim hW₁ hW₂ hF12 hnorth (ε₁ := -ε₁) (ε₂ := -ε₂)
      (by rcases hε₁ with rfl | rfl <;> simp) (by rcases hε₂ with rfl | rfl <;> simp)
      (fun x hx => by rw [hg'x, hg₁ x hx]; simp) (fun x hx => by rw [hg'x, hg₂ x hx]; simp) hh₁ hh₂
    intro y hy
    have := eq_self_of_perp_plane h2 hg'O hg'2 π hneg hy
    rw [hg'x] at this
    have h3 : g y = -y := by
      have := congrArg Neg.neg this
      simpa using this
    rw [h3]
    simp

end Class

section Spin

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal (minusCoeffs minusCoeffs_irr)

variable {p f : ℕ} [Fact p.Prime]


theorem class_spin_td5 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {𝓕 : Set (Subgroup (spinGroup (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)))}
    (cq : CentralQuot (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) 𝓕 (fundSet (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) (scalars (GaloisField p f) (Vm 5 (GaloisField p f))))
    {g₀ h : Vm 5 (GaloisField p f) ≃ₗ[GaloisField p f] Vm 5 (GaloisField p f)}
    (hgO : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2))
    (hg2 : g₀ * g₀ = 1)
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2))
    (hh2 : h * h = 1)
    {RM RM' RJ RN₁ RN₂ : Subgroup (spinGroup (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))}
    (hRM : RM ∈ 𝓕) (hRM' : RM' ∈ 𝓕) (hRJ : RJ ∈ 𝓕) (hRN₁ : RN₁ ∈ 𝓕) (hRN₂ : RN₂ ∈ 𝓕)
    (FM : OFrame (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
    (hFM : RM.map (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) = FM.La.range)
    (hFM' : RM'.map (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) = FM.swap.La.range)
    (hRJM : RJ ≠ RM) (hRJM' : RJ ≠ RM')
    (hcomm : Commutes (RM.map (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))) (RJ.map (spinAction (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2))))
    (hfixM : ∀ l ∈ RM.map (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)), g₀ * l = l * g₀)
    (hfixN₁ : ∀ l ∈ RN₁.map (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)), g₀ * l = l * g₀)
    (hfixN₂ : ∀ l ∈ RN₂.map (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)), g₀ * l = l * g₀)
    (hnormJ : ∀ l ∈ RJ.map (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)), g₀ * l * g₀ ∈ RJ.map (spinAction (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)))
    {x₀ : spinGroup (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)}
    (hx₀J : x₀ ∈ RJ) (hx₀1 : x₀ ≠ 1) (hx₀p : x₀ ^ p = 1)
    (hx₀inv : ∀ v, g₀ (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) x₀ v) = (spinAction (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2) x₀).symm (g₀ v))
    (hhneg : negSpace h ≤ FM.span) (hhdim : Module.finrank (GaloisField p f) (negSpace h) = 2)
    (hN₁h : ∀ l ∈ RN₁.map (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)), h * l = l * h)
    (hN₂h : ∀ l ∈ RN₂.map (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)), h * l = l * h)
    (hbr : BridgeOmega (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
      (RN₁.map (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2))) (RN₂.map (spinAction (quadMinus 5 (GaloisField p f)
        (minusCoeffs p f).1 (minusCoeffs p f).2)))) :
    ∃ (x' : spinGroup (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
      (ε : GaloisField p f), (ε = 1 ∨ ε = -1) ∧
      RJ = ((rootSL2 (minusFrame 5 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame 0 1
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x').toMonoidHom) ∧
      ∀ y, polar (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
          (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) x'
          ((minusFrame 5 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.vec ⟨0, by omega⟩
            true)) y = 0 →
        polar (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
          (spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) x'
          ((minusFrame 5 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.vec ⟨0, by omega⟩
            false)) y = 0 →
        g₀ y = ε • y := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf0
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have hirr := minusCoeffs_irr p f
  have hQ : (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite 5 (GaloisField p f) hirr)
  have hQ' : (polarBilin (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 5 (GaloisField p f) hirr
  have hdim10 : Module.finrank (GaloisField p f) (Vm 5 (GaloisField p f)) = 10 := by
    rw [finrank_minus p f 5 (by omega)]
  obtain ⟨iJ, hiJ⟩ := cq.map_mem _ hRJ
  obtain ⟨FJ, hFJ, hiJe⟩ := hiJ
  have hiMf : IsFundamental (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) (RM.map (spinAction (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2))) (FM.La (-1)) := by
    rw [hFM]
    exact IsFundamental.of_frame FM
  have hiJf : IsFundamental (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) (RJ.map (spinAction (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2))) (FJ.La (-1)) := by
    rw [hFJ]
    exact IsFundamental.of_frame FJ
  obtain ⟨εM, hεM, hgM⟩ := sign_of_commute h2 hiMf hgO hg2 hfixM
  have hgM' : ∀ x ∈ FM.span, g₀ x = εM • x := fun x hx =>
    hgM x (by rw [negSpace_La_neg_one h2]; exact hx)
  have hJspan : ∀ x ∈ FJ.span, g₀ x ∈ FJ.span :=
    normalized_span hodd hgO hg2 FJ (by rw [← hFJ]; exact hnormJ)
  have hx₀mem : spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) x₀ ∈ FJ.La.range := by
    rw [← hFJ]
    exact ⟨x₀, hx₀J, rfl⟩
  obtain ⟨A, hA⟩ := hx₀mem
  have hAp : A ^ p = 1 := by
    apply FJ.La_injective
    rw [map_pow, hA, ← map_pow, hx₀p, map_one, map_one]
  have hA1 : A ≠ 1 := by
    rintro rfl
    rw [map_one] at hA
    exact hx₀1 (cq.inj RJ hRJ x₀ hx₀J hA.symm)
  have hinv : ∀ v, g₀ (FJ.La A v) = (FJ.La A).symm (g₀ v) := by
    intro v
    rw [hA]
    exact hx₀inv v
  obtain ⟨π, ρ, hπρ, hsup, hgπ, hgρ⟩ := eigen_planes_of_inverted hodd hQ' (p := p) hgO hg2 FJ
    hJspan hA1 hAp hinv
  have hMJ : ∀ x ∈ FM.span, ∀ y ∈ FJ.span, polar (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2) x y = 0 := by
    rcases orth_or_twin hodd hiMf hiJf hcomm with ho | ht
    · intro x hx y hy
      exact ho x (by rw [negSpace_La_neg_one h2]; exact hx)
        y (by rw [negSpace_La_neg_one h2]; exact hy)
    · exfalso
      have ht' : FJ.La (-1) = FM.La (-1) := ht
      rcases Frame.La_range_eq_or_eq_swap h2 ht' with h | h
      · exact hRJM (cq.map_inj hRJ hRM (by rw [hFJ, h, hFM]))
      · exact hRJM' (cq.map_inj hRJ hRM' (by rw [hFJ, h, hFM']))
  obtain ⟨π', ρ', hπρ', hsup', hgπ', hgρ'⟩ : ∃ π' ρ' : HypPair (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2), π'.Orth ρ' ∧
      hypPlane π' ⊔ hypPlane ρ' = FJ.span ∧
      (∀ x ∈ hypPlane π', g₀ x = (-εM) • x) ∧ (∀ x ∈ hypPlane ρ', g₀ x = εM • x) := by
    rcases hεM with rfl | rfl
    · exact ⟨π, ρ, hπρ, hsup, fun x hx => by rw [hgπ x hx]; simp, fun x hx => by
        rw [hgρ x hx]; simp⟩
    · exact ⟨ρ, π, hπρ.symm, by rw [sup_comm]; exact hsup, fun x hx => by
        rw [hgρ x hx]; simp, fun x hx => by rw [hgπ x hx]; simp⟩
  obtain ⟨hS₁, hS₂, hSne, hSnc, hSnorm⟩ := hbr
  obtain ⟨s₁, hs₁⟩ := cq.map_mem _ hRN₁
  obtain ⟨s₂, hs₂⟩ := cq.map_mem _ hRN₂
  obtain ⟨ε₁, hε₁, hg₁⟩ := sign_of_commute h2 hs₁ hgO hg2 hfixN₁
  obtain ⟨ε₂, hε₂, hg₂⟩ := sign_of_commute h2 hs₂ hgO hg2 hfixN₂
  have hhN : ∀ {L : Subgroup (Vm 5 (GaloisField p f) ≃ₗ[GaloisField p f] Vm 5 (GaloisField p f))}
      {s : Vm 5 (GaloisField p f) ≃ₗ[GaloisField p f] Vm 5 (GaloisField p f)},
      IsFundamental (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) L s →
      (∀ l ∈ L, h * l = l * h) → ∀ x ∈ negSpace s, h x = x := by
    intro L s hL hc
    obtain ⟨ε', hε', he⟩ := sign_of_commute h2 hL hhO hh2 hc
    rcases hε' with rfl | rfl
    · intro x hx
      simpa using he x hx
    · exfalso
      have hle : negSpace s ≤ negSpace h := fun x hx =>
        mem_negSpace_iff'.mpr (by rw [he x hx]; simp)
      have h4 := Submodule.finrank_mono hle
      rw [finrank_negSpace hodd hL, hhdim] at h4
      omega
  have hW₁ : Module.finrank (GaloisField p f) (negSpace s₁) = 4 := finrank_negSpace hodd hs₁
  have hW₂ : Module.finrank (GaloisField p f) (negSpace s₂) = 4 := finrank_negSpace hodd hs₂
  have hsN : s₂ ∈ Subgroup.normalizer ((RN₁.map (spinAction (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)) : Subgroup _) : Set _) := hSnorm s₂ hs₂
  have hc12 : s₁ * s₂ = s₂ * s₁ := by
    have hmem := (Subgroup.mem_normalizer_iff.mp hsN s₁).mp (hs₁.mem)
    have h1 : s₂ * s₁ * s₂⁻¹ = s₁ := by
      refine IsFundamental.eq_of_orderOf_eq_two hodd hs₁ hmem ?_
      refine orderOf_eq_prime ?_ ?_
      · have hs1 : s₁ * s₁ = 1 := hs₁.mul_self
        calc (s₂ * s₁ * s₂⁻¹) ^ 2 = (s₂ * s₁ * s₂⁻¹) * (s₂ * s₁ * s₂⁻¹) := pow_two _
          _ = s₂ * (s₁ * s₁) * s₂⁻¹ := by group
          _ = 1 := by rw [hs1]; group
      · intro h
        have : s₁ = 1 := by
          have := congrArg (fun w => s₂⁻¹ * w * s₂) h
          simpa [mul_assoc] using this
        exact hs₁.ne_one hodd this
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hC : s₂ ∉ Subgroup.centralizer ((RN₁.map (spinAction (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)) : Subgroup _) : Set _) := fun hcen =>
    hSnc ((IsFundamental.commute_iff hodd hs₁ hs₂ hc12 hSne).mpr hcen)
  have hF12 : Module.finrank (GaloisField p f) ↥(negSpace s₁ ⊓ negSpace s₂) = 2 :=
    finrank_inf_negSpace hodd hs₁ hs₂ hc12 hsN hC
  have hnd₁ : PolarNondegOn (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) (negSpace s₁) := by
    obtain ⟨F₁N, -, rfl⟩ := hs₁
    rw [negSpace_La_neg_one h2]
    exact polarNondegOn_span F₁N
  have hnorth : ¬ ∀ x ∈ negSpace s₁, ∀ y ∈ negSpace s₂, polar (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2) x y = 0 := by
    intro hall
    have hbot : negSpace s₁ ⊓ negSpace s₂ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hx' := Submodule.mem_inf.mp hx
      refine hnd₁ x hx'.1 fun y hy => ?_
      rw [polar_comm]
      exact hall y hy x hx'.2
    rw [hbot, finrank_bot] at hF12
    omega
  have hperp := eq_smul_of_perp_td5 h2 hdim10 hgO hg2 hh2 (WM := FM.span) (WJ := FJ.span)
    FM.finrank_span (polarNondegOn_span FM) hMJ hεM hgM' π' ρ' hsup' hgπ' hgρ' hhneg hhdim
    hW₁ hW₂ hF12 hnorth hε₁ hε₂ hg₁ hg₂ (fun x hx => hhN hs₁ hN₁h x hx)
    (fun x hx => hhN hs₂ hN₂h x hx)
  set F₀ : HypFrame (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
    (5 - 1) := (minusFrame 5 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame with hF₀
  have hspanG : FJ.span = (mkFrame π' ρ' hπρ').span := by
    rw [frame_span_eq (mkFrame π' ρ' hπρ')]
    exact hsup'.symm
  have hii : FJ.La (-1) = (mkFrame π' ρ' hπρ').La (-1) :=
    Frame.La_neg_one_eq_of_span_eq hspanG
  obtain ⟨P1, hP1o, hP1pl, hFJP1⟩ : ∃ (P1 : HypPair (quadMinus 5 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)) (h : π'.Orth (swapPair P1)),
      hypPlane P1 = hypPlane ρ' ∧ FJ.La.range = (mkFrame π' (swapPair P1) h).La.range := by
    rcases Frame.La_range_eq_or_eq_swap h2 hii with hA | hB
    · exact ⟨swapPair ρ', hπρ', by rw [hypPlane_swapPair], hA⟩
    · exact ⟨ρ', orth_swapPair hπρ', rfl, hB⟩
  have hπle : hypPlane π' ≤ FJ.span := by
    rw [← hsup']
    exact le_sup_left
  have hP1le : hypPlane P1 ≤ FJ.span := by
    rw [hP1pl, ← hsup']
    exact le_sup_right
  have hFMP : hypPlane FM.P ≤ FM.span := by
    rw [frame_span_eq]
    exact le_sup_left
  have hFMP' : hypPlane FM.P' ≤ FM.span := by
    rw [frame_span_eq]
    exact le_sup_right
  have horth : ∀ (A B : HypPair (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)), hypPlane A ≤ FJ.span → hypPlane B ≤ FM.span → A.Orth B :=
    fun A B hA hB => orth_of_polar_hypPlane fun x hx y hy => by
      rw [polar_comm]
      exact hMJ y (hB hy) x (hA hx)
  have o01 : π'.Orth P1 := orth_swapPair hP1o
  have o02 : π'.Orth FM.P := horth _ _ hπle hFMP
  have o03 : π'.Orth FM.P' := horth _ _ hπle hFMP'
  have o12 : P1.Orth FM.P := horth _ _ hP1le hFMP
  have o13 : P1.Orth FM.P' := horth _ _ hP1le hFMP'
  have o23 : FM.P.Orth FM.P' := FM.orth
  let Pn : ℕ → HypPair (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) :=
    fun k => if k = 0 then π' else if k = 1 then P1 else if k = 2 then FM.P else FM.P'
  have hPn : ∀ a b, a < 4 → b < 4 → a ≠ b → (Pn a).Orth (Pn b) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first
      | exact absurd rfl hab
      | simp [Pn, o01, o01.symm, o02, o02.symm, o03, o03.symm, o12, o12.symm, o13, o13.symm, o23,
          o23.symm]
  let P : Fin (5 - 1) → HypPair (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) := fun i => Pn i.val
  have hPo : ∀ i j : Fin (5 - 1), i ≠ j → (P i).Orth (P j) := fun i j hij =>
    hPn i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h))
  obtain ⟨x', hx1, -⟩ := exists_spin_family hodd hQ F₀ hPo (⟨3, by omega⟩ : Fin (5 - 1))
  have hP0 : π'.e = spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) x' (F₀.vec ⟨0, by omega⟩ true) ∧
      π'.f = spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) x' (F₀.vec ⟨0, by omega⟩ false) := by
    have := hx1 ⟨0, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    have e : P ⟨0, by omega⟩ = π' := by simp [P, Pn]
    rw [e] at this
    exact this
  have hP1 : P1.e = spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) x' (F₀.vec ⟨1, by omega⟩ true) ∧
      P1.f = spinAction (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) x' (F₀.vec ⟨1, by omega⟩ false) := by
    have := hx1 ⟨1, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    have e : P ⟨1, by omega⟩ = P1 := by simp [P, Pn]
    rw [e] at this
    exact this
  have hrange := La_range_eq_of_pairs F₀ (a := 0) (b := 1) (by omega) (by omega) (by omega) true
    false x' hP1o hP0 ⟨hP1.2, hP1.1⟩
  have hq4 : 4 ≤ p ^ f := by omega
  have hRJeq : RJ = ((rootSL2 F₀ 0 1 (by omega) (by omega) (by omega) true false).map
      (MulAut.conj x').toMonoidHom) :=
    cq.map_inj hRJ (rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ true false x')
      (by rw [hFJ, hFJP1, hrange])
  refine ⟨x', εM, hεM, hRJeq, fun y h1 h2' => hperp y ?_⟩
  rw [← hP0.1] at h1
  rw [← hP0.2] at h2'
  exact HypPair.mem_perp.mpr ⟨h1, h2'⟩

end Spin

end CFSG.ClassicalInvolution.RouteD.TWT8
