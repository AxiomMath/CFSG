module

public import CFSG.ClassicalInvolution.RouteD.TWEB4V
public import CFSG.ClassicalInvolution.RouteD.TWEB4Unip
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Twin
public import CFSG.ClassicalInvolution.RouteD.GapsFrBRel

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B4

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (polarNondegOn_sup)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Frame

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem polarNondegOn_span (F : OFrame Q) : PolarNondegOn Q F.span := by
  rw [frame_span_eq]
  exact polarNondegOn_sup (polarNondegOn_hypPlane F.P) (polarNondegOn_hypPlane F.P')
    (polar_hypPlane_of_orth F.orth)

theorem normalized_span (hodd : Odd (Nat.card K)) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1) (F : OFrame Q)
    (hnorm : ∀ l ∈ F.La.range, g * l * g ∈ F.La.range) : ∀ x ∈ F.span, g x ∈ F.span := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  let F' := F.map hgO
  have hLa : ∀ A, F'.La A = g * F.La A * g := fun A => by
    rw [Frame.map_La F hgO A, hginv]
  have hrange : F'.La.range = F.La.range := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨A, rfl⟩
      rw [hLa]
      exact hnorm _ ⟨A, rfl⟩
    · rintro _ ⟨A, rfl⟩
      obtain ⟨B, hB⟩ := hnorm _ ⟨A, rfl⟩
      refine ⟨B, ?_⟩
      rw [hLa, hB]
      calc g * (g * F.La A * g) * g = (g * g) * F.La A * (g * g) := by group
        _ = F.La A := by rw [hg2]; simp
  have hi : F.La (-1) = F'.La (-1) :=
    IsFundamental.involution_unique hodd (IsFundamental.of_frame F)
      (hrange ▸ IsFundamental.of_frame F')
  intro x hx
  rw [← negSpace_La_neg_one h2] at hx ⊢
  rw [mem_negSpace_iff'] at hx ⊢
  have hgg : g (g x) = x := by simpa using LinearEquiv.congr_fun hg2 x
  have h3 : F'.La (-1) (g x) = g (F.La (-1) x) := by
    rw [hLa]
    simp only [LinearEquiv.mul_apply]
    rw [hgg]
  rw [hi, h3, hx, map_neg]

theorem eigen_planes_of_inverted (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} [Fact p.Prime] [CharP K p] {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1) (F : OFrame Q)
    (hgF : ∀ x ∈ F.span, g x ∈ F.span) {A : SL(2, K)} (hA1 : A ≠ 1) (hAp : A ^ p = 1)
    (hinv : ∀ v, g (F.La A v) = (F.La A).symm (g v)) :
    ∃ π ρ : HypPair Q, π.Orth ρ ∧ hypPlane π ⊔ hypPlane ρ = F.span ∧
      (∀ x ∈ hypPlane π, g x = -x) ∧ (∀ x ∈ hypPlane ρ, g x = x) := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨L, hL1, hL2, hLspan, hiso, hQL, hL0⟩ := exists_unipotent_data F hA1 hAp
  have hgL : ∀ v, g (L v) = -L (g v) := by
    intro v
    have h := hinv v
    rw [hL1, hL2, map_add] at h
    have h' : g v + g (L v) = g v + -L (g v) := by rw [← sub_eq_add_neg]; exact h
    exact add_left_cancel h'
  obtain ⟨⟨x, hx, hLx, hQx, hgx⟩, ⟨y, hy, hLy, hQy, hgy⟩⟩ :=
    exists_singular_eigen h2 hQ hgO hg2 hiso hQL hgL hL0
  exact exists_planes_of_singular_eigen h2 hgO hg2 (polarNondegOn_span F) F.finrank_span hgF
    (hLspan y) hgy hLy hQy (hLspan x) hgx hLx hQx

end Frame

section Spin

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal.Spin

variable {p f : ℕ} [Fact p.Prime]


theorem class_spin_b4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {𝓕 : Set (Subgroup (spinGroup (quadOdd 4 (GaloisField p f))))}
    (cq : CentralQuot (spinAction (quadOdd 4 (GaloisField p f))) 𝓕
      (fundSet (quadOdd 4 (GaloisField p f)))
      (scalars (GaloisField p f) (Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f)))
    {g₀ h : (Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f)}
    (hgO : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 4 (GaloisField p f)))
    (hg2 : g₀ * g₀ = 1)
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 4 (GaloisField p f)))
    (hh2 : h * h = 1)
    {RM RM' RJ RN₁ RN₂ : Subgroup (spinGroup (quadOdd 4 (GaloisField p f)))}
    (hRM : RM ∈ 𝓕) (hRM' : RM' ∈ 𝓕) (hRJ : RJ ∈ 𝓕) (hRN₁ : RN₁ ∈ 𝓕) (hRN₂ : RN₂ ∈ 𝓕)
    (FM : OFrame (quadOdd 4 (GaloisField p f)))
    (hFM : RM.map (spinAction (quadOdd 4 (GaloisField p f))) = FM.La.range)
    (hFM' : RM'.map (spinAction (quadOdd 4 (GaloisField p f))) = FM.swap.La.range)
    (hRJM : RJ ≠ RM) (hRJM' : RJ ≠ RM')
    (hcomm : Commutes (RM.map (spinAction (quadOdd 4 (GaloisField p f))))
      (RJ.map (spinAction (quadOdd 4 (GaloisField p f)))))
    (hfixM : ∀ l ∈ RM.map (spinAction (quadOdd 4 (GaloisField p f))), g₀ * l = l * g₀)
    (hfixN₁ : ∀ l ∈ RN₁.map (spinAction (quadOdd 4 (GaloisField p f))), g₀ * l = l * g₀)
    (hfixN₂ : ∀ l ∈ RN₂.map (spinAction (quadOdd 4 (GaloisField p f))), g₀ * l = l * g₀)
    (hnormJ : ∀ l ∈ RJ.map (spinAction (quadOdd 4 (GaloisField p f))),
      g₀ * l * g₀ ∈ RJ.map (spinAction (quadOdd 4 (GaloisField p f))))
    {x₀ : spinGroup (quadOdd 4 (GaloisField p f))} (hx₀J : x₀ ∈ RJ) (hx₀1 : x₀ ≠ 1)
    (hx₀p : x₀ ^ p = 1)
    (hx₀inv : ∀ v, g₀ (spinAction (quadOdd 4 (GaloisField p f)) x₀ v) =
      (spinAction (quadOdd 4 (GaloisField p f)) x₀).symm (g₀ v))
    (hhneg : negSpace h ≤ FM.span) (hhdim : Module.finrank (GaloisField p f) (negSpace h) = 2)
    (hhfix : ∀ x, (∀ w ∈ FM.span, polar (quadOdd 4 (GaloisField p f)) x w = 0) → h x = x)
    (hN₁h : ∀ l ∈ RN₁.map (spinAction (quadOdd 4 (GaloisField p f))), h * l = l * h)
    (hN₂h : ∀ l ∈ RN₂.map (spinAction (quadOdd 4 (GaloisField p f))), h * l = l * h)
    (hnc : ¬ Commutes (RN₁.map (spinAction (quadOdd 4 (GaloisField p f))))
      (RN₂.map (spinAction (quadOdd 4 (GaloisField p f)))))
    (hne : RN₁.map (spinAction (quadOdd 4 (GaloisField p f))) ≠
      RN₂.map (spinAction (quadOdd 4 (GaloisField p f)))) :
    ∃ (x' : spinGroup (quadOdd 4 (GaloisField p f))) (ε : GaloisField p f),
      (ε = 1 ∨ ε = -1) ∧
      RJ = ((rootSL2 (oddFrame 4 (GaloisField p f)).toHypFrame 0 1 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x').toMonoidHom) ∧
      ∀ y, polar (quadOdd 4 (GaloisField p f)) (spinAction (quadOdd 4 (GaloisField p f)) x'
          ((oddFrame 4 (GaloisField p f)).toHypFrame.vec ⟨0, by omega⟩ true)) y = 0 →
        polar (quadOdd 4 (GaloisField p f)) (spinAction (quadOdd 4 (GaloisField p f)) x'
          ((oddFrame 4 (GaloisField p f)).toHypFrame.vec ⟨0, by omega⟩ false)) y = 0 →
        g₀ y = ε • y := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have hQ : (quadOdd 4 (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd 4 _ h2)
  have hQ' : (polarBilin (quadOdd 4 (GaloisField p f))).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd 4 _ h2
  have hdim9 : Module.finrank (GaloisField p f) (Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f) = 9 := by
    rw [finrank_odd]
  obtain ⟨iJ, hiJ⟩ := cq.map_mem _ hRJ
  obtain ⟨FJ, hFJ, hiJe⟩ := hiJ
  have hiMf : IsFundamental (quadOdd 4 (GaloisField p f))
      (RM.map (spinAction (quadOdd 4 (GaloisField p f)))) (FM.La (-1)) := by
    rw [hFM]
    exact IsFundamental.of_frame FM
  have hiJf : IsFundamental (quadOdd 4 (GaloisField p f))
      (RJ.map (spinAction (quadOdd 4 (GaloisField p f)))) (FJ.La (-1)) := by
    rw [hFJ]
    exact IsFundamental.of_frame FJ
  obtain ⟨εM, hεM, hgM⟩ := sign_of_commute h2 hiMf hgO hg2 hfixM
  have hgM' : ∀ x ∈ FM.span, g₀ x = εM • x := fun x hx =>
    hgM x (by rw [negSpace_La_neg_one h2]; exact hx)
  have hJspan : ∀ x ∈ FJ.span, g₀ x ∈ FJ.span :=
    normalized_span hodd hgO hg2 FJ (by rw [← hFJ]; exact hnormJ)
  have hx₀mem : spinAction (quadOdd 4 (GaloisField p f)) x₀ ∈ FJ.La.range := by
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
  have hMJ : ∀ x ∈ FM.span, ∀ y ∈ FJ.span, polar (quadOdd 4 (GaloisField p f)) x y = 0 := by
    rcases orth_or_twin hodd hiMf hiJf hcomm with ho | ht
    · intro x hx y hy
      exact ho x (by rw [negSpace_La_neg_one h2]; exact hx)
        y (by rw [negSpace_La_neg_one h2]; exact hy)
    · exfalso
      have ht' : FJ.La (-1) = FM.La (-1) := by
        first
        | exact ht.symm
        | exact ht
      rcases Frame.La_range_eq_or_eq_swap h2 ht' with h | h
      · exact hRJM (cq.map_inj hRJ hRM (by rw [hFJ, h, hFM]))
      · exact hRJM' (cq.map_inj hRJ hRM' (by rw [hFJ, h, hFM']))
  obtain ⟨π', ρ', hπρ', hsup', hgπ', hgρ'⟩ : ∃ π' ρ' : HypPair (quadOdd 4 (GaloisField p f)),
      π'.Orth ρ' ∧ hypPlane π' ⊔ hypPlane ρ' = FJ.span ∧
      (∀ x ∈ hypPlane π', g₀ x = (-εM) • x) ∧ (∀ x ∈ hypPlane ρ', g₀ x = εM • x) := by
    rcases hεM with rfl | rfl
    · exact ⟨π, ρ, hπρ, hsup, fun x hx => by rw [hgπ x hx]; simp, fun x hx => by
        rw [hgρ x hx]; simp⟩
    · exact ⟨ρ, π, hπρ.symm, by rw [sup_comm]; exact hsup, fun x hx => by
        rw [hgρ x hx]; simp, fun x hx => by rw [hgπ x hx]; simp⟩
  obtain ⟨s₁, hs₁⟩ := cq.map_mem _ hRN₁
  obtain ⟨s₂, hs₂⟩ := cq.map_mem _ hRN₂
  obtain ⟨ε₁, hε₁, hg₁⟩ := sign_of_commute h2 hs₁ hgO hg2 hfixN₁
  obtain ⟨ε₂, hε₂, hg₂⟩ := sign_of_commute h2 hs₂ hgO hg2 hfixN₂
  have hhN : ∀ {L : Subgroup ((Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f))}
      {s : (Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
        (Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f)},
      IsFundamental (quadOdd 4 (GaloisField p f)) L s → (∀ l ∈ L, h * l = l * h) →
      ∀ x ∈ negSpace s, h x = x := by
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
  have hne12 : negSpace s₁ ≠ negSpace s₂ := negSpace_ne_of_not_commutes hodd hs₁ hs₂ hne hnc
  have hperp := eq_smul_of_perp_b4 h2 hdim9 hgO hg2 (WM := FM.span) (WJ := FJ.span)
    FM.finrank_span (polarNondegOn_span FM) hMJ hεM hgM' π' ρ' hsup' hgπ' hgρ' hhneg hhdim hhfix
    hW₁ hW₂ hne12 hε₁ hε₂ hg₁ hg₂ (hhN hs₁ hN₁h) (hhN hs₂ hN₂h)
  set F₀ := (oddFrame 4 (GaloisField p f)).toHypFrame with hF₀
  have hspanG : FJ.span = (mkFrame π' ρ' hπρ').span := by
    rw [frame_span_eq (mkFrame π' ρ' hπρ')]
    exact hsup'.symm
  have hii : FJ.La (-1) = (mkFrame π' ρ' hπρ').La (-1) :=
    Frame.La_neg_one_eq_of_span_eq hspanG
  obtain ⟨P1, hP1o, hP1pl, hFJP1⟩ : ∃ (P1 : HypPair (quadOdd 4 (GaloisField p f)))
      (h : π'.Orth (swapPair P1)), hypPlane P1 = hypPlane ρ' ∧
      FJ.La.range = (mkFrame π' (swapPair P1) h).La.range := by
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
  have horth : ∀ (A B : HypPair (quadOdd 4 (GaloisField p f))), hypPlane A ≤ FJ.span →
      hypPlane B ≤ FM.span → A.Orth B := fun A B hA hB =>
    orth_of_polar_hypPlane fun x hx y hy => by
      rw [polar_comm]
      exact hMJ y (hB hy) x (hA hx)
  have o01 : π'.Orth P1 := orth_swapPair hP1o
  have o02 : π'.Orth FM.P := horth _ _ hπle hFMP
  have o03 : π'.Orth FM.P' := horth _ _ hπle hFMP'
  have o12 : P1.Orth FM.P := horth _ _ hP1le hFMP
  have o13 : P1.Orth FM.P' := horth _ _ hP1le hFMP'
  have o23 : FM.P.Orth FM.P' := FM.orth
  let Pn : ℕ → HypPair (quadOdd 4 (GaloisField p f)) := fun k =>
    if k = 0 then π' else if k = 1 then P1 else if k = 2 then FM.P else FM.P'
  have hPn : ∀ a b, a < 4 → b < 4 → a ≠ b → (Pn a).Orth (Pn b) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first
      | exact absurd rfl hab
      | simp [Pn, o01, o01.symm, o02, o02.symm, o03, o03.symm, o12, o12.symm, o13, o13.symm, o23,
          o23.symm]
  let P : Fin 4 → HypPair (quadOdd 4 (GaloisField p f)) := fun i => Pn i.val
  have hPo : ∀ i j : Fin 4, i ≠ j → (P i).Orth (P j) := fun i j hij =>
    hPn i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h))
  obtain ⟨x', hx1, -⟩ := exists_spin_family hodd hQ F₀ hPo (⟨3, by omega⟩ : Fin 4)
  have hP0 : π'.e = spinAction (quadOdd 4 (GaloisField p f)) x' (F₀.vec ⟨0, by omega⟩ true) ∧
      π'.f = spinAction (quadOdd 4 (GaloisField p f)) x' (F₀.vec ⟨0, by omega⟩ false) := by
    have := hx1 ⟨0, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    have e : P ⟨0, by omega⟩ = π' := by simp [P, Pn]
    rw [e] at this
    exact this
  have hP1 : P1.e = spinAction (quadOdd 4 (GaloisField p f)) x' (F₀.vec ⟨1, by omega⟩ true) ∧
      P1.f = spinAction (quadOdd 4 (GaloisField p f)) x' (F₀.vec ⟨1, by omega⟩ false) := by
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

end CFSG.ClassicalInvolution.RouteD.TWE.B4
