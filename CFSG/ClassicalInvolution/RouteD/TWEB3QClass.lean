module

public import CFSG.ClassicalInvolution.RouteD.TWEB3QDeg
public import CFSG.ClassicalInvolution.RouteD.TWEB6Fixed

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.RouteD.TWE.B4
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (polarNondegOn_sup)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Spin

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal.Spin

variable {p f : ℕ} [Fact p.Prime]


theorem class_spin_b3_det_one (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {𝓕 : Set (Subgroup (spinGroup (quadOdd 3 (GaloisField p f))))}
    (cq : CentralQuot (spinAction (quadOdd 3 (GaloisField p f))) 𝓕
      (fundSet (quadOdd 3 (GaloisField p f)))
      (scalars (GaloisField p f) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f)))
    {g₀ : (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f)}
    (hgO : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)))
    (hg2 : g₀ * g₀ = 1) (hdet : LinearEquiv.det g₀ = 1)
    {RN : Subgroup (spinGroup (quadOdd 3 (GaloisField p f)))} (hRN : RN ∈ 𝓕)
    (FM : OFrame (quadOdd 3 (GaloisField p f))) (hgJ : ∀ x ∈ FM.span, g₀ x = x)
    (hnormN : ∀ l ∈ RN.map (spinAction (quadOdd 3 (GaloisField p f))),
      g₀ * l * g₀ ∈ RN.map (spinAction (quadOdd 3 (GaloisField p f))))
    {x₀ : spinGroup (quadOdd 3 (GaloisField p f))} (hx₀N : x₀ ∈ RN) (hx₀1 : x₀ ≠ 1)
    (hx₀p : x₀ ^ p = 1)
    (hx₀inv : ∀ v, g₀ (spinAction (quadOdd 3 (GaloisField p f)) x₀ v) =
      (spinAction (quadOdd 3 (GaloisField p f)) x₀).symm (g₀ v)) :
    ∃ x' : spinGroup (quadOdd 3 (GaloisField p f)),
      RN = ((rootSL2 (oddFrame 3 (GaloisField p f)).toHypFrame 0 1 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x').toMonoidHom) ∧
      ∀ y, polar (quadOdd 3 (GaloisField p f)) (spinAction (quadOdd 3 (GaloisField p f)) x'
          ((oddFrame 3 (GaloisField p f)).toHypFrame.vec ⟨0, by omega⟩ true)) y = 0 →
        polar (quadOdd 3 (GaloisField p f)) (spinAction (quadOdd 3 (GaloisField p f)) x'
          ((oddFrame 3 (GaloisField p f)).toHypFrame.vec ⟨0, by omega⟩ false)) y = 0 →
        g₀ y = y := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have hQ : (quadOdd 3 (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd 3 _ h2)
  have hQ' : (polarBilin (quadOdd 3 (GaloisField p f))).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd 3 _ h2
  have hdim7 : Module.finrank (GaloisField p f) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) = 7 := by
    rw [finrank_odd]
  obtain ⟨iN, hiN⟩ := cq.map_mem _ hRN
  obtain ⟨FN, hFN, hiNe⟩ := hiN
  have hNspan : ∀ x ∈ FN.span, g₀ x ∈ FN.span :=
    normalized_span hodd hgO hg2 FN (by rw [← hFN]; exact hnormN)
  have hx₀mem : spinAction (quadOdd 3 (GaloisField p f)) x₀ ∈ FN.La.range := by
    rw [← hFN]
    exact ⟨x₀, hx₀N, rfl⟩
  obtain ⟨A, hA⟩ := hx₀mem
  have hAp : A ^ p = 1 := by
    apply FN.La_injective
    rw [map_pow, hA, ← map_pow, hx₀p, map_one, map_one]
  have hA1 : A ≠ 1 := by
    rintro rfl
    rw [map_one] at hA
    exact hx₀1 (cq.inj RN hRN x₀ hx₀N hA.symm)
  have hinv : ∀ v, g₀ (FN.La A v) = (FN.La A).symm (g₀ v) := by
    intro v
    rw [hA]
    exact hx₀inv v
  obtain ⟨π, ρ, hπρ, hsup, -, hperp⟩ := class_b3_model_det hodd hQ' hdim7 hgO hg2 hdet FM FN
    hgJ hNspan hA1 hAp hinv
  set F₀ := (oddFrame 3 (GaloisField p f)).toHypFrame with hF₀
  have hspanG : FN.span = (mkFrame π ρ hπρ).span := by
    rw [frame_span_eq (mkFrame π ρ hπρ)]
    exact hsup.symm
  have hii : FN.La (-1) = (mkFrame π ρ hπρ).La (-1) :=
    Frame.La_neg_one_eq_of_span_eq hspanG
  obtain ⟨P1, hP1o, hP1pl, hFNP1⟩ : ∃ (P1 : HypPair (quadOdd 3 (GaloisField p f)))
      (h : π.Orth (swapPair P1)), hypPlane P1 = hypPlane ρ ∧
      FN.La.range = (mkFrame π (swapPair P1) h).La.range := by
    rcases Frame.La_range_eq_or_eq_swap h2 hii with hA | hB
    · exact ⟨swapPair ρ, hπρ, by rw [hypPlane_swapPair], hA⟩
    · exact ⟨ρ, orth_swapPair hπρ, rfl, hB⟩
  have o01 : π.Orth P1 := orth_swapPair hP1o
  let p₀ : ℕ → HypPair (quadOdd 3 (GaloisField p f)) := fun k => if k = 0 then π else P1
  have ho₀ : ∀ a b, a < 2 → b < 2 → a ≠ b → (p₀ a).Orth (p₀ b) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;> simp_all [p₀, o01.symm]
  obtain ⟨p', hp', ho'⟩ := exists_orth_ext hodd hQ' p₀ 2 ho₀ 1 (by omega)
  have hp'0 : p' 0 = π := by rw [hp' 0 (by omega)]; simp [p₀]
  have hp'1 : p' 1 = P1 := by rw [hp' 1 (by omega)]; simp [p₀]
  have o02 : π.Orth (p' 2) := by
    rw [← hp'0]; exact ho' 0 2 (by omega) (by omega) (by omega)
  have o12 : P1.Orth (p' 2) := by
    rw [← hp'1]; exact ho' 1 2 (by omega) (by omega) (by omega)
  let Pn : ℕ → HypPair (quadOdd 3 (GaloisField p f)) := fun k =>
    if k = 0 then π else if k = 1 then P1 else p' 2
  have hPn : ∀ a b, a < 3 → b < 3 → a ≠ b → (Pn a).Orth (Pn b) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first
      | exact absurd rfl hab
      | simp [Pn, o01, o01.symm, o02, o02.symm, o12, o12.symm]
  let P : Fin 3 → HypPair (quadOdd 3 (GaloisField p f)) := fun i => Pn i.val
  have hPo : ∀ i j : Fin 3, i ≠ j → (P i).Orth (P j) := fun i j hij =>
    hPn i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h))
  obtain ⟨x', hx1, -⟩ := exists_spin_family hodd hQ F₀ hPo (⟨2, by omega⟩ : Fin 3)
  have hP0 : π.e = spinAction (quadOdd 3 (GaloisField p f)) x' (F₀.vec ⟨0, by omega⟩ true) ∧
      π.f = spinAction (quadOdd 3 (GaloisField p f)) x' (F₀.vec ⟨0, by omega⟩ false) := by
    have := hx1 ⟨0, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    have e : P ⟨0, by omega⟩ = π := by simp [P, Pn]
    rw [e] at this
    exact this
  have hP1 : P1.e = spinAction (quadOdd 3 (GaloisField p f)) x' (F₀.vec ⟨1, by omega⟩ true) ∧
      P1.f = spinAction (quadOdd 3 (GaloisField p f)) x' (F₀.vec ⟨1, by omega⟩ false) := by
    have := hx1 ⟨1, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    have e : P ⟨1, by omega⟩ = P1 := by simp [P, Pn]
    rw [e] at this
    exact this
  have hrange := La_range_eq_of_pairs F₀ (a := 0) (b := 1) (by omega) (by omega) (by omega) true
    false x' hP1o hP0 ⟨hP1.2, hP1.1⟩
  have hq4 : 4 ≤ p ^ f := by omega
  have hRNeq : RN = ((rootSL2 F₀ 0 1 (by omega) (by omega) (by omega) true false).map
      (MulAut.conj x').toMonoidHom) :=
    cq.map_inj hRN (rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ true false x')
      (by rw [hFN, hFNP1, hrange])
  refine ⟨x', hRNeq, fun y h1 h2' => hperp y ?_⟩
  rw [← hP0.1] at h1
  rw [← hP0.2] at h2'
  exact HypPair.mem_perp.mpr ⟨h1, h2'⟩

theorem class_spin_b3_det (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {𝓕 : Set (Subgroup (spinGroup (quadOdd 3 (GaloisField p f))))}
    (cq : CentralQuot (spinAction (quadOdd 3 (GaloisField p f))) 𝓕
      (fundSet (quadOdd 3 (GaloisField p f)))
      (scalars (GaloisField p f) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f)))
    {g₀ : (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f)}
    (hgO : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)))
    (hg2 : g₀ * g₀ = 1) {ε : GaloisField p f} (hε : ε = 1 ∨ ε = -1)
    (hdet : ((LinearEquiv.det g₀ : (GaloisField p f)ˣ) : GaloisField p f) = ε)
    {RN : Subgroup (spinGroup (quadOdd 3 (GaloisField p f)))} (hRN : RN ∈ 𝓕)
    (FM : OFrame (quadOdd 3 (GaloisField p f))) (hgJ : ∀ x ∈ FM.span, g₀ x = ε • x)
    (hnormN : ∀ l ∈ RN.map (spinAction (quadOdd 3 (GaloisField p f))),
      g₀ * l * g₀ ∈ RN.map (spinAction (quadOdd 3 (GaloisField p f))))
    {x₀ : spinGroup (quadOdd 3 (GaloisField p f))} (hx₀N : x₀ ∈ RN) (hx₀1 : x₀ ≠ 1)
    (hx₀p : x₀ ^ p = 1)
    (hx₀inv : ∀ v, g₀ (spinAction (quadOdd 3 (GaloisField p f)) x₀ v) =
      (spinAction (quadOdd 3 (GaloisField p f)) x₀).symm (g₀ v)) :
    ∃ x' : spinGroup (quadOdd 3 (GaloisField p f)),
      RN = ((rootSL2 (oddFrame 3 (GaloisField p f)).toHypFrame 0 1 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x').toMonoidHom) ∧
      ∀ y, polar (quadOdd 3 (GaloisField p f)) (spinAction (quadOdd 3 (GaloisField p f)) x'
          ((oddFrame 3 (GaloisField p f)).toHypFrame.vec ⟨0, by omega⟩ true)) y = 0 →
        polar (quadOdd 3 (GaloisField p f)) (spinAction (quadOdd 3 (GaloisField p f)) x'
          ((oddFrame 3 (GaloisField p f)).toHypFrame.vec ⟨0, by omega⟩ false)) y = 0 →
        g₀ y = ε • y := by
  classical
  rcases hε with rfl | rfl
  · obtain ⟨x', hx', hs⟩ := class_spin_b3_det_one hp2 hq cq hgO hg2
      (Units.ext (by simpa using hdet)) hRN FM (fun x hx => by simpa using hgJ x hx) hnormN hx₀N
      hx₀1 hx₀p hx₀inv
    exact ⟨x', hx', fun y h1 h2 => by simpa using hs y h1 h2⟩
  · let nM : (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
        (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) := LinearEquiv.neg (GaloisField p f)
    let g₁ : (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
        (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) := nM * g₀
    have hg₁ : ∀ v, g₁ v = -g₀ v := fun v => rfl
    have hnegO : nM ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)) :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
        show quadOdd 3 (GaloisField p f) (-v) = quadOdd 3 (GaloisField p f) v
        exact QuadraticMap.map_neg _ v
    have hg₁O : g₁ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)) :=
      Subgroup.mul_mem _ hnegO hgO
    have hg₁2 : g₁ * g₁ = 1 := by
      refine LinearEquiv.ext fun v => ?_
      have h1 : g₀ (g₀ v) = v := by simpa using LinearEquiv.congr_fun hg2 v
      show g₁ (g₁ v) = v
      rw [hg₁, hg₁, map_neg, neg_neg, h1]
    have hdet₁ : LinearEquiv.det g₁ = 1 := by
      refine Units.ext ?_
      have hneg : ((LinearEquiv.det nM : (GaloisField p f)ˣ) : GaloisField p f) = -1 := by
        rw [LinearEquiv.coe_det]
        have : (nM : (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) →ₗ[GaloisField p f]
            (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f)) =
            (-1 : GaloisField p f) • LinearMap.id :=
          LinearMap.ext fun v => by simp [nM]
        rw [this, LinearMap.det_smul, LinearMap.det_id, finrank_odd]
        norm_num
      rw [show g₁ = nM * g₀ from rfl, map_mul, Units.val_mul, hneg, hdet]
      simp
    have hgJ₁ : ∀ x ∈ FM.span, g₁ x = x := fun x hx => by
      rw [hg₁, hgJ x hx]
      simp
    have hnormN₁ : ∀ l ∈ RN.map (spinAction (quadOdd 3 (GaloisField p f))),
        g₁ * l * g₁ ∈ RN.map (spinAction (quadOdd 3 (GaloisField p f))) := by
      intro l hl
      have e : g₁ * l * g₁ = g₀ * l * g₀ := by
        refine LinearEquiv.ext fun v => ?_
        simp only [LinearEquiv.mul_apply]
        rw [hg₁, hg₁]
        simp only [map_neg, neg_neg]
      rw [e]
      exact hnormN l hl
    have hx₀inv₁ : ∀ v, g₁ (spinAction (quadOdd 3 (GaloisField p f)) x₀ v) =
        (spinAction (quadOdd 3 (GaloisField p f)) x₀).symm (g₁ v) := by
      intro v
      rw [hg₁, hg₁, hx₀inv, map_neg]
    obtain ⟨x', hx', hs⟩ := class_spin_b3_det_one hp2 hq cq hg₁O hg₁2 hdet₁ hRN FM hgJ₁ hnormN₁
      hx₀N hx₀1 hx₀p hx₀inv₁
    refine ⟨x', hx', fun y h1 h2 => ?_⟩
    have := hs y h1 h2
    rw [hg₁] at this
    rw [neg_one_smul]
    exact neg_eq_iff_eq_neg.mp this

end Spin

end CFSG.ClassicalInvolution.RouteD.TWE.B3
