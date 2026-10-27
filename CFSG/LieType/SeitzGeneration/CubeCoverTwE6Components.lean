module

public import CFSG.LieType.SeitzGeneration.CubeCoverTwE6NotAll24
public import CFSG.LieType.SeitzGeneration.TwE6CoverShapeOdd
public import CFSG.LieType.SeitzGeneration.TwE6CoverShapeEven
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLineRGen

public section

namespace CFSG.LieType.SeitzGeneration.CubeCoverE6

open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh6
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

section LineComponentsAt

theorem twE6LineComponentsAt_of_line {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hcube : TwE6Cube K σ q E)
    (hq8 : q ≠ 8) {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E) (hf1 : f ≠ 1)
    (hty : ∀ s : twistedE6RootGroup K σ, f = MulAut.conj s → twE6FixDim K σ s ≠ 24) :
    TwE6LineComponentsAt K σ E f := by
  obtain ⟨h, hh, -, hdim⟩ := twE6MatFixDim_mem_of_mem twE6Order3Dim_holds K σ q
    hcube.char_ne_three hcube.frob hcube.card_field hcube.three_dvd hcube.ne_two
    hcube.elemAbelian hcube.le_inndiag hf hf1
  have hLD : ∀ d, twE6MatFixDim K σ h = d → TwE6LineDim K σ f d := fun d hd => ⟨h, hh, hd⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdim
  rcases hdim with h24 | h28 | h30 | h36 | h46
  · have hout : f ∉ twistedE6Inn K σ := by
      rintro ⟨s, hs⟩
      have hq2 : 2 ≤ q := by
        have := Nat.le_of_dvd (by omega) hcube.three_dvd
        omega
      have hfd := twE6MatFixDim_of_inner K σ q hcube.frob hcube.card_field hq2 s h
        (hh.trans hs.symm)
      exact hty s hs.symm (hfd ▸ h24)
    exact twE6LineComponentsAt_a2out hcube hf hf1 hout (hLD 24 h24)
  · exact twE6LineComponentsAt_of_conn twE6ConnCentre twE6ConnShapeEven hcube hf hf1
      ⟨h, hh, by rw [h28]; simp, fun h8 => absurd h8 hq8⟩
  · exact twE6LineComponentsAt_of_d4 d4t2OuterThm_holds hcube hf hf1 (hLD 30 h30)
  · exact twE6LineComponentsAt_of_conn twE6ConnCentre twE6ConnShapeEven hcube hf hf1
      ⟨h, hh, by rw [h36]; simp, fun _ => by rw [h36]; norm_num⟩
  · exact twE6LineComponentsAt_of_conn twE6ConnCentre twE6ConnShapeEven hcube hf hf1
      ⟨h, hh, by rw [h46]; simp, fun _ => by rw [h46]; norm_num⟩

end LineComponentsAt

section CoverTypeOdd

theorem twE6CoverComponentType_of_odd (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hK2 : ringChar K ≠ 2) (hσ : ∀ c, σ c = c ^ q)
    (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q) {f : MulAut (twistedE6RootGroup K σ)}
    (hf3 : f ^ 3 = 1) {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))) :
    TwE6CoverComponentType J := by
  rcases twE6ComponentCoverShape_of_odd K σ q hK3 hK2 hσ hKq hq2 hf3 hJ with
    ⟨d, e, hd3, hD2, hex, hL⟩ | hno | hcop
  · exact Or.inl ⟨d, e, hd3, hD2, fun _ => ⟨hex, hL⟩⟩
  · exact Or.inr (Or.inl hno)
  · exact Or.inr (Or.inr hcop)

end CoverTypeOdd

section CoverComponents

theorem twE6CoverComponents_holds : TwE6CoverComponents := by
  intro k _ _ σ q E hcube hq8 f hf hf1 hty J hJ
  refine ⟨(twE6LineComponentsAt_of_line hcube hq8 hf hf1 hty J hJ).1, ?_⟩
  by_cases h2 : ringChar k = 2
  · exact twE6ComponentCoverShape_of_even hcube h2 hq8 hf hf1 hty hJ
  · have hq2 : 2 ≤ q := by
      have := Nat.le_of_dvd (by omega) hcube.three_dvd
      omega
    exact twE6CoverComponentType_of_odd k σ q hcube.char_ne_three h2 hcube.frob
      hcube.card_field hq2 (hcube.elemAbelian.2 f hf) hJ

end CoverComponents

section LineRGen

theorem twE6LineRGen_holds : TwE6LineRGen :=
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSLineR.twE6LineRGen_holds

end LineRGen

section DiagNotAll24

theorem coverTwE6DiagNotAll24_holds : CoverTwE6DiagNotAll24 :=
  coverTwE6DiagNotAll24_of twE6CoverComponents_holds twE6LineRGen_holds

end DiagNotAll24

end CFSG.LieType.SeitzGeneration.CubeCoverE6

end
