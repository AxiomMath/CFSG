module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeCentre
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeShape
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineGroup
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentSU
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqRat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.LieType.Seitz

namespace KSNotAll24

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Seitz CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Outer


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ} {h : twistedE6InndiagGL K σ}

namespace TwE6LineLang

variable (D : TwE6LineLang K σ q h)

theorem sq_eq : D.S.D.q = q := D.hSq.trans D.hqe.symm

theorem three_dvd_sq (hq3 : 3 ∣ q + 1) : 3 ∣ D.S.D.q + 1 := by
  rw [D.sq_eq]
  exact hq3

theorem conj_mem_inner_of_mem_Gamma (hd : rootDiagUnit Tag.E6 D.a ∈ D.S.Γ) :
    twistedE6InndiagConj K σ h ∈ twistedE6Inn K σ := by
  rw [← D.hrange] at hd
  obtain ⟨c, hc⟩ := hd
  refine ⟨c, MulEquiv.ext fun x => ?_⟩
  apply D.hinj
  rw [D.hconj, ← hc]
  simp [MulAut.conj_apply]

theorem ncard_kernelRoots_a2out (hdim : twE6MatFixDim K σ h = 24) :
    (kernelRoots (rootCharHom D.a)).ncard = 18 := by
  have := D.hker
  rw [hdim] at this
  omega

theorem orbit_three_of_outer (hdim : twE6MatFixDim K σ h = 24) (hq3 : 3 ∣ q + 1) (hq2 : q ≠ 2)
    (hout : twistedE6InndiagConj K σ h ∉ twistedE6Inn K σ) :
    (∀ i : KernelComponent (rootCharHom D.a),
      (componentRoots (rootCharHom D.a) i).ncard = 6) ∧
    ∀ i : KernelComponent (rootCharHom D.a),
      componentOrbitLength D.S.ρ (componentRoots (rootCharHom D.a) i) = 3 ∧
        rationalRoots D.S.ρ (rootCharHom D.a) i = kernelRoots (rootCharHom D.a) := by
  classical
  obtain ⟨c, hc, hc6⟩ :=
    kernel_classes_of_ncard_eighteen D.hL3 D.hap (D.ncard_kernelRoots_a2out hdim)
  have hi6 : ∀ i : KernelComponent (rootCharHom D.a),
      (componentRoots (rootCharHom D.a) i).ncard = 6 := by
    intro i
    obtain ⟨k, rfl⟩ := hc.2 i
    exact hc6 k
  refine ⟨hi6, ?_⟩
  rcases orbit_dichotomy D.S D.hT hc with ⟨i, hi⟩ | hall
  · exfalso
    obtain ⟨ψ, σ', π, hψ, hΨ, hπ⟩ := exists_unitary_frame_of_odd_orbit D.S D.hL3 D.hT D.hap
      D.h1 i (hi6 i) (by rw [hi]) (D.three_dvd_sq hq3)
    have hmem := rootDiagUnit_mem_rationalComponent_of_stable D.S D.hT D.hap D.h1 i (hi6 i) hψ hΨ
      π hπ D.hℓ D.hchar D.he D.hSq hi (D.three_dvd_sq hq3) (by rw [D.sq_eq]; exact hq2)
    have hΓ : rootDiagUnit Tag.E6 D.a ∈ D.S.Γ :=
      ((langSubnormal_of_mem_torus D.S D.hT i).1.trans inf_le_left) hmem
    exact hout (D.conj_mem_inner_of_mem_Gamma hΓ)
  · exact hall

theorem nonempty_kernelComponent_a2out (hdim : twE6MatFixDim K σ h = 24) :
    Nonempty (KernelComponent (rootCharHom D.a)) := by
  obtain ⟨α₀, hα₀⟩ : (kernelRoots (rootCharHom D.a)).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [D.ncard_kernelRoots_a2out hdim]; omega)
  exact ⟨⟦⟨α₀, hα₀⟩⟧⟩

theorem rationalComponent_a2out (hdim : twE6MatFixDim K σ h = 24)
    (hq3 : 3 ∣ q + 1) (hq2 : q ≠ 2)
    (hout : twistedE6InndiagConj K σ h ∉ twistedE6Inn K σ) (i : KernelComponent (rootCharHom D.a)) :
    Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) = ⊥ ∧
      CFSG.IsQuasisimple ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ∧
      StatedClassicalModel (↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ⧸
        Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)) .PSU 3
        (ringChar K) (D.e * 3) := by
  classical
  obtain ⟨hi6, hall⟩ := D.orbit_three_of_outer hdim hq3 hq2 hout
  have h3q := D.three_dvd_sq hq3
  have hs3 := (hall i).1
  obtain ⟨ψ, σ', π, hψ, hΨ, hπ⟩ := exists_unitary_frame_of_odd_orbit D.S D.hL3 D.hT D.hap D.h1 i
    (hi6 i) (by rw [hs3]) h3q
  have hZ := center_rationalComponent_eq_bot_of_orbit_three D.S D.hT D.hap i (hi6 i) hψ hΨ π hπ
    D.hℓ D.hchar D.he D.hSq hs3 h3q
  have hQ : ((3 : ℕ), ringChar K ^ (D.e * componentOrbitLength D.S.ρ
      (componentRoots (rootCharHom D.a) i))) ≠ (3, 2) := by
    intro hc
    have h2 : ringChar K ^ (D.e * componentOrbitLength D.S.ρ
        (componentRoots (rootCharHom D.a) i)) = 2 := (Prod.mk.inj hc).2
    rw [hs3] at h2
    have h3 : ringChar K ^ 3 ≤ ringChar K ^ (D.e * 3) :=
      Nat.pow_le_pow_right D.hℓ.pos (by have := D.he; omega)
    have h4 : 2 ^ 3 ≤ ringChar K ^ 3 := Nat.pow_le_pow_left D.hℓ.two_le 3
    omega
  have hmodel := KSExact.rationalComponent_suN_model D.S D.hT i (le_refl 3) hψ hΨ π hπ D.hℓ
    D.hchar D.he D.hSq hQ
  have hqs := KSFourU.rationalComponent_suN_quasisimple D.S D.hT i (le_refl 3) hψ hΨ π hπ D.hℓ
    D.hchar D.he D.hSq hQ
  rw [hs3] at hmodel
  exact ⟨hZ, hqs, hmodel⟩

theorem twE6ComponentType_rationalComponent (hdim : twE6MatFixDim K σ h = 24)
    (hq3 : 3 ∣ q + 1) (hq2 : q ≠ 2) (hK3 : ringChar K ≠ 3)
    (hout : twistedE6InndiagConj K σ h ∉ twistedE6Inn K σ) (i : KernelComponent (rootCharHom D.a)) :
    TwE6ComponentType (rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) := by
  classical
  obtain ⟨hZ, -, hmodel⟩ := D.rationalComponent_a2out hdim hq3 hq2 hout i
  obtain ⟨q', hv, hq'p, -, ⟨e⟩⟩ :=
    KSExact.exists_twistedA_of_statedClassicalModel_PSU (m := 2) hmodel
  refine Or.inl ⟨?_, ⟨.twistedA 2 q', hv⟩, e, ?_, ?_⟩
  · rw [hZ, Subgroup.card_bot]
    omega
  · change 3 ≠ (TauCeti.LieTypeIndex.twistedA 2 q').characteristic
    rw [TauCeti.LieTypeIndex.characteristic_twistedA, hq'p]
    exact fun h3 => hK3 h3.symm
  · simp [AGLEmbeddingD2.IsD2SeitzException]

include D in
theorem eq_of_isComponentOf_a2out (hdim : twE6MatFixDim K σ h = 24) (hq3 : 3 ∣ q + 1)
    (hq2 : q ≠ 2) (hout : twistedE6InndiagConj K σ h ∉ twistedE6Inn K σ)
    {J J' : Subgroup (twistedE6RootGroup K σ)}
    (hJ : IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))))
    (hJ' : IsComponentOf J' (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))) :
    J' = J := by
  obtain ⟨-, hall⟩ := D.orbit_three_of_outer hdim hq3 hq2 hout
  obtain ⟨i, -, hi⟩ := D.exists_rationalComponent hJ
  obtain ⟨j, -, hj⟩ := D.exists_rationalComponent hJ'
  exact D.eq_of_map_eq (hj.trans ((rationalComponent_eq_of_rationalRoots_eq D.S
    ((hall j).2.trans (hall i).2.symm)).trans hi.symm))

end TwE6LineLang

end Outer

section Main


theorem twE6LineComponentsAt_a2out {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E) (hf1 : f ≠ 1)
    (hfo : f ∉ twistedE6Inn K σ) (hd : TwE6LineDim K σ f 24) : TwE6LineComponentsAt K σ E f := by
  classical
  obtain ⟨h, rfl, -, -, hdim, ⟨D⟩⟩ := exists_twE6LineLang_of_cube hE hf hf1 hd
  intro J hJ
  refine ⟨fun g hg => ?_, ?_⟩
  · have hcomm : twistedE6InndiagConj K σ h * g = g * twistedE6InndiagConj K σ h :=
      congrArg Subtype.val (hE.elemAbelian.1.is_comm.comm ⟨_, hf⟩ ⟨g, hg⟩)
    exact D.eq_of_isComponentOf_a2out hdim hE.three_dvd hE.ne_two hfo hJ
      (isComponentOf_map_of_commute _ g hcomm hJ)
  · obtain ⟨i, -, hi⟩ := D.exists_rationalComponent hJ
    exact twE6ComponentType_of_map_injective D.ι D.hinj
      (hi ▸ D.twE6ComponentType_rationalComponent hdim hE.three_dvd hE.ne_two
        hE.char_ne_three hfo i)

end Main

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
