module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4Untw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcOmegaAll
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.RootTwD0

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces LargeEvenMarking)
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (exists_langSetup_frobRoot_twE6_D0)

section Twisted


theorem l154td4_langPicture_twE6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω} (hSn : S.Normal)
    (hqS : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hQ : catalogIs (PSimple p S) l154ExcTwE6) (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hxy : x * y = y * x) (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S)
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) (hcm : ¬ CentMod p S x) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L 2)
      (SL : LangSetup Tag.E6 L p) (R : FrobRoot SL.D p) (e : ℕ) (a : Fin Tag.E6.rank → Lˣ)
      (i : KernelComponent (rootCharHom a)),
      1 ≤ e ∧ R.q0 = 2 ^ e ∧ L154RootD0 SL R ∧
      rootDiagUnit Tag.E6 a ∈ SL.D.torus ∧ (∀ k, a k ^ p = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      R.step0 (rootDiagUnit Tag.E6 a) = rootDiagUnit Tag.E6 a ∧
      CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
      (∀ z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i,
        R.step0 z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
      (IsTD4 p J → catalogIs (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))
          (onLie fun | .trialityD4 _ => True | _ => False)) := by
  classical
  have hxN := l154_mem_normalizer_of_normal hSn x
  obtain ⟨K, _, _, e, k, σ, θ, φx, φy, h, T, hchar, he, hK, hσ, hT, hh, hhp, hfix, -, hφx, hφy,
    hindx, hindy⟩ := excTwE6_marking_data hp hp2 hQ hxp hyp hxy hInn hF
  haveI := hchar
  haveI : Finite ↥(twistedE6RootGroup K σ) := Finite.of_equiv _ θ.toEquiv
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hcm (l154_centMod_of_conj_one hqS hxN θ φx hφx hindx)
  obtain ⟨SL, R, a, ι, -, hq0, hTa, hap, ha1, hfa, hι, hrange, hβ, hφ, hD0⟩ :=
    exists_langSetup_frobRoot_twE6_D0 hp hp2 he hK σ hσ T hT φx φy h hh hφx hφy hhp hh1 hfix
  obtain ⟨i, hqi, hstab, -, hTD⟩ := l154_lang_of_model hp hSp hxp hxN hJ hJy θ φx φy hindx
    hindy SL R ι hι hrange hβ hφ hTa hap ha1
  exact ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance, SL, R, e, a, i, he, hq0,
    hD0, hTa, hap, ha1, hfa, hqi, hstab, hTD⟩

theorem l154OmegaTD4_excTwE6_D0 (hTD4 : L154LangTD4ResD0) : L154OmegaTD4 l154ExcTwE6 := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp _ hQ hxp hyp hxy hInnx hF hJ hJy
  rintro ⟨rfl, hT⟩
  by_cases hcm : CentMod 3 S x
  · exact (l154_of_centMod hqS hSp hcm hF hJ).2 ⟨rfl, hT⟩
  obtain ⟨L, _, _, _, SL, R, e, a, i, he, hq0, hD0, hTa, hap, ha1, hfa, hqi, hstab, hTD⟩ :=
    l154td4_langPicture_twE6 hp hp2 hSn hqS hSp hQ hxp hyp hxy hInnx hF hJ hJy hcm
  exact hTD4 Tag.E6 L 3 SL R e a i hD0 he hq0 hTa hap ha1 hfa hqi hstab (hTD hT)

theorem l154TD4On_excTwE6_D0 (hTD4 : L154LangTD4ResD0) : L154TD4On l154ExcTwE6 :=
  l154TD4On_of_omegaTD4 (l154OmegaTD4_excTwE6_D0 hTD4)

theorem l154OmegaTD4_exc_D0 (hTD4 : L154LangTD4ResD0) (hRee : L154OmegaTD4 l154ExcRee) :
    L154OmegaTD4 l154Exc :=
  l154OmegaTD4_mono l154_exc_cover_all
    (l154OmegaTD4_or l154OmegaTD4_tits (l154OmegaTD4_or l154OmegaTD4_suz
      (l154OmegaTD4_or l154OmegaTD4_two (l154OmegaTD4_or (l154OmegaTD4_excUntw_D0 hTD4)
        (l154OmegaTD4_or (l154OmegaTD4_excTwE6_D0 hTD4)
          (l154OmegaTD4_or l154OmegaTD4_excTriD4 hRee))))))

theorem l154TD4On_excRest_D0 (hTD4 : L154LangTD4ResD0) (hRee : L154TD4On l154ExcRee) :
    L154TD4On l154ExcRest :=
  l154TD4On_mono l154_excRest_cover
    (l154TD4On_or (l154TD4On_excUntw_D0 hTD4)
      (l154TD4On_or (l154TD4On_excTwE6_D0 hTD4) (l154TD4On_or l154TD4On_excTriD4 hRee)))

theorem l154OmegaTD4_exc_of_class (hC : L154TD4Class) (hRee : L154OmegaTD4 l154ExcRee) :
    L154OmegaTD4 l154Exc :=
  l154OmegaTD4_exc_D0 (l154LangTD4ResD0_of_class hC) hRee

theorem l154TD4On_excRest_of_class (hC : L154TD4Class) (hRee : L154TD4On l154ExcRee) :
    L154TD4On l154ExcRest :=
  l154TD4On_excRest_D0 (l154LangTD4ResD0_of_class hC) hRee

end Twisted

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
