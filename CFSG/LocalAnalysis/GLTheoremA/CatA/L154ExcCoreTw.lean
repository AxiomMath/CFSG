module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcDataTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.RootTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces LargeEvenMarking)
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (exists_langSetup_frobRoot_twE6
  exists_langSetup_frobRoot_triD4)

section Picture

@[expose] def L154LangPicture (p : ℕ) {Ω : Type} [Group Ω] (y : Ω) (J : Subgroup Ω) : Prop :=
  ∃ (τ : Tag) (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L 2)
    (SL : LangSetup τ L p) (R : FrobRoot SL.D p) (e : ℕ) (a : Fin τ.rank → Lˣ)
    (i : KernelComponent (rootCharHom a)),
    1 ≤ e ∧ R.q0 = 2 ^ e ∧
    rootDiagUnit τ a ∈ SL.D.torus ∧ (∀ k, a k ^ p = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
    R.step0 (rootDiagUnit τ a) = rootDiagUnit τ a ∧
    CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
    (∀ z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i,
      R.step0 z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
    (InnDiagOn p (Subgroup.zpowers y) J →
      LargeEvenMarking ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) fun _ _ _ I _ θ =>
        ∃ φ ∈ I, LargeEvenInduces θ
          (fun z z' => R.step0 (z : ModGL τ L) = (z' : ModGL τ L)) φ) ∧
    (IsTD4 p J → catalogIs (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))
        (onLie fun | .trialityD4 _ => True | _ => False))

end Picture

section Conclusions

theorem l154_nid_of_langPicture (hInn : L154LangInnRes) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Ω : Type} [Group Ω] {y : Ω} {J : Subgroup Ω} (hP : L154LangPicture p y J)
    (hInnJ : InnDiagOn p (Subgroup.zpowers y) J) : False := by
  obtain ⟨τ, L, _, _, _, SL, R, e, a, i, he, hq0, hTa, hap, ha1, hfa, hqi, hstab, hNID, -⟩ := hP
  exact l154_lang_noInnDiag hInn hp hp2 SL R he hq0 hTa hap ha1 hfa hqi hstab (hNID hInnJ)

end Conclusions

section Helpers

theorem l154_mem_normalizer_of_normal {Ω : Type} [Group Ω] {S : Subgroup Ω} (hSn : S.Normal)
    (x : Ω) : x ∈ Subgroup.normalizer (S : Set Ω) := by
  haveI := hSn
  rw [Subgroup.normalizer_eq_top S]
  exact Subgroup.mem_top x

theorem l154_centMod_of_conj_one {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω} {x : Ω}
    (hqS : CFSG.Open.IsQuasisimple ↥S) (hxN : x ∈ Subgroup.normalizer (S : Set Ω)) {M : Type}
    [Group M] {H : Subgroup M} (θ : PSimple p S ≃* ↥H) (φx : MulAut ↥H)
    (hφx : ∀ c, (φx c : M) = 1 * c * 1⁻¹) (hindx : LargeEvenInduces θ (indRel p S x) φx) :
    CentMod p S x := by
  have h1 : φx = 1 := by
    ext c
    rw [hφx c]
    simp
  exact l154_centMod_of_induces_one hqS.1 hxN θ (h1 ▸ hindx)

end Helpers

section Twisted

theorem l154_langPicture_twE6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω} (hSn : S.Normal)
    (hqS : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hQ : catalogIs (PSimple p S) l154ExcTwE6) (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hxy : x * y = y * x) (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S)
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) (hcm : ¬ CentMod p S x) :
    L154LangPicture p y J := by
  classical
  have hxN := l154_mem_normalizer_of_normal hSn x
  obtain ⟨K, _, _, e, k, σ, θ, φx, φy, h, T, hchar, he, hK, hσ, hT, hh, hhp, hfix, -, hφx, hφy,
    hindx, hindy⟩ := excTwE6_marking_data hp hp2 hQ hxp hyp hxy hInn hF
  haveI := hchar
  haveI : Finite ↥(twistedE6RootGroup K σ) := Finite.of_equiv _ θ.toEquiv
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hcm (l154_centMod_of_conj_one hqS hxN θ φx hφx hindx)
  obtain ⟨SL, R, a, ι, -, hq0, hTa, hap, ha1, hfa, hι, hrange, hβ, hφ⟩ :=
    exists_langSetup_frobRoot_twE6 hp hp2 he hK σ hσ T hT φx φy h hh hφx hφy hhp hh1 hfix
  obtain ⟨i, hqi, hstab, hNID, hTD⟩ := l154_lang_of_model hp hSp hxp hxN hJ hJy θ φx φy hindx
    hindy SL R ι hι hrange hβ hφ hTa hap ha1
  exact ⟨Tag.E6, AlgebraicClosure K, inferInstance, inferInstance, inferInstance, SL, R, e, a, i,
    he, hq0, hTa, hap, ha1, hfa, hqi, hstab, hNID, hTD⟩

theorem l154_langPicture_triD4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω]
    [Finite Ω] {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω} (hSn : S.Normal)
    (hqS : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hQ : catalogIs (PSimple p S) l154ExcTriD4) (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hxy : x * y = y * x) (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S)
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) (hcm : ¬ CentMod p S x) :
    p ≠ 3 ∧ L154LangPicture p y J := by
  classical
  have hxN := l154_mem_normalizer_of_normal hSn x
  obtain ⟨K, _, _, e, j, k, σ, θ, φx, φy, h, T, hchar, he, hjp, hK, hσ, hT, hh, hhp, hfix, -,
    hφx, hφy, hindx, hindy⟩ := excTriD4_marking_data hp hp2 hQ hxp hyp hxy hInn hF
  haveI := hchar
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv _ θ.toEquiv
  have hp3 : p ≠ 3 := by
    rintro rfl
    omega
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hcm (l154_centMod_of_conj_one hqS hxN θ φx hφx hindx)
  obtain ⟨SL, R, a, ι, -, hq0, hTa, hap, ha1, hfa, hι, hrange, hβ, hφ⟩ :=
    exists_langSetup_frobRoot_triD4 hp hp2 he hjp hK σ hσ T hT φx φy h hh hφx hφy hhp hh1 hfix
  obtain ⟨i, hqi, hstab, hNID, hTD⟩ := l154_lang_of_model hp hSp hxp hxN hJ hJy θ φx φy hindx
    hindy SL R ι hι hrange hβ hφ hTa hap ha1
  exact ⟨hp3, Tag.D4, AlgebraicClosure K, inferInstance, inferInstance, inferInstance, SL, R, e,
    a, i, he, hq0, hTa, hap, ha1, hfa, hqi, hstab, hNID, hTD⟩

theorem l154OmegaNID_excTwE6 (hInn : L154LangInnRes) : L154OmegaNID l154ExcTwE6 := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp _ hQ hxp hyp hxy hInnx hF hJ hJy
  refine ⟨hJy, fun hInnJ => ?_⟩
  by_cases hcm : CentMod p S x
  · exact (l154_of_centMod hqS hSp hcm hF hJ).1.2 hInnJ
  exact l154_nid_of_langPicture hInn hp hp2
    (l154_langPicture_twE6 hp hp2 hSn hqS hSp hQ hxp hyp hxy hInnx hF hJ hJy hcm) hInnJ

theorem l154OmegaNID_excTriD4 (hInn : L154LangInnRes) : L154OmegaNID l154ExcTriD4 := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp _ hQ hxp hyp hxy hInnx hF hJ hJy
  refine ⟨hJy, fun hInnJ => ?_⟩
  by_cases hcm : CentMod p S x
  · exact (l154_of_centMod hqS hSp hcm hF hJ).1.2 hInnJ
  exact l154_nid_of_langPicture hInn hp hp2
    (l154_langPicture_triD4 hp hp2 hSn hqS hSp hQ hxp hyp hxy hInnx hF hJ hJy hcm).2 hInnJ

theorem l154OmegaTD4_excTriD4 : L154OmegaTD4 l154ExcTriD4 := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp _ hQ hxp hyp hxy hInnx hF hJ hJy
  rintro ⟨rfl, hT⟩
  by_cases hcm : CentMod 3 S x
  · exact (l154_of_centMod hqS hSp hcm hF hJ).2 ⟨rfl, hT⟩
  exact (l154_langPicture_triD4 hp hp2 hSn hqS hSp hQ hxp hyp hxy hInnx hF hJ hJy hcm).1 rfl

theorem l154NIDOn_excTwE6 (hInn : L154LangInnRes) : L154NIDOn l154ExcTwE6 :=
  l154NIDOn_of_omegaNID (l154OmegaNID_excTwE6 hInn)

theorem l154NIDOn_excTriD4 (hInn : L154LangInnRes) : L154NIDOn l154ExcTriD4 :=
  l154NIDOn_of_omegaNID (l154OmegaNID_excTriD4 hInn)

theorem l154TD4On_excTriD4 : L154TD4On l154ExcTriD4 :=
  l154TD4On_of_omegaTD4 l154OmegaTD4_excTriD4

end Twisted

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
