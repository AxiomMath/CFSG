module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcG2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcJ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIBase
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Root
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcOmega
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Omega
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces LargeEvenMarking LargeEvenMarkProp)
open CFSG.StandardType (GGOutdiagPrime)
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup PerfectInLayer
  glaPComponent_isComponent_of_le_layer)
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient onCenterQuotient_apply_mk
  centerQuotientHom centerQuotientHom_injective)

section Transport

theorem l154_marking_transport {X Y : Type*} [Group X] [Group Y] (hY : commutator Y = ⊤)
    (E : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) {P : LargeEvenMarkProp X}
    (h : LargeEvenMarking X P) :
    LargeEvenMarking Y fun lab R _ I F θ => P lab R I F (E.trans θ) := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  refine ⟨hY, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  refine ⟨hs, hna, E.symm.trans θ, ?_⟩
  have e : E.trans (E.symm.trans θ) = θ := by
    ext u
    simp
  show P lab R I F (E.trans (E.symm.trans θ))
  rw [e]
  exact hθ

theorem l154_marking_or {X : Type*} [Group X] {P₁ P₂ : LargeEvenMarkProp X}
    (h : LargeEvenMarking X fun lab R _ I F θ => P₁ lab R I F θ ∨ P₂ lab R I F θ) :
    LargeEvenMarking X P₁ ∨ LargeEvenMarking X P₂ := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  have hraw' := CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (Q' := fun R _ I F => (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, P₁ lab R I F θ) ∨
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, P₂ lab R I F θ))
    (by
      rintro R _ I F ⟨hs, hna, θ, hθ | hθ⟩
      · exact Or.inl ⟨hs, hna, θ, hθ⟩
      · exact Or.inr ⟨hs, hna, θ, hθ⟩) hraw
  rcases MI.canonRawDatum_or hraw' with h1 | h2
  · exact Or.inl ⟨hX, lab, hlab, h1⟩
  · exact Or.inr ⟨hX, lab, hlab, h2⟩

theorem l154_induces_transfer {P₁ C M : Type*} [Group P₁] [Group C] [Group M] {JP : Subgroup C}
    {Ri : Subgroup M} (e : ↥JP ≃* ↥Ri) (e₀ : P₁ ≃* ↥JP ⧸ Subgroup.center ↥JP) (A : MulAut P₁)
    (ψ : MulAut ↥JP) (hA : ∀ s, e₀ (A s) = onCenterQuotient ψ (e₀ s)) (σ : M → M)
    (hσ : ∀ j : ↥JP, ((e (ψ j) : ↥Ri) : M) = σ ((e j : ↥Ri) : M)) {R : Type} [Group R]
    (θ : ↥Ri ⧸ Subgroup.center ↥Ri ≃* R) :
    LargeEvenInduces θ (fun x x' : ↥Ri => σ (x : M) = (x' : M))
      (MulAut.congr ((e₀.trans (QuotientGroup.congr (Subgroup.center ↥JP) (Subgroup.center ↥Ri) e
        (Subgroup.map_center_eq e))).trans θ) A) := by
  intro x x' hxx
  obtain ⟨j, rfl⟩ := e.surjective x
  have hx' : x' = e (ψ j) := Subtype.ext ((hσ j).trans hxx).symm
  subst hx'
  obtain ⟨s, hs⟩ := e₀.surjective (QuotientGroup.mk j)
  set Q := QuotientGroup.congr (Subgroup.center ↥JP) (Subgroup.center ↥Ri) e
    (Subgroup.map_center_eq e) with hQdef
  have hQ : ∀ j' : ↥JP, Q (QuotientGroup.mk j') = QuotientGroup.mk (e j') := fun j' =>
    QuotientGroup.congr_mk _ _ _ _ j'
  have h1 : θ (QuotientGroup.mk (e j)) = ((e₀.trans Q).trans θ) s := by
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hs, hQ]
  have h2 : onCenterQuotient ψ (QuotientGroup.mk j) = QuotientGroup.mk (ψ j) :=
    onCenterQuotient_apply_mk ψ j
  rw [h1]
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_apply_apply]
  rw [hA, hs, h2, hQ]

theorem l154_centMod_of_induces_one {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω} {x : Ω}
    (hperf : commutator ↥S = ⊤) (hxN : x ∈ Subgroup.normalizer (S : Set Ω)) {C : Type}
    [Group C] (θ : PSimple p S ≃* C) (hind : LargeEvenInduces θ (indRel p S x) 1) :
    CentMod p S x := by
  have h1 := (MI.induces_indRel_iff hxN θ).1 hind
  have h2 : MI.indAut p S x hxN = 1 :=
    (MulAut.congr θ).injective (by rw [← h1, map_one])
  haveI : Group.IsPerfect ↥S := ⟨hperf⟩
  haveI : Group.IsPerfect (PQuot p S) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (GLAPPrimeCore p ↥S))
      (QuotientGroup.mk'_surjective _)
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hxN
  have h3 : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p S ⟨x⁻¹, hxN'⟩ = 1 :=
    centerQuotientHom_injective (PQuot p S) (by rw [map_one]; exact h2)
  have h4 := (chev_barAut_eq_one_iff_centMod hxN').1 h3
  exact centMod_iff.2 (by simpa using Subgroup.inv_mem _ (centMod_iff.1 h4))

end Transport

section Lang

theorem l154_lang_noInnDiag (hInn : L154LangInnRes) {τ : Tag}
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (S : LangSetup τ L p) (R : FrobRoot S.D p) {e : ℕ} (he : 1 ≤ e) (hq0 : R.q0 = 2 ^ e)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ k, a k ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (hfa : R.step0 (rootDiagUnit τ a) = rootDiagUnit τ a)
    {i : KernelComponent (rootCharHom a)}
    (hqi : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hstab : ∀ z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      R.step0 z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hM : LargeEvenMarking ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) fun _ _ _ I _ θ =>
      ∃ φ ∈ I, LargeEvenInduces θ (fun x x' => R.step0 (x : ModGL τ L) = (x' : ModGL τ L)) φ) :
    False := by
  haveI : ExpChar L 2 := ExpChar.prime Nat.prime_two
  have hF : ∀ z : ModGL τ L, (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      R.step0 x = z * x * z⁻¹) → False := by
    intro z hz
    by_cases hG : τ = .G2
    · subst hG
      exact frobRootNotConjG2_holds L p S p R e a i z hp hp2 he hq0 hT hap ha1 hfa hqi hstab hz
    · have h3 : 3 ≤ p := hp.two_le.lt_of_ne fun h => hp2 h.symm
      have hep : 3 ≤ e * p := by nlinarith
      have h8 : 8 ≤ 2 ^ (e * p) :=
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (e * p) := Nat.pow_le_pow_right (by norm_num) hep
      have hq4 : S.D.q ≠ 4 := by
        rw [R.q_eq, hq0, ← pow_mul]
        omega
      exact FrobRoot.not_conj S R hG Nat.prime_two hq0 he hp.two_le (Or.inl hq4) hT i z hz
  have hsplit := CFSG.StandardType.Canonical.largeEvenMarking_mono
    (X := ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) (P' := fun _ R' _ I _ θ =>
      (GGOutdiagPrime p R' I ∧ ∃ φ ∈ I,
        LargeEvenInduces θ (fun x x' => R.step0 (x : ModGL τ L) = (x' : ModGL τ L)) φ) ∨
      (¬ GGOutdiagPrime p R' I ∧ ∃ φ ∈ I,
        LargeEvenInduces θ (fun x x' => R.step0 (x : ModGL τ L) = (x' : ModGL τ L)) φ))
    (by
      intro _ R' _ I _ _ h
      by_cases hg : GGOutdiagPrime p R' I
      · exact Or.inl ⟨hg, h⟩
      · exact Or.inr ⟨hg, h⟩) hM
  rcases l154_marking_or hsplit with h1 | h2
  · obtain ⟨z, -, hz⟩ := l154_lang_exists_conj S R hstab h1
    exact hF z hz
  · obtain ⟨z, hz⟩ := hInn τ L p S p R a i hp hp2 hT hap ha1 hfa hqi hstab h2
    exact hF z hz

end Lang

section Model

theorem l154_lang_of_model {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥) (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (S : Set Ω))
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) {k : ℕ} {C : Type} [Group C] [Finite C]
    (θ : PSimple p S ≃* C) (φx φy : MulAut C) (hindx : LargeEvenInduces θ (indRel p S x) φx)
    (hindy : LargeEvenInduces θ (indRel p S (y ^ k)) φy) {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] (SL : LangSetup τ L p) (R : FrobRoot SL.D p) {a : Fin τ.rank → Lˣ}
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = SL.Γ)
    (hβ : ∀ c, ι (φx c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hφ : ∀ c, ι (φy c) = R.step0 (ι c)) (hTa : rootDiagUnit τ a ∈ SL.D.torus)
    (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1) :
    ∃ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
      (∀ z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i,
        R.step0 z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
      (InnDiagOn p (Subgroup.zpowers y) J →
        LargeEvenMarking ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) fun _ _ _ I _ θ =>
          ∃ φ ∈ I, LargeEvenInduces θ
            (fun z z' => R.step0 (z : ModGL τ L) = (z' : ModGL τ L)) φ) ∧
      (IsTD4 p J → catalogIs (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))
          (onLie fun | .trialityD4 _ => True | _ => False)) := by
  classical
  set JP : Subgroup C := l154JImage p S J θ with hJPdef
  have hJPc : GLAPComponent p (fixSubgroup φx) JP :=
    l154_JImage_glaPComponent hp hxp hxN hJ θ φx hindx
  have hTame :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame SL hTa hap ha1
  have hPIL : PerfectInLayer φx :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_of_langSetup SL ι hι
      hrange φx hβ hTa hap ha1 hTame
  have hJPcomp := (glaPComponent_isComponent_of_le_layer hJPc
    (hPIL JP hJPc.1 (glaPComponent_perfect hJPc))).1
  obtain ⟨i, hqi, hmap⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup
    SL hp ι hι hrange φx hβ hTa hap ha1 hTame hJPcomp
  set Ri := rationalComponent SL.ρ SL.Γ (rootCharHom a) i with hRidef
  let eJ : ↥JP ≃* ↥Ri := (JP.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hmap)
  have heJ : ∀ j : ↥JP, ((eJ j : ↥Ri) : ModGL τ L) = ι j := fun j => rfl
  have hqJP : CFSG.IsQuasisimple ↥JP := CFSG.IsQuasisimple.of_mulEquiv eJ hqi
  have hJS : J ≤ S := hJ.1.trans inf_le_left
  have hJyk : y ^ k ∈ Subgroup.normalizer (J : Set Ω) := Subgroup.pow_mem _ hJy k
  obtain ⟨ψJ, e₀, hψ, he₀⟩ := l154_JImage_equiv hp hSp hJ hJS hJyk θ φy hindy
    ⟨hqJP.1.commutator_eq_top, hqJP.2.1⟩
  have hσ : ∀ j : ↥JP, ((eJ (ψJ j) : ↥Ri) : ModGL τ L) =
      R.step0 ((eJ j : ↥Ri) : ModGL τ L) := fun j => by
    rw [heJ, heJ, hψ j, hφ]
  have hstab : ∀ z ∈ Ri, R.step0 z ∈ Ri := by
    intro z hz
    obtain ⟨j, hj⟩ := eJ.surjective ⟨z, hz⟩
    have hz' : z = ((eJ j : ↥Ri) : ModGL τ L) := by rw [hj]
    rw [hz', ← hσ j]
    exact (eJ (ψJ j)).2
  let E : PSimple p J ≃* ↥Ri ⧸ Subgroup.center ↥Ri :=
    e₀.trans (QuotientGroup.congr (Subgroup.center ↥JP) (Subgroup.center ↥Ri) eJ
      (Subgroup.map_center_eq eJ))
  refine ⟨i, hqi, hstab, fun hInnJ => ?_, fun hTD => ?_⟩
  · have hMJ : LargeEvenMarking (PQuot p J) fun _ _ _ I _ θJ =>
        ∃ φ ∈ I, LargeEvenInduces θJ (indRel p J (y ^ k)) φ :=
      CFSG.StandardType.Canonical.largeEvenMarking_mono
        (by
          intro _ _ _ _ _ _ hh
          exact hh (y ^ k) (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) k)) hInnJ.2
    refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_
      (l154_marking_transport hqi.1.commutator_eq_top E hMJ)
    rintro lab R' _ I F θ' ⟨φ, hφI, hind⟩
    refine ⟨φ, hφI, ?_⟩
    rw [MI.induces_indRel_iff hJyk] at hind
    subst hind
    exact l154_induces_transfer eJ e₀ (MI.indAut p J (y ^ k) hJyk) ψJ he₀ R.step0 hσ θ'
  · obtain ⟨idx, hidx, ⟨f⟩⟩ := hTD
    exact ⟨idx, hidx, ⟨E.symm.trans f⟩⟩

end Model

section Setup

theorem l154_excUntw_lang {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω} (hSn : S.Normal) (hqS : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hQ : catalogIs (PSimple p S) l154ExcUntw) (hxp : x ^ p = 1)
    (hyp : y ^ p = 1) (hxy : x * y = y * x) (hInn : InnDiagOn p (Subgroup.zpowers x) S)
    (hF : FieldOn p y S) (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) (hcm : ¬ CentMod p S x) :
    ∃ (τ : Tag) (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L 2)
      (SL : LangSetup τ L p) (R : FrobRoot SL.D p) (e : ℕ) (a : Fin τ.rank → Lˣ)
      (i : KernelComponent (rootCharHom a)),
      (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) ∧ 1 ≤ e ∧ R.q0 = 2 ^ e ∧
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
          (onLie fun | .trialityD4 _ => True | _ => False)) := by
  classical
  have hxN : x ∈ Subgroup.normalizer (S : Set Ω) := by
    haveI := hSn
    rw [Subgroup.normalizer_eq_top S]
    exact Subgroup.mem_top x
  obtain ⟨τ, K, _, _, e, k, θ, φx, φy, h, T, hτ, hchar, he, hK, hT, hperf, -, hhp, hfix, hhL,
    -, hφx, hφy, hindx, hindy⟩ := excUntw_marking_data hp hp2 hQ hxp hyp hxy hInn hF
  haveI := hchar
  haveI : Finite ↥(adjointGroup τ K) := Finite.of_equiv _ θ.toEquiv
  have hh1 : h ≠ 1 := by
    rintro rfl
    have h1 : φx = 1 := by
      ext c
      rw [hφx c]
      simp
    exact hcm (l154_centMod_of_induces_one hqS.1 hxN θ (h1 ▸ hindx))
  obtain ⟨SL, R, a, ι, -, hq0, -, hTa, hap, ha1, hfa, hι, hrange, hβ, hφ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_frobRoot_untw hτ hp
      hp2 he hK hperf T hT φx φy h hhL hφx hφy hhp hh1 hfix
  obtain ⟨i, hqi, hstab, hNID, hTD⟩ := l154_lang_of_model hp hSp hxp hxN hJ hJy θ φx φy hindx
    hindy SL R ι hι hrange hβ hφ hTa hap ha1
  exact ⟨τ, AlgebraicClosure K, inferInstance, inferInstance, inferInstance, SL, R, e, a, i, hτ,
    he, hq0, hTa, hap, ha1, hfa, hqi, hstab, hNID, hTD⟩

theorem l154OmegaNID_excUntw (hInn : L154LangInnRes) :
    L154OmegaNID l154ExcUntw := by
  intro p hp hp2 Ω _ _ S x y J hSn hqS hSp _ hQ hxp hyp hxy hInnx hF hJ hJy
  refine ⟨hJy, fun hInnJ => ?_⟩
  by_cases hcm : CentMod p S x
  · exact (l154_of_centMod hqS hSp hcm hF hJ).1.2 hInnJ
  obtain ⟨τ, L, _, _, _, SL, R, e, a, i, -, he, hq0, hTa, hap, ha1, hfa, hqi, hstab, hNID, -⟩ :=
    l154_excUntw_lang hp hp2 hSn hqS hSp hQ hxp hyp hxy hInnx hF hJ hJy hcm
  exact l154_lang_noInnDiag hInn hp hp2 SL R he hq0 hTa hap ha1 hfa hqi hstab (hNID hInnJ)

theorem l154NIDOn_excUntw (hInn : L154LangInnRes) : L154NIDOn l154ExcUntw :=
  l154NIDOn_of_omegaNID (l154OmegaNID_excUntw hInn)

end Setup

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
