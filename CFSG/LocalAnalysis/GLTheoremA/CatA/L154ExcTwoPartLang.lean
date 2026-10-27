module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTwoPartRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTwoPartDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup PerfectInLayer
  glaPComponent_isComponent_of_le_layer)
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient)
open CFSG.LocalAnalysis.GLTheoremA.FP (fixNum fixNum_congr fixNum_eq_of_zpowers)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (exists_langSetup_frobRoot_twE6_D0)

section Aut

theorem l154_onCenterQuotient_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (ψ : MulAut A) :
    MulAut.congr (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
      (Subgroup.map_center_eq e)) (onCenterQuotient ψ) = onCenterQuotient (MulAut.congr e ψ) := by
  ext t
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective t
  rfl

theorem l154_indAut_pow {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (k : ℕ)
    (hgk : g ^ k ∈ Subgroup.normalizer (L : Set G)) :
    MI.indAut p L (g ^ k) hgk = MI.indAut p L g hg ^ k := by
  unfold MI.indAut
  rw [← map_pow]
  congr 1
  exact Subtype.ext (by simp [inv_pow])

theorem l154_fixNum_pow {R : Type*} [Group R] {f : MulAut R} {p k : ℕ} (hp : p.Prime)
    (hf : f ^ p = 1) (hk : Nat.Coprime k p) : fixNum (f ^ k) = fixNum f := by
  refine fixNum_eq_of_zpowers (Subgroup.npow_mem_zpowers f k) ?_
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk hp.one_lt
  have e : f = (f ^ k) ^ m := by
    rw [← pow_mul, ← Nat.div_add_mod (k * m) p, hm, pow_add, pow_mul, hf, one_pow, one_mul,
      pow_one]
  have hmem : (f ^ k) ^ m ∈ Subgroup.zpowers (f ^ k) := Subgroup.npow_mem_zpowers _ m
  rwa [← e] at hmem

end Aut

section Model

theorem l154_twoPart_of_model {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {x y : Ω} {J : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥) (hxp : x ^ p = 1)
    (hyp : y ^ p = 1) (hxN : x ∈ Subgroup.normalizer (S : Set Ω))
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) {k : ℕ} (hk : Nat.Coprime k p) {C : Type}
    [Group C] [Finite C] (θ : PSimple p S ≃* C) (φx φy : MulAut C)
    (hindx : LargeEvenInduces θ (indRel p S x) φx)
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
      Nonempty (PSimple p J ≃* (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))) ∧
      ∃ σ : MulAut ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i),
        (∀ r, ((σ r : ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) : ModGL τ L) =
          R.step0 (r : ModGL τ L)) ∧
        fixNum (MI.indAut p J y hJy) = fixNum (onCenterQuotient σ) := by
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
  let eZ : (↥JP ⧸ Subgroup.center ↥JP) ≃* (↥Ri ⧸ Subgroup.center ↥Ri) :=
    QuotientGroup.congr (Subgroup.center ↥JP) (Subgroup.center ↥Ri) eJ
      (Subgroup.map_center_eq eJ)
  have h1 : MulAut.congr e₀ (MI.indAut p J (y ^ k) hJyk) = onCenterQuotient ψJ := by
    ext t
    have := he₀ (e₀.symm t)
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  refine ⟨i, hqi, hstab, ⟨e₀.trans eZ⟩, MulAut.congr eJ ψJ, fun r => ?_, ?_⟩
  · have h := hσ (eJ.symm r)
    rw [MulEquiv.apply_symm_apply] at h
    exact h
  · have hf3 : MI.indAut p J y hJy ^ p = 1 := l154_indAut_pow_eq_one hJy hyp
    rw [← l154_onCenterQuotient_congr eJ ψJ, fixNum_congr, ← h1, fixNum_congr,
      l154_indAut_pow hJy k hJyk, l154_fixNum_pow hp hf3 hk]

end Model

section Setup

theorem l154_twoPart_of_lang (hC : L154D4Class) (hTP : L154D4TwoPart) {Ω : Type} [Group Ω]
    [Finite Ω] {J : Subgroup Ω} {y : Ω} (hJy : y ∈ Subgroup.normalizer (J : Set Ω))
    (hD4 : catalogIs (PSimple 3 J) isD4any) {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] (SL : LangSetup τ L 3) (R : FrobRoot SL.D 3) (e : ℕ) (a : Fin τ.rank → Lˣ)
    (i : KernelComponent (rootCharHom a)) (hD0 : L154RootD0 SL R) (he : 1 ≤ e)
    (hq0 : R.q0 = 2 ^ e) (hTa : rootDiagUnit τ a ∈ SL.D.torus) (hap : ∀ k, a k ^ 3 = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (hfa : R.step0 (rootDiagUnit τ a) = rootDiagUnit τ a)
    (hqi : CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))
    (hstab : ∀ z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i,
      R.step0 z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i)
    (E : PSimple 3 J ≃* (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)))
    (σ : MulAut ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))
    (hσ : ∀ r, ((σ r : ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) : ModGL τ L) =
      R.step0 (r : ModGL τ L))
    (hfix : fixNum (MI.indAut 3 J y hJy) = fixNum (onCenterQuotient σ)) :
    centCard2 3 J y ^ 3 = card2 3 J := by
  have hcat : catalogIs (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) isD4any := by
    obtain ⟨idx, hidx, ⟨f⟩⟩ := hD4
    exact ⟨idx, hidx, ⟨E.symm.trans f⟩⟩
  obtain ⟨hr, hc, hρ, hinn⟩ := hC τ L 3 SL a i hTa hap ha1 hqi hcat
  have key := hTP τ L 3 SL R e a i hD0 he hq0 hTa hap ha1 hfa hqi hstab hr hc hρ hinn σ hσ
  rw [FP.centCard2_eq_twoPart_fixNum hJy (FP.odd_card_center_pQuot Nat.prime_three
      (by norm_num) J), FP.card2_eq_twoPart_card_pSimple Nat.prime_three (by norm_num) J, hfix,
    Nat.card_congr E.toEquiv]
  exact key

theorem l154_twoPart_untw_lang {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x y : Ω}
    {J : Subgroup Ω} (hSn : S.Normal) (hqS : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore 3 ↥S = ⊥) (hQ : catalogIs (PSimple 3 S) l154ExcUntw) (hxp : x ^ 3 = 1)
    (hyp : y ^ 3 = 1) (hxy : x * y = y * x) (hInn : InnDiagOn 3 (Subgroup.zpowers x) S)
    (hF : FieldOn 3 y S) (hJ : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) (hcm : ¬ CentMod 3 S x) :
    ∃ (τ : Tag) (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L 2)
      (SL : LangSetup τ L 3) (R : FrobRoot SL.D 3) (e : ℕ) (a : Fin τ.rank → Lˣ)
      (i : KernelComponent (rootCharHom a)),
      L154RootD0 SL R ∧ 1 ≤ e ∧ R.q0 = 2 ^ e ∧
      rootDiagUnit τ a ∈ SL.D.torus ∧ (∀ k, a k ^ 3 = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
      R.step0 (rootDiagUnit τ a) = rootDiagUnit τ a ∧
      CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
      (∀ z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i,
        R.step0 z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
      Nonempty (PSimple 3 J ≃* (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))) ∧
      ∃ σ : MulAut ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i),
        (∀ r, ((σ r : ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) : ModGL τ L) =
          R.step0 (r : ModGL τ L)) ∧
        fixNum (MI.indAut 3 J y hJy) = fixNum (onCenterQuotient σ) := by
  classical
  have hxN := l154_mem_normalizer_of_normal hSn x
  obtain ⟨τ, K, _, _, e, k, θ, φx, φy, h, T, hτ, hchar, he, hK, hT, hperf, -, hhp, hfix, hhL,
    hk, hφx, hφy, hindx, hindy⟩ :=
    excUntw_marking_data Nat.prime_three (by norm_num) hQ hxp hyp hxy hInn hF
  haveI := hchar
  haveI : Finite ↥(adjointGroup τ K) := Finite.of_equiv _ θ.toEquiv
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hcm (l154_centMod_of_conj_one hqS hxN θ φx hφx hindx)
  obtain ⟨SL, R, a, ι, -, hq0, -, hTa, hap, ha1, hfa, hι, hrange, hβ, hφ, hD0⟩ :=
    l154td4_exists_langSetup_frobRoot_untw hτ Nat.prime_three (by norm_num) he hK hperf T hT φx
      φy h hhL hφx hφy hhp hh1 hfix
  obtain ⟨i, hqi, hstab, hE, σ, hσ, hfx⟩ := l154_twoPart_of_model Nat.prime_three hSp hxp hyp
    hxN hJ hJy hk θ φx φy hindx hindy SL R ι hι hrange hβ hφ hTa hap ha1
  exact ⟨τ, AlgebraicClosure K, inferInstance, inferInstance, inferInstance, SL, R, e, a, i, hD0,
    he, hq0, hTa, hap, ha1, hfa, hqi, hstab, hE, σ, hσ, hfx⟩

theorem l154_twoPart_twE6_lang {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x y : Ω}
    {J : Subgroup Ω} (hSn : S.Normal) (hqS : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore 3 ↥S = ⊥) (hQ : catalogIs (PSimple 3 S) l154ExcTwE6) (hxp : x ^ 3 = 1)
    (hyp : y ^ 3 = 1) (hxy : x * y = y * x) (hInn : InnDiagOn 3 (Subgroup.zpowers x) S)
    (hF : FieldOn 3 y S) (hJ : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) (hcm : ¬ CentMod 3 S x) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L 2)
      (SL : LangSetup Tag.E6 L 3) (R : FrobRoot SL.D 3) (e : ℕ) (a : Fin Tag.E6.rank → Lˣ)
      (i : KernelComponent (rootCharHom a)),
      L154RootD0 SL R ∧ 1 ≤ e ∧ R.q0 = 2 ^ e ∧
      rootDiagUnit Tag.E6 a ∈ SL.D.torus ∧ (∀ k, a k ^ 3 = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      R.step0 (rootDiagUnit Tag.E6 a) = rootDiagUnit Tag.E6 a ∧
      CFSG.IsQuasisimple ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
      (∀ z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i,
        R.step0 z ∈ rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ∧
      Nonempty (PSimple 3 J ≃* (↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i))) ∧
      ∃ σ : MulAut ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i),
        (∀ r, ((σ r : ↥(rationalComponent SL.ρ SL.Γ (rootCharHom a) i)) : ModGL Tag.E6 L) =
          R.step0 (r : ModGL Tag.E6 L)) ∧
        fixNum (MI.indAut 3 J y hJy) = fixNum (onCenterQuotient σ) := by
  classical
  have hxN := l154_mem_normalizer_of_normal hSn x
  obtain ⟨K, _, _, e, k, σ₀, θ, φx, φy, h, T, hchar, he, hK, hσ₀, hT, hh, hhp, hfix, hk, hφx,
    hφy, hindx, hindy⟩ := excTwE6_marking_data Nat.prime_three (by norm_num) hQ hxp hyp hxy hInn hF
  haveI := hchar
  haveI : Finite ↥(twistedE6RootGroup K σ₀) := Finite.of_equiv _ θ.toEquiv
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hcm (l154_centMod_of_conj_one hqS hxN θ φx hφx hindx)
  obtain ⟨SL, R, a, ι, -, hq0, hTa, hap, ha1, hfa, hι, hrange, hβ, hφ, hD0⟩ :=
    exists_langSetup_frobRoot_twE6_D0 Nat.prime_three (by norm_num) he hK σ₀ hσ₀ T hT φx φy h hh
      hφx hφy hhp hh1 hfix
  obtain ⟨i, hqi, hstab, hE, σ, hσ, hfx⟩ := l154_twoPart_of_model Nat.prime_three hSp hxp hyp
    hxN hJ hJy hk θ φx φy hindx hindy SL R ι hι hrange hβ hφ hTa hap ha1
  exact ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance, SL, R, e, a, i, hD0, he,
    hq0, hTa, hap, ha1, hfa, hqi, hstab, hE, σ, hσ, hfx⟩

theorem compTwoPart3D4_excUntw (hC : L154D4Class) (hTP : L154D4TwoPart) :
    CompTwoPart3D4 l154ExcUntw := by
  intro Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy _ _ hInn hF hJ hJy hD4 _ hnF
  by_cases hcm : CentMod 3 S x
  · exact absurd (by rw [l154_eq_of_centMod hqS hSp hcm hJ]; exact hF) hnF
  obtain ⟨τ, L, _, _, _, SL, R, e, a, i, hD0, he, hq0, hTa, hap, ha1, hfa, hqi, hstab, ⟨E⟩, σ,
    hσ, hfx⟩ := l154_twoPart_untw_lang hSn hqS hSp hQ hxp hyp hxy hInn hF hJ hJy hcm
  exact l154_twoPart_of_lang hC hTP hJy hD4 SL R e a i hD0 he hq0 hTa hap ha1 hfa hqi hstab E σ
    hσ hfx

theorem compTwoPart3D4_excTwE6 (hC : L154D4Class) (hTP : L154D4TwoPart) :
    CompTwoPart3D4 l154ExcTwE6 := by
  intro Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy _ _ hInn hF hJ hJy hD4 _ hnF
  by_cases hcm : CentMod 3 S x
  · exact absurd (by rw [l154_eq_of_centMod hqS hSp hcm hJ]; exact hF) hnF
  obtain ⟨L, _, _, _, SL, R, e, a, i, hD0, he, hq0, hTa, hap, ha1, hfa, hqi, hstab, ⟨E⟩, σ, hσ,
    hfx⟩ := l154_twoPart_twE6_lang hSn hqS hSp hQ hxp hyp hxy hInn hF hJ hJy hcm
  exact l154_twoPart_of_lang hC hTP hJy hD4 SL R e a i hD0 he hq0 hTa hap ha1 hfa hqi hstab E σ
    hσ hfx

end Setup

section Final

theorem compTwoPart3_exc_of_lang (hC : L154D4Class) (hTP : L154D4TwoPart) :
    T158.CompTwoPart3 l154Exc :=
  compTwoPart3_exc_of_d4 (compTwoPart3D4_excUntw hC hTP) (compTwoPart3D4_excTwE6 hC hTP)

end Final

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
