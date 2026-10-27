module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6LModel
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLift
public import CFSG.GroupTheory.PLayer.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2

theorem sylow_coe_smul_eq_map {G : Type*} [Group G] (P : Sylow 3 G) (β : G) :
    ((β • P : Sylow 3 G) : Subgroup G) = (P : Subgroup G).map (MulAut.conj β).toMonoidHom := by
  rw [Sylow.coe_subgroup_smul]
  ext x
  simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨β⁻¹ * x * β, h, by group⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy

theorem sylow_eq_map_conj_of_le {G : Type*} [Group G] (P : Sylow 3 G) (β : G)
    {P₀ : Subgroup G} (h0 : IsPGroup 3 P₀)
    (hle : (P : Subgroup G).map (MulAut.conj β).toMonoidHom ≤ P₀) :
    P₀ = (P : Subgroup G).map (MulAut.conj β).toMonoidHom := by
  have h := (β • P).is_maximal' h0 (by rw [sylow_coe_smul_eq_map]; exact hle)
  rw [h, sylow_coe_smul_eq_map]

section Setup

theorem exists_model (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hd : d.1 = TauCeti.LieTypeIndex.twistedE6 q) (hq : q.card = 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (2 ^ 1) ^ 2 ∧
      (∀ c, σ c = c ^ 2 ^ 1) ∧
      Nonempty ((TauCeti.CFSGIndex.lie d).Group ≃* twistedE6RootGroup K σ) := by
  obtain ⟨x, hv⟩ := d
  have hd' : x = TauCeti.LieTypeIndex.twistedE6 q := hd
  subst hd'
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hqc : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  rw [hqc] at hK hσ
  refine ⟨K, inferInstance, Nat.finite_of_card_ne_zero (by rw [hK]; norm_num), σ, by simpa using hK,
    fun c => by simpa using hσ c, ⟨e⟩⟩

open CFSG.StandardType CFSG.StandardType.NoOffTwE6Three CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_hom_ker_eq_range {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1) :
    ∃ Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K,
      Θ.ker = (rgrpConjAut le_rfl hK σ hσ Fr hFr).range := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two le_rfl K hK σ hσ
  refine ⟨Θ, ?_⟩
  rw [hker, rgrpConjAut_range, ← inn_sup_compatParamAut_eq_range_twConj σ,
    range_compatParamAut_eq_twistedE6Diag σ]
  rfl

theorem isPGroup_le_range_rgrpConjAut {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1) {P : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hP : IsPGroup 3 P) : P ≤ (rgrpConjAut le_rfl hK σ hσ Fr hFr).range := by
  obtain ⟨Θ, hΘ⟩ := exists_hom_ker_eq_range σ hK hσ Fr hFr
  rw [← hΘ]
  intro x hx
  rw [MonoidHom.mem_ker]
  have hcard : Nat.card (RingAut K) = 2 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
      (n := 2) (by rw [hK]; norm_num)).1
  obtain ⟨m, hm⟩ := hP ⟨x, hx⟩
  have h1 : (Θ x) ^ (3 ^ m) = 1 := by
    rw [← map_pow]
    have := congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
    rw [this, map_one]
  have h2 : orderOf (Θ x) ∣ 2 := hcard ▸ orderOf_dvd_natCard _
  have h3 : orderOf (Θ x) ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf (Θ x) ∣ Nat.gcd 2 (3 ^ m) := Nat.dvd_gcd h2 h3
  have h5 : Nat.gcd 2 (3 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num)
  rw [h5] at h4
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)

section Embed

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {Fr : Ω →+* Ω}
  {g : ModGL Tag.E6 Ω}

@[expose] noncomputable def kappa (Fr : Ω →+* Ω) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) :
    TwistedDiag.thetaFixed Fr →* TwistedDiag.Rgrp Ω Fr where
  toFun x := ⟨g * (x : ModGL Tag.E6 Ω) * g⁻¹,
    (TwistedDiag.mem_thetaFixed_iff_conj Fr hg hgn x).1 x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem kappa_injective (Fr : Ω →+* Ω) (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) :
    Function.Injective (kappa Fr hg hgn) := by
  intro x y h
  apply Subtype.ext
  have := congrArg Subtype.val h
  simpa [kappa] using this

@[expose] noncomputable def embP (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) :
    sylP Fr →* MulAut (twistedE6RootGroup K σ) :=
  (rgrpConjAut le_rfl hK σ hσ Fr hFr).comp
    ((kappa Fr hg hgn).comp (Subgroup.inclusion (sylP_le_thetaFixed Fr)))

theorem embP_injective (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) :
    Function.Injective (embP hK σ hσ Fr hFr hg hgn) :=
  (rgrpConjAut_injective le_rfl hK σ hσ Fr hFr).comp
    ((kappa_injective Fr hg hgn).comp (Subgroup.inclusion_injective _))

@[expose] noncomputable def torusAut [IsAlgClosed Ω] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω)
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin 6 → ZMod 3) →* MulAut (twistedE6RootGroup K σ) :=
  (embP hK σ hσ Fr hFr hg hgn).comp (PsiP Fr (fun c => by simpa using hFr c) hζ)

open CFSG.StandardType.TableBExc.E6Three in
theorem frameSubP_of_model (Sel : Subgroup (Multiplicative (Fin 6 → ZMod 3)) → Prop)
    [IsAlgClosed Ω] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω)
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (hgood : ∀ G : Subgroup (Multiplicative (Fin 6 → ZMod 3)), Sel G →
      RootGood ((fun g : Multiplicative (Fin 6 → ZMod 3) => Multiplicative.toAdd g) ''
        (G : Set _)) → IsGood 3 (G.map (torusAut hK σ hσ Fr hFr hg hgn hζ)))
    (P : Sylow 3 (MulAut (twistedE6RootGroup K σ))) :
    FrameSubP Sel (twistedE6RootGroup K σ) (P : Subgroup (MulAut (twistedE6RootGroup K σ))) := by
  have hFr' : ∀ c, Fr c = c ^ 2 := fun c => by simpa using hFr c
  haveI : Fintype K := Fintype.ofFinite K
  haveI hcharK : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  haveI hcharΩ : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Φ := rgrpConjAut le_rfl hK σ hσ Fr hFr with hΦ
  have hΦinj : Function.Injective Φ := rgrpConjAut_injective le_rfl hK σ hσ Fr hFr
  set ι := embP hK σ hσ Fr hFr hg hgn with hι
  have hιinj : Function.Injective ι := embP_injective hK σ hσ Fr hFr hg hgn
  have hP0 : IsPGroup 3 ι.range :=
    (isPGroup_sylP Fr hFr' hζ hζ').of_surjective ι.rangeRestrict
      (MonoidHom.rangeRestrict_surjective ι)
  have hle : (P : Subgroup (MulAut (twistedE6RootGroup K σ))) ≤ Φ.range :=
    isPGroup_le_range_rgrpConjAut σ hK hσ Fr hFr P.isPGroup'
  let X : Subgroup (ModGL Tag.E6 Ω) :=
    ((P : Subgroup (MulAut (twistedE6RootGroup K σ))).comap Φ).map (TwistedDiag.Rgrp Ω Fr).subtype
  have hXR : X ≤ TwistedDiag.Rgrp Ω Fr := Subgroup.map_subtype_le _
  have hXp : IsPGroup 3 X := by
    intro x
    obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨Φ r, hr⟩
    refine ⟨m, Subtype.ext ?_⟩
    have h1 : (Φ r) ^ (3 ^ m) = 1 := by
      have := congrArg Subtype.val hm
      rw [Subgroup.coe_pow, OneMemClass.coe_one] at this
      exact this
    have h2 : r ^ (3 ^ m) = 1 := hΦinj (by rw [map_pow, h1, map_one])
    have h3 : (x : ModGL Tag.E6 Ω) = (r : ModGL Tag.E6 Ω) := hrx.symm
    show (x : ModGL Tag.E6 Ω) ^ (3 ^ m) = 1
    rw [h3, ← Subgroup.coe_pow, h2]
    rfl
  obtain ⟨k, hk, r, hr, hconj⟩ := exists_conj_le_xHat (ℓ := 2) (f := 1) le_rfl K hK σ.toRingHom
    (fun c => hσ c) (by norm_num) Ω Fr hFr hg hgn hXR hXp
  have hkR : g * k * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr :=
    (TwistedDiag.mem_thetaFixed_iff_conj Fr hg hgn k).1 hk
  have hr₂ : (g * k * g⁻¹) * r ∈ TwistedDiag.Rgrp Ω Fr := mul_mem hkR hr
  let r₂ : TwistedDiag.Rgrp Ω Fr := ⟨(g * k * g⁻¹) * r, hr₂⟩
  let β : MulAut (twistedE6RootGroup K σ) := Φ r₂
  have hmap : (P : Subgroup (MulAut (twistedE6RootGroup K σ))).map (MulAut.conj β).toMonoidHom ≤
      ι.range := by
    intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨r', hr'⟩ := hle hy₀
    have hX' : (r' : ModGL Tag.E6 Ω) ∈ X :=
      ⟨r', by rw [SetLike.mem_coe, Subgroup.mem_comap, hr']; exact hy₀, rfl⟩
    have hz : (k * g⁻¹ * r) * (r' : ModGL Tag.E6 Ω) * (k * g⁻¹ * r)⁻¹ ∈ sylP Fr :=
      hconj ⟨(r' : ModGL Tag.E6 Ω), hX', rfl⟩
    refine ⟨⟨_, hz⟩, ?_⟩
    rw [← hr']
    show Φ _ = β * Φ r' * β⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    refine congrArg Φ ?_
    apply Subtype.ext
    simp only [MonoidHom.comp_apply, kappa, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_inclusion, r₂]
    group
  have hP0eq : (ι.range : Subgroup (MulAut (twistedE6RootGroup K σ))) =
      (P : Subgroup (MulAut (twistedE6RootGroup K σ))).map (MulAut.conj β).toMonoidHom :=
    sylow_eq_map_conj_of_le P β hP0 hmap
  have hfr : FrameSubP Sel (twistedE6RootGroup K σ) ι.range :=
    frameSubP_sylP Fr Sel hFr' hζ hζ' ι hιinj hgood
  have h2 := frameSubP_map_mulEquiv Sel
    (β⁻¹ : twistedE6RootGroup K σ ≃* twistedE6RootGroup K σ) hfr
  have hback : ι.range.map (MulAut.congr (β⁻¹ : twistedE6RootGroup K σ ≃* twistedE6RootGroup K σ)).toMonoidHom =
      (P : Subgroup (MulAut (twistedE6RootGroup K σ))) := by
    rw [hP0eq, Subgroup.map_map]
    have hid : (MulAut.congr (β⁻¹ : twistedE6RootGroup K σ ≃* twistedE6RootGroup K σ)).toMonoidHom.comp
        (MulAut.conj β).toMonoidHom = MonoidHom.id _ := by
      ext f a
      simp [MulAut.congr_apply, MulAut.conj_apply]
    rw [hid, Subgroup.map_id]
  rw [hback] at h2
  exact h2

end Embed

@[expose] def X2E6TorusGoodP (Sel : Subgroup (Multiplicative (Fin 6 → ZMod 3)) → Prop) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1) (g : ModGL Tag.E6 Ω)
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω)
    (ζ : Ωˣ) (hζ : ζ ^ 3 = 1) (_hζ' : orderOf ζ = 3)
    (G : Subgroup (Multiplicative (Fin 6 → ZMod 3))), Sel G →
    RootGood ((fun g : Multiplicative (Fin 6 → ZMod 3) => Multiplicative.toAdd g) ''
      (G : Set _)) → IsGood 3 (G.map (torusAut hK σ hσ Fr hFr hg hgn hζ))

@[expose] def X2E6TorusGood9 : Prop := X2E6TorusGoodP (fun G => Nat.card G = 9)

@[expose] def X2E6LocalP (Sel : Subgroup (Multiplicative (Fin 6 → ZMod 3)) → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]
    (q : TauCeti.PrimePower),
    d.1 = TauCeti.LieTypeIndex.twistedE6 q → q.card = 2 →
    ∀ P : Sylow 3 (MulAut (TauCeti.CFSGIndex.lie d).Group),
      FrameSubP Sel (TauCeti.CFSGIndex.lie d).Group (P : Subgroup _)

theorem x2e6LocalP_of_torusGoodP (Sel : Subgroup (Multiplicative (Fin 6 → ZMod 3)) → Prop)
    (h : X2E6TorusGoodP Sel) : X2E6LocalP Sel := by
  intro d _ q hd hq P
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_model d q hd hq
  haveI : Finite (twistedE6RootGroup K σ) := Finite.of_equiv _ e.toEquiv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI hcharK : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  let Ω := AlgebraicClosure K
  haveI hcharΩ : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsAlgClosed Ω := inferInstance
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 1
  have hFr : ∀ c, Fr c = c ^ 2 ^ 1 := fun c => iterateFrobenius_def 2 1 c
  obtain ⟨g, hg, hgn⟩ := exists_inv_mul_twistE6_eq (ℓ := 2) (f := 1) le_rfl hFr
    (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) Ω twE6W0)
  have h30 : (3 : Ω) ≠ 0 := by
    have := (CharP.cast_eq_zero_iff Ω 2 3).not.2 (by norm_num)
    simpa using this
  obtain ⟨ζ, hζ, hζ'⟩ := TwistedDiag.exists_cube_root (Ω := Ω) h30
  have hsurj : Function.Surjective (MulAut.congr e).toMonoidHom := (MulAut.congr e).surjective
  let PC : Sylow 3 (MulAut (twistedE6RootGroup K σ)) := P.mapSurjective hsurj
  have hfr := frameSubP_of_model Sel hK σ hσ Fr hFr hg hgn hζ hζ'
    (h K hK σ hσ Ω Fr hFr g hg hgn ζ hζ hζ') PC
  have h2 := frameSubP_map_mulEquiv Sel e.symm hfr
  convert h2 using 1
  show (P : Subgroup _) = Subgroup.map (MulAut.congr e.symm).toMonoidHom
    (P.mapSurjective hsurj : Sylow 3 _)
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  have hid : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
      MonoidHom.id _ := by
    ext f a
    simp [MulAut.congr_apply]
  rw [hid, Subgroup.map_id]

end Setup

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

end
