module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OTwModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OTwRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OParab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OCompLevi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OTwCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OConj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpine
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviSharp
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentZ2Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.LocalAnalysis.GLTheoremA.T173X CFSG.LocalAnalysis.GLTheoremA.T173A
open CFSG.SeitzReduction.TwistedE6Pilot CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.StandardType.TwE6RootKill CFSG.HardMathSupport.Timmesfeld.CrossChar

private lemma map_conj_mul_subtype {G : Type} [Group G] {C : Subgroup G}
    (B : Subgroup C) (g : C) {y : G} (hyC : y ∈ C) :
    (B.map (MulAut.conj (⟨y, hyC⟩ * g)).toMonoidHom).map C.subtype =
      ((B.map (MulAut.conj g).toMonoidHom).map C.subtype).map
        (MulAut.conj y).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  rw [show (⟨y, hyC⟩ * g) * a * (⟨y, hyC⟩ * g)⁻¹
      = ⟨y, hyC⟩ * (g * a * g⁻¹) * ⟨y, hyC⟩⁻¹ by group]
  simp

theorem card_eq_pow_five_of_isBmax
    {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {A : Subgroup ↥(twistedE6RootGroup F σ)} (hA : GLAIsBmax p A) :
    Nat.card A = p ^ 5 := by
  have hf1 : 1 ≤ f := by omega
  rw [hA.2.1, glaTwoLocalRank_twistedE6RootGroup_eq_five hf1 σ hF hσ hp hp5 hpq]

private theorem exists_twoGroup_normalizing_of_not_stdVanishes
    {G₀ : Type} [Group G₀] [Finite G₀] {A : Subgroup G₀} {d : G₀}
    (hV : ¬ StdVanishes A d) :
    ∃ T : Subgroup G₀, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      A ≤ Subgroup.normalizer (T : Set G₀) ∧
      stdLayer d ≤ Subgroup.normalizer (T : Set G₀) := by
  obtain ⟨T, hTne, hT2, hTN⟩ := not_not.mp hV
  refine ⟨T, hTne, hT2, le_sup_right.trans hTN, ?_⟩
  exact ((le_closureIn_self (stdLayer d) (Subgroup.normalizer (A : Set G₀))).trans
    le_sup_left).trans hTN

private theorem exists_conj_levi_of_normalizes_root
    {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup ↥(twistedE6RootGroup F σ)} {d : ↥(twistedE6RootGroup F σ)}
    {T : Subgroup ↥(twistedE6RootGroup F σ)} (hTne : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hAN : A ≤ Subgroup.normalizer (T : Set ↥(twistedE6RootGroup F σ)))
    (hKN : stdLayer d ≤ Subgroup.normalizer (T : Set ↥(twistedE6RootGroup F σ)))
    (hAp : IsPGroup p A) :
    ∃ (g : ↥(twistedE6RootGroup F σ)) (J : Set (Fin TwistTag.E6.foldedTag.rank))
      (y : ModGL TwistTag.E6.tag F),
      J ≠ Set.univ ∧ y ∈ graphFixedParabolic TwistTag.E6 F σ.toRingHom J ∧
      (A.map (MulAut.conj g).toMonoidHom).map (twistedE6RootGroup F σ).subtype ≤
        graphFixedParabolic TwistTag.E6 F σ.toRingHom J ∧
      ((stdLayer d).map (MulAut.conj g).toMonoidHom).map
        (twistedE6RootGroup F σ).subtype ≤ graphFixedParabolic TwistTag.E6 F σ.toRingHom J ∧
      ((A.map (MulAut.conj g).toMonoidHom).map
        (twistedE6RootGroup F σ).subtype).map (MulAut.conj y).toMonoidHom ≤
        graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J := by
  have hf1 : 1 ≤ f := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmodel : TwistedChevalleyModel ↥(twistedE6RootGroup F σ) .E6 (2 ^ f) :=
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.excTwistedModel_graphFixedRootGroup
      TwistTag.E6 Nat.prime_two hf1 F hF σ hσ
  have hHolds : CFSG.LieType.BorelTits.Holds ↥(twistedE6RootGroup F σ) 2 :=
    CFSG.LieType.BorelTits.holds_of_twistedChevalleyModel (p := 2) (f := f) hf1 hmodel
  obtain ⟨g, J, hJ, hNle⟩ :=
    exists_conj_normalizer_le_graphFixedParabolic (t := TwistTag.E6) (K := F) (σ := σ)
      hHolds hTne hT2
  have hAgP : (A.map (MulAut.conj g).toMonoidHom).map
      (twistedE6RootGroup F σ).subtype ≤ graphFixedParabolic TwistTag.E6 F σ.toRingHom J :=
    (Subgroup.map_mono (Subgroup.map_mono hAN)).trans hNle
  have hKgP : ((stdLayer d).map (MulAut.conj g).toMonoidHom).map
      (twistedE6RootGroup F σ).subtype ≤ graphFixedParabolic TwistTag.E6 F σ.toRingHom J :=
    (Subgroup.map_mono (Subgroup.map_mono hKN)).trans hNle
  have hEp : IsPGroup p ((A.map (MulAut.conj g).toMonoidHom).map
      (twistedE6RootGroup F σ).subtype) := (hAp.map _).map _
  obtain ⟨y, hyP, hyL⟩ :=
    exists_conj_le_graphFixedParabolicLevi (t := TwistTag.E6) (K := F) σ J hp hp2 hAgP hEp
  exact ⟨g, J, y, hJ, hyP, hAgP, hKgP, hyL⟩

private theorem subset_twE6MaxA5_of_card_eq_pow_five
    {f : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {J : Set (Fin TwistTag.E6.foldedTag.rank)} (hJ : J ≠ Set.univ)
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J)
    (hEel : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 5) :
    J ⊆ twE6MaxA5 := by
  by_contra hJA
  have h1 :=
    card_le_pow_four_graphFixedParabolicLevi_of_not_subset hF σ hσ hp hp5 hpq J hJ hJA hE hEel
  have h2 : p ^ 4 < p ^ 5 := Nat.pow_lt_pow_right (by have := hp.one_lt; omega) (by norm_num)
  rw [hEcard] at h1
  omega

theorem map_stdLayer_le_graphFixedParabolicLevi
    {F : Type} [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F)
    (J : Set (Fin TwistTag.E6.foldedTag.rank))
    {p : ℕ} {A : Subgroup ↥(twistedE6RootGroup F σ)} {d : ↥(twistedE6RootGroup F σ)}
    (hd : IsStdElt p A d)
    (hdL : (twistedE6RootGroup F σ).subtype d ∈
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J)
    (hKP : (stdLayer d).map (twistedE6RootGroup F σ).subtype ≤
      graphFixedParabolic TwistTag.E6 F σ.toRingHom J) :
    (stdLayer d).map (twistedE6RootGroup F σ).subtype ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomp0 : IsComponentOf (stdLayer d)
      (Subgroup.centralizer ({d} : Set ↥(twistedE6RootGroup F σ))) := hd.2.2.2.1
  have hcomp1 : IsComponentOf ((stdLayer d).map (twistedE6RootGroup F σ).subtype)
      ((Subgroup.centralizer ({d} : Set ↥(twistedE6RootGroup F σ))).map
        (twistedE6RootGroup F σ).subtype) :=
    (Y10F.isComponentOf_map_iff (twistedE6RootGroup F σ).subtype_injective).2 hcomp0
  rw [CFSG.ComponentClassification.CatFC.map_centralizer_subtype_eq_inf] at hcomp1
  have hcomp3 : IsComponentOf ((stdLayer d).map (twistedE6RootGroup F σ).subtype)
      (Subgroup.centralizer ({(twistedE6RootGroup F σ).subtype d} :
        Set (ModGL TwistTag.E6.tag F)) ⊓ graphFixedParabolic TwistTag.E6 F σ.toRingHom J) := by
    have h := CFSG.HardMathSupport.Timmesfeld.Proving.isComponentOf_inf_of_le hcomp1 hKP
    rwa [inf_assoc, inf_eq_right.2 (le_trans inf_le_right
      (graphFixedParabolic_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom) (J := J)))] at h
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQn, hLP, huniq, -, -, -, -, hQgrp, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors (t := TwistTag.E6) (K := F) σ J
  have hQ2 : IsPGroup 2 (graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J) := hQgrp 2
  have hQs : Group.IsSolvable ↥(graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J) := by
    haveI := hQ2.isNilpotent
    infer_instance
  exact le_of_isComponentOf_centralizer_inf hQP hLP hQn huniq hQs hdL hcomp3

private lemma not_dvd_two_pow_sub_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ f + 1) : ¬ p ∣ 2 ^ f - 1 := by
  intro hdiv
  have hdvd : p ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hpq hdiv
  have hsub : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  rw [hsub] at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)

private theorem map_le_su6Levi_of_isPGroup
    {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {J : Set (Fin TwistTag.E6.foldedTag.rank)} (hJsub : J ⊆ twE6MaxA5)
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J)
    (hEp : IsPGroup p E) : E ≤ su6Levi σ.toRingHom := by
  have hf1 : 1 ≤ f := by omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨k, hkfield, hkalg, hkcard⟩ := exists_subfield_twE6 hf1 hF
  letI : Field k := hkfield
  letI : Algebra k F := hkalg
  have hA5le : graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ≤
      parabolicLevi TwistTag.E6.tag F setA ⊓ graphFixedRootGroup TwistTag.E6 F σ.toRingHom := by
    rw [graphFixedParabolicLevi, twE6MaxA5_eq_foldedSetA, orbitUnion_foldedSetA]
  exact le_su6Levi_of_isPGroup (σ := σ.toRingHom) hf1 hkcard hF hσ hp
    (not_dvd_two_pow_sub_one hp hp2 hpq)
    (hE.trans ((graphFixedParabolicLevi_mono hJsub).trans hA5le)) hEp

private theorem map_le_su6Levi_of_isQuasisimple
    {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {J : Set (Fin TwistTag.E6.foldedTag.rank)} (hJsub : J ⊆ twE6MaxA5)
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J)
    (hq : CFSG.IsQuasisimple ↥E) : E ≤ su6Levi σ.toRingHom := by
  have hf1 : 1 ≤ f := by omega
  obtain ⟨k, hkfield, hkalg, hkcard⟩ := exists_subfield_twE6 hf1 hF
  letI : Field k := hkfield
  letI : Algebra k F := hkalg
  have hA5le : graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ≤
      parabolicLevi TwistTag.E6.tag F setA ⊓ graphFixedRootGroup TwistTag.E6 F σ.toRingHom := by
    rw [graphFixedParabolicLevi, twE6MaxA5_eq_foldedSetA, orbitUnion_foldedSetA]
  exact le_su6Levi_of_isQuasisimple (σ := σ.toRingHom) hf1 hkcard hF hσ
    (hE.trans ((graphFixedParabolicLevi_mono hJsub).trans hA5le)) hq

theorem exists_conj_stdElt_le_levi
    {F : Type} [Field F] (σ : F ≃+* F) {p : ℕ}
    {A : Subgroup ↥(twistedE6RootGroup F σ)} {d : ↥(twistedE6RootGroup F σ)}
    (hA : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 5) (hd : IsStdElt p A d)
    {J : Set (Fin TwistTag.E6.foldedTag.rank)} {g : ↥(twistedE6RootGroup F σ)}
    {y : ModGL TwistTag.E6.tag F}
    (hyP : y ∈ graphFixedParabolic TwistTag.E6 F σ.toRingHom J)
    (hKgP : ((stdLayer d).map (MulAut.conj g).toMonoidHom).map
      (twistedE6RootGroup F σ).subtype ≤ graphFixedParabolic TwistTag.E6 F σ.toRingHom J)
    (hyL : ((A.map (MulAut.conj g).toMonoidHom).map
      (twistedE6RootGroup F σ).subtype).map (MulAut.conj y).toMonoidHom ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J) :
    ∃ c : ↥(twistedE6RootGroup F σ),
      IsStdElt p (A.map (MulAut.conj c).toMonoidHom) ((MulAut.conj c) d) ∧
      IsElemAbelian p (A.map (MulAut.conj c).toMonoidHom) ∧
      Nat.card (A.map (MulAut.conj c).toMonoidHom) = p ^ 5 ∧
      (A.map (MulAut.conj c).toMonoidHom).map (twistedE6RootGroup F σ).subtype ≤
        graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ∧
      (stdLayer ((MulAut.conj c) d)).map (twistedE6RootGroup F σ).subtype ≤
        graphFixedParabolic TwistTag.E6 F σ.toRingHom J := by
  classical
  have hyC : y ∈ twistedE6RootGroup F σ :=
    graphFixedParabolic_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom) (J := J) hyP
  refine ⟨⟨y, hyC⟩ * g, isStdElt_map (MulAut.conj _) hd,
    (Y10F.isElemAbelian_map_iff_of_injective (MulAut.conj _).injective A).2 hA, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hAcard]
  · rw [map_conj_mul_subtype A g hyC]
    exact hyL
  · rw [stdLayer_map_mulEquiv, map_conj_mul_subtype (stdLayer d) g hyC]
    refine (Subgroup.map_mono hKgP).trans ?_
    rintro - ⟨z, hz, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      mul_mem (mul_mem hyP hz) (inv_mem hyP)

private theorem stdExtendsN_of_conj_levi
    {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {A : Subgroup ↥(twistedE6RootGroup F σ)} {d : ↥(twistedE6RootGroup F σ)}
    (hA : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 5) (hd : IsStdElt p A d)
    {J : Set (Fin TwistTag.E6.foldedTag.rank)} (hJsub : J ⊆ twE6MaxA5)
    {g : ↥(twistedE6RootGroup F σ)} {y : ModGL TwistTag.E6.tag F}
    (hyP : y ∈ graphFixedParabolic TwistTag.E6 F σ.toRingHom J)
    (hKgP : ((stdLayer d).map (MulAut.conj g).toMonoidHom).map
      (twistedE6RootGroup F σ).subtype ≤ graphFixedParabolic TwistTag.E6 F σ.toRingHom J)
    (hyL : ((A.map (MulAut.conj g).toMonoidHom).map
      (twistedE6RootGroup F σ).subtype).map (MulAut.conj y).toMonoidHom ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J) :
    StdExtendsN p A d := by
  obtain ⟨c, hd', hA'el, hA'card, hA'L, hK'P⟩ :=
    exists_conj_stdElt_le_levi σ hA hAcard hd hyP hKgP hyL
  have hK'L : (stdLayer ((MulAut.conj c) d)).map
      (twistedE6RootGroup F σ).subtype ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J :=
    map_stdLayer_le_graphFixedParabolicLevi σ J hd'
      (hA'L (Subgroup.mem_map_of_mem _ hd'.1)) hK'P
  have hA'su6 : (A.map (MulAut.conj c).toMonoidHom).map
      (twistedE6RootGroup F σ).subtype ≤ su6Levi σ.toRingHom :=
    map_le_su6Levi_of_isPGroup hf hF σ hσ hp hp5 hpq hJsub hA'L
      ((IsPGroup.of_card hA'card).map (twistedE6RootGroup F σ).subtype)
  have hq' : CFSG.IsQuasisimple ↥((stdLayer ((MulAut.conj c) d)).map
      (twistedE6RootGroup F σ).subtype) :=
    CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective _ (twistedE6RootGroup F σ).subtype
        (twistedE6RootGroup F σ).subtype_injective).symm
      ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mpr hd'.2.2.2.1.2.2)
  have hK'su6 : (stdLayer ((MulAut.conj c) d)).map
      (twistedE6RootGroup F σ).subtype ≤ su6Levi σ.toRingHom :=
    map_le_su6Levi_of_isQuasisimple hf hF σ hσ hJsub hK'L hq'
  exact (stdExtendsN_map_iff (MulAut.conj c)).1
    (stdExtendsN_of_le_su6Levi hf hF σ hσ hp hp5 hpq hA'el hA'card hd' hA'su6 hK'su6)

private theorem exists_conj_levi_subset_A5
    {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    {A : Subgroup ↥(twistedE6RootGroup F σ)} {d : ↥(twistedE6RootGroup F σ)}
    (hA : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 5)
    (hd : IsStdElt p A d) (hV : ¬ StdVanishes A d) :
    ∃ (g : ↥(twistedE6RootGroup F σ)) (J : Set (Fin TwistTag.E6.foldedTag.rank))
      (y : ModGL TwistTag.E6.tag F),
      J ⊆ twE6MaxA5 ∧ y ∈ graphFixedParabolic TwistTag.E6 F σ.toRingHom J ∧
      ((stdLayer d).map (MulAut.conj g).toMonoidHom).map
        (twistedE6RootGroup F σ).subtype ≤ graphFixedParabolic TwistTag.E6 F σ.toRingHom J ∧
      ((A.map (MulAut.conj g).toMonoidHom).map
        (twistedE6RootGroup F σ).subtype).map (MulAut.conj y).toMonoidHom ≤
        graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨T, hTne, hT2, hAN, hKN⟩ := exists_twoGroup_normalizing_of_not_stdVanishes hV
  obtain ⟨g, J, y, hJ, hyP, -, hKgP, hyL⟩ :=
    exists_conj_levi_of_normalizes_root hf hF σ hσ hp hp2 hTne hT2 hAN hKN
      (IsPGroup.of_card hAcard)
  have hEel : IsElemAbelian p ((A.map (MulAut.conj g).toMonoidHom).map
      (twistedE6RootGroup F σ).subtype) :=
    (Y10F.isElemAbelian_map_iff_of_injective
      (twistedE6RootGroup F σ).subtype_injective _).2
      ((Y10F.isElemAbelian_map_iff_of_injective (MulAut.conj g).injective A).2 hA)
  have hEcard : Nat.card ((A.map (MulAut.conj g).toMonoidHom).map
      (twistedE6RootGroup F σ).subtype) = p ^ 5 := by
    rw [Subgroup.card_map_of_injective (twistedE6RootGroup F σ).subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hAcard]
  have hEyel : IsElemAbelian p (((A.map (MulAut.conj g).toMonoidHom).map
      (twistedE6RootGroup F σ).subtype).map (MulAut.conj y).toMonoidHom) :=
    (Y10F.isElemAbelian_map_iff_of_injective (MulAut.conj y).injective _).2 hEel
  have hEycard : Nat.card (((A.map (MulAut.conj g).toMonoidHom).map
      (twistedE6RootGroup F σ).subtype).map (MulAut.conj y).toMonoidHom) = p ^ 5 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hEcard]
  exact ⟨g, J, y,
    subset_twE6MaxA5_of_card_eq_pow_five hF σ hσ hp hp5 hpq hJ hyL hEyel hEycard,
    hyP, hKgP, hyL⟩

theorem modelFactO_twistedE6 {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1) :
    ModelFactO p ↥(twistedE6RootGroup F σ) := by
  classical
  intro A d hA hd
  haveI : CharP F 2 := charP_two_of_card (by omega : 1 ≤ f) hF
  have hAcard : Nat.card A = p ^ 5 := card_eq_pow_five_of_isBmax hf hF σ hσ hp hp5 hpq hA
  by_cases hV : StdVanishes A d
  · exact Or.inl hV
  right
  obtain ⟨g, J, y, hJsub, hyP, hKgP, hyL⟩ :=
    exists_conj_levi_subset_A5 hf hF σ hσ hp hp5 hpq hA.1 hAcard hd hV
  exact stdExtendsN_of_conj_levi hf hF σ hσ hp hp5 hpq hA.1 hAcard hd hJsub hyP hKgP hyL

theorem i173OOn_famTwE6 : I173OOn famTwE6 := by
  intro p Ω _ _ S B N D K x lab hcfg hlab hfam hmark
  obtain ⟨F, hF, hFin, σ, hcard, hσ, hpq, hp5, hn, hZ, ⟨M⟩⟩ :=
    exists_model_twE6 hcfg hlab hfam hmark
  letI : Field F := hF
  letI : Finite F := hFin
  exact concl_of_modelFactO hcfg M hZ
    (modelFactO_twistedE6 hn hcard σ hσ hcfg.prime hp5 hpq)

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
