module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourSc
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourNonInner
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoModel

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Minuscule.MinData (toWeight reflectWeight)
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Sc


private theorem e6W0FourWord_foldl_reflectWeight (l : Fin Tag.E6.rank) :
    e6W0FourWord.foldl (fun ν j => reflectWeight j ν) (Pi.single l 1) =
      -(Pi.single (e6RhoFour l) 1 : Fin Tag.E6.rank → ℤ) := by
  fin_cases l <;> decide +kernel

private theorem foldr_e6StarS_w0 {k : Type} [Field k] (v : Fin Tag.E6.rank → kˣ) :
    e6W0FourWord.foldr e6StarS v = fun l => (v (e6RhoFour l))⁻¹ := by
  funext l
  have h1 : e6WtEval (e6W0FourWord.foldr e6StarS v) (Pi.single l 1) =
      e6W0FourWord.foldr e6StarS v l := by
    simp [e6WtEval, Pi.single_apply]
  rw [← h1, e6WtEval_foldr, e6W0FourWord_foldl_reflectWeight]
  simp [e6WtEval, Pi.single_apply, zpow_neg]

private theorem twE6Two_sigma_minTorus {k : Type} [Field k] (θ : k →+* k)
    (u : Fin Tag.E6.rank → kˣ) :
    TwistedE6.sigma k θ (minTorus e6Data_valid k u) =
      minTorus e6Data_valid k (fun l => Units.map θ.toMonoidHom (u (e6RhoFour l))) := by
  induction u using CFSG.LieType.Chevalley.ExceptionalCover.torusVec_induction with
  | h1 =>
    have e : (fun l => Units.map θ.toMonoidHom ((1 : Fin Tag.E6.rank → kˣ) (e6RhoFour l))) = 1 := by
      funext l
      simp
    rw [map_one, map_one, e, map_one]
  | hmul t t' ht ht' =>
    have e : (fun l => Units.map θ.toMonoidHom ((t * t') (e6RhoFour l))) =
        (fun l => Units.map θ.toMonoidHom (t (e6RhoFour l))) *
          fun l => Units.map θ.toMonoidHom (t' (e6RhoFour l)) := by
      funext l
      simp
    rw [map_mul, map_mul, ht, ht', e, map_mul]
  | hsingle a s =>
    have e : (fun l => Units.map θ.toMonoidHom
        ((Pi.mulSingle a s : Fin Tag.E6.rank → kˣ) (e6RhoFour l))) =
        Pi.mulSingle (e6RhoFour a) (Units.map θ.toMonoidHom s) := by
      funext l
      by_cases hl : l = e6RhoFour a
      · subst hl
        simp [e6RhoFour_apply_apply]
      · have : e6RhoFour l ≠ a := fun h => hl (by rw [← h, e6RhoFour_apply_apply])
        simp [Pi.mulSingle_eq_of_ne hl, Pi.mulSingle_eq_of_ne this]
    rw [e, minTorus_mulSingle, minTorus_mulSingle, TwistedE6.sigma_hm]
    rfl

@[expose] noncomputable def twE6NSc (k : Type) [Field k] : e6Data_valid.minGroup k :=
  e6NWord k e6W0FourWord

@[expose] noncomputable def twistSc {k : Type} [Field k] (θ : k →+* k) :
    e6Data_valid.minGroup k →* e6Data_valid.minGroup k :=
  (MulAut.conj (twE6NSc k)).toMonoidHom.comp (TwistedE6.sigma k θ)

private theorem twistSc_apply {k : Type} [Field k] (θ : k →+* k) (g : e6Data_valid.minGroup k) :
    twistSc θ g = twE6NSc k * TwistedE6.sigma k θ g * (twE6NSc k)⁻¹ := rfl

theorem twistSc_minTorus {k : Type} [Field k] (θ : k →+* k) (u : Fin Tag.E6.rank → kˣ) :
    twistSc θ (minTorus e6Data_valid k u) =
      minTorus e6Data_valid k (fun l => (Units.map θ.toMonoidHom (u l))⁻¹) := by
  rw [twistSc_apply, twE6Two_sigma_minTorus, twE6NSc, nWord_conj_minTorus, foldr_e6StarS_w0]
  congr 1
  funext l
  simp [e6RhoFour_apply_apply]

private theorem twistSc_minTorus_of_pow_three {k : Type} [Field k] (θ : k →+* k)
    (hθ : ∀ c, θ c = c ^ 2) (u : Fin Tag.E6.rank → kˣ) (hu : ∀ l, u l ^ 3 = 1) :
    twistSc θ (minTorus e6Data_valid k u) = minTorus e6Data_valid k u := by
  rw [twistSc_minTorus]
  congr 1
  funext l
  apply inv_eq_of_mul_eq_one_left
  apply Units.ext
  have h3 : ((u l : kˣ) : k) ^ 3 = 1 := by
    have := congrArg Units.val (hu l)
    simpa using this
  change ((u l : kˣ) : k) * θ ((u l : kˣ) : k) = 1
  rw [hθ, ← pow_succ']
  exact h3

private theorem twistSc_center {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ c = c ^ 2)
    {z : e6Data_valid.minGroup k} (hz : z ∈ Subgroup.center (e6Data_valid.minGroup k)) :
    twistSc θ z = z := by
  obtain ⟨v, rfl, hv3⟩ := exists_minTorus_of_mem_center_E6 hz
  exact twistSc_minTorus_of_pow_three θ hθ v hv3

private theorem sigma_minBC {k k' : Type} [Field k] [Field k'] (ι : k →+* k') (θ : k →+* k)
    (θ' : k' →+* k') (h : θ'.comp ι = ι.comp θ) (g : e6Data_valid.minGroup k) :
    TwistedE6.sigma k' θ' (minBC e6Data_valid ι g) =
      minBC e6Data_valid ι (TwistedE6.sigma k θ g) := by
  have hh : (TwistedE6.sigma k' θ').comp (minBC e6Data_valid ι) =
      (minBC e6Data_valid ι).comp (TwistedE6.sigma k θ) := by
    refine MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e6Data_valid k) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · simp only [MonoidHom.comp_apply]
      rw [minBC_xm_single, TwistedE6.sigma_xm_single, TwistedE6.sigma_xm_single, minBC_xm_single]
      exact congrArg _ (RingHom.congr_fun h c)
    · simp only [MonoidHom.comp_apply]
      rw [minBC_xm_neg_single, TwistedE6.sigma_xm_neg_single, TwistedE6.sigma_xm_neg_single,
        minBC_xm_neg_single]
      exact congrArg _ (RingHom.congr_fun h c)
  exact DFunLike.congr_fun hh g

section Finite

variable {k : Type} [Field k] [Finite k] [CharP k 2]

private theorem e6Isogeny_twE6NSc :
    ((e6Isogeny k (twE6NSc k) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      canonicalRep (coxeterSystem Tag.E6) k e6W0Four := by
  rw [twE6NSc, e6Isogeny_nWord, e6W0Four,
    CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_wordProd_of_charTwo]

theorem e6Isogeny_twistSc (θ : k →+* k) (g : e6Data_valid.minGroup k) :
    ((e6Isogeny k (twistSc θ g) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) k twE6W0) θ
        ((e6Isogeny k g : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) := by
  have hn : ((e6Isogeny k (twE6NSc k) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) k twE6W0 := e6Isogeny_twE6NSc
  rw [twistSc_apply, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, hn, e6Isogeny_sigma θ g]
  rfl

end Finite

section Lift

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_twistSc_fixed_lift (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {k : Type} [Field k] [Finite k] [CharP k 2] (ι : K →+* k)
    {g₀ : ModGL Tag.E6 k} (hg₀ : g₀ ∈ adjointGroup Tag.E6 k)
    (hLang : twistHom TwistTag.E6 k (iterateFrobenius k 2 1) g₀ =
      g₀ * canonicalRep (coxeterSystem Tag.E6) k e6W0Four)
    {t : ModGL Tag.E6 K} (ht : t ∈ twistedE6RootGroup K σ) :
    ∃ sl : e6Data_valid.minGroup k, twistSc (iterateFrobenius k 2 1) sl = sl ∧
      ((e6Isogeny k sl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
        g₀⁻¹ * baseChangeGL ι t * g₀ := by
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hder, -, -, -⟩ :=
    CFSG.LieType.Chevalley.twisted_E6_all_characteristic_exact_automorphism_normal_form
      Nat.prime_two le_rfl K hK2 σ hσ2
  have hθθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    have h := FiniteField.pow_card c
    rw [← Nat.card_eq_fintype_card, hK] at h
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ, ← pow_mul]
    exact h
  have hk4 : 4 ≤ Nat.card K := hK.ge
  obtain ⟨⟨sK, hsKfix⟩, hsK⟩ : t ∈ (e6IsogenyFixed σ.toRingHom).range := by
    rw [range_e6IsogenyFixed σ.toRingHom hθθ hk4, hder]
    exact ht
  have hsKσ : TwistedE6.sigma K σ.toRingHom sK = sK := (TwistedE6.mem_fixedGroup _).1 hsKfix
  have hsKt : ((e6Isogeny K sK : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = t := hsK
  obtain ⟨gt, hgt⟩ := e6Isogeny_surjective k ⟨g₀, hg₀⟩
  have hgtπ : ((e6Isogeny k gt : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = g₀ := by rw [hgt]
  obtain ⟨θk, hθkdef⟩ : ∃ θk : k →+* k, θk = iterateFrobenius k 2 1 := ⟨_, rfl⟩
  rw [← hθkdef] at hLang ⊢
  have hθkc : ∀ c, θk c = c ^ 2 := fun c => by rw [hθkdef, iterateFrobenius_two_one]
  have hcomp : θk.comp ι = ι.comp σ.toRingHom := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, hθkc, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ,
      map_pow]
  have hn : ((e6Isogeny k (twE6NSc k) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      canonicalRep (coxeterSystem Tag.E6) k e6W0Four := e6Isogeny_twE6NSc
  have hσgt : ((e6Isogeny k (TwistedE6.sigma k θk gt) : adjointGroup Tag.E6 k) :
      ModGL Tag.E6 k) = g₀ * canonicalRep (coxeterSystem Tag.E6) k e6W0Four := by
    rw [e6Isogeny_sigma θk gt, ← hLang, ← hgtπ]
    rfl
  obtain ⟨z, hz⟩ : ∃ z, z = (gt * twE6NSc k)⁻¹ * TwistedE6.sigma k θk gt := ⟨_, rfl⟩
  have hzc : z ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [hz, map_mul, map_inv, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
      hgtπ, hn, hσgt]
    group
  have hσg : TwistedE6.sigma k θk gt = gt * twE6NSc k * z := by rw [hz]; group
  have hzc' : ∀ w : e6Data_valid.minGroup k, z⁻¹ * w * z = w := fun w => by
    have h := Subgroup.mem_center_iff.1 hzc w
    calc z⁻¹ * w * z = z⁻¹ * (w * z) := by group
      _ = z⁻¹ * (z * w) := by rw [h]
      _ = w := by group
  refine ⟨gt⁻¹ * minBC e6Data_valid ι sK * gt, ?_, ?_⟩
  · rw [twistSc_apply, map_mul, map_mul, map_inv, hσg, sigma_minBC ι σ.toRingHom θk hcomp, hsKσ]
    calc twE6NSc k * ((gt * twE6NSc k * z)⁻¹ * minBC e6Data_valid ι sK *
          (gt * twE6NSc k * z)) * (twE6NSc k)⁻¹ =
        twE6NSc k * (z⁻¹ * ((twE6NSc k)⁻¹ * gt⁻¹ * minBC e6Data_valid ι sK * gt * twE6NSc k) * z) *
          (twE6NSc k)⁻¹ := by group
      _ = twE6NSc k * ((twE6NSc k)⁻¹ * gt⁻¹ * minBC e6Data_valid ι sK * gt * twE6NSc k) *
          (twE6NSc k)⁻¹ := by rw [hzc']
      _ = gt⁻¹ * minBC e6Data_valid ι sK * gt := by group
  · rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hgtπ,
      e6Isogeny_minBC, hsKt]

end Lift

section Core

variable
  {k : Type} [Field k] [Finite k] [CharP k 2]

theorem mem_toralRootGroup_of_commute_lift (u : Fin Tag.E6.rank → kˣ)
    (hu3 : ∀ j, e6RootParams u j ^ 3 = 1) {c : ModGL Tag.E6 k}
    (hcC : c ∈ toralCentralizer Tag.E6 k (e6RootParams u)) {cl : e6Data_valid.minGroup k}
    (hcl : ((e6Isogeny k cl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = c)
    (hcomm : cl * minTorus e6Data_valid k u = minTorus e6Data_valid k u * cl) :
    c ∈ toralRootGroup Tag.E6 k (e6RootParams u) := by
  obtain ⟨w, hw, h₃, hh₃, u₃, hu₃, v₃, hv₃, hdec⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors Tag.E6 k (e6RootParams u)).1 c hcC
  have hdec' : ((e6Isogeny k cl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      h₃ * u₃ * canonicalRep (coxeterSystem Tag.E6) k w * v₃ := by rw [hcl, hdec]
  have hshift := rootChar_e6Shift_of_commute_lift u hcomm hh₃
    (rootSpan_mono Set.inter_subset_left hu₃) (rootSpan_mono Set.inter_subset_left hv₃) hdec' hw
  have hwS : w ∈ kernelReflectionGroup (e6RootParams u) :=
    mem_kernelReflectionGroup_of_e6Shift (e6RootParams u) hu3 hw hshift
  have hnM : canonicalRep (coxeterSystem Tag.E6) k w ∈
      toralRootGroup Tag.E6 k (e6RootParams u) := by
    have hk := kernelReflectionGroup_le_ker (K := k) (e6RootParams u)
      (show (⟨w, hw⟩ : rootCharStabilizerSubgroup (e6RootParams u)) ∈
        (kernelReflectionGroup (e6RootParams u)).subgroupOf
          (rootCharStabilizerSubgroup (e6RootParams u)) from hwS)
    rw [MonoidHom.mem_ker, weylToralQuotientHom_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hk
    exact hk
  rw [hdec]
  exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left hh₃)
    (Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hu₃))) hnM)
    (Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hv₃))

private theorem twistSc_cocycle_rel (θ : k →+* k) (hθ : ∀ c, θ c = c ^ 2) (u : Fin Tag.E6.rank → kˣ)
    {yl sl : e6Data_valid.minGroup k} (hsl : twistSc θ sl = sl) {z₀ : e6Data_valid.minGroup k}
    (hz₀ : z₀ ∈ Subgroup.center (e6Data_valid.minGroup k))
    (hsyz : sl = yl * minTorus e6Data_valid k u * yl⁻¹ * z₀) :
    (yl⁻¹ * twistSc θ yl) * twistSc θ (minTorus e6Data_valid k u) * (yl⁻¹ * twistSc θ yl)⁻¹ =
      minTorus e6Data_valid k u := by
  have hz : twistSc θ z₀ = z₀ := twistSc_center θ hθ hz₀
  have h1 := congrArg (twistSc θ) hsyz
  rw [hsl, map_mul, map_mul, map_mul, map_inv, hz] at h1
  have h2 : yl * minTorus e6Data_valid k u * yl⁻¹ * z₀ =
      twistSc θ yl * twistSc θ (minTorus e6Data_valid k u) * (twistSc θ yl)⁻¹ * z₀ := by
    rw [← hsyz]
    exact h1
  have h3 := mul_right_cancel h2
  calc (yl⁻¹ * twistSc θ yl) * twistSc θ (minTorus e6Data_valid k u) *
        (yl⁻¹ * twistSc θ yl)⁻¹ =
      yl⁻¹ * (twistSc θ yl * twistSc θ (minTorus e6Data_valid k u) * (twistSc θ yl)⁻¹) * yl := by
        group
    _ = yl⁻¹ * (yl * minTorus e6Data_valid k u * yl⁻¹) * yl := by rw [h3]
    _ = minTorus e6Data_valid k u := by group

theorem rootChar_e6RootParams_e6Omega3 (u : Fin Tag.E6.rank → kˣ) :
    rootChar (e6RootParams u) e6Omega3 = u 0 ^ 3 := by
  rw [← e6WtEval_toWeight, toWeight_e6Omega3]
  simp [e6WtEval, Pi.single_apply]

private theorem twistSc_minTorus_eq_inv_sq (θ : k →+* k) (hθ : ∀ c, θ c = c ^ 2)
    (u : Fin Tag.E6.rank → kˣ) :
    twistSc θ (minTorus e6Data_valid k u) = (minTorus e6Data_valid k u)⁻¹ ^ 2 := by
  rw [twistSc_minTorus, ← map_inv, ← map_pow]
  congr 1
  funext l
  apply Units.ext
  simp [hθ]

theorem twE6Two_cocycle_mem (u : Fin Tag.E6.rank → kˣ) (ha3 : ∀ j, e6RootParams u j ^ 3 = 1)
    (hu : (∀ l, u l ^ 3 = 1) ∨ rootChar (e6RootParams u) e6Omega3 ≠ 1)
    {y : ModGL Tag.E6 k} (hy : y ∈ adjointGroup Tag.E6 k) {sl : e6Data_valid.minGroup k}
    (hsl : twistSc (iterateFrobenius k 2 1) sl = sl)
    (hsy : ((e6Isogeny k sl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      y * rootDiagUnit Tag.E6 (e6RootParams u) * y⁻¹) :
    (∀ l, u l ^ 3 = 1) ∧ y⁻¹ * twE6TwoF k y ∈ toralRootGroup Tag.E6 k (e6RootParams u) := by
  have hθ : ∀ c, iterateFrobenius k 2 1 c = c ^ 2 := fun c => iterateFrobenius_two_one c
  obtain ⟨yl, hyl⟩ := e6Isogeny_surjective k ⟨y, hy⟩
  have hylπ : ((e6Isogeny k yl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = y := by rw [hyl]
  obtain ⟨T, hT⟩ : ∃ T, T = minTorus e6Data_valid k u := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = rootDiagUnit Tag.E6 (e6RootParams u) := ⟨_, rfl⟩
  have hTπ : ((e6Isogeny k T : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = d := by
    rw [hT, hd]; exact e6Isogeny_minTorus u
  rw [← hd] at hsy
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, z₀ = (yl * T * yl⁻¹)⁻¹ * sl := ⟨_, rfl⟩
  have hz₀c : z₀ ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [hz₀, map_mul, map_inv, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hylπ, hTπ, hsy]
    group
  have hsyz : sl = yl * T * yl⁻¹ * z₀ := by rw [hz₀]; group
  have hrel := twistSc_cocycle_rel (iterateFrobenius k 2 1) hθ u hsl hz₀c (hT ▸ hsyz)
  rw [← hT] at hrel
  obtain ⟨c, hc⟩ : ∃ c, c = y⁻¹ * twE6TwoF k y := ⟨_, rfl⟩
  obtain ⟨cl, hcl⟩ : ∃ cl, cl = yl⁻¹ * twistSc (iterateFrobenius k 2 1) yl := ⟨_, rfl⟩
  rw [← hcl] at hrel
  have hclπ : ((e6Isogeny k cl : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = c := by
    rw [hcl, hc, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hylπ,
      e6Isogeny_twistSc, hylπ]
    rfl
  have hcG : c ∈ adjointGroup Tag.E6 k := by
    rw [← hclπ]
    exact (e6Isogeny k cl).2
  have hd3 : d ^ 3 = 1 := by
    rw [hd, rootDiagUnit_pow]
    have : e6RootParams u ^ 3 = 1 := funext fun j => by simpa using ha3 j
    rw [this, rootDiagUnit_one]
  have hFd : twE6TwoF k d = d := by
    rw [hd, twE6TwoF_rootDiagUnit, ← hd, inv_pow]
    exact inv_eq_of_mul_eq_one_left (by rw [← pow_succ']; exact hd3)
  have hFs : twE6TwoF k (y * d * y⁻¹) = y * d * y⁻¹ := by
    rw [← hsy]
    have := e6Isogeny_twistSc (iterateFrobenius k 2 1) sl
    rw [hsl] at this
    exact this.symm
  rw [map_mul, map_mul, map_inv, hFd] at hFs
  have hcd : c * d * c⁻¹ = d := by
    calc c * d * c⁻¹ = y⁻¹ * (twE6TwoF k y * d * (twE6TwoF k y)⁻¹) * y := by rw [hc]; group
      _ = y⁻¹ * (y * d * y⁻¹) * y := by rw [hFs]
      _ = d := by group
  have hcC : c ∈ toralCentralizer Tag.E6 k (e6RootParams u) := by
    refine mem_toralCentralizer.2 ⟨hcG, ?_⟩
    rw [← hd]
    have h1 : c * d = d * c := mul_inv_eq_iff_eq_mul.1 hcd
    calc d * c * d⁻¹ = c * d * d⁻¹ := by rw [← h1]
      _ = c := by group
  rcases hu with hu3 | hnon
  · have hTT : twistSc (iterateFrobenius k 2 1) T = T := by
      rw [hT]
      exact twistSc_minTorus_of_pow_three _ hθ u hu3
    rw [hTT] at hrel
    have hcomm : cl * T = T * cl := mul_inv_eq_iff_eq_mul.1 hrel
    exact ⟨hu3, hc ▸ mem_toralRootGroup_of_commute_lift u ha3 hcC hclπ (by rw [← hT]; exact hcomm)⟩
  · exfalso
    have hW : rootCharStabilizerSubgroup (e6RootParams u) ≤
        kernelReflectionGroup (e6RootParams u) := fun w hw =>
      mem_kernelReflectionGroup_of_nonInner (e6RootParams u) ha3 hnon hw
    have hcM : c ∈ toralRootGroup Tag.E6 k (e6RootParams u) := by
      rw [← toralCentralizer_eq_toralRootGroup_of_stabilizer_le Tag.E6 _ (e6RootParams u) hW]
      exact hcC
    have hcomm : cl * T = T * cl := by
      rw [hT]
      exact commute_minTorus_of_mem_toralRootGroup u hcM hclπ
    have hTF : twistSc (iterateFrobenius k 2 1) T = T⁻¹ ^ 2 := by
      rw [hT]
      exact twistSc_minTorus_eq_inv_sq _ hθ u
    rw [hTF] at hrel
    have hcomm2 : cl * T⁻¹ ^ 2 * cl⁻¹ = T⁻¹ ^ 2 := by
      have h1 : cl * T * cl⁻¹ = T := by rw [hcomm]; group
      calc cl * T⁻¹ ^ 2 * cl⁻¹ = (cl * T * cl⁻¹)⁻¹ ^ 2 := by rw [pow_two, pow_two]; group
        _ = T⁻¹ ^ 2 := by rw [h1]
    rw [hcomm2] at hrel
    have hT3 : T ^ 3 = 1 := by
      calc T ^ 3 = T ^ 2 * T := by rw [pow_succ]
        _ = T ^ 2 * T⁻¹ ^ 2 := by rw [hrel]
        _ = 1 := by rw [pow_two, pow_two]; group
    have hu3 : u ^ 3 = 1 := by
      apply minTorus_injective e6Data_valid k
      rw [map_pow, map_one, ← hT]
      exact hT3
    have hu3' : ∀ l, u l ^ 3 = 1 := fun l => by simpa using congrFun hu3 l
    apply hnon
    rw [rootChar_e6RootParams_e6Omega3]
    exact hu3' 0

end Core

section LangTw

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

private theorem familyGroup_unit_eq (a : Fin Tag.E6.rank → Lˣ) :
    familyGroup (K := L) (fun _ : Unit => a) = toralRootGroup Tag.E6 L a := by
  have h : familyKernel (fun _ : Unit => a) = rootCharKernel a := by
    ext α
    simp [familyKernel, rootCharKernel]
  rw [familyGroup, toralRootGroup, h]

theorem toralRootGroup_lang_tw (a : Fin Tag.E6.rank → Lˣ) :
    ∀ c ∈ toralRootGroup Tag.E6 L a, ∃ z ∈ toralRootGroup Tag.E6 L a,
      z⁻¹ * twE6TwoF L z = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFrs : Function.Surjective (iterateFrobenius L 2 1) := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (by norm_num : 0 < 2)
    exact ⟨x, by rw [iterateFrobenius_two_one, hx]⟩
  have himg : (fun α => twE6W0 • permLattice TwistTag.E6.perm α) ''
      familyKernel (fun _ : Unit => a) = familyKernel (fun _ : Unit => a) := by
    ext β
    constructor
    · rintro ⟨α, ⟨hα, hαa⟩, rfl⟩
      refine ⟨?_, fun i => ?_⟩
      · dsimp only
        rw [twE6W0_smul_permLattice]
        exact IsRoot.neg hα
      · dsimp only
        rw [twE6W0_smul_permLattice]
        exact (rootChar_neg_vec_E6Four (τ := Tag.E6) a α).trans
          (by have h : rootChar a α = 1 := hαa i; rw [h, inv_one])
    · rintro ⟨hβ, hβa⟩
      refine ⟨-β, ⟨IsRoot.neg hβ, fun i => ?_⟩, ?_⟩
      · exact (rootChar_neg_vec_E6Four (τ := Tag.E6) a β).trans
          (by have h : rootChar a β = 1 := hβa i; rw [h, inv_one])
      · simp only
        rw [twE6W0_smul_permLattice, neg_neg]
  have hF : ∀ g : ModGL Tag.E6 L, frobTwistGL Tag.E6 L 2 1
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0 * diagramMap TwistTag.E6 L) g =
        twE6TwoF L g := fun g => rfl
  have hst : ∀ g ∈ familyGroup (K := L) (fun _ : Unit => a),
      frobTwistGL Tag.E6 L 2 1 (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0 *
        diagramMap TwistTag.E6 L) g ∈ familyGroup (K := L) (fun _ : Unit => a) := by
    intro g hg
    rw [hF]
    exact twFrob_mem_familyGroup TwistTag.E6 hFrs twE6W0 (fun _ : Unit => a) himg hg
  intro c hc
  rw [← familyGroup_unit_eq] at hc ⊢
  obtain ⟨z, hz, hzc⟩ := lang_familyGroup_of_mapsTo 2 (fun _ : Unit => a) 1 le_rfl _ hst c hc
  refine ⟨z, hz, ?_⟩
  rw [← hzc, ← hF]
  rfl

end LangTw

end Sc

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
