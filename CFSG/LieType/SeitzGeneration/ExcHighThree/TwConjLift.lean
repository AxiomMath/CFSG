module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourRigid
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagLift

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.LieType.Steinberg.Minuscule.MinData (toWeight reflectWeight)

set_option linter.unusedSectionVars false

section Sc


theorem twl_foldl_reflectWeight_w0 (l : Fin Tag.E6.rank) :
    e6W0FourWord.foldl (fun ν j => reflectWeight j ν) (Pi.single l 1) =
      -(Pi.single (e6RhoFour l) 1 : Fin Tag.E6.rank → ℤ) := by
  fin_cases l <;> decide +kernel

theorem twl_foldr_e6StarS_w0 {k : Type} [Field k] (v : Fin Tag.E6.rank → kˣ) :
    e6W0FourWord.foldr e6StarS v = fun l => (v (e6RhoFour l))⁻¹ := by
  funext l
  have h1 : e6WtEval (e6W0FourWord.foldr e6StarS v) (Pi.single l 1) =
      e6W0FourWord.foldr e6StarS v l := by
    simp [e6WtEval, Pi.single_apply]
  rw [← h1, e6WtEval_foldr, twl_foldl_reflectWeight_w0]
  simp [e6WtEval, Pi.single_apply, zpow_neg]

theorem twl_sigma_minTorus {k : Type} [Field k] (θ : k →+* k) (u : Fin Tag.E6.rank → kˣ) :
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

theorem twl_sigma_minBC {k k' : Type} [Field k] [Field k'] (ι : k →+* k') (θ : k →+* k)
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

theorem twl_center_inv {k : Type} [Field k] {u : Fin Tag.E6.rank → kˣ}
    (hz : minTorus e6Data_valid k u ∈ Subgroup.center (e6Data_valid.minGroup k)) :
    ∀ l, u (e6RhoFour l) = (u l)⁻¹ := by
  have hc := Subgroup.mem_center_iff.1 hz (e6NWord k e6W0FourWord)
  have h1 : e6NWord k e6W0FourWord * minTorus e6Data_valid k u * (e6NWord k e6W0FourWord)⁻¹ =
      minTorus e6Data_valid k u := by
    rw [hc]
    group
  rw [nWord_conj_minTorus, twl_foldr_e6StarS_w0] at h1
  intro l
  have h2 := congrFun (minTorus_injective e6Data_valid k h1) (e6RhoFour l)
  simp only [e6RhoFour_apply_apply] at h2
  exact h2.symm

theorem twl_sigma_center {k : Type} [Field k] (θ : k →+* k) (q : ℕ) (hθ : ∀ c, θ c = c ^ q)
    (hq : q % 3 = 2) {z : e6Data_valid.minGroup k}
    (hz : z ∈ Subgroup.center (e6Data_valid.minGroup k)) :
    TwistedE6.sigma k θ z = z := by
  obtain ⟨u, rfl, hu3⟩ := exists_minTorus_of_mem_center_E6 hz
  have hinv := twl_center_inv hz
  rw [twl_sigma_minTorus]
  congr 1
  funext l
  rw [hinv l, map_inv]
  obtain ⟨t, ht⟩ : ∃ t : ℕ, q = 3 * t + 2 := ⟨q / 3, by omega⟩
  have h3 : (u l) ^ 3 = 1 := hu3 l
  have e1 : Units.map θ.toMonoidHom (u l) = (u l) ^ q := by
    apply Units.ext
    simp [hθ]
  rw [e1]
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ, ht, show 3 * t + 2 + 1 = 3 * (t + 1) by ring, pow_mul, h3, one_pow]

theorem tw_fixed_lift_class_trivial {k : Type} [Field k] [Finite k] (θ : k →+* k) (q : ℕ)
    (hθq : ∀ c : k, θ c = c ^ q) (hq : q % 3 = 2)
    (g0 : ModGL Tag.E6 k) (hg0 : g0 ∈ adjointGroup Tag.E6 k) {ω : List (Fin Tag.E6.rank)}
    (hω : (coxeterSystem Tag.E6).IsReduced ω)
    (hF : twistHom TwistTag.E6 k θ g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) k ((coxeterSystem Tag.E6).wordProd ω))
    (u : Fin Tag.E6.rank → kˣ) (x : e6Data_valid.minGroup k)
    (hx : TwistedE6.sigma k θ x = x)
    (hπ : ((e6Isogeny k x : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      g0 * rootDiagUnit Tag.E6 (e6RootParams u) * g0⁻¹) :
    ω.foldr e6StarS (fun l => Units.map θ.toMonoidHom (u (e6RhoFour l))) = u := by
  classical
  obtain ⟨g1, hg1⟩ := e6Isogeny_surjective k ⟨g0, hg0⟩
  have hg1' : ((e6Isogeny k g1 : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = g0 :=
    congrArg Subtype.val hg1
  set Fb := TwistedE6.sigma k θ with hFb
  set n1 := e6NWord k ω with hn1
  have hn1' : ((e6Isogeny k n1 : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      canonicalRep (coxeterSystem Tag.E6) k ((coxeterSystem Tag.E6).wordProd ω) :=
    e6Isogeny_nWord_eq_canonicalRep hω
  have hFg1 : ((e6Isogeny k (Fb g1) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      twistHom TwistTag.E6 k θ g0 := by
    rw [hFb, e6Isogeny_sigma θ g1]
    show twistHom TwistTag.E6 k θ ((e6Isogeny k g1 : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = _
    rw [hg1']
  set ζ0 := (g1 * n1)⁻¹ * Fb g1 with hζ0
  have hζ0ker : ζ0 ∈ Subgroup.center ↥(e6Data_valid.minGroup k) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [hζ0, map_mul, map_inv, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
      hg1', hn1', hFg1, hF]
    simp
  have hF1 : Fb g1 = g1 * n1 * ζ0 := by rw [hζ0]; group
  have hc0 := Subgroup.mem_center_iff.1 hζ0ker
  set T0 := minTorus e6Data_valid k u with hT0
  set yh := g1 * T0 * g1⁻¹ with hyh
  have hyhπ : ((e6Isogeny k yh : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      g0 * rootDiagUnit Tag.E6 (e6RootParams u) * g0⁻¹ := by
    rw [hyh, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hg1', hT0, e6Isogeny_minTorus]
  set ζ' := yh⁻¹ * x with hζ'
  have hζ'ker : ζ' ∈ Subgroup.center ↥(e6Data_valid.minGroup k) := by
    refine mem_center_of_isogeny_eq_one ?_
    rw [hζ', map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hyhπ, hπ]
    group
  have hFζ' : Fb ζ' = ζ' := twl_sigma_center θ q hθq hq hζ'ker
  have hxeq : x = yh * ζ' := by rw [hζ']; group
  have h1 : Fb yh * ζ' = yh * ζ' := by
    calc Fb yh * ζ' = Fb yh * Fb ζ' := by rw [hFζ']
      _ = Fb (yh * ζ') := (map_mul _ _ _).symm
      _ = Fb x := by rw [← hxeq]
      _ = x := hx
      _ = yh * ζ' := hxeq
  have h2 : Fb yh = yh := mul_right_cancel h1
  have hFyh : Fb yh = g1 * (n1 * Fb T0 * n1⁻¹) * g1⁻¹ := by
    rw [hyh, map_mul, map_mul, map_inv, hF1]
    calc g1 * n1 * ζ0 * Fb T0 * (g1 * n1 * ζ0)⁻¹
        = g1 * n1 * (ζ0 * Fb T0 * ζ0⁻¹) * n1⁻¹ * g1⁻¹ := by group
      _ = g1 * n1 * Fb T0 * n1⁻¹ * g1⁻¹ := by
        rw [show ζ0 * Fb T0 * ζ0⁻¹ = Fb T0 by rw [← hc0 (Fb T0)]; group]
      _ = g1 * (n1 * Fb T0 * n1⁻¹) * g1⁻¹ := by group
  rw [hFyh, hyh] at h2
  have h3 : n1 * Fb T0 * n1⁻¹ = T0 := mul_left_cancel (mul_right_cancel h2)
  rw [hFb, hT0, twl_sigma_minTorus, hn1, nWord_conj_minTorus] at h3
  exact minTorus_injective e6Data_valid k h3

theorem twl_e6StarS_map {k k' : Type} [Field k] [Field k'] (ψ : k →+* k')
    (j : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → kˣ) :
    e6StarS j (fun l => Units.map ψ.toMonoidHom (v l)) =
      fun l => Units.map ψ.toMonoidHom (e6StarS j v l) := by
  funext l
  simp only [e6StarS, Pi.mul_apply, map_mul, map_prod, map_zpow]
  congr 1
  by_cases hl : l = j
  · subst hl
    simp
  · simp [Pi.mulSingle_eq_of_ne hl]

theorem twl_foldr_e6StarS_map {k k' : Type} [Field k] [Field k'] (ψ : k →+* k')
    (ω : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → kˣ) :
    ω.foldr e6StarS (fun l => Units.map ψ.toMonoidHom (v l)) =
      fun l => Units.map ψ.toMonoidHom (ω.foldr e6StarS v l) := by
  induction ω with
  | nil => rfl
  | cons j ω ih => rw [List.foldr_cons, List.foldr_cons, ih, twl_e6StarS_map]

theorem tw_exists_sigma_fixed_lift {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {y : ModGL Tag.E6 K} (hy : y ∈ twistedE6RootGroup K σ) :
    ∃ s : e6Data_valid.minGroup K, TwistedE6.sigma K σ.toRingHom s = s ∧
      ((e6Isogeny K s : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = y := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hder, -, -, -⟩ :=
    CFSG.LieType.Chevalley.twisted_E6_all_characteristic_exact_automorphism_normal_form
      hp hf K hK σ hσ
  have hθθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    have h := FiniteField.pow_card c
    rw [← Nat.card_eq_fintype_card, hK] at h
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
    rw [← pow_mul, ← sq]
    exact h
  have hk4 : 4 ≤ Nat.card K := by
    rw [hK]
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    nlinarith
  obtain ⟨⟨sK, hsKfix⟩, hsK⟩ : y ∈ (e6IsogenyFixed σ.toRingHom).range := by
    rw [range_e6IsogenyFixed σ.toRingHom hθθ hk4, hder]
    exact hy
  exact ⟨sK, (TwistedE6.mem_fixedGroup _).1 hsKfix, hsK⟩

theorem tw_class_trivial_of_mem {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 2)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (p ^ f))
    (g0 : ModGL Tag.E6 (AlgebraicClosure K)) (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    {ω : List (Fin Tag.E6.rank)} (hω : (coxeterSystem Tag.E6).IsReduced ω)
    (hF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
        ((coxeterSystem Tag.E6).wordProd ω))
    (u : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) {y : ModGL Tag.E6 K}
    (hy : y ∈ twistedE6RootGroup K σ)
    (hyu : baseChangeGL (algebraMap K (AlgebraicClosure K)) y =
      g0 * rootDiagUnit Tag.E6 (e6RootParams u) * g0⁻¹) :
    ω.foldr e6StarS (fun l => Units.map Fr.toMonoidHom (u (e6RhoFour l))) = u := by
  classical
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI hKp : CharP K p :=
    charP_of_card_eq_prime_pow (f := f * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : CharP L p := charP_of_injective_algebraMap ι.injective p
  obtain ⟨Eg, hEg⟩ := exists_finset_descent hg0C
  obtain ⟨K₃, hK₃, hSK₃, hιK₃⟩ := exists_finite_subfield_of_finset (K := K)
    (Eg ∪ Finset.univ.image fun l => ((u l : Lˣ) : L))
  haveI : Finite K₃ := hK₃
  have hgK : (Eg : Set L) ⊆ K₃ := fun x hx =>
    hSK₃ (Finset.mem_coe.2 (Finset.mem_union_left _ hx))
  have huK : ∀ l, ((u l : Lˣ) : L) ∈ K₃ := fun l =>
    hSK₃ (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨l, Finset.mem_univ l, rfl⟩)))
  have hιK : ∀ x : K, ι x ∈ K₃ := fun x => hιK₃ ⟨x, rfl⟩
  obtain ⟨g3, hg3C, hg3⟩ := hEg K₃ hgK
  obtain ⟨u₃, hu₃⟩ : ∃ u₃ : Fin Tag.E6.rank → K₃ˣ,
      ∀ l, Units.map K₃.subtype.toMonoidHom (u₃ l) = u l :=
    ⟨fun l => Units.mk0 ⟨((u l : Lˣ) : L), huK l⟩
      fun h0 => (u l).ne_zero (congrArg Subtype.val h0), fun l => Units.ext rfl⟩
  obtain ⟨ι₃, hιι⟩ : ∃ ι₃ : K →+* K₃, K₃.subtype.comp ι₃ = ι :=
    ⟨ι.codRestrict K₃ hιK, RingHom.ext fun x => rfl⟩
  haveI : CharP K₃ p := Subfield.charP K₃ p
  obtain ⟨φ, hφdef⟩ : ∃ φ : K₃ →+* K₃, φ = iterateFrobenius K₃ p f := ⟨_, rfl⟩
  have hφq : ∀ c : K₃, φ c = c ^ (p ^ f) := fun c => by
    rw [hφdef, iterateFrobenius_def]
  have hφL : K₃.subtype.comp φ = Fr.comp K₃.subtype := by
    ext c
    simp only [RingHom.comp_apply, Subfield.coe_subtype, hφq, hFr, map_pow]
  have hφι : φ.comp ι₃ = ι₃.comp σ.toRingHom := by
    ext c
    simp only [RingHom.comp_apply, hφq, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ,
      map_pow]
  have hbcinj : Function.Injective (baseChangeGL (τ := Tag.E6) K₃.subtype) :=
    baseChangeGL_injective K₃.subtype
  have hbcι : ∀ x : ModGL Tag.E6 K, baseChangeGL K₃.subtype (baseChangeGL ι₃ x) =
      baseChangeGL ι x := fun x => by
    rw [baseChangeGL_baseChangeGL, hιι]
  have hF₃ : twistHom TwistTag.E6 K₃ φ g3 =
      g3 * canonicalRep (coxeterSystem Tag.E6) K₃ ((coxeterSystem Tag.E6).wordProd ω) := by
    apply hbcinj
    have h1 := twistHom_baseChangeGL (t := TwistTag.E6) K₃.subtype
      (σk := φ) (σ := Fr) (by rw [hφL]) g3
    have e1 : baseChangeGL K₃.subtype (twistHom TwistTag.E6 K₃ φ g3) =
        twistHom TwistTag.E6 L Fr g0 :=
      h1.symm.trans (congrArg (twistHom TwistTag.E6 L Fr) hg3)
    have e2 : baseChangeGL K₃.subtype
        (g3 * canonicalRep (coxeterSystem Tag.E6) K₃ ((coxeterSystem Tag.E6).wordProd ω)) =
        g0 * canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω) := by
      rw [map_mul, baseChangeGL_canonicalRep, hg3]
    exact e1.trans (hF.trans e2.symm)
  obtain ⟨s, hsσ, hsπ⟩ := tw_exists_sigma_fixed_lift hp hf hK σ hσ hy
  set x := minBC e6Data_valid ι₃ s with hxdef
  have hxF : TwistedE6.sigma K₃ φ x = x := by
    rw [hxdef, twl_sigma_minBC ι₃ σ.toRingHom φ hφι, hsσ]
  have hxπ : ((e6Isogeny K₃ x : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) =
      baseChangeGL ι₃ y := by
    rw [hxdef, e6Isogeny_minBC, hsπ]
  have hπ : ((e6Isogeny K₃ x : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) =
      g3 * rootDiagUnit Tag.E6 (e6RootParams u₃) * g3⁻¹ := by
    apply hbcinj
    rw [hxπ, hbcι, hyu, map_mul, map_mul, map_inv, hg3, baseChangeGL_rootDiagUnit]
    have hd : (fun i => Units.map K₃.subtype.toMonoidHom (e6RootParams u₃ i)) =
        e6RootParams u := by
      rw [← e6RootParams_map']
      congr 1
      funext l
      exact hu₃ l
    rw [hd]
  have key := tw_fixed_lift_class_trivial φ (p ^ f) hφq hq g3 hg3C hω hF₃ u₃ x hxF hπ
  have hv : (fun l => Units.map Fr.toMonoidHom (u (e6RhoFour l))) =
      fun l => Units.map K₃.subtype.toMonoidHom (Units.map φ.toMonoidHom (u₃ (e6RhoFour l))) := by
    funext l'
    rw [← hu₃ (e6RhoFour l')]
    apply Units.ext
    have := RingHom.congr_fun hφL ((u₃ (e6RhoFour l') : K₃ˣ) : K₃)
    simpa using this.symm
  funext l
  rw [hv, twl_foldr_e6StarS_map, key]
  exact hu₃ l

end Sc

end CFSG.LieType.SeitzGeneration.ExcHighThree
