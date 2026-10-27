module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoSc
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourFusion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCore

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

section Fusion


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conj_toral_E6_three
    {s : ModGL Tag.E6 (AlgebraicClosure K)} (hs : s ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hs3 : s ^ 3 = 1) :
    ∃ y ∈ adjointGroup Tag.E6 (AlgebraicClosure K), ∃ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
      (∀ i, a i ^ 3 = 1) ∧ s = y * rootDiagUnit Tag.E6 a * y⁻¹ := by
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : ((Subgroup.zpowers s : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) :
      Set (ModGL Tag.E6 (AlgebraicClosure K))).Finite :=
    (finite_zpowers).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hs3⟩)
  have hexp : ∀ x ∈ Subgroup.zpowers s, x ^ 3 = 1 := by
    rintro _ ⟨n, rfl⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs3, one_zpow]
  have hzle : Subgroup.zpowers s ≤ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [Subgroup.zpowers_le]
    exact hs
  obtain ⟨c₁, hc₁, hc₁m⟩ := exists_conj_le_monomial_bar (ℓ := 2) (p := 3)
    (by norm_num) (isAlgebraic_zmod_algebraicClosure_of_finite K 2) hzle hfin hexp
  have hn := hc₁m s (Subgroup.mem_zpowers s)
  have hn3 : (c₁ * s * c₁⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hs3, mul_one, mul_inv_cancel]
  have hL3 : ringChar (AlgebraicClosure K) ≠ 3 := by
    rw [ringChar.eq (AlgebraicClosure K) 2]
    norm_num
  obtain ⟨c₂, hc₂, hc₂t⟩ := exists_conj_mem_torusGroup_of_mem_monomial
    monomialToralAt_E6_three hL3 hn hn3
  obtain ⟨t, ht⟩ : ∃ t, t = (c₂ * c₁) * s * (c₂ * c₁)⁻¹ := ⟨_, rfl⟩
  have ht' : t = c₂ * (c₁ * s * c₁⁻¹) * c₂⁻¹ := by rw [ht]; group
  have htT : t ∈ torusGroup Tag.E6 (AlgebraicClosure K) := ht' ▸ hc₂t
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom htT
  have hta : t = rootDiagUnit Tag.E6 a := ha.symm
  have ht3 : t ^ 3 = 1 := by rw [ht, conj_pow, hs3, mul_one, mul_inv_cancel]
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    have h1 : rootDiagUnitHom Tag.E6 (AlgebraicClosure K) (a ^ 3) =
        rootDiagUnitHom Tag.E6 (AlgebraicClosure K) 1 := by
      rw [map_pow, map_one]
      change (rootDiagUnit Tag.E6 a) ^ 3 = 1
      rw [← hta, ht3]
    have h2 := rootDiagUnit_injective (τ := Tag.E6) (K := AlgebraicClosure K) h1
    intro i
    have := congrFun h2 i
    simpa using this
  refine ⟨(c₂ * c₁)⁻¹, inv_mem (mul_mem hc₂ hc₁), a, ha3, ?_⟩
  rw [← hta, ht]
  group

private theorem baseChangeGL_twFrob (t : TwistTag) {k L : Type} [Field k] [Field L] (ι : k →+* L)
    (θ : k →+* k) (θ' : L →+* L) (h : θ'.comp ι = ι.comp θ) (n g : ModGL t.tag k) :
    baseChangeGL ι (twFrob t n θ g) = twFrob t (baseChangeGL ι n) θ' (baseChangeGL ι g) := by
  have h1 := units_map_entrywiseHom_baseChangeGL ι θ' θ h g
  unfold twFrob twistHom
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
    baseChangeGL_diagramMap, h1]

theorem baseChangeGL_twE6TwoF {k L : Type} [Field k] [CharP k 2] [Field L] [CharP L 2]
    (ι : k →+* L) (g : ModGL Tag.E6 k) :
    baseChangeGL ι (twE6TwoF k g) = twE6TwoF L (baseChangeGL ι g) := by
  have hcomp : (iterateFrobenius L 2 1).comp ι = ι.comp (iterateFrobenius k 2 1) :=
    RingHom.ext fun c => by
      simp only [RingHom.comp_apply, iterateFrobenius_two_one, map_pow]
  have h := baseChangeGL_twFrob TwistTag.E6 ι (iterateFrobenius k 2 1) (iterateFrobenius L 2 1)
    hcomp (canonicalRep (coxeterSystem TwistTag.E6.tag) k twE6W0) g
  rw [baseChangeGL_canonicalRep] at h
  exact h

private theorem e6InnerParam_pow_three {k : Type} [Field k] {ω : kˣ} (hω : ω ^ 3 = 1)
    (y : Fin 5 → ZMod 3) (l : Fin Tag.E6.rank) : e6InnerParam ω y l ^ 3 = 1 := by
  have h : e6InnerParam ω y ^ 3 = 1 := by
    unfold e6InnerParam
    rw [← powMonoidHom_apply, map_list_prod, List.map_map]
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    simp only [Function.comp_apply, powMonoidHom_apply]
    rw [← pow_mul, mul_comm, pow_mul]
    have : (Pi.mulSingle (⟨i.val, lt_of_lt_of_le i.2 (by decide)⟩ : Fin Tag.E6.rank) ω :
        Fin Tag.E6.rank → kˣ) ^ 3 = 1 := by
      rw [← Pi.mulSingle_pow, hω, Pi.mulSingle_one]
    rw [this, one_pow]
  have := congrFun h l
  simpa using this

private theorem twE6Two_exists_finite_subfield_descent (S : Finset (AlgebraicClosure K))
    {y g₀ : ModGL Tag.E6 (AlgebraicClosure K)} (hy : y ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg₀ : g₀ ∈ adjointGroup Tag.E6 (AlgebraicClosure K)) :
    ∃ k : Subfield (AlgebraicClosure K), Finite k ∧ (∀ x ∈ S, x ∈ k) ∧
      (∀ c : K, algebraMap K (AlgebraicClosure K) c ∈ k) ∧
      (∃ y₃ ∈ adjointGroup Tag.E6 k, baseChangeGL k.subtype y₃ = y) ∧
      (∃ g₃ ∈ adjointGroup Tag.E6 k, baseChangeGL k.subtype g₃ = g₀) := by
  classical
  obtain ⟨Ey, hEy⟩ := exists_finset_descent hy
  obtain ⟨Eg, hEg⟩ := exists_finset_descent hg₀
  obtain ⟨k, hk, hEk, hιk⟩ := exists_finite_subfield_of_finset (K := K) (S ∪ Ey ∪ Eg)
  have hmem : ∀ x ∈ S ∪ Ey ∪ Eg, x ∈ k := fun x hx => hEk (Finset.mem_coe.2 hx)
  refine ⟨k, hk, fun x hx => hmem x (Finset.mem_union_left _ (Finset.mem_union_left _ hx)),
    fun c => hιk ⟨c, rfl⟩, hEy k fun x hx => hmem x ?_, hEg k fun x hx => hmem x ?_⟩
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  · exact Finset.mem_union_right _ hx

private theorem exists_twE6TwoModel_conj_of_cocycle {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]
    {y : ModGL Tag.E6 L} (hy : y ∈ adjointGroup Tag.E6 L) (a : Fin Tag.E6.rank → Lˣ)
    (hc : y⁻¹ * twE6TwoF L y ∈ toralRootGroup Tag.E6 L a) :
    ∃ u' ∈ twE6TwoModel L, u' * rootDiagUnit Tag.E6 a * u'⁻¹ =
      y * rootDiagUnit Tag.E6 a * y⁻¹ := by
  obtain ⟨z, hz, hzc⟩ := toralRootGroup_lang_tw a _ hc
  obtain ⟨hzG, hzd⟩ := mem_toralCentralizer.1 (toralRootGroup_le a hz)
  have hFz : twE6TwoF L z = z * (y⁻¹ * twE6TwoF L y) := by rw [← hzc]; group
  have hadj : y * z⁻¹ ∈ adjointGroup Tag.E6 L := mul_mem hy (inv_mem hzG)
  refine ⟨y * z⁻¹, ⟨hadj, ?_⟩, ?_⟩
  · change twE6TwoF L (y * z⁻¹) = y * z⁻¹
    rw [map_mul, map_inv, hFz]
    group
  · have h1 : rootDiagUnit Tag.E6 a * z = z * rootDiagUnit Tag.E6 a := by
      rw [mul_inv_eq_iff_eq_mul] at hzd
      exact hzd
    calc y * z⁻¹ * rootDiagUnit Tag.E6 a * (y * z⁻¹)⁻¹ =
        y * (z⁻¹ * (rootDiagUnit Tag.E6 a * z)) * y⁻¹ := by group
      _ = y * (z⁻¹ * (z * rootDiagUnit Tag.E6 a)) * y⁻¹ := by rw [h1]
      _ = y * rootDiagUnit Tag.E6 a * y⁻¹ := by group

private theorem twE6Two_baseChangeGL_twistHom (t : TwistTag) {k L : Type} [Field k] [Field L]
    (ι : k →+* L) (θ : k →+* k) (θ' : L →+* L) (h : θ'.comp ι = ι.comp θ) (g : ModGL t.tag k) :
    baseChangeGL ι (twistHom t k θ g) = twistHom t L θ' (baseChangeGL ι g) := by
  have h1 := units_map_entrywiseHom_baseChangeGL ι θ' θ h g
  unfold twistHom
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
    baseChangeGL_diagramMap, h1]

private theorem twistHom_lang_descent (t : TwistTag) {k L : Type} [Field k] [Field L] (ι : k →+* L)
    (θ : k →+* k) (θ' : L →+* L) (h : θ'.comp ι = ι.comp θ) {g₃ n₃ : ModGL t.tag k}
    {g0 n0 : ModGL t.tag L} (hg : baseChangeGL ι g₃ = g0) (hn : baseChangeGL ι n₃ = n0)
    (hLang : twistHom t L θ' g0 = g0 * n0) : twistHom t k θ g₃ = g₃ * n₃ := by
  apply baseChangeGL_injective ι
  rw [twE6Two_baseChangeGL_twistHom t ι θ θ' h, hg, map_mul, hg, hn]
  exact hLang

private theorem conj_descent {τ : Tag} {k L : Type} [Field k] [Field L] (ι : k →+* L)
    {g₃ y₃ s₃ : ModGL τ k} {g0 y s0 : ModGL τ L} {a₃ : Fin τ.rank → kˣ}
    {a : Fin τ.rank → Lˣ} (hg : baseChangeGL ι g₃ = g0) (hy : baseChangeGL ι y₃ = y)
    (hs : baseChangeGL ι s₃ = s0) (ha : (fun i => Units.map ι.toMonoidHom (a₃ i)) = a)
    (h : g0⁻¹ * s0 * g0 = y * rootDiagUnit τ a * y⁻¹) :
    g₃⁻¹ * s₃ * g₃ = y₃ * rootDiagUnit τ a₃ * y₃⁻¹ := by
  apply baseChangeGL_injective ι
  rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hg, hs, hy, baseChangeGL_rootDiagUnit,
    ha]
  exact h

section Bar


private theorem twE6Two_cocycle_mem_bar (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {g0 : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) e6W0Four)
    {sK : ModGL Tag.E6 K} (hsK : sK ∈ twistedE6RootGroup K σ)
    (k : Subfield (AlgebraicClosure K)) [Finite k]
    (hKk : ∀ c : K, algebraMap K (AlgebraicClosure K) c ∈ k)
    {y₃ g₃ : ModGL Tag.E6 k} (hy₃ : y₃ ∈ adjointGroup Tag.E6 k)
    (hg₃ : g₃ ∈ adjointGroup Tag.E6 k) (hg₃0 : baseChangeGL k.subtype g₃ = g0)
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ} (u₃ : Fin Tag.E6.rank → kˣ)
    (hua : (fun j => Units.map k.subtype.toMonoidHom (e6RootParams u₃ j)) = a)
    (ha3 : ∀ j, e6RootParams u₃ j ^ 3 = 1)
    (hu : (∀ l, u₃ l ^ 3 = 1) ∨ rootChar (e6RootParams u₃) e6Omega3 ≠ 1)
    (hsy : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) sK * g0 =
      baseChangeGL k.subtype y₃ * rootDiagUnit Tag.E6 a * (baseChangeGL k.subtype y₃)⁻¹) :
    (∀ l, u₃ l ^ 3 = 1) ∧ (baseChangeGL k.subtype y₃)⁻¹ *
      twE6TwoF (AlgebraicClosure K) (baseChangeGL k.subtype y₃) ∈
        toralRootGroup Tag.E6 (AlgebraicClosure K) a := by
  have hcL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hck : CharP k 2 := Subfield.charP k 2
  obtain ⟨ι₃, hι₃⟩ : ∃ ι₃ : K →+* k, k.subtype.comp ι₃ = algebraMap K (AlgebraicClosure K) :=
    ⟨(algebraMap K (AlgebraicClosure K)).codRestrict k hKk, RingHom.ext fun _ => rfl⟩
  have hcomp : (iterateFrobenius (AlgebraicClosure K) 2 1).comp k.subtype =
      k.subtype.comp (iterateFrobenius k 2 1) := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, iterateFrobenius_two_one, map_pow]
  have hLang₃ : twistHom TwistTag.E6 k (iterateFrobenius k 2 1) g₃ =
      g₃ * canonicalRep (coxeterSystem Tag.E6) k e6W0Four :=
    twistHom_lang_descent TwistTag.E6 k.subtype (iterateFrobenius k 2 1)
      (iterateFrobenius (AlgebraicClosure K) 2 1) hcomp hg₃0
      (baseChangeGL_canonicalRep k.subtype twE6W0) hg0
  have hsy₃ : g₃⁻¹ * baseChangeGL ι₃ sK * g₃ =
      y₃ * rootDiagUnit Tag.E6 (e6RootParams u₃) * y₃⁻¹ :=
    conj_descent (τ := Tag.E6) k.subtype hg₃0 rfl
      (by rw [baseChangeGL_baseChangeGL, hι₃]) hua hsy
  obtain ⟨sl, hsl, hπ⟩ := exists_twistSc_fixed_lift hK σ hσ ι₃ hg₃ hLang₃ hsK
  obtain ⟨hu3, hcM⟩ := twE6Two_cocycle_mem u₃ ha3 hu hy₃ hsl (hπ.trans hsy₃)
  refine ⟨hu3, ?_⟩
  have h1 := baseChangeGL_mem_toralRootGroup k.subtype hcM
  rw [hua, map_mul, map_inv, baseChangeGL_twE6TwoF] at h1
  exact h1

end Bar

private theorem exists_twE6TwoModel_conj_dV {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]
    {ω : Lˣ} {s y : ModGL Tag.E6 L} (hy : y ∈ adjointGroup Tag.E6 L) {a : Fin Tag.E6.rank → Lˣ}
    (hsy : s = y * rootDiagUnit Tag.E6 a * y⁻¹)
    (hc : y⁻¹ * twE6TwoF L y ∈ toralRootGroup Tag.E6 L a) {x : Fin Tag.E6.rank → ZMod 3}
    (hax : a = torV ω x) :
    ∃ m ∈ twE6TwoModel L, m * s * m⁻¹ = dV (τ := Tag.E6) ω x := by
  obtain ⟨u', hu'M, hu'⟩ := exists_twE6TwoModel_conj_of_cocycle hy a hc
  have hu'G : u' ∈ adjointGroup Tag.E6 L := hu'M.1
  refine ⟨u'⁻¹, (twE6TwoModel L).inv_mem hu'M, ?_⟩
  have hd : dV (τ := Tag.E6) ω x = rootDiagUnit Tag.E6 a := by rw [hax]; rfl
  rw [hd, hsy, ← hu']
  group

section Final


theorem twE6TwoFusion_holds : TwE6TwoFusion := by
  classical
  intro K _ _ _ hK σ hσ g0 hg0C hg0 ω hω s hs hs3
  have hcL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  have hsM : s ∈ twE6TwoModel (AlgebraicClosure K) := twE6Two_commutator_le_model hs
  have hsG : s ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := hsM.1
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨sK, hsK⟩ := (twE6TwoEquiv hK σ hσ hg0C hg0).surjective ⟨s, hs⟩
  have hsKs : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (sK : ModGL TwistTag.E6.tag K) * g0 = s := by
    have h := coe_twE6TwoEquiv hK σ hσ hg0C hg0 sK
    rw [hsK] at h
    exact h.symm
  obtain ⟨y, hyG, a, ha3, hsy⟩ := exists_conj_toral_E6_three hsG hs3
  have hprim : IsPrimitiveRoot (ω : AlgebraicClosure K) 3 :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hω)
  have hapow : ∀ i, ∃ m : ℕ, a i = ω ^ m := fun i => by
    obtain ⟨m, -, hm⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (a i : AlgebraicClosure K))
      (by have := congrArg Units.val (ha3 i); simpa using this)
    exact ⟨m, Units.ext (by simpa using hm.symm)⟩
  choose mm hmm using hapow
  have hax : a = torV ω (fun i => (mm i : ZMod 3)) := by
    funext i
    rw [torV, ZMod.val_natCast, hmm i]
    have := pow_mod_orderOf ω (mm i)
    rw [hω] at this
    exact this.symm
  by_cases hinner : rootChar a e6Omega3 = 1
  ·
    obtain ⟨y₀, hy₀⟩ := exists_subLin_eq_of_rootChar hω (x := fun i => (mm i : ZMod 3))
      (by rw [← hax]; exact hinner)
    have hax' : a = torV ω (subLin (τ := Tag.E6) e6InnerVec y₀) := by rw [hy₀]; exact hax
    obtain ⟨k, hk, hSk, hKk, ⟨y₃, hy₃G, hy₃⟩, ⟨g₃, hg₃G, hg₃⟩⟩ :=
      twE6Two_exists_finite_subfield_descent (K := K) {(ω : AlgebraicClosure K)} hyG hg0C
    haveI : Finite k := hk
    have hωk : (ω : AlgebraicClosure K) ∈ k := hSk _ (Finset.mem_singleton_self _)
    obtain ⟨ω₃, hω₃⟩ : ∃ ω₃ : kˣ, Units.map k.subtype.toMonoidHom ω₃ = ω :=
      ⟨Units.mk0 ⟨(ω : AlgebraicClosure K), hωk⟩
        (fun h0 => ω.ne_zero (congrArg Subtype.val h0)), Units.ext rfl⟩
    have hinj : Function.Injective (Units.map k.subtype.toMonoidHom) :=
      units_map_subtype_injective k
    have hω₃3 : ω₃ ^ 3 = 1 := hinj (by rw [map_pow, hω₃, hω3, map_one])
    have hua : (fun j => Units.map k.subtype.toMonoidHom
        (e6RootParams (e6InnerParam ω₃ y₀) j)) = a := by
      rw [e6RootParams_e6InnerParam hω₃3 y₀, hax']
      funext j
      simp only [torV, map_pow, hω₃]
    have ha3' : ∀ j, e6RootParams (e6InnerParam ω₃ y₀) j ^ 3 = 1 := fun j => by
      rw [e6RootParams_e6InnerParam hω₃3 y₀, torV, ← pow_mul, mul_comm, pow_mul, hω₃3, one_pow]
    have hsy' : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (sK : ModGL TwistTag.E6.tag K) * g0 = baseChangeGL k.subtype y₃ * rootDiagUnit Tag.E6 a *
          (baseChangeGL k.subtype y₃)⁻¹ := by
      rw [hy₃, ← hsy]
      exact hsKs
    obtain ⟨-, hcM⟩ := twE6Two_cocycle_mem_bar hK σ hσ hg0
      (sK := (sK : ModGL TwistTag.E6.tag K)) sK.2 k hKk hy₃G hg₃G hg₃ (e6InnerParam ω₃ y₀) hua ha3'
      (Or.inl (e6InnerParam_pow_three hω₃3 y₀)) hsy'
    rw [hy₃] at hcM
    obtain ⟨m, hmM, hm⟩ := exists_twE6TwoModel_conj_dV hyG hsy hcM hax'
    exact ⟨m, hmM, y₀, hm⟩
  ·
    exfalso
    obtain ⟨u, hu⟩ := exists_e6RootParams_eq a
    obtain ⟨k, hk, hSk, hKk, ⟨y₃, hy₃G, hy₃⟩, ⟨g₃, hg₃G, hg₃⟩⟩ :=
      twE6Two_exists_finite_subfield_descent (K := K)
        (Finset.univ.image fun i => ((u i : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))
        hyG hg0C
    haveI : Finite k := hk
    obtain ⟨u₃, hu₃⟩ := exists_units_descent k u fun i =>
      hSk _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hua : (fun j => Units.map k.subtype.toMonoidHom (e6RootParams u₃ j)) = a := by
      rw [← e6RootParams_map, hu₃, hu]
    have hinj : Function.Injective (Units.map k.subtype.toMonoidHom) :=
      units_map_subtype_injective k
    have ha3' : ∀ j, e6RootParams u₃ j ^ 3 = 1 := fun j =>
      hinj (by rw [map_pow, congrFun hua j, map_one]; exact ha3 j)
    have hnon' : rootChar (e6RootParams u₃) e6Omega3 ≠ 1 := fun h => hinner (by
      rw [← hua, rootChar_map_tuple, h, map_one])
    have hsy' : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (sK : ModGL TwistTag.E6.tag K) * g0 = baseChangeGL k.subtype y₃ * rootDiagUnit Tag.E6 a *
          (baseChangeGL k.subtype y₃)⁻¹ := by
      rw [hy₃, ← hsy]
      exact hsKs
    obtain ⟨hu3, -⟩ := twE6Two_cocycle_mem_bar hK σ hσ hg0
      (sK := (sK : ModGL TwistTag.E6.tag K)) sK.2 k hKk hy₃G hg₃G hg₃ u₃ hua ha3' (Or.inr hnon')
      hsy'
    apply hnon'
    rw [rootChar_e6RootParams_e6Omega3]
    exact hu3 0

end Final

end Fusion

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
