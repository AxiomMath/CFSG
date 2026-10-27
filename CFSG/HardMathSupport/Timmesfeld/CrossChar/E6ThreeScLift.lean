module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Minuscule.MinData (toWeight reflectWeight toWeight_reflect toWeight_smul
  toWeight_sub)

local instance e6ScLiftNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section EndBC

variable {d : ℕ} {k k' : Type*} [Field k] [Field k'] (ι : k →+* k')

omit [Field k'] in
theorem minEnd_ext {f g : Module.End k (Fin d →₀ k)}
    (h : ∀ a : Fin d, f (Finsupp.single a 1) = g (Finsupp.single a 1)) : f = g :=
  Finsupp.lhom_ext' fun a => LinearMap.ext_ring (h a)

@[expose] def minEndBC (A : Module.End k (Fin d →₀ k)) : Module.End k' (Fin d →₀ k') :=
  Finsupp.linearCombination k' fun b => Finsupp.mapRange ι ι.map_zero (A (Finsupp.single b 1))

theorem minEndBC_single (A : Module.End k (Fin d →₀ k)) (b : Fin d) :
    minEndBC ι A (Finsupp.single b 1) = Finsupp.mapRange ι ι.map_zero (A (Finsupp.single b 1)) := by
  simp [minEndBC]

theorem mapRange_smul_ringHom (c : k) (v : Fin d →₀ k) :
    Finsupp.mapRange ι ι.map_zero (c • v) = ι c • Finsupp.mapRange ι ι.map_zero v := by
  ext a
  simp

theorem minEndBC_mapRange (A : Module.End k (Fin d →₀ k)) (v : Fin d →₀ k) :
    minEndBC ι A (Finsupp.mapRange ι ι.map_zero v) = Finsupp.mapRange ι ι.map_zero (A v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v₁ v₂ h₁ h₂ =>
    rw [Finsupp.mapRange_add ι.map_add, map_add, h₁, h₂, map_add, Finsupp.mapRange_add ι.map_add]
  | single b c =>
    have e1 : Finsupp.mapRange ι ι.map_zero (Finsupp.single b c) =
        ι c • Finsupp.single b (1 : k') := by simp
    have e2 : Finsupp.single b c = c • Finsupp.single b (1 : k) := by simp
    rw [e1, map_smul, minEndBC_single, e2, map_smul, mapRange_smul_ringHom]

theorem minEndBC_mul (A B : Module.End k (Fin d →₀ k)) :
    minEndBC ι (A * B) = minEndBC ι A * minEndBC ι B :=
  minEnd_ext fun b => by
    rw [Module.End.mul_apply, minEndBC_single, minEndBC_single, minEndBC_mapRange,
      Module.End.mul_apply]

theorem minEndBC_one : minEndBC ι (1 : Module.End k (Fin d →₀ k)) = 1 :=
  minEnd_ext fun b => by
    rw [minEndBC_single, Module.End.one_apply, Module.End.one_apply]
    simp

theorem minEndBC_add (A B : Module.End k (Fin d →₀ k)) :
    minEndBC ι (A + B) = minEndBC ι A + minEndBC ι B :=
  minEnd_ext fun b => by
    rw [LinearMap.add_apply, minEndBC_single, minEndBC_single, minEndBC_single, LinearMap.add_apply,
      Finsupp.mapRange_add ι.map_add]

theorem minEndBC_smul (c : k) (A : Module.End k (Fin d →₀ k)) :
    minEndBC ι (c • A) = ι c • minEndBC ι A :=
  minEnd_ext fun b => by
    rw [LinearMap.smul_apply, minEndBC_single, minEndBC_single, LinearMap.smul_apply,
      mapRange_smul_ringHom]

@[expose] def minEndBCHom : Module.End k (Fin d →₀ k) →* Module.End k' (Fin d →₀ k') where
  toFun := minEndBC ι
  map_one' := minEndBC_one ι
  map_mul' := minEndBC_mul ι

@[expose] def minUnitsBC : (Module.End k (Fin d →₀ k))ˣ →* (Module.End k' (Fin d →₀ k'))ˣ :=
  Units.map (minEndBCHom ι)

theorem coe_minUnitsBC (g : (Module.End k (Fin d →₀ k))ˣ) :
    ((minUnitsBC ι g : (Module.End k' (Fin d →₀ k'))ˣ) : Module.End k' (Fin d →₀ k')) =
      minEndBC ι (g : Module.End k (Fin d →₀ k)) :=
  rfl

end EndBC

section MinBC

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) {k k' : Type*} [Field k] [Field k']
  (ι : k →+* k')


include hV

theorem minEndBC_rootOp_single (i : Fin τ.rank) :
    minEndBC ι (D.rootOp k (Pi.single i 1)) = D.rootOp k' (Pi.single i 1) :=
  minEnd_ext fun a => by
    rw [minEndBC_single, hV.rootOp_single_apply (R := k), hV.rootOp_single_apply (R := k')]
    split_ifs <;> simp

theorem minEndBC_rootOp_neg_single (i : Fin τ.rank) :
    minEndBC ι (D.rootOp k (-Pi.single i 1)) = D.rootOp k' (-Pi.single i 1) :=
  minEnd_ext fun a => by
    rw [minEndBC_single, hV.rootOp_neg_single_apply (R := k), hV.rootOp_neg_single_apply (R := k')]
    split_ifs <;> simp

theorem minUnitsBC_xu_single (i : Fin τ.rank) (c : k) :
    minUnitsBC ι (hV.xu k (Pi.single i 1) c) = hV.xu k' (Pi.single i 1) (ι c) := by
  ext1
  rw [coe_minUnitsBC, hV.xu_val, hV.xu_val, minEndBC_add, minEndBC_one, minEndBC_smul,
    minEndBC_rootOp_single hV]

theorem minUnitsBC_xu_neg_single (i : Fin τ.rank) (c : k) :
    minUnitsBC ι (hV.xu k (-Pi.single i 1) c) = hV.xu k' (-Pi.single i 1) (ι c) := by
  ext1
  rw [coe_minUnitsBC, hV.xu_val, hV.xu_val, minEndBC_add, minEndBC_one, minEndBC_smul,
    minEndBC_rootOp_neg_single hV]

variable (k) in
theorem minGroup_le_closure_simple :
    hV.minGroup k ≤ Subgroup.closure {g | ∃ (i : Fin τ.rank) (c : k),
      g = hV.xu k (Pi.single i 1) c ∨ g = hV.xu k (-Pi.single i 1) c} := by
  intro x hx
  have hmem : (⟨x, hx⟩ : hV.minGroup k) ∈ Subgroup.closure {g | ∃ (i : Fin τ.rank) (c : k),
      g = hV.xm k (Pi.single i 1) c ∨ g = hV.xm k (-Pi.single i 1) c} := by
    rw [closure_xm_simple_eq_top hV k]
    exact Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem (hV.minGroup k).subtype hmem
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨g, ⟨i, c, rfl | rfl⟩, rfl⟩
  · exact ⟨i, c, Or.inl rfl⟩
  · exact ⟨i, c, Or.inr rfl⟩

theorem map_minUnitsBC_minGroup_le :
    (hV.minGroup k).map (minUnitsBC ι) ≤ hV.minGroup k' := by
  refine (Subgroup.map_mono (minGroup_le_closure_simple hV k)).trans ?_
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, ⟨i, c, rfl | rfl⟩, rfl⟩
  · rw [SetLike.mem_coe, minUnitsBC_xu_single hV]
    exact hV.xu_mem k' _ _
  · rw [SetLike.mem_coe, minUnitsBC_xu_neg_single hV]
    exact hV.xu_mem k' _ _

@[expose] def minBC : hV.minGroup k →* hV.minGroup k' :=
  ((minUnitsBC ι).comp (hV.minGroup k).subtype).codRestrict _ fun g =>
    map_minUnitsBC_minGroup_le hV ι ⟨g, g.2, rfl⟩

theorem minBC_xm_single (i : Fin τ.rank) (c : k) :
    minBC hV ι (hV.xm k (Pi.single i 1) c) = hV.xm k' (Pi.single i 1) (ι c) :=
  Subtype.ext (minUnitsBC_xu_single hV ι i c)

theorem minBC_xm_neg_single (i : Fin τ.rank) (c : k) :
    minBC hV ι (hV.xm k (-Pi.single i 1) c) = hV.xm k' (-Pi.single i 1) (ι c) :=
  Subtype.ext (minUnitsBC_xu_neg_single hV ι i c)

end MinBC

section E6


theorem e6Isogeny_minBC {k k' : Type} [Field k] [Finite k] [Field k'] [Finite k'] (ι : k →+* k')
    (g : e6Data_valid.minGroup k) :
    ((e6Isogeny k' (minBC e6Data_valid ι g) : adjointGroup Tag.E6 k') : ModGL Tag.E6 k') =
      baseChangeGL ι ((e6Isogeny k g : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) := by
  have h : (adjointGroup Tag.E6 k').subtype.comp ((e6Isogeny k').comp (minBC e6Data_valid ι)) =
      (baseChangeGL ι).comp ((adjointGroup Tag.E6 k).subtype.comp (e6Isogeny k)) := by
    refine MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e6Data_valid k) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [minBC_xm_single, e6Isogeny_xm_single, e6Isogeny_xm_single, eltElement_simpleRoot_E6,
        eltElement_simpleRoot_E6]
      exact (baseChangeGL_xUnit ι i c).symm
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [minBC_xm_neg_single, e6Isogeny_xm_neg_single, e6Isogeny_xm_neg_single,
        eltElement_neg_simpleRoot_E6, eltElement_neg_simpleRoot_E6]
      exact (baseChangeGL_yUnit ι i c).symm
  exact DFunLike.congr_fun h g

variable {k : Type} [Field k] [Finite k]

theorem e6Isogeny_nt_eq (a : Fin Tag.E6.rank) (s : kˣ) :
    ((e6Isogeny k (e6Data_valid.nt k a s) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      weylElt Tag.E6 k a s := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  change ((e6Isogeny k (e6Data_valid.xm k (Pi.single a 1) s *
    e6Data_valid.xm k (-Pi.single a 1) (-((s⁻¹ : kˣ) : k)) *
      e6Data_valid.xm k (Pi.single a 1) s) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = _
  rw [map_mul, map_mul, e6Isogeny_xm_single, e6Isogeny_xm_neg_single, eltElement_simpleRoot_E6,
    eltElement_neg_simpleRoot_E6]
  rfl

theorem e6Isogeny_hm_eq (a : Fin Tag.E6.rank) (s : kˣ) :
    ((e6Isogeny k (e6Data_valid.hm k a s) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 (fun j => s ^ Tag.cartan Tag.E6 a j) := by
  rw [← torusElt_eq_rootDiagUnit]
  change ((e6Isogeny k (e6Data_valid.nt k a s * (e6Data_valid.nt k a 1)⁻¹) :
    adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = _
  rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, e6Isogeny_nt_eq, e6Isogeny_nt_eq,
    CFSG.Blueprint.Chevalley.weylElt_inv]
  rfl

@[expose] def e6RootParams {K : Type} [Field K] (u : Fin Tag.E6.rank → Kˣ) :
    Fin Tag.E6.rank → Kˣ :=
  fun j => ∏ l, u l ^ Tag.cartan Tag.E6 l j

theorem e6Isogeny_minTorus (u : Fin Tag.E6.rank → kˣ) :
    ((e6Isogeny k (minTorus e6Data_valid k u) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 (e6RootParams u) := by
  induction u using CFSG.LieType.Chevalley.ExceptionalCover.torusVec_induction with
  | h1 =>
    rw [map_one, map_one, OneMemClass.coe_one]
    have e : e6RootParams (1 : Fin Tag.E6.rank → kˣ) = 1 := by
      funext j
      simp [e6RootParams]
    rw [e, rootDiagUnit_one]
  | hmul t t' ht ht' =>
    rw [map_mul, map_mul, Subgroup.coe_mul, ht, ht', ← rootDiagUnit_mul]
    congr 1
    funext j
    simp only [e6RootParams, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
  | hsingle a s =>
    rw [minTorus_mulSingle, e6Isogeny_hm_eq]
    congr 1
    funext j
    simp only [e6RootParams]
    rw [Finset.prod_eq_single a (fun l _ hl => by rw [Pi.mulSingle_eq_of_ne hl, one_zpow])
      (fun h => absurd (Finset.mem_univ a) h), Pi.mulSingle_eq_same]

@[expose] def e6NWord (k : Type) [Field k] (ω : List (Fin Tag.E6.rank)) :
    e6Data_valid.minGroup k :=
  (ω.map (e6Data_valid.nm k)).prod

theorem e6NWord_cons (k : Type) [Field k] (j : Fin Tag.E6.rank) (ω : List (Fin Tag.E6.rank)) :
    e6NWord k (j :: ω) = e6Data_valid.nm k j * e6NWord k ω := by
  rw [e6NWord, e6NWord, List.map_cons, List.prod_cons]

theorem e6Isogeny_nWord (ω : List (Fin Tag.E6.rank)) :
    ((e6Isogeny k (e6NWord k ω) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      (ω.map fun i => weylElt Tag.E6 k i 1).prod := by
  induction ω with
  | nil => simp [e6NWord]
  | cons j ω ih =>
    rw [e6NWord_cons, map_mul, Subgroup.coe_mul, ih, List.map_cons, List.prod_cons]
    congr 1
    exact e6Isogeny_nt_eq j 1

theorem e6Isogeny_nWord_eq_canonicalRep {ω : List (Fin Tag.E6.rank)}
    (hω : (coxeterSystem Tag.E6).IsReduced ω) :
    ((e6Isogeny k (e6NWord k ω) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      canonicalRep (coxeterSystem Tag.E6) k ((coxeterSystem Tag.E6).wordProd ω) := by
  rw [e6Isogeny_nWord, canonicalRep_wordProd hω]

@[expose] def e6StarS {K : Type} [Field K] (j : Fin Tag.E6.rank) (u : Fin Tag.E6.rank → Kˣ) :
    Fin Tag.E6.rank → Kˣ :=
  u * Pi.mulSingle j (∏ l, u l ^ (-Tag.cartan Tag.E6 l j))

theorem e6StarS_mul {K : Type} [Field K] (j : Fin Tag.E6.rank) (t t' : Fin Tag.E6.rank → Kˣ) :
    e6StarS j (t * t') = e6StarS j t * e6StarS j t' := by
  simp only [e6StarS, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Pi.mulSingle_mul]
  rw [mul_mul_mul_comm]

theorem nm_conj_minTorus (k : Type) [Field k] (j : Fin Tag.E6.rank) (u : Fin Tag.E6.rank → kˣ) :
    e6Data_valid.nm k j * minTorus e6Data_valid k u * (e6Data_valid.nm k j)⁻¹ =
      minTorus e6Data_valid k (e6StarS j u) := by
  induction u using CFSG.LieType.Chevalley.ExceptionalCover.torusVec_induction with
  | h1 =>
    have e : e6StarS j (1 : Fin Tag.E6.rank → kˣ) = 1 := by
      simp [e6StarS]
    rw [e, map_one, mul_one, mul_inv_cancel]
  | hmul t t' ht ht' =>
    rw [e6StarS_mul, map_mul, map_mul, ← ht, ← ht']
    group
  | hsingle a s =>
    rw [minTorus_mulSingle, e6Data_valid.nm_conj_hm k j a s, e6StarS, map_mul,
      minTorus_mulSingle, minTorus_mulSingle]
    congr 2
    rw [Finset.prod_eq_single a (fun l _ hl => by rw [Pi.mulSingle_eq_of_ne hl, one_zpow])
      (fun h => absurd (Finset.mem_univ a) h), Pi.mulSingle_eq_same]

theorem nWord_conj_minTorus (k : Type) [Field k] (ω : List (Fin Tag.E6.rank))
    (u : Fin Tag.E6.rank → kˣ) :
    e6NWord k ω * minTorus e6Data_valid k u * (e6NWord k ω)⁻¹ =
      minTorus e6Data_valid k (ω.foldr e6StarS u) := by
  induction ω with
  | nil => simp [e6NWord]
  | cons j ω ih =>
    rw [e6NWord_cons, List.foldr_cons, ← nm_conj_minTorus k j, ← ih]
    group

@[expose] def e6WtEval {K : Type} [Field K] (u : Fin Tag.E6.rank → Kˣ)
    (μ : Fin Tag.E6.rank → ℤ) : Kˣ :=
  ∏ l, u l ^ μ l

theorem e6WtEval_add {K : Type} [Field K] (u : Fin Tag.E6.rank → Kˣ)
    (μ ν : Fin Tag.E6.rank → ℤ) : e6WtEval u (μ + ν) = e6WtEval u μ * e6WtEval u ν := by
  simp only [e6WtEval, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem e6WtEval_sub {K : Type} [Field K] (u : Fin Tag.E6.rank → Kˣ)
    (μ ν : Fin Tag.E6.rank → ℤ) : e6WtEval u (μ - ν) = e6WtEval u μ * (e6WtEval u ν)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← e6WtEval_add, sub_add_cancel]

theorem e6WtEval_starS {K : Type} [Field K] (j : Fin Tag.E6.rank) (u : Fin Tag.E6.rank → Kˣ)
    (μ : Fin Tag.E6.rank → ℤ) : e6WtEval (e6StarS j u) μ = e6WtEval u (reflectWeight j μ) := by
  have h1 : reflectWeight j μ = μ + (-μ j) • toWeight (Pi.single j 1) := by
    rw [reflectWeight, neg_smul, sub_eq_add_neg]
  rw [h1, e6WtEval_add]
  simp only [e6WtEval, e6StarS, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single j (fun l _ hl => by rw [Pi.mulSingle_eq_of_ne hl, one_zpow])
    (fun h => absurd (Finset.mem_univ j) h), Pi.mulSingle_eq_same, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← zpow_mul, Pi.smul_apply, smul_eq_mul]
  congr 1
  simp only [toWeight, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

theorem e6WtEval_foldr {K : Type} [Field K] (ω : List (Fin Tag.E6.rank))
    (u : Fin Tag.E6.rank → Kˣ) (μ : Fin Tag.E6.rank → ℤ) :
    e6WtEval (ω.foldr e6StarS u) μ = e6WtEval u (ω.foldl (fun ν j => reflectWeight j ν) μ) := by
  induction ω generalizing μ with
  | nil => rfl
  | cons j ω ih => rw [List.foldr_cons, e6WtEval_starS, ih, List.foldl_cons]

theorem e6WtEval_toWeight {K : Type} [Field K] (u : Fin Tag.E6.rank → Kˣ)
    (β : Fin Tag.E6.rank → ℤ) : e6WtEval u (toWeight β) = rootChar (e6RootParams u) β := by
  simp only [e6WtEval, rootChar, e6RootParams, toWeight]
  simp_rw [CFSG.LieType.Steinberg.CentralExt.AdjointClosed.zpow_sum_eq_prod, ← Finset.prod_zpow,
    ← zpow_mul]
  rw [Finset.prod_comm]

theorem toWeight_foldl_reflect (ω : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    toWeight (ω.foldl (fun x j => reflect Tag.E6 j x) v) =
      ω.foldl (fun ν j => reflectWeight j ν) (toWeight v) := by
  induction ω generalizing v with
  | nil => rfl
  | cons j ω ih => rw [List.foldl_cons, ih, toWeight_reflect, List.foldl_cons]

theorem reflectWeight_smul (j : Fin Tag.E6.rank) (c : ℤ) (μ : Fin Tag.E6.rank → ℤ) :
    reflectWeight j (c • μ) = c • reflectWeight j μ := by
  funext l
  simp only [reflectWeight, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem foldl_reflectWeight_smul (ω : List (Fin Tag.E6.rank)) (c : ℤ)
    (μ : Fin Tag.E6.rank → ℤ) :
    ω.foldl (fun ν j => reflectWeight j ν) (c • μ) =
      c • ω.foldl (fun ν j => reflectWeight j ν) μ := by
  induction ω generalizing μ with
  | nil => rfl
  | cons j ω ih => rw [List.foldl_cons, List.foldl_cons, reflectWeight_smul, ih]

theorem toWeight_e6Omega3 :
    toWeight (τ := Tag.E6) e6Omega3 = (3 : ℤ) • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) := by
  decide +kernel

theorem wordProd_inv_smul_E6 (ω : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    ((coxeterSystem Tag.E6).wordProd ω)⁻¹ • v = ω.foldl (fun x j => reflect Tag.E6 j x) v := by
  rw [← CoxeterSystem.wordProd_reverse]
  induction ω generalizing v with
  | nil => simp
  | cons j ω ih =>
    rw [List.reverse_cons, CoxeterSystem.wordProd_append, mul_smul, List.foldl_cons, ← ih,
      CoxeterSystem.wordProd_singleton, simple_smul]

theorem toWeight_e6Shift_inv (ω : List (Fin Tag.E6.rank)) :
    toWeight (e6Shift ((coxeterSystem Tag.E6).wordProd ω)⁻¹) =
      ω.foldl (fun ν j => reflectWeight j ν) (Pi.single 0 1) - Pi.single 0 1 := by
  have h3 := three_smul_e6Shift ((coxeterSystem Tag.E6).wordProd ω)⁻¹
  have h := congrArg toWeight h3
  rw [toWeight_smul, toWeight_sub, wordProd_inv_smul_E6, toWeight_foldl_reflect,
    toWeight_e6Omega3, foldl_reflectWeight_smul, ← smul_sub] at h
  funext l
  have hl := congrFun h l
  simp only [Pi.smul_apply, smul_eq_mul] at hl
  omega

theorem rootChar_e6Shift_inv_of_conj_eq (k : Type) [Field k] (u : Fin Tag.E6.rank → kˣ)
    {ω : List (Fin Tag.E6.rank)}
    (h : e6NWord k ω * minTorus e6Data_valid k u * (e6NWord k ω)⁻¹ =
      minTorus e6Data_valid k u) :
    rootChar (e6RootParams u) (e6Shift ((coxeterSystem Tag.E6).wordProd ω)⁻¹) = 1 := by
  rw [nWord_conj_minTorus] at h
  have hu := minTorus_injective e6Data_valid k h
  have h1 : e6WtEval (ω.foldr e6StarS u) (Pi.single 0 1) = e6WtEval u (Pi.single 0 1) := by
    rw [hu]
  rw [e6WtEval_foldr] at h1
  rw [← e6WtEval_toWeight, toWeight_e6Shift_inv, e6WtEval_sub, h1, mul_inv_cancel]

theorem rootChar_e6Shift_of_commute {x y : e6Data_valid.minGroup k} (hxy : x * y = y * x)
    {a b : Fin Tag.E6.rank → kˣ} {w : WeylGroup Tag.E6}
    (hx : ((e6Isogeny k x : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = rootDiagUnit Tag.E6 a)
    (hy : ((e6Isogeny k y : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) k w)
    {u u' : Fin Tag.E6.rank → kˣ} (hu : e6RootParams u = a) (hu' : e6RootParams u' = b)
    (hw : w ∈ rootCharStabilizer a) :
    rootChar a (e6Shift w) = 1 := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  set T := minTorus e6Data_valid k u with hT
  set S := minTorus e6Data_valid k u' * e6NWord k ω with hS
  have hker : ∀ g g' : e6Data_valid.minGroup k,
      ((e6Isogeny k g : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
        ((e6Isogeny k g' : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) →
      g'⁻¹ * g ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    intro g g' hgg'
    refine ker_e6IsogenyT_le_center k ?_
    rw [MonoidHom.mem_ker]
    change e6Isogeny k (g'⁻¹ * g) = 1
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact Subtype.ext hgg'.symm
  have hxT : T⁻¹ * x ∈ Subgroup.center (e6Data_valid.minGroup k) :=
    hker x T (by rw [hx, hT, e6Isogeny_minTorus, hu])
  have hyS : S⁻¹ * y ∈ Subgroup.center (e6Data_valid.minGroup k) :=
    hker y S (by
      rw [hy, hS, map_mul, Subgroup.coe_mul, e6Isogeny_minTorus, hu',
        e6Isogeny_nWord_eq_canonicalRep hω])
  obtain ⟨z₁, hz₁⟩ : ∃ z, z = T⁻¹ * x := ⟨_, rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z, z = S⁻¹ * y := ⟨_, rfl⟩
  rw [← hz₁] at hxT
  rw [← hz₂] at hyS
  have hz1 := Subgroup.mem_center_iff.1 hxT
  have hz2 := Subgroup.mem_center_iff.1 hyS
  have ex : x = T * z₁ := by rw [hz₁]; group
  have ey : y = S * z₂ := by rw [hz₂]; group
  have hTS' : T * S * (z₁ * z₂) = S * T * (z₁ * z₂) := by
    calc T * S * (z₁ * z₂) = T * (S * z₁) * z₂ := by group
      _ = T * (z₁ * S) * z₂ := by rw [hz1 S]
      _ = x * y := by rw [ex, ey]; group
      _ = y * x := hxy
      _ = S * (z₂ * T) * z₁ := by rw [ex, ey]; group
      _ = S * (T * z₂) * z₁ := by rw [hz2 T]
      _ = S * T * (z₂ * z₁) := by group
      _ = S * T * (z₁ * z₂) := by rw [hz1 z₂]
  have hTS : T * S = S * T := mul_right_cancel hTS'
  have hTT : T * minTorus e6Data_valid k u' = minTorus e6Data_valid k u' * T := by
    rw [hT, ← map_mul, ← map_mul, mul_comm]
  have hN : e6NWord k ω * T * (e6NWord k ω)⁻¹ = T := by
    have h2 : minTorus e6Data_valid k u' * (T * e6NWord k ω) =
        minTorus e6Data_valid k u' * (e6NWord k ω * T) := by
      calc minTorus e6Data_valid k u' * (T * e6NWord k ω)
          = (minTorus e6Data_valid k u' * T) * e6NWord k ω := by group
        _ = (T * minTorus e6Data_valid k u') * e6NWord k ω := by rw [← hTT]
        _ = T * S := by rw [hS]; group
        _ = S * T := hTS
        _ = minTorus e6Data_valid k u' * (e6NWord k ω * T) := by rw [hS]; group
    have h3 := mul_left_cancel h2
    rw [← h3]
    group
  have hcore := rootChar_e6Shift_inv_of_conj_eq k u hN
  rw [hu] at hcore
  set w := (coxeterSystem Tag.E6).wordProd ω with hwdef
  have hcoc := e6Shift_mul w w⁻¹
  rw [mul_inv_cancel, e6Shift_one] at hcoc
  have e5 : e6Shift w = -(w • e6Shift w⁻¹) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hcoc.symm
  have e6 : rootChar a (-(w • e6Shift w⁻¹)) * rootChar a (w • e6Shift w⁻¹) = 1 := by
    rw [← rootChar_add, neg_add_cancel, rootChar_zero]
  rw [hw (e6Shift w⁻¹), hcore, mul_one] at e6
  rw [e5, e6]

end E6

end CFSG.HardMathSupport.Timmesfeld.CrossChar
