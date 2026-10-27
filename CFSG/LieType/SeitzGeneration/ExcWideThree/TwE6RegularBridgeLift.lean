module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegularBridge
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularSAData
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourRigid

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Bridge

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular CFSG.LieType.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
open CFSG.LieType.Steinberg.Minuscule.MinData (toWeight reflectWeight)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux
  (eq_of_e6RootParams_eq_of_wtEval rootChar_e6Shift_inv_eq_one)

attribute [local instance] CFSG.HardMathSupport.Timmesfeld.CrossChar.e6ScLiftNeZeroRank

section Lift


theorem twE6B_sigma_minTorus {k : Type} [Field k] (θ : k →+* k) (u : Fin Tag.E6.rank → kˣ) :
    TwistedE6.sigma k θ (minTorus e6Data_valid k u) =
      minTorus e6Data_valid k (fun l => Units.map θ.toMonoidHom (u (TwistedE6.rhoPerm l))) := by
  induction u using CFSG.LieType.Chevalley.ExceptionalCover.torusVec_induction with
  | h1 =>
    have e : (fun l => Units.map θ.toMonoidHom
        ((1 : Fin Tag.E6.rank → kˣ) (TwistedE6.rhoPerm l))) = 1 := by
      funext l
      simp
    rw [map_one, map_one, e, map_one]
  | hmul t t' ht ht' =>
    have e : (fun l => Units.map θ.toMonoidHom ((t * t') (TwistedE6.rhoPerm l))) =
        (fun l => Units.map θ.toMonoidHom (t (TwistedE6.rhoPerm l))) *
          fun l => Units.map θ.toMonoidHom (t' (TwistedE6.rhoPerm l)) := by
      funext l
      simp
    rw [map_mul, map_mul, ht, ht', e, map_mul]
  | hsingle a s =>
    have e : (fun l => Units.map θ.toMonoidHom
        ((Pi.mulSingle a s : Fin Tag.E6.rank → kˣ) (TwistedE6.rhoPerm l))) =
        Pi.mulSingle (TwistedE6.rhoPerm a) (Units.map θ.toMonoidHom s) := by
      funext l
      by_cases hl : l = TwistedE6.rhoPerm a
      · subst hl
        simp [TwistedE6.rhoPerm_apply_rhoPerm]
      · have : TwistedE6.rhoPerm l ≠ a := fun h =>
          hl (by rw [← h, TwistedE6.rhoPerm_apply_rhoPerm])
        simp [Pi.mulSingle_eq_of_ne hl, Pi.mulSingle_eq_of_ne this]
    rw [e, minTorus_mulSingle, minTorus_mulSingle, TwistedE6.sigma_hm]
    rfl

theorem twE6B_e6RhoFour_eq : e6RhoFour = TwistedE6.rhoPerm := by
  ext i
  fin_cases i <;> rfl

theorem twE6B_w0Word_foldl_reflectWeight (l : Fin Tag.E6.rank) :
    e6W0FourWord.foldl (fun ν j => reflectWeight j ν) (Pi.single l 1) =
      -(Pi.single (e6RhoFour l) 1 : Fin Tag.E6.rank → ℤ) := by
  fin_cases l <;> decide +kernel

theorem twE6B_foldr_e6StarS_w0 {k : Type} [Field k] (v : Fin Tag.E6.rank → kˣ) :
    e6W0FourWord.foldr e6StarS v = fun l => (v (e6RhoFour l))⁻¹ := by
  funext l
  have h1 : e6WtEval (e6W0FourWord.foldr e6StarS v) (Pi.single l 1) =
      e6W0FourWord.foldr e6StarS v l := by
    simp [e6WtEval, Pi.single_apply]
  rw [← h1, e6WtEval_foldr, twE6B_w0Word_foldl_reflectWeight]
  simp [e6WtEval, Pi.single_apply, zpow_neg]

theorem twE6B_sigma_minTorus_eq_conj {k : Type} [Field k] (θ : k →+* k) {q : ℕ}
    (hθ : ∀ c, θ c = c ^ q) (hq : 3 ∣ q + 1) (u : Fin Tag.E6.rank → kˣ)
    (hu : ∀ l, u l ^ 3 = 1) :
    TwistedE6.sigma k θ (minTorus e6Data_valid k u) =
      e6NWord k e6W0FourWord * minTorus e6Data_valid k u * (e6NWord k e6W0FourWord)⁻¹ := by
  rw [twE6B_sigma_minTorus, nWord_conj_minTorus, twE6B_foldr_e6StarS_w0]
  congr 1
  funext l
  have h1 : Units.map θ.toMonoidHom (u (TwistedE6.rhoPerm l)) = u (TwistedE6.rhoPerm l) ^ q :=
    Units.ext (by simp [hθ])
  rw [h1, twE6_pow_eq_inv_of_dvd (hu _) hq, twE6B_e6RhoFour_eq]

theorem twE6B_inv_smul_eq {v w' : WeylGroup Tag.E6}
    (hw' : ∀ y, w' • y = -permLattice TwistedE6.rhoPerm (v⁻¹ • y)) (y : Fin Tag.E6.rank → ℤ) :
    w'⁻¹ • y = v • (-permLattice TwistedE6.rhoPerm y) := by
  have h1 := hw' (w'⁻¹ • y)
  rw [smul_inv_smul] at h1
  have h2 : permLattice TwistedE6.rhoPerm (v⁻¹ • w'⁻¹ • y) = -y :=
    neg_eq_iff_eq_neg.1 h1.symm
  have h3 : v⁻¹ • w'⁻¹ • y = permLattice TwistedE6.rhoPerm (-y) := by
    have := congrArg (permLattice TwistedE6.rhoPerm) h2
    rw [show permLattice TwistedE6.rhoPerm (permLattice TwistedE6.rhoPerm (v⁻¹ • w'⁻¹ • y)) =
      v⁻¹ • w'⁻¹ • y from TwistedE6.rho_rho _] at this
    exact this
  have h4 : permLattice TwistedE6.rhoPerm (-y) = -permLattice TwistedE6.rhoPerm y := by
    funext i
    simp [permLattice]
  rw [← h4, ← h3, smul_inv_smul]

theorem twE6B_nWord_sigma_minTorus {k : Type} [Field k] (θ : k →+* k) {q : ℕ}
    (hθ : ∀ c, θ c = c ^ q) (hq : 3 ∣ q + 1) (u : Fin Tag.E6.rank → kˣ)
    (hu : ∀ l, u l ^ 3 = 1) {ω : List (Fin Tag.E6.rank)} {v w' : WeylGroup Tag.E6}
    (hω : (coxeterSystem Tag.E6).wordProd ω = v)
    (hw' : ∀ y, w' • y = -permLattice TwistedE6.rhoPerm (v⁻¹ • y))
    (hstab : w' ∈ rootCharStabilizer (e6RootParams u))
    (hs : rootChar (e6RootParams u) (e6Shift w') = 1) :
    e6NWord k ω * TwistedE6.sigma k θ (minTorus e6Data_valid k u) * (e6NWord k ω)⁻¹ =
      minTorus e6Data_valid k u := by
  rw [twE6B_sigma_minTorus_eq_conj θ hθ hq u hu]
  have hW : ∀ y : Fin Tag.E6.rank → ℤ,
      ((coxeterSystem Tag.E6).wordProd (ω ++ e6W0FourWord)) • y = w'⁻¹ • y := by
    intro y
    have h0 : (coxeterSystem Tag.E6).wordProd e6W0FourWord • y =
        -permLattice TwistedE6.rhoPerm y := by
      have := e6W0Four_smul y
      rw [twE6B_e6RhoFour_eq] at this
      exact this
    rw [CoxeterSystem.wordProd_append, hω, mul_smul, twE6B_inv_smul_eq hw' y, h0]
  have hw : (coxeterSystem Tag.E6).wordProd (ω ++ e6W0FourWord) ∈
      rootCharStabilizer (e6RootParams u) := by
    intro y
    rw [hW y]
    have := hstab (w'⁻¹ • y)
    rw [smul_inv_smul] at this
    exact this.symm
  have hs' : rootChar (e6RootParams u)
      (e6Shift ((coxeterSystem Tag.E6).wordProd (ω ++ e6W0FourWord))) = 1 := by
    have e : e6Shift ((coxeterSystem Tag.E6).wordProd (ω ++ e6W0FourWord)) = e6Shift w'⁻¹ := by
      funext i
      simp only [e6Shift, hW]
    rw [e]
    exact rootChar_e6Shift_inv_eq_one hstab hs
  have key := e6NWord_conj_minTorus_eq u (ω ++ e6W0FourWord) hw hs'
  have hmul : e6NWord k (ω ++ e6W0FourWord) = e6NWord k ω * e6NWord k e6W0FourWord := by
    simp only [e6NWord, List.map_append, List.prod_append]
  rw [hmul] at key
  calc e6NWord k ω * (e6NWord k e6W0FourWord * minTorus e6Data_valid k u *
        (e6NWord k e6W0FourWord)⁻¹) * (e6NWord k ω)⁻¹
      = (e6NWord k ω * e6NWord k e6W0FourWord) * minTorus e6Data_valid k u *
        (e6NWord k ω * e6NWord k e6W0FourWord)⁻¹ := by group
    _ = minTorus e6Data_valid k u := key

theorem twE6B_exists_fixed_lift {k : Type} [Field k] [Finite k] (θ : k →+* k) {q : ℕ}
    (hθ : ∀ c, θ c = c ^ q) (hq : 3 ∣ q + 1) {v w' : WeylGroup Tag.E6}
    (hw' : ∀ y, w' • y = -permLattice TwistedE6.rhoPerm (v⁻¹ • y))
    {g : ModGL Tag.E6 k} (hg : g ∈ adjointGroup Tag.E6 k)
    (hθg : twistHom TwistTag.E6 k θ g = g * canonicalRep (coxeterSystem Tag.E6) k v)
    (u : Fin Tag.E6.rank → kˣ) (hu : ∀ l, u l ^ 3 = 1)
    (hstab : w' ∈ rootCharStabilizer (e6RootParams u))
    (hs : rootChar (e6RootParams u) (e6Shift w') = 1) :
    ∃ h : e6Data_valid.minGroup k,
      ((e6Isogeny k h : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
        g * rootDiagUnit Tag.E6 (e6RootParams u) * g⁻¹ ∧ TwistedE6.sigma k θ h = h := by
  obtain ⟨gt, hgt⟩ := e6Isogeny_surjective k ⟨g, hg⟩
  have hπg : ((e6Isogeny k gt : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = g := by rw [hgt]
  obtain ⟨ω, hω, hωv⟩ := (coxeterSystem Tag.E6).exists_isReduced v
  set N := e6NWord k ω with hNdef
  set T := minTorus e6Data_valid k u with hT
  have hπN : ((e6Isogeny k N : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      canonicalRep (coxeterSystem Tag.E6) k v := by
    rw [hNdef, e6Isogeny_nWord_eq_canonicalRep hω, hωv]
  have hzc : (gt * N)⁻¹ * TwistedE6.sigma k θ gt ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    apply e6Isogeny_ker_central
    rw [e6Isogeny_sigma θ gt, map_mul, Subgroup.coe_mul, hπg, hπN]
    change twistHom TwistTag.E6 k θ ((e6Isogeny k gt : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = _
    rw [hπg]
    exact hθg
  obtain ⟨z, hz⟩ : ∃ z, z = (gt * N)⁻¹ * TwistedE6.sigma k θ gt := ⟨_, rfl⟩
  rw [← hz] at hzc
  have hFg : TwistedE6.sigma k θ gt = gt * N * z := by rw [hz]; group
  have hzT : z * TwistedE6.sigma k θ T * z⁻¹ = TwistedE6.sigma k θ T := by
    rw [← Subgroup.mem_center_iff.1 hzc (TwistedE6.sigma k θ T), mul_inv_cancel_right]
  have hNT : N * TwistedE6.sigma k θ T * N⁻¹ = T :=
    twE6B_nWord_sigma_minTorus θ hθ hq u hu (ω := ω) (v := v) hωv.symm hw' hstab hs
  refine ⟨gt * T * gt⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hπg, hT,
      e6Isogeny_minTorus]
  · calc TwistedE6.sigma k θ (gt * T * gt⁻¹)
        = (gt * N * z) * TwistedE6.sigma k θ T * (gt * N * z)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hFg]
      _ = gt * (N * (z * TwistedE6.sigma k θ T * z⁻¹) * N⁻¹) * gt⁻¹ := by group
      _ = gt * (N * TwistedE6.sigma k θ T * N⁻¹) * gt⁻¹ := by rw [hzT]
      _ = gt * T * gt⁻¹ := by rw [hNT]

theorem twE6B_exists_sigma_fixed_of_fixed_lift {K k : Type} [Field K] [Finite K] [Field k]
    [Finite k] (σ : K →+* K) (ι : K →+* k) (φ : k →+* k) (hφι : φ.comp ι = ι.comp σ)
    (hfix : ∀ x : k, φ (φ x) = x → x ∈ Set.range ι)
    (b : Fin Tag.E6.rank → Kˣ) (v : Fin Tag.E6.rank → kˣ)
    (hv : e6RootParams v = fun i => Units.map ι.toMonoidHom (b i))
    (h : e6Data_valid.minGroup k)
    (hπ : ((e6Isogeny k h : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 (fun i => Units.map ι.toMonoidHom (b i)))
    (hF : TwistedE6.sigma k φ h = h) :
    ∃ s : e6Data_valid.minGroup K, TwistedE6.sigma K σ s = s ∧
      ((e6Isogeny K s : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 b := by
  have hcent : (minTorus e6Data_valid k v)⁻¹ * h ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    apply e6Isogeny_ker_central
    rw [hπ, e6Isogeny_minTorus, hv]
  obtain ⟨χ, hχ⟩ := center_le_range_minTorus e6Data_valid k isFiniteType_cartan_E6
    (e6Datum_isCTGroupDatum k) (e6Datum_steinbergExtras k) (e6Datum_bruhatExtras k) hcent
  have hχc : e6RootParams χ = 1 := by
    have h1 : χ ∈ centerChars Tag.E6 k := (minTorus_mem_center_iff e6Data_valid k χ).1 (hχ ▸ hcent)
    funext i
    exact mem_centerChars.1 h1 i
  have hh : h = minTorus e6Data_valid k (v * χ) := by
    rw [map_mul, hχ]
    group
  have hw : ∀ l, Units.map φ.toMonoidHom ((v * χ) (TwistedE6.rhoPerm l)) = (v * χ) l := by
    have h1 := hF
    rw [hh, twE6B_sigma_minTorus] at h1
    exact fun l => congrFun (minTorus_injective e6Data_valid k h1) l
  have hw2 : ∀ l, Units.map φ.toMonoidHom (Units.map φ.toMonoidHom ((v * χ) l)) = (v * χ) l := by
    intro l
    have h1 := hw (TwistedE6.rhoPerm l)
    rw [TwistedE6.rhoPerm_apply_rhoPerm] at h1
    rw [h1, hw l]
  have hK : ∀ l, ∃ x : Kˣ, Units.map ι.toMonoidHom x = (v * χ) l := fun l => by
    obtain ⟨x, hx⟩ := hfix (((v * χ) l : kˣ) : k) (congrArg Units.val (hw2 l))
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact ((v * χ) l).ne_zero hx.symm
    exact ⟨Units.mk0 x hx0, Units.ext hx⟩
  choose v' hv' using hK
  have hc : e6RootParams v' = b := by
    funext j
    apply Units.map_injective ι.injective
    have h1 := congrFun (E6DiagRegular.e6RootParams_map ι v') j
    rw [← h1, show (fun l => Units.map ι.toMonoidHom (v' l)) = v * χ from funext hv',
      E6DiagRegular.e6RootParams_mul, hv, hχc]
    simp
  refine ⟨minTorus e6Data_valid K v', ?_, ?_⟩
  · rw [twE6B_sigma_minTorus]
    congr 1
    funext l
    apply Units.map_injective ι.injective
    have h1 : Units.map ι.toMonoidHom (Units.map σ.toMonoidHom (v' (TwistedE6.rhoPerm l))) =
        Units.map φ.toMonoidHom (Units.map ι.toMonoidHom (v' (TwistedE6.rhoPerm l))) :=
      Units.ext (RingHom.congr_fun hφι _).symm
    rw [h1, hv', hw l, hv']
  · rw [e6Isogeny_minTorus, hc]

theorem twE6B_sigma_minBC {k k' : Type} [Field k] [Field k'] (ι : k →+* k') (θ : k →+* k)
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

theorem twE6B_core {K k L : Type} [Field K] [Finite K] [Field k] [Finite k] [Field L]
    (σ : K ≃+* K) {q : ℕ} (hσ : ∀ c, σ c = c ^ q) (h3q : 3 ∣ q + 1)
    (ι : K →+* k) (ι₂ : k →+* L) (ι₀ : K →+* L) (hιι : ι₂.comp ι = ι₀)
    (φ : k →+* k) (hφq : ∀ c, φ c = c ^ q)
    (hfix : ∀ x : k, φ (φ x) = x → x ∈ Set.range ι)
    {v w' : WeylGroup Tag.E6}
    (hw' : ∀ y, w' • y = -permLattice TwistedE6.rhoPerm (v⁻¹ • y))
    {g₂ : ModGL Tag.E6 k} (hg₂C : g₂ ∈ adjointGroup Tag.E6 k)
    (hφg : twistHom TwistTag.E6 k φ g₂ = g₂ * canonicalRep (coxeterSystem Tag.E6) k v)
    {a : Fin Tag.E6.rank → Lˣ} (hwa : w' ∈ rootCharStabilizer a)
    (hsh : rootChar a (e6Shift w') = 1)
    {uT : Fin Tag.E6.rank → Lˣ} (hu3 : ∀ l, uT l ^ 3 = 1) (huc : e6RootParams uT = a)
    {u₂ : Fin Tag.E6.rank → kˣ} (hu₂ : (fun i => Units.map ι₂.toMonoidHom (u₂ i)) = uT)
    {vT : Fin Tag.E6.rank → Lˣ} {b' : Fin Tag.E6.rank → Kˣ}
    (hvc : e6RootParams vT = fun i => Units.map ι₀.toMonoidHom (b' i))
    {v₂ : Fin Tag.E6.rank → kˣ} (hv₂ : (fun i => Units.map ι₂.toMonoidHom (v₂ i)) = vT)
    {y u₀ : ModGL Tag.E6 K} {g0 : ModGL Tag.E6 L} (hg₂ : baseChangeGL ι₂ g₂ = g0)
    (hy : baseChangeGL ι₀ y = g0 * rootDiagUnit Tag.E6 a * g0⁻¹)
    (hyb : y = rootDiagUnit Tag.E6 b' * u₀)
    {sK : e6Data_valid.minGroup K} (hsKσ : TwistedE6.sigma K σ.toRingHom sK = sK)
    (hsKt : ((e6Isogeny K sK : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = u₀) :
    ∃ s : e6Data_valid.minGroup K, TwistedE6.sigma K σ.toRingHom s = s ∧
      ((e6Isogeny K s : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = rootDiagUnit Tag.E6 b' := by
  have hu₂3 : ∀ l, u₂ l ^ 3 = 1 := fun l => by
    apply Units.map_injective ι₂.injective
    rw [map_pow, congrFun hu₂ l, hu3 l, map_one]
  have ha₂ : (fun j => Units.map ι₂.toMonoidHom (e6RootParams u₂ j)) = a := by
    rw [← E6DiagRegular.e6RootParams_map, hu₂, huc]
  have hw₂ : w' ∈ rootCharStabilizer (e6RootParams u₂) := by
    intro x
    apply Units.map_injective ι₂.injective
    have e1 := rootChar_map_tuple ι₂ (e6RootParams u₂) (w' • x)
    have e2 := rootChar_map_tuple ι₂ (e6RootParams u₂) x
    rw [ha₂] at e1 e2
    rw [← e1, ← e2]
    exact hwa x
  have hs₂ : rootChar (e6RootParams u₂) (e6Shift w') = 1 := by
    apply Units.map_injective ι₂.injective
    have e1 := rootChar_map_tuple ι₂ (e6RootParams u₂) (e6Shift w')
    rw [ha₂] at e1
    rw [← e1, hsh, map_one]
  obtain ⟨h, hπh, hFh⟩ := twE6B_exists_fixed_lift φ hφq h3q hw' hg₂C hφg u₂ hu₂3 hw₂ hs₂
  have hπy : baseChangeGL ι y = g₂ * rootDiagUnit Tag.E6 (e6RootParams u₂) * g₂⁻¹ := by
    apply baseChangeGL_injective ι₂
    rw [map_mul, map_mul, map_inv, baseChangeGL_baseChangeGL, hιι, hg₂, baseChangeGL_rootDiagUnit,
      ha₂, hy]
  have hφι : φ.comp ι = ι.comp σ.toRingHom := RingHom.ext fun x => by
    simp only [RingHom.comp_apply, hφq, map_pow, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, hσ]
  have hFũ : TwistedE6.sigma k φ (minBC e6Data_valid ι sK) = minBC e6Data_valid ι sK := by
    rw [twE6B_sigma_minBC ι σ.toRingHom φ hφι, hsKσ]
  have hπũ : ((e6Isogeny k (minBC e6Data_valid ι sK) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      baseChangeGL ι u₀ := by
    rw [e6Isogeny_minBC, hsKt]
  have hπh₁ : ((e6Isogeny k (h * (minBC e6Data_valid ι sK)⁻¹) : adjointGroup Tag.E6 k) :
      ModGL Tag.E6 k) = rootDiagUnit Tag.E6 (fun i => Units.map ι.toMonoidHom (b' i)) := by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hπh, hπũ, ← hπy, hyb, map_mul,
      baseChangeGL_rootDiagUnit]
    group
  have hFh₁ : TwistedE6.sigma k φ (h * (minBC e6Data_valid ι sK)⁻¹) =
      h * (minBC e6Data_valid ι sK)⁻¹ := by
    rw [map_mul, map_inv, hFh, hFũ]
  have hv₂' : e6RootParams v₂ = fun i => Units.map ι.toMonoidHom (b' i) := by
    funext i
    apply Units.map_injective ι₂.injective
    have h1 := congrFun (E6DiagRegular.e6RootParams_map ι₂ v₂) i
    rw [← h1, hv₂, hvc]
    exact (Units.ext (congrArg (fun f => f ((b' i : Kˣ) : K)) hιι)).symm
  exact twE6B_exists_sigma_fixed_of_fixed_lift σ.toRingHom ι φ hφι hfix b' v₂ hv₂' _ hπh₁ hFh₁

end Lift

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Bridge
