module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagLift

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed

section Conv


theorem fixed_lift_class_trivial {k : Type} [Field k] [Finite k] (φ : k →+* k) (q : ℕ)
    (hφq : ∀ c : k, φ c = c ^ q) (hq : q % 3 = 1)
    (g0 : ModGL Tag.E6 k) (hg0 : g0 ∈ adjointGroup Tag.E6 k) (w : WeylGroup Tag.E6)
    (hF : baseChangeGL φ g0 = g0 * canonicalRep (coxeterSystem Tag.E6) k w) (ζ : kˣ)
    (hζ3 : ζ ^ 3 = 1) (hζφ : Units.map φ.toMonoidHom ζ = ζ) (m : Fin Tag.E6.rank → ℤ)
    (x : e6Data_valid.minGroup k) (hx : minBC e6Data_valid φ x = x)
    (hπ : ((e6Isogeny k x : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      g0 * rootDiagUnit Tag.E6 (e6RootParams (fun l => ζ ^ m l)) * g0⁻¹) :
    ∀ l, ζ ^ ((w • m) l) = ζ ^ (m l) := by
  classical
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  obtain ⟨g1, hg1⟩ := e6Isogeny_surjective k ⟨g0, hg0⟩
  have hg1' : ((e6Isogeny k g1 : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = g0 :=
    congrArg Subtype.val hg1
  set Fb := minBC e6Data_valid φ with hFb
  set n1 := e6NWord k ω with hn1
  have hn1' : ((e6Isogeny k n1 : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      canonicalRep (coxeterSystem Tag.E6) k ((coxeterSystem Tag.E6).wordProd ω) :=
    e6Isogeny_nWord_eq_canonicalRep hω
  have hFg1 : ((e6Isogeny k (Fb g1) : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      baseChangeGL φ g0 := by
    rw [hFb, e6Isogeny_minBC, hg1']
  set ζ0 := (g1 * n1)⁻¹ * Fb g1 with hζ0
  have hζ0ker : ζ0 ∈ Subgroup.center ↥(e6Data_valid.minGroup k) := by
    rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center, MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hζ0, map_mul, map_inv, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
      hg1', hn1', hFg1, hF]
    simp
  have hF1 : Fb g1 = g1 * n1 * ζ0 := by rw [hζ0]; group
  have hc0 := Subgroup.mem_center_iff.1 hζ0ker
  set u0 : Fin Tag.E6.rank → kˣ := fun l => ζ ^ m l with hu0
  set T0 := minTorus e6Data_valid k u0 with hT0
  set T1 := minTorus e6Data_valid k
    (fun l => ζ ^ (((coxeterSystem Tag.E6).wordProd ω • m) l)) with hT1
  have hFT : Fb T0 = T0 := by
    rw [hFb, hT0, minBC_minTorus_E6]
    congr 1
    funext l
    simp only [hu0, map_zpow, hζφ]
  have hnT : n1 * T0 * n1⁻¹ = T1 := by
    rw [hn1, hT0, nWord_conj_minTorus, hu0, foldr_e6StarS_zpow, hT1]
    congr 1
    funext l
    rw [wordProd_smul_eq_foldr]
  set yh := g1 * T0 * g1⁻¹ with hyh
  have hyhπ : ((e6Isogeny k yh : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      g0 * rootDiagUnit Tag.E6 (e6RootParams u0) * g0⁻¹ := by
    rw [hyh, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hg1', hT0, e6Isogeny_minTorus]
  set ζ' := yh⁻¹ * x with hζ'
  have hζ'ker : ζ' ∈ Subgroup.center ↥(e6Data_valid.minGroup k) := by
    rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center, MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hζ', map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hyhπ, hπ, Subgroup.coe_one]
    group
  obtain ⟨z, hzeq, hz3⟩ := exists_minTorus_of_mem_center_E6 hζ'ker
  have hz1 : ∀ l, Units.map φ.toMonoidHom (z l) = z l := by
    intro l
    obtain ⟨t, ht⟩ : ∃ t : ℕ, q = 3 * t + 1 := ⟨q / 3, by omega⟩
    apply Units.ext
    have h1 : ((Units.map φ.toMonoidHom (z l) : kˣ) : k) = ((z l : kˣ) : k) ^ q := by
      simp [hφq]
    rw [h1, ht, pow_succ, pow_mul]
    have h3 : ((z l : kˣ) : k) ^ 3 = 1 := by
      have := congrArg (fun u : kˣ => (u : k)) (hz3 l)
      simpa using this
    rw [h3, one_pow, one_mul]
  have hFζ' : Fb ζ' = ζ' := by
    rw [hzeq, hFb, minBC_minTorus_E6]
    congr 1
    funext l
    exact hz1 l
  have hFyh : Fb yh = g1 * T1 * g1⁻¹ := by
    have hnT' : g1 * n1 * ζ0 * T0 * (g1 * n1 * ζ0)⁻¹ = g1 * T1 * g1⁻¹ := by
      calc g1 * n1 * ζ0 * T0 * (g1 * n1 * ζ0)⁻¹
          = g1 * n1 * (ζ0 * T0 * ζ0⁻¹) * n1⁻¹ * g1⁻¹ := by group
        _ = g1 * n1 * T0 * n1⁻¹ * g1⁻¹ := by
          rw [show ζ0 * T0 * ζ0⁻¹ = T0 by rw [← hc0 T0]; group]
        _ = g1 * (n1 * T0 * n1⁻¹) * g1⁻¹ := by group
        _ = g1 * T1 * g1⁻¹ := by rw [hnT]
    rw [hyh, map_mul, map_mul, map_inv, hFT, hF1]
    exact hnT'
  have hxeq : x = yh * ζ' := by rw [hζ']; group
  have h1 : Fb yh * ζ' = yh * ζ' := by
    calc Fb yh * ζ' = Fb yh * Fb ζ' := by rw [hFζ']
      _ = Fb (yh * ζ') := (map_mul _ _ _).symm
      _ = Fb x := by rw [← hxeq]
      _ = x := hx
      _ = yh * ζ' := hxeq
  have h2 : Fb yh = yh := mul_right_cancel h1
  rw [hFyh, hyh] at h2
  have h3 : T1 = T0 := by
    have := mul_right_cancel h2
    exact mul_left_cancel this
  intro l
  have hl := minTorus_injective e6Data_valid k (hT1 ▸ hT0 ▸ h3)
  exact congrFun hl l


theorem not_mem_adjointGroup_of_not_fixed {K : Type} [Field K] [Finite K]
    (hq : Nat.card K % 3 = 1) (w : WeylGroup Tag.E6)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (g0 : ModGL Tag.E6 (AlgebraicClosure K)) (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
    (ω : (AlgebraicClosure K)ˣ) (hω : IsPrimitiveRoot (ω : AlgebraicClosure K) 3)
    (k : Fin Tag.E6.rank → ℕ) (m : Fin Tag.E6.rank → ℤ)
    (hm : ∀ j, (3 : ℤ) ∣ (∑ l, Tag.E6.cartan l j * m l) - k j)
    (hwm : ¬ ∀ i, (3 : ℤ) ∣ (w • m) i - m i) {y : ModGL Tag.E6 K}
    (hy : baseChangeGL (algebraMap K (AlgebraicClosure K)) y =
      g0 * rootDiagUnit Tag.E6 (fun i => ω ^ k i) * g0⁻¹) :
    y ∉ adjointGroup Tag.E6 K := by
  classical
  intro hyad
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  haveI hpf : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  obtain ⟨Eg, hEg⟩ := exists_finset_descent hg0C
  obtain ⟨K₃, hK₃, hSK₃, hιK₃⟩ := exists_finite_subfield_of_finset (K := K)
    (Eg ∪ {(ω : L)})
  haveI : Finite K₃ := hK₃
  have hgK : (Eg : Set L) ⊆ K₃ := fun x hx =>
    hSK₃ (Finset.mem_coe.2 (Finset.mem_union_left _ hx))
  have hωK : (ω : L) ∈ K₃ :=
    hSK₃ (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_singleton_self _)))
  have hιK : ∀ x : K, ι x ∈ K₃ := fun x => hιK₃ ⟨x, rfl⟩
  obtain ⟨g3, hg3C, hg3⟩ := hEg K₃ hgK
  obtain ⟨ω₃, hω₃⟩ : ∃ ω₃ : K₃ˣ, Units.map K₃.subtype.toMonoidHom ω₃ = ω :=
    ⟨Units.mk0 ⟨(ω : L), hωK⟩ fun h0 => ω.ne_zero (congrArg Subtype.val h0),
      Units.ext rfl⟩
  obtain ⟨ι₃, hιι⟩ : ∃ ι₃ : K →+* K₃, K₃.subtype.comp ι₃ = ι :=
    ⟨ι.codRestrict K₃ hιK, RingHom.ext fun x => rfl⟩
  haveI : CharP L (ringChar K) := charP_of_injective_algebraMap ι.injective _
  haveI : CharP K₃ (ringChar K) := Subfield.charP K₃ (ringChar K)
  obtain ⟨φ, hφdef⟩ : ∃ φ : K₃ →+* K₃, φ = iterateFrobenius K₃ (ringChar K) e := ⟨_, rfl⟩
  have hφq : ∀ c : K₃, φ c = c ^ Nat.card K := fun c => by
    rw [hφdef, iterateFrobenius_def, hcard]
  have hφL : K₃.subtype.comp φ = Fr.comp K₃.subtype := by
    ext c
    simp only [RingHom.comp_apply, Subfield.coe_subtype, hφq, hFr, map_pow]
  have hφι : φ.comp ι₃ = ι₃ := by
    have : Fintype K := Fintype.ofFinite K
    ext c
    rw [RingHom.comp_apply, hφq, ← map_pow]
    have h := FiniteField.pow_card c
    rw [← Nat.card_eq_fintype_card] at h
    rw [h]
  have hbcinj : Function.Injective (baseChangeGL (τ := Tag.E6) K₃.subtype) :=
    baseChangeGL_injective K₃.subtype
  have hbcι : ∀ x : ModGL Tag.E6 K, baseChangeGL K₃.subtype (baseChangeGL ι₃ x) =
      baseChangeGL ι x := fun x => by
    rw [baseChangeGL_baseChangeGL, hιι]
  have hF₃ : baseChangeGL φ g3 = g3 * canonicalRep (coxeterSystem Tag.E6) K₃ w := by
    apply hbcinj
    rw [baseChangeGL_baseChangeGL, hφL, ← baseChangeGL_baseChangeGL, hg3, map_mul,
      baseChangeGL_canonicalRep, hg3, ← units_map_entrywiseHom_eq_baseChangeGL]
    exact hg0
  have hω₃3 : ω₃ ^ 3 = 1 := by
    apply units_map_subtype_injective K₃
    rw [map_pow, hω₃, hω3, map_one]
  obtain ⟨t', ht'⟩ : ∃ t', Nat.card K = 3 * t' + 1 := ⟨Nat.card K / 3, by omega⟩
  have hω₃φ : Units.map φ.toMonoidHom ω₃ = ω₃ := by
    apply Units.ext
    have h1 : ((Units.map φ.toMonoidHom ω₃ : K₃ˣ) : K₃) = ((ω₃ : K₃ˣ) : K₃) ^ Nat.card K := by
      simp [hφq]
    rw [h1, ht', pow_succ, pow_mul]
    have h3 : ((ω₃ : K₃ˣ) : K₃) ^ 3 = 1 := by
      have := congrArg (fun u : K₃ˣ => (u : K₃)) hω₃3
      simpa using this
    rw [h3, one_pow, one_mul]
  obtain ⟨y1, hy1⟩ := e6Isogeny_surjective K ⟨y, hyad⟩
  have hy1' : ((e6Isogeny K y1 : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = y :=
    congrArg Subtype.val hy1
  set x := minBC e6Data_valid ι₃ y1 with hxdef
  have hxF : minBC e6Data_valid φ x = x := by
    rw [hxdef, minBC_minBC_E6, hφι]
  have hxπ : ((e6Isogeny K₃ x : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) =
      baseChangeGL ι₃ y := by
    rw [hxdef, e6Isogeny_minBC, hy1']
  have hparams : e6RootParams (fun l => ω ^ m l) = fun i => ω ^ k i := by
    funext i
    simp only [e6RootParams]
    rw [show (∏ l, (ω ^ m l) ^ Tag.E6.cartan l i) = ω ^ (∑ l, Tag.E6.cartan l i * m l) by
      rw [← liftProd_zpow_sum]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [← zpow_mul, mul_comm]]
    rw [← zpow_natCast]
    exact zpow_eq_zpow_of_dvd hω3 (hm i)
  have hπ : ((e6Isogeny K₃ x : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) =
      g3 * rootDiagUnit Tag.E6 (e6RootParams (fun l => ω₃ ^ m l)) * g3⁻¹ := by
    apply hbcinj
    rw [hxπ, hbcι, hy, map_mul, map_mul, map_inv, hg3, baseChangeGL_rootDiagUnit]
    have hd : (fun i => Units.map K₃.subtype.toMonoidHom
        (e6RootParams (fun l => ω₃ ^ m l) i)) = fun i => ω ^ k i := by
      rw [← hparams, ← e6RootParams_map']
      congr 1
      funext l
      simp only [map_zpow]
      rw [hω₃]
    rw [hd]
  have key := fixed_lift_class_trivial φ (Nat.card K) hφq hq g3 hg3C w hF₃ ω₃ hω₃3 hω₃φ m x hxF hπ
  apply hwm
  intro i
  have h1 := key i
  have h2 : ω ^ ((w • m) i) = ω ^ (m i) := by
    have := congrArg (Units.map K₃.subtype.toMonoidHom) h1
    simpa only [map_zpow, hω₃] using this
  have hωu : IsPrimitiveRoot ω 3 := IsPrimitiveRoot.coe_units_iff.1 hω
  have h3 : ω ^ ((w • m) i - m i) = 1 := by rw [zpow_sub, h2, mul_inv_cancel]
  exact (hωu.zpow_eq_one_iff_dvd _).1 h3

end Conv

end CFSG.LieType.SeitzGeneration.ExcWideThree
