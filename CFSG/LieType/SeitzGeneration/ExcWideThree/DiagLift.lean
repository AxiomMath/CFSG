module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourSc
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagKill

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed

section Arith

theorem zpow_eq_zpow_of_dvd {G : Type*} [Group G] {ζ : G} (h3 : ζ ^ 3 = 1) {a b : ℤ}
    (h : (3 : ℤ) ∣ a - b) : ζ ^ a = ζ ^ b := by
  obtain ⟨t, ht⟩ := h
  have hab : a = b + 3 * t := by omega
  rw [hab, zpow_add, zpow_mul, show ζ ^ (3 : ℤ) = 1 by exact_mod_cast h3, one_zpow, mul_one]

theorem liftProd_zpow_sum {G ι : Type*} [CommGroup G] (ξ : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ξ ^ f i = ξ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

theorem e6Cartan_symm' (i j : Fin Tag.E6.rank) : Tag.E6.cartan i j = Tag.E6.cartan j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem e6StarS_zpow {k : Type} [Field k] (j : Fin Tag.E6.rank) (ζ : kˣ)
    (m : Fin Tag.E6.rank → ℤ) :
    e6StarS j (fun l => ζ ^ m l) = fun l => ζ ^ (reflect Tag.E6 j m l) := by
  funext l
  have hsum : ∏ l', (ζ ^ m l') ^ (-Tag.cartan Tag.E6 l' j) =
      ζ ^ (-(∑ i, Tag.cartan Tag.E6 j i * m i)) := by
    simp only [← zpow_mul]
    rw [liftProd_zpow_sum]
    congr 1
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e6Cartan_symm' i j]
    ring
  simp only [e6StarS, Pi.mul_apply, hsum]
  by_cases hl : l = j
  · subst hl
    simp only [Pi.mulSingle_eq_same, reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same, mul_one]
    rw [← zpow_add]
    congr 1
  · simp [Pi.mulSingle_eq_of_ne hl, reflect, Pi.single_eq_of_ne hl]

theorem foldr_e6StarS_zpow {k : Type} [Field k] (ζ : kˣ) (ω : List (Fin Tag.E6.rank))
    (m : Fin Tag.E6.rank → ℤ) :
    ω.foldr e6StarS (fun l => ζ ^ m l) =
      fun l => ζ ^ ((ω.foldr (fun j x => reflect Tag.E6 j x) m) l) := by
  induction ω with
  | nil => rfl
  | cons j ω ih =>
    rw [List.foldr_cons, ih, e6StarS_zpow, List.foldr_cons]

theorem wordProd_smul_eq_foldr
    (ω : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    ((coxeterSystem Tag.E6).wordProd ω) • v = ω.foldr (fun j x => reflect Tag.E6 j x) v := by
  induction ω with
  | nil => simp
  | cons j ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih, List.foldr_cons, simple_smul]

theorem e6RootParams_map' {k k' : Type} [Field k] [Field k'] (ι : k →+* k')
    (u : Fin Tag.E6.rank → kˣ) :
    e6RootParams (fun l => Units.map ι.toMonoidHom (u l)) =
      fun j => Units.map ι.toMonoidHom (e6RootParams u j) := by
  funext j
  simp only [e6RootParams, map_prod, map_zpow]

end Arith

section Lift


theorem exists_fixed_lift_of_classZero {k : Type} [Field k] [Finite k] (φ : k →+* k)
    (g0 : ModGL Tag.E6 k) (hg0 : g0 ∈ adjointGroup Tag.E6 k) (w : WeylGroup Tag.E6)
    (hF : baseChangeGL φ g0 = g0 * canonicalRep (coxeterSystem Tag.E6) k w) (ζ : kˣ)
    (hζ3 : ζ ^ 3 = 1) (hζφ : Units.map φ.toMonoidHom ζ = ζ) (m : Fin Tag.E6.rank → ℤ)
    (hwm : ∀ i, (3 : ℤ) ∣ (w • m) i - m i) :
    ∃ x : e6Data_valid.minGroup k, minBC e6Data_valid φ x = x ∧
      ((e6Isogeny k x : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
        g0 * rootDiagUnit Tag.E6 (e6RootParams (fun l => ζ ^ m l)) * g0⁻¹ := by
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
  set u0 : Fin Tag.E6.rank → kˣ := fun l => ζ ^ m l with hu0
  set T0 := minTorus e6Data_valid k u0 with hT0
  have hFT : Fb T0 = T0 := by
    rw [hFb, hT0, minBC_minTorus_E6]
    congr 1
    funext l
    simp only [hu0, map_zpow, hζφ]
  have hnT : n1 * T0 * n1⁻¹ = T0 := by
    rw [hn1, hT0, nWord_conj_minTorus, hu0, foldr_e6StarS_zpow]
    congr 1
    funext l
    have hs := wordProd_smul_eq_foldr ω m
    have h3 := hwm l
    rw [hs] at h3
    exact zpow_eq_zpow_of_dvd hζ3 h3
  refine ⟨g1 * T0 * g1⁻¹, ?_, ?_⟩
  · have hc := Subgroup.mem_center_iff.1 hζ0ker
    rw [map_mul, map_mul, map_inv, hFT, hF1]
    have : (g1 * n1 * ζ0) * T0 * (g1 * n1 * ζ0)⁻¹ = g1 * (n1 * T0 * n1⁻¹) * g1⁻¹ := by
      calc (g1 * n1 * ζ0) * T0 * (g1 * n1 * ζ0)⁻¹
          = g1 * n1 * (ζ0 * T0 * ζ0⁻¹) * n1⁻¹ * g1⁻¹ := by group
        _ = g1 * n1 * T0 * n1⁻¹ * g1⁻¹ := by
          rw [show ζ0 * T0 * ζ0⁻¹ = T0 by rw [← hc T0]; group]
        _ = g1 * (n1 * T0 * n1⁻¹) * g1⁻¹ := by group
    rw [this, hnT]
  · rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg1',
      hT0, e6Isogeny_minTorus]

theorem fixed_lift_params_fixed {k K : Type} [Field k] [Finite k] [Field K] [Finite K]
    (ι₃ : K →+* k) (φ : k →+* k) (hφι : φ.comp ι₃ = ι₃)
    (hφq : ∀ c : k, φ c = c ^ Nat.card K) (hq : Nat.card K % 3 = 1)
    (b : Fin Tag.E6.rank → Kˣ) {j : ModGL Tag.E6 K} (hj : j ∈ adjointGroup Tag.E6 K)
    (v : Fin Tag.E6.rank → kˣ) (hv : e6RootParams v = fun i => Units.map ι₃.toMonoidHom (b i))
    (x : e6Data_valid.minGroup k) (hfix : minBC e6Data_valid φ x = x)
    (hπ : ((e6Isogeny k x : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      baseChangeGL ι₃ (rootDiagUnit Tag.E6 b * j)) :
    ∀ l, Units.map φ.toMonoidHom (v l) = v l := by
  classical
  obtain ⟨j1, hj1⟩ := e6Isogeny_surjective K ⟨j, hj⟩
  have hj1' : ((e6Isogeny K j1 : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = j :=
    congrArg Subtype.val hj1
  set J := minBC e6Data_valid ι₃ j1 with hJ
  have hJπ : ((e6Isogeny k J : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = baseChangeGL ι₃ j := by
    rw [hJ, e6Isogeny_minBC, hj1']
  set Tv := minTorus e6Data_valid k v with hTv
  have hTπ : ((e6Isogeny k Tv : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      baseChangeGL ι₃ (rootDiagUnit Tag.E6 b) := by
    rw [hTv, e6Isogeny_minTorus, hv, baseChangeGL_rootDiagUnit]
  set ζ' := (Tv * J)⁻¹ * x with hζ'
  have hζ'ker : ζ' ∈ Subgroup.center ↥(e6Data_valid.minGroup k) := by
    rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center, MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hζ', map_mul, map_inv, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
      hTπ, hJπ, hπ, map_mul]
    simp
  obtain ⟨z, hzeq, hz3⟩ := exists_minTorus_of_mem_center_E6 hζ'ker
  have hz1 : ∀ l, Units.map φ.toMonoidHom (z l) = z l := by
    intro l
    obtain ⟨t, ht⟩ : ∃ t, Nat.card K = 3 * t + 1 := ⟨Nat.card K / 3, by omega⟩
    apply Units.ext
    have h1 : ((Units.map φ.toMonoidHom (z l) : kˣ) : k) = ((z l : kˣ) : k) ^ Nat.card K := by
      simp [hφq]
    rw [h1, ht, pow_succ, pow_mul]
    have h3 : ((z l : kˣ) : k) ^ 3 = 1 := by
      have := congrArg (fun u : kˣ => (u : k)) (hz3 l)
      simpa using this
    rw [h3, one_pow, one_mul]
  have hFζ' : minBC e6Data_valid φ ζ' = ζ' := by
    rw [hzeq, minBC_minTorus_E6]
    congr 1
    funext l
    exact hz1 l
  have hFJ : minBC e6Data_valid φ J = J := by
    rw [hJ, minBC_minBC_E6, hφι]
  have hxeq : x = Tv * J * ζ' := by rw [hζ']; group
  have hmain : minTorus e6Data_valid k (fun l => Units.map φ.toMonoidHom (v l)) = Tv := by
    have h1 : minBC e6Data_valid φ x = minTorus e6Data_valid k
        (fun l => Units.map φ.toMonoidHom (v l)) * J * ζ' := by
      rw [hxeq, map_mul, map_mul, hFJ, hFζ', hTv, minBC_minTorus_E6]
    rw [hfix] at h1
    have h2 : Tv * J * ζ' = minTorus e6Data_valid k (fun l => Units.map φ.toMonoidHom (v l)) * J *
        ζ' := by
      rw [← hxeq]
      exact h1
    exact (mul_right_cancel (mul_right_cancel h2)).symm
  intro l
  have := minTorus_injective e6Data_valid k hmain
  exact congrFun this l

theorem liftConjHom_apply {G : Type*} [Group G] (g x : G) :
    (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl

theorem mem_adjointGroup_of_classZero {K : Type} [Field K] [Finite K] (hq : Nat.card K % 3 = 1)
    {A : Subgroup (ModGL Tag.E6 K)} (D : LangGLData Tag.E6 K A)
    (ω : (AlgebraicClosure K)ˣ) (hω : IsPrimitiveRoot (ω : AlgebraicClosure K) 3)
    {y : ModGL Tag.E6 K} (hy : y ∈ A) (k : Fin Tag.E6.rank → ℕ)
    (ha : rootDiagUnit Tag.E6 (fun i => ω ^ k i) =
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * y * D.c⁻¹) * D.g0)
    (m : Fin Tag.E6.rank → ℤ) (hm : ∀ j, (3 : ℤ) ∣ (∑ l, Tag.E6.cartan l j * m l) - k j)
    (hwm : ∀ i, (3 : ℤ) ∣ (D.w • m) i - m i) :
    y ∈ adjointGroup Tag.E6 K := by
  classical
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  haveI hpf : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  set y' : ModGL Tag.E6 K := D.c * y * D.c⁻¹ with hy'
  suffices hadj : y' ∈ adjointGroup Tag.E6 K by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem D.hcN) y').1 hadj
    rwa [show D.c⁻¹ * y' * D.c⁻¹⁻¹ = y by rw [hy']; group] at this
  obtain ⟨t, ht, hte⟩ := D.hc y hy
  have hy'L : baseChangeGL ι y' = D.g0 * t * D.g0⁻¹ := by
    rw [← hte, liftConjHom_apply]
  have ht' : t ∈ torusGroup Tag.E6 L := (Subgroup.mem_inf.1 ht).1
  have hy'Lad : baseChangeGL ι y' ∈ adjointGroup Tag.E6 L := by
    rw [hy'L]
    exact mul_mem (mul_mem D.hg0C (torusGroup_le_adjointGroup' ht')) (inv_mem D.hg0C)
  have hy'F : Units.map (entrywiseHom D.Fr) (baseChangeGL ι y') = baseChangeGL ι y' :=
    baseChangeGL_frobenius_fixed D.Fr D.hFr y'
  obtain ⟨b, u, hu, hbu⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed Tag.E6 D.Fr D.hFr hy'Lad hy'F
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hu
  have hy'eq : y' = rootDiagUnit Tag.E6 b * j := by
    apply baseChangeGL_injective ι
    rw [hbu, map_mul]
  rw [hy'eq]
  suffices hb : rootDiagUnit Tag.E6 b ∈ adjointGroup Tag.E6 K from mul_mem hb hj
  obtain ⟨v, hv⟩ := exists_e6RootParams_eq (fun i => Units.map ι.toMonoidHom (b i))
  obtain ⟨Eg, hEg⟩ := exists_finset_descent D.hg0C
  obtain ⟨K₃, hK₃, hSK₃, hιK₃⟩ := exists_finite_subfield_of_finset (K := K)
    (Eg ∪ (Finset.univ.image fun i : Fin Tag.E6.rank => ((v i : Lˣ) : L)) ∪ {(ω : L)})
  haveI : Finite K₃ := hK₃
  have hgK : (Eg : Set L) ⊆ K₃ := fun x hx =>
    hSK₃ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_left _ hx)))
  have hvK : ∀ i, ((v i : Lˣ) : L) ∈ K₃ := fun i =>
    hSK₃ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩))))
  have hωK : (ω : L) ∈ K₃ :=
    hSK₃ (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_singleton_self _)))
  have hιK : ∀ x : K, ι x ∈ K₃ := fun x => hιK₃ ⟨x, rfl⟩
  obtain ⟨g3, hg3C, hg3⟩ := hEg K₃ hgK
  obtain ⟨v₃, hv₃⟩ := exists_units_descent K₃ v hvK
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
  have hφL : K₃.subtype.comp φ = D.Fr.comp K₃.subtype := by
    ext c
    simp only [RingHom.comp_apply, Subfield.coe_subtype, hφq, D.hFr, map_pow]
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
  have hF₃ : baseChangeGL φ g3 = g3 * canonicalRep (coxeterSystem Tag.E6) K₃ D.w := by
    apply hbcinj
    rw [baseChangeGL_baseChangeGL, hφL, ← baseChangeGL_baseChangeGL, hg3, map_mul,
      baseChangeGL_canonicalRep, hg3, ← units_map_entrywiseHom_eq_baseChangeGL]
    exact D.hg0
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
  obtain ⟨x, hxF, hxπ⟩ := exists_fixed_lift_of_classZero φ g3 hg3C D.w hF₃ ω₃ hω₃3 hω₃φ m hwm
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
      baseChangeGL ι₃ (rootDiagUnit Tag.E6 b * j) := by
    apply hbcinj
    rw [hxπ, hbcι, map_mul, map_mul, map_inv, hg3, baseChangeGL_rootDiagUnit, ← hy'eq]
    have hd : (fun i => Units.map K₃.subtype.toMonoidHom
        (e6RootParams (fun l => ω₃ ^ m l) i)) = fun i => ω ^ k i := by
      rw [← hparams, ← e6RootParams_map']
      congr 1
      funext l
      simp only [map_zpow]
      rw [hω₃]
    rw [hd, ha]
    group
  have hv₃b : e6RootParams v₃ = fun i => Units.map ι₃.toMonoidHom (b i) := by
    funext i
    apply units_map_subtype_injective K₃
    have h1 := congrFun (e6RootParams_map' K₃.subtype v₃) i
    rw [← h1, hv₃, hv]
    apply Units.ext
    exact (congrArg (fun f : K →+* L => f ((b i : Kˣ) : K)) hιι).symm
  have hfixv := fixed_lift_params_fixed ι₃ φ hφι hφq hq b hj v₃ hv₃b x hxF hπ
  have hrat : ∀ l, ∃ c : Kˣ, Units.map ι.toMonoidHom c = v l := by
    intro l
    have hpow : ((v l : Lˣ) : L) ^ Nat.card K = (v l : L) := by
      have h1 : φ ((v₃ l : K₃ˣ) : K₃) = ((v₃ l : K₃ˣ) : K₃) := by
        have := congrArg (fun u : K₃ˣ => (u : K₃)) (hfixv l)
        simpa using this
      rw [hφq] at h1
      have h2 := congrArg (fun x : K₃ => K₃.subtype x) h1
      simp only [map_pow] at h2
      have h3 : K₃.subtype ((v₃ l : K₃ˣ) : K₃) = ((v l : Lˣ) : L) := by
        have := congrArg (fun u : Lˣ => (u : L)) (congrFun hv₃ l)
        simpa using this
      rw [h3] at h2
      exact h2
    obtain ⟨c, hc⟩ := mem_range_algebraMap_of_pow_card_eq (k := K) hpow
    have hc0 : c ≠ 0 := fun h0 => (v l).ne_zero (by rw [← hc, h0, map_zero])
    exact ⟨Units.mk0 c hc0, Units.ext (by simpa using hc)⟩
  choose v' hv' using hrat
  have hbv' : e6RootParams v' = b := by
    funext i
    apply Units.map_injective ι.injective
    have h1 := congrFun (e6RootParams_map' ι v') i
    rw [← h1]
    have : (fun l => Units.map ι.toMonoidHom (v' l)) = v := funext hv'
    rw [this, hv]
  have := e6Isogeny_minTorus (k := K) v'
  rw [hbv'] at this
  rw [← this]
  exact Subtype.mem _

end Lift

end CFSG.LieType.SeitzGeneration.ExcWideThree
