module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeTorality
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LieType.AlgebraicGroups

theorem commute_conj_of_ker_le_center {G H : Type*} [Group G] [Group H] (π : G →* H)
    (hker : π.ker ≤ Subgroup.center G) {x y z : G} (hxy : x * y = y * x)
    (hz : π z * π x = π x * π z) : x * (z * y * z⁻¹) = (z * y * z⁻¹) * x := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = x⁻¹ * (z⁻¹ * x * z) := ⟨_, rfl⟩
  have hζk : ζ ∈ π.ker := by
    rw [MonoidHom.mem_ker, hζ, map_mul, map_inv, map_mul, map_mul, map_inv]
    have : π x * π z = π z * π x := hz.symm
    calc (π x)⁻¹ * ((π z)⁻¹ * π x * π z) = (π x)⁻¹ * ((π z)⁻¹ * (π x * π z)) := by group
      _ = (π x)⁻¹ * ((π z)⁻¹ * (π z * π x)) := by rw [this]
      _ = 1 := by group
  have hζc := Subgroup.mem_center_iff.1 (hker hζk)
  have e1 : z⁻¹ * x * z = x * ζ := by rw [hζ]; group
  calc x * (z * y * z⁻¹) = z * (z⁻¹ * x * z) * y * z⁻¹ := by group
    _ = z * x * (ζ * y) * z⁻¹ := by rw [e1]; group
    _ = z * x * (y * ζ) * z⁻¹ := by rw [hζc y]
    _ = z * (x * y) * ζ * z⁻¹ := by group
    _ = z * (y * x) * ζ * z⁻¹ := by rw [hxy]
    _ = z * y * (x * ζ) * z⁻¹ := by group
    _ = z * y * (z⁻¹ * x * z) * z⁻¹ := by rw [e1]
    _ = (z * y * z⁻¹) * x := by group

@[expose] def e6CartanAdj : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![4, 3, 5, 6, 4, 2], ![3, 6, 6, 9, 6, 3], ![5, 6, 10, 12, 8, 4], ![6, 9, 12, 18, 12, 6],
    ![4, 6, 8, 12, 10, 5], ![2, 3, 4, 6, 5, 4]]

theorem e6CartanAdj_mul : ∀ i j : Fin Tag.E6.rank,
    ∑ l, e6CartanAdj i l * Tag.cartan Tag.E6 l j = if i = j then 3 else 0 := by
  decide +kernel

theorem exists_e6RootParams_eq {L : Type} [Field L] [IsAlgClosed L]
    (a : Fin Tag.E6.rank → Lˣ) : ∃ u : Fin Tag.E6.rank → Lˣ, e6RootParams u = a := by
  have hv : ∀ i, ∃ v : Lˣ, v ^ 3 = a i := fun i => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (a i : L) (by norm_num : 0 < 3)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hx
      exact (a i).ne_zero hx.symm
    exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hx)⟩
  choose v hv using hv
  refine ⟨fun l => ∏ i, v i ^ e6CartanAdj i l, funext fun j => ?_⟩
  simp only [e6RootParams, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  simp_rw [← CFSG.LieType.Steinberg.CentralExt.AdjointClosed.zpow_sum_eq_prod, e6CartanAdj_mul]
  rw [Finset.prod_eq_single j (fun i _ hij => by rw [ite_eq_right hij, zpow_zero])
    (fun h => absurd (Finset.mem_univ j) h), ite_eq_left rfl, ← hv j]
  norm_cast

theorem exists_units_descent {L : Type} [Field L] (K₃ : Subfield L) {n : ℕ} (a : Fin n → Lˣ)
    (h : ∀ i, (a i : L) ∈ K₃) :
    ∃ a₃ : Fin n → K₃ˣ, (fun i => Units.map K₃.subtype.toMonoidHom (a₃ i)) = a := by
  refine ⟨fun i => Units.mk0 ⟨a i, h i⟩ fun h0 => (a i).ne_zero (congrArg Subtype.val h0),
    funext fun i => Units.ext rfl⟩

theorem units_map_subtype_injective {L : Type} [Field L] (K₃ : Subfield L) :
    Function.Injective (Units.map K₃.subtype.toMonoidHom) := fun _ _ h =>
  Units.ext (Subtype.ext (congrArg Units.val h))

section Isotropic


theorem rootChar_e6Shift_of_isotropic {K : Type} [Field K] [Finite K]
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] {K₁ : Type} [Field K₁]
    [Finite K₁] (ι : K₁ →+* L) {s t : e6Data_valid.minGroup K₁}
    (hst : s * t = t * s) {c z : ModGL Tag.E6 (L)}
    (hc : c ∈ adjointGroup Tag.E6 (L))
    (hz : z ∈ adjointGroup Tag.E6 (L))
    {a b : Fin Tag.E6.rank → (L)ˣ} {w : WeylGroup Tag.E6}
    (ha : c * e6ScToBar K₁ ι s * c⁻¹ = rootDiagUnit Tag.E6 a)
    (hza : rootDiagUnit Tag.E6 a * z = z * rootDiagUnit Tag.E6 a)
    (hb : z * (c * e6ScToBar K₁ ι t * c⁻¹) * z⁻¹ =
      rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) (L) w)
    (hw : w ∈ rootCharStabilizer a) :
    rootChar a (e6Shift w) = 1 := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  classical
  obtain ⟨u, hu⟩ := exists_e6RootParams_eq a
  obtain ⟨u', hu'⟩ := exists_e6RootParams_eq b
  obtain ⟨Ec, hEc⟩ := exists_finset_descent hc
  obtain ⟨Ez, hEz⟩ := exists_finset_descent hz
  obtain ⟨Ev, hEv⟩ : ∃ Ev : Finset (L), ∀ i,
      (u i : L) ∈ Ev ∧ (u' i : L) ∈ Ev ∧
        (a i : L) ∈ Ev ∧ (b i : L) ∈ Ev :=
    ⟨(Finset.univ.image fun i => ((u i : (L)ˣ) : L)) ∪
      (Finset.univ.image fun i => ((u' i : (L)ˣ) : L)) ∪
      (Finset.univ.image fun i => ((a i : (L)ˣ) : L)) ∪
      (Finset.univ.image fun i => ((b i : (L)ˣ) : L)),
      fun i => by simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        exists_apply_eq_apply, or_true, true_or, and_self]⟩
  obtain ⟨K₃, hK₃, hEK₃, -⟩ := exists_finite_subfield_of_finset (K := K)
    (Ec ∪ Ez ∪ Ev ∪ (Set.finite_range ι).toFinset)
  have hmem : ∀ x ∈ Ec ∪ Ez ∪ Ev ∪ (Set.finite_range ι).toFinset, x ∈ K₃ :=
    fun x hx => hEK₃ (Finset.mem_coe.2 hx)
  have hcK : (Ec : Set (L)) ⊆ K₃ := fun x hx =>
    hmem x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hx)))
  have hzK : (Ez : Set (L)) ⊆ K₃ := fun x hx =>
    hmem x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx)))
  have hvK : ∀ x ∈ Ev, x ∈ K₃ := fun x hx =>
    hmem x (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  have hιK : ∀ x, ι x ∈ K₃ := fun x => hmem _ (Finset.mem_union_right _
    ((Set.finite_range ι).mem_toFinset.2 ⟨x, rfl⟩))
  obtain ⟨u₃, hu₃⟩ := exists_units_descent K₃ u fun i => hvK _ (hEv i).1
  obtain ⟨u'₃, hu'₃⟩ := exists_units_descent K₃ u' fun i => hvK _ (hEv i).2.1
  obtain ⟨a₃, ha₃⟩ := exists_units_descent K₃ a fun i => hvK _ (hEv i).2.2.1
  obtain ⟨b₃, hb₃⟩ := exists_units_descent K₃ b fun i => hvK _ (hEv i).2.2.2
  have : Finite K₃ := hK₃
  obtain ⟨ι₃, hιι⟩ : ∃ ι₃ : K₁ →+* K₃, K₃.subtype.comp ι₃ = ι :=
    ⟨ι.codRestrict K₃ hιK, RingHom.ext fun x => rfl⟩
  obtain ⟨c₃, hc₃C, hc₃⟩ := hEc K₃ hcK
  obtain ⟨z₃, hz₃C, hz₃⟩ := hEz K₃ hzK
  obtain ⟨bc, hbc⟩ : ∃ f : ModGL Tag.E6 K₃ →* ModGL Tag.E6 (L),
      f = baseChangeGL K₃.subtype := ⟨_, rfl⟩
  have hbcinj : Function.Injective bc := hbc ▸ baseChangeGL_injective K₃.subtype
  have hc₃' : bc c₃ = c := by rw [hbc]; exact hc₃
  have hz₃' : bc z₃ = z := by rw [hbc]; exact hz₃
  have hpar : ∀ (v : Fin Tag.E6.rank → K₃ˣ) (v' : Fin Tag.E6.rank → (L)ˣ),
      (fun i => Units.map K₃.subtype.toMonoidHom (v i)) = v' → ∀ j,
      Units.map K₃.subtype.toMonoidHom (e6RootParams v j) = e6RootParams v' j := by
    intro v v' hv j
    rw [← hv]
    simp only [e6RootParams, map_prod, map_zpow]
  have hu₃a : e6RootParams u₃ = a₃ := by
    funext j
    apply units_map_subtype_injective K₃
    rw [hpar u₃ u hu₃ j, hu, ← congrFun ha₃ j]
  have hu'₃b : e6RootParams u'₃ = b₃ := by
    funext j
    apply units_map_subtype_injective K₃
    rw [hpar u'₃ u' hu'₃ j, hu', ← congrFun hb₃ j]
  have hda : bc (rootDiagUnit Tag.E6 a₃) = rootDiagUnit Tag.E6 a := by
    rw [hbc, baseChangeGL_rootDiagUnit, ha₃]
  have hdb : bc (rootDiagUnit Tag.E6 b₃) = rootDiagUnit Tag.E6 b := by
    rw [hbc, baseChangeGL_rootDiagUnit, hb₃]
  have hdw : bc (canonicalRep (coxeterSystem Tag.E6) K₃ w) =
      canonicalRep (coxeterSystem Tag.E6) (L) w := by
    rw [hbc, baseChangeGL_canonicalRep]
  obtain ⟨cS, hcS⟩ := e6Isogeny_surjective K₃ ⟨c₃, hc₃C⟩
  obtain ⟨zS, hzS⟩ := e6Isogeny_surjective K₃ ⟨z₃, hz₃C⟩
  obtain ⟨π₃, hπ₃⟩ : ∃ π : e6Data_valid.minGroup K₃ →* ModGL Tag.E6 K₃,
      π = (adjointGroup Tag.E6 K₃).subtype.comp (e6Isogeny K₃) := ⟨_, rfl⟩
  have hπc : π₃ cS = c₃ := by rw [hπ₃, MonoidHom.comp_apply, hcS]; rfl
  have hπz : π₃ zS = z₃ := by rw [hπ₃, MonoidHom.comp_apply, hzS]; rfl
  have hbcπ : ∀ g : e6Data_valid.minGroup K₁,
      bc (π₃ (minBC e6Data_valid ι₃ g)) = e6ScToBar K₁ ι g := by
    intro g
    rw [hπ₃, MonoidHom.comp_apply, Subgroup.coe_subtype, e6Isogeny_minBC, hbc,
      baseChangeGL_baseChangeGL, hιι]
    rfl
  obtain ⟨xS, hxS⟩ : ∃ x, x = cS * minBC e6Data_valid ι₃ s * cS⁻¹ := ⟨_, rfl⟩
  obtain ⟨yS', hyS'⟩ : ∃ y, y = cS * minBC e6Data_valid ι₃ t * cS⁻¹ := ⟨_, rfl⟩
  have hxSπ : π₃ xS = rootDiagUnit Tag.E6 a₃ := by
    apply hbcinj
    rw [hda, ← ha, hxS]
    simp only [map_mul, map_inv, hbcπ, hπc, hc₃']
  have hySπ : π₃ (zS * yS' * zS⁻¹) =
      rootDiagUnit Tag.E6 b₃ * canonicalRep (coxeterSystem Tag.E6) K₃ w := by
    apply hbcinj
    rw [map_mul bc, hdb, hdw, ← hb, hyS']
    simp only [map_mul, map_inv, hbcπ, hπc, hπz, hc₃', hz₃']
  have hst' : minBC e6Data_valid ι₃ s * minBC e6Data_valid ι₃ t =
      minBC e6Data_valid ι₃ t * minBC e6Data_valid ι₃ s := by rw [← map_mul, hst, map_mul]
  have hxy' : xS * yS' = yS' * xS := by
    rw [hxS, hyS']
    calc cS * minBC e6Data_valid ι₃ s * cS⁻¹ * (cS * minBC e6Data_valid ι₃ t * cS⁻¹)
        = cS * (minBC e6Data_valid ι₃ s * minBC e6Data_valid ι₃ t) * cS⁻¹ := by group
      _ = cS * (minBC e6Data_valid ι₃ t * minBC e6Data_valid ι₃ s) * cS⁻¹ := by rw [hst']
      _ = cS * minBC e6Data_valid ι₃ t * cS⁻¹ * (cS * minBC e6Data_valid ι₃ s * cS⁻¹) := by
          group
  have hzx : e6IsogenyT K₃ zS * e6IsogenyT K₃ xS = e6IsogenyT K₃ xS * e6IsogenyT K₃ zS := by
    have key : π₃ zS * π₃ xS = π₃ xS * π₃ zS := by
      rw [hπz, hxSπ]
      apply hbcinj
      rw [map_mul, map_mul, hda, hz₃']
      exact hza.symm
    rw [hπ₃] at key
    exact Subtype.ext key
  have hcomm := commute_conj_of_ker_le_center (e6IsogenyT K₃) (ker_e6IsogenyT_le_center K₃)
    hxy' hzx
  have hw₃ : w ∈ rootCharStabilizer a₃ := by
    intro v
    apply units_map_subtype_injective K₃
    have e1 := rootChar_map_tuple K₃.subtype a₃ (w • v)
    have e2 := rootChar_map_tuple K₃.subtype a₃ v
    rw [ha₃] at e1 e2
    rw [← e1, ← e2]
    exact hw v
  have hx' : ((e6Isogeny K₃ xS : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) =
      rootDiagUnit Tag.E6 a₃ := by
    rw [← hxSπ, hπ₃]
    rfl
  have hy' : ((e6Isogeny K₃ (zS * yS' * zS⁻¹) : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) =
      rootDiagUnit Tag.E6 b₃ * canonicalRep (coxeterSystem Tag.E6) K₃ w := by
    rw [← hySπ, hπ₃]
    rfl
  have hfin := rootChar_e6Shift_of_commute hcomm hx' hy' hu₃a hu'₃b hw₃
  have e3 := rootChar_map_tuple K₃.subtype a₃ (e6Shift w)
  rw [ha₃, hfin, map_one] at e3
  exact e3

end Isotropic


section Plane


theorem exists_conj_mem_torusGroup_of_mem_kernelReflectionGroup {τ : Tag} {p : ℕ}
    (hmon : MonomialToralAt τ p) {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ p)
    {a : Fin τ.rank → Lˣ} {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hwS : weylQuotientHom τ L ⟨n, hn⟩ ∈ kernelReflectionGroup a) (hp : n ^ p = 1) :
    ∃ g ∈ adjointGroup τ L, rootDiagUnit τ a * g = g * rootDiagUnit τ a ∧
      g * n * g⁻¹ ∈ torusGroup τ L := by
  obtain ⟨g, hg, hgn⟩ := hmon L hL Lˣ (rootCharHom3 a) _ hn hwS (weylQuotientHom_pow_eq_one hn hp)
  have hgc : g ∈ Subgroup.centralizer {rootDiagUnit τ a} :=
    CFSG.LieType.Chevalley.rootSpan_le_centralizer a (fun _ h => h) hg
  refine ⟨g, rootSpan_le_adjointGroup L _ hg, ?_, hgn⟩
  exact (Subgroup.mem_centralizer_singleton_iff.1 hgc).symm

theorem exists_conj_le_torusGroup_of_isotropic_plane_E6
    {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) {K₁ : Type} [Field K₁] [Finite K₁]
    (ι : K₁ →+* AlgebraicClosure K) {S : Subgroup (e6Data_valid.minGroup K₁)}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {A : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))}
    (hAS : A ≤ S.map (e6ScToBar K₁ ι)) (hexp : ∀ x ∈ A, x ^ 3 = 1) (hcard : Nat.card A = 3 ^ 2) :
    ∃ C ∈ adjointGroup Tag.E6 (AlgebraicClosure K), ∀ x ∈ A,
      C * x * C⁻¹ ∈ torusGroup Tag.E6 (AlgebraicClosure K) := by
  classical
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp1 : 1 < 3 := by norm_num
  obtain ⟨ℓ, hℓK⟩ := CharP.exists K
  have hℓp : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hℓ : ℓ ≠ 3 := by
    rintro rfl
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 3
    apply h3
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 3 n.ne_zero
  have halg := isAlgebraic_zmod_algebraicClosure_of_finite K ℓ
  have hLp : ringChar (AlgebraicClosure K) ≠ 3 := by
    rw [ringChar.eq (AlgebraicClosure K) ℓ]
    exact hℓ
  have hmon := monomialToralAt_E6_three
  have hA : A ≤ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    intro x hx
    obtain ⟨s, -, rfl⟩ := hAS hx
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι (e6Isogeny K₁ s).2
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    obtain ⟨s, hs, rfl⟩ := hAS hx
    obtain ⟨t, ht, rfl⟩ := hAS hy
    rw [← map_mul, hS s hs t ht, map_mul]
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hAfin : (A : Set (ModGL Tag.E6 (AlgebraicClosure K))).Finite := Set.toFinite _
  obtain ⟨x₀, hx₀A, hx₀1⟩ : ∃ x ∈ A, x ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨c₁, hc₁, hc₁N⟩ := exists_conj_le_monomial_bar hℓ halg hA hAfin hexp
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_mem_monomial hmon hLp (hc₁N x₀ hx₀A)
    (conj_pow_eq_one' c₁ (hexp x₀ hx₀A))
  obtain ⟨c, hcdef⟩ : ∃ c, c = g * c₁ := ⟨_, rfl⟩
  have hcC : c ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := hcdef ▸ mul_mem hg hc₁
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgn
  have hda : c * x₀ * c⁻¹ = rootDiagUnit Tag.E6 a := by
    rw [← ha, hcdef]
    group
  have hap : ∀ i, a i ^ 3 = 1 := by
    have h : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 1 := by
      rw [rootDiagUnit_pow', rootDiagUnit_one, ← hda, conj_pow_eq_one' c (hexp x₀ hx₀A)]
    intro i
    have := congrFun (rootDiagUnit_injective h) i
    simpa using this
  obtain ⟨A', hA'⟩ : ∃ A' : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)),
      A' = A.map (MulAut.conj c).toMonoidHom := ⟨_, rfl⟩
  have hA'mem : ∀ x ∈ A, c * x * c⁻¹ ∈ A' := fun x hx => hA' ▸ ⟨x, hx, rfl⟩
  have hA'C : A' ≤ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hA']
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hcC (hA hx)) (inv_mem hcC)
  have hA'fin : (A' : Set (ModGL Tag.E6 (AlgebraicClosure K))).Finite := by
    rw [hA']
    exact Set.Finite.image _ hAfin
  have hA'a : ∀ y ∈ A', rootDiagUnit Tag.E6 a * y = y * rootDiagUnit Tag.E6 a := by
    rw [hA']
    rintro _ ⟨x, hx, rfl⟩
    change rootDiagUnit Tag.E6 a * (c * x * c⁻¹) = c * x * c⁻¹ * rootDiagUnit Tag.E6 a
    rw [← hda]
    calc c * x₀ * c⁻¹ * (c * x * c⁻¹) = c * (x₀ * x) * c⁻¹ := by group
      _ = c * (x * x₀) * c⁻¹ := by rw [hcomm x₀ hx₀A x hx]
      _ = c * x * c⁻¹ * (c * x₀ * c⁻¹) := by group
  have hA'exp : ∀ y ∈ A', y ^ 3 = 1 := by
    rw [hA']
    rintro _ ⟨x, hx, rfl⟩
    exact conj_pow_eq_one' c (hexp x hx)
  obtain ⟨z, hz, hzd, hzN⟩ := exists_conj_le_monomial_centralizer_bar hℓ halg a hA'C hA'fin hA'a
    hA'exp
  have hx₀ord : orderOf x₀ = 3 := orderOf_eq_prime (hexp x₀ hx₀A) hx₀1
  obtain ⟨y₀, hy₀A, hy₀⟩ : ∃ y ∈ A, y ∉ Subgroup.zpowers x₀ := by
    by_contra h
    push Not at h
    have heq : A = Subgroup.zpowers x₀ :=
      le_antisymm (fun y hy => h y hy) ((Subgroup.zpowers_le).2 hx₀A)
    rw [heq, Nat.card_zpowers, hx₀ord] at hcard
    omega
  obtain ⟨n', hn'⟩ : ∃ n, n = z * (c * y₀ * c⁻¹) * z⁻¹ := ⟨_, rfl⟩
  have hn'N : n' ∈ monomialSubgroup Tag.E6 (AlgebraicClosure K) := hn' ▸ hzN _ (hA'mem y₀ hy₀A)
  have hn'a : rootDiagUnit Tag.E6 a * n' = n' * rootDiagUnit Tag.E6 a := by
    have h1 := hA'a _ (hA'mem y₀ hy₀A)
    have hzd' : rootDiagUnit Tag.E6 a * z⁻¹ = z⁻¹ * rootDiagUnit Tag.E6 a := by
      calc rootDiagUnit Tag.E6 a * z⁻¹ = z⁻¹ * (z * rootDiagUnit Tag.E6 a) * z⁻¹ := by group
        _ = z⁻¹ * (rootDiagUnit Tag.E6 a * z) * z⁻¹ := by rw [hzd]
        _ = z⁻¹ * rootDiagUnit Tag.E6 a := by group
    calc rootDiagUnit Tag.E6 a * n' = (rootDiagUnit Tag.E6 a * z) * (c * y₀ * c⁻¹) * z⁻¹ := by
          rw [hn']; group
      _ = z * (rootDiagUnit Tag.E6 a * (c * y₀ * c⁻¹)) * z⁻¹ := by rw [hzd]; group
      _ = z * (c * y₀ * c⁻¹) * (rootDiagUnit Tag.E6 a * z⁻¹) := by rw [h1]; group
      _ = n' * rootDiagUnit Tag.E6 a := by rw [hzd', hn']; group
  have hn'p : n' ^ 3 = 1 := hn' ▸ conj_pow_eq_one' z (hA'exp _ (hA'mem y₀ hy₀A))
  obtain ⟨w, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hn'N
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hk
  have hπ : weylQuotientHom Tag.E6 (AlgebraicClosure K) ⟨n', hn'N⟩ = w := by
    have hn'N' : k * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w ∈
        monomialSubgroup Tag.E6 (AlgebraicClosure K) := e ▸ hn'N
    have h := weylQuotientHom_torus_mul hk w hn'N'
    have e' : (⟨n', hn'N⟩ : monomialSubgroup Tag.E6 (AlgebraicClosure K)) = ⟨_, hn'N'⟩ :=
      Subtype.ext e
    rw [e', h]
  have hw : w ∈ rootCharStabilizer a := by
    rw [← conj_canonicalRep_eq_iff]
    have hdk : rootDiagUnit Tag.E6 a * k = k * rootDiagUnit Tag.E6 a :=
      rootDiagUnit_mul_comm_of_mem_torusGroup a hk
    have hna : rootDiagUnit Tag.E6 a * (k * canonicalRep (coxeterSystem Tag.E6) _ w) =
        (k * canonicalRep (coxeterSystem Tag.E6) _ w) * rootDiagUnit Tag.E6 a := by
      rw [← e]
      exact hn'a
    have h1 : rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w =
        canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w * rootDiagUnit Tag.E6 a := by
      have e1 : rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w =
          k⁻¹ * (rootDiagUnit Tag.E6 a *
            (k * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)) := by
        rw [← mul_assoc (rootDiagUnit Tag.E6 a) k, hdk]
        group
      rw [e1, hna]
      group
    rw [h1, mul_inv_cancel_right]
  obtain ⟨s₀, hs₀, hs₀x⟩ := hAS hx₀A
  obtain ⟨t₀, ht₀, ht₀y⟩ := hAS hy₀A
  have h1 : rootChar a (e6Shift w) = 1 := by
    refine rootChar_e6Shift_of_isotropic (K := K) ι (hS s₀ hs₀ t₀ ht₀) hcC hz (a := a) (b := b) ?_
      hzd ?_ hw
    · rw [hs₀x]
      exact hda
    · rw [ht₀y, ← hn', e, hb]
  have hwS : w ∈ kernelReflectionGroup a := mem_kernelReflectionGroup_of_e6Shift a hap hw h1
  obtain ⟨g', hg', hg'd, hg'n⟩ := exists_conj_mem_torusGroup_of_mem_kernelReflectionGroup hmon
    hLp hn'N (hπ ▸ hwS) hn'p
  refine ⟨g' * z * c, mul_mem (mul_mem hg' hz) hcC, ?_⟩
  obtain ⟨S', hS'⟩ : ∃ S' : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)),
      S' = A ⊓ (torusGroup Tag.E6 (AlgebraicClosure K)).comap
        (MulAut.conj (g' * z * c)).toMonoidHom := ⟨_, rfl⟩
  have hx₀S : x₀ ∈ S' := by
    rw [hS']
    refine ⟨hx₀A, ?_⟩
    change g' * z * c * x₀ * (g' * z * c)⁻¹ ∈ torusGroup Tag.E6 (AlgebraicClosure K)
    have e1 : g' * z * c * x₀ * (g' * z * c)⁻¹ =
        g' * (z * rootDiagUnit Tag.E6 a * z⁻¹) * g'⁻¹ := by
      rw [← hda]
      group
    have hzd'' : z * rootDiagUnit Tag.E6 a * z⁻¹ = rootDiagUnit Tag.E6 a := by
      rw [← hzd, mul_inv_cancel_right]
    have hg'd' : g' * rootDiagUnit Tag.E6 a * g'⁻¹ = rootDiagUnit Tag.E6 a := by
      rw [← hg'd, mul_inv_cancel_right]
    rw [e1, hzd'', hg'd']
    exact ha ▸ hgn
  have hy₀S : y₀ ∈ S' := by
    rw [hS']
    refine ⟨hy₀A, ?_⟩
    change g' * z * c * y₀ * (g' * z * c)⁻¹ ∈ torusGroup Tag.E6 (AlgebraicClosure K)
    have e1 : g' * z * c * y₀ * (g' * z * c)⁻¹ = g' * n' * g'⁻¹ := by
      rw [hn']
      group
    rw [e1]
    exact hg'n
  have hSA : S' ≤ A := by rw [hS']; exact inf_le_left
  have hle : Subgroup.zpowers x₀ ≤ S' := (Subgroup.zpowers_le).2 hx₀S
  have hlt : Subgroup.zpowers x₀ < S' := lt_of_le_of_ne hle fun h => hy₀ (h ▸ hy₀S)
  have : Finite S' := Finite.of_injective (Subgroup.inclusion hSA) (Subgroup.inclusion_injective _)
  have h1' := Subgroup.card_lt_of_lt hlt
  rw [Nat.card_zpowers, hx₀ord] at h1'
  have h2 : Nat.card S' ∣ Nat.card A := Subgroup.card_dvd_of_le hSA
  rw [hcard] at h2
  have h3' : Nat.card S' = 3 ^ 2 := by
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow hp.out).1 h2
    interval_cases m
    · rw [hm', pow_zero] at h1'
      omega
    · rw [hm', pow_one] at h1'
      omega
    · exact hm'
  have hSA' : S' = A := Subgroup.eq_of_le_of_card_ge hSA (by rw [h3', hcard])
  intro x hx
  rw [← hSA', hS'] at hx
  exact hx.2

end Plane

section Lang


theorem exists_lang_torus_of_conj_torus {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ] (f : ℕ) (hf : 1 ≤ f) {p : ℕ} (hpq : Nat.Coprime p (ℓ ^ f))
    {A : Subgroup (ModGL τ L)} (hexp : ∀ x ∈ A, x ^ p = 1)
    (hFix : ∀ x ∈ A, entrywiseFrobGL τ L ℓ f x = x) {g : ModGL τ L}
    (hg : g ∈ adjointGroup τ L) (hgA : ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup τ L) :
    ∃ w : WeylGroup τ, ∃ g0 ∈ adjointGroup τ L,
      entrywiseFrobGL τ L ℓ f g0 = g0 * canonicalRep (coxeterSystem τ) L w ∧
      ∀ x ∈ A, x ∈ (twistedTorusOf (canonicalRep (coxeterSystem τ) L w)
        (entrywiseFrobGL τ L ℓ f)).map (MulAut.conj g0).toMonoidHom := by
  classical
  choose a ha using fun x : A => exists_rootDiagUnit_eq_of_mem_torusGroup (hgA x x.2)
  have hexp' : ∀ (x : A) i, a x i ^ p = 1 := by
    intro x
    have h1 : rootDiagUnit τ (a x ^ p) = rootDiagUnit τ 1 := by
      have : rootDiagUnit τ (a x ^ p) = rootDiagUnit τ (a x) ^ p :=
        ((rootDiagUnitHom τ L).map_pow (a x) p)
      rw [this, ← ha x, rootDiagUnit_one]
      calc (g⁻¹ * (x : ModGL τ L) * g) ^ p = g⁻¹ * (x : ModGL τ L) ^ p * g := by
            have := conj_pow (a := g⁻¹) (b := (x : ModGL τ L)) (i := p)
            rwa [inv_inv] at this
        _ = 1 := by rw [hexp x x.2]; group
    have h2 : a x ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have hn : ∀ x : A, (g⁻¹ * entrywiseFrobGL τ L ℓ f g) *
      entrywiseFrobGL τ L ℓ f (rootDiagUnit τ (a x)) *
      (g⁻¹ * entrywiseFrobGL τ L ℓ f g)⁻¹ = rootDiagUnit τ (a x) := by
    intro x
    rw [← ha x, map_mul, map_mul, map_inv, hFix x x.2]
    group
  obtain ⟨w', z, hz, hlang⟩ := exists_lang_datum_of_plane ℓ f hf hpq a hexp' hg hn
  have hzC := familyGroup_le_familyCentralizer (K := L) a hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hu : entrywiseFrobGL τ L ℓ f (g * z) =
      (g * z) * canonicalRep (coxeterSystem τ) L w' := inv_mul_eq_iff_eq_mul.1 hlang
  refine ⟨w', g * z, mul_mem hg hzG, hu, fun x hx => ?_⟩
  obtain ⟨d, hd⟩ : ∃ d, d = rootDiagUnit τ (a ⟨x, hx⟩) := ⟨_, rfl⟩
  have hzd : z⁻¹ * d * z = d := by
    have := hzcomm ⟨x, hx⟩
    rw [← hd, mul_inv_eq_iff_eq_mul] at this
    calc z⁻¹ * d * z = z⁻¹ * (d * z) := by group
      _ = z⁻¹ * (z * d) := by rw [this]
      _ = d := by group
  have ht : (g * z)⁻¹ * x * (g * z) = d := by
    have h0 := ha ⟨x, hx⟩
    rw [← hd] at h0
    calc (g * z)⁻¹ * x * (g * z) = z⁻¹ * (g⁻¹ * x * g) * z := by group
      _ = d := by rw [h0, hzd]
  refine ⟨(g * z)⁻¹ * x * (g * z), ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_twistedTorusOf, ht]
    refine ⟨hd ▸ rootDiagUnit_mem_torusGroup _, ?_⟩
    have hFd : entrywiseFrobGL τ L ℓ f d =
        (canonicalRep (coxeterSystem τ) L w')⁻¹ * d * canonicalRep (coxeterSystem τ) L w' := by
      rw [← ht, map_mul, map_mul, map_inv, hFix x hx, hu]
      group
    rw [hFd]
    group
  · change (g * z) * ((g * z)⁻¹ * x * (g * z)) * (g * z)⁻¹ = x
    group

end Lang

theorem e6PlaneToralLang_proved :
    E6PlaneToralLang := by
  intro K _ _ h3 K₁ _ _ ι S hS A hAS hexp hcard Fr hFr hFix
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  have : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hFr' : Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ) :=
    RingHom.ext fun c => by rw [hFr, iterateFrobenius_def, Nat.card_eq_fintype_card, hf]
  subst hFr'
  obtain ⟨C, hC, hCA⟩ := exists_conj_le_torusGroup_of_isotropic_plane_E6 h3 ι hS hAS hexp hcard
  have hpq : Nat.Coprime 3 (ringChar K ^ (f : ℕ)) := by
    rw [← hf, ← Nat.card_eq_fintype_card]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  exact exists_lang_torus_of_conj_torus (f : ℕ) f.pos hpq hexp hFix (inv_mem hC)
    fun x hx => by rw [inv_inv]; exact hCA x hx

end CFSG.HardMathSupport.Timmesfeld.CrossChar
