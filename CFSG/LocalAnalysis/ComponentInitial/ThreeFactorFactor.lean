module

public import CFSG.LocalAnalysis.ComponentInitial.EmptyLayerCharTwo
public import CFSG.LocalAnalysis.ComponentInitial.FactorwiseFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {G : Type*} [Group G]

theorem map_conj_eq_of_mem_normalizer {A : Subgroup G} {u : G}
    (hu : u ∈ normalizer (A : Set G)) : A.map (MulAut.conj u).toMonoidHom = A :=
  conjSub_eq_of_mem_normalizer hu

@[expose] def conjAut (A : Subgroup G) {u : G} (hu : u ∈ normalizer (A : Set G)) : MulAut A :=
  restrictAut (MulAut.conj u) A (map_conj_eq_of_mem_normalizer hu)

theorem coe_conjAut {A : Subgroup G} {u : G} (hu : u ∈ normalizer (A : Set G)) (x : A) :
    ((conjAut A hu x : A) : G) = u * x * u⁻¹ := rfl

theorem map_fixed_conjAut {A : Subgroup G} {u : G} (hu : u ∈ normalizer (A : Set G)) :
    (fixedSubgroup (conjAut A hu)).map A.subtype = A ⊓ centralizer ({u} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.2 ⟨y.2, ?_⟩
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.1 hw]
    have h := congrArg Subtype.val (show conjAut A hu y = y from hy)
    rw [coe_conjAut] at h
    calc u * (y : G) = u * y * u⁻¹ * u := by group
      _ = y * u := by rw [h]
  · intro hx
    obtain ⟨hxA, hxu⟩ := Subgroup.mem_inf.1 hx
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    change conjAut A hu ⟨x, hxA⟩ = ⟨x, hxA⟩
    apply Subtype.ext
    rw [coe_conjAut]
    have h := mem_centralizer_iff.1 hxu u rfl
    rw [h, mul_inv_cancel_right]

theorem card_modEq_card_fixedSubgroup {S : Type*} [Group S] [Finite S] (α : MulAut S)
    (hα : ∀ s, α (α s) = s) : Nat.card S ≡ Nat.card (fixedSubgroup α) [MOD 2] := by
  classical
  have : Fintype S := Fintype.ofFinite S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Function.End S := (α : S → S)
  have hf : f ^ 2 ^ 1 = 1 := by
    funext s
    show α (α s) = s
    exact hα s
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf
  rw [Nat.card_eq_fintype_card]
  have hfix : Nat.card (fixedSubgroup α) = Fintype.card (Function.fixedPoints f) := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hfix]
  exact h

section Factor

variable {A : Subgroup G} {u : G}

theorem conjAut_conjAut (hu : orderOf u = 2) (hnorm : u ∈ normalizer (A : Set G)) (x : A) :
    conjAut A hnorm (conjAut A hnorm x) = x := by
  apply Subtype.ext
  rw [coe_conjAut, coe_conjAut]
  have hu' : u⁻¹ = u := inv_eq_self_of_orderOf_eq_two hu
  calc u * (u * x * u⁻¹) * u⁻¹ = u * u * x * (u⁻¹ * u⁻¹) := by group
    _ = x := by
      rw [show u * u = 1 by rw [← sq, ← hu, pow_orderOf_eq_one], hu',
        show u * u = 1 by rw [← sq, ← hu, pow_orderOf_eq_one]]
      group

noncomputable abbrev quotientConjAut (hnorm : u ∈ normalizer (A : Set G)) :
    MulAut (A ⧸ center A) :=
  PerfectAutomorphisms.centerQuotientHom A (conjAut A hnorm)

theorem quotientConjAut_mk (hnorm : u ∈ normalizer (A : Set G)) (x : A) :
    quotientConjAut hnorm (QuotientGroup.mk' (center A) x) =
      QuotientGroup.mk' (center A) (conjAut A hnorm x) :=
  PerfectAutomorphisms.onCenterQuotient_apply_mk _ x

theorem quotientConjAut_sq (hu : orderOf u = 2) (hnorm : u ∈ normalizer (A : Set G))
    (s : A ⧸ center A) : quotientConjAut hnorm (quotientConjAut hnorm s) = s := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center A) s
  rw [quotientConjAut_mk, quotientConjAut_mk, conjAut_conjAut hu]

theorem quotientConjAut_ne_one (hA : CFSG.Assembly.IsQuasisimple A)
    (hnorm : u ∈ normalizer (A : Set G)) (hncent : u ∉ centralizer (A : Set G)) :
    quotientConjAut hnorm ≠ 1 := by
  intro h
  have : Group.IsPerfect A := ⟨hA.1⟩
  have h1 : conjAut A hnorm = 1 := PerfectAutomorphisms.centerQuotientHom_injective A
    (h.trans (map_one _).symm)
  apply hncent
  rw [mem_centralizer_iff]
  intro x hx
  have h2 := congrArg Subtype.val (congrArg (fun φ : MulAut A => φ ⟨x, hx⟩) h1)
  simp only [coe_conjAut, MulAut.one_apply] at h2
  calc x * u = u * x * u⁻¹ * u := by rw [h2]
    _ = u * x := by group

theorem orderOf_quotientConjAut (hA : CFSG.Assembly.IsQuasisimple A) (hu : orderOf u = 2)
    (hnorm : u ∈ normalizer (A : Set G)) (hncent : u ∉ centralizer (A : Set G)) :
    orderOf (quotientConjAut hnorm) = 2 := by
  refine orderOf_eq_prime ?_ (quotientConjAut_ne_one hA hnorm hncent)
  refine MulEquiv.ext fun s => ?_
  rw [sq, MulAut.mul_apply, quotientConjAut_sq hu, MulAut.one_apply]

theorem quotient_center_simple_nonabelian (hA : CFSG.Assembly.IsQuasisimple A) :
    IsSimpleGroup (A ⧸ center A) ∧ ∃ x y : A ⧸ center A, x * y ≠ y * x := by
  obtain ⟨-, hs, hnab⟩ := (AssemblyBPredicates.isQuasisimple_iff_native A).1 hA
  exact ⟨hs, hnab⟩

theorem even_card_of_simple_nonabelian {S : Type*} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hnab : ∃ x y : S, x * y ≠ y * x) : Even (Nat.card S) := by
  rw [← Nat.not_odd_iff_even]
  intro hodd
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨x, y, hxy⟩ := hnab
  have := hs
  exact hxy ((IsSimpleGroup.comm_iff_isSolvable).2 hsolv x y)

theorem even_card_fixed_quotientConjAut [Finite G] (hA : CFSG.Assembly.IsQuasisimple A) (hu : orderOf u = 2)
    (hnorm : u ∈ normalizer (A : Set G)) :
    Even (Nat.card (fixedSubgroup (quotientConjAut hnorm))) := by
  obtain ⟨hs, hnab⟩ := quotient_center_simple_nonabelian hA
  have heven := even_card_of_simple_nonabelian hs hnab
  have hmod := card_modEq_card_fixedSubgroup _ (quotientConjAut_sq hu hnorm)
  rw [Nat.even_iff] at heven ⊢
  rw [Nat.ModEq] at hmod
  omega

end Factor

section FactorImage

variable [Finite G] {A : Subgroup G} {u : G}

@[expose] noncomputable def fixedImageHom (hnorm : u ∈ normalizer (A : Set G)) :
    fixedSubgroup (conjAut A hnorm) →*
      ((fixedSubgroup (conjAut A hnorm)).map (QuotientGroup.mk' (center A))).subgroupOf
        (fixedSubgroup (quotientConjAut hnorm)) where
  toFun x := ⟨⟨QuotientGroup.mk' (center A) x, by
      change quotientConjAut hnorm _ = _
      rw [quotientConjAut_mk, show conjAut A hnorm x = x from x.2]
      rfl⟩, ⟨x, x.2, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
theorem coe_fixedImageHom (hnorm : u ∈ normalizer (A : Set G))
    (x : fixedSubgroup (conjAut A hnorm)) :
    (((fixedImageHom hnorm x : _) : fixedSubgroup (quotientConjAut hnorm)) : A ⧸ center A) =
      QuotientGroup.mk' (center A) x := rfl

omit [Finite G] in
theorem fixedImageHom_surjective (hnorm : u ∈ normalizer (A : Set G)) :
    Function.Surjective (fixedImageHom hnorm) := by
  intro z
  obtain ⟨x, hx, hxz⟩ := z.2
  exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hxz)⟩

omit [Finite G] in
theorem ker_fixedImageHom (hnorm : u ∈ normalizer (A : Set G)) :
    (fixedImageHom hnorm).ker = (center A ⊓ fixedSubgroup (conjAut A hnorm)).subgroupOf
      (fixedSubgroup (conjAut A hnorm)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have key : fixedImageHom hnorm x = 1 ↔ QuotientGroup.mk' (center A) (x : A) = 1 := by
    constructor
    · intro h
      exact congrArg Subtype.val (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext (Subtype.ext h)
  rw [key, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩

omit [Finite G] in
theorem ker_fixedImageHom_le_center (hnorm : u ∈ normalizer (A : Set G)) :
    (fixedImageHom hnorm).ker ≤ center (fixedSubgroup (conjAut A hnorm)) := by
  intro x hx
  rw [ker_fixedImageHom, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subtype.ext (congrArg Subtype.val (Subgroup.mem_center_iff.1 hx.1 y)))

theorem fixed_quotient_two_components_ordinary (hu : orderOf u = 2)
    (hnorm : u ∈ normalizer (A : Set G))
    (h2B : ∀ L : Subgroup (fixedSubgroup (conjAut A hnorm)),
      CFSG.IsPComponent 2 L → CFSG.IsComponent L) :
    ∀ L : Subgroup (fixedSubgroup (quotientConjAut hnorm)),
      CFSG.IsPComponent 2 L → CFSG.IsComponent L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ := QuotientGroup.mk'_surjective (center A)
  have hK : (QuotientGroup.mk' (center A)).ker ≤ center A := by
    rw [QuotientGroup.ker_mk']
  obtain ⟨hN, -, hab⟩ := fixedImage_quotient_embedding hK hπ (conjAut_conjAut hu hnorm)
    (fun x => (quotientConjAut_mk hnorm x).symm)
  have : Group.IsSolvable (fixedSubgroup (quotientConjAut hnorm) ⧸
      ((fixedSubgroup (conjAut A hnorm)).map (QuotientGroup.mk' (center A))).subgroupOf
        (fixedSubgroup (quotientConjAut hnorm))) :=
    Group.isSolvable_of_comm fun x y => hab.is_comm.comm x y
  intro L hL
  have hq := CatalogueBFixedCentralQuotient.pComponent_quasisimple_of_normal_solvable_quotient 2
    (((fixedSubgroup (conjAut A hnorm)).map (QuotientGroup.mk' (center A))).subgroupOf
      (fixedSubgroup (quotientConjAut hnorm))) (fun J hJ => ?_) L hL
  · obtain ⟨_, _, hsub, _⟩ := hL
    exact ⟨hq, hsub⟩
  · obtain ⟨-, hlift, hdown⟩ := CatalogueBCentralQuotient.central_quotient_p_component_bijection
      2 Nat.prime_two (fixedImageHom hnorm) (fixedImageHom_surjective hnorm)
      (ker_fixedImageHom_le_center hnorm)
    obtain ⟨hL', hmap⟩ := hdown J hJ
    have hq' := (h2B _ hL').1
    have h3 := ((hlift _ hL').2.2).1 hq'
    rwa [hmap] at h3

end FactorImage

section FactorConfiguration

variable {A : Subgroup G} {u : G}

@[expose] def FixedFactorConclusions (A : Subgroup G) {u : G}
    (hnorm : u ∈ normalizer (A : Set G)) : Prop :=
  let π := QuotientGroup.mk' (center A)
  let α := quotientConjAut hnorm
  let B := fixedSubgroup (conjAut A hnorm)
  let C := fixedSubgroup α
  let I' := (B.map π).subgroupOf C
  let f := fixedImageHom hnorm
  let R := pPrimeCore 2 B
  let D := pPrimeCore 2 C
  let P := pCore 2 (B ⧸ R)
  let T := pCore 2 (C ⧸ D)
  (IsSimpleGroup (A ⧸ center A) ∧ ∃ x y : A ⧸ center A, x * y ≠ y * x) ∧ orderOf α = 2 ∧
    Even (Nat.card B) ∧ Even (Nat.card C) ∧
    (π.comp B.subtype).ker = (center A ⊓ B).subgroupOf B ∧
    (∃ _ : I'.Normal, IsElementaryAbelian 2 (C ⧸ I')) ∧
    Set.BijOn (Subgroup.map π) {Q | CFSG.Assembly.IsComponentOf Q B}
      {R | CFSG.Assembly.IsComponentOf R C} ∧ layer C = ⊥ ∧
    (∀ L : Subgroup B, CFSG.IsPComponent 2 L → CFSG.IsComponent L) ∧
    (∀ L : Subgroup C, CFSG.IsPComponent 2 L → CFSG.IsComponent L) ∧
    (∀ L : Subgroup B, ¬ CFSG.IsPComponent 2 L) ∧ (∀ L : Subgroup C, ¬ CFSG.IsPComponent 2 L) ∧
    D ≤ I' ∧ (pPrimeCore 2 I').map I'.subtype = D ∧ (R.map f).map I'.subtype = D ∧
    (D.subgroupOf I').comap f = R ⊔ f.ker ∧ R ⊓ f.ker = (pPrimeCore 2 f.ker).map f.ker.subtype ∧
    (∃ β : B ⧸ R →* I' ⧸ D.subgroupOf I',
      (∀ b : B, β b = ((f b : I') : I' ⧸ D.subgroupOf I')) ∧ Function.Surjective β ∧
      β.ker = f.ker.map (QuotientGroup.mk' R) ∧ β.ker ≤ center (B ⧸ R) ∧ IsPGroup 2 β.ker ∧
      (∀ S : Sylow 2 f.ker,
        Function.Injective
          ((QuotientGroup.mk' R).comp (f.ker.subtype.comp (S : Subgroup f.ker).subtype)) ∧
        ((QuotientGroup.mk' R).comp (f.ker.subtype.comp (S : Subgroup f.ker).subtype)).range =
          β.ker) ∧
      P.map β = pCore 2 (I' ⧸ D.subgroupOf I') ∧
      pCore 2 (I' ⧸ D.subgroupOf I') = T.comap (quotientInclusion I' D) ∧
      (T.comap (quotientInclusion I' D)).comap β = P ∧ β.ker ≤ P) ∧
    fittingSubgroup (B ⧸ R) = P ∧ generalizedFitting (B ⧸ R) = P ∧ P ≠ ⊥ ∧
      layer (B ⧸ R) = ⊥ ∧ pPrimeCore 2 (B ⧸ R) = ⊥ ∧
      centralizer (P : Set (B ⧸ R)) = (center P).map P.subtype ∧ IsCharacteristicP 2 (B ⧸ R) ∧
    fittingSubgroup (C ⧸ D) = T ∧ generalizedFitting (C ⧸ D) = T ∧ T ≠ ⊥ ∧
      layer (C ⧸ D) = ⊥ ∧ pPrimeCore 2 (C ⧸ D) = ⊥ ∧
      centralizer (T : Set (C ⧸ D)) = (center T).map T.subtype ∧ IsCharacteristicP 2 (C ⧸ D) ∧
    (MulAut.conjNormal (H := P)).ker = (center P).map P.subtype ∧
    (MulAut.conjNormal (H := T)).ker = (center T).map T.subtype ∧
    (Group.IsSolvable B ↔ Group.IsSolvable C) ∧
    (Group.IsSolvable B ↔ Group.IsSolvable (MulAut.conjNormal (H := P)).range) ∧
    (Group.IsSolvable C ↔ Group.IsSolvable (MulAut.conjNormal (H := T)).range)

theorem fixedFactorConclusions_of [Finite G] (hA : CFSG.Assembly.IsQuasisimple A)
    (hu : orderOf u = 2) (hnorm : u ∈ normalizer (A : Set G))
    (hncent : u ∉ centralizer (A : Set G)) (hE : layer (fixedSubgroup (conjAut A hnorm)) = ⊥)
    (h2B : ∀ L : Subgroup (fixedSubgroup (conjAut A hnorm)),
      CFSG.IsPComponent 2 L → CFSG.IsComponent L)
    (hBeven : Even (Nat.card (fixedSubgroup (conjAut A hnorm)))) :
    FixedFactorConclusions A hnorm := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ := QuotientGroup.mk'_surjective (center A)
  have hK : (QuotientGroup.mk' (center A)).ker ≤ center A := by rw [QuotientGroup.ker_mk']
  have ha := conjAut_conjAut hu hnorm
  have hα := quotientConjAut_sq hu hnorm
  have hcomm : ∀ x, QuotientGroup.mk' (center A) (conjAut A hnorm x) =
      quotientConjAut hnorm (QuotientGroup.mk' (center A) x) := fun x =>
    (quotientConjAut_mk hnorm x).symm
  obtain ⟨⟨hN, hab, -⟩, hkerB, hbij, -, -, -, -, hiff⟩ :=
    full_central_kernel_involution_fixed_component_correspondence hπ hK ha hα hcomm
  rw [QuotientGroup.ker_mk'] at hkerB
  have hCeven := even_card_fixed_quotientConjAut hA hu hnorm
  have hlayerC : layer (fixedSubgroup (quotientConjAut hnorm)) = ⊥ := hiff.1 hE
  have h2C := fixed_quotient_two_components_ordinary hu hnorm h2B
  have hCI : IsPGroup 2 (fixedSubgroup (quotientConjAut hnorm) ⧸
      ((fixedSubgroup (conjAut A hnorm)).map (QuotientGroup.mk' (center A))).subgroupOf
        (fixedSubgroup (quotientConjAut hnorm))) := fun g => ⟨1, by
    obtain ⟨k, hk⟩ := hab.exponent_dvd_p
    rw [pow_one, show (2 : ℕ) = Monoid.exponent _ * k from hk, pow_mul,
      Monoid.pow_exponent_eq_one, one_pow]⟩
  obtain ⟨o1, o2, o3, o4, o5, β, o6, o7, o8, o9, o10, o11, -, -, o12, o13, o14, o15, o16⟩ :=
    central_quotient_normal_two_index_odd_core_correspondence hCI (fixedImageHom hnorm)
      (fixedImageHom_surjective hnorm) (ker_fixedImageHom_le_center hnorm)
  obtain ⟨hnoB, hlB, hcB, hFB, hFsB, hcentB, hcharB, -, hevB, -, hkerρ, -, hsolρ⟩ :=
    empty_layer_ordinary_two_components_force_characteristic_two_quotient h2B hE
  obtain ⟨hnoC, hlC, hcC, hFC, hFsC, hcentC, hcharC, -, hevC, -, hkerσ, -, hsolσ⟩ :=
    empty_layer_ordinary_two_components_force_characteristic_two_quotient h2C hlayerC
  exact ⟨quotient_center_simple_nonabelian hA, orderOf_quotientConjAut hA hu hnorm hncent,
    hBeven, hCeven, hkerB, ⟨hN, hab⟩, hbij, hlayerC, h2B, h2C, hnoB, hnoC,
    o1, o2, o3, o4, o5, ⟨β, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15⟩,
    hFB, hFsB, (hevB hBeven).2, hlB, hcB, hcentB, hcharB,
    hFC, hFsC, (hevC hCeven).2, hlC, hcC, hcentC, hcharC,
    hkerρ, hkerσ, o16, hsolρ, hsolσ⟩

end FactorConfiguration

end CFSG.LocalAnalysis.ComponentInitial
