module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Module
open LinearMap (BilinForm)
open TauCeti.BilinForm (isometryGroup mem_isometryGroup_iff)

theorem factorization_card_isometryGroup_of_isAlt {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] (B : BilinForm (ZMod 2) W)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) {r : ℕ} (hr : finrank (ZMod 2) W = 2 * r) :
    (Nat.card (isometryGroup B)).factorization 2 = r ^ 2 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup r B hB hnd hr,
    Nat.card_zmod]
  have hodd : ¬ 2 ∣ ∏ j ∈ Finset.Icc 1 r, (2 ^ (2 * j) - 1) := by
    rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
    rintro ⟨j, hj, hdvd⟩
    rw [Finset.mem_Icc] at hj
    have h2 : 2 ∣ 2 ^ (2 * j) := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ (2 * j) := Nat.one_le_two_pow
    generalize 2 ^ (2 * j) = t at h1 h2 hdvd
    omega
  have hne : ∏ j ∈ Finset.Icc 1 r, (2 ^ (2 * j) - 1) ≠ 0 := fun h => hodd (h ▸ dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hne, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]

theorem factorization_le_of_dvd_card_isometryGroup {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] (B : BilinForm (ZMod 2) W)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) {r : ℕ} (hr : finrank (ZMod 2) W = 2 * r) {a : ℕ}
    (ha : a ∣ Nat.card (isometryGroup B)) : a.factorization 2 ≤ r ^ 2 := by
  have hne : Nat.card (isometryGroup B) ≠ 0 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup r B hB hnd hr,
      Nat.card_zmod]
    refine mul_ne_zero (pow_ne_zero _ two_ne_zero) (Finset.prod_ne_zero_iff.2 fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    have : 2 ≤ 2 ^ (2 * j) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hne (Nat.eq_zero_of_zero_dvd ha)
  rw [← factorization_card_isometryGroup_of_isAlt B hB hnd hr]
  exact (Nat.factorization_le_iff_dvd ha0 hne).2 ha 2

private theorem zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

private theorem zmod_two_mul_self (a : ZMod 2) : a * a = a := by
  revert a
  decide

private theorem zmod_two_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  revert a
  decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def bilinDiag (β : BilinForm (ZMod 2) V) (hs : β.IsSymm) : V →ₗ[ZMod 2] ZMod 2 where
  toFun v := β v v
  map_add' v w := by
    simp only [map_add, LinearMap.add_apply, hs.eq w v]
    calc β v v + β v w + (β v w + β w w) = β v v + β w w + (β v w + β v w) := by ring
      _ = β v v + β w w := by rw [zmod_two_add_self, add_zero]
  map_smul' c v := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← mul_assoc, zmod_two_mul_self]

@[simp]
theorem bilinDiag_apply (β : BilinForm (ZMod 2) V) (hs : β.IsSymm) (v : V) :
    bilinDiag β hs v = β v v := rfl

theorem bilinDiag_apply_isometry {β : BilinForm (ZMod 2) V} (hs : β.IsSymm)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ isometryGroup β) (v : V) :
    bilinDiag β hs (g v) = bilinDiag β hs v := by
  rw [bilinDiag_apply, bilinDiag_apply, (mem_isometryGroup_iff.1 hg) v v]

variable {β : BilinForm (ZMod 2) V} (hs : β.IsSymm)
include hs

@[expose] def bilinDiagAlt (β : BilinForm (ZMod 2) V) (hs : β.IsSymm) : BilinForm (ZMod 2) V :=
  β + BilinForm.linMulLin (bilinDiag β hs) (bilinDiag β hs)

theorem bilinDiagAlt_apply (v w : V) : bilinDiagAlt β hs v w = β v w + β v v * β w w := by
  simp [bilinDiagAlt, BilinForm.linMulLin_apply]

theorem bilinDiagAlt_isAlt : (bilinDiagAlt β hs).IsAlt := fun v => by
  rw [bilinDiagAlt_apply, zmod_two_mul_self, zmod_two_add_self]

theorem bilinDiagAlt_comm (v w : V) : bilinDiagAlt β hs v w = bilinDiagAlt β hs w v := by
  rw [bilinDiagAlt_apply, bilinDiagAlt_apply, hs.eq v w, mul_comm]

theorem isometryGroup_le_bilinDiagAlt : isometryGroup β ≤ isometryGroup (bilinDiagAlt β hs) := by
  intro g hg
  rw [mem_isometryGroup_iff] at hg ⊢
  intro v w
  rw [bilinDiagAlt_apply, bilinDiagAlt_apply, hg, hg v v, hg w w]

theorem bilinDiagAlt_nondegenerate (hnd : β.Nondegenerate) {u : V} (hu : ∀ v, β u v = β v v)
    (huu : β u u = 0) : (bilinDiagAlt β hs).Nondegenerate := by
  have hleft : ∀ v, (∀ w, bilinDiagAlt β hs v w = 0) → v = 0 := by
    intro v hv
    have h1 : ∀ w, β (v + β v v • u) w = 0 := by
      intro w
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hu, smul_eq_mul,
        ← bilinDiagAlt_apply]
      exact hv w
    have h2 : v + β v v • u = 0 := hnd.1 _ h1
    have h3 : β v v = 0 := by
      have := congrArg (bilinDiag β hs) h2
      rwa [map_add, map_smul, map_zero, bilinDiag_apply, bilinDiag_apply, huu, smul_zero,
        add_zero] at this
    rwa [h3, zero_smul, add_zero] at h2
  exact ⟨hleft, fun w hw => hleft w fun v => by rw [bilinDiagAlt_comm]; exact hw v⟩

omit hs in
theorem isometry_apply_diag_vector (hnd : β.Nondegenerate) {u : V} (hu : ∀ v, β u v = β v v)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ isometryGroup β) : g u = u := by
  have hg' := mem_isometryGroup_iff.1 hg
  rw [← sub_eq_zero]
  refine hnd.1 _ fun x => ?_
  obtain ⟨y, rfl⟩ := g.surjective x
  rw [map_sub, LinearMap.sub_apply, hg', hu, hu, hg', sub_self]

variable [FiniteDimensional (ZMod 2) V]

theorem factorization_card_isometryGroup_le_of_apply_self_eq_one (hnd : β.Nondegenerate)
    {u : V} (hu : ∀ v, β u v = β v v) (huu : β u u = 1) :
    (Nat.card (isometryGroup β)).factorization 2 ≤ (finrank (ZMod 2) V / 2) ^ 2 := by
  set ℓ := bilinDiag β hs with hℓ
  set W₀ := LinearMap.ker ℓ with hW₀
  have hℓu : ℓ u = 1 := huu
  have hsurj : Function.Surjective ℓ := fun c => ⟨c • u, by rw [map_smul, hℓu, smul_eq_mul,
    mul_one]⟩
  have hdim : finrank (ZMod 2) W₀ + 1 = finrank (ZMod 2) V := by
    have h : finrank (ZMod 2) (LinearMap.range ℓ) + finrank (ZMod 2) W₀ = finrank (ZMod 2) V :=
      LinearMap.finrank_range_add_finrank_ker ℓ
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self] at h
    omega
  have hproj : ∀ v : V, v - ℓ v • u ∈ W₀ := fun v => by
    rw [LinearMap.mem_ker, map_sub, map_smul, hℓu, smul_eq_mul, mul_one, sub_self]
  have hW₀u : ∀ w ∈ W₀, β w u = 0 := fun w hw => by
    rw [hs.eq, hu]
    exact hw
  set β₀ := β.restrict W₀ with hβ₀
  have halt₀ : β₀.IsAlt := fun w => w.2
  have hleft : ∀ w : W₀, (∀ w' : W₀, β₀ w w' = 0) → w = 0 := by
    intro w hw
    apply Subtype.ext
    refine hnd.1 _ fun v => ?_
    have h1 : β w (v - ℓ v • u) = 0 := hw ⟨_, hproj v⟩
    rw [map_sub, map_smul, smul_eq_mul, hW₀u w w.2, mul_zero, sub_zero] at h1
    exact h1
  have hnd₀ : β₀.Nondegenerate := ⟨hleft, fun w hw => hleft w fun v => by
    have := hw v
    simp only [hβ₀, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at this ⊢
    rw [hs.eq]
    exact this⟩
  obtain ⟨r, hr⟩ := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.even_finrank β₀
    halt₀ hnd₀
  have hmaps : ∀ g ∈ isometryGroup β, ∀ w ∈ W₀, g w ∈ W₀ := fun g hg w hw => by
    rw [LinearMap.mem_ker, bilinDiag_apply_isometry hs hg]
    exact hw
  let res : isometryGroup β → (W₀ ≃ₗ[ZMod 2] W₀) := fun g =>
    LinearEquiv.ofInjectiveEndo ((g : V →ₗ[ZMod 2] V).restrict (hmaps g g.2))
      fun x y hxy => Subtype.ext ((g : V ≃ₗ[ZMod 2] V).injective (congrArg Subtype.val hxy))
  have hres : ∀ g w, ((res g w : W₀) : V) = (g : V ≃ₗ[ZMod 2] V) w := fun g w => rfl
  let ρ : isometryGroup β →* isometryGroup β₀ :=
    { toFun := fun g => ⟨res g, mem_isometryGroup_iff.2 fun x y => by
        simp only [hβ₀, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, hres]
        exact mem_isometryGroup_iff.1 g.2 x y⟩
      map_one' := by
        ext x
        rfl
      map_mul' := fun g h => by
        ext x
        rfl }
  have hρ : Function.Injective ρ := by
    intro g h hgh
    have hw : ∀ w : W₀, (g : V ≃ₗ[ZMod 2] V) w = (h : V ≃ₗ[ZMod 2] V) w := fun w => by
      rw [← hres, ← hres]
      exact congrArg (fun k : isometryGroup β₀ => (((k : W₀ ≃ₗ[ZMod 2] W₀) w : W₀) : V)) hgh
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv : v = (v - ℓ v • u) + ℓ v • u := by rw [sub_add_cancel]
    rw [hv, map_add, map_add, map_smul, map_smul, isometry_apply_diag_vector hnd hu g.2,
      isometry_apply_diag_vector hnd hu h.2]
    congr 1
    exact hw ⟨_, hproj v⟩
  have hdvd := Subgroup.card_dvd_of_injective ρ hρ
  have := factorization_le_of_dvd_card_isometryGroup β₀ halt₀ hnd₀ (r := r) (by omega) hdvd
  rwa [show finrank (ZMod 2) V / 2 = r by omega]

theorem factorization_card_isometryGroup_le (hnd : β.Nondegenerate) :
    (Nat.card (isometryGroup β)).factorization 2 ≤ (finrank (ZMod 2) V / 2) ^ 2 := by
  set u := (β.toDual hnd).symm (bilinDiag β hs)
  have hu : ∀ v, β u v = β v v := fun v => LinearMap.BilinForm.apply_toDual_symm_apply _ v
  rcases eq_or_ne (β u u) 0 with huu | huu
  · have halt' := bilinDiagAlt_isAlt hs
    have hnd' := bilinDiagAlt_nondegenerate hs hnd hu huu
    obtain ⟨r, hr⟩ := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.even_finrank
      (bilinDiagAlt β hs) halt' hnd'
    have hdvd := Subgroup.card_dvd_of_le (isometryGroup_le_bilinDiagAlt hs)
    have := factorization_le_of_dvd_card_isometryGroup (bilinDiagAlt β hs) halt' hnd' (r := r)
      (by omega) hdvd
    rwa [show finrank (ZMod 2) V / 2 = r by omega]
  · exact factorization_card_isometryGroup_le_of_apply_self_eq_one hs hnd hu
      (zmod_two_eq_one_of_ne_zero huu)

theorem card_le_of_isPGroup (hnd : β.Nondegenerate) {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hP : IsPGroup 2 P) (hPβ : P ≤ isometryGroup β) :
    Nat.card P ≤ 2 ^ ((finrank (ZMod 2) V / 2) ^ 2) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V)) DFunLike.coe_injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  have hne : Nat.card (isometryGroup β) ≠ 0 := Nat.card_pos.ne'
  have hdvd : 2 ^ a ∣ Nat.card (isometryGroup β) := ha ▸ Subgroup.card_dvd_of_le hPβ
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 hdvd
  rw [ha]
  exact Nat.pow_le_pow_right (by norm_num) (hle.trans (factorization_card_isometryGroup_le hs hnd))

end CFSG.LargeExtraspecial.GLR
