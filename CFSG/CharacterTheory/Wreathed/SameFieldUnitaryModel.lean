module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.BaseBorel

public section

open scoped Classical

namespace CFSG.Wreathed.SameFieldUnitary

open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

section Squares

variable {F : Type} [Field F]

theorem units_isSquare_iff (x : Fˣ) : IsSquare x ↔ IsSquare (x : F) := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by push_cast; rfl⟩
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by rw [hr, mul_zero])
    exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr)⟩

theorem quadraticChar_units [Fintype F] (x : Fˣ) :
    quadraticChar F (x : F) = if IsSquare x then 1 else -1 := by
  split_ifs with h
  · exact (quadraticChar_one_iff_isSquare x.ne_zero).mpr ((units_isSquare_iff x).mp h)
  · exact quadraticChar_neg_one_iff_not_isSquare.mpr (fun h' => h ((units_isSquare_iff x).mpr h'))

theorem isSquare_mul_of_not_isSquare [Finite F] {x y : Fˣ} (hx : ¬ IsSquare x)
    (hy : ¬ IsSquare y) : IsSquare (x * y) := by
  have : Fintype F := Fintype.ofFinite F
  have h := quadraticChar_units (x * y)
  rw [Units.val_mul, map_mul, quadraticChar_units, quadraticChar_units] at h
  by_contra hxy
  simp [hx, hy, hxy] at h

theorem not_isSquare_mul_of_isSquare [Finite F] {x y : Fˣ} (hx : ¬ IsSquare x)
    (hy : IsSquare y) : ¬ IsSquare (x * y) := by
  have : Fintype F := Fintype.ofFinite F
  intro hxy
  have h := quadraticChar_units (x * y)
  rw [Units.val_mul, map_mul, quadraticChar_units, quadraticChar_units] at h
  simp [hx, hy, hxy] at h

theorem isSquare_pow_of_isSquare {x : Fˣ} (hx : IsSquare x) (k : ℕ) : IsSquare (x ^ k) := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨r ^ k, by rw [← mul_pow]⟩

theorem not_isSquare_neg_one_units [Finite F] (hq : Nat.card F % 4 = 3) :
    ¬ IsSquare (-1 : Fˣ) := by
  have : Fintype F := Fintype.ofFinite F
  rw [units_isSquare_iff, Units.val_neg, Units.val_one, FiniteField.isSquare_neg_one_iff,
    ← Nat.card_eq_fintype_card]
  omega

theorem exists_pow_two_pow_eq_of_isSquare [Finite F] (hq : Nat.card F % 4 = 3) (n : ℕ)
    {y : Fˣ} (hy : IsSquare y) : ∃ c : Fˣ, c ^ 2 ^ n = y := by
  obtain ⟨w, rfl⟩ := hy
  have hcard : Nat.card Fˣ = Nat.card F - 1 := by
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card, Fintype.card_units, Nat.card_eq_fintype_card]
  have hodd : Odd ((Nat.card F - 1) / 2) := by
    refine ⟨(Nat.card F - 3) / 4, ?_⟩
    omega
  have hpow : (w * w) ^ ((Nat.card F - 1) / 2) = 1 := by
    rw [← sq, ← pow_mul, show 2 * ((Nat.card F - 1) / 2) = Nat.card F - 1 by omega, ← hcard,
      pow_card_eq_one']
  have hord : Odd (orderOf (w * w)) := hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  have hcop : Nat.Coprime (2 ^ n) (orderOf (w * w)) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hord)
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  exact ⟨(w * w) ^ t, by rw [← pow_mul, Nat.mul_comm t, pow_mul]; exact ht⟩

end Squares

section Torus

variable {F : Type} [Field F] [Finite F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

theorem torusConstant_not_isSquare (hq : Nat.card F % 4 = 3) (hb : ¬ IsSquare b) :
    ¬ IsSquare (torusConstant F b m) := by
  have hneg := not_isSquare_neg_one_units (F := F) hq
  have hbinv : ¬ IsSquare b⁻¹ := fun h => hb (isSquare_inv.mp h)
  have h1 : IsSquare (-b⁻¹) := by
    rw [← neg_one_mul]
    exact isSquare_mul_of_not_isSquare hneg hbinv
  rw [torusConstant, ← neg_one_mul]
  exact not_isSquare_mul_of_isSquare hneg (isSquare_pow_of_isSquare h1 _)

omit [Finite F] in
theorem torusDiag_zpow (c : Fˣ) (k : ℤ) :
    torusDiag F b m hm heven (c ^ k) = torusDiag F b m hm heven c ^ k :=
  map_zpow ((specialInclusion F b m hm heven).comp (diagHom F)) c k

theorem exists_splitTorus_eq_zpowers (hq : Nat.card F % 4 = 3) (hb : ¬ IsSquare b) {n : ℕ}
    (hmn : m = 2 ^ n) :
    ∃ g, splitTorus F b m hm heven = Subgroup.zpowers g := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hγsq : ¬ IsSquare γ := by
    intro h
    apply not_isSquare_neg_one_units (F := F) hq
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ (-1))
    rw [← hk]
    obtain ⟨r, rfl⟩ := h
    exact ⟨r ^ k, by rw [← mul_zpow]⟩
  have hc0 := torusConstant_not_isSquare (m := m) hq hb
  obtain ⟨c, hc⟩ := exists_pow_two_pow_eq_of_isSquare hq n
    (isSquare_mul_of_not_isSquare hγsq (fun h => hc0 (isSquare_inv.mp h)))
  set g := torusDiag F b m hm heven c * torusGenerator F b m hm heven with hg
  have hcomm : Commute (torusDiag F b m hm heven c) (torusGenerator F b m hm heven) :=
    (torusGenerator_mul_torusDiag F b m hm heven c).symm
  have hc' : c ^ m = γ * (torusConstant F b m)⁻¹ := by rw [← hc, hmn]
  have hgm : g ^ m = torusDiag F b m hm heven γ := by
    rw [hg, hcomm.mul_pow, ← torusDiag_pow, torusGenerator_pow_m, ← torusDiag_mul, hc',
      inv_mul_cancel_right]
  have hdiag : ∀ d : Fˣ, torusDiag F b m hm heven d ∈ Subgroup.zpowers g := by
    intro d
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hγ d)
    rw [torusDiag_zpow, ← hgm]
    exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _) _
  refine ⟨g, le_antisymm ?_ ?_⟩
  · rw [splitTorus_eq_closure, Subgroup.closure_le]
    rintro _ (⟨d, rfl⟩ | h)
    · exact hdiag d
    · rw [Set.mem_singleton_iff] at h
      rw [h, show torusGenerator F b m hm heven = (torusDiag F b m hm heven c)⁻¹ * g by
        rw [hg, inv_mul_cancel_left]]
      exact (Subgroup.zpowers g).mul_mem ((Subgroup.zpowers g).inv_mem (hdiag c))
        (Subgroup.mem_zpowers g)
  · rw [Subgroup.zpowers_le]
    exact (splitTorus F b m hm heven).mul_mem (torusDiag_mem_splitTorus F b m hm heven c)
      (torusGenerator_mem_splitTorus F b m hm heven)

theorem splitTorus_isCyclic (hq : Nat.card F % 4 = 3) (hb : ¬ IsSquare b) {n : ℕ}
    (hmn : m = 2 ^ n) : IsCyclic (splitTorus F b m hm heven) := by
  obtain ⟨g, hg⟩ := exists_splitTorus_eq_zpowers (hm := hm) (heven := heven) hq hb hmn
  rw [hg]
  infer_instance

end Torus

section Root

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

theorem unipotentElement_injective :
    Function.Injective (unipotentElement F b m hm heven) := by
  intro s t h
  have h0 := congrArg (fun g : CentralExtension F b m hm heven => g • (some 0 : Omega F)) h
  simp only [unipotentElement_smul_some, zero_add] at h0
  exact Option.some.inj h0

theorem card_unipotentSubgroup [Finite F] :
    Nat.card (unipotentSubgroup F b m hm heven) = Nat.card F := by
  have hinj : Function.Injective ((specialInclusion F b m hm heven).comp (upperHom F)) := by
    intro s t h
    exact Multiplicative.toAdd.injective (unipotentElement_injective h)
  rw [unipotentSubgroup, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

theorem unipotentSubgroup_comm {g g' : CentralExtension F b m hm heven}
    (hg : g ∈ unipotentSubgroup F b m hm heven) (hg' : g' ∈ unipotentSubgroup F b m hm heven) :
    g * g' = g' * g := by
  obtain ⟨s, rfl⟩ := (mem_unipotentSubgroup_iff F b m hm heven g).mp hg
  obtain ⟨t, rfl⟩ := (mem_unipotentSubgroup_iff F b m hm heven g').mp hg'
  rw [← unipotentElement_add, ← unipotentElement_add, add_comm]

theorem splitTorus_le_normalizer_unipotentSubgroup :
    splitTorus F b m hm heven ≤ Subgroup.normalizer
      (unipotentSubgroup F b m hm heven : Set (CentralExtension F b m hm heven)) := by
  have hconj : ∀ g ∈ splitTorus F b m hm heven, ∀ u ∈ unipotentSubgroup F b m hm heven,
      g * u * g⁻¹ ∈ unipotentSubgroup F b m hm heven := by
    intro g hg u hu
    obtain ⟨t, rfl⟩ := (mem_unipotentSubgroup_iff F b m hm heven u).mp hu
    obtain ⟨s, hs⟩ := splitTorus_conj_unipotent F b m hm heven g hg t
    rw [hs]
    exact (mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨s, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => hconj g hg u hu, fun hu => ?_⟩
  have h := hconj g⁻¹ ((splitTorus F b m hm heven).inv_mem hg) _ hu
  simpa [mul_assoc] using h

end Root

end CFSG.Wreathed.SameFieldUnitary
