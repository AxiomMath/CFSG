module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeFaithful
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.LieType.Ree.LargeReeTorusRootForms

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeCover
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace LargeReeCatalog

section Field

variable {K : Type} [Field K] {a : ℕ}

theorem entrywise_largeReeA1X (β : K ≃+* K) (c : K) :
    Units.map (entrywiseHom β.toRingHom) (largeReeA1X a c) = largeReeA1X a (β c) := by
  rw [largeReeA1X, largeReeA1X, map_mul, units_map_entrywiseHom_xUnit,
    units_map_entrywiseHom_xUnit]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_pow]

theorem entrywise_largeReeA1H (β : K ≃+* K) (t : Kˣ) :
    Units.map (entrywiseHom β.toRingHom) (largeReeA1H a t) =
      largeReeA1H a (Units.map β.toMonoidHom t) := by
  rw [largeReeA1H, largeReeA1H, map_mul, entrywise_torusElt, entrywise_torusElt, map_pow]

theorem entrywise_largeReeX (β : K →+* K) (i : Fin 4) (c : K) :
    Units.map (entrywiseHom β) (largeReeX K i c) = largeReeX K i (β c) :=
  Units.ext (entrywise_pinnedX β (largeReeRoot i) c)

theorem entrywise_largeReeCoord (β : K →+* K) (s v : K) :
    Units.map (entrywiseHom β) (largeReeCoord a K s v) = largeReeCoord a K (β s) (β v) := by
  simp only [largeReeCoord, largeReeP, map_mul, entrywise_largeReeX, largeReeSigma, map_add,
    map_pow]

end Field

section Torus

variable {K : Type} [Field K] {a : ℕ}

theorem torusExp_values (θ : ℤ) :
    torusExp0 θ (Pi.single largeReeI1 1) = 2 ∧ torusExp1 θ (Pi.single largeReeI1 1) = -1 ∧
      torusExp0 θ (Pi.single largeReeI4 1) = 2 * θ ∧
      torusExp1 θ (Pi.single largeReeI4 1) = -θ ∧
      torusExp0 θ (largeReeRoot 0) = -θ ∧ torusExp1 θ (largeReeRoot 0) = 2 * θ - 1 := by
  have h : F4.cartanPair (f4i 0) (Pi.single largeReeI1 1) = 2 ∧
      F4.cartanPair (f4i 3) (Pi.single largeReeI1 1) = 0 ∧
      F4.cartanPair (f4i 1) (Pi.single largeReeI1 1) = -1 ∧
      F4.cartanPair (f4i 2) (Pi.single largeReeI1 1) = 0 ∧
      F4.cartanPair (f4i 0) (Pi.single largeReeI4 1) = 0 ∧
      F4.cartanPair (f4i 3) (Pi.single largeReeI4 1) = 2 ∧
      F4.cartanPair (f4i 1) (Pi.single largeReeI4 1) = 0 ∧
      F4.cartanPair (f4i 2) (Pi.single largeReeI4 1) = -1 ∧
      F4.cartanPair (f4i 0) (largeReeRoot 0) = 0 ∧ F4.cartanPair (f4i 3) (largeReeRoot 0) = -1 ∧
      F4.cartanPair (f4i 1) (largeReeRoot 0) = -1 ∧ F4.cartanPair (f4i 2) (largeReeRoot 0) = 2 := by
    decide
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := h
  simp only [torusExp0, torusExp1, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]
  exact ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩

theorem torusPair_conj_largeReeA1X (t u : Kˣ) (c : K) :
    torusPair a (t, u) * largeReeA1X a c * (torusPair a (t, u))⁻¹ =
      largeReeA1X a (((t ^ 2 * u⁻¹ : Kˣ) : K) * c) := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := torusExp_values (2 ^ a : ℤ)
  have e : ∀ A X Y : ModGL F4.tag K, A * (X * Y) * A⁻¹ = (A * X * A⁻¹) * (A * Y * A⁻¹) :=
    fun A X Y => by group
  rw [largeReeA1X, largeReeA1X, e, ← pinnedX_single, ← pinnedX_single,
    torusPair_conj_pinnedX _ _ (isRoot_single _ _), torusPair_conj_pinnedX _ _ (isRoot_single _ _),
    pinnedX_single, pinnedX_single, torusWeight_apply, torusWeight_apply, e1, e2, e3, e4]
  congr 2
  · simp [zpow_neg, zpow_ofNat]
  · have hθ : ((2 : ℤ) * 2 ^ a) = ((2 * 2 ^ a : ℕ) : ℤ) := by push_cast; ring
    have hθ' : (-(2 : ℤ) ^ a) = -((2 ^ a : ℕ) : ℤ) := by push_cast; ring
    rw [hθ, hθ', zpow_neg, zpow_natCast, zpow_natCast]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, mul_pow,
      inv_pow]
    ring

theorem torusWeight_largeReeRoot_zero (t u : Kˣ) :
    torusWeight a (largeReeRoot 0) (t, u) = t ^ (-(2 ^ a : ℤ)) * u ^ (2 * 2 ^ a - 1 : ℤ) := by
  obtain ⟨-, -, -, -, e5, e6⟩ := torusExp_values (2 ^ a : ℤ)
  change t ^ torusExp0 (2 ^ a) (largeReeRoot 0) * u ^ torusExp1 (2 ^ a) (largeReeRoot 0) = _
  rw [e5, e6]

theorem commute_torusPair_largeReeA1H (t u t' : Kˣ) :
    Commute (torusPair a (t, u)) (largeReeA1H a t') := by
  rw [torusPair_apply, largeReeA1H]
  have hc : ∀ (i : Fin F4.tag.rank) (x : Kˣ), Commute (torusElt F4.tag K i x)
      (torusElt F4.tag K largeReeI1 t' * torusElt F4.tag K largeReeI4 (t' ^ 2 ^ a)) :=
    fun i x => (torusElt_commute i largeReeI1 x t').mul_right
      (torusElt_commute i largeReeI4 x (t' ^ 2 ^ a))
  exact ((hc _ _).mul_left (hc _ _)).mul_left ((hc _ _).mul_left (hc _ _))

theorem torusPair_mem_torusGroup (t u : Kˣ) : torusPair a (t, u) ∈ torusGroup F4.tag K := by
  rw [torusPair_apply]
  exact mul_mem (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
    (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))

variable [Finite K] [CharP K F4.prime]

theorem torusPair_conj_largeReeCoord (hK : Nat.card K = 2 ^ (2 * a + 1)) (t u : Kˣ) (s v : K) :
    ∃ w : K, ((MulAut.conj (⟨torusPair a (t, u), torusPair_mem_reeGamma a hK (t, u)⟩ :
      F4.reeGamma K a) ⟨largeReeCoord a K s v, largeReeCoord_mem_reeGamma hK s v⟩ :
        F4.reeGamma K a) : ModGL F4.tag K) =
      largeReeCoord a K (((t ^ (-(2 ^ a : ℤ)) * u ^ (2 * 2 ^ a - 1 : ℤ) : Kˣ) : K) * s) w := by
  set g : F4.reeGamma K a := ⟨torusPair a (t, u), torusPair_mem_reeGamma a hK (t, u)⟩ with hgdef
  set x : F4.reeGamma K a := ⟨largeReeCoord a K s v, largeReeCoord_mem_reeGamma hK s v⟩ with hx
  have hP := conj_largeReeP (g := torusPair a (t, u))
    (fun i => (torusWeight a (largeReeRoot i) (t, u) : K))
    (fun i x => torusPair_conj_pinnedX a (t, u) (largeReeRoot_pos i).1 x) s (largeReeSigma a s) v
    (largeReeSigma a v + s ^ 2 * largeReeSigma a s)
  have hP' : ((MulAut.conj g x : F4.reeGamma K a) : ModGL F4.tag K) =
      largeReeP K ((torusWeight a (largeReeRoot 0) (t, u) : K) * s)
        ((torusWeight a (largeReeRoot 1) (t, u) : K) * largeReeSigma a s)
        ((torusWeight a (largeReeRoot 2) (t, u) : K) * v)
        ((torusWeight a (largeReeRoot 3) (t, u) : K) *
          (largeReeSigma a v + s ^ 2 * largeReeSigma a s)) := hP
  have hmem : ((MulAut.conj g x : F4.reeGamma K a) : ModGL F4.tag K) ∈
      F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ := by
    refine Subgroup.mem_inf.2 ⟨?_, (MulAut.conj g x).2⟩
    rw [F4_fixedOrbitRoots_one, hP']
    exact largeReeP_mem_rootSpan _ _ _ _
  obtain ⟨s', w, hsw⟩ := exists_largeReeCoord_eq hK hmem
  refine ⟨w, ?_⟩
  rw [← hsw]
  have h1 := (largeReeP_injective (hsw.trans hP')).1
  rw [h1, torusWeight_largeReeRoot_zero]

end Torus

section Params

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem isLargeReeParam_conj_torusPair (hK : Nat.card K = 2 ^ (2 * a + 1)) (t u : Kˣ) :
    IsLargeReeParam a hK (MulAut.conj (⟨torusPair a (t, u), torusPair_mem_reeGamma a hK (t, u)⟩ :
      F4.reeGamma K a)) (t ^ 2 * u⁻¹, t ^ (-(2 ^ a : ℤ)) * u ^ (2 * 2 ^ a - 1 : ℤ), 1) := by
  refine ⟨fun c => ?_, fun t' => ?_, fun s v => ?_⟩
  · exact torusPair_conj_largeReeA1X t u c
  · change torusPair a (t, u) * largeReeA1H a t' * (torusPair a (t, u))⁻¹ = largeReeA1H a t'
    rw [(commute_torusPair_largeReeA1H t u t').eq, mul_inv_cancel_right]
  · exact torusPair_conj_largeReeCoord hK t u s v

theorem isLargeReeParam_reeGammaFieldAut (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) :
    IsLargeReeParam a hK (F4.reeGammaFieldAut K a β) (1, 1, β) := by
  refine ⟨fun c => ?_, fun t => ?_, fun s v => ⟨β v, ?_⟩⟩
  · rw [coe_reeGammaFieldAut]
    change Units.map (entrywiseHom β.toRingHom) (largeReeA1X a c) = largeReeA1X a (1 * β c)
    rw [entrywise_largeReeA1X, one_mul]
  · rw [coe_reeGammaFieldAut]
    exact entrywise_largeReeA1H β t
  · rw [coe_reeGammaFieldAut]
    change Units.map (entrywiseHom β.toRingHom) (largeReeCoord a K s v) =
      largeReeCoord a K (1 * β s) (β v)
    rw [entrywise_largeReeCoord, one_mul]
    rfl

theorem map_reeFixedNegUnipotent_exactEntrywiseAut {t : ReeTag} {K : Type} [Field K] [Finite K]
    [CharP K t.prime] {a : ℕ} (β : K ≃+* K) :
    (t.reeFixedNegUnipotent K a).map (exactEntrywiseAut t.tag β).toMonoidHom =
      t.reeFixedNegUnipotent K a := by
  rw [reeFixedNegUnipotent, Subgroup.map_inf _ _ (exactEntrywiseAut t.tag β).toMonoidHom
    (exactEntrywiseAut t.tag β).injective, map_exactEntrywiseAut β (Or.inr (Or.inr rfl)),
    map_reeGamma_exactEntrywiseAut]

theorem reeGammaFieldAut_mem_largeReeOppAut (β : K ≃+* K) :
    F4.reeGammaFieldAut K a β ∈ largeReeOppAut K a :=
  ⟨map_subgroupOf_mulAutRestrict (map_reeGamma_exactEntrywiseAut β)
      (map_reeFixedPosUnipotent_exactEntrywiseAut β),
    map_subgroupOf_mulAutRestrict (map_reeGamma_exactEntrywiseAut β)
      (map_reeFixedNegUnipotent_exactEntrywiseAut β)⟩

theorem conj_mem_largeReeOppAut_iff {w₀ : WeylGroup F4.tag}
    (hw₀ : ∀ w, (coxeterSystem F4.tag).length w ≤ (coxeterSystem F4.tag).length w₀)
    (y : F4.reeGamma K a) :
    MulAut.conj y ∈ largeReeOppAut K a ↔ (y : ModGL F4.tag K) ∈ F4.reeFixedTorus K a := by
  have hB : F4.reeFixedBorel K a ⊓ (F4.reeFixedTorus K a ⊔ F4.reeFixedNegUnipotent K a) =
      F4.reeFixedTorus K a := by
    rw [← map_conj_reeFixedBorel hw₀, reeFixedBorel_inf_map_conj hw₀]
  have key : MulAut.conj y ∈ largeReeOppAut K a ↔
      y ∈ Subgroup.normalizer (((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) :
        Subgroup (F4.reeGamma K a)) : Set (F4.reeGamma K a)) ∧
      y ∈ Subgroup.normalizer (((F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a) :
        Subgroup (F4.reeGamma K a)) : Set (F4.reeGamma K a)) :=
    ⟨fun h => ⟨Subgroup.mem_normalizer_iff_map_conj_eq.2 h.1,
      Subgroup.mem_normalizer_iff_map_conj_eq.2 h.2⟩,
     fun h => ⟨Subgroup.mem_normalizer_iff_map_conj_eq.1 h.1,
      Subgroup.mem_normalizer_iff_map_conj_eq.1 h.2⟩⟩
  rw [key, normalizer_reeFixedPosUnipotent_subgroupOf,
    normalizer_reeFixedNegUnipotent_subgroupOf hw₀, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf, ← Subgroup.mem_inf, hB]

theorem ringEquiv_eq_one_of_mem_reeFixedTorus (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y : F4.reeGamma K a} (hy : (y : ModGL F4.tag K) ∈ F4.reeFixedTorus K a)
    {p : Kˣ × Kˣ × (K ≃+* K)} (hp : IsLargeReeParam a hK (MulAut.conj y) p) : p.2.2 = 1 := by
  obtain ⟨l, hl⟩ := exists_torus_characters (Subgroup.mem_inf.1 hy).1
  have e : ∀ A X Y : ModGL F4.tag K, A * (X * Y) * A⁻¹ = (A * X * A⁻¹) * (A * Y * A⁻¹) :=
    fun A X Y => by group
  have hx : ∀ c : K, (((∏ j, l j ^ (Pi.single largeReeI1 1 : Fin F4.tag.rank → ℤ) j : Kˣ) :
      K) * c) = p.1 * p.2.2 c := fun c => by
    have h1 := hp.1 c
    change (y : ModGL F4.tag K) * largeReeA1X a c * (y : ModGL F4.tag K)⁻¹ =
      largeReeA1X a (p.1 * p.2.2 c) at h1
    rw [largeReeA1X, largeReeA1X, e, ← pinnedX_single, ← pinnedX_single,
      (hl _ (isRoot_single _ _)).2, (hl _ (isRoot_single _ _)).2, pinnedX_single,
      pinnedX_single] at h1
    exact (largeRee_x_inj h1).1
  have h1 := hx 1
  rw [mul_one, map_one, mul_one] at h1
  refine RingEquiv.ext fun c => ?_
  have h2 := hx c
  rw [h1] at h2
  exact (mul_left_cancel₀ p.1.ne_zero h2).symm

variable (a) in
@[expose] def largeReeScalarHom : Kˣ × Kˣ →* Kˣ × Kˣ where
  toFun p := (p.1 ^ 2 * p.2⁻¹, p.1 ^ (-(2 ^ a : ℤ)) * p.2 ^ (2 * 2 ^ a - 1 : ℤ))
  map_one' := by simp
  map_mul' p q := Prod.ext (by
      simp only [Prod.fst_mul, Prod.snd_mul, mul_pow, mul_inv]
      exact mul_mul_mul_comm _ _ _ _)
    (by
      simp only [Prod.fst_mul, Prod.snd_mul, mul_zpow]
      exact mul_mul_mul_comm _ _ _ _)

omit [CharP K F4.prime] in
theorem largeReeScalarHom_bijective (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Bijective (largeReeScalarHom (K := K) a) := by
  refine Function.Injective.bijective_of_finite ?_
  rw [injective_iff_map_eq_one]
  rintro ⟨t, u⟩ h
  have h1 : t ^ 2 * u⁻¹ = 1 := congrArg Prod.fst h
  have h2 : t ^ (-(2 ^ a : ℤ)) * u ^ (2 * 2 ^ a - 1 : ℤ) = 1 := congrArg Prod.snd h
  have hu : u = t ^ 2 := (mul_inv_eq_one.1 h1).symm
  rw [hu, ← zpow_natCast, ← zpow_mul, ← zpow_add] at h2
  have h3 : t ^ (3 * (2 ^ a : ℤ) - 2) = 1 := by
    rw [← h2]
    congr 1
    push_cast
    ring
  have hN : t ^ (2 * (2 ^ a : ℤ) ^ 2 - 1) = 1 := by
    have h4 : t ^ Nat.card Kˣ = 1 := pow_card_eq_one'
    rw [Nat.card_units, hK] at h4
    have e : (2 * (2 ^ a : ℤ) ^ 2 - 1) = ((2 ^ (2 * a + 1) - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
        two_pow_two_mul_add_one, add_sub_cancel_right]
    rw [e, zpow_natCast]
    exact h4
  have ht : t = 1 := by
    have e : (1 : ℤ) = (3 * (2 ^ a : ℤ) - 2) * (2 * (3 * 2 ^ a + 2)) +
        (2 * (2 ^ a : ℤ) ^ 2 - 1) * (-9) := by ring
    rw [← zpow_one t, e, zpow_add, zpow_mul t (3 * (2 ^ a : ℤ) - 2),
      zpow_mul t (2 * (2 ^ a : ℤ) ^ 2 - 1), h3, hN, one_zpow, one_zpow, one_mul]
  rw [ht, hu, ht, one_pow]
  rfl

end Params

section NormalForm

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem eq_one_of_conj_eq_one (hK : Nat.card K = 2 ^ (2 * a + 1)) {y : F4.reeGamma K a}
    (h : MulAut.conj y = 1) : y = 1 := by
  have hy : y ∈ Subgroup.center (F4.reeGamma K a) := Subgroup.mem_center_iff.2 fun g => by
    have := congrArg (fun α : MulAut (F4.reeGamma K a) => α g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * y = y * g * y⁻¹ * y := by rw [this]
      _ = y * g := by group
  rw [large_Ree_fixed_group_center_trivial a K hK] at hy
  exact hy

theorem exists_conj_mul_reeGammaFieldAut_of_mem (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {α : MulAut (F4.reeGamma K a)} (hα : α ∈ largeReeOppAut K a) :
    ∃ (h : F4.reeGamma K a) (β : K ≃+* K), (h : ModGL F4.tag K) ∈ F4.reeFixedTorus K a ∧
      α = MulAut.conj h * F4.reeGammaFieldAut K a β := by
  obtain ⟨Φ, hΦ, hΦinj, -, -⟩ := large_Ree_opposite_Sylow_parameters_faithful a ha K hK
  obtain ⟨p, hp⟩ := exists_isLargeReeParam ha hK ⟨α, hα⟩
  obtain ⟨⟨t, u⟩, htu⟩ := (largeReeScalarHom_bijective (K := K) hK).2 (p.1, p.2.1)
  have htu1 : t ^ 2 * u⁻¹ = p.1 := congrArg Prod.fst htu
  have htu2 : t ^ (-(2 ^ a : ℤ)) * u ^ (2 * 2 ^ a - 1 : ℤ) = p.2.1 := congrArg Prod.snd htu
  set h : F4.reeGamma K a := ⟨torusPair a (t, u), torusPair_mem_reeGamma a hK (t, u)⟩ with hh
  have hhT : (h : ModGL F4.tag K) ∈ F4.reeFixedTorus K a :=
    Subgroup.mem_inf.2 ⟨torusPair_mem_torusGroup t u, h.2⟩
  have hmem : MulAut.conj h * F4.reeGammaFieldAut K a p.2.2 ∈ largeReeOppAut K a :=
    mul_mem ((conj_mem_largeReeOppAut_iff (weyl_longest_element F4.tag).choose_spec.1 h).2 hhT)
      (reeGammaFieldAut_mem_largeReeOppAut p.2.2)
  have hq := (isLargeReeParam_conj_torusPair hK t u).mul (isLargeReeParam_reeGammaFieldAut hK p.2.2)
  have e : ((t ^ 2 * u⁻¹ : Kˣ) * Units.map (1 : K ≃+* K).toMonoidHom 1,
      (t ^ (-(2 ^ a : ℤ)) * u ^ (2 * 2 ^ a - 1 : ℤ) : Kˣ) * Units.map (1 : K ≃+* K).toMonoidHom 1,
      (1 : K ≃+* K) * p.2.2) = p := by
    rw [map_one, mul_one, mul_one, one_mul, htu1, htu2]
  rw [e] at hq
  refine ⟨h, p.2.2, hhT, ?_⟩
  have h1 := hΦ ⟨α, hα⟩ p (fun c _ => hp.1 c) (fun t' _ => hp.2.1 t') (fun s v _ => hp.2.2 s v)
  have h2 := hΦ ⟨_, hmem⟩ p (fun c _ => hq.1 c) (fun t' _ => hq.2.1 t') (fun s v _ => hq.2.2 s v)
  exact congrArg Subtype.val (hΦinj (h1.trans h2.symm))

theorem eq_of_conj_mul_reeGammaFieldAut_eq (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {h h' : F4.reeGamma K a} (hh : (h : ModGL F4.tag K) ∈ F4.reeFixedTorus K a)
    (hh' : (h' : ModGL F4.tag K) ∈ F4.reeFixedTorus K a) {β β' : K ≃+* K}
    (e : MulAut.conj h * F4.reeGammaFieldAut K a β = MulAut.conj h' * F4.reeGammaFieldAut K a β') :
    h = h' ∧ β = β' := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
  have hfield : ∀ {y : F4.reeGamma K a}, (y : ModGL F4.tag K) ∈ F4.reeFixedTorus K a →
      ∀ γ : K ≃+* K, ∃ p : Kˣ × Kˣ × (K ≃+* K), p.2.2 = γ ∧
        IsLargeReeParam a hK (MulAut.conj y * F4.reeGammaFieldAut K a γ) p := by
    intro y hy γ
    obtain ⟨q, hq⟩ := exists_isLargeReeParam ha hK
      ⟨MulAut.conj y, (conj_mem_largeReeOppAut_iff hw₀ y).2 hy⟩
    have hq1 := ringEquiv_eq_one_of_mem_reeFixedTorus hK hy hq
    refine ⟨_, ?_, hq.mul (isLargeReeParam_reeGammaFieldAut hK γ)⟩
    change q.2.2 * γ = γ
    rw [hq1, one_mul]
  obtain ⟨p, hp1, hp⟩ := hfield hh β
  obtain ⟨p', hp1', hp'⟩ := hfield hh' β'
  rw [e] at hp
  have hββ : β = β' := by rw [← hp1, ← hp1', hp.unique hp']
  subst hββ
  refine ⟨?_, rfl⟩
  have h1 := mul_right_cancel e
  have h2 : MulAut.conj (h'⁻¹ * h) = 1 := by rw [map_mul, h1, map_inv, inv_mul_cancel]
  exact (inv_mul_eq_one.1 (eq_one_of_conj_eq_one hK h2)).symm

end NormalForm

end LargeReeCatalog

open LargeReeCatalog

theorem large_Ree_full_inner_field_automorphism_normal_form (a : ℕ) (ha : 1 ≤ a) (K : Type)
    [Field K] [Finite K] [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ β : K ≃+* K, (∀ g : F4.reeGamma K a,
        ((F4.reeGammaFieldAut K a β g : F4.reeGamma K a) : ModGL F4.tag K) =
          Units.map (entrywiseHom β.toRingHom) (g : ModGL F4.tag K)) ∧
      F4.reeGammaFieldAut K a β ∈ largeReeOppAut K a) ∧
    (∀ α : MulAut (F4.reeGamma K a), ∃! p : F4.reeGamma K a × (K ≃+* K),
      α = MulAut.conj p.1 * F4.reeGammaFieldAut K a p.2) ∧
    (∃ Ψ : F4.reeGamma K a ⋊[F4.reeGammaFieldAutHom K a] (K ≃+* K) ≃* MulAut (F4.reeGamma K a),
      ∀ (x : F4.reeGamma K a) (β : K ≃+* K),
        Ψ ⟨x, β⟩ = MulAut.conj x * F4.reeGammaFieldAut K a β) ∧
    IsCyclic (Outer (F4.reeGamma K a)) ∧ Nat.card (Outer (F4.reeGamma K a)) = 2 * a + 1 ∧
    (∀ α : MulAut (F4.reeGamma K a), α ∈ largeReeOppAut K a ↔
      ∃ (h : F4.reeGamma K a) (β : K ≃+* K), (h : ModGL F4.tag K) ∈ F4.reeFixedTorus K a ∧
        α = MulAut.conj h * F4.reeGammaFieldAut K a β) ∧
    (∀ α ∈ largeReeOppAut K a, ∃! p : F4.reeGamma K a × (K ≃+* K),
      (p.1 : ModGL F4.tag K) ∈ F4.reeFixedTorus K a ∧
        α = MulAut.conj p.1 * F4.reeGammaFieldAut K a p.2) ∧
    (∀ t u : Kˣ, ∃ htu : torusPair a (t, u) ∈ F4.reeGamma K a,
      torusPair a (t, u) ∈ F4.reeFixedTorus K a ∧
        IsLargeReeParam a hK (MulAut.conj (⟨_, htu⟩ : F4.reeGamma K a))
          (t ^ 2 * u⁻¹, t ^ (-(2 ^ a : ℤ)) * u ^ (2 * 2 ^ a - 1 : ℤ), 1)) ∧
    Function.Bijective (fun p : Kˣ × Kˣ =>
      (p.1 ^ 2 * p.2⁻¹, p.1 ^ (-(2 ^ a : ℤ)) * p.2 ^ (2 * 2 ^ a - 1 : ℤ))) := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
  set Γ := F4.reeGamma K a
  set ψ := F4.reeGammaFieldAutHom K a
  have hψapp : ∀ β, ψ β = F4.reeGammaFieldAut K a β := fun β => rfl
  have hA : ∀ α : MulAut Γ, α ∈ largeReeOppAut K a ↔ ∃ (h : Γ) (β : K ≃+* K),
      (h : ModGL F4.tag K) ∈ F4.reeFixedTorus K a ∧ α = MulAut.conj h * F4.reeGammaFieldAut K a β :=
    fun α => ⟨fun hα => exists_conj_mul_reeGammaFieldAut_of_mem ha hK hα, by
      rintro ⟨h, β, hh, rfl⟩
      exact mul_mem ((conj_mem_largeReeOppAut_iff hw₀ h).2 hh)
        (reeGammaFieldAut_mem_largeReeOppAut β)⟩
  have huniq : ∀ (x x' : Γ) (β β' : K ≃+* K),
      MulAut.conj x * F4.reeGammaFieldAut K a β = MulAut.conj x' * F4.reeGammaFieldAut K a β' →
        x = x' ∧ β = β' := by
    intro x x' β β' e
    have e' : MulAut.conj (x'⁻¹ * x) * F4.reeGammaFieldAut K a 1 =
        MulAut.conj 1 * F4.reeGammaFieldAut K a (β' * β⁻¹) := by
      rw [← hψapp, ← hψapp, map_one, map_one, mul_one, one_mul, map_mul, map_mul, map_inv,
        map_inv, hψapp, hψapp, show (MulAut.conj x')⁻¹ * MulAut.conj x =
          (MulAut.conj x')⁻¹ * (MulAut.conj x * F4.reeGammaFieldAut K a β) *
            (F4.reeGammaFieldAut K a β)⁻¹ by group, e]
      group
    have hy : MulAut.conj (x'⁻¹ * x) ∈ largeReeOppAut K a := by
      have h1 : MulAut.conj (x'⁻¹ * x) = F4.reeGammaFieldAut K a (β' * β⁻¹) := by
        rw [← hψapp, map_one, mul_one, map_one, one_mul] at e'
        exact e'
      rw [h1]
      exact reeGammaFieldAut_mem_largeReeOppAut _
    have hyT := (conj_mem_largeReeOppAut_iff hw₀ _).1 hy
    obtain ⟨h1, h2⟩ := eq_of_conj_mul_reeGammaFieldAut_eq ha hK hyT (one_mem _) e'
    refine ⟨(inv_mul_eq_one.1 h1).symm, ?_⟩
    have h3 : β' * β⁻¹ = 1 := h2.symm
    exact (mul_inv_eq_one.1 h3).symm
  have hexists : ∀ α : MulAut Γ, ∃ (x : Γ) (β : K ≃+* K),
      α = MulAut.conj x * F4.reeGammaFieldAut K a β := by
    intro α
    obtain ⟨-, -, -, -, -, hprod⟩ := large_Ree_Sylow_opposition F4 a K w₀ hw₀
    obtain ⟨c, β', hU, hV, rfl⟩ := hprod α
    obtain ⟨h, β, -, hβ'⟩ := (hA β').1 ⟨hU, hV⟩
    exact ⟨c * h, β, by rw [hβ', ← mul_assoc, map_mul]⟩
  have hcompat : ∀ β : K ≃+* K, (MulAut.conj : Γ →* MulAut Γ).comp (ψ β).toMonoidHom =
      (MulAut.conj (ψ β)).toMonoidHom.comp MulAut.conj := fun β =>
    MonoidHom.ext fun y => MulEquiv.ext fun g => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
  set Ψ₀ : Γ ⋊[ψ] (K ≃+* K) →* MulAut Γ := SemidirectProduct.lift MulAut.conj ψ hcompat
  have hΨ₀ : ∀ (x : Γ) (β : K ≃+* K), Ψ₀ ⟨x, β⟩ = MulAut.conj x * F4.reeGammaFieldAut K a β :=
    fun x β => rfl
  have hbij : Function.Bijective Ψ₀ := by
    refine ⟨fun p q hpq => ?_, fun α => ?_⟩
    · have e : MulAut.conj p.left * F4.reeGammaFieldAut K a p.right =
          MulAut.conj q.left * F4.reeGammaFieldAut K a q.right := hpq
      obtain ⟨h1, h2⟩ := huniq _ _ _ _ e
      exact SemidirectProduct.ext h1 h2
    · obtain ⟨x, β, rfl⟩ := hexists α
      exact ⟨⟨x, β⟩, rfl⟩
  set Ψ := MulEquiv.ofBijective Ψ₀ hbij
  have hΨ : ∀ (x : Γ) (β : K ≃+* K), Ψ ⟨x, β⟩ = MulAut.conj x * F4.reeGammaFieldAut K a β :=
    hΨ₀
  set χ : MulAut Γ →* (K ≃+* K) := SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom with hχ
  have hconj : ∀ x : Γ, MulAut.conj x = Ψ ⟨x, 1⟩ := fun x => by
    rw [hΨ, ← hψapp, map_one, mul_one]
  have hχs : Function.Surjective χ := fun β => ⟨Ψ ⟨1, β⟩, by
    rw [hχ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl⟩
  have hker : inner Γ = χ.ker := by
    ext α
    constructor
    · rintro ⟨x, rfl⟩
      rw [MonoidHom.mem_ker, hχ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hconj,
        MulEquiv.symm_apply_apply]
      rfl
    · intro hα
      obtain ⟨⟨x, β⟩, rfl⟩ := Ψ.surjective α
      have h1 : β = 1 := by
        have := hα
        rw [MonoidHom.mem_ker, hχ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply] at this
        exact this
      exact ⟨x, by rw [h1, ← hconj]⟩
  let E : Outer Γ ≃* (K ≃+* K) := (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective χ hχs)
  obtain ⟨σ₀, -, -, hσ₀, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  have hcycAut : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ₀, hσ₀⟩
  refine ⟨fun β => ⟨fun g => rfl, reeGammaFieldAut_mem_largeReeOppAut β⟩, fun α => ?_,
    ⟨Ψ, hΨ⟩, isCyclic_of_surjective E.symm.toMonoidHom E.symm.surjective,
    (Nat.card_congr E.toEquiv).trans hcardAut, hA, fun α hα => ?_, fun t u =>
      ⟨torusPair_mem_reeGamma a hK (t, u), Subgroup.mem_inf.2 ⟨torusPair_mem_torusGroup t u,
        torusPair_mem_reeGamma a hK (t, u)⟩, isLargeReeParam_conj_torusPair hK t u⟩,
    largeReeScalarHom_bijective hK⟩
  · obtain ⟨x, β, hα⟩ := hexists α
    refine ⟨(x, β), hα, fun q hq => ?_⟩
    obtain ⟨h1, h2⟩ := huniq q.1 x q.2 β (hq.symm.trans hα)
    exact Prod.ext h1 h2
  · obtain ⟨h, β, hh, hα'⟩ := (hA α).1 hα
    refine ⟨(h, β), ⟨hh, hα'⟩, fun q hq => ?_⟩
    obtain ⟨e1, e2⟩ := eq_of_conj_mul_reeGammaFieldAut_eq ha hK hq.1 hh (hq.2.symm.trans hα')
    exact Prod.ext e1 e2

end CFSG.ComponentClassification.UnbalancedCatalog
