module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockExtension
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitBorel

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

@[expose] def SplitInv (h : UnitaryFieldData p f K) (μ : Subgroup Kˣ) : Prop :=
  ∀ a : μ, h.bar ((a : Kˣ) : K) = ((a : Kˣ) : K)

theorem splitTorusRatio {h : UnitaryFieldData p f K} {μ : Subgroup Kˣ} (hμ : SplitInv h μ)
    (x : Fin r → μ) :
    torusRatio h (fun i => (x i : Kˣ)) (1 : Fin ε → Kˣ) = 1 := by
  have h1 : ∀ i, ((x i : Kˣ) : K) / h.bar ((x i : Kˣ) : K) = 1 := fun i => by
    rw [hμ (x i)]
    exact div_self (Units.ne_zero ((x i : μ) : Kˣ) :
      (((x i : μ) : Kˣ) : K) ≠ 0)
  rw [torusRatio, Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_const_one]
  simp

@[expose] noncomputable def splitTorusFun (h : UnitaryFieldData p f K) (r ε : ℕ)
    (μ : Subgroup Kˣ) (hμ : SplitInv h μ) (x : Fin r → μ) : hypSU h r ε :=
  (torusMat_mem_hypSU h (fun i => (x i : Kˣ)) (d := 1)
    (fun _ => by simp [UnitaryFieldData.norm])
    (splitTorusRatio hμ x)).choose

theorem splitTorusFun_spec {h : UnitaryFieldData p f K} {r ε : ℕ} {μ : Subgroup Kˣ}
    (hμ : SplitInv h μ) (x : Fin r → μ) :
    splitTorusFun h r ε μ hμ x ∈ hypTorus h r ε ∧
      (((splitTorusFun h r ε μ hμ x : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) =
        diagonal (torusEntries h (fun i => (x i : Kˣ)) (1 : Fin ε → Kˣ)) :=
  (torusMat_mem_hypSU h (fun i => (x i : Kˣ)) (d := 1)
    (fun _ => by simp [UnitaryFieldData.norm])
    (splitTorusRatio hμ x)).choose_spec

@[expose] noncomputable def splitTorusHom (h : UnitaryFieldData p f K) (r ε : ℕ)
    (μ : Subgroup Kˣ) (hμ : SplitInv h μ) : (Fin r → μ) →* hypSU h r ε where
  toFun := splitTorusFun h r ε μ hμ
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [(splitTorusFun_spec (r := r) (ε := ε) hμ 1).2]
    change diagonal (torusEntries h (fun i => ((1 : Fin r → μ) i : Kˣ)) 1) =
      (1 : Matrix (HypIndex r ε) (HypIndex r ε) K)
    rw [← Matrix.diagonal_one]
    congr 1
    funext y
    rcases y with i | k | i <;> simp [torusEntries]
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, (splitTorusFun_spec (r := r) (ε := ε) hμ x).2,
      (splitTorusFun_spec (r := r) (ε := ε) hμ y).2,
      (splitTorusFun_spec (r := r) (ε := ε) hμ (x * y)).2,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext z
    rcases z with i | k | i <;> simp [torusEntries, map_mul, mul_inv, mul_comm]

@[simp] theorem splitTorusHom_apply {h : UnitaryFieldData p f K} {r ε : ℕ} {μ : Subgroup Kˣ}
    (hμ : SplitInv h μ) (x : Fin r → μ) :
    splitTorusHom h r ε μ hμ x = splitTorusFun h r ε μ hμ x := rfl

theorem splitTorusHom_mem_hypTorus {h : UnitaryFieldData p f K} {r ε : ℕ} {μ : Subgroup Kˣ}
    (hμ : SplitInv h μ) (x : Fin r → μ) :
    splitTorusHom h r ε μ hμ x ∈ hypTorus h r ε :=
  (splitTorusFun_spec hμ x).1

theorem coe_splitTorusHom {h : UnitaryFieldData p f K} {r ε : ℕ} {μ : Subgroup Kˣ}
    (hμ : SplitInv h μ) (x : Fin r → μ) :
    (((splitTorusHom h r ε μ hμ x : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal (torusEntries h (fun i => (x i : Kˣ)) (1 : Fin ε → Kˣ)) :=
  (splitTorusFun_spec hμ x).2

theorem splitTorusHom_injective {h : UnitaryFieldData p f K} {r ε : ℕ} {μ : Subgroup Kˣ}
    (hμ : SplitInv h μ) : Function.Injective (splitTorusHom h r ε μ hμ) := by
  intro x y hxy
  have hmat : (((splitTorusHom h r ε μ hμ x : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      (((splitTorusHom h r ε μ hμ y : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by rw [hxy]
  rw [coe_splitTorusHom, coe_splitTorusHom] at hmat
  funext i
  apply Subtype.ext
  apply Units.ext
  have h1 := congrArg (fun M : Matrix (HypIndex r ε) (HypIndex r ε) K =>
    M (.inl i) (.inl i)) hmat
  simpa [torusEntries] using h1

theorem splitTorusHom_range_card {h : UnitaryFieldData p f K} {r ε : ℕ} {μ : Subgroup Kˣ}
    (hμ : SplitInv h μ) :
    Nat.card (splitTorusHom h r ε μ hμ).range = Nat.card μ ^ r := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (splitTorusHom_injective hμ)).toEquiv]
  simp [Nat.card_fun]

theorem splitTorusHom_range_comm {h : UnitaryFieldData p f K} {r ε : ℕ} {μ : Subgroup Kˣ}
    (hμ : SplitInv h μ) : IsMulCommutative (splitTorusHom h r ε μ hμ).range :=
  IsMulCommutative.of_comm fun a b => by
    apply Subtype.ext
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul,
      show (a : hypSU h r ε) = splitTorusHom h r ε μ hμ x from hx.symm,
      show (b : hypSU h r ε) = splitTorusHom h r ε μ hμ y from hy.symm]
    exact CFSG.Quasithin.H13.Sec53F.Unit.hypTorus_comm h
      (splitTorusHom_mem_hypTorus hμ x) (splitTorusHom_mem_hypTorus hμ y)

theorem splitTorusHom_range_isElemAbelian {h : UnitaryFieldData p f K} {r ε : ℕ}
    {μ : Subgroup Kˣ} (hμ : SplitInv h μ) {ℓ : ℕ} (hexp : ∀ a : μ, a ^ ℓ = 1) :
    IsElemAbelian ℓ (splitTorusHom h r ε μ hμ).range := by
  refine ⟨splitTorusHom_range_comm hμ, ?_⟩
  rintro z ⟨x, hx⟩
  rw [← hx, ← map_pow]
  have hx' : x ^ ℓ = 1 := funext fun i => hexp (x i)
  rw [hx', map_one]

theorem splitTorusHom_eq_one_of_mem_scalars {h : UnitaryFieldData p f K} {r ε : ℕ}
    {μ : Subgroup Kˣ} (hμ : SplitInv h μ) (hodd : Odd (Nat.card μ)) {x : Fin r → μ}
    (hx : splitTorusHom h r ε μ hμ x ∈ hypScalars h r ε) : x = 1 := by
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hx
  have hmat : (((splitTorusHom h r ε μ hμ x : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = Matrix.scalar (HypIndex r ε) (c : K) := by
    have h := congrArg (fun g : GL (HypIndex r ε) K =>
      ((g : Matrix (HypIndex r ε) (HypIndex r ε) K))) hc
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using h
  have hdiag : ∀ y, torusEntries h (fun i => (x i : Kˣ)) (1 : Fin ε → Kˣ) y = (c : K) := by
    intro y
    have h1 := congrFun (congrFun (coe_splitTorusHom hμ x ▸ hmat) y) y
    simpa [Matrix.scalar_apply] using h1
  funext i
  apply Subtype.ext
  apply Units.ext
  have h1 : ((x i : Kˣ) : K) = (c : K) := by
    simpa [torusEntries] using hdiag (.inl i)
  have h2 : (((x i : Kˣ) : K))⁻¹ = (c : K) := by
    simpa [torusEntries, hμ (x i)] using hdiag (.inr (.inr i))
  have hsq : ((x i : μ) : Kˣ) ^ 2 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_two, Units.val_one]
    have h3 : (((x i : Kˣ) : K))⁻¹ = ((x i : Kˣ) : K) := h2.trans h1.symm
    calc (((x i : μ) : Kˣ) : K) * (((x i : μ) : Kˣ) : K)
        = (((x i : μ) : Kˣ) : K) * ((((x i : μ) : Kˣ) : K))⁻¹ := by rw [h3]
      _ = 1 := mul_inv_cancel₀ (Units.ne_zero ((x i : μ) : Kˣ))
  have hdvd2 : orderOf (((x i : μ) : Kˣ)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hord : orderOf (((x i : μ) : Kˣ)) = orderOf (x i) :=
    orderOf_injective (Subgroup.subtype μ) (Subgroup.subtype_injective μ) (x i)
  have hdvdμ : orderOf (((x i : μ) : Kˣ)) ∣ Nat.card μ := by
    rw [hord]
    exact orderOf_dvd_natCard _
  have hodd' : Odd (orderOf (((x i : μ) : Kˣ))) := Odd.of_dvd_nat hodd hdvdμ
  have h1' : orderOf (((x i : μ) : Kˣ)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h | h
    · exact h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  have hxi : ((x i : μ) : Kˣ) = 1 := orderOf_eq_one_iff.mp h1'
  rw [hxi]
  rfl

theorem splitTorusHom_comp_injective {h : UnitaryFieldData p f K} {r ε : ℕ} {μ : Subgroup Kˣ}
    (hμ : SplitInv h μ) (hodd : Odd (Nat.card μ)) {X : Type} [Group X]
    (α : hypSU h r ε →* X) (hker : ∀ s, α s = 1 → s ∈ hypScalars h r ε) :
    Function.Injective (α.comp (splitTorusHom h r ε μ hμ)) := by
  refine (injective_iff_map_eq_one _).2 fun a ha => ?_
  exact splitTorusHom_eq_one_of_mem_scalars hμ hodd (hker _ ha)

theorem splitTorusHom_range_map_card {h : UnitaryFieldData p f K} {r ε : ℕ} {μ : Subgroup Kˣ}
    (hμ : SplitInv h μ) (hodd : Odd (Nat.card μ)) {X : Type} [Group X]
    (α : hypSU h r ε →* X) (hker : ∀ s, α s = 1 → s ∈ hypScalars h r ε) :
    Nat.card ((splitTorusHom h r ε μ hμ).range.map α) = Nat.card μ ^ r := by
  classical
  let D : Subgroup (hypSU h r ε) := (splitTorusHom h r ε μ hμ).range
  let f : (Fin r → μ) → (D.map α) := fun a =>
    ⟨α (splitTorusHom h r ε μ hμ a), Subgroup.mem_map_of_mem α ⟨a, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · exact splitTorusHom_comp_injective hμ hodd α hker (congrArg Subtype.val hab)
    · obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
      obtain ⟨a, ha⟩ := hx
      refine ⟨a, Subtype.ext ?_⟩
      change α (splitTorusHom h r ε μ hμ a) = (y : X)
      rw [ha, hxy]
  have hcard : Nat.card (D.map α) = Nat.card (Fin r → μ) :=
    (Nat.card_congr (Equiv.ofBijective f hf)).symm
  rw [show (splitTorusHom h r ε μ hμ).range.map α = D.map α from rfl, hcard]
  simp [Nat.card_fun]

theorem extId_mul_diagonal_of_eq_one_on_range {ι κ R : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [CommRing R] (θ : ι → κ) (hθ : Function.Injective θ)
    (M : Matrix ι ι R) (d : κ → R) (hd : ∀ i, d (θ i) = 1) :
    CFSG.HardMathSupport.Curtis.UnitaryLevi.extId θ hθ M * diagonal d =
      diagonal d * CFSG.HardMathSupport.Curtis.UnitaryLevi.extId θ hθ M := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases ha : a ∈ Set.range θ
  · obtain ⟨i, rfl⟩ := ha
    by_cases hb : b ∈ Set.range θ
    · obtain ⟨j, rfl⟩ := hb
      rw [CFSG.HardMathSupport.Curtis.UnitaryLevi.extId_apply_map, hd i, hd j]
      ring
    · rw [CFSG.HardMathSupport.Curtis.UnitaryLevi.extId_apply_of_not_right θ hθ M _ hb]
      by_cases hab : θ i = b
      · subst hab
        exact absurd ⟨i, rfl⟩ hb
      · simp [one_apply, hab]
  · by_cases hb : b ∈ Set.range θ
    · obtain ⟨j, rfl⟩ := hb
      rw [CFSG.HardMathSupport.Curtis.UnitaryLevi.extId_apply_of_not_left θ hθ M ha]
      by_cases hab : a = θ j
      · subst hab
        exact absurd ⟨j, rfl⟩ ha
      · simp [one_apply, hab]
    · rw [CFSG.HardMathSupport.Curtis.UnitaryLevi.extId_apply_of_not_left θ hθ M ha]
      by_cases hab : a = b
      · subst hab; simp
      · simp [one_apply, hab]

@[expose] noncomputable def torusFunOfRatio (h : UnitaryFieldData p f K) (r ε : ℕ)
    {M : Type*} [Monoid M] (a : M →* (Fin r → Kˣ))
    (ha : ∀ m, torusRatio h (a m) (1 : Fin ε → Kˣ) = 1) (m : M) : hypSU h r ε :=
  (torusMat_mem_hypSU h (a m) (d := 1)
    (fun _ => by simp [UnitaryFieldData.norm]) (ha m)).choose

theorem torusFunOfRatio_spec {h : UnitaryFieldData p f K} {r ε : ℕ} {M : Type*} [Monoid M]
    (a : M →* (Fin r → Kˣ)) (ha : ∀ m, torusRatio h (a m) (1 : Fin ε → Kˣ) = 1)
    (m : M) :
    torusFunOfRatio h r ε a ha m ∈ hypTorus h r ε ∧
      (((torusFunOfRatio h r ε a ha m : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) =
        diagonal (torusEntries h (a m) (1 : Fin ε → Kˣ)) :=
  (torusMat_mem_hypSU h (a m) (d := 1)
    (fun _ => by simp [UnitaryFieldData.norm]) (ha m)).choose_spec

@[expose] noncomputable def torusHomOfRatio (h : UnitaryFieldData p f K) (r ε : ℕ)
    {M : Type*} [Monoid M] (a : M →* (Fin r → Kˣ))
    (ha : ∀ m, torusRatio h (a m) (1 : Fin ε → Kˣ) = 1) : M →* hypSU h r ε where
  toFun := torusFunOfRatio h r ε a ha
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [(torusFunOfRatio_spec (r := r) (ε := ε) a ha 1).2]
    change diagonal (torusEntries h (a 1) 1) = (1 : Matrix (HypIndex r ε) (HypIndex r ε) K)
    rw [map_one a, ← Matrix.diagonal_one]
    congr 1
    funext y
    rcases y with i | k | i <;> simp [torusEntries]
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, (torusFunOfRatio_spec (r := r) (ε := ε) a ha x).2,
      (torusFunOfRatio_spec (r := r) (ε := ε) a ha y).2,
      (torusFunOfRatio_spec (r := r) (ε := ε) a ha (x * y)).2,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext z
    rcases z with i | k | i <;> simp [torusEntries, map_mul, mul_inv, mul_comm]

@[simp] theorem torusHomOfRatio_apply {h : UnitaryFieldData p f K} {r ε : ℕ} {M : Type*}
    [Monoid M] {a : M →* (Fin r → Kˣ)}
    {ha : ∀ m, torusRatio h (a m) (1 : Fin ε → Kˣ) = 1} (m : M) :
    torusHomOfRatio h r ε a ha m = torusFunOfRatio h r ε a ha m := rfl

theorem coe_torusHomOfRatio {h : UnitaryFieldData p f K} {r ε : ℕ} {M : Type*} [Monoid M]
    {a : M →* (Fin r → Kˣ)} {ha : ∀ m, torusRatio h (a m) (1 : Fin ε → Kˣ) = 1} (m : M) :
    (((torusHomOfRatio h r ε a ha m : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal (torusEntries h (a m) (1 : Fin ε → Kˣ)) :=
  (torusFunOfRatio_spec a ha m).2

@[expose] noncomputable def invPairParams {r : ℕ} (i j : Fin r) :
    Kˣ →* (Fin r → Kˣ) :=
  MonoidHom.mulSingle (fun _ => Kˣ) i * (MonoidHom.mulSingle (fun _ => Kˣ) j).comp invMonoidHom

theorem invPairParams_apply_left {i j : Fin r} (hij : i ≠ j) (t : Kˣ) :
    invPairParams i j t i = t := by
  simp [invPairParams, Pi.mulSingle_apply, hij]

theorem invPairParams_apply_right {i j : Fin r} (hij : i ≠ j) (t : Kˣ) :
    invPairParams i j t j = t⁻¹ := by
  simp [invPairParams, Pi.mulSingle_apply, hij]

theorem invPairParams_apply_of_ne {i j k : Fin r} (hki : k ≠ i) (hkj : k ≠ j) (t : Kˣ) :
    invPairParams i j t k = 1 := by
  simp [invPairParams, Pi.mulSingle_apply, hki, hkj]

theorem torusRatio_mulSingle (h : UnitaryFieldData p f K) (i : Fin r) (t : Kˣ) :
    torusRatio h (Pi.mulSingle i t : Fin r → Kˣ) (1 : Fin ε → Kˣ) =
      (t : K) / h.bar (t : K) := by
  rw [torusRatio]
  have hprod : ∏ b, ((Pi.mulSingle i t : Fin r → Kˣ) b : K) /
      h.bar (((Pi.mulSingle i t : Fin r → Kˣ) b) : K) = (t : K) / h.bar (t : K) := by
    rw [Finset.prod_eq_single i]
    · rw [Pi.mulSingle_eq_same]
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne (i := i) (i' := b) hb]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hprod]
  simp

theorem torusRatio_invPairParams (h : UnitaryFieldData p f K) {i j : Fin r} (hij : i ≠ j)
    (t : Kˣ) : torusRatio h (invPairParams i j t) (1 : Fin ε → Kˣ) = 1 := by
  have hsplit : invPairParams i j t =
      (Pi.mulSingle i t : Fin r → Kˣ) * Pi.mulSingle j t⁻¹ := rfl
  rw [hsplit, ← mul_one (1 : Fin ε → Kˣ), torusRatio_mul, torusRatio_mulSingle,
    torusRatio_mulSingle]
  have ht : (t : K) ≠ 0 := Units.ne_zero t
  have hbt : h.bar (t : K) ≠ 0 := by
    intro h0
    exact ht (h.bar.injective (by rw [h0, map_zero]))
  rw [Units.val_inv_eq_inv_val, map_inv₀, div_inv_eq_mul, div_eq_mul_inv]
  field_simp

theorem hypSU_commute_of_matrix_comm {h : UnitaryFieldData p f K} {r ε : ℕ}
    {g g' : hypSU h r ε}
    (hm : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((g' : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        ((g' : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) :
    Commute g g' := by
  apply Subtype.ext
  apply Units.ext
  simpa only [Subgroup.coe_mul, Units.val_mul] using hm

theorem splitInv_zpowers (h : UnitaryFieldData p f K) {ζ : Kˣ} {d : ℕ} (hd1 : 1 < d)
    (hd : ζ ^ d = 1) (hdq : d ∣ p ^ f - 1) :
    SplitInv h (Subgroup.zpowers ζ) := by
  have hbarζ : h.bar (ζ : K) = (ζ : K) := by
    rw [UnitaryFieldData.bar_apply, ← Units.val_pow_eq_pow_val,
      pow_eq_pow_mod (p ^ f) hd]
    have hq : p ^ f = (p ^ f - 1) + 1 := by
      have := Nat.one_le_pow f p h.prime.pos
      omega
    have hqmod : p ^ f % d = 1 := by
      rw [hq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdq, Nat.zero_add]
      have h1d : 1 % d = 1 := Nat.mod_eq_of_lt hd1
      rw [h1d, h1d]
    rw [hqmod, pow_one]
  intro a
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
  rw [show ((a : Kˣ) : K) = ((ζ ^ k : Kˣ) : K) from congrArg Units.val hk.symm,
    Units.val_zpow_eq_zpow_val, map_zpow₀ h.bar, hbarζ]

end CFSG.ClassicalGroups.UnitaryFlag
