module

public import CFSG.LieType.Ree.LargeReeBlockCollection
public import CFSG.LieType.Ree.LargeReeB2PairAutomorphism
public import CFSG.LieType.Ree.LargeReeA1Pair
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Ree.LargeReeHeightQuotient

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag

@[expose] def kTwo (t : Fin 4) : Fin F4.fixedWeylOrder :=
  ⟨![0, 2, 3, 6] t, by fin_cases t <;> decide⟩

@[expose] def kFour (f : Fin 4) : Fin F4.fixedWeylOrder :=
  ⟨![0, 1, 4, 5] f, by fin_cases f <;> decide⟩

@[expose] def relWord (k : Fin F4.fixedWeylOrder) : List (Fin F4.tag.rank) :=
  (F4.fixedRelWord k).flatMap F4.fixedOrbitWord

@[expose] def stdTwoRoot (i : Fin 2) : Fin F4.tag.rank → ℤ :=
  (F4.fixedOrbitRootList ⟨0, by decide⟩).getD i 0

@[expose] def stdFourRoot (i : Fin 4) : Fin F4.tag.rank → ℤ :=
  (F4.fixedOrbitRootList ⟨1, by decide⟩).getD i 0

@[expose] def twoRoot (t : Fin 4) (i : Fin 2) : Fin F4.tag.rank → ℤ :=
  (relWord (kTwo t)).foldr (reflect F4.tag) (stdTwoRoot i)

@[expose] def fourRoot (f : Fin 4) (i : Fin 4) : Fin F4.tag.rank → ℤ :=
  (relWord (kFour f)).foldr (reflect F4.tag) (stdFourRoot i)

theorem fixedRelElt_smul
    (k : Fin F4.fixedWeylOrder) (v : Fin F4.tag.rank → ℤ) :
    F4.fixedRelElt k • v = (relWord k).foldr (reflect F4.tag) v := by
  rw [fixedRelElt, list_prod_map_fixedOrbitElement, CFSG.LieType.Ree.wordProd_smul]
  rfl

@[expose] def twoPos (t : Fin 4) (i : Fin 2) : ℕ :=
  ![![3, 0], ![25, 21], ![31, 30], ![36, 35]] t i

@[expose] def fourPos (f : Fin 4) (i : Fin 4) : ℕ :=
  ![![2, 1, 8, 7], ![10, 5, 24, 22], ![17, 13, 40, 39], ![16, 15, 44, 43]] f i

theorem twoRoot_check : ∀ t : Fin 4, ∀ i : Fin 2,
    twoPos t i < F4.tag.rootCertificate.roots.length ∧
      twoRoot t i = F4.tag.rootCertificate.root (twoPos t i) := by
  decide +kernel

theorem fourRoot_check : ∀ f : Fin 4, ∀ i : Fin 4,
    fourPos f i < F4.tag.rootCertificate.roots.length ∧
      fourRoot f i = F4.tag.rootCertificate.root (fourPos f i) := by
  decide +kernel

theorem stdTwoRoot_eq (i : Fin 2) : stdTwoRoot i = twoRoot 0 i :=
  rfl

theorem stdFourRoot_eq (i : Fin 4) : stdFourRoot i = fourRoot 0 i :=
  rfl

theorem isRoot_twoRoot
    (t : Fin 4) (i : Fin 2) : IsRoot F4.tag (twoRoot t i) := by
  rw [(twoRoot_check t i).2]
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check F4.tag) _ (twoRoot_check t i).1

theorem isRoot_fourRoot
    (f : Fin 4) (i : Fin 4) : IsRoot F4.tag (fourRoot f i) := by
  rw [(fourRoot_check f i).2]
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check F4.tag) _ (fourRoot_check f i).1

theorem isRoot_stdTwoRoot
    (i : Fin 2) : IsRoot F4.tag (stdTwoRoot i) := by
  rw [stdTwoRoot_eq]
  exact isRoot_twoRoot 0 i

theorem isRoot_stdFourRoot
    (i : Fin 4) : IsRoot F4.tag (stdFourRoot i) := by
  rw [stdFourRoot_eq]
  exact isRoot_fourRoot 0 i

theorem height_check :
    (∀ t : Fin 4, 0 < height (twoRoot t 0) ∧ height (twoRoot t 0) ≤ height (twoRoot t 1)) ∧
    ∀ f : Fin 4, 0 < height (fourRoot f 0) ∧ height (fourRoot f 0) ≤ height (fourRoot f 1) ∧
      height (fourRoot f 0) < height (fourRoot f 2) ∧
      height (fourRoot f 2) ≤ height (fourRoot f 3) := by
  decide +kernel

theorem char_check :
    (∀ t : Fin 4, (7 : ℤ) ∣ torusExp0 2 (twoRoot t 1) - 4 * torusExp0 2 (twoRoot t 0) ∧
      (7 : ℤ) ∣ torusExp1 2 (twoRoot t 1) - 4 * torusExp1 2 (twoRoot t 0)) ∧
    ∀ f : Fin 4, (7 : ℤ) ∣ torusExp0 2 (fourRoot f 1) - 4 * torusExp0 2 (fourRoot f 0) ∧
      (7 : ℤ) ∣ torusExp1 2 (fourRoot f 1) - 4 * torusExp1 2 (fourRoot f 0) ∧
      (7 : ℤ) ∣ torusExp0 2 (fourRoot f 3) - 4 * torusExp0 2 (fourRoot f 2) ∧
      (7 : ℤ) ∣ torusExp1 2 (fourRoot f 3) - 4 * torusExp1 2 (fourRoot f 2) ∧
      (7 : ℤ) ∣ torusExp0 2 (fourRoot f 3) - 6 * torusExp0 2 (fourRoot f 0) ∧
      (7 : ℤ) ∣ torusExp1 2 (fourRoot f 3) - 6 * torusExp1 2 (fourRoot f 0) := by
  decide +kernel

variable {K : Type} [Field K]

theorem units_pow_seven [Finite K] (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (u : Kˣ) : u ^ 7 = 1 := by
  have h := pow_card_eq_one' (G := Kˣ) (x := u)
  rwa [Nat.card_units, hK] at h

theorem zpow_eq_of_dvd [Finite K] (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (u : Kˣ) {m n : ℤ}
    (h : (7 : ℤ) ∣ m - n) : u ^ m = u ^ n := by
  obtain ⟨k, hk⟩ := h
  rw [show m = n + 7 * k by linarith, zpow_add, zpow_mul, show (7 : ℤ) = ((7 : ℕ) : ℤ) from rfl,
    zpow_natCast, units_pow_seven hK, one_zpow, mul_one]

theorem torusWeight_eq_pow [Finite K] (hK : Nat.card K = 2 ^ (2 * 1 + 1))
    {α β : Fin F4.tag.rank → ℤ} {n : ℕ}
    (h0 : (7 : ℤ) ∣ torusExp0 2 β - n * torusExp0 2 α)
    (h1 : (7 : ℤ) ∣ torusExp1 2 β - n * torusExp1 2 α) (t : Kˣ × Kˣ) :
    torusWeight (K := K) 1 β t = torusWeight 1 α t ^ n := by
  obtain ⟨u, v⟩ := t
  rw [torusWeight_apply, torusWeight_apply, mul_pow, ← zpow_natCast, ← zpow_natCast,
    ← zpow_mul, ← zpow_mul]
  congr 1
  · exact zpow_eq_of_dvd hK u (by rw [mul_comm]; exact h0)
  · exact zpow_eq_of_dvd hK v (by rw [mul_comm]; exact h1)

@[expose] def stdTwo
    (s : K) : ModGL F4.tag K :=
  pinnedX F4.tag K (stdTwoRoot 0) s * pinnedX F4.tag K (stdTwoRoot 1) (s ^ 4)

@[expose] def stdFour
    (c d : K) : ModGL F4.tag K :=
  pinnedX F4.tag K (stdFourRoot 0) c * pinnedX F4.tag K (stdFourRoot 1) (c ^ 4) *
    pinnedX F4.tag K (stdFourRoot 2) d * pinnedX F4.tag K (stdFourRoot 3) (d ^ 4 + c ^ 6)

theorem stdFour_eq_largeReeCoord
    (c d : K) : stdFour c d = largeReeCoord 1 K c d := by
  have e : ∀ i : Fin 4, stdFourRoot i = largeReeRoot i := by
    intro i
    fin_cases i <;> rfl
  simp only [stdFour, largeReeCoord, largeReeP, largeReeX, largeReeSigma, e]
  congr 2
  ring

theorem stdTwo_eq_xUnit
    (s : K) :
    stdTwo s = xUnit F4.tag K largeReeI1 (s ^ 4) * xUnit F4.tag K largeReeI4 s := by
  have e0 : stdTwoRoot 0 = Pi.single largeReeI4 1 := by decide +kernel
  have e1 : stdTwoRoot 1 = Pi.single largeReeI1 1 := by decide +kernel
  rw [stdTwo, e0, e1, pinnedX_single, pinnedX_single]
  exact ((largeRee_commute_xx (s ^ 4) s).eq).symm

variable [Finite K] [CharP K F4.prime]

theorem stdTwo_mem
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (s : K) :
    stdTwo s ∈ F4.reeFixedOrbitUnipotent K 1 ⟨0, by decide⟩ := by
  have : Fintype K := Fintype.ofFinite K
  have hs : (s ^ 4) ^ 2 ^ 1 = s := by
    rw [← pow_mul, show 4 * 2 ^ 1 = Fintype.card K by rw [← Nat.card_eq_fintype_card, hK]; rfl,
      FiniteField.pow_card]
  have h := coe_reeFixedOrbitUnipotent_zero (K := K) (a := 1) hK
  have hmem : xUnit F4.tag K largeReeI1 (s ^ 4) * xUnit F4.tag K largeReeI4 ((s ^ 4) ^ 2 ^ 1) ∈
      (F4.reeFixedOrbitUnipotent K 1 ⟨0, by decide⟩ : Set (ModGL F4.tag K)) := by
    rw [h]
    exact ⟨s ^ 4, rfl⟩
  rw [hs] at hmem
  rw [stdTwo_eq_xUnit]
  exact hmem

theorem stdFour_mem
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (c d : K) :
    stdFour c d ∈ F4.reeFixedOrbitUnipotent K 1 ⟨1, by decide⟩ := by
  rw [stdFour_eq_largeReeCoord]
  exact largeReeCoord_mem hK c d

theorem exists_stdTwo_eq
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) {g : ModGL F4.tag K}
    (hg : g ∈ F4.reeFixedOrbitUnipotent K 1 ⟨0, by decide⟩) : ∃ s : K, stdTwo s = g := by
  have : Fintype K := Fintype.ofFinite K
  have h := coe_reeFixedOrbitUnipotent_zero (K := K) (a := 1) hK
  have hg' : g ∈ (F4.reeFixedOrbitUnipotent K 1 ⟨0, by decide⟩ : Set (ModGL F4.tag K)) := hg
  rw [h] at hg'
  obtain ⟨c, rfl⟩ := hg'
  refine ⟨c ^ 2 ^ 1, ?_⟩
  have hc : (c ^ 2 ^ 1) ^ 4 = c := by
    rw [← pow_mul, show 2 ^ 1 * 4 = Fintype.card K by rw [← Nat.card_eq_fintype_card, hK]; rfl,
      FiniteField.pow_card]
  rw [stdTwo_eq_xUnit, hc]

theorem exists_stdFour_eq
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) {g : ModGL F4.tag K}
    (hg : g ∈ F4.reeFixedOrbitUnipotent K 1 ⟨1, by decide⟩) :
    ∃ c d : K, stdFour c d = g := by
  obtain ⟨c, d, rfl⟩ := exists_largeReeCoord_eq hK hg
  exact ⟨c, d, stdFour_eq_largeReeCoord c d⟩

variable (K) in
@[expose] def nTwo
    (t : Fin 4) : ModGL F4.tag K :=
  canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt (kTwo t))

variable (K) in
@[expose] def nFour
    (f : Fin 4) : ModGL F4.tag K :=
  canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt (kFour f))

theorem nTwo_mem
    (t : Fin 4) : nTwo K t ∈ F4.reeGamma K 1 :=
  (Subgroup.mem_inf.1 (canonicalRep_mem_reeFixedMonomial F4 K 1 (fixedRelElt_mem _))).2

theorem nFour_mem
    (f : Fin 4) : nFour K f ∈ F4.reeGamma K 1 :=
  (Subgroup.mem_inf.1 (canonicalRep_mem_reeFixedMonomial F4 K 1 (fixedRelElt_mem _))).2

@[expose] def twoCoord
    (t : Fin 4) (s : K) : ModGL F4.tag K :=
  nTwo K t * stdTwo s * (nTwo K t)⁻¹

@[expose] def fourCoord
    (f : Fin 4) (c d : K) : ModGL F4.tag K :=
  nFour K f * stdFour c d * (nFour K f)⁻¹

omit [Finite K] in
theorem conj_relElt_pinnedX
    (k : Fin F4.fixedWeylOrder) {α : Fin F4.tag.rank → ℤ}
    (hα : IsRoot F4.tag α) (c : K) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k) * pinnedX F4.tag K α c *
        (canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k))⁻¹ =
      pinnedX F4.tag K ((relWord k).foldr (reflect F4.tag) α) c := by
  rw [canonicalRep_mul_pinnedX_mul_inv_of_two F4_two_eq_zero _ hα, fixedRelElt_smul]

omit [Finite K] in
theorem twoCoord_eq
    (t : Fin 4) (s : K) :
    twoCoord t s =
      pinnedX F4.tag K (twoRoot t 0) s * pinnedX F4.tag K (twoRoot t 1) (s ^ 4) := by
  have e : ∀ n A B : ModGL F4.tag K, n * (A * B) * n⁻¹ = n * A * n⁻¹ * (n * B * n⁻¹) :=
    fun _ _ _ => by group
  rw [twoCoord, stdTwo, e, nTwo, conj_relElt_pinnedX _ (isRoot_stdTwoRoot 0),
    conj_relElt_pinnedX _ (isRoot_stdTwoRoot 1)]
  rfl

omit [Finite K] in
theorem fourCoord_eq
    (f : Fin 4) (c d : K) :
    fourCoord f c d =
      pinnedX F4.tag K (fourRoot f 0) c * pinnedX F4.tag K (fourRoot f 1) (c ^ 4) *
        pinnedX F4.tag K (fourRoot f 2) d * pinnedX F4.tag K (fourRoot f 3) (d ^ 4 + c ^ 6) := by
  have e : ∀ n A B C D : ModGL F4.tag K, n * (A * B * C * D) * n⁻¹ =
      n * A * n⁻¹ * (n * B * n⁻¹) * (n * C * n⁻¹) * (n * D * n⁻¹) := fun _ _ _ _ _ => by group
  rw [fourCoord, stdFour, e, nFour, conj_relElt_pinnedX _ (isRoot_stdFourRoot 0),
    conj_relElt_pinnedX _ (isRoot_stdFourRoot 1), conj_relElt_pinnedX _ (isRoot_stdFourRoot 2),
    conj_relElt_pinnedX _ (isRoot_stdFourRoot 3)]
  rfl

theorem twoCoord_mem_reeGamma
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (t : Fin 4) (s : K) :
    twoCoord t s ∈ F4.reeGamma K 1 :=
  mul_mem (mul_mem (nTwo_mem t) (Subgroup.mem_inf.1 (stdTwo_mem hK s)).2) (inv_mem (nTwo_mem t))

theorem fourCoord_mem_reeGamma
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (f : Fin 4) (c d : K) :
    fourCoord f c d ∈ F4.reeGamma K 1 :=
  mul_mem (mul_mem (nFour_mem f) (Subgroup.mem_inf.1 (stdFour_mem hK c d)).2)
    (inv_mem (nFour_mem f))

omit [Finite K] in
theorem twoCoord_mem_heightSeries
    (t : Fin 4) (s : K) :
    twoCoord t s ∈ heightSeries F4.tag K (height (twoRoot t 0)) := by
  obtain ⟨h0, h1⟩ := height_check.1 t
  rw [twoCoord_eq]
  exact mul_mem (pinnedX_mem_heightSeries ⟨isRoot_twoRoot t 0, h0, le_rfl⟩ _)
    (pinnedX_mem_heightSeries ⟨isRoot_twoRoot t 1, by omega, h1⟩ _)

omit [Finite K] in
theorem fourCoord_mem_heightSeries
    (f : Fin 4) (c d : K) :
    fourCoord f c d ∈ heightSeries F4.tag K (height (fourRoot f 0)) := by
  obtain ⟨h0, h1, h2, h3⟩ := height_check.2 f
  rw [fourCoord_eq]
  exact mul_mem (mul_mem (mul_mem (pinnedX_mem_heightSeries ⟨isRoot_fourRoot f 0, h0, le_rfl⟩ _)
    (pinnedX_mem_heightSeries ⟨isRoot_fourRoot f 1, by omega, h1⟩ _))
    (pinnedX_mem_heightSeries ⟨isRoot_fourRoot f 2, by omega, h2.le⟩ _))
    (pinnedX_mem_heightSeries ⟨isRoot_fourRoot f 3, by omega, by omega⟩ _)

omit [Finite K] in
theorem fourCoord_zero_mem_heightSeries
    (f : Fin 4) (d : K) :
    fourCoord f 0 d ∈ heightSeries F4.tag K (height (fourRoot f 2)) := by
  obtain ⟨h0, -, h2, h3⟩ := height_check.2 f
  rw [fourCoord_eq, zero_pow (by norm_num), zero_pow (by norm_num), add_zero, pinnedX_zero,
    pinnedX_zero, one_mul, one_mul]
  exact mul_mem (pinnedX_mem_heightSeries ⟨isRoot_fourRoot f 2, by omega, le_rfl⟩ _)
    (pinnedX_mem_heightSeries ⟨isRoot_fourRoot f 3, by omega, h3⟩ _)

theorem twoCoord_mem
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (t : Fin 4) (s : K) :
    twoCoord t s ∈ F4.reeFixedPosUnipotent K 1 := by
  refine Subgroup.mem_inf.2 ⟨?_, twoCoord_mem_reeGamma hK t s⟩
  rw [← heightSeries_one]
  exact heightSeries_antitone (by have := (height_check.1 t).1; omega)
    (twoCoord_mem_heightSeries t s)

theorem fourCoord_mem
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (f : Fin 4) (c d : K) :
    fourCoord f c d ∈ F4.reeFixedPosUnipotent K 1 := by
  refine Subgroup.mem_inf.2 ⟨?_, fourCoord_mem_reeGamma hK f c d⟩
  rw [← heightSeries_one]
  exact heightSeries_antitone (by have := (height_check.2 f).1; omega)
    (fourCoord_mem_heightSeries f c d)

omit [Finite K] in
theorem stdTwo_add
    (s s' : K) : stdTwo (s + s') = stdTwo s * stdTwo s' := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hc : Commute (pinnedX F4.tag K (stdTwoRoot 1) (s ^ 4))
      (pinnedX F4.tag K (stdTwoRoot 0) s') := by
    have e0 : stdTwoRoot 0 = Pi.single largeReeI4 1 := by decide +kernel
    have e1 : stdTwoRoot 1 = Pi.single largeReeI1 1 := by decide +kernel
    rw [e0, e1, pinnedX_single, pinnedX_single]
    exact largeRee_commute_xx _ _
  have hp : (s + s') ^ 4 = s ^ 4 + s' ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, pow_mul, CharTwo.add_sq, CharTwo.add_sq]
  rw [stdTwo, stdTwo, stdTwo, hp, pinnedX_add, pinnedX_add, mul_assoc,
    ← mul_assoc _ (pinnedX _ _ _ (s ^ 4)), ← hc.eq]
  group

omit [Finite K] in
theorem twoCoord_add
    (t : Fin 4) (s s' : K) :
    twoCoord t (s + s') = twoCoord t s * twoCoord t s' := by
  rw [twoCoord, twoCoord, twoCoord, stdTwo_add]
  group

theorem stdFour_mul
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (c d c' d' : K) :
    stdFour c d * stdFour c' d' = stdFour (c + c') (d + d' + c ^ 4 * c') := by
  rw [stdFour_eq_largeReeCoord, stdFour_eq_largeReeCoord, stdFour_eq_largeReeCoord]
  exact largeReeCoord_mul hK c d c' d'

theorem fourCoord_mul
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (f : Fin 4) (c d c' d' : K) :
    fourCoord f c d * fourCoord f c' d' = fourCoord f (c + c') (d + d' + c ^ 4 * c') := by
  have e : ∀ n A B : ModGL F4.tag K, n * A * n⁻¹ * (n * B * n⁻¹) = n * (A * B) * n⁻¹ :=
    fun _ _ _ => by group
  rw [fourCoord, fourCoord, fourCoord, e, stdFour_mul hK]

theorem fourCoord_eq_mul
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (f : Fin 4) (c d : K) :
    fourCoord f c d = fourCoord f c 0 * fourCoord f 0 d := by
  rw [fourCoord_mul hK, add_zero, zero_add, mul_zero, add_zero]

theorem fourCoord_zero_add
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (f : Fin 4) (d d' : K) :
    fourCoord f 0 (d + d') = fourCoord f 0 d * fourCoord f 0 d' := by
  rw [fourCoord_mul hK, add_zero, zero_pow (by norm_num), zero_mul, add_zero]

theorem fourCoord_add_zero
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (f : Fin 4) (c c' : K) :
    fourCoord f c 0 * fourCoord f c' 0 = fourCoord f (c + c') 0 * fourCoord f 0 (c ^ 4 * c') := by
  rw [fourCoord_mul hK, fourCoord_mul hK]
  congr 1 <;> ring

@[expose] def twoSet
    (t : Fin 4) : Set (Fin F4.tag.rank → ℤ) :=
  (F4.fixedRelElt (kTwo t) • ·) '' F4.fixedOrbitRoots ⟨0, by decide⟩

@[expose] def fourSet
    (f : Fin 4) : Set (Fin F4.tag.rank → ℤ) :=
  (F4.fixedRelElt (kFour f) • ·) '' F4.fixedOrbitRoots ⟨1, by decide⟩

theorem exists_twoCoord_eq
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (t : Fin 4) {g : ModGL F4.tag K}
    (hg : g ∈ largeReeBlockGroup K 1 (twoSet t)) : ∃ s : K, twoCoord t s = g := by
  rw [twoSet, largeReeBlockGroup_eq_map K 1 (fixedRelElt_mem _)] at hg
  obtain ⟨y, hy, rfl⟩ := hg
  obtain ⟨s, rfl⟩ := exists_stdTwo_eq hK hy
  exact ⟨s, rfl⟩

theorem exists_fourCoord_eq
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (f : Fin 4) {g : ModGL F4.tag K}
    (hg : g ∈ largeReeBlockGroup K 1 (fourSet f)) : ∃ c d : K, fourCoord f c d = g := by
  rw [fourSet, largeReeBlockGroup_eq_map K 1 (fixedRelElt_mem _)] at hg
  obtain ⟨y, hy, rfl⟩ := hg
  obtain ⟨c, d, rfl⟩ := exists_stdFour_eq hK hy
  exact ⟨c, d, rfl⟩

theorem fourCoord_mem_block
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (f : Fin 4) (c d : K) :
    fourCoord f c d ∈ largeReeBlockGroup K 1 (fourSet f) := by
  rw [fourSet, largeReeBlockGroup_eq_map K 1 (fixedRelElt_mem _)]
  exact ⟨stdFour c d, stdFour_mem hK c d, rfl⟩

theorem twoCoord_mem_block
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (t : Fin 4) (s : K) :
    twoCoord t s ∈ largeReeBlockGroup K 1 (twoSet t) := by
  rw [twoSet, largeReeBlockGroup_eq_map K 1 (fixedRelElt_mem _)]
  exact ⟨stdTwo s, stdTwo_mem hK s, rfl⟩

theorem torusPair_conj_twoCoord
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (u : Kˣ × Kˣ) (t : Fin 4)
    (s : K) :
    torusPair 1 u * twoCoord t s * (torusPair 1 u)⁻¹ =
      twoCoord t ((torusWeight 1 (twoRoot t 0) u : K) * s) := by
  have e : ∀ n A B : ModGL F4.tag K, n * (A * B) * n⁻¹ = n * A * n⁻¹ * (n * B * n⁻¹) :=
    fun _ _ _ => by group
  have hχ := torusWeight_eq_pow hK (char_check.1 t).1 (char_check.1 t).2 u
  rw [twoCoord_eq, twoCoord_eq, e, torusPair_conj_pinnedX 1 u (isRoot_twoRoot t 0),
    torusPair_conj_pinnedX 1 u (isRoot_twoRoot t 1), hχ, Units.val_pow_eq_pow_val, mul_pow]

theorem torusPair_conj_fourCoord
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (u : Kˣ × Kˣ) (f : Fin 4)
    (c d : K) :
    torusPair 1 u * fourCoord f c d * (torusPair 1 u)⁻¹ =
      fourCoord f ((torusWeight 1 (fourRoot f 0) u : K) * c)
        ((torusWeight 1 (fourRoot f 2) u : K) * d) := by
  have e : ∀ n A B C D : ModGL F4.tag K, n * (A * B * C * D) * n⁻¹ =
      n * A * n⁻¹ * (n * B * n⁻¹) * (n * C * n⁻¹) * (n * D * n⁻¹) := fun _ _ _ _ _ => by group
  obtain ⟨h1, h1', h3, h3', h6, h6'⟩ := char_check.2 f
  have hχ1 := torusWeight_eq_pow hK h1 h1' u
  have hχ3 := torusWeight_eq_pow hK h3 h3' u
  have hχ6 := torusWeight_eq_pow hK h6 h6' u
  have h1 : ((torusWeight 1 (fourRoot f 1) u : Kˣ) : K) * c ^ 4 =
      ((torusWeight 1 (fourRoot f 0) u : K) * c) ^ 4 := by
    rw [hχ1, Units.val_pow_eq_pow_val, mul_pow]
  have ha : ((torusWeight 1 (fourRoot f 3) u : Kˣ) : K) * d ^ 4 =
      ((torusWeight 1 (fourRoot f 2) u : K) * d) ^ 4 := by
    rw [hχ3, Units.val_pow_eq_pow_val, mul_pow]
  have hb : ((torusWeight 1 (fourRoot f 3) u : Kˣ) : K) * c ^ 6 =
      ((torusWeight 1 (fourRoot f 0) u : K) * c) ^ 6 := by
    rw [hχ6, Units.val_pow_eq_pow_val, mul_pow]
  rw [fourCoord_eq, fourCoord_eq, e, torusPair_conj_pinnedX 1 u (isRoot_fourRoot f 0),
    torusPair_conj_pinnedX 1 u (isRoot_fourRoot f 1),
    torusPair_conj_pinnedX 1 u (isRoot_fourRoot f 2),
    torusPair_conj_pinnedX 1 u (isRoot_fourRoot f 3), h1, mul_add, ha, hb]

end CFSG.LieType.Ree.LargeReeCover
