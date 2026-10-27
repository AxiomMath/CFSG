module

public import CFSG.LieType.Chevalley.TrialityFieldTwoRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourLift

public noncomputable section

namespace CFSG.LieType.Chevalley.TrialityFieldTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Chevalley.TrialityCover
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem conj_eq_of_pow_mem_center {G : Type*} [Group G] {g z : G} {n : ℕ} (hn : Odd n)
    (hgn : g ^ n ∈ Subgroup.center G) (hc : g * z * g⁻¹ * z⁻¹ ∈ Subgroup.center G)
    (hc2 : (g * z * g⁻¹ * z⁻¹) ^ 2 = 1) : g * z * g⁻¹ = z := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = g * z * g⁻¹ * z⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hc hc2
  have hgz : g * z * g⁻¹ = c * z := by
    rw [hcdef]
    group
  have hk : ∀ k : ℕ, g ^ k * z * (g ^ k)⁻¹ = c ^ k * z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : g * c ^ k = c ^ k * g := Subgroup.mem_center_iff.1 (pow_mem hc k) g
      calc g ^ (k + 1) * z * (g ^ (k + 1))⁻¹ = g * (g ^ k * z * (g ^ k)⁻¹) * g⁻¹ := by group
        _ = g * c ^ k * z * g⁻¹ := by rw [ih]; group
        _ = c ^ k * (g * z * g⁻¹) := by rw [hck]; group
        _ = c ^ (k + 1) * z := by rw [hgz, pow_succ]; group
  have hn' : c ^ n = 1 := by
    have h := hk n
    rw [show g ^ n * z = z * g ^ n from (Subgroup.mem_center_iff.1 hgn z).symm,
      mul_inv_cancel_right] at h
    exact mul_eq_right.1 h.symm
  obtain ⟨m, rfl⟩ := hn
  have hc1 : c = 1 := by
    rw [pow_succ, pow_mul, hc2, one_pow, one_mul] at hn'
    exact hn'
  rw [hgz, hc1, one_mul]

section Elements

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : σ ^ 3 = 1)

@[expose] def shortX
    (j : Fin 6) (hj : j = 0 ∨ j = 2 ∨ j = 3) (c : K) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  ⟨trialityOrbitProd K σ.toRingHom (trialityRoot j) c, trialityGroup_le_graphFixedRootGroup σ j
    (trialityOrbitProd_mem hj (toRingHom_pow_three σ hσ) c)⟩

@[expose] def longX
    (j : Fin 6) (hj : j = 1 ∨ j = 4 ∨ j = 5) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  ⟨pinnedX TwistTag.D4.tag K (trialityRoot j) ((1 : trialityFixedField K σ.toRingHom) : K),
    trialityGroup_le_graphFixedRootGroup σ j (pinnedX_trialityRoot_mem hj 1)⟩

@[expose] def torusX
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  ⟨trialityTorus σ p, trialityTorus_mem_graphFixedRootGroup σ hσ p⟩

omit [Finite K] in
theorem coe_shortX
    (j : Fin 6) (hj : j = 0 ∨ j = 2 ∨ j = 3) (c : K) :
    (shortX σ hσ j hj c : ModGL TwistTag.D4.tag K) =
      trialityOrbitProd K σ.toRingHom (trialityRoot j) c :=
  rfl

omit [Finite K] in
theorem coe_longX
    (j : Fin 6) (hj : j = 1 ∨ j = 4 ∨ j = 5) :
    (longX σ j hj : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K (trialityRoot j) ((1 : trialityFixedField K σ.toRingHom) : K) :=
  rfl

theorem coe_torusX
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    (torusX σ hσ p : ModGL TwistTag.D4.tag K) = trialityTorus σ p :=
  rfl

omit [Finite K] in
theorem shortX_add
    (j : Fin 6) (hj : j = 0 ∨ j = 2 ∨ j = 3) (a b : K) :
    shortX σ hσ j hj (a + b) = shortX σ hσ j hj a * shortX σ hσ j hj b :=
  Subtype.ext (by rw [coe_shortX, trialityOrbitProd_add' hj, Subgroup.coe_mul]; rfl)

omit [Finite K] in
theorem mem_trialityGroup_shortX
    (j : Fin 6) (hj : j = 0 ∨ j = 2 ∨ j = 3) (c : K) :
    (shortX σ hσ j hj c : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ j :=
  trialityOrbitProd_mem hj (toRingHom_pow_three σ hσ) c

omit [Finite K] in
theorem mem_trialityGroup_longX
    (j : Fin 6) (hj : j = 1 ∨ j = 4 ∨ j = 5) :
    (longX σ j hj : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ j :=
  pinnedX_trialityRoot_mem hj 1

theorem torusX_conj_shortX
    (j : Fin 6) (hj : j = 0 ∨ j = 2 ∨ j = 3)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) (c : K) :
    torusX σ hσ p * shortX σ hσ j hj c * (torusX σ hσ p)⁻¹ =
      shortX σ hσ j hj ((rootChar K (trialityRoot j) (torusParam σ p) : K) * c) :=
  Subtype.ext (trialityTorus_conj_orbitProd σ hσ (isRoot_trialityRoot j) p c)

theorem torusX_mul_comm
    (p p' : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    torusX σ hσ p * torusX σ hσ p' = torusX σ hσ p' * torusX σ hσ p :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_torusX, coe_torusX, ← map_mul, ← map_mul,
      mul_comm])

theorem torusX_pow
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) (n : ℕ) :
    torusX σ hσ p ^ n = torusX σ hσ (p ^ n) :=
  Subtype.ext (by rw [Subgroup.coe_pow, coe_torusX, coe_torusX, map_pow])

theorem torusX_one :
    torusX σ hσ 1 = 1 :=
  Subtype.ext (by rw [coe_torusX, map_one, Subgroup.coe_one])

include hσ in
omit [Finite K] [CharP K 2] in
theorem weights_two (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    rootChar K (trialityRoot 0) (torusParam σ p) = p.1 ^ 2 ∧
      rootChar K (trialityRoot 1) (torusParam σ p) = 1 ∧
      rootChar K (trialityRoot 2) (torusParam σ p) = p.1 ^ 2 ∧
      rootChar K (trialityRoot 3) (torusParam σ p) = (p.1 ^ 2)⁻¹ ∧
      rootChar K (trialityRoot 4) (torusParam σ p) = 1 ∧
      rootChar K (trialityRoot 5) (torusParam σ p) = 1 := by
  obtain ⟨a, b⟩ := p
  have := fixedUnits_subsingleton σ hk
  obtain rfl : b = 1 := Subsingleton.elim _ _
  exact weights_normOne σ (norm_eq_one σ hσ hk a)

theorem torusX_conj_long
    (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2)
    {l : Fin 6} (hl : l = 1 ∨ l = 4 ∨ l = 5) (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ)
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : (g : ModGL TwistTag.D4.tag K) ∈ trialityGroup σ l) :
    torusX σ hσ p * g * (torusX σ hσ p)⁻¹ = g := by
  obtain ⟨e, he⟩ := exists_pinnedX_trialityRoot_eq hl hg
  obtain ⟨-, w1, -, -, w4, w5⟩ := weights_two σ hσ hk p
  have hχ : rootChar K (trialityRoot l) (torusParam σ p) = 1 := by
    rcases hl with rfl | rfl | rfl
    · exact w1
    · exact w4
    · exact w5
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_torusX, ← he,
    trialityTorus_conj_pinnedX σ (isRoot_trialityRoot' l) p, hχ, Units.val_one, one_mul]

omit [Finite K] [CharP K 2] in
theorem card_torus (hK : Nat.card K = 8) (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2) :
    Nat.card (Kˣ × (trialityFixedField K σ.toRingHom)ˣ) = 7 := by
  have : Finite (trialityFixedField K σ.toRingHom) := Nat.finite_of_card_ne_zero (by omega)
  rw [Nat.card_prod, Nat.card_units, Nat.card_units, hK, hk]

end Elements

structure TwoCover (K : Type) [Field K] [Finite K] [CharP K 2] (E : Type*) [Group E] where
  σ : K ≃+* K
  hσ : σ ^ 3 = 1
  hq : ∀ c, σ c = c ^ 2
  hK : Nat.card K = 8
  hk : Nat.card (trialityFixedField K σ.toRingHom) = 2
  η : E →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  surj : Function.Surjective η
  central : η.ker ≤ Subgroup.center E
  sq : ∀ c, η c = 1 → c ^ 2 = 1

namespace TwoCover

variable
    {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type*} [Group E] (D : TwoCover K E)

theorem mem_center
    {z : E} (hz : D.η z = 1) : z ∈ Subgroup.center E :=
  D.central hz

theorem commute_of_map_eq_one
    {z : E} (hz : D.η z = 1) (g : E) : Commute z g :=
  ((Subgroup.mem_center_iff.1 (D.mem_center hz)) g).symm

theorem map_inv_mul_eq_one
    {y z : E} (h : D.η y = D.η z) : D.η (y⁻¹ * z) = 1 := by
  rw [map_mul, map_inv, h, inv_mul_cancel]

theorem commute_of_map_eq
    {y z g : E} (h : D.η y = D.η z) (hy : Commute y g) : Commute z g := by
  have hz : z = y * (y⁻¹ * z) := by group
  rw [hz]
  exact hy.mul_left (D.commute_of_map_eq_one (D.map_inv_mul_eq_one h) g)

theorem lift_commute_short
    (j : Fin 6) (hj : j = 0 ∨ j = 2 ∨ j = 3) (y y' : E)
    (hy : (D.η y : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ j)
    (hy' : (D.η y' : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ j) : y * y' = y' * y := by
  have hK3 : Nat.card K = 2 ^ 3 := by rw [D.hK]; norm_num
  have h0 : ∀ z z' : E, (D.η z : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ 0 →
      (D.η z' : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ 0 → z * z' = z' * z :=
    lift_commute_zero D.σ D.surj D.central D.hσ le_rfl hK3
  have hw1 := TwistTag.D4.orbitReflection_mem ⟨1, by decide⟩
  have hw0 := TwistTag.D4.orbitReflection_mem ⟨0, by decide⟩
  have hmap2 := map_conj_orbitGroup D.σ hw1 (isRoot_trialityRoot' 0)
  rw [orbitReflection_one_smul_root_zero] at hmap2
  have h2 : ∀ z z' : E, (D.η z : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ 2 →
      (D.η z' : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ 2 → z * z' = z' * z :=
    lift_commute_of_map_conj D.σ D.surj (canonicalRep_mem_graphFixedRootGroup hw1) hmap2 h0
  have hmap3 := map_conj_orbitGroup D.σ hw0 (isRoot_trialityRoot' 2)
  rw [orbitReflection_zero_smul_root_two] at hmap3
  have h3 : ∀ z z' : E, (D.η z : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ 3 →
      (D.η z' : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ 3 → z * z' = z' * z :=
    lift_commute_of_map_conj D.σ D.surj (canonicalRep_mem_graphFixedRootGroup hw0) hmap3 h2
  rcases hj with rfl | rfl | rfl
  · exact h0 y y' hy hy'
  · exact h2 y y' hy hy'
  · exact h3 y y' hy hy'

theorem long_cases
    {l : Fin 6} (hl : l = 1 ∨ l = 4 ∨ l = 5)
    {g : graphFixedRootGroup TwistTag.D4 K D.σ.toRingHom}
    (hg : (g : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ l) : g = 1 ∨ g = longX D.σ l hl := by
  obtain ⟨e, he⟩ := exists_pinnedX_trialityRoot_eq hl hg
  rcases fixedField_eq_zero_or_one D.σ D.hk e with rfl | rfl
  · left
    refine Subtype.ext ?_
    rw [← he, Subgroup.coe_one, ZeroMemClass.coe_zero, pinnedX_zero]
  · right
    exact Subtype.ext he.symm

theorem long_lift_comm
    {l : Fin 6} (hl : l = 1 ∨ l = 4 ∨ l = 5) (z z' : E)
    (hz : (D.η z : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ l)
    (hz' : (D.η z' : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ l) : z * z' = z' * z := by
  rcases D.long_cases hl hz with h | h
  · exact (D.commute_of_map_eq_one h z').eq
  rcases D.long_cases hl hz' with h' | h'
  · exact (D.commute_of_map_eq_one h' z).eq.symm
  exact (D.commute_of_map_eq (h.trans h'.symm) (Commute.refl z)).eq.symm

theorem torus_conj_long
    {l : Fin 6} (hl : l = 1 ∨ l = 4 ∨ l = 5) (g z : E)
    (p : Kˣ × (trialityFixedField K D.σ.toRingHom)ˣ) (hg : D.η g = torusX D.σ D.hσ p)
    (hz : (D.η z : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ l) : g * z * g⁻¹ = z := by
  have hc1 : D.η (g * z * g⁻¹ * z⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg,
      torusX_conj_long D.σ D.hσ D.hk hl p _ hz, mul_inv_cancel]
  have hg7 : D.η (g ^ 7) = 1 := by
    rw [map_pow, hg, torusX_pow, ← card_torus D.σ D.hK D.hk, pow_card_eq_one', torusX_one]
  exact conj_eq_of_pow_mem_center (by decide) (D.mem_center hg7) (D.mem_center hc1)
    (D.sq _ hc1)

theorem lift_commute_of_heightSeries
    (h : ℤ) (a : E)
    (hS : ∀ j : Fin 6, h ≤ height (trialityRoot j) → ∀ y : E,
      (D.η y : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ j → Commute y a)
    (y : E) (hy : (D.η y : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K h) :
    Commute y a := by
  set Z : Subgroup (ModGL TwistTag.D4.tag K) :=
    ((Subgroup.centralizer {a}).map D.η).map
      (graphFixedRootGroup TwistTag.D4 K D.σ.toRingHom).subtype with hZ
  have hle : Subgroup.closure {g | ∃ j : Fin 6, h ≤ height (trialityRoot j) ∧
      g ∈ trialityGroup D.σ j} ≤ Z := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨j, hj, hg⟩
    obtain ⟨z, hz⟩ := D.surj ⟨g, trialityGroup_le_graphFixedRootGroup D.σ j hg⟩
    have hzg : (D.η z : ModGL TwistTag.D4.tag K) = g := by rw [hz]
    refine ⟨D.η z, ⟨z, Subgroup.mem_centralizer_singleton_iff.2 ?_, rfl⟩, hzg⟩
    exact (hS j hj z (hzg ▸ hg)).eq
  have hyΓ : (D.η y : ModGL TwistTag.D4.tag K) ∈
      heightSeries TwistTag.D4.tag K h ⊓ twistedFixedGroup TwistTag.D4 K D.σ.toRingHom :=
    Subgroup.mem_inf.2 ⟨hy, graphFixedRootGroup_le _ _ _ (D.η y).2⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, hzy⟩ := hle (heightSeries_inf_le_closure D.σ h hyΓ)
  have hzy' : D.η z = D.η y := Subtype.ext hzy
  exact D.commute_of_map_eq hzy' (Subgroup.mem_centralizer_singleton_iff.1 hz)

structure ShortLift
    (j : Fin 6) (hj : j = 0 ∨ j = 2 ∨ j = 3) where
  A : K → E
  map : ∀ c, D.η (A c) = shortX D.σ D.hσ j hj c
  add : ∀ a b, A (a + b) = A a * A b
  torus : ∀ (g : E) (p : Kˣ × (trialityFixedField K D.σ.toRingHom)ˣ),
    D.η g = torusX D.σ D.hσ p → ∀ c,
      g * A c * g⁻¹ = A ((rootChar K (trialityRoot j) (torusParam D.σ p) : K) * c)
  comm : ∀ l : Fin 6, (l = 1 ∨ l = 4 ∨ l = 5) →
    (∀ (c : K) (e : trialityFixedField K D.σ.toRingHom),
      Commute (trialityOrbitProd K D.σ.toRingHom (trialityRoot j) c : ModGL TwistTag.D4.tag K)
        (pinnedX TwistTag.D4.tag K (trialityRoot l) e)) →
    ∀ g : E, (D.η g : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ l → ∀ c, g * A c = A c * g

theorem exists_shortLift
    (j : Fin 6) (hj : j = 0 ∨ j = 2 ∨ j = 3) :
    Nonempty (D.ShortLift j hj) := by
  have hker : ∀ z, D.η z = 1 → z ∈ Subgroup.center E := fun z hz => D.mem_center hz
  have h7 : 1 < Nat.card Kˣ := by rw [Nat.card_units, D.hK]; norm_num
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 h7
  obtain ⟨a₀, ha₀⟩ := exists_ne (1 : Kˣ)
  have hsq : a₀ ^ 2 ≠ 1 := sq_ne_one_of_odd (odd_card_units_of_charTwo K) ha₀
  set p₀ : Kˣ × (trialityFixedField K D.σ.toRingHom)ˣ := (a₀, 1)
  obtain ⟨w0, -, w2, w3, -, -⟩ := weights_two D.σ D.hσ D.hk p₀
  have hr₀ : (rootChar K (trialityRoot j) (torusParam D.σ p₀) : K) ≠ 1 := by
    intro h
    have h' : rootChar K (trialityRoot j) (torusParam D.σ p₀) = 1 := Units.ext h
    rcases hj with rfl | rfl | rfl
    · exact hsq (w0 ▸ h')
    · exact hsq (w2 ▸ h')
    · exact hsq (inv_eq_one.1 (w3 ▸ h'))
  obtain ⟨xl, hxl, hadd, hconj⟩ := LinearCover.exists_torus_lift D.η hker D.surj
    (x := shortX D.σ D.hσ j hj) (shortX_add D.σ D.hσ j hj)
    (fun e e' a b he he' => D.lift_commute_short j hj e e'
      (by rw [he]; exact mem_trialityGroup_shortX D.σ D.hσ j hj a)
      (by rw [he']; exact mem_trialityGroup_shortX D.σ D.hσ j hj b)) hr₀
    (torusX_conj_shortX D.σ D.hσ j hj p₀)
  refine ⟨⟨xl, hxl, hadd, fun g p hg c => ?_, fun l hl hcomm g hg c => ?_⟩⟩
  · refine hconj g _ ?_ (fun c => ?_) c
    · rw [hg]
      exact torusX_mul_comm D.σ D.hσ p p₀
    · rw [hg]
      exact torusX_conj_shortX D.σ D.hσ j hj p c
  · have h := hconj g 1 ?_ (fun c => ?_) c
    · rw [one_mul] at h
      exact (mul_inv_eq_iff_eq_mul.1 h)
    · have e := torusX_conj_long D.σ D.hσ D.hk hl p₀ (D.η g) hg
      calc D.η g * torusX D.σ D.hσ p₀ =
            torusX D.σ D.hσ p₀ * D.η g * (torusX D.σ D.hσ p₀)⁻¹ * torusX D.σ D.hσ p₀ := by
            rw [e]
        _ = torusX D.σ D.hσ p₀ * D.η g := by group
    · obtain ⟨e, he⟩ := exists_pinnedX_trialityRoot_eq hl hg
      refine Subtype.ext ?_
      rw [one_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← he, coe_shortX,
        (hcomm c e).eq.symm, mul_inv_cancel_right]

end TwoCover

end CFSG.LieType.Chevalley.TrialityFieldTwo
