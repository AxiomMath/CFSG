module

public import CFSG.LieType.Steinberg.CentralExt.SpinSevenThree
public import CFSG.LieType.Steinberg.CentralExt.LiftRelations

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg.CentralExt.SpinOddClosed
open scoped commutatorElement

variable {K : Type} [Field K] {E : Type*} [Group E] {π : E →* spinGroup (quadOdd 3 K)}

@[expose] def baseLong : Fin 3 → ℤ := ofStdB 3 (Pi.single 0 1 + Pi.single 1 1)

@[expose] def baseShort : Fin 3 → ℤ := ofStdB 3 (Pi.single 2 1)

theorem isOrthPair_base : IsOrthPair baseLong baseShort :=
  ⟨0, 1, 2, true, true, true, by decide, by decide, by decide,
    by rw [baseLong, toStdB_ofStdB]; rfl, by rw [baseShort, toStdB_ofStdB]; rfl⟩

@[expose] noncomputable def cOrth (π : E →* spinGroup (quadOdd 3 K)) : E :=
  ⁅X π baseLong 1, X π baseShort 1⁆

theorem cartanB_three_diag (k : Fin 3) : cartanB 3 k k = 2 := by
  fin_cases k <;> decide

theorem reflection_cartanB_invol (k : Fin 3) (γ : Fin 3 → ℤ) :
    reflection (cartanB 3) k (reflection (cartanB 3) k γ) = γ := by
  have h := reflection_mul_self (A := cartanB 3) (i := k) (cartanB_three_diag k)
  have := congrArg (fun f => f γ) h
  simpa using this

section RootElts

open CFSG.LieType.Steinberg.SpinOdd (IsRootVec IsShort isShort_single elt elt_of_isLong
  elt_of_isShort shortElt_eq)

theorem x_long_eq {γ : Fin 3 → ℤ} {i j : Fin 3} (hij : i ≠ j) {s t : Bool}
    (he : toStdB 3 γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) (a : K) :
    SpinOdd.x 3 K γ a = (oddFrame 3 K).toHypFrame.longRoot hij s t
      (.ofAdd ((repSign i j s t : K) * a)) := by
  simp only [SpinOdd.x]
  rw [he, elt_of_isLong _ (isLong_single_add_single hij s t), rootElt_eq _ hij rfl]

theorem x_short_eq {γ : Fin 3 → ℤ} {k : Fin 3} {u : Bool}
    (he : toStdB 3 γ = Pi.single k (boolSign u)) (a : K) :
    SpinOdd.x 3 K γ a = (oddFrame 3 K).shortRoot k u (.ofAdd ((boolSign u : K) * a)) := by
  simp only [SpinOdd.x]
  rw [he, elt_of_isShort _ (isShort_single k u), shortElt_eq _ rfl]

@[expose] def rootX1 : Fin 3 → ℤ := ofStdB 3 (Pi.single 0 (boolSign true) + Pi.single 2 (boolSign false))

@[expose] def rootY1 : Fin 3 → ℤ := ofStdB 3 (Pi.single 1 (boolSign true))

@[expose] def rootX2 : Fin 3 → ℤ := ofStdB 3 (Pi.single 1 (boolSign true) + Pi.single 2 (boolSign true))

@[expose] def rootY2 : Fin 3 → ℤ := ofStdB 3 (Pi.single 0 (boolSign true))

theorem std_baseLong : toStdB 3 baseLong = Pi.single 0 (boolSign true) + Pi.single 1 (boolSign true) := by
  rw [baseLong, toStdB_ofStdB]; rfl

theorem std_baseShort : toStdB 3 baseShort = Pi.single 2 (boolSign true) := by
  rw [baseShort, toStdB_ofStdB]; rfl

theorem std_rootX1 : toStdB 3 rootX1 = Pi.single 0 (boolSign true) + Pi.single 2 (boolSign false) := by
  rw [rootX1, toStdB_ofStdB]

theorem std_rootY1 : toStdB 3 rootY1 = Pi.single 1 (boolSign true) := by
  rw [rootY1, toStdB_ofStdB]

theorem std_rootX2 : toStdB 3 rootX2 = Pi.single 1 (boolSign true) + Pi.single 2 (boolSign true) := by
  rw [rootX2, toStdB_ofStdB]

theorem std_rootY2 : toStdB 3 rootY2 = Pi.single 0 (boolSign true) := by
  rw [rootY2, toStdB_ofStdB]

theorem mem_roots_baseLong : baseLong ∈ roots (isFiniteType_cartanB 3) ∅ :=
  (mem_roots_of_isOrthPair isOrthPair_base).1

theorem mem_roots_baseShort : baseShort ∈ roots (isFiniteType_cartanB 3) ∅ :=
  (mem_roots_of_isOrthPair isOrthPair_base).2

theorem mem_roots_rootX1 : rootX1 ∈ roots (isFiniteType_cartanB 3) ∅ :=
  SpinOdd.mem_roots_iff.2 (Or.inl ⟨0, 2, by decide, true, false, std_rootX1⟩)

theorem mem_roots_rootY1 : rootY1 ∈ roots (isFiniteType_cartanB 3) ∅ :=
  SpinOdd.mem_roots_iff.2 (Or.inr ⟨1, true, std_rootY1⟩)

theorem mem_roots_rootX2 : rootX2 ∈ roots (isFiniteType_cartanB 3) ∅ :=
  SpinOdd.mem_roots_iff.2 (Or.inl ⟨1, 2, by decide, true, true, std_rootX2⟩)

theorem mem_roots_rootY2 : rootY2 ∈ roots (isFiniteType_cartanB 3) ∅ :=
  SpinOdd.mem_roots_iff.2 (Or.inr ⟨0, true, std_rootY2⟩)

theorem isOrthPair_X1Y1 : IsOrthPair rootX1 rootY1 :=
  ⟨0, 2, 1, true, false, true, by decide, by decide, by decide, std_rootX1, std_rootY1⟩

theorem isOrthPair_X2Y2 : IsOrthPair rootX2 rootY2 :=
  ⟨1, 2, 0, true, true, true, by decide, by decide, by decide, std_rootX2, std_rootY2⟩

theorem commute_x_base_X1 (a b : K) :
    SpinOdd.x 3 K baseLong a * SpinOdd.x 3 K rootX1 b =
      SpinOdd.x 3 K rootX1 b * SpinOdd.x 3 K baseLong a := by
  rw [x_long_eq (by decide : (0 : Fin 3) ≠ 1) std_baseLong,
    x_long_eq (by decide : (0 : Fin 3) ≠ 2) std_rootX1]
  exact ((oddFrame 3 K).toHypFrame.commute_longRoot_longRoot_left (by decide : (0 : Fin 3) ≠ 1)
    (by decide : (0 : Fin 3) ≠ 2) true true false _ _).eq

theorem commute_x_base_Y1 (a b : K) :
    SpinOdd.x 3 K baseLong a * SpinOdd.x 3 K rootY1 b =
      SpinOdd.x 3 K rootY1 b * SpinOdd.x 3 K baseLong a := by
  rw [x_long_eq (by decide : (0 : Fin 3) ≠ 1) std_baseLong, x_short_eq std_rootY1]
  exact ((oddFrame 3 K).commute_longRoot_shortRoot_right (by decide : (0 : Fin 3) ≠ 1) true true
    _ _).eq

theorem commute_x_base_Y2 (a b : K) :
    SpinOdd.x 3 K baseLong a * SpinOdd.x 3 K rootY2 b =
      SpinOdd.x 3 K rootY2 b * SpinOdd.x 3 K baseLong a := by
  rw [x_long_eq (by decide : (0 : Fin 3) ≠ 1) std_baseLong, x_short_eq std_rootY2]
  exact ((oddFrame 3 K).commute_longRoot_shortRoot_left (by decide : (0 : Fin 3) ≠ 1) true true
    _ _).eq

theorem commute_x_X1_Y2 (a b : K) :
    SpinOdd.x 3 K rootX1 a * SpinOdd.x 3 K rootY2 b =
      SpinOdd.x 3 K rootY2 b * SpinOdd.x 3 K rootX1 a := by
  rw [x_long_eq (by decide : (0 : Fin 3) ≠ 2) std_rootX1, x_short_eq std_rootY2]
  exact ((oddFrame 3 K).commute_longRoot_shortRoot_left (by decide : (0 : Fin 3) ≠ 2) true false
    _ _).eq

theorem commute_x_X2_Y1 (a b : K) :
    SpinOdd.x 3 K rootX2 a * SpinOdd.x 3 K rootY1 b =
      SpinOdd.x 3 K rootY1 b * SpinOdd.x 3 K rootX2 a := by
  rw [x_long_eq (by decide : (1 : Fin 3) ≠ 2) std_rootX2, x_short_eq std_rootY1]
  exact ((oddFrame 3 K).commute_longRoot_shortRoot_left (by decide : (1 : Fin 3) ≠ 2) true true
    _ _).eq

theorem commute_x_base_X2 (a b : K) :
    SpinOdd.x 3 K baseLong a * SpinOdd.x 3 K rootX2 b =
      SpinOdd.x 3 K rootX2 b * SpinOdd.x 3 K baseLong a := by
  rw [x_long_eq (by decide : (0 : Fin 3) ≠ 1) std_baseLong,
    x_long_eq (by decide : (1 : Fin 3) ≠ 2) std_rootX2,
    (oddFrame 3 K).toHypFrame.longRoot_swap (by decide : (1 : Fin 3) ≠ 2)]
  exact ((oddFrame 3 K).toHypFrame.commute_longRoot_longRoot_right (by decide : (0 : Fin 3) ≠ 1)
    (by decide : (2 : Fin 3) ≠ 1) true true true _ _).eq

theorem commutator_x_X1_X2 :
    ∃ C : K, ∀ u v : K, ⁅SpinOdd.x 3 K rootX1 u, SpinOdd.x 3 K rootX2 v⁆ =
      SpinOdd.x 3 K baseLong (C * u * v) := by
  have h3 : (repSign (0 : Fin 3) 1 true true : K) * (repSign (0 : Fin 3) 1 true true : K) = 1 :=
    repSign_cast_mul_self _ _ _ _
  refine ⟨-((repSign (0 : Fin 3) 2 true false : K) * (repSign (1 : Fin 3) 2 true true : K) *
    (repSign (0 : Fin 3) 1 true true : K)), fun u v => ?_⟩
  rw [x_long_eq (by decide : (0 : Fin 3) ≠ 2) std_rootX1,
    x_long_eq (by decide : (1 : Fin 3) ≠ 2) std_rootX2,
    (oddFrame 3 K).toHypFrame.longRoot_swap (by decide : (1 : Fin 3) ≠ 2),
    x_long_eq (by decide : (0 : Fin 3) ≠ 1) std_baseLong]
  have := (oddFrame 3 K).toHypFrame.commutator_longRoot_longRoot (by decide : (0 : Fin 3) ≠ 2)
    (by decide : (2 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 1) true false true
    ((repSign (0 : Fin 3) 2 true false : K) * u) (-((repSign (1 : Fin 3) 2 true true : K) * v))
  rw [show (!false) = true from rfl] at this
  rw [this]
  congr 2
  linear_combination (((repSign (0 : Fin 3) 2 true false : K) *
    (repSign (1 : Fin 3) 2 true true : K) * u * v)) * h3

theorem commutator_x_Y1_Y2 :
    ∃ C : K, ∀ u v : K, ⁅SpinOdd.x 3 K rootY1 u, SpinOdd.x 3 K rootY2 v⁆ =
      SpinOdd.x 3 K baseLong (C * u * v) := by
  have h3 : (repSign (0 : Fin 3) 1 true true : K) * (repSign (0 : Fin 3) 1 true true : K) = 1 :=
    repSign_cast_mul_self _ _ _ _
  refine ⟨2 * (repSign (0 : Fin 3) 1 true true : K), fun u v => ?_⟩
  rw [x_short_eq std_rootY1, x_short_eq std_rootY2,
    x_long_eq (by decide : (0 : Fin 3) ≠ 1) std_baseLong]
  rw [(oddFrame 3 K).commutator_shortRoot_shortRoot (by decide : (1 : Fin 3) ≠ 0) true true,
    (oddFrame 3 K).toHypFrame.longRoot_swap (by decide : (1 : Fin 3) ≠ 0)]
  congr 2
  simp only [boolSign, ite_true, Int.cast_one, one_mul]
  linear_combination (-(2 * u * v)) * h3

end RootElts

section Torus

theorem chi_parity {i j : Fin 3} (hij : i ≠ j) (e : Fin 3 → ℤ) :
    chi (.long i j hij true true (-1) : TorIdx 3 K) e =
      (((-1 : Kˣ) ^ (toStdB 3 e i + toStdB 3 e j) : Kˣ) : K) := by
  rw [chi_long_neg_one, dotProduct_comm,
    CFSG.LieType.Steinberg.CentralExt.SpinTorus.single_add_single_dotProduct, one_mul, one_mul]

theorem chi_parity_even {i j : Fin 3} (hij : i ≠ j) {e : Fin 3 → ℤ}
    (h : Even (toStdB 3 e i + toStdB 3 e j)) :
    chi (.long i j hij true true (-1) : TorIdx 3 K) e = 1 := by
  have h1 : ((-1 : Kˣ) ^ (toStdB 3 e i + toStdB 3 e j) : Kˣ) = 1 := h.neg_one_zpow
  rw [chi_parity hij, h1, Units.val_one]

theorem chi_parity_odd {i j : Fin 3} (hij : i ≠ j) {e : Fin 3 → ℤ}
    (h : Odd (toStdB 3 e i + toStdB 3 e j)) :
    chi (.long i j hij true true (-1) : TorIdx 3 K) e = -1 := by
  have h1 : ((-1 : Kˣ) ^ (toStdB 3 e i + toStdB 3 e j) : Kˣ) = -1 := h.neg_one_zpow
  rw [chi_parity hij, h1, Units.val_neg, Units.val_one]

end Torus

theorem parity_base_02 : Odd (toStdB 3 baseLong 0 + toStdB 3 baseLong 2) := by
  rw [std_baseLong]; decide
theorem parity_X1_02 : Even (toStdB 3 rootX1 0 + toStdB 3 rootX1 2) := by
  rw [std_rootX1]; decide
theorem parity_Y1_02 : Even (toStdB 3 rootY1 0 + toStdB 3 rootY1 2) := by
  rw [std_rootY1]; decide
theorem parity_X2_02 : Odd (toStdB 3 rootX2 0 + toStdB 3 rootX2 2) := by
  rw [std_rootX2]; decide
theorem parity_Y2_02 : Odd (toStdB 3 rootY2 0 + toStdB 3 rootY2 2) := by
  rw [std_rootY2]; decide
theorem parity_base_01 : Even (toStdB 3 baseLong 0 + toStdB 3 baseLong 1) := by
  rw [std_baseLong]; decide
theorem parity_X2_01 : Odd (toStdB 3 rootX2 0 + toStdB 3 rootX2 1) := by
  rw [std_rootX2]; decide
theorem parity_base_12 : Odd (toStdB 3 baseLong 1 + toStdB 3 baseLong 2) := by
  rw [std_baseLong]; decide
theorem parity_Y2_12 : Even (toStdB 3 rootY2 1 + toStdB 3 rootY2 2) := by
  rw [std_rootY2]; decide
theorem parity_X1_12 : Odd (toStdB 3 rootX1 1 + toStdB 3 rootX1 2) := by
  rw [std_rootX1]; decide

section Chi

variable {K : Type} [Field K]

theorem two_ne_zero_K (hK : Nat.card K = 3) [Finite K] : (2 : K) ≠ 0 :=
  CFSG.LieType.Steinberg.CentralExt.FieldThree.two_ne_zero_of_card_three hK

theorem neg_one_ne_one_K (hK : Nat.card K = 3) [Finite K] : (-1 : K) ≠ 1 :=
  neg_one_ne_one_of_two (two_ne_zero_K hK)

@[expose] def torP02 (K : Type) [Field K] : TorIdx 3 K := .long 0 2 (by decide) true true (-1)

@[expose] def torP01 (K : Type) [Field K] : TorIdx 3 K := .long 0 1 (by decide) true true (-1)

@[expose] def torP12 (K : Type) [Field K] : TorIdx 3 K := .long 1 2 (by decide) true true (-1)

theorem chi_P02_X1 : chi (torP02 K) rootX1 = 1 := chi_parity_even _ parity_X1_02
theorem chi_P02_Y1 : chi (torP02 K) rootY1 = 1 := chi_parity_even _ parity_Y1_02
theorem chi_P02_base : chi (torP02 K) baseLong = -1 := chi_parity_odd _ parity_base_02
theorem chi_P02_X2 : chi (torP02 K) rootX2 = -1 := chi_parity_odd _ parity_X2_02
theorem chi_P02_Y2 : chi (torP02 K) rootY2 = -1 := chi_parity_odd _ parity_Y2_02
theorem chi_P01_base : chi (torP01 K) baseLong = 1 := chi_parity_even _ parity_base_01
theorem chi_P01_X2 : chi (torP01 K) rootX2 = -1 := chi_parity_odd _ parity_X2_01
theorem chi_P12_base : chi (torP12 K) baseLong = -1 := chi_parity_odd _ parity_base_12
theorem chi_P12_Y2 : chi (torP12 K) rootY2 = 1 := chi_parity_even _ parity_Y2_12
theorem chi_P12_X1 : chi (torP12 K) rootX1 = -1 := chi_parity_odd _ parity_X1_12

end Chi

section CommLemma

variable {E : Type*} [Group E]

theorem conj_eq_of_comm_eq {x y z : E} (hz : z ∈ Subgroup.center E) (h : ⁅x, y⁆ = z) :
    y⁻¹ * x * y = x * z := by
  have h1 : x * y = z * (y * x) := by
    have := h
    rw [commutatorElement_def] at this
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = z * (y * x) := by rw [this]
  calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
    _ = y⁻¹ * (z * (y * x)) := by rw [h1]
    _ = (y⁻¹ * z) * (y * x) := by rw [mul_assoc]
    _ = (z * y⁻¹) * (y * x) := by rw [Subgroup.mem_center_iff.1 hz y⁻¹]
    _ = z * x := by group
    _ = x * z := (Subgroup.mem_center_iff.1 hz x).symm

end CommLemma

section Lifts

variable [Finite K] (hK : Nat.card K = 3) (hπ : Function.Surjective π)
  (hcen : π.ker ≤ Subgroup.center E)
include hK hπ hcen

theorem spec_X : ∀ γ ∈ roots (isFiniteType_cartanB 3) ∅, IsRootLift π γ (X π γ) :=
  fun _ hγ => isRootLift_X_three hK le_rfl hπ hcen hγ

theorem orth_comm_mem_ker {γ δ : Fin 3 → ℤ} (h : IsOrthPair γ δ) (a b : K) :
    ⁅X π γ a, X π δ b⁆ ∈ π.ker := by
  obtain ⟨hγ, hδ⟩ := mem_roots_of_isOrthPair h
  rw [MonoidHom.mem_ker, map_commutatorElement, (spec_X hK hπ hcen γ hγ).2.1,
    (spec_X hK hπ hcen δ hδ).2.1, commutatorElement_eq_one_iff_mul_comm]
  exact commute_x_of_isOrthPair h a b

theorem cOrth_pow_three : cOrth π ^ 3 = 1 := by
  obtain ⟨hγ, hδ⟩ := mem_roots_of_isOrthPair isOrthPair_base
  exact (commutator_mem_zpowers_of_add hK (spec_X hK hπ hcen _ hγ).1 (spec_X hK hπ hcen _ hδ).1
    fun s t => hcen (orth_comm_mem_ker hK hπ hcen isOrthPair_base s t)).1

theorem cOrth_mem_ker : cOrth π ∈ π.ker := orth_comm_mem_ker hK hπ hcen isOrthPair_base 1 1

theorem cOrth_mem_center : cOrth π ∈ Subgroup.center E := hcen (cOrth_mem_ker hK hπ hcen)

theorem orth_comm_mem_zpowers {γ δ : Fin 3 → ℤ} (h : IsOrthPair γ δ) (a b : K) :
    ⁅X π γ a, X π δ b⁆ ∈ Subgroup.zpowers (cOrth π) := by
  have hspec := spec_X hK hπ hcen
  obtain ⟨hγ₀r, hδ₀r⟩ := mem_roots_of_isOrthPair isOrthPair_base
  have hc := (commutator_mem_zpowers_of_add hK (hspec _ hγ₀r).1 (hspec _ hδ₀r).1
    fun s t => hcen (orth_comm_mem_ker hK hπ hcen isOrthPair_base s t)).2
  set Z := Subgroup.zpowers (cOrth π) with hZdef
  have hZc : Z ≤ Subgroup.center E :=
    Subgroup.zpowers_le.2 (cOrth_mem_center hK hπ hcen)
  exact (isOrthPair_induction (P := fun γ δ => γ ∈ roots (isFiniteType_cartanB 3) ∅ ∧
        δ ∈ roots (isFiniteType_cartanB 3) ∅ ∧ ∀ a b, ⁅X π γ a, X π δ b⁆ ∈ Z)
      ⟨hγ₀r, hδ₀r, hc⟩
      (fun k γ δ ⟨hγ, hδ, h⟩ => ⟨(SpinOdd.Φ 3 K).refl_mem k γ hγ, (SpinOdd.Φ 3 K).refl_mem k δ hδ,
        commutator_mem_of_reflection hπ hcen (fun γ hγ => (hspec γ hγ).2.1) hZc k hγ hδ h⟩)
      h).2.2 a b

theorem cOrth_eq_one_of_comm {γ δ : Fin 3 → ℤ} (h : IsOrthPair γ δ)
    (hc : ∀ a b, ⁅X π γ a, X π δ b⁆ = 1) : cOrth π = 1 := by
  have hspec := spec_X hK hπ hcen
  have hbot : (⊥ : Subgroup E) ≤ Subgroup.center E := bot_le
  have key := isOrthPair_induction (P := fun γ δ => γ ∈ roots (isFiniteType_cartanB 3) ∅ ∧
        δ ∈ roots (isFiniteType_cartanB 3) ∅ ∧
        ((∀ a b, ⁅X π γ a, X π δ b⁆ = 1) ↔
          ∀ a b, ⁅X π baseLong a, X π baseShort b⁆ = 1))
    (γ := γ) (δ := δ)
    (by
      obtain ⟨h1, h2⟩ := mem_roots_of_isOrthPair isOrthPair_base
      exact ⟨h1, h2, Iff.rfl⟩)
    (fun k γ δ ⟨hγ, hδ, hiff⟩ => by
      have hrγ : reflection (cartanB 3) k γ ∈ roots (isFiniteType_cartanB 3) ∅ :=
        (SpinOdd.Φ 3 K).refl_mem k γ hγ
      have hrδ : reflection (cartanB 3) k δ ∈ roots (isFiniteType_cartanB 3) ∅ :=
        (SpinOdd.Φ 3 K).refl_mem k δ hδ
      refine ⟨hrγ, hrδ, ?_⟩
      have hfwd : (∀ a b, ⁅X π γ a, X π δ b⁆ = 1) →
          ∀ a b, ⁅X π (reflection (cartanB 3) k γ) a, X π (reflection (cartanB 3) k δ) b⁆ = 1 :=
        fun hh a b => by
          have := commutator_mem_of_reflection hπ hcen (fun γ hγ => (hspec γ hγ).2.1) hbot k hγ hδ
            (fun a b => by rw [hh a b]; exact Subgroup.one_mem _) a b
          simpa using this
      have hbwd : (∀ a b, ⁅X π (reflection (cartanB 3) k γ) a,
          X π (reflection (cartanB 3) k δ) b⁆ = 1) → ∀ a b, ⁅X π γ a, X π δ b⁆ = 1 :=
        fun hh a b => by
          have := commutator_mem_of_reflection hπ hcen (fun γ hγ => (hspec γ hγ).2.1) hbot k hrγ
            hrδ (fun a b => by rw [hh a b]; exact Subgroup.one_mem _) a b
          rw [reflection_cartanB_invol, reflection_cartanB_invol] at this
          simpa using this
      exact ⟨fun hh => hiff.1 (hbwd hh), fun hh => hfwd (hiff.2 hh)⟩)
    h
  have hbase := key.2.2.1 hc
  have := hbase 1 1
  exact this

theorem cOrth_ne_one [Group.IsPerfect E] (hker : π.ker ≠ ⊥) : cOrth π ≠ 1 := by
  intro h1
  apply hker
  have horth : ∀ γ δ, IsOrthPair γ δ → ∀ a b, X π γ a * X π δ b = X π δ b * X π γ a :=
    fun γ δ h a b => by
      have := orth_comm_mem_zpowers hK hπ hcen h a b
      rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at this
      exact this
  obtain ⟨σ, hσ⟩ := exists_section_of_orth hK le_rfl hπ hcen (spec_X hK hπ hcen) horth
  exact CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section π hcen σ hσ

theorem orth_comm_ne_one [Group.IsPerfect E] (hker : π.ker ≠ ⊥) {γ δ : Fin 3 → ℤ}
    (h : IsOrthPair γ δ) : ⁅X π γ 1, X π δ 1⁆ ≠ 1 := by
  intro h1
  obtain ⟨hγ, hδ⟩ := mem_roots_of_isOrthPair h
  have hspec := spec_X hK hπ hcen
  have hall : ∀ a b, ⁅X π γ a, X π δ b⁆ = 1 := fun a b => by
    have := (commutator_mem_zpowers_of_add hK (hspec γ hγ).1 (hspec δ hδ).1
      fun s t => hcen (orth_comm_mem_ker hK hπ hcen h s t)).2 a b
    rwa [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
  exact cOrth_ne_one hK hπ hcen hker (cOrth_eq_one_of_comm hK hπ hcen h hall)


theorem commute_lifts_of_sep {γ δ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB 3) ∅)
    (hδ : δ ∈ roots (isFiniteType_cartanB 3) ∅)
    (hxy : ∀ a b, SpinOdd.x 3 K γ a * SpinOdd.x 3 K δ b = SpinOdd.x 3 K δ b * SpinOdd.x 3 K γ a)
    {p : TorIdx 3 K} (hpγ : chi p γ = 1) (hpδ : chi p δ ≠ 1) (a b : K) :
    X π γ a * X π δ b = X π δ b * X π γ a := by
  have hspec := spec_X hK hπ hcen
  have he : π (CFSG.LieType.Steinberg.CentralExt.TorusLift.lift hπ (tor K p)) = tor K p := CFSG.LieType.Steinberg.CentralExt.TorusLift.map_lift hπ _
  have key := CFSG.LieType.Steinberg.CentralExt.LiftRel.commute_of_rev_sep_elem hcen
    (x := fun s => SpinOdd.x 3 K δ s) (hspec δ hδ).1 (hspec δ hδ).2.1
    (z := X π γ a) (e := CFSG.LieType.Steinberg.CentralExt.TorusLift.lift hπ (tor K p)) (a := chi p δ)
    (fun s => by rw [(hspec γ hγ).2.1]; exact (hxy a s).symm) hpδ
    (fun s => (hspec δ hδ).2.2 p _ he s)
    (by rw [(hspec γ hγ).2.2 p _ he a, hpγ, one_mul]) b
  exact key.symm

theorem lcomm_base_X1 (a b : K) :
    X π baseLong a * X π rootX1 b = X π rootX1 b * X π baseLong a :=
  (commute_lifts_of_sep hK hπ hcen mem_roots_rootX1 mem_roots_baseLong
    (fun a b => (commute_x_base_X1 b a).symm) (p := torP02 K)
    chi_P02_X1
    (by rw [chi_P02_base]; exact neg_one_ne_one_K hK) b a).symm

theorem lcomm_base_Y1 (a b : K) :
    X π baseLong a * X π rootY1 b = X π rootY1 b * X π baseLong a :=
  (commute_lifts_of_sep hK hπ hcen mem_roots_rootY1 mem_roots_baseLong
    (fun a b => (commute_x_base_Y1 b a).symm) (p := torP02 K)
    chi_P02_Y1
    (by rw [chi_P02_base]; exact neg_one_ne_one_K hK) b a).symm

theorem lcomm_base_X2 (a b : K) :
    X π baseLong a * X π rootX2 b = X π rootX2 b * X π baseLong a :=
  commute_lifts_of_sep hK hπ hcen mem_roots_baseLong mem_roots_rootX2
    (fun a b => commute_x_base_X2 a b) (p := torP01 K)
    chi_P01_base
    (by rw [chi_P01_X2]; exact neg_one_ne_one_K hK) a b

theorem lcomm_base_Y2 (a b : K) :
    X π baseLong a * X π rootY2 b = X π rootY2 b * X π baseLong a :=
  (commute_lifts_of_sep hK hπ hcen mem_roots_rootY2 mem_roots_baseLong
    (fun a b => (commute_x_base_Y2 b a).symm) (p := torP12 K)
    chi_P12_Y2
    (by rw [chi_P12_base]; exact neg_one_ne_one_K hK) b a).symm

theorem lcomm_X1_Y2 (a b : K) :
    X π rootX1 a * X π rootY2 b = X π rootY2 b * X π rootX1 a :=
  (commute_lifts_of_sep hK hπ hcen mem_roots_rootY2 mem_roots_rootX1
    (fun a b => (commute_x_X1_Y2 b a).symm) (p := torP12 K)
    chi_P12_Y2
    (by rw [chi_P12_X1]; exact neg_one_ne_one_K hK) b a).symm

theorem lcomm_X2_Y1 (a b : K) :
    X π rootX2 a * X π rootY1 b = X π rootY1 b * X π rootX2 a :=
  (commute_lifts_of_sep hK hπ hcen mem_roots_rootY1 mem_roots_rootX2
    (fun a b => (commute_x_X2_Y1 b a).symm) (p := torP02 K)
    chi_P02_Y1
    (by rw [chi_P02_X2]; exact neg_one_ne_one_K hK) b a).symm

theorem X_mem_zpowers {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB 3) ∅) (t : K) :
    X π γ t ∈ Subgroup.zpowers (X π γ 1) := by
  have hadd := (spec_X hK hπ hcen γ hγ).1
  have h0 : X π γ 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hneg : X π γ (-1) = (X π γ 1)⁻¹ := by
    have h := hadd 1 (-1)
    rw [add_neg_cancel, h0] at h
    exact (eq_inv_of_mul_eq_one_right h.symm)
  rcases CFSG.LieType.Steinberg.CentralExt.WeylLift.eq_zero_or_one_or_neg_one hK t with rfl | rfl | rfl
  · rw [h0]; exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers _
  · rw [hneg]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

theorem lcomm_X1_X2 :
    ∃ C : K, ∀ u v : K, ⁅X π rootX1 u, X π rootX2 v⁆ = X π baseLong (C * u * v) := by
  have hspec := spec_X hK hπ hcen
  obtain ⟨C, hC⟩ := commutator_x_X1_X2 (K := K)
  refine ⟨C, fun u v => ?_⟩
  have he : π (CFSG.LieType.Steinberg.CentralExt.TorusLift.lift hπ (tor K (torP02 K))) =
      tor K (torP02 K) := CFSG.LieType.Steinberg.CentralExt.TorusLift.map_lift hπ _
  exact CFSG.LieType.Steinberg.CentralExt.LiftRel.commutatorElement_eq_of_sep hcen
    (X := X π rootX1) (Y := X π rootX2) (Z := X π baseLong) (C := C)
    (hspec _ mem_roots_rootX2).1 (hspec _ mem_roots_baseLong).1
    (fun u v => by
      rw [map_commutatorElement, (hspec _ mem_roots_rootX1).2.1, (hspec _ mem_roots_rootX2).2.1, hC,
        (hspec _ mem_roots_baseLong).2.1])
    (fun v w => (lcomm_base_X2 hK hπ hcen w v).symm)
    (e := CFSG.LieType.Steinberg.CentralExt.TorusLift.lift hπ (tor K (torP02 K))) (b := -1)
    (neg_one_ne_one_K hK)
    (fun u => by rw [(hspec _ mem_roots_rootX1).2.2 _ _ he u, chi_P02_X1, one_mul])
    (fun v => by rw [(hspec _ mem_roots_rootX2).2.2 _ _ he v, chi_P02_X2])
    (fun w => by rw [(hspec _ mem_roots_baseLong).2.2 _ _ he w, chi_P02_base]) u v

theorem lcomm_Y1_Y2 :
    ∃ C : K, ∀ u v : K, ⁅X π rootY1 u, X π rootY2 v⁆ = X π baseLong (C * u * v) := by
  have hspec := spec_X hK hπ hcen
  obtain ⟨C, hC⟩ := commutator_x_Y1_Y2 (K := K)
  refine ⟨C, fun u v => ?_⟩
  have he : π (CFSG.LieType.Steinberg.CentralExt.TorusLift.lift hπ (tor K (torP02 K))) =
      tor K (torP02 K) := CFSG.LieType.Steinberg.CentralExt.TorusLift.map_lift hπ _
  exact CFSG.LieType.Steinberg.CentralExt.LiftRel.commutatorElement_eq_of_sep hcen
    (X := X π rootY1) (Y := X π rootY2) (Z := X π baseLong) (C := C)
    (hspec _ mem_roots_rootY2).1 (hspec _ mem_roots_baseLong).1
    (fun u v => by
      rw [map_commutatorElement, (hspec _ mem_roots_rootY1).2.1, (hspec _ mem_roots_rootY2).2.1, hC,
        (hspec _ mem_roots_baseLong).2.1])
    (fun v w => (lcomm_base_Y2 hK hπ hcen w v).symm)
    (e := CFSG.LieType.Steinberg.CentralExt.TorusLift.lift hπ (tor K (torP02 K))) (b := -1)
    (neg_one_ne_one_K hK)
    (fun u => by rw [(hspec _ mem_roots_rootY1).2.2 _ _ he u, chi_P02_Y1, one_mul])
    (fun v => by rw [(hspec _ mem_roots_rootY2).2.2 _ _ he v, chi_P02_Y2])
    (fun w => by rw [(hspec _ mem_roots_baseLong).2.2 _ _ he w, chi_P02_base]) u v

theorem X_pow_three {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB 3) ∅) (t : K) :
    X π γ t ^ 3 = 1 := by
  have hadd := (spec_X hK hπ hcen γ hγ).1
  have h0 : X π γ 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have h3 : t + t + t = 0 := by
    have := CFSG.LieType.Steinberg.CentralExt.WeylLift.three_eq_zero hK
    linear_combination t * this
  rw [pow_three, ← mul_assoc, ← hadd, ← hadd, h3, h0]

theorem X_zero {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB 3) ∅) :
    X π γ 0 = 1 := by
  have h := (spec_X hK hπ hcen γ hγ).1 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem comm_neg_param {γ δ : Fin 3 → ℤ} (h : IsOrthPair γ δ) (a : K) :
    ⁅X π γ a, X π δ (-1)⁆ = ⁅X π γ a, X π δ 1⁆⁻¹ := by
  obtain ⟨hγ, hδ⟩ := mem_roots_of_isOrthPair h
  have hadd := (spec_X hK hπ hcen δ hδ).1
  have key : ⁅X π γ a, X π δ 1 * X π δ (-1)⁆ = ⁅X π γ a, X π δ 1⁆ * ⁅X π γ a, X π δ (-1)⁆ :=
    CFSG.LieType.Steinberg.CentralExt.TorusLift.commutatorElement_mul_right_of_central
      (hcen (orth_comm_mem_ker hK hπ hcen h a (-1)))
  rw [← hadd, add_neg_cancel, X_zero hK hπ hcen hδ, commutatorElement_one_right] at key
  exact eq_inv_of_mul_eq_one_right key.symm

theorem exists_param_comm_eq [Group.IsPerfect E] (hker : π.ker ≠ ⊥) {γ δ : Fin 3 → ℤ}
    (h : IsOrthPair γ δ) : ∃ b : K, ⁅X π γ 1, X π δ b⁆ = cOrth π := by
  have hc3 := cOrth_pow_three hK hπ hcen
  have hne := orth_comm_ne_one hK hπ hcen hker h
  have hmem := orth_comm_mem_zpowers hK hπ hcen h 1 1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  set c := cOrth π with hcdef
  have hk' : ⁅X π γ 1, X π δ 1⁆ = c ^ (k % 3) := by
    rw [← hk]
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
    simp [hc3]
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · rw [h0, zpow_zero] at hk'; exact absurd hk' hne
  · refine ⟨1, ?_⟩
    rw [hk', h1, zpow_one]
  · refine ⟨-1, ?_⟩
    rw [comm_neg_param hK hπ hcen h, hk', h2]
    have : c ^ (2 : ℤ) = c⁻¹ := by
      have : c * c ^ (2 : ℤ) = 1 := by
        calc c * c ^ (2 : ℤ) = c ^ 3 := by rw [zpow_two, pow_three]
          _ = 1 := hc3
      exact eq_inv_of_mul_eq_one_right this
    rw [this, inv_inv]

theorem relHeis_data [Group.IsPerfect E] (hker : π.ker ≠ ⊥) :
    ∃ (a b z : E) (x y : Fin 2 → E), z ∈ π.ker ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧ a ^ 3 = 1 ∧
      b⁻¹ * a * b = a * z ∧
      (∀ i, x i * a = a * x i) ∧ (∀ i, y i * a = a * y i) ∧ (∀ i, x i ^ 3 = 1) ∧
      (∀ i, (y i)⁻¹ * x i * y i = x i * z) ∧
      (∀ i j, x i * x j * (x j * x i)⁻¹ ∈ Subgroup.zpowers a) ∧
      (∀ i j, i ≠ j → y i * y j * (y j * y i)⁻¹ ∈ Subgroup.zpowers a) ∧
      (∀ i j, i ≠ j → x i * y j * (y j * x i)⁻¹ ∈ Subgroup.zpowers a) := by
  have hz : cOrth π ∈ Subgroup.center E := cOrth_mem_center hK hπ hcen
  obtain ⟨b₁, hb₁⟩ := exists_param_comm_eq hK hπ hcen hker isOrthPair_X1Y1
  obtain ⟨b₂, hb₂⟩ := exists_param_comm_eq hK hπ hcen hker isOrthPair_X2Y2
  obtain ⟨C₁, hC₁⟩ := lcomm_X1_X2 hK hπ hcen
  obtain ⟨C₂, hC₂⟩ := lcomm_Y1_Y2 hK hπ hcen
  have hmem : ∀ t : K, X π baseLong t ∈ Subgroup.zpowers (X π baseLong 1) :=
    fun t => X_mem_zpowers hK hπ hcen mem_roots_baseLong t
  have hcomm_mem : ∀ g h : E, g * h = h * g → g * h * (h * g)⁻¹ ∈ Subgroup.zpowers (X π baseLong 1) :=
    fun g h hgh => by rw [hgh, mul_inv_cancel]; exact Subgroup.one_mem _
  have hbr : ∀ g h : E, g * h * (h * g)⁻¹ = ⁅g, h⁆ := fun g h => by
    rw [commutatorElement_def, mul_inv_rev]; group
  refine ⟨X π baseLong 1, X π baseShort 1, cOrth π, ![X π rootX1 1, X π rootX2 1],
    ![X π rootY1 b₁, X π rootY2 b₂], cOrth_mem_ker hK hπ hcen, cOrth_ne_one hK hπ hcen hker,
    cOrth_pow_three hK hπ hcen, X_pow_three hK hπ hcen mem_roots_baseLong 1,
    conj_eq_of_comm_eq hz rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (lcomm_base_X1 hK hπ hcen 1 1).symm
    · exact (lcomm_base_X2 hK hπ hcen 1 1).symm
  · intro i
    fin_cases i
    · exact (lcomm_base_Y1 hK hπ hcen 1 b₁).symm
    · exact (lcomm_base_Y2 hK hπ hcen 1 b₂).symm
  · intro i
    fin_cases i
    · exact X_pow_three hK hπ hcen mem_roots_rootX1 1
    · exact X_pow_three hK hπ hcen mem_roots_rootX2 1
  · intro i
    fin_cases i
    · exact conj_eq_of_comm_eq hz hb₁
    · exact conj_eq_of_comm_eq hz hb₂
  · have hsw : ∀ g h : E, g * h * (h * g)⁻¹ ∈ Subgroup.zpowers (X π baseLong 1) →
        h * g * (g * h)⁻¹ ∈ Subgroup.zpowers (X π baseLong 1) := fun g h hm => by
      have := Subgroup.inv_mem _ hm
      rwa [mul_inv_rev, inv_inv] at this
    have h01 : X π rootX1 1 * X π rootX2 1 * (X π rootX2 1 * X π rootX1 1)⁻¹ ∈
        Subgroup.zpowers (X π baseLong 1) := by rw [hbr, hC₁]; exact hmem _
    intro i j
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, mul_inv_cancel]; exact Subgroup.one_mem _
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact h01
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact hsw _ _ h01
    · simp only [Fin.mk_one, Matrix.cons_val_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · have hsw : ∀ g h : E, g * h * (h * g)⁻¹ ∈ Subgroup.zpowers (X π baseLong 1) →
        h * g * (g * h)⁻¹ ∈ Subgroup.zpowers (X π baseLong 1) := fun g h hm => by
      have := Subgroup.inv_mem _ hm
      rwa [mul_inv_rev, inv_inv] at this
    have h01 : X π rootY1 b₁ * X π rootY2 b₂ * (X π rootY2 b₂ * X π rootY1 b₁)⁻¹ ∈
        Subgroup.zpowers (X π baseLong 1) := by rw [hbr, hC₂]; exact hmem _
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact h01
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact hsw _ _ h01
    · exact absurd rfl hij
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact hcomm_mem _ _ (lcomm_X1_Y2 hK hπ hcen 1 b₂)
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact hcomm_mem _ _ (lcomm_X2_Y1 hK hπ hcen 1 b₁)
    · exact absurd rfl hij

end Lifts

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
