module

public import CFSG.LieType.Steinberg.CentralExt.SpinTorus
public import CFSG.LieType.Steinberg.CentralExt.HalfSpaceLift
public import CFSG.LieType.Steinberg.CentralExt.SpTorus

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem CFSG.LieType.Steinberg.CentralExt.SpinTorus
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed

attribute [local instance] TorusLift.centerCommGroup

structure TorIdx (n : ℕ) (K : Type) [Field K] where
  i : Fin n
  j : Fin n
  ne : i ≠ j
  s : Bool
  t : Bool
  τ : Kˣ

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)

@[expose] def TorIdx.vec (p : TorIdx n K) : Fin n → ℤ :=
  Pi.single p.i (boolSign p.s) + Pi.single p.j (boolSign p.t)

variable (K) in
@[expose] noncomputable def tor (p : TorIdx n K) : spinGroup (quadPlus n K) :=
  (plusFrame n K hn).longTorus p.ne p.s p.t p.τ

@[expose] def chi (p : TorIdx n K) (γ : Fin n → ℤ) : K :=
  ((p.τ ^ (toStdD n γ ⬝ᵥ p.vec) : Kˣ) : K)

include hn in
theorem isLong_of_mem {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅) :
    IsLong (toStdD n γ) :=
  (SpinPlus.isLong_toStdD_iff (by omega)).2 hγ

theorem x_add (γ : Fin n → ℤ) (s t : K) :
    SpinPlus.x n K hn γ (s + t) = SpinPlus.x n K hn γ s * SpinPlus.x n K hn γ t :=
  rootElt_add _ _ s t

theorem tor_conj_x (p : TorIdx n K) {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅)
    (c : K) :
    tor K hn p * SpinPlus.x n K hn γ c * (tor K hn p)⁻¹ = SpinPlus.x n K hn γ (chi p γ * c) :=
  SpinFrame.longTorus_conj_rootElt _ p.ne p.s p.t p.τ (isLong_of_mem hn hγ) c

theorem tor_comm (p p' : TorIdx n K) : tor K hn p' * tor K hn p * (tor K hn p')⁻¹ = tor K hn p := by
  have h : Commute (tor K hn p') (tor K hn p) :=
    (plusFrame n K hn).commute_longTorus_longTorus p'.ne p'.s p'.t p'.τ p.ne p.s p.t p.τ
  rw [h.eq, mul_inv_cancel_right]

section Lift

variable {E : Type*} [Group E] {π : E →* spinGroup (quadPlus n K)}

variable (π) in
@[expose] def IsRootLift (γ : Fin n → ℤ) (Y : K → E) : Prop :=
  (∀ s t, Y (s + t) = Y s * Y t) ∧ (∀ s, π (Y s) = SpinPlus.x n K hn γ s) ∧
    ∀ (p : TorIdx n K) (e : E), π e = tor K hn p → ∀ s, e * Y s * e⁻¹ = Y (chi p γ * s)

variable (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)

include hcen in
theorem commPairing_eq_zero {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅) :
    TorusLift.commPairing hcen hπ (x_add hn (K := K) γ) = 0 := by
  obtain ⟨i, j, hij, s, t, he⟩ := isLong_of_mem hn hγ
  obtain ⟨m, hmi, hmj⟩ := exists_ne_and_ne hn i j
  set F := plusFrame n K hn
  refine AddMonoidHom.ext fun c => AddMonoidHom.ext fun d => ?_
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [TorusLift.commPairing_apply, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, toMul_zero,
    Subgroup.coe_one]
  set r : K := (repSign i j s t : K)
  set a := TorusLift.lift hπ (F.longRoot hmi.symm s true (.ofAdd (r * c)))
  set b := TorusLift.lift hπ (F.longRoot hmj (!true) t (.ofAdd 1))
  set y := TorusLift.lift hπ (SpinPlus.x n K hn γ d)
  have hx : ∀ c' : K, SpinPlus.x n K hn γ c' = F.longRoot hij s t (.ofAdd (r * c')) :=
    fun c' => rootElt_eq F hij he c'
  have hab : π ⁅a, b⁆ = SpinPlus.x n K hn γ c := by
    rw [map_commutatorElement, TorusLift.map_lift, TorusLift.map_lift,
      F.commutator_longRoot_longRoot hmi.symm hmj hij s true t, mul_one, hx]
  rw [TorusLift.commutatorElement_eq_of_map_eq hcen ((TorusLift.map_lift hπ _).trans hab.symm)
    rfl, commutatorElement_eq_one_iff_mul_comm]
  refine (commute_commutatorElement_of_central hcen ?_ ?_).symm
  · rw [TorusLift.map_lift, TorusLift.map_lift, hx]
    exact (F.commute_longRoot_longRoot_left hij hmi.symm s t true _ _).eq
  · rw [TorusLift.map_lift, TorusLift.map_lift, hx]
    exact (F.commute_longRoot_longRoot_right hij hmj s t (!true) _ _).eq

include hcen hπ in
theorem exists_isRootLift {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅)
    {p : TorIdx n K} (hp : chi p γ ≠ 1) : ∃ Y : K → E, IsRootLift hn π γ Y :=
  ⟨TorusLift.canonLift hπ (x := SpinPlus.x n K hn γ) (tor K hn p) (chi p γ),
    TorusLift.canonLift_add hcen hπ (x_add hn γ) (commPairing_eq_zero hn hcen hπ hγ)
      (tor_conj_x hn p hγ) hp,
    TorusLift.map_canonLift hπ (x_add hn γ) (tor_conj_x hn p hγ) hp,
    fun p' _e he s => TorusLift.conj_canonLift hcen hπ (tor_comm hn p p') (tor_conj_x hn p' hγ) he
      s⟩

variable (π) in
open _root_.Classical in
@[expose] noncomputable def X (γ : Fin n → ℤ) : K → E :=
  if h : ∃ Y : K → E, IsRootLift hn π γ Y then h.choose else fun _ => 1

theorem X_isRootLift {γ : Fin n → ℤ} (h : ∃ Y : K → E, IsRootLift hn π γ Y) :
    IsRootLift hn π γ (X hn π γ) := by
  classical
  rw [X, dite_eq_left h]
  exact h.choose_spec

end Lift

include hn in
theorem chi_self {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅) {i j : Fin n}
    (hij : i ≠ j) {s t : Bool} (he : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (w : Kˣ) : chi ⟨i, j, hij, s, t, w⟩ γ = ((w ^ 2 : Kˣ) : K) := by
  rw [chi, TorIdx.vec, ← he, dot_self_of_isLong (isLong_of_mem hn hγ), zpow_two, pow_two]

theorem chi_eq_one {γ : Fin n → ℤ} {p : TorIdx n K} (h : toStdD n γ ⬝ᵥ p.vec = 0) :
    chi p γ = 1 := by
  rw [chi, h, zpow_zero, Units.val_one]

include hn in
theorem chi_ne_one {δ : Fin n → ℤ} (hδ : δ ∈ roots (isFiniteType_cartanD n) ∅) {w : Kˣ}
    (hw : w ^ 2 ≠ 1) {i j : Fin n} (hij : i ≠ j) {s t : Bool}
    (h : toStdD n δ ⬝ᵥ (Pi.single i (boolSign s) + Pi.single j (boolSign t)) ≠ 0) :
    chi ⟨i, j, hij, s, t, w⟩ δ ≠ 1 := fun h' =>
  SpTorus.zpow_ne_one hw h (abs_dot_le_two (isLong_of_mem hn hδ) (isLong_single_add_single hij s t))
    (Units.val_eq_one.1 h')

theorem toStdD_ne_of_linIndepPair {γ δ : Fin n → ℤ} (hli : LinIndepPair γ δ) :
    toStdD n δ ≠ toStdD n γ ∧ toStdD n δ ≠ -toStdD n γ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hδ := toStdD_injective n h
    subst hδ
    have := (hli 1 (-1) (by simp)).2
    exact absurd this (by norm_num)
  · rw [← toStdD_neg] at h
    have hδ := toStdD_injective n h
    subst hδ
    have := (hli 1 1 (by simp)).2
    exact absurd this (by norm_num)

include hn in
theorem spinPlus_exists_section_of_central [Finite K] (hK : 4 ≤ Nat.card K) {E : Type*} [Group E]
    {π : E →* spinGroup (quadPlus n K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : spinGroup (quadPlus n K) →* E, ∀ g, π (σ g) = g := by
  obtain ⟨w, hw⟩ := exists_unit_sq_ne_one hK
  have hspec : ∀ γ ∈ roots (isFiniteType_cartanD n) ∅, IsRootLift hn π γ (X hn π γ) :=
    fun γ hγ => by
      obtain ⟨i, j, hij, s, t, he⟩ := isLong_of_mem hn hγ
      refine X_isRootLift hn (exists_isRootLift hn hcen hπ hγ (p := ⟨i, j, hij, s, t, w⟩) ?_)
      rw [chi_self hn hγ hij he]
      exact fun h => hw (Units.val_eq_one.1 h)
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (plusDatum n K hn).isFiniteType
    (Dv := (plusDatum n K hn).divisible) rfl
  refine HalfSpaceLift.exists_section_of_lift hcen rfl
    (SpinPlus.chevalleyExtras hn O SpinPlus.commC (SpinPlus.commutatorFormula hn O))
    (SpinPlus.presentationB hn) (X := X hn π)
    (tor := fun p : TorIdx n K => TorusLift.lift hπ (tor K hn p))
    (χ := fun p γ => chi p γ) (fun γ hγ => (hspec γ hγ).1)
    (fun γ hγ => (hspec γ hγ).2.1)
    (fun p γ hγ c => (hspec γ hγ).2.2 p _ (TorusLift.map_lift hπ _) c)
    fun γ hγ δ hδ hli => ?_
  obtain ⟨hne, hne'⟩ := toStdD_ne_of_linIndepPair hli
  obtain ⟨a, ⟨i, j, hij, s, t, rfl⟩, h0, h1⟩ :=
    exists_dot_sep (isLong_of_mem hn hγ) (isLong_of_mem hn hδ) hne hne'
  exact ⟨⟨i, j, hij, s, t, w⟩, chi_eq_one h0, chi_ne_one hn hδ hw hij h1⟩

end CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed
