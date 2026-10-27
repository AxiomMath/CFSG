module

public import CFSG.LieType.Steinberg.CentralExt.SpinTorus
public import CFSG.LieType.Steinberg.CentralExt.HalfSpaceLift
public import CFSG.LieType.Steinberg.CentralExt.SpTorus

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem
open CFSG.LieType.Steinberg.SpinOdd (IsRootVec IsShort isShort_single elt elt_of_isLong
  elt_of_isShort shortElt_eq)
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SpinOddClosed

attribute [local instance] TorusLift.centerCommGroup

section Frame

variable {n : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (F : OddFrame Q n)

theorem shortCoroot_eq (i : Fin n) (s : Bool) (m : Fin n) (r : Bool) :
    shortCoroot i s m r = 2 * (boolSign r * (Pi.single i (boolSign s) : Fin n → ℤ) m) := by
  unfold shortCoroot
  by_cases hm : m = i
  · subst hm
    cases r <;> cases s <;> simp [boolSign]
  · simp [hm]

theorem longTorus_conj_elt {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) {e : Fin n → ℤ}
    (he : IsRootVec e) (c : K) :
    F.longTorus hij s t τ * elt F e c * (F.longTorus hij s t τ)⁻¹ =
      elt F e (((τ ^ (e ⬝ᵥ (Pi.single i (boolSign s) + Pi.single j (boolSign t))) : Kˣ) : K) *
        c) := by
  rcases he with he | ⟨k, u, rfl⟩
  · rw [elt_of_isLong F he, elt_of_isLong F he]
    exact SpinFrame.longTorus_conj_rootElt F.toHypFrame hij s t τ he c
  · rw [elt_of_isShort F (isShort_single k u), elt_of_isShort F (isShort_single k u),
      shortElt_eq F rfl, shortElt_eq F rfl, F.longTorus_conj_shortRoot hij s t τ k u,
      SpinFrame.longCoroot_eq, single_dotProduct]
    congr 2
    ring

theorem shortTorus_conj_elt (i : Fin n) (s : Bool) (τ : Kˣ) {e : Fin n → ℤ} (he : IsRootVec e)
    (c : K) :
    F.shortTorus i s τ * elt F e c * (F.shortTorus i s τ)⁻¹ =
      elt F e (((τ ^ (2 * (e ⬝ᵥ Pi.single i (boolSign s))) : Kˣ) : K) * c) := by
  rcases he with ⟨k, l, hkl, u, v, rfl⟩ | ⟨k, u, rfl⟩
  · rw [elt_of_isLong F (isLong_single_add_single hkl u v),
      elt_of_isLong F (isLong_single_add_single hkl u v), rootElt_eq F.toHypFrame hkl rfl,
      rootElt_eq F.toHypFrame hkl rfl, F.shortTorus_conj_longRoot i s τ hkl u v,
      shortCoroot_eq, shortCoroot_eq, add_dotProduct, single_dotProduct, single_dotProduct]
    congr 2
    ring_nf
  · rw [elt_of_isShort F (isShort_single k u), elt_of_isShort F (isShort_single k u),
      shortElt_eq F rfl, shortElt_eq F rfl, F.shortTorus_conj_shortRoot i s τ k u,
      shortCoroot_eq, single_dotProduct]
    congr 2
    ring

end Frame

section Vectors

variable {n : ℕ}

theorem rootVec_apply_mem {e : Fin n → ℤ} (he : IsRootVec e) (m : Fin n) :
    e m = 0 ∨ e m = 1 ∨ e m = -1 := by
  rcases he with he | ⟨i, s, rfl⟩
  · exact he.apply_mem m
  · rw [Pi.single_apply]
    split_ifs
    · exact Or.inr (boolSign_eq_one_or_eq_neg_one s)
    · exact Or.inl rfl

theorem dot_self_ne_zero {e : Fin n → ℤ} (he : IsRootVec e) : e ⬝ᵥ e ≠ 0 := by
  rcases he with he | he
  · rw [SpinOdd.dot_self_of_isLong he]
    norm_num
  · rw [SpinOdd.dot_self_of_isShort he]
    norm_num

theorem abs_dot_short_le {e a : Fin n → ℤ} (he : IsRootVec e) (ha : IsShort a) : |e ⬝ᵥ a| ≤ 1 := by
  obtain ⟨i, s, rfl⟩ := ha
  rw [dotProduct_single]
  rcases boolSign_eq_one_or_eq_neg_one s with hs | hs <;> rw [hs] <;>
    rcases rootVec_apply_mem he i with h | h | h <;> rw [h] <;> norm_num

theorem abs_dot_long_le {e a : Fin n → ℤ} (he : IsRootVec e) (ha : IsLong a) : |e ⬝ᵥ a| ≤ 2 := by
  rcases he with he | he
  · exact SpinTorus.abs_dot_le_two he ha
  · rw [dotProduct_comm]
    exact (abs_dot_short_le (Or.inl ha) he).trans (by norm_num)

theorem exists_dot_sep_rootVec {e e' : Fin n → ℤ} (he : IsRootVec e) (he' : IsRootVec e')
    (h1 : e' ≠ e) (h2 : e' ≠ -e) : ∃ a, IsRootVec a ∧ e ⬝ᵥ a = 0 ∧ e' ⬝ᵥ a ≠ 0 := by
  by_cases h0 : e ⬝ᵥ e' = 0
  · exact ⟨e', he', h0, dot_self_ne_zero he'⟩
  rcases he with he | ⟨i, s, rfl⟩
  · rcases he' with he' | ⟨k, u, rfl⟩
    · obtain ⟨a, ha, h⟩ := SpinTorus.exists_dot_sep he he' h1 h2
      exact ⟨a, Or.inl ha, h⟩
    · obtain ⟨i, j, hij, s, t, rfl⟩ := he
      refine ⟨Pi.single i (boolSign s) + Pi.single j (boolSign (!t)),
        Or.inl (isLong_single_add_single hij _ _), ?_, ?_⟩
      · rw [SpinTorus.single_add_single_dotProduct, single_add_single_apply_left hij,
          single_add_single_apply_right hij, boolSign_not, mul_neg, boolSign_mul_self,
          boolSign_mul_self]
        norm_num
      · rw [dotProduct_comm, single_dotProduct] at h0
        rw [single_dotProduct]
        refine mul_ne_zero (boolSign_ne_zero u) fun h => h0 ?_
        by_cases hki : k = i
        · subst hki
          rw [single_add_single_apply_left hij] at h
          exact absurd h (boolSign_ne_zero s)
        · by_cases hkj : k = j
          · subst hkj
            rw [single_add_single_apply_right hij] at h
            exact absurd h (boolSign_ne_zero _)
          · rw [single_add_single_apply_of_ne hki hkj, mul_zero]
  · rcases he' with he' | ⟨k, u, rfl⟩
    · rw [single_dotProduct] at h0
      have hi : e' i ≠ 0 := right_ne_zero_of_mul h0
      obtain ⟨l, hil, u', v', rfl⟩ := he'.exists_eq_of_apply_ne_zero hi
      refine ⟨Pi.single l (boolSign true), Or.inr (isShort_single l true), ?_, ?_⟩
      · rw [single_dotProduct, Pi.single_eq_of_ne hil, mul_zero]
      · rw [SpinTorus.single_add_single_dotProduct, Pi.single_eq_of_ne hil, Pi.single_eq_same,
          mul_zero, zero_add, boolSign_true, mul_one]
        exact boolSign_ne_zero v'
    · exfalso
      rw [single_dotProduct] at h0
      by_cases hki : k = i
      · subst hki
        rcases boolSign_eq_one_or_eq_neg_one s with hs | hs <;>
          rcases boolSign_eq_one_or_eq_neg_one u with hu | hu
        · exact h1 (by rw [hu, hs])
        · exact h2 (by rw [hu, hs, Pi.single_neg])
        · exact h2 (by rw [hu, hs, ← Pi.single_neg, neg_neg])
        · exact h1 (by rw [hu, hs])
      · exact h0 (by rw [Pi.single_eq_of_ne (Ne.symm hki), mul_zero])

end Vectors

inductive TorIdx (n : ℕ) (K : Type) [Field K]
  | long (i j : Fin n) (ne : i ≠ j) (s t : Bool) (τ : Kˣ)
  | short (i : Fin n) (s : Bool) (τ : Kˣ)

variable {n : ℕ} {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def tor : TorIdx n K → spinGroup (quadOdd n K)
  | .long _ _ h s t τ => (oddFrame n K).longTorus h s t τ
  | .short i s τ => (oddFrame n K).shortTorus i s τ

@[expose] def chi : TorIdx n K → (Fin n → ℤ) → K
  | .long i j _ s t τ, γ =>
      ((τ ^ (toStdB n γ ⬝ᵥ (Pi.single i (boolSign s) + Pi.single j (boolSign t))) : Kˣ) : K)
  | .short i s τ, γ => ((τ ^ (2 * (toStdB n γ ⬝ᵥ Pi.single i (boolSign s))) : Kˣ) : K)

theorem isRootVec_of_mem {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) :
    IsRootVec (toStdB n γ) :=
  SpinOdd.mem_roots_iff.1 hγ

theorem x_add (γ : Fin n → ℤ) (s t : K) :
    SpinOdd.x n K γ (s + t) = SpinOdd.x n K γ s * SpinOdd.x n K γ t :=
  SpinOdd.elt_add _ _ s t

theorem tor_conj_x (p : TorIdx n K) {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅)
    (c : K) : tor K p * SpinOdd.x n K γ c * (tor K p)⁻¹ = SpinOdd.x n K γ (chi p γ * c) := by
  cases p with
  | long i j h s t τ => exact longTorus_conj_elt _ h s t τ (isRootVec_of_mem hγ) c
  | short i s τ => exact shortTorus_conj_elt _ i s τ (isRootVec_of_mem hγ) c

theorem tor_comm (p p' : TorIdx n K) : tor K p' * tor K p * (tor K p')⁻¹ = tor K p := by
  have h : Commute (tor K p') (tor K p) := by
    cases p' with
    | long i j h s t τ =>
      cases p with
      | long k l h' u v σ => exact (oddFrame n K).commute_longTorus_longTorus h s t τ h' u v σ
      | short k u σ => exact (oddFrame n K).commute_longTorus_shortTorus h s t τ k u σ
    | short i s τ =>
      cases p with
      | long k l h' u v σ => exact ((oddFrame n K).commute_longTorus_shortTorus h' u v σ i s τ).symm
      | short k u σ => exact (oddFrame n K).commute_shortTorus_shortTorus i s τ k u σ
  rw [h.eq, mul_inv_cancel_right]

section Lift

variable {E : Type*} [Group E] {π : E →* spinGroup (quadOdd n K)}

variable (π) in
@[expose] def IsRootLift (γ : Fin n → ℤ) (Y : K → E) : Prop :=
  (∀ s t, Y (s + t) = Y s * Y t) ∧ (∀ s, π (Y s) = SpinOdd.x n K γ s) ∧
    ∀ (p : TorIdx n K) (e : E), π e = tor K p → ∀ s, e * Y s * e⁻¹ = Y (chi p γ * s)

variable (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)

include hcen in
theorem commPairing_eq_zero_long (hn : 3 ≤ n) {γ : Fin n → ℤ} (hγ : IsLong (toStdB n γ)) :
    TorusLift.commPairing hcen hπ (x_add (K := K) γ) = 0 := by
  obtain ⟨i, j, hij, s, t, he⟩ := hγ
  obtain ⟨m, hmi, hmj⟩ := exists_ne_and_ne hn i j
  set F := (oddFrame n K).toHypFrame
  refine AddMonoidHom.ext fun c => AddMonoidHom.ext fun d => ?_
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [TorusLift.commPairing_apply, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, toMul_zero,
    Subgroup.coe_one]
  set r : K := (repSign i j s t : K)
  set a := TorusLift.lift hπ (F.longRoot hmi.symm s true (.ofAdd (r * c)))
  set b := TorusLift.lift hπ (F.longRoot hmj (!true) t (.ofAdd 1))
  set y := TorusLift.lift hπ (SpinOdd.x n K γ d)
  have hx : ∀ c' : K, SpinOdd.x n K γ c' = F.longRoot hij s t (.ofAdd (r * c')) := fun c' =>
    SpinOdd.x_eq_long hij he c'
  have hab : π ⁅a, b⁆ = SpinOdd.x n K γ c := by
    rw [map_commutatorElement, TorusLift.map_lift, TorusLift.map_lift,
      F.commutator_longRoot_longRoot hmi.symm hmj hij s true t, mul_one, hx]
  rw [TorusLift.commutatorElement_eq_of_map_eq hcen ((TorusLift.map_lift hπ _).trans hab.symm)
    rfl, commutatorElement_eq_one_iff_mul_comm]
  refine (SpinTorus.commute_commutatorElement_of_central hcen ?_ ?_).symm
  · rw [TorusLift.map_lift, TorusLift.map_lift, hx]
    exact (F.commute_longRoot_longRoot_left hij hmi.symm s t true _ _).eq
  · rw [TorusLift.map_lift, TorusLift.map_lift, hx]
    exact (F.commute_longRoot_longRoot_right hij hmj s t (!true) _ _).eq

include hcen in
theorem commPairing_eq_zero_short [Finite K] (hn : 3 ≤ n) (hK4 : Nat.card K ≠ 4)
    {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) (hs : IsShort (toStdB n γ)) :
    TorusLift.commPairing hcen hπ (x_add (K := K) γ) = 0 := by
  obtain ⟨i, s, he⟩ := hs
  obtain ⟨j, hji, -⟩ := exists_ne_and_ne hn i i
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := K)
  refine Pairing.pairing_eq_zero_of_units p hK4 (TorusLift.commPairing_self hcen hπ (x_add γ))
    fun u hu c d => ?_
  refine TorusLift.commPairing_smul hcen hπ (x_add γ)
    (g := tor K (.long i j hji.symm s true (Units.mk0 u hu))) (fun c' => ?_) c d
  rw [tor_conj_x _ hγ]
  congr 1
  rw [chi, he, single_dotProduct, single_add_single_apply_left hji.symm, boolSign_mul_self,
    zpow_one, Units.val_mk0]

include hcen hπ in
theorem exists_isRootLift {γ : Fin n → ℤ}
    (h0 : TorusLift.commPairing hcen hπ (x_add (K := K) γ) = 0)
    (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) {p : TorIdx n K}
    (hp : chi p γ ≠ 1) : ∃ Y : K → E, IsRootLift π γ Y :=
  ⟨TorusLift.canonLift hπ (x := SpinOdd.x n K γ) (tor K p) (chi p γ),
    TorusLift.canonLift_add hcen hπ (x_add γ) h0 (tor_conj_x p hγ) hp,
    TorusLift.map_canonLift hπ (x_add γ) (tor_conj_x p hγ) hp,
    fun p' _e he s => TorusLift.conj_canonLift hcen hπ (tor_comm p p') (tor_conj_x p' hγ) he s⟩

variable (π) in
open _root_.Classical in
@[expose] noncomputable def X (γ : Fin n → ℤ) : K → E :=
  if h : ∃ Y : K → E, IsRootLift π γ Y then h.choose else fun _ => 1

theorem X_isRootLift {γ : Fin n → ℤ} (h : ∃ Y : K → E, IsRootLift π γ Y) :
    IsRootLift π γ (X π γ) := by
  classical
  rw [X, dite_eq_left h]
  exact h.choose_spec

end Lift

theorem chi_eq_one {γ : Fin n → ℤ} {a : Fin n → ℤ} (ha : IsRootVec a) (h : toStdB n γ ⬝ᵥ a = 0)
    (w : Kˣ) : ∃ p : TorIdx n K, chi p γ = 1 ∧
      ∀ δ : Fin n → ℤ, δ ∈ roots (isFiniteType_cartanB n) ∅ → toStdB n δ ⬝ᵥ a ≠ 0 →
        w ^ 2 ≠ 1 → chi p δ ≠ 1 := by
  rcases ha with ⟨i, j, hij, s, t, rfl⟩ | ⟨i, s, rfl⟩
  · refine ⟨.long i j hij s t w, ?_, fun δ hδ hd hw h' => ?_⟩
    · rw [chi, h, zpow_zero, Units.val_one]
    · rw [chi] at h'
      exact SpTorus.zpow_ne_one hw hd
        (abs_dot_long_le (isRootVec_of_mem hδ) (isLong_single_add_single hij s t))
        (Units.val_eq_one.1 h')
  · refine ⟨.short i s w, ?_, fun δ hδ hd hw h' => ?_⟩
    · rw [chi, h, mul_zero, zpow_zero, Units.val_one]
    · rw [chi] at h'
      have hle := abs_dot_short_le (isRootVec_of_mem hδ) (isShort_single i s)
      refine SpTorus.zpow_ne_one hw (mul_ne_zero two_ne_zero hd) ?_ (Units.val_eq_one.1 h')
      rw [abs_mul, abs_two]
      linarith

theorem toStdB_ne_of_linIndepPair {γ δ : Fin n → ℤ} (hli : LinIndepPair γ δ) :
    toStdB n δ ≠ toStdB n γ ∧ toStdB n δ ≠ -toStdB n γ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hδ := toStdB_injective n h
    subst hδ
    have := (hli 1 (-1) (by simp)).2
    exact absurd this (by norm_num)
  · rw [← toStdB_neg] at h
    have hδ := toStdB_injective n h
    subst hδ
    have := (hli 1 1 (by simp)).2
    exact absurd this (by norm_num)

theorem exists_chi_sq {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) (w : Kˣ) :
    ∃ p : TorIdx n K, chi p γ = ((w ^ 2 : Kˣ) : K) := by
  rcases isRootVec_of_mem hγ with ⟨i, j, hij, s, t, he⟩ | ⟨i, s, he⟩
  · refine ⟨.long i j hij s t w, ?_⟩
    rw [chi, ← he, SpinOdd.dot_self_of_isLong (he ▸ isLong_single_add_single hij s t),
      zpow_two, pow_two]
  · refine ⟨.short i s w, ?_⟩
    rw [chi, ← he, SpinOdd.dot_self_of_isShort (he ▸ isShort_single i s), mul_one, zpow_two,
      pow_two]

theorem spinOdd_exists_section_of_central [Finite K] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n)
    (hK : 5 ≤ Nat.card K) {E : Type*} [Group E] {π : E →* spinGroup (quadOdd n K)}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : spinGroup (quadOdd n K) →* E, ∀ g, π (σ g) = g := by
  obtain ⟨w, hw⟩ := SpinTorus.exists_unit_sq_ne_one (F := K) (by omega)
  have hspec : ∀ γ ∈ roots (isFiniteType_cartanB n) ∅, IsRootLift π γ (X π γ) := fun γ hγ => by
    have h0 : TorusLift.commPairing hcen hπ (x_add (K := K) γ) = 0 := by
      rcases isRootVec_of_mem hγ with h | h
      · exact commPairing_eq_zero_long hcen hπ hn h
      · exact commPairing_eq_zero_short hcen hπ hn (by omega) hγ h
    obtain ⟨p, hp⟩ := exists_chi_sq hγ w
    refine X_isRootLift (exists_isRootLift hcen hπ h0 hγ (p := p) ?_)
    rw [hp]
    exact fun h => hw (Units.val_eq_one.1 h)
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (oddDatum n K).isFiniteType
    (Dv := (oddDatum n K).divisible) rfl
  refine HalfSpaceLift.exists_section_of_lift hcen rfl
    (SpinOdd.chevalleyExtras (by omega) O SpinOdd.commC (SpinOdd.commutatorFormula O))
    (SpinOdd.presentationB h2 hn) (X := X π)
    (tor := fun p : TorIdx n K => TorusLift.lift hπ (tor K p))
    (χ := fun p γ => chi p γ) (fun γ hγ => (hspec γ hγ).1)
    (fun γ hγ => (hspec γ hγ).2.1)
    (fun p γ hγ c => (hspec γ hγ).2.2 p _ (TorusLift.map_lift hπ _) c)
    fun γ hγ δ hδ hli => ?_
  obtain ⟨hne, hne'⟩ := toStdB_ne_of_linIndepPair hli
  obtain ⟨a, ha, h0, h1⟩ :=
    exists_dot_sep_rootVec (isRootVec_of_mem hγ) (isRootVec_of_mem hδ) hne hne'
  obtain ⟨p, hp1, hp2⟩ := chi_eq_one ha h0 w
  exact ⟨p, hp1, hp2 δ hδ h1 hw⟩

end CFSG.LieType.Steinberg.CentralExt.SpinOddClosed
