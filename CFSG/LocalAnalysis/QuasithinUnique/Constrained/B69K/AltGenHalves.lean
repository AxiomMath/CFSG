module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.B69K

open Equiv Equiv.Perm

theorem bk_conj {m : ℕ} (g : Perm (Fin m)) (a b c : Fin m) :
    g * (swap a c * swap a b) * g⁻¹ = swap (g a) (g c) * swap (g a) (g b) := by
  rw [swap_apply_apply g a c, swap_apply_apply g a b]
  group

theorem bk_cyc_alt {m : ℕ} {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    swap a c * swap a b ∈ alternatingGroup (Fin m) :=
  (Equiv.Perm.isThreeCycle_swap_mul_swap_same hac hab hbc.symm).mem_alternatingGroup

theorem bk_cyc_fix {m : ℕ} (a b c p : Fin m) (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c) :
    (swap a c * swap a b) p = p := by
  rw [Equiv.Perm.mul_apply, swap_apply_of_ne_of_ne hpa hpb, swap_apply_of_ne_of_ne hpa hpc]

theorem bk_rot {m : ℕ} {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    swap a c * swap a b = swap b a * swap b c := by
  ext x
  simp only [Equiv.Perm.mul_apply]
  by_cases h1 : x = a
  · rw [h1]
    simp [Equiv.swap_apply_def, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  by_cases h2 : x = b
  · rw [h2]
    simp [Equiv.swap_apply_def, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  by_cases h3 : x = c
  · rw [h3]
    simp [Equiv.swap_apply_def, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  simp [Equiv.swap_apply_def, h1, h2, h3]

theorem bk_identity {m : ℕ} (u v w w' : Fin m) :
    swap u w * swap u v * (swap u w' * swap u v)⁻¹ = swap u w * swap u w' := by
  rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv, mul_assoc, ← mul_assoc (swap u v) (swap u v),
    Equiv.swap_mul_self, one_mul]

theorem bk_apply_inv {m : ℕ} (g : Perm (Fin m)) (x : Fin m) : g (g⁻¹ x) = x :=
  calc g (g⁻¹ x) = (g * g⁻¹) x := rfl
    _ = (1 : Perm (Fin m)) x := by rw [mul_inv_cancel]
    _ = x := rfl

theorem bk_inv_apply {m : ℕ} (g : Perm (Fin m)) (x : Fin m) : g⁻¹ (g x) = x :=
  calc g⁻¹ (g x) = (g⁻¹ * g) x := rfl
    _ = (1 : Perm (Fin m)) x := by rw [inv_mul_cancel]
    _ = x := rfl

theorem bk_exists_avoid {m : ℕ} (S : Set (Fin m)) (F : Finset (Fin m)) (h : F.card < S.ncard) :
    ∃ p ∈ S, p ∉ F := by
  by_contra hcon
  push Not at hcon
  have hsub : S ⊆ (F : Set (Fin m)) := fun p hp => Finset.mem_coe.mpr (hcon p hp)
  have hle : S.ncard ≤ (F : Set (Fin m)).ncard :=
    Set.ncard_le_ncard hsub (Finset.finite_toSet F)
  rw [Set.ncard_coe_finset] at hle
  omega

theorem bk_two_avoid {m : ℕ} (S : Set (Fin m)) (hS : 4 ≤ S.ncard) (a b : Fin m) :
    ∃ p ∈ S, p ≠ a ∧ p ≠ b := by
  have hc : ({a, b} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
  obtain ⟨p, hp, hpF⟩ := bk_exists_avoid S {a, b} (by omega)
  refine ⟨p, hp, ?_, ?_⟩
  · rintro rfl
    exact hpF (by simp)
  · rintro rfl
    exact hpF (by simp)

theorem bk_three_avoid {m : ℕ} (S : Set (Fin m)) (hS : 4 ≤ S.ncard) (a b c : Fin m) :
    ∃ p ∈ S, p ≠ a ∧ p ≠ b ∧ p ≠ c := by
  have hc : ({a, b, c} : Finset (Fin m)).card ≤ 3 := Finset.card_le_three
  obtain ⟨p, hp, hpF⟩ := bk_exists_avoid S {a, b, c} (by omega)
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · rintro rfl
    exact hpF (by simp)
  · rintro rfl
    exact hpF (by simp)
  · rintro rfl
    exact hpF (by simp)

theorem bk_ne_of_mem_compl {m : ℕ} {S : Set (Fin m)} {p a : Fin m} (hp : p ∈ Sᶜ) (ha : a ∈ S) :
    p ≠ a :=
  fun h => (Set.mem_compl_iff S p).mp hp (by rw [h]; exact ha)

theorem bk_ne_of_compl_mem {m : ℕ} {S : Set (Fin m)} {p a : Fin m} (hp : p ∈ S) (ha : a ∈ Sᶜ) :
    p ≠ a :=
  fun h => (Set.mem_compl_iff S a).mp ha (by rw [← h]; exact hp)

theorem bk_transport2 {m : ℕ} (H : Subgroup (Perm (Fin m))) (S T : Set (Fin m))
    (hdisj : ∀ p ∈ S, p ∉ T) (hS : 4 ≤ S.ncard)
    (hSsupp : ∀ σ : Perm (Fin m), σ ∈ alternatingGroup (Fin m) → (∀ p ∈ T, σ p = p) → σ ∈ H)
    {x y u v : Fin m} (hx : x ∈ S) (hy : y ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    (hxy : x ≠ y) (huv : u ≠ v) :
    ∃ g ∈ H, g x = u ∧ g y = v ∧ ∀ p ∈ T, g p = p := by
  obtain ⟨y', hy'⟩ : ∃ y' : Fin m, y' = swap x u y := ⟨_, rfl⟩
  have hy'S : y' ∈ S := by
    rw [hy']
    by_cases hyu : y = u
    · rw [hyu, swap_apply_right]
      exact hx
    · rw [swap_apply_of_ne_of_ne (Ne.symm hxy) hyu]
      exact hy
  have hu'y' : u ≠ y' := by
    intro h
    rw [hy'] at h
    by_cases hyu : y = u
    · rw [hyu, swap_apply_right] at h
      exact hxy (h.symm.trans hyu.symm)
    · rw [swap_apply_of_ne_of_ne (Ne.symm hxy) hyu] at h
      exact hyu h.symm
  have hτx : (swap y' v * swap x u) x = u := by
    rw [Equiv.Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hu'y' huv]
  have hτy : (swap y' v * swap x u) y = v := by
    rw [Equiv.Perm.mul_apply, ← hy', swap_apply_left]
  have hτT : ∀ p ∈ T, (swap y' v * swap x u) p = p := by
    intro p hp
    have hpS : p ∉ S := fun h => hdisj p h hp
    have hpx : p ≠ x := by
      rintro rfl
      exact hpS hx
    have hpu : p ≠ u := by
      rintro rfl
      exact hpS hu
    have hpy' : p ≠ y' := by
      rintro rfl
      exact hpS hy'S
    have hpv : p ≠ v := by
      rintro rfl
      exact hpS hv
    rw [Equiv.Perm.mul_apply, swap_apply_of_ne_of_ne hpx hpu, swap_apply_of_ne_of_ne hpy' hpv]
  obtain ⟨p₁, hp₁S, hp₁u, hp₁v⟩ := bk_two_avoid S hS u v
  obtain ⟨q₁, hq₁S, hq₁u, hq₁v, hq₁p⟩ := bk_three_avoid S hS u v p₁
  have hp₁q₁ : p₁ ≠ q₁ := Ne.symm hq₁p
  have hfix : ∀ p ∈ T, (swap p₁ q₁ * (swap y' v * swap x u)) p = p := by
    intro p hp
    have hpS : p ∉ S := fun h => hdisj p h hp
    have hpp₁ : p ≠ p₁ := by
      rintro rfl
      exact hpS hp₁S
    have hpq₁ : p ≠ q₁ := by
      rintro rfl
      exact hpS hq₁S
    rw [Equiv.Perm.mul_apply, hτT p hp, swap_apply_of_ne_of_ne hpp₁ hpq₁]
  by_cases hsgn : Equiv.Perm.sign (swap y' v * swap x u) = 1
  · exact ⟨swap y' v * swap x u,
      hSsupp _ (Equiv.Perm.mem_alternatingGroup.mpr hsgn) hτT, hτx, hτy, hτT⟩
  · have hsgn' : Equiv.Perm.sign (swap y' v * swap x u) = -1 :=
      (Int.units_eq_one_or _).resolve_left hsgn
    have hσsgn : Equiv.Perm.sign (swap p₁ q₁ * (swap y' v * swap x u)) = 1 := by
      rw [map_mul, Equiv.Perm.sign_swap hp₁q₁, hsgn']
      first
        | rfl
        | decide
        | exact Int.units_mul_self _
    refine ⟨swap p₁ q₁ * (swap y' v * swap x u),
      hSsupp _ (Equiv.Perm.mem_alternatingGroup.mpr hσsgn) hfix, ?_, ?_, hfix⟩
    · rw [Equiv.Perm.mul_apply, hτx, swap_apply_of_ne_of_ne (Ne.symm hp₁u) (Ne.symm hq₁u)]
    · rw [Equiv.Perm.mul_apply, hτy, swap_apply_of_ne_of_ne (Ne.symm hp₁v) (Ne.symm hq₁v)]

theorem bk_transport1 {m : ℕ} (H : Subgroup (Perm (Fin m))) (S T : Set (Fin m))
    (hdisj : ∀ p ∈ S, p ∉ T) (hT : 4 ≤ T.ncard)
    (hTsupp : ∀ σ : Perm (Fin m), σ ∈ alternatingGroup (Fin m) → (∀ p ∈ S, σ p = p) → σ ∈ H)
    {z w : Fin m} (hz : z ∈ T) (hw : w ∈ T) :
    ∃ g ∈ H, g z = w ∧ ∀ p ∈ S, g p = p := by
  by_cases hzw : z = w
  · exact ⟨1, H.one_mem, by simp [hzw], fun p _ => rfl⟩
  · obtain ⟨p₀, hp₀T, hp₀z, hp₀w⟩ := bk_two_avoid T hT z w
    have hwz : w ≠ z := Ne.symm hzw
    have hz'p : z ≠ p₀ := Ne.symm hp₀z
    have hw'p : w ≠ p₀ := Ne.symm hp₀w
    have hg : swap z p₀ * swap z w ∈ alternatingGroup (Fin m) := bk_cyc_alt hzw hz'p hw'p
    have hfix : ∀ p ∈ S, (swap z p₀ * swap z w) p = p := by
      intro p hp
      have hpT : p ∉ T := hdisj p hp
      have hpz : p ≠ z := by
        rintro rfl
        exact hpT hz
      have hpw : p ≠ w := by
        rintro rfl
        exact hpT hw
      have hpp₀ : p ≠ p₀ := by
        rintro rfl
        exact hpT hp₀T
      exact bk_cyc_fix z w p₀ p hpz hpw hpp₀
    have hgz : (swap z p₀ * swap z w) z = w := by
      rw [Equiv.Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hwz hw'p]
    exact ⟨swap z p₀ * swap z w, hTsupp _ hg hfix, hgz, hfix⟩

theorem bk_Q {m : ℕ} (H : Subgroup (Perm (Fin m))) (S T : Set (Fin m))
    (hdisj : ∀ p ∈ S, p ∉ T) (hS : 4 ≤ S.ncard) (hT : 4 ≤ T.ncard)
    (hSsupp : ∀ σ : Perm (Fin m), σ ∈ alternatingGroup (Fin m) → (∀ p ∈ T, σ p = p) → σ ∈ H)
    (hTsupp : ∀ σ : Perm (Fin m), σ ∈ alternatingGroup (Fin m) → (∀ p ∈ S, σ p = p) → σ ∈ H)
    {u₀ v₀ w₀ : Fin m} (hu₀ : u₀ ∈ S) (hv₀ : v₀ ∈ S) (hw₀ : w₀ ∈ T) (huv₀ : u₀ ≠ v₀)
    (hc : swap u₀ w₀ * swap u₀ v₀ ∈ H) :
    ∀ u v w : Fin m, u ∈ S → v ∈ S → w ∈ T → u ≠ v → swap u w * swap u v ∈ H := by
  intro u v w hu hv hw huv
  obtain ⟨g₁, hg₁H, hg₁u, hg₁v, hg₁T⟩ :=
    bk_transport2 H S T hdisj hS hSsupp hu₀ hv₀ hu hv huv₀ huv
  obtain ⟨g₂, hg₂H, hg₂w, hg₂S⟩ := bk_transport1 H S T hdisj hT hTsupp hw₀ hw
  have hgH : g₁ * g₂ ∈ H := H.mul_mem hg₁H hg₂H
  have key := H.mul_mem (H.mul_mem hgH hc) (H.inv_mem hgH)
  rw [bk_conj] at key
  have e1 : (g₁ * g₂) u₀ = u := by rw [Equiv.Perm.mul_apply, hg₂S u₀ hu₀, hg₁u]
  have e2 : (g₁ * g₂) v₀ = v := by rw [Equiv.Perm.mul_apply, hg₂S v₀ hv₀, hg₁v]
  have e3 : (g₁ * g₂) w₀ = w := by rw [Equiv.Perm.mul_apply, hg₂w, hg₁T w hw]
  rw [e1, e2, e3] at key
  exact key

theorem bk_Q_both {m : ℕ} (H : Subgroup (Perm (Fin m))) (S T : Set (Fin m))
    (hdisj : ∀ p ∈ S, p ∉ T) (hS : 4 ≤ S.ncard) (hT : 4 ≤ T.ncard)
    (hSsupp : ∀ σ : Perm (Fin m), σ ∈ alternatingGroup (Fin m) → (∀ p ∈ T, σ p = p) → σ ∈ H)
    (hTsupp : ∀ σ : Perm (Fin m), σ ∈ alternatingGroup (Fin m) → (∀ p ∈ S, σ p = p) → σ ∈ H)
    {u₀ v₀ w₀ : Fin m} (hu₀ : u₀ ∈ S) (hv₀ : v₀ ∈ S) (hw₀ : w₀ ∈ T) (huv₀ : u₀ ≠ v₀)
    (hc : swap u₀ w₀ * swap u₀ v₀ ∈ H) :
    (∀ u v w : Fin m, u ∈ S → v ∈ S → w ∈ T → u ≠ v → swap u w * swap u v ∈ H) ∧
      (∀ u v w : Fin m, u ∈ T → v ∈ T → w ∈ S → u ≠ v → swap u w * swap u v ∈ H) := by
  have h1 := bk_Q H S T hdisj hS hT hSsupp hTsupp hu₀ hv₀ hw₀ huv₀ hc
  refine ⟨h1, ?_⟩
  obtain ⟨w', hw'T, hw'⟩ := bk_exists_avoid T {w₀} (by rw [Finset.card_singleton]; omega)
  have hw'w₀ : w' ≠ w₀ := by
    rintro rfl
    exact hw' (by simp)
  have hu₀w' : u₀ ≠ w' := fun h => hdisj u₀ hu₀ (by rw [h]; exact hw'T)
  have hu₀w₀ : u₀ ≠ w₀ := fun h => hdisj u₀ hu₀ (by rw [h]; exact hw₀)
  have hc' : swap u₀ w' * swap u₀ v₀ ∈ H := h1 u₀ v₀ w' hu₀ hv₀ hw'T huv₀
  have hid : swap u₀ w₀ * swap u₀ w' ∈ H := by
    rw [← bk_identity u₀ v₀ w₀ w']
    exact H.mul_mem hc (H.inv_mem hc')
  have hP : swap w' u₀ * swap w' w₀ ∈ H := by
    rw [← bk_rot hu₀w' hu₀w₀ hw'w₀]
    exact hid
  exact bk_Q H T S (fun p hp hpS => hdisj p hpS hp) hT hS hTsupp hSsupp hw'T hw₀ hu₀ hw'w₀ hP

theorem bk_mixed {m : ℕ} (H : Subgroup (Perm (Fin m))) (B : Set (Fin m))
    (hB : 4 ≤ B.ncard) (hBc : 4 ≤ Bᶜ.ncard)
    (hsupp : ∀ σ : Perm (Fin m), σ ∈ alternatingGroup (Fin m) → (∀ p ∈ Bᶜ, σ p = p) → σ ∈ H)
    (hsuppc : ∀ σ : Perm (Fin m), σ ∈ alternatingGroup (Fin m) → (∀ p ∈ B, σ p = p) → σ ∈ H)
    (g : Perm (Fin m)) (hg : g ∈ H) (hgB : g '' B ≠ B) (hgBc : g '' B ≠ Bᶜ) :
    ∃ p q r : Fin m, p ∈ B ∧ q ∈ Bᶜ ∧ r ≠ p ∧ r ≠ q ∧ swap p r * swap p q ∈ H := by
  by_cases h1 : ∃ b ∈ B, g b ∈ B
  · by_cases h2 : ∃ b ∈ B, g b ∉ B
    · obtain ⟨b₁, hb₁, hgb₁⟩ := h1
      obtain ⟨b₂, hb₂, hgb₂⟩ := h2
      have hb12 : b₁ ≠ b₂ := by
        rintro rfl
        exact hgb₂ hgb₁
      obtain ⟨b₃, hb₃, hb₃₁, hb₃₂⟩ := bk_two_avoid B hB b₁ b₂
      have hcyc : swap b₁ b₃ * swap b₁ b₂ ∈ H := by
        refine hsupp _ (bk_cyc_alt hb12 (Ne.symm hb₃₁) (Ne.symm hb₃₂)) ?_
        intro p hp
        exact bk_cyc_fix b₁ b₂ b₃ p (bk_ne_of_mem_compl hp hb₁) (bk_ne_of_mem_compl hp hb₂)
          (bk_ne_of_mem_compl hp hb₃)
      have hconj := H.mul_mem (H.mul_mem hg hcyc) (H.inv_mem hg)
      rw [bk_conj] at hconj
      refine ⟨g b₁, g b₂, g b₃, hgb₁, (Set.mem_compl_iff B _).mpr hgb₂, ?_, ?_, hconj⟩
      · intro h
        exact hb₃₁ (g.injective h)
      · intro h
        exact hb₃₂ (g.injective h)
    · exfalso
      push Not at h2
      have hsub : g '' B ⊆ B := by
        rintro _ ⟨b, hb, rfl⟩
        exact h2 b hb
      have hcard : B.ncard ≤ (g '' B).ncard :=
        (Set.ncard_image_of_injective B g.injective).ge
      exact hgB (Set.eq_of_subset_of_ncard_le hsub hcard)
  · push Not at h1
    have hsub : g '' B ⊆ Bᶜ := by
      rintro _ ⟨b, hb, rfl⟩
      exact (Set.mem_compl_iff B _).mpr (h1 b hb)
    obtain ⟨c₀, hc₀, hc₀'⟩ : ∃ c₀ ∈ Bᶜ, c₀ ∉ g '' B := by
      by_contra hcon
      push Not at hcon
      exact hgBc (Set.Subset.antisymm hsub hcon)
    have hc₂ : g⁻¹ c₀ ∈ Bᶜ := by
      rw [Set.mem_compl_iff]
      intro hmem
      exact hc₀' ⟨g⁻¹ c₀, hmem, bk_apply_inv g c₀⟩
    obtain ⟨b₀, hb₀⟩ := Set.nonempty_of_ncard_ne_zero (show B.ncard ≠ 0 by omega)
    have hc₁ : g⁻¹ b₀ ∈ Bᶜ := by
      rw [Set.mem_compl_iff]
      intro hmem
      exact h1 (g⁻¹ b₀) hmem (by rw [bk_apply_inv]; exact hb₀)
    have hc₁₂ : g⁻¹ b₀ ≠ g⁻¹ c₀ := by
      intro h
      have hbc : g (g⁻¹ b₀) = g (g⁻¹ c₀) := by rw [h]
      rw [bk_apply_inv, bk_apply_inv] at hbc
      rw [← hbc] at hc₀
      exact (Set.mem_compl_iff B b₀).mp hc₀ hb₀
    obtain ⟨c₃, hc₃, hc₃₁, hc₃₂⟩ := bk_two_avoid Bᶜ hBc (g⁻¹ b₀) (g⁻¹ c₀)
    have hcyc : swap (g⁻¹ b₀) c₃ * swap (g⁻¹ b₀) (g⁻¹ c₀) ∈ H := by
      refine hsuppc _ (bk_cyc_alt hc₁₂ (Ne.symm hc₃₁) (Ne.symm hc₃₂)) ?_
      intro p hp
      exact bk_cyc_fix (g⁻¹ b₀) (g⁻¹ c₀) c₃ p (bk_ne_of_compl_mem hp hc₁)
        (bk_ne_of_compl_mem hp hc₂) (bk_ne_of_compl_mem hp hc₃)
    have hconj := H.mul_mem (H.mul_mem hg hcyc) (H.inv_mem hg)
    rw [bk_conj, bk_apply_inv, bk_apply_inv] at hconj
    refine ⟨b₀, c₀, g c₃, hb₀, hc₀, ?_, ?_, hconj⟩
    · intro h
      exact hc₃₁ (by rw [← h, bk_inv_apply])
    · intro h
      exact hc₃₂ (by rw [← h, bk_inv_apply])

theorem bk_main {m : ℕ} (H : Subgroup (Perm (Fin m))) (B : Set (Fin m))
    (hB : 4 ≤ B.ncard) (hBc : 4 ≤ Bᶜ.ncard)
    (hsupp : ∀ σ : Perm (Fin m), σ ∈ alternatingGroup (Fin m) → (∀ p ∈ Bᶜ, σ p = p) → σ ∈ H)
    (hsuppc : ∀ σ : Perm (Fin m), σ ∈ alternatingGroup (Fin m) → (∀ p ∈ B, σ p = p) → σ ∈ H)
    (hmixed : ∃ p q r : Fin m, p ∈ B ∧ q ∈ Bᶜ ∧ r ≠ p ∧ r ≠ q ∧ swap p r * swap p q ∈ H) :
    ∀ x y z : Fin m, x ≠ y → x ≠ z → y ≠ z → swap x z * swap x y ∈ H := by
  obtain ⟨p, q, r, hpB, hqBc, hrp, hrq, hmix3⟩ := hmixed
  have hpq : p ≠ q := bk_ne_of_compl_mem hpB hqBc
  have hdisj : ∀ s ∈ B, s ∉ Bᶜ := fun s hs hsc => (Set.mem_compl_iff B s).mp hsc hs
  have hdisj' : ∀ s ∈ Bᶜ, s ∉ B := fun s hs hsB => (Set.mem_compl_iff B s).mp hs hsB
  have hQ : (∀ u v w : Fin m, u ∈ B → v ∈ B → w ∈ Bᶜ → u ≠ v → swap u w * swap u v ∈ H) ∧
      (∀ u v w : Fin m, u ∈ Bᶜ → v ∈ Bᶜ → w ∈ B → u ≠ v → swap u w * swap u v ∈ H) := by
    by_cases hrB : r ∈ B
    · have hc : swap r q * swap r p ∈ H := by
        rw [bk_rot hrp hrq hpq]
        exact hmix3
      exact bk_Q_both H B Bᶜ hdisj hB hBc hsupp hsuppc hrB hpB hqBc hrp hc
    · have hrBc : r ∈ Bᶜ := (Set.mem_compl_iff B r).mpr hrB
      have hc : swap q p * swap q r ∈ H := by
        rw [bk_rot (Ne.symm hrq) (Ne.symm hpq) hrp, bk_rot hrp hrq hpq]
        exact hmix3
      obtain ⟨h1, h2⟩ :=
        bk_Q_both H Bᶜ B hdisj' hBc hB hsuppc hsupp hqBc hrBc hpB (Ne.symm hrq) hc
      exact ⟨h2, h1⟩
  obtain ⟨QB, QBc⟩ := hQ
  intro x y z hxy hxz hyz
  have hzx : z ≠ x := Ne.symm hxz
  have hzy : z ≠ y := Ne.symm hyz
  by_cases hx : x ∈ B
  · by_cases hy : y ∈ B
    · by_cases hz : z ∈ B
      · exact hsupp _ (bk_cyc_alt hxy hxz hyz) (fun s hs =>
          bk_cyc_fix x y z s (bk_ne_of_mem_compl hs hx) (bk_ne_of_mem_compl hs hy)
            (bk_ne_of_mem_compl hs hz))
      · exact QB x y z hx hy ((Set.mem_compl_iff B z).mpr hz) hxy
    · by_cases hz : z ∈ B
      · rw [← bk_rot hzx hzy hxy]
        exact QB z x y hz hx ((Set.mem_compl_iff B y).mpr hy) hzx
      · rw [bk_rot hxy hxz hyz]
        exact QBc y z x ((Set.mem_compl_iff B y).mpr hy) ((Set.mem_compl_iff B z).mpr hz) hx hyz
  · by_cases hy : y ∈ B
    · by_cases hz : z ∈ B
      · rw [bk_rot hxy hxz hyz]
        exact QB y z x hy hz ((Set.mem_compl_iff B x).mpr hx) hyz
      · rw [← bk_rot hzx hzy hxy]
        exact QBc z x y ((Set.mem_compl_iff B z).mpr hz) ((Set.mem_compl_iff B x).mpr hx) hy hzx
    · by_cases hz : z ∈ B
      · exact QBc x y z ((Set.mem_compl_iff B x).mpr hx) ((Set.mem_compl_iff B y).mpr hy) hz hxy
      · exact hsuppc _ (bk_cyc_alt hxy hxz hyz) (fun s hs =>
          bk_cyc_fix x y z s (bk_ne_of_compl_mem hs hx) (bk_ne_of_compl_mem hs hy)
            (bk_ne_of_compl_mem hs hz))

theorem alt_eq_top_of_halves {m : ℕ} {B : Set (Fin m)} (hB : 4 ≤ B.ncard) (hBc : 4 ≤ Bᶜ.ncard)
    (G : Subgroup (alternatingGroup (Fin m)))
    (hsupp : ∀ g : alternatingGroup (Fin m), (∀ x ∈ Bᶜ, (g : Perm (Fin m)) x = x) → g ∈ G)
    (hsuppc : ∀ g : alternatingGroup (Fin m), (∀ x ∈ B, (g : Perm (Fin m)) x = x) → g ∈ G)
    (hmix : ∃ g ∈ G, (g : Perm (Fin m)) '' B ≠ B ∧ (g : Perm (Fin m)) '' B ≠ Bᶜ) : G = ⊤ := by
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (Perm (Fin m)),
      H = G.map (alternatingGroup (Fin m)).subtype := ⟨_, rfl⟩
  have hsupp' : ∀ σ : Perm (Fin m), σ ∈ alternatingGroup (Fin m) →
      (∀ p ∈ Bᶜ, σ p = p) → σ ∈ H := by
    intro σ hσ hfix
    rw [hH]
    exact Subgroup.mem_map.mpr ⟨⟨σ, hσ⟩, hsupp ⟨σ, hσ⟩ hfix, rfl⟩
  have hsuppc' : ∀ σ : Perm (Fin m), σ ∈ alternatingGroup (Fin m) →
      (∀ p ∈ B, σ p = p) → σ ∈ H := by
    intro σ hσ hfix
    rw [hH]
    exact Subgroup.mem_map.mpr ⟨⟨σ, hσ⟩, hsuppc ⟨σ, hσ⟩ hfix, rfl⟩
  obtain ⟨g, hgG, hgB, hgBc⟩ := hmix
  have hgH : (g : Perm (Fin m)) ∈ H := by
    rw [hH]
    exact Subgroup.mem_map.mpr ⟨g, hgG, rfl⟩
  have hmixed := bk_mixed H B hB hBc hsupp' hsuppc' (g : Perm (Fin m)) hgH hgB hgBc
  have hmain := bk_main H B hB hBc hsupp' hsuppc' hmixed
  have hAlt : alternatingGroup (Fin m) ≤ H := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ
    have h3 : σ.IsThreeCycle := hσ
    have hne : σ.support.Nonempty := Finset.card_pos.mp (by simp [h3.card_support])
    obtain ⟨a, ha⟩ := hne
    have hnd : [a, σ a, σ (σ a)].Nodup := h3.nodup_iff_mem_support.mpr ha
    have hrep : σ = swap a (σ a) * swap (σ a) (σ (σ a)) :=
      h3.eq_swap_mul_swap_iff_mem_support.mpr ha
    rw [Equiv.swap_comm a (σ a)] at hrep
    have hne1 : σ a ≠ σ (σ a) := fun h => (Equiv.Perm.mem_support.mp ha) (σ.injective h).symm
    have hne2 : σ a ≠ a := Equiv.Perm.mem_support.mp ha
    have hne3 : σ (σ a) ≠ a := by
      intro h
      simp [List.nodup_cons, h] at hnd
    rw [hrep]
    exact hmain (σ a) (σ (σ a)) a hne1 hne2 hne3
  rw [Subgroup.eq_top_iff']
  intro x
  have hx : (x : Perm (Fin m)) ∈ H := hAlt x.2
  rw [hH] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hxy : y = x := Subtype.ext hyx
  rw [← hxy]
  exact hy

end CFSG.Quasithin.B69K
