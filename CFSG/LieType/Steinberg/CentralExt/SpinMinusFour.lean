module

public import CFSG.LieType.Steinberg.CentralExt.SpinMinusThree

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.SpinOdd (IsRootVec IsShort isShort_single elt elt_of_isLong
  elt_of_isShort)
open CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed (single_add_single_apply_of_ne'
  neg_one_zpow_boolSign negPair negPair_swap single_add_single_add_not two_mul_boolSign
  not_isLong_single_two swapPair swapPair_swap not_isLong_add_disjoint)
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed

attribute [local instance] TorusLift.centerCommGroup

open SpinOddClosed (TorIdx chi)
open QuadraticAlgebra

variable {n : ℕ} {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem ne_zero_of_irr : c ≠ 0 := by simpa using hirr 0

theorem fieldCoord_omega_ne_zero : fieldCoord (QuadraticAlgebra.omega : ShortField b c) ≠ 0 := fun h => by
  simpa [fieldCoord] using congrFun h 1

theorem planeNorm_fieldCoord_omega : planeNorm b c (fieldCoord (QuadraticAlgebra.omega : ShortField b c)) = c := by
  simp [planeNorm, fieldCoord]

theorem planeRefl_omega (hc : c ≠ 0) (t : ShortField b c) :
    planeRefl b c (fieldCoord (QuadraticAlgebra.omega : ShortField b c)) (planeRefl b c planeOne (fieldCoord t)) =
      fieldCoord (algebraMap K (ShortField b c) c⁻¹ * (QuadraticAlgebra.omega * QuadraticAlgebra.omega * t)) := by
  rw [← fieldCoord_negStar, planeRefl, planeNorm_fieldCoord_omega]
  ext k
  fin_cases k <;> simp [fieldCoord, negStar, polarPlane] <;> field_simp <;> ring

@[expose] noncomputable def torOmega (m : Fin (n - 1)) : spinGroup (quadMinus n K b c) :=
  shortTorusElt n hirr m (fieldCoord (QuadraticAlgebra.omega : ShortField b c))

variable (b c) in
open _root_.Classical in
@[expose] noncomputable def chiOmega (m : Fin (n - 1)) (γ : Fin (n - 1) → ℤ) : ShortField b c :=
  if IsLong (toStdB (n - 1) γ) then algebraMap K (ShortField b c) (c ^ toStdB (n - 1) γ m)
  else algebraMap K (ShortField b c) (c ^ toStdB (n - 1) γ m * c⁻¹) * QuadraticAlgebra.omega * QuadraticAlgebra.omega

theorem chiOmega_of_isLong {m : Fin (n - 1)} {γ : Fin (n - 1) → ℤ}
    (h : IsLong (toStdB (n - 1) γ)) :
    chiOmega b c m γ = algebraMap K (ShortField b c) (c ^ toStdB (n - 1) γ m) := by
  rw [chiOmega, ite_eq_left h]

theorem chiOmega_of_not_isLong {m : Fin (n - 1)} {γ : Fin (n - 1) → ℤ}
    (h : ¬IsLong (toStdB (n - 1) γ)) :
    chiOmega b c m γ =
      algebraMap K (ShortField b c) (c ^ toStdB (n - 1) γ m * c⁻¹) * QuadraticAlgebra.omega * QuadraticAlgebra.omega := by
  rw [chiOmega, ite_eq_right h]

theorem chiOmega_eq_one {m : Fin (n - 1)} {γ : Fin (n - 1) → ℤ} (h : IsLong (toStdB (n - 1) γ))
    (h0 : toStdB (n - 1) γ m = 0) : chiOmega b c m γ = 1 := by
  rw [chiOmega_of_isLong h, h0, zpow_zero, map_one]

theorem chiOmega_self (hc : c ≠ 0) {m : Fin (n - 1)} {γ : Fin (n - 1) → ℤ}
    (h : toStdB (n - 1) γ = Pi.single m (boolSign true)) :
    chiOmega b c m γ = QuadraticAlgebra.omega * QuadraticAlgebra.omega := by
  have hnl : ¬IsLong (toStdB (n - 1) γ) := by
    rw [h]
    exact (isShort_single m true).not_isLong
  rw [chiOmega_of_not_isLong hnl, h, Pi.single_eq_same, boolSign_true, zpow_one,
    mul_inv_cancel₀ hc, map_one, one_mul]

include hirr in
theorem omega_mul_omega_ne_one : (QuadraticAlgebra.omega : ShortField b c) * QuadraticAlgebra.omega ≠ 1 := fun h => by
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp only [re_mul, im_mul, re_omega, im_omega, re_one, im_one] at h1 h2
  exact hirr 1 (by linear_combination h2 - h1)

theorem shortTorusScalar_omega (m k : Fin (n - 1)) (r : Bool) :
    shortTorusScalar n b c m (fieldCoord (QuadraticAlgebra.omega : ShortField b c)) k r =
      c ^ ((Pi.single k (boolSign r) : Fin (n - 1) → ℤ) m) := by
  rw [shortTorusScalar, planeNorm_fieldCoord_omega]
  by_cases hk : k = m
  · subst hk
    rw [ite_eq_left rfl, Pi.single_eq_same]
    cases r <;> simp [boolSign]
  · rw [ite_eq_right hk, Pi.single_eq_of_ne (Ne.symm hk), zpow_zero]

theorem torOmega_conj_x (m : Fin (n - 1)) {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) (t : ShortField b c) :
    torOmega hirr m * x hirr γ t * (torOmega hirr m)⁻¹ = x hirr γ (chiOmega b c m γ * t) := by
  have hc := ne_zero_of_irr hirr
  have ha := fieldCoord_omega_ne_zero (b := b) (c := c)
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, u, h⟩ | ⟨i, s, h⟩
  · have hl : IsLong (toStdB (n - 1) γ) := h ▸ isLong_single_add_single hij s u
    rw [x_of_isLong hirr hl, x_of_isLong hirr hl, elt_of_isLong _ hl, elt_of_isLong _ hl,
      torOmega, conj_rootElt_of_diag (minusFrame n b c).toHypFrame _ _
        (spinAction_shortTorusElt_minusVec n hirr m ha) hij h,
      chiOmega_of_isLong hl, re_mul, algebraMap_re, algebraMap_im, shortTorusScalar_omega,
      shortTorusScalar_omega, ← zpow_add₀ hc, h]
    simp only [Pi.add_apply, mul_zero, zero_mul, add_zero]
  · have hnl : ¬IsLong (toStdB (n - 1) γ) := by
      rw [h]
      exact (isShort_single i s).not_isLong
    rw [x_of_short hirr h, x_of_short hirr h, torOmega,
      conj_twShortRoot n hirr _ i s (spinAction_shortTorusElt_minusVec n hirr m ha i s)
        (spinAction_shortTorusElt_planeVec n hirr m ha (fieldCoord t)),
      planeRefl_omega hc, shortTorusScalar_omega, ← fieldCoord_algebraMap_mul,
      chiOmega_of_not_isLong hnl, h, map_mul]
    congr 3
    ring

theorem torOmega_conj_tor [Finite K] {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (τ : Kˣ)
    (m : Fin (n - 1)) :
    torOmega hirr m * tor (.long i j hij s t τ) * (torOmega hirr m)⁻¹ =
      tor (.long i j hij s t τ) := by
  have he := (minusFrame n b c).spinAction_longTorus_vec hij s t τ m true
  have hf := (minusFrame n b c).spinAction_longTorus_vec hij s t τ m false
  simp only [minusFrame_vec] at he hf
  have key := shortTorusElt_conj_of_scalar n hirr m _ (τ ^ longCoroot i j s t m true) he
    (by rw [hf, ← zpow_neg, ← longCoroot_not, Bool.not_true])
    (spinAction_longTorus_planeVec n hij s t τ) (fieldCoord_omega_ne_zero (b := b) (c := c))
  have hc : Commute ((minusFrame n b c).longTorus hij s t τ) (torOmega hirr m) :=
    mul_inv_eq_iff_eq_mul.mp key
  show torOmega hirr m * (minusFrame n b c).longTorus hij s t τ * (torOmega hirr m)⁻¹ =
    (minusFrame n b c).longTorus hij s t τ
  rw [← hc.eq, mul_inv_cancel_right]

variable {E : Type*} [Group E] {π : E →* spinGroup (quadMinus n K b c)}
  (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)

include hcen hπ in
theorem isRootLift_conj_torOmega [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] [Finite K]
    {γ : Fin (n - 1) → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅)
    (h0 : TorusLift.commPairing hcen hπ (x_add hirr γ) = 0) {i j : Fin (n - 1)} (hij : i ≠ j)
    (hp₀ : algebraMap K (ShortField b c) (chi (.long i j hij true true (-1)) γ) ≠ 1) :
    IsRootLift hirr π γ (X hirr π γ) ∧ ∀ (m : Fin (n - 1)) (e : E), π e = torOmega hirr m →
      ∀ s, e * X hirr π γ s * e⁻¹ = X hirr π γ (chiOmega b c m γ * s) := by
  have hX := X_isRootLift hirr (exists_isRootLift hirr hcen hπ hγ h0 hp₀)
  refine ⟨hX, fun m e he s => ?_⟩
  have hXY : X hirr π γ = TorusLift.canonLift hπ (x := x hirr γ)
      (tor (.long i j hij true true (-1)))
      (algebraMap K (ShortField b c) (chi (.long i j hij true true (-1)) γ)) :=
    TorusLift.lift_unique hcen hX.1
      (TorusLift.canonLift_add hcen hπ (x_add hirr γ) h0 (tor_conj_x hirr _ hγ) hp₀) hX.2.1
      (TorusLift.map_canonLift hπ (x_add hirr γ) (tor_conj_x hirr _ hγ) hp₀) hp₀
      (hX.2.2.2 _ _ (TorusLift.map_lift hπ _))
      (TorusLift.conj_canonLift hcen hπ (tor_comm _ _) (tor_conj_x hirr _ hγ)
        (TorusLift.map_lift hπ _))
  rw [hXY]
  exact TorusLift.conj_canonLift hcen hπ (torOmega_conj_tor hirr hij true true (-1) m)
    (torOmega_conj_x hirr m hγ) he s

theorem eq_true_of_ht_pos {γ : Fin (n - 1) → ℤ} (hpos : 0 < ht γ) {k : Fin (n - 1)} {u : Bool}
    (h : toStdB (n - 1) γ = Pi.single k (boolSign u)) : u = true := by
  by_contra hu
  have hu' : u = false := by simpa using hu
  rw [ht_of_toStdB_eq_single (n - 1) h, hu', boolSign_false] at hpos
  have := k.isLt
  omega

theorem chi_long_neg_one_eq_one {i j : Fin (n - 1)} (hij : i ≠ j) {γ : Fin (n - 1) → ℤ}
    {s t : Bool} (he : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    chi (.long i j hij true true (-1)) γ = (1 : K) := by
  rw [SpinOddClosed.chi_long_neg_one, he, SpinTorus.single_add_single_dotProduct,
    single_add_single_apply_left hij, single_add_single_apply_right hij, mul_one, mul_one,
    SpinOddClosed.neg_one_zpow_boolSign_add, Units.val_one]

theorem chi_long_neg_one_ne_one (h2 : (2 : K) ≠ 0) {i j : Fin (n - 1)} (hij : i ≠ j)
    {δ : Fin (n - 1) → ℤ} {r : Bool}
    (hδ : toStdB (n - 1) δ i + toStdB (n - 1) δ j = boolSign r) :
    chi (.long i j hij true true (-1)) δ ≠ (1 : K) := by
  rw [SpinOddClosed.chi_long_neg_one, dotProduct_comm, SpinTorus.single_add_single_dotProduct,
    one_mul, one_mul, hδ, neg_one_zpow_boolSign]
  exact SpinOddClosed.neg_one_ne_one_of_two h2

include hcen hπ in
theorem sep_or_comm_four [Finite K] (hK : Nat.card K = 3) (hn4 : 4 ≤ n)
    (hspec : ∀ γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅, IsRootLift hirr π γ (X hirr π γ) ∧
      ∀ (m : Fin (n - 1)) (e : E), π e = torOmega hirr m →
        ∀ s, e * X hirr π γ s * e⁻¹ = X hirr π γ (chiOmega b c m γ * s))
    {γ δ : Fin (n - 1) → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅)
    (hδ : δ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) (hγp : 0 < ht γ) (hδp : 0 < ht δ)
    (hne : toStdB (n - 1) δ ≠ toStdB (n - 1) γ) (hne' : toStdB (n - 1) δ ≠ -toStdB (n - 1) γ) :
    (∃ p : TorIdx (n - 1) K, chi p γ = 1 ∧ chi p δ ≠ 1) ∨
      (∃ m : Fin (n - 1), chiOmega b c m γ = 1 ∧ chiOmega b c m δ ≠ 1) ∨
        ∀ s t, X hirr π γ s * X hirr π δ t = X hirr π δ t * X hirr π γ s := by
  have := fact_shortField hirr
  have hn : 3 ≤ n - 1 := by omega
  have h2 : (2 : K) ≠ 0 := FieldThree.two_ne_zero_of_card_three hK
  have hc := ne_zero_of_irr hirr
  have hω := omega_mul_omega_ne_one hirr
  have hbs : ∀ u : Bool, boolSign u = boolSign true ∨ boolSign u = boolSign false := fun u => by
    cases u <;> simp
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, he⟩ | ⟨i, s, he⟩ <;>
    rcases exists_toStdB_eq_of_mem_roots n hδ with ⟨k, l, hkl, u, v, he'⟩ | ⟨k, u, he'⟩
  ·
    have hγl : IsLong (toStdB (n - 1) γ) := by rw [he]; exact isLong_single_add_single hij s t
    have hδl : IsLong (toStdB (n - 1) δ) := by rw [he']; exact isLong_single_add_single hkl u v
    by_cases hk : k ≠ i ∧ k ≠ j
    · by_cases hl : l ≠ i ∧ l ≠ j
      ·
        right; right
        obtain ⟨a, ha, h1, h2'⟩ := swapPair_swap (minusFrame n b c).toHypFrame hij hk.1.symm
          hl.1.symm hk.2.symm hl.2.symm hkl s t u v
        rw [← he, ← he'] at h1 h2'
        refine commute_X_of_swap hirr hcen hπ hK (hspec γ hγ).1 (hspec δ hδ).1 hγl hδl ?_ ?_ ha
          h1 h2'
        · rw [he, he']
          exact not_isLong_add_disjoint hij hk.1.symm hl.1.symm hk.2.symm hl.2.symm hkl s t u v
        · rw [he, he']
          intro h0
          have := congrFun h0 i
          simp [hij, hk.1.symm, hl.1.symm, boolSign] at this
          cases s <;> simp at this
      ·
        left
        have hl' : l = i ∨ l = j := by tauto
        refine ⟨.long i j hij true true (-1), chi_long_neg_one_eq_one hij he,
          chi_long_neg_one_ne_one h2 hij (r := v) ?_⟩
        rw [he']
        rcases hl' with rfl | rfl
        · rw [single_add_single_apply_right hkl, single_add_single_apply_of_ne' hk.2.symm hij.symm,
            add_zero]
        · rw [single_add_single_apply_of_ne' hk.1.symm hij, single_add_single_apply_right hkl,
            zero_add]
    have hk' : k = i ∨ k = j := by tauto
    by_cases hl : l ≠ i ∧ l ≠ j
    ·
      left
      refine ⟨.long i j hij true true (-1), chi_long_neg_one_eq_one hij he,
        chi_long_neg_one_ne_one h2 hij (r := u) ?_⟩
      rw [he']
      rcases hk' with rfl | rfl
      · rw [single_add_single_apply_left hkl, single_add_single_apply_of_ne' hij.symm hl.2.symm,
          add_zero]
      · rw [single_add_single_apply_of_ne' hij hl.1.symm, single_add_single_apply_left hkl,
          zero_add]
    right; right
    obtain ⟨u', v', he''⟩ : ∃ u' v' : Bool,
        toStdB (n - 1) δ = Pi.single i (boolSign u') + Pi.single j (boolSign v') := by
      have hl' : l = i ∨ l = j := by tauto
      rcases hk' with rfl | rfl <;> rcases hl' with rfl | rfl
      · exact absurd rfl hkl
      · exact ⟨u, v, he'⟩
      · exact ⟨v, u, by rw [he', add_comm]⟩
      · exact absurd rfl hkl
    obtain ⟨m, hmi, hmj⟩ := exists_ne_and_ne hn i j
    have hcase : (u' = s ∧ v' = !t) ∨ (u' = !s ∧ v' = t) := by
      have hnot : ∀ b c : Bool, b ≠ c → b = !c := fun b c h => by
        cases b <;> cases c <;> simp_all
      by_cases hu : u' = s <;> by_cases hv : v' = t
      · exact absurd (by rw [he'', he, hu, hv]) hne
      · exact Or.inl ⟨hu, hnot _ _ hv⟩
      · exact Or.inr ⟨hnot _ _ hu, hv⟩
      · exfalso
        apply hne'
        rw [he'', he, SpinTorus.neg_single_add_single, hnot _ _ hu, hnot _ _ hv, boolSign_not,
          boolSign_not]
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨a, ha, h1, h2'⟩ := negPair_swap (minusFrame n b c).toHypFrame hij hmi hmj u' t
      rw [← he, ← he''] at h1 h2'
      refine commute_X_of_swap hirr hcen hπ hK (hspec γ hγ).1 (hspec δ hδ).1 hγl hδl ?_ ?_ ha
        h1 h2'
      · rw [he, he'', single_add_single_add_not]
        exact not_isLong_single_two (two_mul_boolSign u')
      · rw [he, he'', single_add_single_add_not]
        intro h0
        have := congrFun h0 i
        rw [Pi.single_eq_same, Pi.zero_apply] at this
        rcases two_mul_boolSign u' with h' | h' <;> omega
    · obtain ⟨a, ha, h1, h2'⟩ := negPair_swap (minusFrame n b c).toHypFrame hij.symm hmj hmi v' s
      have ehe : toStdB (n - 1) γ = Pi.single j (boolSign v') + Pi.single i (boolSign s) := by
        rw [he, add_comm]
      have ehe' : toStdB (n - 1) δ = Pi.single j (boolSign v') + Pi.single i (boolSign (!s)) := by
        rw [he'', add_comm]
      rw [← ehe, ← ehe'] at h1 h2'
      refine commute_X_of_swap hirr hcen hπ hK (hspec γ hγ).1 (hspec δ hδ).1 hγl hδl ?_ ?_ ha
        h1 h2'
      · rw [ehe, ehe', single_add_single_add_not]
        exact not_isLong_single_two (two_mul_boolSign v')
      · rw [ehe, ehe', single_add_single_add_not]
        intro h0
        have := congrFun h0 j
        rw [Pi.single_eq_same, Pi.zero_apply] at this
        rcases two_mul_boolSign v' with h' | h' <;> omega
  ·
    have hγl : IsLong (toStdB (n - 1) γ) := by rw [he]; exact isLong_single_add_single hij s t
    by_cases hk : k = i ∨ k = j
    ·
      left
      refine ⟨.long i j hij true true (-1), chi_long_neg_one_eq_one hij he,
        chi_long_neg_one_ne_one h2 hij (r := u) ?_⟩
      rw [he']
      rcases hk with rfl | rfl
      · rw [Pi.single_eq_same, Pi.single_eq_of_ne hij.symm, add_zero]
      · rw [Pi.single_eq_of_ne hij, Pi.single_eq_same, zero_add]
    ·
      right; left
      push Not at hk
      obtain rfl := eq_true_of_ht_pos hδp he'
      refine ⟨k, chiOmega_eq_one hγl ?_, ?_⟩
      · rw [he, single_add_single_apply_of_ne' hk.1 hk.2]
      · rw [chiOmega_self hc he']
        exact hω
  ·
    obtain rfl := eq_true_of_ht_pos hγp he
    have hδl : IsLong (toStdB (n - 1) δ) := by rw [he']; exact isLong_single_add_single hkl u v
    have hS : ∀ x, x ≠ i → x ≠ i → toStdB (n - 1) γ x = 0 := fun x hxi _ => by
      rw [he, Pi.single_eq_of_ne hxi]
    by_cases hik : i = k
    ·
      left
      subst hik
      obtain ⟨m, hmi, hml⟩ := exists_ne_and_ne hn i l
      refine SpinOddClosed.exists_sep_out h2 hS (l := i) ?_ (fun x hxl hxi => ?_) hkl.symm
        hkl.symm ⟨m, hmi, hmi, hml, hmi⟩
      · rw [he', single_add_single_apply_right hkl]
        exact hbs v
      · rw [he', single_add_single_apply_of_ne' hxi hxl]
    by_cases hil : i = l
    ·
      left
      subst hil
      obtain ⟨m, hmi, hmk⟩ := exists_ne_and_ne hn i k
      refine SpinOddClosed.exists_sep_out h2 hS (l := i) ?_ (fun x hxk hxi => ?_) hkl hkl
        ⟨m, hmi, hmi, hmk, hmi⟩
      · rw [he', single_add_single_apply_left hkl]
        exact hbs u
      · rw [he', single_add_single_apply_of_ne' hxk hxi]
    right; right
    intro s' t'
    refine PosLift.commute_of_rev_sep hcen (hspec γ hγ).1.1 (hspec γ hγ).1.2.1 (hspec δ hδ).1.2.1
      (fun s₁ t₁ => ?_) hω (e := TorusLift.lift hπ (torOmega hirr i)) (fun s₁ => ?_)
      (fun t₁ => ?_) s' t'
    · rw [x_of_short hirr he, x_of_isLong hirr hδl, elt_of_isLong _ hδl, rootElt_eq _ hkl he']
      exact (commute_longRoot_twShortRoot_of_ne n hirr hkl hik hil u v true _ _).eq.symm
    · rw [(hspec γ hγ).2 i _ (TorusLift.map_lift hπ _), chiOmega_self hc he]
    · rw [(hspec δ hδ).2 i _ (TorusLift.map_lift hπ _),
        chiOmega_eq_one hδl (by rw [he', single_add_single_apply_of_ne' hik hil]), one_mul]
  ·
    have hS : ∀ x, x ≠ i → x ≠ i → toStdB (n - 1) γ x = 0 := fun x hxi _ => by
      rw [he, Pi.single_eq_of_ne hxi]
    by_cases hk : k = i
    · exfalso
      subst hk
      cases u <;> cases s
      · exact hne (by rw [he, he'])
      · apply hne'
        rw [he, he', ← Pi.single_neg]
        simp [boolSign]
      · apply hne'
        rw [he, he', ← Pi.single_neg]
        simp [boolSign]
      · exact hne (by rw [he, he'])
    ·
      left
      obtain ⟨m, hmi, hmk⟩ := exists_ne_and_ne hn i k
      refine SpinOddClosed.exists_sep_out h2 hS (l := k) ?_ (fun x hxk _ => ?_) hk hk
        ⟨m, hmi, hmi, hmk, hmk⟩
      · rw [he', Pi.single_eq_same]
        exact hbs u
      · rw [he', Pi.single_eq_of_ne hxk]

include hirr in
theorem spinMinus_three_exists_section_of_pKernel' [Finite K] (hK : Nat.card K = 3) (hn4 : 4 ≤ n)
    {p : ℕ} [Fact p.Prime] [CharP K p] {E : Type*} [Group E] [Finite E]
    {π : E →* spinGroup (quadMinus n K b c)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    ∃ s : spinGroup (quadMinus n K b c) →* E, ∀ g, π (s g) = g := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : Finite (spinGroup (quadMinus n K b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have h2 : (2 : K) ≠ 0 := FieldThree.two_ne_zero_of_card_three hK
  have hm1 := SpinOddClosed.neg_one_ne_one_of_two h2
  have hι : ∀ r : K, algebraMap K (ShortField b c) r = 1 → r = 1 := fun r h => by
    rw [← map_one (algebraMap K (ShortField b c))] at h
    exact (algebraMap K (ShortField b c)).injective h
  have hspec : ∀ γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅, IsRootLift hirr π γ (X hirr π γ) ∧
      ∀ (m : Fin (n - 1)) (e : E), π e = torOmega hirr m →
        ∀ s, e * X hirr π γ s * e⁻¹ = X hirr π γ (chiOmega b c m γ * s) := by
    intro γ hγ
    have h0 : TorusLift.commPairing hcen hπ (x_add hirr γ) = 0 := by
      rcases SpinOddClosed.isRootVec_of_mem hγ with hl | ⟨k, u, he⟩
      · exact commPairing_eq_zero_long hirr hcen hπ hn4 hl
      · exact commPairing_eq_zero_short_three hirr hcen hπ hK hn4 he
    obtain ⟨i, m, hmi, hp₀⟩ : ∃ (i m : Fin (n - 1)) (hmi : i ≠ m),
        chi (.long i m hmi true true (-1)) γ ≠ (1 : K) := by
      rcases SpinOddClosed.isRootVec_of_mem hγ with ⟨i, j, hij, s, t, he⟩ | ⟨i, s, he⟩
      · obtain ⟨m, hmi, hmj⟩ := exists_ne_and_ne (show 3 ≤ n - 1 by omega) i j
        refine ⟨i, m, hmi.symm, ?_⟩
        rw [SpinOddClosed.chi_long_neg_one, he, SpinTorus.single_add_single_dotProduct,
          single_add_single_apply_left hmi.symm, single_add_single_apply_of_ne' hij.symm hmj.symm,
          mul_one, mul_zero, add_zero, neg_one_zpow_boolSign]
        exact hm1
      · obtain ⟨m, hmi, -⟩ := exists_ne_and_ne (show 3 ≤ n - 1 by omega) i i
        refine ⟨i, m, hmi.symm, ?_⟩
        rw [SpinOddClosed.chi_long_neg_one, he, single_dotProduct,
          single_add_single_apply_left hmi.symm, mul_one, neg_one_zpow_boolSign]
        exact hm1
    exact isRootLift_conj_torOmega hirr hcen hπ hγ h0 hmi fun h => hp₀ (hι _ h)
  refine PosLift.exists_section_of_posLift' (minusDatum_isCTGroupDatum n hirr hn4)
    (minusDatum_steinbergExtras n hirr) (bruhatExtras hirr hn4) rfl (p := p)
    (fun γ hγ => isPGroup_minusRootGroup hirr hγ) (coprime_card_torus hirr) hπ hcen hpk
    (x := x hirr) (fun γ hγ g => ⟨fun hg => exists_x_eq_of_mem hirr hγ.1 hg,
      fun ⟨t, ht⟩ => ht ▸ x_mem hirr hγ.1 t⟩)
    (fun γ _ => x_add hirr γ) (X := X hirr π) (fun γ hγ => (hspec γ hγ.1).1.1)
    (fun γ hγ => (hspec γ hγ.1).1.2.1) (fun γ hγ => (hspec γ hγ.1).1.2.2.1)
    (tor := Sum.elim (fun p => TorusLift.lift hπ (tor p))
      (fun m => TorusLift.lift hπ (torOmega hirr m)))
    (χ := Sum.elim (fun p γ => algebraMap K (ShortField b c) (chi p γ)) (chiOmega b c))
    (fun q γ hγ c' => ?_) ?_
  · rcases q with p' | m
    · exact (hspec γ hγ.1).1.2.2.2 p' _ (TorusLift.map_lift hπ _) c'
    · exact (hspec γ hγ.1).2 m _ (TorusLift.map_lift hπ _) c'
  intro a ha b' hb hab
  have hD : (minusDatum n hirr).divisible = ∅ := rfl
  have hli : LinIndepPair a b' := by
    by_contra h
    rcases eq_or_eq_neg_of_not_linIndepPair (minusDatum n hirr).isFiniteType hD ha.1 hb.1 h with
      h | h
    · exact hab h.symm
    · have h2 := hb.2
      rw [h] at h2
      have : ht (-a) = -ht a := by simp [ht, Finset.sum_neg_distrib]
      rw [this] at h2
      linarith [ha.2]
  obtain ⟨hne, hne'⟩ := SpinOddClosed.toStdB_ne_of_linIndepPair hli
  rcases sep_or_comm_four hirr hcen hπ hK hn4 hspec ha.1 hb.1 ha.2 hb.2 hne hne' with
    ⟨q, hq1, hq2⟩ | ⟨m, hm1', hm2⟩ | hcomm
  · exact Or.inl ⟨.inl q, show algebraMap K (ShortField b c) (chi q a) = 1 by rw [hq1, map_one],
      fun h => hq2 (hι _ (show algebraMap K (ShortField b c) (chi q b') = 1 from h))⟩
  · exact Or.inl ⟨.inr m, hm1', hm2⟩
  · right
    intro t c'
    rw [hcomm t c', mul_inv_cancel_right]
    exact Subgroup.mem_iSup_of_mem b' (Subgroup.mem_iSup_of_mem ⟨hb, Or.inl rfl⟩
      (CFSG.LieType.Steinberg.xh_mem_chevRoot b' c'))

include hirr in
theorem spinMinus_three_exists_section_of_central'
    [Finite K] (hK : Nat.card K = 3)
    (hn4 : 4 ≤ n) {E : Type} [Group E] [Finite E] {π : E →* spinGroup (quadMinus n K b c)}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : spinGroup (quadMinus n K b c) →* E, ∀ g, π (s g) = g := by
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := K)
  exact CoprimeSplit.exists_section_of_parts (p := p) hπ hcen
    (fun _ _ _ _ hπ' hcen' hp' =>
      spinMinus_three_exists_section_of_pKernel' hirr hK hn4 hπ' hcen' hp')
    (fun _ _ _ _ hπ' hcen' hc' => spinMinus_exists_section_of_coprime hirr hn4 hπ' hcen' hc')

theorem pomegaMinus_three_hopfMultiplier'
    [Finite K] {p f : ℕ} (hn4 : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = p ^ f) (hK3 : Nat.card K = 3) :
    commutator (StatedProj (StatedOmega (StatedQuadMinus n K b c))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier
        (StatedProj (StatedOmega (StatedQuadMinus n K b c))) ≃*
          Multiplicative (ZMod (Nat.gcd 4 ((p ^ f) ^ n + 1)))) := by
  set q := spinToStatedProj (quadMinus n K b c) (range_spinMatrix_quadMinus hn4 hirr)
  obtain ⟨hq, hkerZ, hker⟩ := spinToStatedProj_quadMinus (K := K) hn4 hirr
  have : Group.IsPerfect (spinGroup (quadMinus n K b c)) := isPerfect_spinGroup_quadMinus hn4 hirr
  have hperf : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadMinus n K b c))) :=
    Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have : Finite (CFSG.RankThree.PerfectCover.HopfCover
      (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) :=
    CFSG.RankThree.PerfectCover.finite_hopfCover hperf
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedOmega (StatedQuadMinus n K b c))) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq hker.le
      fun π hπ hcen => spinMinus_three_exists_section_of_central' hirr hK3 hn4 hπ hcen)
  obtain ⟨hcard, hcyc⟩ := card_scalarSpinM hirr hn4 hK
  rw [← hcard]
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((MulEquiv.subgroupCongr hkerZ).trans (zmodCyclicMulEquiv hcyc).symm))⟩

end CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed
