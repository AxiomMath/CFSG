module

public import CFSG.LieType.Steinberg.CentralExt.SpinOddThree
public import CFSG.LieType.Steinberg.CentralExt.PosLiftGen
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCenter
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.SpinOdd (IsRootVec IsShort isShort_single elt elt_of_isLong
  elt_of_isShort)
open CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed (exists_ne_three single_add_single_apply_of_ne'
  neg_one_zpow_boolSign negPair negPair_swap single_add_single_add_not two_mul_boolSign
  not_isLong_single_two swapPair swapPair_swap not_isLong_add_disjoint)
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.TorusLift

attribute [local instance] centerCommGroup

variable {E K : Type*} [Group E] [Group K] {π : E →* K} (hcen : π.ker ≤ Subgroup.center E)
  (hπ : Function.Surjective π) {k : Type*} [Field k] {x : k → K}
  (hx : ∀ s t, x (s + t) = x s * x t)

theorem commPairing_map {g : K} {σ : k → k} (hg : ∀ s, g * x s * g⁻¹ = x (σ s)) (s t : k) :
    commPairing hcen hπ hx (σ s) (σ t) = commPairing hcen hπ hx s t := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [commPairing_apply, commPairing_apply]
  set g' := lift hπ g
  rw [commutatorElement_eq_of_map_eq hcen
      (show π (lift hπ (x (σ s))) = π (g' * lift hπ (x s) * g'⁻¹) by
        rw [map_mul, map_mul, map_inv, map_lift, map_lift, map_lift, hg])
      (show π (lift hπ (x (σ t))) = π (g' * lift hπ (x t) * g'⁻¹) by
        rw [map_mul, map_mul, map_inv, map_lift, map_lift, map_lift, hg]),
    ← conjugate_commutatorElement]
  have hc := Subgroup.mem_center_iff.1 (hcen (commLift_mem_ker hπ hx s t)) g'
  rw [hc, mul_inv_cancel_right]

end CFSG.LieType.Steinberg.CentralExt.TorusLift

namespace CFSG.LieType.Steinberg.CentralExt.SpinOddClosed

variable {n : ℕ} {K : Type} [Field K]

theorem sep_or_swap (h2 : (2 : K) ≠ 0) (hn4 : 4 ≤ n) {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (F : HypFrame Q n) {γ δ : Fin n → ℤ} (hγ : IsRootVec (toStdB n γ))
    (hδ : IsRootVec (toStdB n δ)) (hne : toStdB n δ ≠ toStdB n γ)
    (hne' : toStdB n δ ≠ -toStdB n γ) :
    (∃ p : TorIdx n K, chi p γ = 1 ∧ chi p δ ≠ 1) ∨
      (IsLong (toStdB n γ) ∧ IsLong (toStdB n δ) ∧ ¬IsLong (toStdB n γ + toStdB n δ) ∧
        toStdB n γ + toStdB n δ ≠ 0 ∧ ∃ (g : spinGroup Q) (a : K), a * a = 1 ∧
          (∀ c, g * rootElt F (toStdB n γ) c * g⁻¹ = rootElt F (toStdB n δ) (a * c)) ∧
          ∀ c, g * rootElt F (toStdB n δ) c * g⁻¹ = rootElt F (toStdB n γ) (a * c)) := by
  have hn : 3 ≤ n := by omega
  have hm1 := neg_one_ne_one_of_two h2
  have hbs : ∀ u : Bool, boolSign u = boolSign true ∨ boolSign u = boolSign false := fun u => by
    cases u <;> simp
  rcases hγ with ⟨i, j, hij, s, t, he⟩ | ⟨i, s, he⟩ <;>
    rcases hδ with ⟨k, l, hkl, u, v, he'⟩ | ⟨k, u, he'⟩
  ·
    have hγl : IsLong (toStdB n γ) := by rw [he]; exact isLong_single_add_single hij s t
    have hS : ∀ x, x ≠ i → x ≠ j → toStdB n γ x = 0 := fun x hxi hxj => by
      rw [he, single_add_single_apply_of_ne' hxi hxj]
    by_cases hk : k ≠ i ∧ k ≠ j
    · by_cases hl : l ≠ i ∧ l ≠ j
      ·
        right
        have hδl : IsLong (toStdB n δ) := by rw [he']; exact isLong_single_add_single hkl u v
        obtain ⟨a, ha, h1, h2'⟩ := swapPair_swap F hij hk.1.symm hl.1.symm hk.2.symm hl.2.symm
          hkl s t u v
        rw [← he, ← he'] at h1 h2'
        refine ⟨hγl, hδl, ?_, ?_, _, a, ha, h1, h2'⟩
        · rw [he, he']
          exact not_isLong_add_disjoint hij hk.1.symm hl.1.symm hk.2.symm hl.2.symm hkl s t u v
        · rw [he, he']
          intro h0
          have := congrFun h0 i
          simp [hij, hk.1.symm, hl.1.symm, boolSign] at this
          cases s <;> simp at this
      · have hl' : l = i ∨ l = j := by tauto
        obtain ⟨m, hmi, hmj, hmk⟩ := exists_ne_three hn4 i j k
        refine Or.inl (exists_sep_out h2 hS (l := l) ?_ (fun x hxk hxl => ?_) hk.1 hk.2
          ⟨m, hmi, hmj, hmk, by rcases hl' with rfl | rfl <;> assumption⟩)
        · rw [he', single_add_single_apply_left hkl]
          exact hbs u
        · rw [he', single_add_single_apply_of_ne' hxk hxl]
    by_cases hl : l ≠ i ∧ l ≠ j
    · have hk' : k = i ∨ k = j := by tauto
      obtain ⟨m, hmi, hmj, hml⟩ := exists_ne_three hn4 i j l
      refine Or.inl (exists_sep_out h2 hS (l := k) ?_ (fun x hxl hxk => ?_) hl.1 hl.2
        ⟨m, hmi, hmj, hml, by rcases hk' with rfl | rfl <;> assumption⟩)
      · rw [he', single_add_single_apply_right hkl]
        exact hbs v
      · rw [he', single_add_single_apply_of_ne' hxk hxl]
    right
    obtain ⟨u', v', he''⟩ : ∃ u' v' : Bool,
        toStdB n δ = Pi.single i (boolSign u') + Pi.single j (boolSign v') := by
      have hk' : k = i ∨ k = j := by tauto
      have hl' : l = i ∨ l = j := by tauto
      rcases hk' with rfl | rfl <;> rcases hl' with rfl | rfl
      · exact absurd rfl hkl
      · exact ⟨u, v, he'⟩
      · exact ⟨v, u, by rw [he', add_comm]⟩
      · exact absurd rfl hkl
    obtain ⟨m, hmi, hmj⟩ := exists_ne_and_ne hn i j
    have hδl : IsLong (toStdB n δ) := by rw [he'']; exact isLong_single_add_single hij u' v'
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
    refine ⟨hγl, hδl, ?_⟩
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨a, ha, h1, h2'⟩ := negPair_swap F hij hmi hmj u' t
      rw [← he, ← he''] at h1 h2'
      refine ⟨?_, ?_, _, a, ha, h1, h2'⟩
      · rw [he, he'', single_add_single_add_not]
        exact not_isLong_single_two (two_mul_boolSign u')
      · rw [he, he'', single_add_single_add_not]
        intro h0
        have := congrFun h0 i
        rw [Pi.single_eq_same, Pi.zero_apply] at this
        rcases two_mul_boolSign u' with h' | h' <;> omega
    · obtain ⟨a, ha, h1, h2'⟩ := negPair_swap F hij.symm hmj hmi v' s
      have ehe : toStdB n γ = Pi.single j (boolSign v') + Pi.single i (boolSign s) := by
        rw [he, add_comm]
      have ehe' : toStdB n δ = Pi.single j (boolSign v') + Pi.single i (boolSign (!s)) := by
        rw [he'', add_comm]
      rw [← ehe, ← ehe'] at h1 h2'
      refine ⟨?_, ?_, _, a, ha, h1, h2'⟩
      · rw [ehe, ehe', single_add_single_add_not]
        exact not_isLong_single_two (two_mul_boolSign v')
      · rw [ehe, ehe', single_add_single_add_not]
        intro h0
        have := congrFun h0 j
        rw [Pi.single_eq_same, Pi.zero_apply] at this
        rcases two_mul_boolSign v' with h' | h' <;> omega
  ·
    have hS : ∀ x, x ≠ i → x ≠ j → toStdB n γ x = 0 := fun x hxi hxj => by
      rw [he, single_add_single_apply_of_ne' hxi hxj]
    by_cases hk : k ≠ i ∧ k ≠ j
    · obtain ⟨m, hmi, hmj, hmk⟩ := exists_ne_three hn4 i j k
      refine Or.inl (exists_sep_out h2 hS (l := k) ?_ (fun x hxk _ => ?_) hk.1 hk.2
        ⟨m, hmi, hmj, hmk, hmk⟩)
      · rw [he', Pi.single_eq_same]
        exact hbs u
      · rw [he', Pi.single_eq_of_ne hxk]
    · left
      refine ⟨.long i j hij true true (-1), ?_, ?_⟩
      · rw [chi_long_neg_one, he, SpinTorus.single_add_single_dotProduct,
          single_add_single_apply_left hij, single_add_single_apply_right hij, mul_one, mul_one,
          neg_one_zpow_boolSign_add, Units.val_one]
      · rw [chi_long_neg_one, he', single_dotProduct]
        have hk' : k = i ∨ k = j := by tauto
        rcases hk' with rfl | rfl
        · rw [single_add_single_apply_left hij, mul_one, neg_one_zpow_boolSign]
          exact hm1
        · rw [single_add_single_apply_right hij, mul_one, neg_one_zpow_boolSign]
          exact hm1
  ·
    have hS : ∀ x, x ≠ i → x ≠ i → toStdB n γ x = 0 := fun x hxi _ => by
      rw [he, Pi.single_eq_of_ne hxi]
    by_cases hk : k ≠ i
    · obtain ⟨m, hmi, hmk, hml⟩ := exists_ne_three hn4 i k l
      refine Or.inl (exists_sep_out h2 hS (l := l) ?_ (fun x hxk hxl => ?_) hk hk
        ⟨m, hmi, hmi, hmk, hml⟩)
      · rw [he', single_add_single_apply_left hkl]
        exact hbs u
      · rw [he', single_add_single_apply_of_ne' hxk hxl]
    · push Not at hk
      subst hk
      obtain ⟨m, hmk, hml, -⟩ := exists_ne_three hn4 k l l
      refine Or.inl (exists_sep_out h2 hS (l := k) ?_ (fun x hxl hxk => ?_) hkl.symm hkl.symm
        ⟨m, hmk, hmk, hml, hmk⟩)
      · rw [he', single_add_single_apply_right hkl]
        exact hbs v
      · rw [he', single_add_single_apply_of_ne' hxk hxl]
  ·
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
    · have hS : ∀ x, x ≠ i → x ≠ i → toStdB n γ x = 0 := fun x hxi _ => by
        rw [he, Pi.single_eq_of_ne hxi]
      obtain ⟨m, hmi, hmk, -⟩ := exists_ne_three hn4 i k k
      refine Or.inl (exists_sep_out h2 hS (l := k) ?_ (fun x hxk _ => ?_) hk hk
        ⟨m, hmi, hmi, hmk, hmk⟩)
      · rw [he', Pi.single_eq_same]
        exact hbs u
      · rw [he', Pi.single_eq_of_ne hxk]

end CFSG.LieType.Steinberg.CentralExt.SpinOddClosed

namespace CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed

attribute [local instance] TorusLift.centerCommGroup

open SpinOddClosed (TorIdx chi)
open QuadraticAlgebra

variable {n : ℕ} {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] def negStar (t : ShortField b c) : ShortField b c := ⟨-(t.re + b * t.im), t.im⟩

theorem fieldCoord_negStar (t : ShortField b c) :
    fieldCoord (negStar t) = planeRefl b c planeOne (fieldCoord t) := by
  rw [planeRefl, planeNorm_planeOne, div_one]
  ext k
  fin_cases k <;> simp [fieldCoord, negStar, polarPlane, planeOne]
  ring

theorem pairing_eq_zero_of_negStar [Finite K] (hK : Nat.card K = 3) {A : Type*} [AddCommGroup A]
    (P : ShortField b c →+ ShortField b c →+ A) (hP0 : ∀ s, P s s = 0)
    (hσ : ∀ s t, P (negStar s) (negStar t) = P s t) : P = 0 := by
  have h3 : (3 : K) = 0 := WeylLift.three_eq_zero hK
  have hsmul : ∀ (r : K) x y, P x y = 0 → P (r • x) y = 0 := fun r x y h => by
    rcases WeylLift.eq_zero_or_one_or_neg_one hK r with rfl | rfl | rfl
    · rw [zero_smul, map_zero, AddMonoidHom.zero_apply]
    · rw [one_smul, h]
    · rw [neg_smul, one_smul, map_neg, AddMonoidHom.neg_apply, h, neg_zero]
  have hsmul' : ∀ (r : K) x y, P x y = 0 → P x (r • y) = 0 := fun r x y h => by
    rcases WeylLift.eq_zero_or_one_or_neg_one hK r with rfl | rfl | rfl
    · rw [zero_smul, map_zero]
    · rw [one_smul, h]
    · rw [neg_smul, one_smul, map_neg, h, neg_zero]
  have hσ1 : negStar (1 : ShortField b c) = -1 := by
    ext <;> simp [negStar]
  have hσω : negStar (QuadraticAlgebra.omega : ShortField b c) = QuadraticAlgebra.omega - b • 1 := by
    ext <;> simp [negStar]
  have h1b : P 1 (b • 1) = 0 := hsmul' b 1 1 (hP0 1)
  have hneg : P 1 QuadraticAlgebra.omega = -P 1 QuadraticAlgebra.omega := by
    have h := hσ 1 QuadraticAlgebra.omega
    rw [hσ1, hσω, map_neg, AddMonoidHom.neg_apply, map_sub, h1b, sub_zero] at h
    exact h.symm
  have h111 : (1 : ShortField b c) + 1 + 1 = 0 := by
    ext
    · simp only [re_add, re_one, re_zero]
      linear_combination h3
    · simp
  have h1ω : P 1 QuadraticAlgebra.omega = 0 := by
    have h := congrArg (fun z => P z QuadraticAlgebra.omega) h111
    simp only [map_add, AddMonoidHom.add_apply, map_zero, AddMonoidHom.zero_apply] at h
    have h2 : P 1 QuadraticAlgebra.omega + P 1 QuadraticAlgebra.omega = 0 := by
      nth_rewrite 2 [hneg]
      exact add_neg_cancel _
    rw [h2, zero_add] at h
    exact h
  have hω1 : P QuadraticAlgebra.omega 1 = 0 := by
    have h := hP0 (1 + QuadraticAlgebra.omega)
    simp only [map_add, AddMonoidHom.add_apply, hP0, h1ω, zero_add, add_zero] at h
    exact h
  have hbase : ∀ x ∈ ({1, QuadraticAlgebra.omega} : Set (ShortField b c)),
      ∀ y ∈ ({1, QuadraticAlgebra.omega} : Set (ShortField b c)), P x y = 0 := by
    rintro x (rfl | rfl) y (rfl | rfl)
    · exact hP0 1
    · exact h1ω
    · exact hω1
    · exact hP0 QuadraticAlgebra.omega
  refine AddMonoidHom.ext fun s => AddMonoidHom.ext fun t => ?_
  rw [← re_smul_add_im_smul s, ← re_smul_add_im_smul t]
  simp only [map_add, AddMonoidHom.add_apply, AddMonoidHom.zero_apply]
  have h1 : (1 : ShortField b c) ∈ ({1, QuadraticAlgebra.omega} : Set (ShortField b c)) := Or.inl rfl
  have hω : (QuadraticAlgebra.omega : ShortField b c) ∈ ({1, QuadraticAlgebra.omega} : Set (ShortField b c)) := Or.inr rfl
  rw [hsmul _ _ _ (hsmul' _ _ _ (hbase _ h1 _ h1)), hsmul _ _ _ (hsmul' _ _ _ (hbase _ h1 _ hω)),
    hsmul _ _ _ (hsmul' _ _ _ (hbase _ hω _ h1)), hsmul _ _ _ (hsmul' _ _ _ (hbase _ hω _ hω))]

theorem shortWeyl_conj_x {i k : Fin (n - 1)} (hik : i ≠ k) {γ : Fin (n - 1) → ℤ} {u : Bool}
    (h : toStdB (n - 1) γ = Pi.single k (boolSign u)) (t : ShortField b c) :
    shortWeyl n hirr i * x hirr γ t * (shortWeyl n hirr i)⁻¹ = x hirr γ (negStar t) := by
  rw [x_of_short hirr h, x_of_short hirr h, shortWeyl_conj_twShortRoot, fieldCoord_negStar,
    longWeylSign_of_ne hik.symm, one_smul]
  congr 1
  simp [shortWeylBool, hik.symm]

variable {E : Type*} [Group E] {π : E →* spinGroup (quadMinus n K b c)}
  (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)

include hcen in
theorem commPairing_eq_zero_short_three [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] [Finite K]
    (hK : Nat.card K = 3) (hn : 4 ≤ n)
    {γ : Fin (n - 1) → ℤ} {k : Fin (n - 1)} {u : Bool}
    (h : toStdB (n - 1) γ = Pi.single k (boolSign u)) :
    TorusLift.commPairing hcen hπ (x_add hirr γ) = 0 := by
  obtain ⟨i, hik, -⟩ := exists_ne_and_ne (show 3 ≤ n - 1 by omega) k k
  exact pairing_eq_zero_of_negStar hK _ (TorusLift.commPairing_self hcen hπ (x_add hirr γ))
    (TorusLift.commPairing_map hcen hπ (x_add hirr γ) (shortWeyl_conj_x hirr hik h))

omit hcen in
theorem X_eq_algebraMap_re {γ : Fin (n - 1) → ℤ} (hγ : IsRootLift hirr π γ (X hirr π γ))
    (hl : IsLong (toStdB (n - 1) γ)) (s : ShortField b c) :
    X hirr π γ s = X hirr π γ (algebraMap K (ShortField b c) s.re) := by
  have h := hγ.1 (algebraMap K (ShortField b c) s.re) (s - algebraMap K (ShortField b c) s.re)
  rw [add_sub_cancel] at h
  rw [h, hγ.2.2.1 (s - algebraMap K (ShortField b c) s.re) ?_, mul_one]
  rw [x_of_isLong hirr hl, re_sub, algebraMap_re, sub_self, elt_of_isLong _ hl, rootElt_zero]

include hcen hπ in
theorem commute_X_of_swap [Finite K] (hK : Nat.card K = 3) {γ δ : Fin (n - 1) → ℤ}
    (hγ : IsRootLift hirr π γ (X hirr π γ)) (hδ : IsRootLift hirr π δ (X hirr π δ))
    (hγl : IsLong (toStdB (n - 1) γ)) (hδl : IsLong (toStdB (n - 1) δ))
    (hl : ¬IsLong (toStdB (n - 1) γ + toStdB (n - 1) δ))
    (h0 : toStdB (n - 1) γ + toStdB (n - 1) δ ≠ 0) {g : spinGroup (quadMinus n K b c)} {a : K}
    (ha : a * a = 1)
    (h1 : ∀ d, g * rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) γ) d * g⁻¹ =
      rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) δ) (a * d))
    (h2 : ∀ d, g * rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) δ) d * g⁻¹ =
      rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) γ) (a * d)) (s t : ShortField b c) :
    X hirr π γ s * X hirr π δ t = X hirr π δ t * X hirr π γ s := by
  have hx : ∀ {e : Fin (n - 1) → ℤ}, IsLong (toStdB (n - 1) e) → ∀ r : K,
      x hirr e (algebraMap K (ShortField b c) r) =
        rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) e) r := fun hel r => by
    rw [x_of_isLong hirr hel, algebraMap_re, elt_of_isLong _ hel]
  rw [X_eq_algebraMap_re hirr hγ hγl, X_eq_algebraMap_re hirr hδ hδl]
  exact WeylLift.commute_of_swap_lift hK hcen hπ
    (x := rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) γ))
    (x₁ := rootElt (minusFrame n b c).toHypFrame (toStdB (n - 1) δ))
    (Y := fun r => X hirr π γ (algebraMap K (ShortField b c) r))
    (Y₁ := fun r => X hirr π δ (algebraMap K (ShortField b c) r))
    (fun r r' => (congrArg (X hirr π γ) (map_add _ r r')).trans (hγ.1 _ _))
    (fun r r' => (congrArg (X hirr π δ) (map_add _ r r')).trans (hδ.1 _ _))
    (fun r => (hγ.2.1 _).trans (hx hγl r)) (fun r => (hδ.2.1 _).trans (hx hδl r))
    (fun r r' => (commute_rootElt (minusFrame n b c).toHypFrame hγl hδl h0 hl r r').eq) ha h1 h2
    _ _

include hirr in
theorem spinMinus_three_exists_section_of_pKernel [Finite K] (hK : Nat.card K = 3) (hn5 : 5 ≤ n)
    {p : ℕ} [Fact p.Prime] [CharP K p] {E : Type*} [Group E] [Finite E]
    {π : E →* spinGroup (quadMinus n K b c)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    ∃ s : spinGroup (quadMinus n K b c) →* E, ∀ g, π (s g) = g := by
  have hn : 4 ≤ n := by omega
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : Finite (spinGroup (quadMinus n K b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have h2 : (2 : K) ≠ 0 := FieldThree.two_ne_zero_of_card_three hK
  have hm1 := SpinOddClosed.neg_one_ne_one_of_two h2
  have hι : ∀ r : K, algebraMap K (ShortField b c) r = 1 → r = 1 := fun r h => by
    rw [← map_one (algebraMap K (ShortField b c))] at h
    exact (algebraMap K (ShortField b c)).injective h
  have hspec : ∀ γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅, IsRootLift hirr π γ (X hirr π γ) := by
    intro γ hγ
    have h0 : TorusLift.commPairing hcen hπ (x_add hirr γ) = 0 := by
      rcases SpinOddClosed.isRootVec_of_mem hγ with hl | ⟨k, u, he⟩
      · exact commPairing_eq_zero_long hirr hcen hπ hn hl
      · exact commPairing_eq_zero_short_three hirr hcen hπ hK hn he
    obtain ⟨p₀, hp₀⟩ : ∃ p₀ : TorIdx (n - 1) K, chi p₀ γ ≠ 1 := by
      rcases SpinOddClosed.isRootVec_of_mem hγ with ⟨i, j, hij, s, t, he⟩ | ⟨i, s, he⟩
      · obtain ⟨m, hmi, hmj⟩ := exists_ne_and_ne (show 3 ≤ n - 1 by omega) i j
        refine ⟨.long i m hmi.symm true true (-1), ?_⟩
        rw [SpinOddClosed.chi_long_neg_one, he, SpinTorus.single_add_single_dotProduct,
          single_add_single_apply_left hmi.symm, single_add_single_apply_of_ne' hij.symm hmj.symm,
          mul_one, mul_zero, add_zero, neg_one_zpow_boolSign]
        exact hm1
      · obtain ⟨m, hmi, -⟩ := exists_ne_and_ne (show 3 ≤ n - 1 by omega) i i
        refine ⟨.long i m hmi.symm true true (-1), ?_⟩
        rw [SpinOddClosed.chi_long_neg_one, he, single_dotProduct,
          single_add_single_apply_left hmi.symm, mul_one, neg_one_zpow_boolSign]
        exact hm1
    exact X_isRootLift hirr (exists_isRootLift hirr hcen hπ hγ h0 fun h => hp₀ (hι _ h))
  refine PosLift.exists_section_of_posLift' (minusDatum_isCTGroupDatum n hirr hn)
    (minusDatum_steinbergExtras n hirr) (bruhatExtras hirr hn) rfl (p := p)
    (fun γ hγ => isPGroup_minusRootGroup hirr hγ) (coprime_card_torus hirr) hπ hcen hpk
    (x := x hirr) (fun γ hγ g => ⟨fun hg => exists_x_eq_of_mem hirr hγ.1 hg,
      fun ⟨t, ht⟩ => ht ▸ x_mem hirr hγ.1 t⟩)
    (fun γ _ => x_add hirr γ) (X := X hirr π) (fun γ hγ => (hspec γ hγ.1).1)
    (fun γ hγ => (hspec γ hγ.1).2.1) (fun γ hγ => (hspec γ hγ.1).2.2.1)
    (tor := fun p => TorusLift.lift hπ (tor p))
    (χ := fun p γ => algebraMap K (ShortField b c) (chi p γ))
    (fun p γ hγ c' => (hspec γ hγ.1).2.2.2 p _ (TorusLift.map_lift hπ _) c') ?_
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
  rcases SpinOddClosed.sep_or_swap h2 (show 4 ≤ n - 1 by omega) (minusFrame n b c).toHypFrame
      (SpinOddClosed.isRootVec_of_mem ha.1) (SpinOddClosed.isRootVec_of_mem hb.1) hne hne' with
    ⟨j, hj1, hj2⟩ | ⟨hγl, hδl, hl, h0, g, a', ha', h1, h2'⟩
  · exact Or.inl ⟨j, by rw [hj1, map_one], fun h => hj2 (hι _ h)⟩
  · right
    intro t c'
    rw [commute_X_of_swap hirr hcen hπ hK (hspec a ha.1) (hspec b' hb.1) hγl hδl hl h0 ha' h1 h2' t
      c', mul_inv_cancel_right]
    exact Subgroup.mem_iSup_of_mem b' (Subgroup.mem_iSup_of_mem ⟨hb, Or.inl rfl⟩
      (CFSG.LieType.Steinberg.xh_mem_chevRoot b' c'))

include hirr in
theorem spinMinus_three_exists_section_of_central
    [Finite K] (hK : Nat.card K = 3)
    (hn5 : 5 ≤ n) {E : Type} [Group E] [Finite E] {π : E →* spinGroup (quadMinus n K b c)}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : spinGroup (quadMinus n K b c) →* E, ∀ g, π (s g) = g := by
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := K)
  exact CoprimeSplit.exists_section_of_parts (p := p) hπ hcen
    (fun _ _ _ _ hπ' hcen' hp' =>
      spinMinus_three_exists_section_of_pKernel hirr hK hn5 hπ' hcen' hp')
    (fun _ _ _ _ hπ' hcen' hc' =>
      spinMinus_exists_section_of_coprime hirr (by omega) hπ' hcen' hc')

theorem pomegaMinus_three_hopfMultiplier
    [Finite K] {p f : ℕ} (hn5 : 5 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = p ^ f) (hK3 : Nat.card K = 3) :
    commutator (StatedProj (StatedOmega (StatedQuadMinus n K b c))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier
        (StatedProj (StatedOmega (StatedQuadMinus n K b c))) ≃*
          Multiplicative (ZMod (Nat.gcd 4 ((p ^ f) ^ n + 1)))) := by
  have hn : 4 ≤ n := by omega
  set q := spinToStatedProj (quadMinus n K b c) (range_spinMatrix_quadMinus hn hirr)
  obtain ⟨hq, hkerZ, hker⟩ := spinToStatedProj_quadMinus (K := K) hn hirr
  have : Group.IsPerfect (spinGroup (quadMinus n K b c)) := isPerfect_spinGroup_quadMinus hn hirr
  have hperf : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadMinus n K b c))) :=
    Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have : Finite (CFSG.RankThree.PerfectCover.HopfCover
      (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) :=
    CFSG.RankThree.PerfectCover.finite_hopfCover hperf
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedOmega (StatedQuadMinus n K b c))) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq hker.le
      fun π hπ hcen => spinMinus_three_exists_section_of_central hirr hK3 hn5 hπ hcen)
  obtain ⟨hcard, hcyc⟩ := card_scalarSpinM hirr hn hK
  rw [← hcard]
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((MulEquiv.subgroupCongr hkerZ).trans (zmodCyclicMulEquiv hcyc).symm))⟩

end CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed
