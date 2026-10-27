module

public import CFSG.ClassicalGroups.Orthogonal.Restrict
public import CFSG.ClassicalInvolution.RouteD.TWYPlane
public import CFSG.ClassicalInvolution.RouteD.TWYType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors
import CFSG.ClassicalGroups.Orthogonal.PolarPairPlane

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap Module CFSG.GroupTheory.WeirSylow CFSG.RankThree.PartOne.KCOrthogonal

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def IsAnisoPair (Q : QuadraticForm F V) (a b : V) : Prop :=
  polar Q a b = 1 ∧ ∀ s t : F, Q (s • a + t • b) = 0 → s = 0 ∧ t = 0

structure PairOrth (Q : QuadraticForm F V) (a b c d : V) : Prop where
  ac : polar Q a c = 0
  ad : polar Q a d = 0
  bc : polar Q b c = 0
  bd : polar Q b d = 0

theorem PairOrth.symm {Q : QuadraticForm F V} {a b c d : V} (h : PairOrth Q a b c d) :
    PairOrth Q c d a b where
  ac := by rw [polar_comm]; exact h.ac
  ad := by rw [polar_comm]; exact h.bc
  bc := by rw [polar_comm]; exact h.ad
  bd := by rw [polar_comm]; exact h.bd

theorem PairOrth.of_restrict {Q : QuadraticForm F V} {W : Submodule F V} {a b c d : W}
    (h : PairOrth (Q.restrict W) a b c d) : PairOrth Q (a : V) b c d where
  ac := by have := h.ac; rwa [polar_restrict] at this
  ad := by have := h.ad; rwa [polar_restrict] at this
  bc := by have := h.bc; rwa [polar_restrict] at this
  bd := by have := h.bd; rwa [polar_restrict] at this

theorem pairOrth_of_mem_orthPerp {Q : QuadraticForm F V} {a b c d : V}
    (hc : c ∈ orthPerp Q (Submodule.span F {a, b})) (hd : d ∈ orthPerp Q (Submodule.span F {a, b})) :
    PairOrth Q a b c d where
  ac := mem_orthPerp.1 hc a (Submodule.subset_span (by simp))
  ad := mem_orthPerp.1 hd a (Submodule.subset_span (by simp))
  bc := mem_orthPerp.1 hc b (Submodule.subset_span (by simp))
  bd := mem_orthPerp.1 hd b (Submodule.subset_span (by simp))

namespace IsAnisoPair

variable {Q : QuadraticForm F V} {a b : V}

theorem linearIndependent_pair (h : IsAnisoPair Q a b) : LinearIndependent F ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  exact h.2 s t (by rw [hst, QuadraticMap.map_zero])

theorem finrank_span_pair (h : IsAnisoPair Q a b) : finrank F (Submodule.span F {a, b}) = 2 := by
  have h1 := finrank_span_eq_card h.linearIndependent_pair
  rw [Fintype.card_fin] at h1
  rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union] at h1

theorem eq_zero_of_mem_span_pair (h : IsAnisoPair Q a b) {x : V}
    (hx : x ∈ Submodule.span F {a, b}) (hQ : Q x = 0) : x = 0 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hx
  obtain ⟨rfl, rfl⟩ := h.2 s t hQ
  simp

theorem polarNondegOn [CharP F 2] (h : IsAnisoPair Q a b) :
    PolarNondegOn Q (Submodule.span F {a, b}) :=
  polarNondegOn_span_pair_of_polar_eq_one h.1

theorem of_restrict {W : Submodule F V} {a b : W} (h : IsAnisoPair (Q.restrict W) a b) :
    IsAnisoPair Q (a : V) b := by
  refine ⟨by have := h.1; rwa [polar_restrict] at this, fun s t hst => h.2 s t ?_⟩
  exact hst

end IsAnisoPair

theorem exists_forall_sq_add_self_ne [Finite F] : ∃ c : F, ∀ z : F, z ^ 2 + z ≠ c := by
  by_contra! h
  have hinj : Function.Injective (fun z : F => z ^ 2 + z) :=
    Finite.injective_iff_surjective.2 fun c => h c
  have h0 : (fun z : F => z ^ 2 + z) 0 = (fun z : F => z ^ 2 + z) (-1) := by simp
  exact one_ne_zero (neg_eq_zero.1 (hinj h0).symm)

theorem exists_map_ne_zero_of_polarNondegOn {Q : QuadraticForm F V} {W : Submodule F V}
    (hW : PolarNondegOn Q W) {u : V} (huW : u ∈ W) (hu : u ≠ 0) : ∃ w ∈ W, Q w ≠ 0 := by
  obtain ⟨v, hvW, hv⟩ := hW.exists_polar_ne_zero huW hu
  by_cases hQu : Q u = 0
  · by_cases hQv : Q v = 0
    · refine ⟨u + v, W.add_mem huW hvW, ?_⟩
      rw [QuadraticMap.map_add Q, hQu, hQv, zero_add, zero_add]
      exact hv
    · exact ⟨v, hvW, hQv⟩
  · exact ⟨u, huW, hQu⟩

theorem HypPair.finrank_perp_add_two [FiniteDimensional F V] {Q : QuadraticForm F V} (P : HypPair Q) :
    finrank F P.perp + 2 = finrank F V := by
  let φ : V →ₗ[F] F × F := (polarBilin Q P.e).prod (polarBilin Q P.f)
  have hker : LinearMap.ker φ = P.perp := LinearMap.ker_prod _ _
  have hrange : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨s, t⟩
    refine ⟨s • P.f + t • P.e, Prod.ext ?_ ?_⟩
    · show polar Q P.e (s • P.f + t • P.e) = s
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ef, P.polar_ee]
      ring
    · show polar Q P.f (s • P.f + t • P.e) = t
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ff, P.polar_fe]
      ring
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hker, hrange, finrank_top, Module.finrank_prod, Module.finrank_self] at h
  omega

private theorem exists_isAnisoPair_aux1 [Finite F] [CharP F 2] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    (hWd : 2 ≤ finrank F P.perp) :
    ∃ w w' : V, w ∈ P.perp ∧ Q w ≠ 0 ∧ w' ∈ P.perp ∧ polar Q w w' = 1 ∧
      polar Q w P.e = 0 ∧ polar Q w P.f = 0 ∧ polar Q w' P.e = 0 ∧ polar Q w' P.f = 0 := by
  have hW : PolarNondegOn Q P.perp := P.polarNondegOn_perp hQ
  obtain ⟨u, huW, hu0⟩ : ∃ u ∈ P.perp, u ≠ 0 := by
    obtain ⟨⟨u, huW⟩, hu⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by omega : 0 < finrank F P.perp)
    exact ⟨u, huW, fun h => hu (Subtype.ext h)⟩
  obtain ⟨w, hwW, hQw⟩ := exists_map_ne_zero_of_polarNondegOn hW huW hu0
  have hw0 : w ≠ 0 := fun h => hQw (by rw [h, QuadraticMap.map_zero])
  obtain ⟨w₁, hw₁W, hw₁⟩ := hW.exists_polar_ne_zero hwW hw0
  have hw'W : (polar Q w w₁)⁻¹ • w₁ ∈ P.perp := P.perp.smul_mem _ hw₁W
  refine ⟨w, (polar Q w w₁)⁻¹ • w₁, hwW, hQw, hw'W, ?_, ?_, ?_, ?_, ?_⟩
  · rw [polar_smul_right_eq, inv_mul_cancel₀ hw₁]
  · rw [polar_comm]; exact (P.mem_perp.1 hwW).1
  · rw [polar_comm]; exact (P.mem_perp.1 hwW).2
  · rw [polar_comm]; exact (P.mem_perp.1 hw'W).1
  · rw [polar_comm]; exact (P.mem_perp.1 hw'W).2

private theorem exists_isAnisoPair_aux2 [CharP F 2] {Q : QuadraticForm F V} {w y : V} {c : F}
    (hc : ∀ z : F, z ^ 2 + z ≠ c) (hwy : polar Q w y = 1) (hQw : Q w ≠ 0)
    (hQy : Q y = c / Q w) : IsAnisoPair Q w y := by
  refine ⟨hwy, fun s t hst => ?_⟩
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hexp : Q (s • w + t • y) = s ^ 2 * Q w + t ^ 2 * (c / Q w) + s * t := by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
      polar_smul_right_eq, hwy, hQy]
    ring
  have key : (s * Q w) ^ 2 + (s * Q w) * t + c * t ^ 2 = 0 := by
    have h0 : Q w * Q (s • w + t • y) = 0 := by rw [hst, mul_zero]
    rw [hexp] at h0
    field_simp at h0
    linear_combination h0
  by_cases ht : t = 0
  · subst ht
    have h1 : s * Q w = 0 := by simpa using key
    exact ⟨(mul_eq_zero.1 h1).resolve_right hQw, rfl⟩
  · exfalso
    apply hc (s * Q w / t)
    field_simp
    linear_combination key - (c * t ^ 2) * h2

theorem exists_isAnisoPair [Finite F] [CharP F 2] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hQ : (polarBilin Q).Nondegenerate) {m : ℕ} (hdim : finrank F V = 2 * m) (hm : 2 ≤ m) :
    ∃ a b : V, IsAnisoPair Q a b := by
  obtain ⟨e, -, he0, heQ⟩ := CFSG.ComponentClassification.UnbalancedCatalog.exists_singular_of_three_le
    (Q := Q) (S := ⊤) (polarNondegOn_top hQ) (by rw [finrank_top]; omega)
  obtain ⟨P, -⟩ := exists_hypPair hQ heQ he0
  have hWd : 2 ≤ finrank F P.perp := by have := P.finrank_perp_add_two; omega
  obtain ⟨w, w', hwW, hQw, hw'W, hww', hwe, hwf, hw'e, hw'f⟩ :=
    exists_isAnisoPair_aux1 hQ P hWd
  obtain ⟨c, hc⟩ := exists_forall_sq_add_self_ne (F := F)
  set δ : F := c / Q w + Q w' with hδ
  set y : V := w' + (P.e + δ • P.f) with hy
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hQz : Q (P.e + δ • P.f) = δ := by
    rw [QuadraticMap.map_add Q, P.Q_e, map_smul_eq_sq, P.Q_f, polar_smul_right_eq, P.polar_ef]
    ring
  have hQy : Q y = c / Q w := by
    have hpz : polar Q w' (P.e + δ • P.f) = 0 := by
      rw [polar_add_right, polar_smul_right_eq, hw'e, hw'f]
      ring
    rw [hy, QuadraticMap.map_add Q, hQz, hpz, hδ]
    linear_combination (Q w') * h2
  have hwy : polar Q w y = 1 := by
    rw [hy, polar_add_right, polar_add_right, hww', hwe, polar_smul_right_eq, hwf]
    ring
  exact ⟨w, y, exists_isAnisoPair_aux2 hc hwy hQw hQy⟩

section Complement

variable {Q : QuadraticForm F V} {a b : V}

theorem IsAnisoPair.isCompl_span_orthPerp [CharP F 2] [FiniteDimensional F V] (h : IsAnisoPair Q a b) :
    IsCompl (Submodule.span F {a, b}) (orthPerp Q (Submodule.span F {a, b})) :=
  isCompl_orthPerp (nondegenerate_polarBilin_restrict h.polarNondegOn)

theorem polarNondegOn_orthPerp [FiniteDimensional F V] (hQ : (polarBilin Q).Nondegenerate)
    {R : Submodule F V} (hR : IsCompl R (orthPerp Q R)) : PolarNondegOn Q (orthPerp Q R) := by
  intro x hx hx'
  apply eq_zero_of_polar_eq_zero hQ
  intro z
  obtain ⟨r, w, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_add_of_isCompl hR z
  rw [polar_add_right, hx' _ w.2, add_zero, polar_comm]
  exact mem_orthPerp.1 hx r r.2

theorem IsAnisoPair.isPlusType_iff_restrict_orthPerp [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (h : IsAnisoPair Q a b) {k : ℕ}
    (hdim : finrank F V = 2 * (k + 2)) :
    IsPlusType Q ↔ ¬ IsPlusType (Q.restrict (orthPerp Q (Submodule.span F {a, b}))) := by
  have hc := h.isCompl_span_orthPerp
  have hWnd := polarNondegOn_orthPerp hQ hc
  have hWd : finrank F (orthPerp Q (Submodule.span F {a, b})) = 2 * (k + 1) := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    rw [h.finrank_span_pair] at this
    omega
  have hU : ¬ IsPlusType (Q.restrict (Submodule.span F {a, b})) := by
    rw [CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_restrict_iff_of_finrank_two h.finrank_span_pair]
    rintro ⟨w, hw, hw0, hQw⟩
    exact hw0 (h.eq_zero_of_mem_span_pair hw hQw)
  rw [CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_iff_of_isCompl hc
    (fun x hx y hy => mem_orthPerp.1 hy x hx) h.polarNondegOn hWnd (a := 1) (b := k + 1) le_rfl
    (by omega) (by rw [h.finrank_span_pair]) hWd]
  tauto

end Complement

private theorem exists_anisoPairFrame_aux1 [Finite F] [CharP F 2] :
    ∀ {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V},
      (polarBilin Q).Nondegenerate → finrank F V = 2 * (0 + 1) → (IsPlusType Q ↔ Even 0) →
      ∃ (a b : Fin 0 → V) (e f : V), (∀ i, IsAnisoPair Q (a i) (b i)) ∧
        (∀ i j, i ≠ j → PairOrth Q (a i) (b i) (a j) (b j)) ∧ Q e = 0 ∧ Q f = 0 ∧ polar Q e f = 1 ∧
        ∀ i, PairOrth Q e f (a i) (b i) := by
  intro V _ _ _ Q hQ _ hplus
  obtain ⟨S, hS, hSQ⟩ := hplus.2 ⟨0, rfl⟩
  obtain ⟨⟨e, heS⟩, he⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by omega : 0 < finrank F S)
  obtain ⟨P, -⟩ := exists_hypPair hQ (hSQ e heS) (fun h => he (Subtype.ext h))
  exact ⟨Fin.elim0, Fin.elim0, P.e, P.f, fun i => i.elim0, fun i => i.elim0, P.Q_e, P.Q_f,
    P.polar_ef, fun i => i.elim0⟩

private theorem exists_anisoPairFrame_aux2 [Finite F] [CharP F 2] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hQ : (polarBilin Q).Nondegenerate) {k : ℕ} {a₀ b₀ : V}
    (h₀ : IsAnisoPair Q a₀ b₀) (hdim : finrank F V = 2 * ((k + 1) + 1))
    (hplus : IsPlusType Q ↔ Even (k + 1)) :
    finrank F (orthPerp Q (Submodule.span F {a₀, b₀})) = 2 * (k + 1) ∧
      (IsPlusType (Q.restrict (orthPerp Q (Submodule.span F {a₀, b₀}))) ↔ Even k) := by
  have hc := h₀.isCompl_span_orthPerp
  have hWd : finrank F (orthPerp Q (Submodule.span F {a₀, b₀})) = 2 * (k + 1) := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    rw [h₀.finrank_span_pair] at this
    omega
  have hWtype : IsPlusType (Q.restrict (orthPerp Q (Submodule.span F {a₀, b₀}))) ↔ Even k := by
    have h1 := h₀.isPlusType_iff_restrict_orthPerp hQ (k := k) (by omega)
    rw [hplus, Nat.even_add_one] at h1
    tauto
  exact ⟨hWd, hWtype⟩

private theorem exists_anisoPairFrame_aux3 [Finite F] [CharP F 2] {k : ℕ}
    (ih : ∀ {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V},
      (polarBilin Q).Nondegenerate → finrank F V = 2 * (k + 1) → (IsPlusType Q ↔ Even k) →
      ∃ (a b : Fin k → V) (e f : V), (∀ i, IsAnisoPair Q (a i) (b i)) ∧
        (∀ i j, i ≠ j → PairOrth Q (a i) (b i) (a j) (b j)) ∧ Q e = 0 ∧ Q f = 0 ∧ polar Q e f = 1 ∧
        ∀ i, PairOrth Q e f (a i) (b i)) :
    ∀ {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V},
      (polarBilin Q).Nondegenerate → finrank F V = 2 * ((k + 1) + 1) →
      (IsPlusType Q ↔ Even (k + 1)) →
      ∃ (a b : Fin (k + 1) → V) (e f : V), (∀ i, IsAnisoPair Q (a i) (b i)) ∧
        (∀ i j, i ≠ j → PairOrth Q (a i) (b i) (a j) (b j)) ∧ Q e = 0 ∧ Q f = 0 ∧ polar Q e f = 1 ∧
        ∀ i, PairOrth Q e f (a i) (b i) := by
  intro V _ _ _ Q hQ hdim hplus
  obtain ⟨a₀, b₀, h₀⟩ := exists_isAnisoPair hQ (m := k + 2) (by omega) (by omega)
  obtain ⟨hWd, hWtype⟩ := exists_anisoPairFrame_aux2 hQ h₀ hdim hplus
  have hWnd := polarNondegOn_orthPerp hQ h₀.isCompl_span_orthPerp
  obtain ⟨a', b', e', f', hp', ho', he', hf', hef', hpe'⟩ :=
    ih (nondegenerate_polarBilin_restrict hWnd) hWd hWtype
  refine ⟨Fin.cons a₀ (fun i => (a' i : V)), Fin.cons b₀ (fun i => (b' i : V)), (e' : V), (f' : V),
    ?_, ?_, he', hf', by have := hef'; rwa [polar_restrict] at this, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero => simpa using h₀
    | succ i => simpa using (hp' i).of_restrict
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j =>
        simpa using pairOrth_of_mem_orthPerp (a' j).2 (b' j).2
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        simpa using (pairOrth_of_mem_orthPerp (a' i).2 (b' i).2).symm
      | succ j =>
        simpa using (ho' i j (fun h => hij (congrArg Fin.succ h))).of_restrict
  · intro i
    cases i using Fin.cases with
    | zero => simpa using (pairOrth_of_mem_orthPerp e'.2 f'.2).symm
    | succ i => simpa using (hpe' i).of_restrict

theorem exists_anisoPairFrame_aux [Finite F] [CharP F 2] :
    ∀ (k : ℕ) {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V},
      (polarBilin Q).Nondegenerate → finrank F V = 2 * (k + 1) → (IsPlusType Q ↔ Even k) →
      ∃ (a b : Fin k → V) (e f : V), (∀ i, IsAnisoPair Q (a i) (b i)) ∧
        (∀ i j, i ≠ j → PairOrth Q (a i) (b i) (a j) (b j)) ∧ Q e = 0 ∧ Q f = 0 ∧ polar Q e f = 1 ∧
        ∀ i, PairOrth Q e f (a i) (b i) := by
  intro k
  induction k with
  | zero => exact exists_anisoPairFrame_aux1
  | succ k ih => exact exists_anisoPairFrame_aux3 ih

theorem exists_anisoPairFrame [Finite F] [CharP F 2] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank F V = 2 * n)
    (hminus : ¬ IsPlusType Q) (hn : 2 ≤ n) (heven : Even n) :
    ∃ (a b : Fin (n - 1) → V) (e f : V), (∀ i, IsAnisoPair Q (a i) (b i)) ∧
      (∀ i j, i ≠ j → PairOrth Q (a i) (b i) (a j) (b j)) ∧ Q e = 0 ∧ Q f = 0 ∧ polar Q e f = 1 ∧
      ∀ i, PairOrth Q e f (a i) (b i) := by
  have hodd : ¬ Even (n - 1) := by
    obtain ⟨r, hr⟩ := heven
    rintro ⟨s, hs⟩
    omega
  exact exists_anisoPairFrame_aux (n - 1) hQ (by omega) ⟨fun h => absurd h hminus,
    fun h => absurd h hodd⟩

end CFSG.ClassicalGroups.Orthogonal

end
