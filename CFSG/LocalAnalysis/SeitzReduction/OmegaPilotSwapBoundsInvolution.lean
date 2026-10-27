module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsRadical

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG QuadraticMap CFSG.ClassicalGroups.Orthogonal

section ChevalleyWarning

variable {K M : Type*} [Field K] [Finite K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

theorem exists_ne_zero_map_eq_zero_of_three_le {p : ℕ} [Fact p.Prime] [CharP K p]
    (Q' : QuadraticForm K M) (h3 : 3 ≤ Module.finrank K M) : ∃ z : M, z ≠ 0 ∧ Q' z = 0 := by
  classical
  have := Fintype.ofFinite K
  set k := Module.finrank K M with hk
  let b := Module.finBasis K M
  set B' := Q'.toBilin b with hB'
  let P : MvPolynomial (Fin k) K := ∑ i, ∑ j,
    MvPolynomial.C (B' (b i) (b j)) * (MvPolynomial.X i * MvPolynomial.X j)
  have hdeg : P.totalDegree < Fintype.card (Fin k) := by
    rw [Fintype.card_fin]
    have h2 : P.totalDegree ≤ 2 := by
      refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
      refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    omega
  have heval : ∀ x : Fin k → K, MvPolynomial.eval x P = Q' (∑ i, x i • b i) := by
    intro x
    have hQ : Q' (∑ i, x i • b i) = B' (∑ i, x i • b i) (∑ i, x i • b i) := by
      conv_lhs => rw [← QuadraticMap.toQuadraticMap_toBilin Q' b]
      rfl
    rw [hQ, LinearMap.map_sum₂]
    simp only [P, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, smul_eq_mul]
    ring
  have hdvd := char_dvd_card_solutions (K := K) (σ := Fin k) p hdeg
  have h0 : MvPolynomial.eval (0 : Fin k → K) P = 0 := by
    rw [heval]
    simp
  have hpos : 0 < Fintype.card { x : Fin k → K // MvPolynomial.eval x P = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  have hone : 1 < Fintype.card { x : Fin k → K // MvPolynomial.eval x P = 0 } := by
    have := Nat.le_of_dvd hpos hdvd
    have hp2 := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨⟨x, hx⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card hone ⟨0, h0⟩
  have hx0 : x ≠ 0 := fun h => hne (Subtype.ext h)
  refine ⟨∑ i, x i • b i, fun h => hx0 ?_, by rw [← heval]; exact hx⟩
  exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent x h)

end ChevalleyWarning

section Extension

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
theorem polar_eq_zero_of_totallySingular {U : Submodule K V} (hU : ∀ u ∈ U, Q u = 0) {x y : V}
    (hx : x ∈ U) (hy : y ∈ U) : polar Q x y = 0 := by
  rw [polar, hU _ (U.add_mem hx hy), hU x hx, hU y hy, sub_zero, sub_zero]

theorem exists_totallySingular_succ {p : ℕ} [Fact p.Prime] [CharP K p]
    (hQ : (polarBilin Q).Nondegenerate) {a : V} {U : Submodule K V} (hU : ∀ u ∈ U, Q u = 0)
    (hUa : ∀ u ∈ U, polar Q u a = 0) (hd : 2 * Module.finrank K U + 4 ≤ Module.finrank K V) :
    ∃ U' : Submodule K V, U ≤ U' ∧ Module.finrank K U' = Module.finrank K U + 1 ∧
      (∀ x ∈ U', Q x = 0) ∧ ∀ x ∈ U', polar Q x a = 0 := by
  set X := LinearMap.BilinForm.orthogonal (polarBilin Q) (U ⊔ K ∙ a) with hX
  have hmemX : ∀ v, v ∈ X ↔ (∀ u ∈ U, polar Q u v = 0) ∧ polar Q a v = 0 := by
    intro v
    rw [hX, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact ⟨fun u hu => h u (Submodule.mem_sup_left hu),
        h a (Submodule.mem_sup_right (Submodule.mem_span_singleton_self a))⟩
    · rintro ⟨h1, h2⟩ w hw
      obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      change polar Q (u + c • a) v = 0
      rw [polar_add_left, polar_smul_left, h1 u hu, h2, smul_zero, add_zero]
  have hUX : U ≤ X := fun u hu => (hmemX u).mpr
    ⟨fun u' hu' => polar_eq_zero_of_totallySingular hU hu' hu, by rw [polar_comm]; exact hUa u hu⟩
  have hXdim : Module.finrank K V - (Module.finrank K U + 1) ≤ Module.finrank K X := by
    rw [hX, LinearMap.BilinForm.finrank_orthogonal hQ]
    have h1 := Submodule.finrank_add_le_finrank_add_finrank U (K ∙ a)
    have h2 : Module.finrank K (K ∙ a) ≤ 1 := by
      by_cases ha : a = 0
      · rw [ha, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
        omega
      · rw [finrank_span_singleton ha]
    omega
  obtain ⟨Y', hY'⟩ := exists_isCompl U
  set Y := Y' ⊓ X with hY
  have hUY : U ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have := hY'.disjoint.le_bot (show v ∈ U ⊓ Y' from ⟨hv.1, hv.2.1⟩)
    exact this
  have hUYX : U ⊔ Y = X := by
    rw [hY, ← sup_inf_assoc_of_le Y' hUX, hY'.codisjoint.eq_top, top_inf_eq]
  have hYdim : Module.finrank K X = Module.finrank K U + Module.finrank K Y := by
    have := Submodule.finrank_sup_add_finrank_inf_eq U Y
    rw [hUY, finrank_bot, add_zero, hUYX] at this
    exact this
  obtain ⟨z, hz0, hzQ⟩ := exists_ne_zero_map_eq_zero_of_three_le (p := p)
    (Q.comp Y.subtype) (by omega)
  have hzY : (z : V) ∈ Y := z.2
  have hzX : (z : V) ∈ X := hzY.2
  have hzU : (z : V) ∉ U := fun h => hz0 (Subtype.ext (by
    have : (z : V) ∈ U ⊓ Y := ⟨h, hzY⟩
    rw [hUY] at this
    exact this))
  obtain ⟨hzU', hza⟩ := (hmemX z).mp hzX
  refine ⟨U ⊔ K ∙ (z : V), le_sup_left, ?_, ?_, ?_⟩
  · have hdisj : U ⊓ K ∙ (z : V) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv.2
      by_cases hc : c = 0
      · rw [hc, zero_smul]; exact Submodule.zero_mem _
      · exfalso
        apply hzU
        have := U.smul_mem c⁻¹ hv.1
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    have := Submodule.finrank_sup_add_finrank_inf_eq U (K ∙ (z : V))
    rw [hdisj, finrank_bot, add_zero,
      finrank_span_singleton (fun h => hz0 (Subtype.ext h))] at this
    exact this
  · intro x hx
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hU u hu, polar_smul_right, hzU' u hu]
    have : Q (z : V) = 0 := hzQ
    rw [this]
    simp
  · intro x hx
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_add_left, polar_smul_left, hUa u hu, polar_comm, hza, smul_zero, add_zero]

theorem exists_totallySingular_extension {p : ℕ} [Fact p.Prime] [CharP K p]
    (hQ : (polarBilin Q).Nondegenerate) {a : V} {r : ℕ} (hr : 2 * r + 4 ≤ Module.finrank K V) :
    ∀ (k : ℕ) (U : Submodule K V), Module.finrank K U + k = r → (∀ u ∈ U, Q u = 0) →
      (∀ u ∈ U, polar Q u a = 0) →
      ∃ T : Submodule K V, U ≤ T ∧ Module.finrank K T = r ∧ (∀ x ∈ T, Q x = 0) ∧
        ∀ x ∈ T, polar Q x a = 0 := by
  intro k
  induction k with
  | zero => intro U hUr hU hUa; exact ⟨U, le_rfl, by omega, hU, hUa⟩
  | succ k ih =>
    intro U hUr hU hUa
    obtain ⟨U', hUU', hdim, hU', hU'a⟩ := exists_totallySingular_succ (p := p) hQ hU hUa
      (by omega)
    obtain ⟨T, hU'T, hT⟩ := ih U' (by omega) hU' hU'a
    exact ⟨T, hUU'.trans hU'T, hT⟩

end Extension

section Singular

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

@[expose] def singularPart (W : Submodule K V) (hW : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0) :
    Submodule K V where
  carrier := {w | w ∈ W ∧ Q w = 0}
  add_mem' := by
    rintro x y ⟨hx, hQx⟩ ⟨hy, hQy⟩
    refine ⟨W.add_mem hx hy, ?_⟩
    rw [QuadraticMap.map_add Q, hQx, hQy, hW x hx y hy]
    ring
  zero_mem' := ⟨W.zero_mem, QuadraticMap.map_zero Q⟩
  smul_mem' := by
    rintro c x ⟨hx, hQx⟩
    exact ⟨W.smul_mem c hx, by rw [QuadraticMap.map_smul, hQx, smul_zero]⟩

variable {Q}

theorem mem_singularPart {W : Submodule K V} {hW : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0} {w : V} :
    w ∈ singularPart Q W hW ↔ w ∈ W ∧ Q w = 0 := Iff.rfl

theorem exists_le_singularPart_sup [Finite K] [CharP K 2] (W : Submodule K V)
    (hW : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0) :
    ∃ a ∈ W, W ≤ singularPart Q W hW ⊔ K ∙ a := by
  by_cases h : ∀ w ∈ W, Q w = 0
  · exact ⟨0, W.zero_mem, fun w hw => Submodule.mem_sup_left ⟨hw, h w hw⟩⟩
  push Not at h
  obtain ⟨a, haW, ha⟩ := h
  refine ⟨a, haW, fun w hw => ?_⟩
  have := Fintype.ofFinite K
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q w / Q a)
  have hmem : w + c • a ∈ singularPart Q W hW := by
    refine ⟨W.add_mem hw (W.smul_mem c haW), ?_⟩
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right, hW w hw a haW,
      smul_zero, add_zero, smul_eq_mul, ← _root_.sq, show c ^ 2 = c * c by ring, ← hc,
      div_mul_cancel₀ _ ha, CharTwo.add_self_eq_zero]
  have hw' : w = (w + c • a) + (-c) • a := by
    rw [neg_smul, add_neg_cancel_right]
  rw [hw']
  exact Submodule.add_mem_sup hmem (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a))

end Singular

section Involution

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions (fixSpace commSpace mem_fixSpace mem_commSpace
  fixSpace_eq_orthogonal_commSpace polar_commSpace_eq_zero)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_twoSubgroup_of_totallySingular (hQ : (polarBilin Q).Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {s : GL (Fin d) K} (hs : s ∈ matrixIsometries Q) (hss : s * s = 1)
    {T : Submodule K (Fin d → K)} {m : ℕ} (hTm : Module.finrank K T = m)
    (hTsing : ∀ x ∈ T, Q x = 0) {a : Fin d → K} (hTa : ∀ x ∈ T, polar Q x a = 0)
    (hW : ∀ v, matrixLinearIso s v - v ∈ T ⊔ K ∙ a) {c : ℕ}
    (hc : c ≤ d - (2 * m + 1) ∨ (a ∈ T ∧ c ≤ d - 2 * m)) :
    ∃ R : Subgroup (GL (Fin d) K), IsPGroup 2 R ∧
      R ≤ matrixDerived Q ⊓ Subgroup.centralizer {s} ∧
      R ≤ (CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical.flagRadical Q T).map
        (matrixDerived Q).subtype ∧
      Nat.card K ^ (m * c + m * (m - 1) / 2) ≤ Nat.card R := by
  set t := matrixLinearIso s with htdef
  have ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hs
  have htt : t * t = 1 := by rw [htdef, ← map_mul, hss, map_one]
  let b := Module.finBasisOfFinrankEq K T hTm
  set e : Fin m → (Fin d → K) := fun i => (b i : Fin d → K) with hedef
  have hind : LinearIndependent K e := b.linearIndependent.map' T.subtype T.ker_subtype
  have hspan : Submodule.span K (Set.range e) = T := by
    have : Set.range e = T.subtype '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  obtain ⟨f, hef⟩ := exists_dual_family hQ hind
  have heT : ∀ i, e i ∈ T := fun i => (b i).2
  have hTfix : ∀ x ∈ T, t x = x := by
    intro x hx
    have hmem : x ∈ fixSpace t := by
      rw [fixSpace_eq_orthogonal_commSpace hQ ht htt, LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hw
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hW v)
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hz
      change polarBilin Q (t v - v) x = 0
      rw [polarBilin_apply_apply, ← hyz, polar_add_left, polar_smul_left,
        polar_eq_zero_of_totallySingular hTsing hy hx, polar_comm, hTa x hx, smul_zero, add_zero]
    exact mem_fixSpace.mp hmem
  obtain ⟨R, hR2, hRle, hRrad, hRcard⟩ := exists_twoSubgroup_centralizer_of_setup (a := a)
    (f := f) hQ hE hs hss hind (fun i => hTsing _ (heT i))
    (fun i j => polar_eq_zero_of_totallySingular hTsing (heT i) (heT j)) hef
    (fun i => hTfix _ (heT i)) (fun v => by rw [hspan]; exact hW v)
  refine ⟨R, hR2, hRle, hspan ▸ hRrad, le_trans (Nat.pow_le_pow_right Nat.card_pos ?_) hRcard⟩
  have hN : c ≤ Module.finrank K (radicalKer Q e f a) := by
    rcases hc with hc | ⟨haT, hc⟩
    · exact hc.trans (finrank_radicalKer_ge Q e f a)
    · exact hc.trans (finrank_radicalKer_ge_of_mem_span (by rw [hspan]; exact haT))
  have := Nat.mul_le_mul_left m hN
  omega

theorem exponent_le_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    n * (n - 1) / 2 + 2 ≤ (n - 2) * 3 + (n - 2) * (n - 2 - 1) / 2 := by
  have e1 : 2 * ((n - 2) * (n - 2 - 1) / 2) = (n - 2) * (n - 2 - 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_pred_self (n - 2)).two_dvd
  have e2 : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have e3 : (k + 5 - 2) * (k + 5 - 2 - 1) + 4 * (k + 5) = (k + 5) * (k + 5 - 1) + 6 := by
    simp only [show k + 5 - 2 = k + 3 by omega, show k + 3 - 1 = k + 2 by omega,
      show k + 5 - 1 = k + 4 by omega]
    ring
  omega

theorem exponent_le_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    n * (n - 1) / 2 + 2 ≤ (n - 1) * 2 + (n - 1) * (n - 1 - 1) / 2 := by
  have e1 : 2 * ((n - 1) * (n - 1 - 1) / 2) = (n - 1) * (n - 1 - 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_pred_self (n - 1)).two_dvd
  have e2 : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have e3 : (k + 3 - 1) * (k + 3 - 1 - 1) + 2 * (k + 3) = (k + 3) * (k + 3 - 1) + 2 := by
    simp only [show k + 3 - 1 = k + 2 by omega, show k + 2 - 1 = k + 1 by omega]
    ring
  omega

theorem exists_twoSubgroup_centralizer_of_finrank_lt {n : ℕ} (hn : 5 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : (polarBilin Q).Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {s : GL (Fin (2 * n)) K} (hs : s ∈ matrixIsometries Q) (hss : s * s = 1)
    (hl : Module.finrank K (commSpace (matrixLinearIso s)) < n) :
    ∃ R : Subgroup (GL (Fin (2 * n)) K), IsPGroup 2 R ∧
      R ≤ matrixDerived Q ⊓ Subgroup.centralizer {s} ∧
      Nat.card K ^ (n * (n - 1) / 2 + 2) ≤ Nat.card R := by
  set t := matrixLinearIso s with htdef
  have ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hs
  have htt : t * t = 1 := by rw [htdef, ← map_mul, hss, map_one]
  set W := commSpace t with hWdef
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0 := fun x hx y hy =>
    polar_commSpace_eq_zero ht htt hx hy
  obtain ⟨a, haW, hWa⟩ := exists_le_singularPart_sup W hWiso
  set W₀ := singularPart Q W hWiso with hW₀def
  have hW₀sing : ∀ x ∈ W₀, Q x = 0 := fun x hx => hx.2
  have hW₀a : ∀ x ∈ W₀, polar Q x a = 0 := fun x hx => hWiso x hx.1 a haW
  have hWv : ∀ v, t v - v ∈ W := fun v => ⟨v, rfl⟩
  have hdimV : Module.finrank K (Fin (2 * n) → K) = 2 * n := Module.finrank_fin_fun K
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  by_cases h0 : Module.finrank K W₀ ≤ n - 2
  · obtain ⟨T, hW₀T, hTdim, hTsing, hTa⟩ := exists_totallySingular_extension (p := 2) hQ
      (r := n - 2) (by omega) (n - 2 - Module.finrank K W₀) W₀ (by omega) hW₀sing hW₀a
    have hW : ∀ v, t v - v ∈ T ⊔ K ∙ a := fun v =>
      sup_le_sup_right hW₀T _ (hWa (hWv v))
    obtain ⟨R, hR2, hRle, -, hRcard⟩ := exists_twoSubgroup_of_totallySingular hQ hE hs hss hTdim
      hTsing hTa hW (c := 3) (Or.inl (by omega))
    exact ⟨R, hR2, hRle, le_trans (Nat.pow_le_pow_right hq (exponent_le_of_five_le hn)) hRcard⟩
  · have hle : W₀ ≤ W := fun x hx => hx.1
    have hW₀W : W₀ = W := Submodule.eq_of_le_of_finrank_eq hle (by
      have := Submodule.finrank_mono hle
      omega)
    have hWdim : Module.finrank K W = n - 1 := by
      have := Submodule.finrank_mono hle
      omega
    have hWsing : ∀ x ∈ W, Q x = 0 := fun x hx => hW₀sing x (hW₀W ▸ hx)
    obtain ⟨R, hR2, hRle, -, hRcard⟩ := exists_twoSubgroup_of_totallySingular (a := 0) hQ hE hs
      hss hWdim hWsing (fun x _ => polar_zero_right Q x)
      (fun v => Submodule.mem_sup_left (hWv v)) (c := 2) (Or.inr ⟨W.zero_mem, by omega⟩)
    exact ⟨R, hR2, hRle, le_trans (Nat.pow_le_pow_right hq (exponent_le_of_three_le (by omega)))
      hRcard⟩

end Involution

end CFSG.SeitzReduction.OmegaPilot
