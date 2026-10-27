module

public import CFSG.ClassicalInvolution.RouteD.GapsFrLie
public import CFSG.ClassicalInvolution.RouteD.GapsFrSpin

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups

section Eigen

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}

theorem hypRel6 {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg2 : g * g = 1) {e f : V} (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1)
    {a b c d : K} (hge : g e = a • e + b • f) (hgf : g f = c • e + d • f) :
    a * b = 0 ∧ c * d = 0 ∧ a * d + b * c = 1 ∧ a * a + b * c = 1 ∧ a * b + b * d = 0 ∧
      c * a + d * c = 0 ∧ c * b + d * d = 1 := by
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hef
  have hee : polar Q e e = 0 := by rw [polar_self, he]; simp
  have hff : polar Q f f = 0 := by rw [polar_self, hf]; simp
  have hgg : ∀ v, g (g v) = v := fun v => by
    have := LinearEquiv.congr_fun hg2 v
    simpa using this
  have hQg : ∀ v, Q (g v) = Q v := fun v => map_of_mem hgO v
  have hQab : ∀ x y : K, Q (x • e + y • f) = x * y := by
    intro x y
    rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, QuadraticMap.map_smul, he, hf,
      polar_smul_left, polar_smul_right, hef]
    simp
  have hP : ∀ x y x' y' : K, polar Q (x • e + y • f) (x' • e + y' • f) = x * y' + y * x' := by
    intro x y x' y'
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, hee, hff, hef,
      hfe, smul_eq_mul]
    ring
  have R1 : a * b = 0 := by
    have := hQg e
    rw [hge, hQab, he] at this
    exact this
  have R2 : c * d = 0 := by
    have := hQg f
    rw [hgf, hQab, hf] at this
    exact this
  have R3 : a * d + b * c = 1 := by
    have := polar_map_of_mem hgO e f
    rw [hge, hgf, hP, hef] at this
    exact this
  have hge2 : g (g e) = (a * a + b * c) • e + (a * b + b * d) • f := by
    rw [hge, map_add, map_smul, map_smul, hge, hgf]
    module
  have hgf2 : g (g f) = (c * a + d * c) • e + (c * b + d * d) • f := by
    rw [hgf, map_add, map_smul, map_smul, hge, hgf]
    module
  have e1 := congrArg (fun v => polar Q v f) (hgg e)
  have e2 := congrArg (fun v => polar Q v e) (hgg e)
  have e3 := congrArg (fun v => polar Q v f) (hgg f)
  have e4 := congrArg (fun v => polar Q v e) (hgg f)
  simp only [hge2, hgf2, polar_add_left, polar_smul_left, hee, hff, hef, hfe,
    smul_eq_mul] at e1 e2 e3 e4
  exact ⟨R1, R2, R3, by linear_combination e1, by linear_combination e2,
    by linear_combination e3, by linear_combination e4⟩

theorem rootSL2_span6 (F₀ : HypFrame Q m) {a b : ℕ} (ha : a < m) (hb : b < m)
    (hab : a ≠ b) {y : spinGroup Q} (hy : y ∈ rootSL2 F₀ a b ha hb hab true false) :
    (∀ v ∈ Submodule.span K {F₀.vec ⟨a, ha⟩ true, F₀.vec ⟨b, hb⟩ true},
      spinAction Q y v ∈ Submodule.span K {F₀.vec ⟨a, ha⟩ true, F₀.vec ⟨b, hb⟩ true}) ∧
    (∀ v ∈ Submodule.span K {F₀.vec ⟨a, ha⟩ true, F₀.vec ⟨b, hb⟩ true},
      spinAction Q y⁻¹ v ∈ Submodule.span K {F₀.vec ⟨a, ha⟩ true, F₀.vec ⟨b, hb⟩ true}) := by
  have hij : (⟨a, ha⟩ : Fin m) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
  set U := Submodule.span K {F₀.vec ⟨a, ha⟩ true, F₀.vec ⟨b, hb⟩ true} with hU
  let Pres : Subgroup (spinGroup Q) :=
    { carrier := {y | (∀ v ∈ U, spinAction Q y v ∈ U) ∧ (∀ v ∈ U, spinAction Q y⁻¹ v ∈ U)}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨fun v hv => ?_, fun v hv => ?_⟩
        · rw [map_mul, LinearEquiv.mul_apply]
          exact hx.1 _ (hy.1 v hv)
        · rw [mul_inv_rev, map_mul, LinearEquiv.mul_apply]
          exact hy.2 _ (hx.2 v hv)
      one_mem' := ⟨fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩
      inv_mem' := fun {x} hx => ⟨hx.2, fun v hv => by simpa using hx.1 v hv⟩ }
  have he : F₀.vec ⟨a, ha⟩ true ∈ U := Submodule.subset_span (by simp)
  have he' : F₀.vec ⟨b, hb⟩ true ∈ U := Submodule.subset_span (by simp)
  have hroot1 : ∀ (c : K), ∀ v ∈ U,
      spinAction Q (F₀.longRoot hij true false (.ofAdd c)) v ∈ U := by
    intro c v hv
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
    rw [HypFrame.spinAction_longRoot]
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, HypFrame.polar_vec_vec, hij,
      Ne.symm hij, false_and, ite_false]
    simp
    exact add_mem hv (Submodule.smul_mem _ _ he)
  have hroot2 : ∀ (c : K), ∀ v ∈ U,
      spinAction Q (F₀.longRoot hij.symm true false (.ofAdd c)) v ∈ U := by
    intro c v hv
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
    rw [HypFrame.spinAction_longRoot]
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, HypFrame.polar_vec_vec, hij,
      Ne.symm hij, false_and, ite_false]
    simp
    exact add_mem hv (Submodule.smul_mem _ _ he')
  have hrange : rootSL2 F₀ a b ha hb hab true false ≤ Pres := by
    unfold rootSL2
    rw [longSL2_range_eq_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective x
      refine ⟨hroot1 c, fun v hv => ?_⟩
      rw [← map_inv, ← ofAdd_neg]
      exact hroot1 (-c) v hv
    · rintro _ ⟨x, rfl⟩
      obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective x
      refine ⟨hroot2 c, fun v hv => ?_⟩
      rw [← map_inv, ← ofAdd_neg]
      exact hroot2 (-c) v hv
  exact hrange hy

end Eigen

section Classify

variable {F : Type} [Field F] {b c : F} {n : ℕ}

theorem minusVecNe6 (b c : F) (i : Fin (n - 1)) (u : Bool) :
    minusVec n (K := F) i u ≠ 0 := by
  intro h
  have h1 := polar_minusVec_minusVec n b c i i u (!u)
  rw [h] at h1
  simp at h1

section Frame

variable (b c)

theorem eqZeroPolarFrame6
    (hQ : (polarBilin (quadMinus n F b c)).Nondegenerate) {y : Vm n F}
    (he : ∀ i : Fin (n - 1), polar (quadMinus n F b c) y (minusVec n i true) = 0)
    (hf : ∀ i : Fin (n - 1), polar (quadMinus n F b c) y (minusVec n i false) = 0)
    (hp : ∀ t : Fin 2, polar (quadMinus n F b c) y (planeVec n (Pi.single t 1)) = 0) :
    y = 0 := by
  refine hQ.1 y fun z => ?_
  have hz : polarBilin (quadMinus n F b c) y = 0 := by
    refine (Pi.basisFun F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)).ext fun c' => ?_
    rcases c' with i | i | t
    · have e : (Pi.basisFun F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)) (.inl i) =
          minusVec n i true := by simp [Pi.basisFun_apply, minusVec, eVec]
      rw [e]
      simpa [polarBilin_apply_apply] using he i
    · have e : (Pi.basisFun F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)) (.inr (.inl i)) =
          minusVec n i false := by simp [Pi.basisFun_apply, minusVec, fVec]
      rw [e]
      simpa [polarBilin_apply_apply] using hf i
    · have e : (Pi.basisFun F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)) (.inr (.inr t)) =
          planeVec n (Pi.single t 1) := by
        funext v
        rcases v with i' | i' | t' <;> simp [Pi.basisFun_apply, planeVec, Pi.single_apply]
      rw [e]
      simpa [polarBilin_apply_apply] using hp t
  simpa using LinearMap.congr_fun hz z

theorem eqOfPolarFrame6
    (hQ : (polarBilin (quadMinus n F b c)).Nondegenerate) {x y : Vm n F}
    (he : ∀ i : Fin (n - 1), polar (quadMinus n F b c) x (minusVec n i true) =
      polar (quadMinus n F b c) y (minusVec n i true))
    (hf : ∀ i : Fin (n - 1), polar (quadMinus n F b c) x (minusVec n i false) =
      polar (quadMinus n F b c) y (minusVec n i false))
    (hp : ∀ t : Fin 2, polar (quadMinus n F b c) x (planeVec n (Pi.single t 1)) =
      polar (quadMinus n F b c) y (planeVec n (Pi.single t 1))) : x = y := by
  have := eqZeroPolarFrame6 b c hQ (y := x - y)
    (fun i => by rw [polar_sub_left, he i, sub_self])
    (fun i => by rw [polar_sub_left, hf i, sub_self])
    (fun t => by rw [polar_sub_left, hp t, sub_self])
  exact sub_eq_zero.mp this

end Frame

theorem polarApplyOfEig6 {g : Vm n F ≃ₗ[F] Vm n F}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c)) {l : F} (hl : l * l = 1)
    {z : Vm n F} (hz : g z = l • z) (v : Vm n F) :
    polar (quadMinus n F b c) (g v) z = l * polar (quadMinus n F b c) v z := by
  have h1 : z = l • g z := by
    rw [hz, smul_smul, hl, one_smul]
  conv_lhs => rw [h1]
  rw [polar_smul_right, polar_map_of_mem hgO, smul_eq_mul]

theorem h0Alg6 (h2 : (2 : F) ≠ 0) {a b c d : F}
    (R1 : a * b = 0) (R3 : a * d + b * c = 1) (R4 : a * a + b * c = 1)
    (R5 : a * b + b * d = 0) (R6 : c * a + d * c = 0) :
    (b = 0 ∧ c = 0 ∧ d = a ∧ (a = 1 ∨ a = -1)) ∨ (a = 0 ∧ d = 0 ∧ b ≠ 0 ∧ b * c = 1) := by
  by_cases hb : b = 0
  · left
    subst hb
    have h4 : a * a = 1 := by simpa using R4
    have ha0 : a ≠ 0 := fun h => by rw [h] at h4; simp at h4
    have hd : d = a := by
      have h3 : a * d = 1 := by simpa using R3
      have : a * d = a * a := h3.trans h4.symm
      exact mul_left_cancel₀ ha0 this
    have hc : c = 0 := by
      have : c * (2 * a) = 0 := by rw [hd] at R6; linear_combination R6
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (mul_ne_zero h2 ha0)
    refine ⟨rfl, hc, hd, ?_⟩
    have : (a - 1) * (a + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  · right
    have ha : a = 0 := (mul_eq_zero.mp R1).resolve_right hb
    subst ha
    have hd : d = 0 := by
      have : b * d = 0 := by simpa using R5
      exact (mul_eq_zero.mp this).resolve_left hb
    subst hd
    exact ⟨rfl, rfl, hb, by simpa using R3⟩

theorem notAntidiag6 {g : Vm n F ≃ₗ[F] Vm n F} (hg2 : g * g = 1) {a b' : ℕ} (ha : a < n - 1)
    (hb : b' < n - 1) (hab : a ≠ b') {ε bb cc : F}
    (hεε : ε * ε = 1) (hbb : bb ≠ 0) (hbc : bb * cc = 1)
    (hge : g (minusVec n ⟨a, ha⟩ true) = bb • minusVec n ⟨a, ha⟩ false)
    (hgf : g (minusVec n ⟨a, ha⟩ false) = cc • minusVec n ⟨a, ha⟩ true)
    (hg1 : ∀ u, g (minusVec n ⟨b', hb⟩ u) = ε • minusVec n ⟨b', hb⟩ u)
    (hnorm : ∀ y ∈ rootSL2 (minusFrame n b c).toHypFrame a b' ha hb hab true false,
      ∃ y' ∈ rootSL2 (minusFrame n b c).toHypFrame a b' ha hb hab true false,
        g * spinAction (quadMinus n F b c) y = spinAction (quadMinus n F b c) y' * g) :
    False := by
  have hij : (⟨a, ha⟩ : Fin (n - 1)) ≠ ⟨b', hb⟩ := fun h => hab (congrArg Fin.val h)
  set F₀ := (minusFrame n b c).toHypFrame with hF₀
  have hv : ∀ i s, F₀.vec i s = minusVec n i s := fun _ _ => rfl
  have hgg : ∀ v, g (g v) = v := fun v => by
    have := LinearEquiv.congr_fun hg2 v
    simpa using this
  have hy₀ : F₀.longRoot hij true false (.ofAdd 1) ∈ rootSL2 F₀ a b' ha hb hab true false :=
    ⟨upperSL2 1, by rw [HypFrame.longSL2_upperSL2]⟩
  obtain ⟨y', hy', hcomm⟩ := hnorm _ hy₀
  have h1 := LinearEquiv.congr_fun hcomm (g (minusVec n ⟨a, ha⟩ true))
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgg, hge, map_smul,
    HypFrame.spinAction_longRoot, hv, hv] at h1
  have hY : spinAction (quadMinus n F b c) y' (minusVec n ⟨a, ha⟩ true) =
      minusVec n ⟨a, ha⟩ true - (bb * ε) • minusVec n ⟨b', hb⟩ false := by
    rw [← h1]
    simp only [polar_minusVec_minusVec n b c, hij, false_and, ite_false]
    simp only [map_add, map_sub, map_smul, hge, hgf, hg1]
    simp only [minusVec_true, minusVec_false]
    simp
    rw [smul_sub, smul_smul, smul_smul, hbc, one_smul]
  obtain ⟨hinv, -⟩ := rootSL2_span6 F₀ ha hb hab hy'
  have hmem := hinv (minusVec n ⟨a, ha⟩ true) (Submodule.subset_span (by simp [hv]))
  rw [hY] at hmem
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
  have h2' := congrArg (fun v => polar (quadMinus n F b c) v (minusVec n ⟨b', hb⟩ true)) hαβ
  simp only [polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul, hv,
    polar_minusVec_minusVec n b c, hij] at h2'
  simp at h2'
  have hε0 : ε ≠ 0 := fun h => by rw [h] at hεε; simp at hεε
  rcases h2' with h | h
  · exact hbb h
  · exact hε0 h

end Classify

end CFSG.ClassicalInvolution.RouteD.TwinSmall
