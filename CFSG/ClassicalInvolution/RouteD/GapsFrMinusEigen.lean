module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBEigen
public import CFSG.ClassicalInvolution.RouteD.GapsFrSpin
public import CFSG.ClassicalInvolution.RouteD.GapsFrLie

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Eigen

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}

private def imgPairS (F₀ : HypFrame Q m) (j : Fin m) (s : Bool) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : HypPair Q :=
  ⟨g (F₀.vec j s), g (F₀.vec j (!s)), by rw [map_of_mem hg]; exact F₀.map_vec j s,
    by rw [map_of_mem hg]; exact F₀.map_vec j (!s),
    by rw [polar_map_of_mem hg]; exact F₀.polar_vec_not j s⟩

private theorem orth_imgPairS (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    (imgPairS F₀ i s hg).Orth (imgPairS F₀ j t hg) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [imgPairS]; rw [polar_map_of_mem hg]; exact F₀.polar_vec_of_ne hij _ _)

private theorem eigen_smul_of_commute_La (h2 : (2 : K) ≠ 0) (Fr : OFrame Q) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hc : ∀ A : SL(2, K), g * Fr.La A = Fr.La A * g) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ v ∈ Fr.span, g v = ε • v := by
  rcases frame_eigen_of_commute_La h2 Fr hgO hg2 hc with h | h
  · exact ⟨1, Or.inl rfl, fun v hv => by rw [one_smul]; exact h v hv⟩
  · exact ⟨-1, Or.inr rfl, fun v hv => by rw [neg_one_smul]; exact h v hv⟩

theorem eigen_of_commute_conj_rootSL2 (h2 : (2 : K) ≠ 0) (F₀ : HypFrame Q m) {a b : ℕ}
    (ha : a < m) (hb : b < m) (hab : a ≠ b) (s t : Bool) (x : spinGroup Q) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hcomm : ∀ y ∈ (rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom,
      g * spinAction Q y = spinAction Q y * g) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ u : Bool,
      g (spinAction Q x (F₀.vec ⟨a, ha⟩ u)) = ε • spinAction Q x (F₀.vec ⟨a, ha⟩ u) ∧
      g (spinAction Q x (F₀.vec ⟨b, hb⟩ u)) = ε • spinAction Q x (F₀.vec ⟨b, hb⟩ u) := by
  have hij : (⟨a, ha⟩ : Fin m) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
  have hX : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have horth := orth_imgPairS F₀ hij s t hX
  have heq := La_range_eq_of_pairs F₀ ha hb hab s t x horth ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  have hc : ∀ A : SL(2, K), g * (mkFrame (imgPairS F₀ ⟨a, ha⟩ s hX)
      (imgPairS F₀ ⟨b, hb⟩ t hX) horth).La A =
      (mkFrame (imgPairS F₀ ⟨a, ha⟩ s hX) (imgPairS F₀ ⟨b, hb⟩ t hX) horth).La A * g := by
    intro A
    have hmem : (mkFrame (imgPairS F₀ ⟨a, ha⟩ s hX) (imgPairS F₀ ⟨b, hb⟩ t hX) horth).La A ∈
        (mkFrame (imgPairS F₀ ⟨a, ha⟩ s hX) (imgPairS F₀ ⟨b, hb⟩ t hX) horth).La.range :=
      ⟨A, rfl⟩
    rw [heq] at hmem
    obtain ⟨y, hy, hyeq⟩ := hmem
    rw [← hyeq]
    exact hcomm y hy
  obtain ⟨ε, hε, hv⟩ := eigen_smul_of_commute_La h2 _ hgO hg2 hc
  refine ⟨ε, hε, fun u => ⟨hv _ ?_, hv _ ?_⟩⟩
  · cases s <;> cases u
    · exact Frame.e₁_mem_span _
    · exact Frame.f₁_mem_span _
    · exact Frame.f₁_mem_span _
    · exact Frame.e₁_mem_span _
  · cases t <;> cases u
    · exact Frame.e₂_mem_span _
    · exact Frame.f₂_mem_span _
    · exact Frame.f₂_mem_span _
    · exact Frame.e₂_mem_span _

private theorem hyp_relations {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
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

private theorem rootSL2_preserves_span (F₀ : HypFrame Q m) {a b : ℕ} (ha : a < m) (hb : b < m)
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

open CFSG.LieType.Universal.Spin.Twisted

variable {F : Type} [Field F] {b c : F} {n : ℕ}

private theorem minusVec_ne_zero (b c : F) (i : Fin (n - 1)) (u : Bool) :
    minusVec n (K := F) i u ≠ 0 := by
  intro h
  have h1 := polar_minusVec_minusVec n b c i i u (!u)
  rw [h] at h1
  simp at h1

@[expose] def EigAt (g : Vm n F ≃ₗ[F] Vm n F) (ε : F) (a : ℕ) : Prop :=
  ∃ h : a < n - 1, ∀ u : Bool, g (minusVec n ⟨a, h⟩ u) = ε • minusVec n ⟨a, h⟩ u

private theorem EigAt.unique (b c : F) {g : Vm n F ≃ₗ[F] Vm n F} {ε ε' : F} {a : ℕ}
    (h : EigAt g ε a) (h' : EigAt g ε' a) : ε = ε' := by
  obtain ⟨ha, hv⟩ := h
  obtain ⟨_, hv'⟩ := h'
  exact smul_left_injective F (minusVec_ne_zero b c ⟨a, ha⟩ true) ((hv true).symm.trans (hv' true))

private theorem eigAt_all (b c : F) {s : ℕ} (hs : 1 ≤ s) {g : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F}
    (hchain : ∀ a, 1 ≤ a → a ≤ s → ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt g ε a ∧ EigAt g ε (a + 1))
    (hN : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt g ε (s + 1) ∧ EigAt g ε (s + 2))
    (hM : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt g ε (s + 2) ∧ EigAt g ε (s + 3)) :
    ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ ∀ a, 1 ≤ a → a ≤ s + 3 → EigAt g ε a := by
  obtain ⟨ε₁, hε₁, h1a, h1b⟩ := hchain 1 le_rfl hs
  refine ⟨ε₁, hε₁, ?_⟩
  have hc : ∀ a, 1 ≤ a → a ≤ s → EigAt g ε₁ a ∧ EigAt g ε₁ (a + 1) := by
    intro a ha1
    induction a, ha1 using Nat.le_induction with
    | base => exact fun _ => ⟨h1a, h1b⟩
    | succ a ha1 ih =>
      intro has
      obtain ⟨ε', hε', h', h''⟩ := hchain (a + 1) (by omega) has
      have := EigAt.unique b c (ih (by omega)).2 h'
      subst this
      exact ⟨h', h''⟩
  intro a ha1 ha3
  by_cases has : a ≤ s
  · exact (hc a ha1 has).1
  by_cases has1 : a = s + 1
  · subst has1
    exact (hc s hs le_rfl).2
  obtain ⟨εN, -, hN1, hN2⟩ := hN
  have e1 : εN = ε₁ := EigAt.unique b c hN1 (hc s hs le_rfl).2
  subst e1
  by_cases has2 : a = s + 2
  · subst has2
    exact hN2
  obtain ⟨εM, -, hM1, hM2⟩ := hM
  have e2 : εM = εN := EigAt.unique b c hM1 hN2
  subst e2
  have : a = s + 3 := by omega
  subst this
  exact hM2

section Frame

variable (b c)

private theorem eq_zero_of_polar_frame
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

private theorem eq_of_polar_frame
    (hQ : (polarBilin (quadMinus n F b c)).Nondegenerate) {x y : Vm n F}
    (he : ∀ i : Fin (n - 1), polar (quadMinus n F b c) x (minusVec n i true) =
      polar (quadMinus n F b c) y (minusVec n i true))
    (hf : ∀ i : Fin (n - 1), polar (quadMinus n F b c) x (minusVec n i false) =
      polar (quadMinus n F b c) y (minusVec n i false))
    (hp : ∀ t : Fin 2, polar (quadMinus n F b c) x (planeVec n (Pi.single t 1)) =
      polar (quadMinus n F b c) y (planeVec n (Pi.single t 1))) : x = y := by
  have := eq_zero_of_polar_frame b c hQ (y := x - y)
    (fun i => by rw [polar_sub_left, he i, sub_self])
    (fun i => by rw [polar_sub_left, hf i, sub_self])
    (fun t => by rw [polar_sub_left, hp t, sub_self])
  exact sub_eq_zero.mp this

end Frame

private theorem polar_apply_of_eig {g : Vm n F ≃ₗ[F] Vm n F}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c)) {l : F} (hl : l * l = 1)
    {z : Vm n F} (hz : g z = l • z) (v : Vm n F) :
    polar (quadMinus n F b c) (g v) z = l * polar (quadMinus n F b c) v z := by
  have h1 : z = l • g z := by
    rw [hz, smul_smul, hl, one_smul]
  conv_lhs => rw [h1]
  rw [polar_smul_right, polar_map_of_mem hgO, smul_eq_mul]

private theorem eq_H0_of_polar (hQ : (polarBilin (quadMinus n F b c)).Nondegenerate)
    (h0 : 0 < n - 1) {v : Vm n F}
    (hi : ∀ i : Fin (n - 1), 1 ≤ i.val →
      polar (quadMinus n F b c) v (minusVec n i true) = 0 ∧
        polar (quadMinus n F b c) v (minusVec n i false) = 0)
    (hp : ∀ t : Fin 2, polar (quadMinus n F b c) v (planeVec n (Pi.single t 1)) = 0) :
    v = polar (quadMinus n F b c) v (minusVec n ⟨0, h0⟩ false) • minusVec n ⟨0, h0⟩ true +
      polar (quadMinus n F b c) v (minusVec n ⟨0, h0⟩ true) • minusVec n ⟨0, h0⟩ false := by
  set e0 := minusVec n (K := F) ⟨0, h0⟩ true with he0
  set f0 := minusVec n (K := F) ⟨0, h0⟩ false with hf0
  have hy : v - (polar (quadMinus n F b c) v f0 • e0 + polar (quadMinus n F b c) v e0 • f0) =
      0 := by
    refine eq_zero_of_polar_frame b c hQ (fun i => ?_) (fun i => ?_) (fun t => ?_)
    · by_cases hi0 : i = ⟨0, h0⟩
      · subst hi0
        simp only [polar_sub_left, polar_add_left, polar_smul_left, smul_eq_mul, he0, hf0,
          polar_minusVec_minusVec n b c]
        simp
      · have hv := hi i (by
          have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
          omega)
        simp only [polar_sub_left, polar_add_left, polar_smul_left, smul_eq_mul, he0, hf0,
          polar_minusVec_minusVec n b c, hv.1]
        simp [Ne.symm hi0]
    · by_cases hi0 : i = ⟨0, h0⟩
      · subst hi0
        simp only [polar_sub_left, polar_add_left, polar_smul_left, smul_eq_mul, he0, hf0,
          polar_minusVec_minusVec n b c]
        simp
      · have hv := hi i (by
          have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
          omega)
        simp only [polar_sub_left, polar_add_left, polar_smul_left, smul_eq_mul, he0, hf0,
          polar_minusVec_minusVec n b c, hv.2]
        simp [Ne.symm hi0]
    · simp only [polar_sub_left, polar_add_left, polar_smul_left, smul_eq_mul, he0, hf0,
        polar_minusVec_planeVec n b c, hp t]
      simp
  exact sub_eq_zero.mp hy

private theorem h0_algebra (h2 : (2 : F) ≠ 0) {a b c d : F}
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

private theorem h0_data (h2 : (2 : F) ≠ 0) (hQ : (polarBilin (quadMinus n F b c)).Nondegenerate)
    (h0 : 0 < n - 1) {g : Vm n F ≃ₗ[F] Vm n F}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c)) (hg2 : g * g = 1)
    {ε : F} (hεε : ε * ε = 1)
    (hU : ∀ i : Fin (n - 1), 1 ≤ i.val → ∀ u, g (minusVec n i u) = ε • minusVec n i u)
    (hA : ∀ t : Fin 2, g (planeVec n (Pi.single t 1)) = ε • planeVec n (Pi.single t 1)) :
    ∃ a b' c' d' : F,
      g (minusVec n ⟨0, h0⟩ true) = a • minusVec n ⟨0, h0⟩ true + b' • minusVec n ⟨0, h0⟩ false ∧
      g (minusVec n ⟨0, h0⟩ false) =
        c' • minusVec n ⟨0, h0⟩ true + d' • minusVec n ⟨0, h0⟩ false ∧
      ((b' = 0 ∧ c' = 0 ∧ d' = a ∧ (a = 1 ∨ a = -1)) ∨
        (a = 0 ∧ d' = 0 ∧ b' ≠ 0 ∧ b' * c' = 1)) := by
  have hperp : ∀ x : Vm n F,
      (∀ i : Fin (n - 1), 1 ≤ i.val → ∀ u, polar (quadMinus n F b c) x (minusVec n i u) = 0) →
      (∀ t : Fin 2, polar (quadMinus n F b c) x (planeVec n (Pi.single t 1)) = 0) →
      (∀ i : Fin (n - 1), 1 ≤ i.val →
        polar (quadMinus n F b c) (g x) (minusVec n i true) = 0 ∧
          polar (quadMinus n F b c) (g x) (minusVec n i false) = 0) ∧
      (∀ t : Fin 2, polar (quadMinus n F b c) (g x) (planeVec n (Pi.single t 1)) = 0) := by
    intro x hx hxp
    refine ⟨fun i hi => ⟨?_, ?_⟩, fun t => ?_⟩
    · rw [polar_apply_of_eig hgO hεε (hU i hi true), hx i hi true, mul_zero]
    · rw [polar_apply_of_eig hgO hεε (hU i hi false), hx i hi false, mul_zero]
    · rw [polar_apply_of_eig hgO hεε (hA t), hxp t, mul_zero]
  have hperp0 : ∀ u : Bool,
      (∀ i : Fin (n - 1), 1 ≤ i.val → ∀ u', polar (quadMinus n F b c) (minusVec n ⟨0, h0⟩ u)
        (minusVec n i u') = 0) ∧
      (∀ t : Fin 2, polar (quadMinus n F b c) (minusVec n ⟨0, h0⟩ u) (planeVec n (Pi.single t 1)) =
        0) := by
    intro u
    refine ⟨fun i hi u' => ?_, fun t => polar_minusVec_planeVec n b c _ _ _⟩
    rw [polar_minusVec_minusVec n b c]
    have : (⟨0, h0⟩ : Fin (n - 1)) ≠ i := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    simp [this]
  have hge := eq_H0_of_polar hQ h0 (hperp _ (hperp0 true).1 (hperp0 true).2).1
    (hperp _ (hperp0 true).1 (hperp0 true).2).2
  have hgf := eq_H0_of_polar hQ h0 (hperp _ (hperp0 false).1 (hperp0 false).2).1
    (hperp _ (hperp0 false).1 (hperp0 false).2).2
  have hef : polar (quadMinus n F b c) (minusVec n ⟨0, h0⟩ true)
      (minusVec n ⟨0, h0⟩ false) = 1 := by
    rw [polar_minusVec_minusVec n b c]
    simp
  obtain ⟨R1, -, R3, R4, R5, R6, -⟩ := hyp_relations hgO hg2 (quadMinus_minusVec n b c _ true)
    (quadMinus_minusVec n b c _ false) hef hge hgf
  exact ⟨_, _, _, _, hge, hgf, h0_algebra h2 R1 R3 R4 R5 R6⟩

private theorem eig_planeVec (b c : F) {s : ℕ} (hs : 1 ≤ s) {g : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F}
    {ε : F}
    (hU : ∀ i : Fin (s + 5 - 1), 1 ≤ i.val → ∀ u,
      g (minusVec (s + 5) i u) = ε • minusVec (s + 5) i u)
    (hW : ∀ t : Fin 2, ∃ ε' : F,
      g (minusVec (s + 5) ⟨3, by omega⟩ true) = ε' • minusVec (s + 5) ⟨3, by omega⟩ true ∧
      g (minusVec (s + 5) ⟨4, by omega⟩ true) = ε' • minusVec (s + 5) ⟨4, by omega⟩ true ∧
      g (minusVec (s + 5) ⟨4, by omega⟩ false + planeVec (s + 5) (Pi.single t 1) -
          planeNorm b c (Pi.single t 1) • minusVec (s + 5) ⟨4, by omega⟩ true) =
        ε' • (minusVec (s + 5) ⟨4, by omega⟩ false + planeVec (s + 5) (Pi.single t 1) -
          planeNorm b c (Pi.single t 1) • minusVec (s + 5) ⟨4, by omega⟩ true)) :
    ∀ t : Fin 2, g (planeVec (s + 5) (Pi.single t 1)) = ε • planeVec (s + 5) (Pi.single t 1) := by
  intro t
  obtain ⟨ε', h3, h4, hf⟩ := hW t
  have e3 : ε' = ε := by
    have := h3.symm.trans (hU ⟨3, by omega⟩ (by simp) true)
    exact smul_left_injective F (minusVec_ne_zero b c _ true) this
  subst e3
  have hf4 := hU ⟨4, by omega⟩ (by simp) false
  set w : Fin 2 → F := Pi.single t 1 with hw
  set e4 := minusVec (s + 5) (K := F) ⟨4, by omega⟩ true with he4
  set f4 := minusVec (s + 5) (K := F) ⟨4, by omega⟩ false with hf4'
  have hpv : planeVec (s + 5) w = (f4 + planeVec (s + 5) w - planeNorm b c w • e4) - f4 +
      planeNorm b c w • e4 := by abel
  calc g (planeVec (s + 5) w)
      = g ((f4 + planeVec (s + 5) w - planeNorm b c w • e4) - f4 + planeNorm b c w • e4) :=
        congrArg g hpv
    _ = ε' • planeVec (s + 5) w := by
      rw [map_add, map_sub, map_smul, hf, hf4, h4]
      module

private theorem eq_smul_of_eig (hQ : (polarBilin (quadMinus n F b c)).Nondegenerate)
    {g : Vm n F ≃ₗ[F] Vm n F}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c)) {ε : F}
    (hεε : ε * ε = 1)
    (hz : ∀ i : Fin (n - 1), ∀ u, g (minusVec n i u) = ε • minusVec n i u)
    (hA : ∀ t : Fin 2, g (planeVec n (Pi.single t 1)) = ε • planeVec n (Pi.single t 1))
    (v : Vm n F) : g v = ε • v := by
  refine eq_of_polar_frame b c hQ (fun i => ?_) (fun i => ?_) (fun t => ?_)
  · rw [polar_apply_of_eig hgO hεε (hz i true), polar_smul_left, smul_eq_mul]
  · rw [polar_apply_of_eig hgO hεε (hz i false), polar_smul_left, smul_eq_mul]
  · rw [polar_apply_of_eig hgO hεε (hA t), polar_smul_left, smul_eq_mul]

private theorem not_antidiag {g : Vm n F ≃ₗ[F] Vm n F} (hg2 : g * g = 1) {a b' : ℕ} (ha : a < n - 1)
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
  obtain ⟨hinv, -⟩ := rootSL2_preserves_span F₀ ha hb hab hy'
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

private theorem commute_of_split (hQ : (polarBilin (quadMinus n F b c)).Nondegenerate)
    (h0 : 0 < n - 1) {g : Vm n F ≃ₗ[F] Vm n F}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c)) {ε : F}
    (hεε : ε * ε = 1)
    (hU : ∀ i : Fin (n - 1), 1 ≤ i.val → ∀ u, g (minusVec n i u) = ε • minusVec n i u)
    (hA : ∀ t : Fin 2, g (planeVec n (Pi.single t 1)) = ε • planeVec n (Pi.single t 1))
    (hz : ∀ u, g (minusVec n ⟨0, h0⟩ u) = (-ε) • minusVec n ⟨0, h0⟩ u)
    {Y : Vm n F ≃ₗ[F] Vm n F}
    (hYO : Y ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c))
    (hYe : Y (minusVec n ⟨0, h0⟩ true) = minusVec n ⟨0, h0⟩ true)
    (hYf : Y (minusVec n ⟨0, h0⟩ false) = minusVec n ⟨0, h0⟩ false) : g * Y = Y * g := by
  set e0 := minusVec n (K := F) ⟨0, h0⟩ true with he0
  set f0 := minusVec n (K := F) ⟨0, h0⟩ false with hf0
  have hεε' : (-ε) * (-ε) = 1 := by rw [neg_mul_neg]; exact hεε
  have hpef : polar (quadMinus n F b c) e0 f0 = 1 := by
    rw [he0, hf0, polar_minusVec_minusVec n b c]; simp
  have hpfe : polar (quadMinus n F b c) f0 e0 = 1 := by rw [polar_comm]; exact hpef
  have hpee : polar (quadMinus n F b c) e0 e0 = 0 := by
    rw [he0, polar_minusVec_minusVec n b c]; simp
  have hpff : polar (quadMinus n F b c) f0 f0 = 0 := by
    rw [hf0, polar_minusVec_minusVec n b c]; simp
  have hperp : ∀ w : Vm n F, polar (quadMinus n F b c) w e0 = 0 →
      polar (quadMinus n F b c) w f0 = 0 → g w = ε • w := by
    intro w hwe hwf
    refine eq_of_polar_frame b c hQ (fun i => ?_) (fun i => ?_) (fun t => ?_)
    · by_cases hi : 1 ≤ i.val
      · rw [polar_apply_of_eig hgO hεε (hU i hi true), polar_smul_left, smul_eq_mul]
      · have : i = ⟨0, h0⟩ := Fin.ext (by show i.val = 0; omega)
        subst this
        rw [polar_apply_of_eig hgO hεε' (hz true), polar_smul_left, smul_eq_mul]
        change -ε * polar _ w e0 = ε * polar _ w e0
        rw [hwe]; ring
    · by_cases hi : 1 ≤ i.val
      · rw [polar_apply_of_eig hgO hεε (hU i hi false), polar_smul_left, smul_eq_mul]
      · have : i = ⟨0, h0⟩ := Fin.ext (by show i.val = 0; omega)
        subst this
        rw [polar_apply_of_eig hgO hεε' (hz false), polar_smul_left, smul_eq_mul]
        change -ε * polar _ w f0 = ε * polar _ w f0
        rw [hwf]; ring
    · rw [polar_apply_of_eig hgO hεε (hA t), polar_smul_left, smul_eq_mul]
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  set v₀ := polar (quadMinus n F b c) v f0 • e0 + polar (quadMinus n F b c) v e0 • f0 with hv₀
  set v₁ := v - v₀ with hv₁
  have hv : v = v₀ + v₁ := by rw [hv₁]; abel
  have hv₁e : polar (quadMinus n F b c) v₁ e0 = 0 := by
    rw [hv₁, polar_sub_left, hv₀, polar_add_left, polar_smul_left, polar_smul_left, hpee, hpfe]
    simp
  have hv₁f : polar (quadMinus n F b c) v₁ f0 = 0 := by
    rw [hv₁, polar_sub_left, hv₀, polar_add_left, polar_smul_left, polar_smul_left, hpef, hpff]
    simp
  have hYv₁ : polar (quadMinus n F b c) (Y v₁) e0 = 0 ∧
      polar (quadMinus n F b c) (Y v₁) f0 = 0 := by
    constructor
    · have := polar_map_of_mem hYO v₁ e0
      rw [hYe] at this
      rw [this, hv₁e]
    · have := polar_map_of_mem hYO v₁ f0
      rw [hYf] at this
      rw [this, hv₁f]
  have hYv₀ : Y v₀ = v₀ := by
    rw [hv₀, map_add, map_smul, map_smul, hYe, hYf]
  have hgv₀ : g v₀ = (-ε) • v₀ := by
    rw [hv₀, map_add, map_smul, map_smul, hz true, hz false]
    module
  have hgYv : g (Y v) = (-ε) • v₀ + ε • Y v₁ := by
    conv_lhs => rw [hv]
    rw [map_add, hYv₀, map_add, hgv₀, hperp _ hYv₁.1 hYv₁.2]
  have hYgv : Y (g v) = (-ε) • v₀ + ε • Y v₁ := by
    conv_lhs => rw [hv]
    rw [map_add, hgv₀, hperp _ hv₁e hv₁f, map_add, map_smul, map_smul, hYv₀]
  rw [hgYv, hYgv]

theorem minus_classify (h2 : (2 : F) ≠ 0) {s : ℕ} (hs : 1 ≤ s)
    (hQ : (polarBilin (quadMinus (s + 5) F b c)).Nondegenerate)
    {g : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus (s + 5) F b c)) (hg2 : g * g = 1)
    (hchain : ∀ a, 1 ≤ a → a ≤ s → ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt g ε a ∧ EigAt g ε (a + 1))
    (hN : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt g ε (s + 1) ∧ EigAt g ε (s + 2))
    (hM : ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ EigAt g ε (s + 2) ∧ EigAt g ε (s + 3))
    (hW : ∀ t : Fin 2, ∃ ε' : F,
      g (minusVec (s + 5) ⟨3, by omega⟩ true) = ε' • minusVec (s + 5) ⟨3, by omega⟩ true ∧
      g (minusVec (s + 5) ⟨4, by omega⟩ true) = ε' • minusVec (s + 5) ⟨4, by omega⟩ true ∧
      g (minusVec (s + 5) ⟨4, by omega⟩ false + planeVec (s + 5) (Pi.single t 1) -
          planeNorm b c (Pi.single t 1) • minusVec (s + 5) ⟨4, by omega⟩ true) =
        ε' • (minusVec (s + 5) ⟨4, by omega⟩ false + planeVec (s + 5) (Pi.single t 1) -
          planeNorm b c (Pi.single t 1) • minusVec (s + 5) ⟨4, by omega⟩ true))
    (hnorm : ∀ y ∈ rootSL2 (minusFrame (s + 5) b c).toHypFrame 0 1 (by omega) (by omega)
        (by omega) true false,
      ∃ y' ∈ rootSL2 (minusFrame (s + 5) b c).toHypFrame 0 1 (by omega) (by omega) (by omega)
        true false, g * spinAction (quadMinus (s + 5) F b c) y =
          spinAction (quadMinus (s + 5) F b c) y' * g)
    (hmov : ∃ y ∈ rootSL2 (minusFrame (s + 5) b c).toHypFrame 0 1 (by omega) (by omega)
        (by omega) true false,
      g * spinAction (quadMinus (s + 5) F b c) y ≠ spinAction (quadMinus (s + 5) F b c) y * g) :
    ∀ Y : Vm (s + 5) F ≃ₗ[F] Vm (s + 5) F,
      Y ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus (s + 5) F b c) →
      Y (minusVec (s + 5) ⟨0, by omega⟩ true) = minusVec (s + 5) ⟨0, by omega⟩ true →
      Y (minusVec (s + 5) ⟨0, by omega⟩ false) = minusVec (s + 5) ⟨0, by omega⟩ false →
      g * Y = Y * g := by
  classical
  intro Y hYO hYe hYf
  obtain ⟨ε, hε, hall⟩ := eigAt_all b c hs hchain hN hM
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  have hU : ∀ i : Fin (s + 5 - 1), 1 ≤ i.val → ∀ u,
      g (minusVec (s + 5) i u) = ε • minusVec (s + 5) i u := by
    intro i hi u
    obtain ⟨_, hv⟩ := hall i.val hi (by have := i.isLt; omega)
    exact hv u
  have hA := eig_planeVec b c hs hU hW
  have h0 : 0 < s + 5 - 1 := by omega
  have hgg : ∀ v, g (g v) = v := fun v => by
    have := LinearEquiv.congr_fun hg2 v
    simpa using this
  obtain ⟨a, b', c', d', hge, hgf, hcls⟩ := h0_data h2 hQ h0 hgO hg2 hεε hU hA
  rcases hcls with ⟨hb0, hc0, hda, ha1⟩ | ⟨ha0, hd0, hb', hbc⟩
  · subst hb0 hc0 hda
    simp only [zero_smul, add_zero, zero_add] at hge hgf
    by_cases haε : d' = ε
    · exfalso
      subst haε
      have hz : ∀ (i : Fin (s + 5 - 1)) u,
          g (minusVec (s + 5) i u) = d' • minusVec (s + 5) i u := by
        intro i u
        by_cases hi : 1 ≤ i.val
        · exact hU i hi u
        · have : i = ⟨0, h0⟩ := Fin.ext (by show i.val = 0; omega)
          subst this
          cases u
          · exact hgf
          · exact hge
      have hgs := eq_smul_of_eig hQ hgO hεε hz hA
      obtain ⟨y, hy, hne⟩ := hmov
      apply hne
      refine LinearEquiv.ext fun v => ?_
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgs, hgs v, map_smul]
    · have hneg : d' = -ε := by
        rcases ha1 with h | h <;> rcases hε with h' | h' <;> simp_all
      subst hneg
      refine commute_of_split hQ h0 hgO hεε hU hA (fun u => ?_) hYO hYe hYf
      cases u
      · exact hgf
      · exact hge
  · exfalso
    subst ha0 hd0
    simp only [zero_smul, zero_add] at hge
    simp only [zero_smul, add_zero] at hgf
    exact not_antidiag hg2 (a := 0) (b' := 1) h0 (by omega) (by omega) hεε hb' hbc hge hgf
      (fun u => hU ⟨1, by omega⟩ (by simp) u) hnorm

end Classify

end CFSG.ClassicalInvolution.RouteD.Gaps
