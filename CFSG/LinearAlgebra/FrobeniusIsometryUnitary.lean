module

public import CFSG.LinearAlgebra.FrobeniusIsometryInverse
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBSemilinear
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankFix

public section

namespace CFSG.LinearAlgebra

open Module CFSG.LocalAnalysis.ComponentInitial

namespace FrobeniusIsometryUnitary

variable {K : Type} [Field K] [Finite K] {n : ℕ} (hK : UnitaryFieldData 2 n K)

include hK in
theorem card_fixedField : Nat.card hK.fixedField = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := hK.charP
  have hcard : Nat.card K = (2 ^ n) ^ 2 := by rw [hK.card, ← pow_mul, mul_comm]
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
    (K := K) (p := 2) (f := n) hcard
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq := CFSG.LocalAnalysis.RankThreeUC.card_fixedField_mul_self hσ h2
  have he : Nat.card hK.fixedField = Nat.card {c : K //
      CFSG.LieType.BorelTits.unitaryInvolution K 2 n c = c} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
    rw [UnitaryFieldData.mem_fixedField, UnitaryFieldData.bar_apply,
      CFSG.LieType.BorelTits.unitaryInvolution_apply]
  rw [he]
  rw [hcard, ← sq] at hsq
  exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hsq

include hK in
theorem exists_add_mul_of_not_mem {ω : K} (hω : ω ∉ hK.fixedField) (c : K) :
    ∃ a b : hK.fixedField, c = a + b * ω := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype hK.fixedField := Fintype.ofFinite _
  have hli : LinearIndependent hK.fixedField ![(1 : K), ω] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_contra hne
    have hb : b ≠ 0 := by
      intro hb
      subst hb
      rw [zero_smul, add_zero, smul_eq_zero] at hab
      exact hne ⟨hab.resolve_right one_ne_zero, rfl⟩
    apply hω
    have hω' : ω = ((-(a / b) : hK.fixedField) : K) := by
      rw [Subfield.coe_neg, Subfield.coe_div]
      have h1 : (a : K) + (b : K) * ω = 0 := by simpa [Subfield.smul_def] using hab
      have hb' : (b : K) ≠ 0 := by exact_mod_cast hb
      field_simp
      linear_combination h1
    rw [hω']
    exact (-(a / b)).2
  have hfr : finrank hK.fixedField K = 2 := by
    have h1 := Module.card_eq_pow_finrank (K := hK.fixedField) (V := K)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_fixedField hK, hK.card,
      ← pow_mul] at h1
    have h2 := (Nat.pow_right_injective le_rfl h1).symm
    have hn := hK.one_le
    exact Nat.eq_of_mul_eq_mul_left (show 0 < n by omega) (by rw [h2, mul_comm])
  have hspan : Submodule.span hK.fixedField (Set.range ![(1 : K), ω]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hfr])
  have hc : c ∈ Submodule.span hK.fixedField (Set.range ![(1 : K), ω]) := by
    rw [hspan]
    exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hc
  obtain ⟨f, hf⟩ := hc
  refine ⟨f 0, f 1, ?_⟩
  rw [← hf, Fin.sum_univ_two]
  simp [Subfield.smul_def]

@[expose] noncomputable def traceForm {V : Type} [AddCommGroup V] [Module K V]
    (hf : V →ₛₗ[hK.bar] V →ₗ[K] K) : LinearMap.BilinForm hK.fixedField V :=
  LinearMap.mk₂ hK.fixedField (fun v w => Algebra.trace hK.fixedField K (hf v w))
    (fun v v' w => by rw [map_add, LinearMap.add_apply, map_add])
    (fun c v w => by
      rw [Subfield.smul_def, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        show hK.bar (c : K) = c from c.2, ← smul_eq_mul, ← Subfield.smul_def, map_smul])
    (fun v w w' => by rw [map_add, map_add])
    (fun c v w => by rw [Subfield.smul_def, LinearMap.map_smul, ← Subfield.smul_def, map_smul])

omit [Finite K] in
theorem traceForm_apply {V : Type} [AddCommGroup V] [Module K V]
    (hf : V →ₛₗ[hK.bar] V →ₗ[K] K) (v w : V) :
    traceForm hK hf v w = Algebra.trace hK.fixedField K (hf v w) := rfl

theorem traceForm_symm {V : Type} [AddCommGroup V] [Module K V] (hf : V →ₛₗ[hK.bar] V →ₗ[K] K)
    (hherm : ∀ v w, hf w v = hK.bar (hf v w)) (v w : V) :
    traceForm hK hf v w = traceForm hK hf w v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := hK.charP
  let σ : K ≃ₐ[hK.fixedField] K := AlgEquiv.ofRingEquiv
    (f := CFSG.LieType.BorelTits.unitaryInvolution K 2 n) fun c => by
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
      exact c.2
  have hσ : ∀ c, σ c = hK.bar c := fun c => by
    change CFSG.LieType.BorelTits.unitaryInvolution K 2 n c = hK.bar c
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, UnitaryFieldData.bar_apply]
  rw [traceForm_apply, traceForm_apply, hherm v w, ← hσ, Algebra.trace_eq_of_algEquiv]

include hK in
theorem eq_zero_of_trace_mul_eq_zero {a : K}
    (ha : ∀ c : K, Algebra.trace hK.fixedField K (a * c) = 0) : a = 0 := by
  have : Finite hK.fixedField := Subtype.finite
  have : FiniteDimensional hK.fixedField K := Module.Finite.of_finite
  exact (traceForm_nondegenerate hK.fixedField K).1 a fun c => ha c

theorem traceForm_nondeg {V : Type} [AddCommGroup V] [Module K V] (hf : V →ₛₗ[hK.bar] V →ₗ[K] K)
    (hnd : ∀ v, (∀ w, hf v w = 0) → v = 0) (v : V) (hv : ∀ w, traceForm hK hf v w = 0) : v = 0 :=
  hnd v fun w => eq_zero_of_trace_mul_eq_zero hK fun c => by
    rw [mul_comm, ← smul_eq_mul, ← LinearMap.map_smul]
    exact hv (c • w)

@[expose] noncomputable def restrictHom (V : Type) [AddCommGroup V] [Module K V] :
    (V ≃ₗ[K] V) →* (V ≃ₗ[hK.fixedField] V) where
  toFun x := x.restrictScalars hK.fixedField
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite K] in
theorem restrictHom_apply {V : Type} [AddCommGroup V] [Module K V] (x : V ≃ₗ[K] V) (v : V) :
    restrictHom hK V x v = x v := rfl

end FrobeniusIsometryUnitary

open FrobeniusIsometryUnitary in
theorem exists_hermitian_isometry_conj_eq_pow_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : UnitaryFieldData 2 n K) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hf : V →ₛₗ[hK.bar] V →ₗ[K] K) (hherm : ∀ v w, hf w v = hK.bar (hf v w))
    (hnd : ∀ v, (∀ w, hf v w = 0) → v = 0) {E : Subgroup (V ≃ₗ[K] V)} [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hodd : Odd (Nat.card E))
    (hiso : ∀ x ∈ E, ∀ v w, hf (x v) (x w) = hf v w) :
    ∃ T : V ≃ₗ[K] V, (∀ v w, hf (T v) (T w) = hf v w) ∧
      (∀ x ∈ E, T * x * T⁻¹ = x ^ Nat.card K) ∧
      hK.bar (LinearMap.det (T : V →ₗ[K] V)) = LinearMap.det (T : V →ₗ[K] V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := hK.charP
  have : Fintype K := Fintype.ofFinite K
  have : Finite hK.fixedField := Subtype.finite
  have : Fintype hK.fixedField := Fintype.ofFinite _
  have : CharP hK.fixedField 2 := Subfield.charP _ 2
  have : FiniteDimensional hK.fixedField K := Module.Finite.of_finite
  have : FiniteDimensional hK.fixedField V := Module.Finite.trans K V
  have hK0 : Fintype.card hK.fixedField = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact card_fixedField hK
  obtain ⟨c₀, hc₀⟩ := hK.exists_bar_ne
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    exact hc₀ (map_zero _)
  set ω : K := hK.bar c₀ * c₀⁻¹ with hωdef
  have hω0 : ω ≠ 0 := mul_ne_zero (by rwa [ne_eq, map_eq_zero]) (inv_ne_zero hc₀0)
  have hb0 : hK.bar c₀ ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hωn : hK.bar ω * ω = 1 := by
    rw [hωdef, map_mul, map_inv₀, hK.bar_bar]
    field_simp
  have hωK0 : ω ∉ hK.fixedField := fun h => by
    have h1 : hK.bar ω = ω := h
    rw [h1] at hωn
    have h2 : (ω + 1) * (ω + 1) = 0 := by
      linear_combination hωn + (ω + 1) * (CharTwo.two_eq_zero (R := K))
    have h3 : ω = 1 := by
      have h4 := mul_self_eq_zero.mp h2
      linear_combination h4 - (CharTwo.two_eq_zero (R := K))
    apply hc₀
    rw [hωdef, mul_inv_eq_one₀ hc₀0] at h3
    exact h3
  clear_value ω
  let mω : V ≃ₗ[K] V := LinearEquiv.smulOfNeZero K V ω hω0
  let ρ := restrictHom hK V
  let S : Set (V ≃ₗ[hK.fixedField] V) := ρ '' (E : Set (V ≃ₗ[K] V)) ∪ {ρ mω}
  have hmω : ∀ x : V ≃ₗ[K] V, x * mω = mω * x := fun x => LinearEquiv.ext fun v => by
    change x (ω • v) = ω • x v
    rw [map_smul]
  have hS : S.Pairwise Commute := by
    have key : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
      rintro a (⟨x, hx, rfl⟩ | rfl) b (⟨y, hy, rfl⟩ | rfl)
      · rw [← map_mul, ← map_mul, hcomm x hx y hy]
      · rw [← map_mul, ← map_mul, hmω x]
      · rw [← map_mul, ← map_mul, hmω y]
      · rfl
    exact fun a ha b hb _ => key a ha b hb
  let Ê := Subgroup.closure S
  let : CommGroup Ê := Subgroup.closureCommGroupOfComm hS
  have hcommÊ : ∀ a ∈ Ê, ∀ b ∈ Ê, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : Ê) ⟨b, hb⟩)
  have : Finite V := Module.finite_of_finite hK.fixedField
  have : Finite (V ≃ₗ[hK.fixedField] V) :=
    Finite.of_injective (fun e : V ≃ₗ[hK.fixedField] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set N := Nat.card E * (2 ^ n + 1) with hN
  have hNodd : Odd N := hodd.mul (by
    rw [Nat.odd_add_one, Nat.not_odd_iff_even]
    exact (Nat.even_pow' (by have := hK.one_le; omega)).mpr even_two)
  have hmωpow : ∀ k : ℕ, ∀ v, (mω ^ k) v = ω ^ k • v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, mul_smul]
      rfl
  have hpowS : ∀ a ∈ S, a ^ N = 1 := by
    rintro a (⟨x, hx, rfl⟩ | rfl)
    · rw [← map_pow, hN, pow_mul]
      have hx' : x ^ Nat.card E = 1 := by
        have := pow_card_eq_one' (G := E) (x := ⟨x, hx⟩)
        exact congrArg Subtype.val this
      rw [hx', one_pow, map_one]
    · rw [← map_pow, hN, mul_comm, pow_mul]
      have hm1 : mω ^ (2 ^ n + 1) = 1 := LinearEquiv.ext fun v => by
        rw [hmωpow, pow_succ, ← UnitaryFieldData.bar_apply hK, hωn, one_smul]
        rfl
      rw [hm1, one_pow, map_one]
  have hpowÊ : ∀ a ∈ Ê, a ^ N = 1 := fun a ha => by
    induction ha using Subgroup.closure_induction with
    | mem a ha => exact hpowS a ha
    | one => exact one_pow N
    | mul a b ha hb iha ihb => rw [(Commute.mul_pow (hcommÊ a ha b hb)), iha, ihb, one_mul]
    | inv a _ iha => rw [inv_pow, iha, inv_one]
  have hoddÊ : Odd (Nat.card Ê) := by
    rw [Nat.odd_iff]
    by_contra h2
    have h2' : 2 ∣ Nat.card Ê := by omega
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Ê) 2 h2'
    have hyN : y ^ N = 1 := Subtype.ext (by simpa using hpowÊ y y.2)
    have := orderOf_dvd_of_pow_eq_one hyN
    rw [hy] at this
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr this)
  have hisoÊ : ∀ a ∈ Ê, ∀ v w, traceForm hK hf (a v) (a w) = traceForm hK hf v w := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with ⟨x, hx, rfl⟩ | rfl
      · intro v w
        rw [traceForm_apply, traceForm_apply, restrictHom_apply, restrictHom_apply, hiso x hx]
      · intro v w
        rw [traceForm_apply, traceForm_apply, restrictHom_apply, restrictHom_apply]
        change Algebra.trace _ K (hf (ω • v) (ω • w)) = _
        rw [LinearMap.map_smul, LinearMap.map_smulₛₗ₂, smul_eq_mul, smul_eq_mul, ← mul_assoc,
          mul_comm ω, hωn, one_mul]
    | one => intro v w; rfl
    | mul a b _ _ iha ihb => intro v w; exact (iha (b v) (b w)).trans (ihb v w)
    | inv a _ iha =>
      intro v w
      have h := iha (a.symm v) (a.symm w)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
      exact h.symm
  obtain ⟨g, hg, hconj, -⟩ := exists_isometry_conj_eq_pow_card (traceForm hK hf)
    (traceForm_symm hK hf hherm) (traceForm_nondeg hK hf hnd) hcommÊ hoddÊ hisoÊ
  have hgx : ∀ a ∈ Ê, ∀ v, g (a v) = (a ^ 2 ^ n) (g v) := fun a ha v => by
    have h := congrArg (fun f : V ≃ₗ[hK.fixedField] V => f (g v)) (hconj a ha)
    simpa [hK0] using h
  have hρpow : ∀ (x : V ≃ₗ[K] V) (k : ℕ) (v : V), (ρ x ^ k) v = (x ^ k) v := fun x k v => by
    rw [← map_pow]
    rfl
  have hgω : ∀ v, g (ω • v) = hK.bar ω • g v := fun v => by
    have h := hgx (ρ mω) (Subgroup.subset_closure (Or.inr rfl)) v
    rw [hρpow, hmωpow, ← UnitaryFieldData.bar_apply hK] at h
    exact h
  have hgsemi : ∀ (c : K) (v : V), g (c • v) = hK.bar c • g v := fun c v => by
    obtain ⟨a, b, rfl⟩ := exists_add_mul_of_not_mem hK hωK0 c
    have ha : ∀ u, g ((a : K) • u) = (a : K) • g u := fun u => by
      rw [← Subfield.smul_def, map_smul, Subfield.smul_def]
    have hb : ∀ u, g ((b : K) • u) = (b : K) • g u := fun u => by
      rw [← Subfield.smul_def, map_smul, Subfield.smul_def]
    rw [add_smul, mul_smul, map_add, ha, hb, hgω, map_add, map_mul,
      show hK.bar (a : K) = a from a.2, show hK.bar (b : K) = b from b.2, add_smul, mul_smul]
  let T : V ≃ₗ[K] V :=
    { toFun := fun v => g (g v)
      map_add' := fun v w => by rw [map_add, map_add]
      map_smul' := fun c v => by rw [hgsemi, hgsemi, hK.bar_bar, RingHom.id_apply]
      invFun := fun v => g.symm (g.symm v)
      left_inv := fun v => by simp
      right_inv := fun v => by simp }
  have hT : ∀ v, T v = g (g v) := fun _ => rfl
  refine ⟨T, fun v w => ?_, fun x hx => ?_, ?_⟩
  ·
    have h0 : hf (T v) (T w) - hf v w = 0 := eq_zero_of_trace_mul_eq_zero hK fun c => by
      rw [sub_mul, map_sub, mul_comm, ← smul_eq_mul, ← LinearMap.map_smul, ← map_smul T,
        mul_comm, ← smul_eq_mul, ← LinearMap.map_smul, ← traceForm_apply, ← traceForm_apply,
        hT, hT, hg, hg, sub_self]
    exact sub_eq_zero.mp h0
  · refine LinearEquiv.ext fun v => ?_
    change T (x (T.symm v)) = (x ^ Nat.card K) v
    obtain ⟨u, rfl⟩ := T.surjective v
    rw [LinearEquiv.symm_apply_apply, hT, hT]
    have h1 := hgx (ρ x) (Subgroup.subset_closure (Or.inl ⟨x, hx, rfl⟩)) u
    have h2 := hgx (ρ (x ^ 2 ^ n)) (Subgroup.subset_closure (Or.inl ⟨_, pow_mem hx _, rfl⟩))
      (g u)
    rw [restrictHom_apply, hρpow] at h1
    rw [restrictHom_apply, hρpow] at h2
    rw [h1, h2, ← pow_mul, ← pow_add, hK.card, two_mul]
  ·
    let τ : V ≃+ V := g.toAddEquiv
    have hτ : ∀ (c : K) (v : V), τ (c • v) = hK.bar c • τ v := hgsemi
    have hfix : CFSG.ComponentClassification.CatalogueBUnitaryB.semiConjEnd hK τ hτ
        (T : V →ₗ[K] V) = (T : V →ₗ[K] V) := LinearMap.ext fun v => by
      rw [CFSG.ComponentClassification.CatalogueBUnitaryB.semiConjEnd_apply]
      change g (g (g (g.symm v))) = g (g v)
      rw [LinearEquiv.apply_symm_apply]
    have h := CFSG.ComponentClassification.CatalogueBUnitaryB.det_semiConjEnd hK τ hτ
      (T : V →ₗ[K] V)
    rw [hfix] at h
    exact h.symm


open FrobeniusIsometryUnitary in
theorem exists_hermitian_isometry_conj_eq_inv_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : UnitaryFieldData 2 n K) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hf : V →ₛₗ[hK.bar] V →ₗ[K] K) (hherm : ∀ v w, hf w v = hK.bar (hf v w))
    (hnd : ∀ v, (∀ w, hf v w = 0) → v = 0) {E : Subgroup (V ≃ₗ[K] V)} [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hodd : Odd (Nat.card E))
    (hiso : ∀ x ∈ E, ∀ v w, hf (x v) (x w) = hf v w) :
    ∃ T : V ≃ₗ[K] V, (∀ v w, hf (T v) (T w) = hf v w) ∧ ∀ x ∈ E, T * x * T⁻¹ = x⁻¹ ^ 2 ^ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := hK.charP
  have : Fintype K := Fintype.ofFinite K
  have : Finite hK.fixedField := Subtype.finite
  have : Fintype hK.fixedField := Fintype.ofFinite _
  have : CharP hK.fixedField 2 := Subfield.charP _ 2
  have : FiniteDimensional hK.fixedField K := Module.Finite.of_finite
  have : FiniteDimensional hK.fixedField V := Module.Finite.trans K V
  have hK0 : Fintype.card hK.fixedField = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact card_fixedField hK
  obtain ⟨c₀, hc₀⟩ := hK.exists_bar_ne
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    exact hc₀ (map_zero _)
  set ω : K := hK.bar c₀ * c₀⁻¹ with hωdef
  have hω0 : ω ≠ 0 := mul_ne_zero (by rwa [ne_eq, map_eq_zero]) (inv_ne_zero hc₀0)
  have hb0 : hK.bar c₀ ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hωn : hK.bar ω * ω = 1 := by
    rw [hωdef, map_mul, map_inv₀, hK.bar_bar]
    field_simp
  have hωK0 : ω ∉ hK.fixedField := fun h => by
    have h1 : hK.bar ω = ω := h
    rw [h1] at hωn
    have h2 : (ω + 1) * (ω + 1) = 0 := by
      linear_combination hωn + (ω + 1) * (CharTwo.two_eq_zero (R := K))
    have h3 : ω = 1 := by
      have h4 := mul_self_eq_zero.mp h2
      linear_combination h4 - (CharTwo.two_eq_zero (R := K))
    apply hc₀
    rw [hωdef, mul_inv_eq_one₀ hc₀0] at h3
    exact h3
  clear_value ω
  let mω : V ≃ₗ[K] V := LinearEquiv.smulOfNeZero K V ω hω0
  let ρ := restrictHom hK V
  let S : Set (V ≃ₗ[hK.fixedField] V) := ρ '' (E : Set (V ≃ₗ[K] V)) ∪ {ρ mω}
  have hmω : ∀ x : V ≃ₗ[K] V, x * mω = mω * x := fun x => LinearEquiv.ext fun v => by
    change x (ω • v) = ω • x v
    rw [map_smul]
  have hS : S.Pairwise Commute := by
    have key : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
      rintro a (⟨x, hx, rfl⟩ | rfl) b (⟨y, hy, rfl⟩ | rfl)
      · rw [← map_mul, ← map_mul, hcomm x hx y hy]
      · rw [← map_mul, ← map_mul, hmω x]
      · rw [← map_mul, ← map_mul, hmω y]
      · rfl
    exact fun a ha b hb _ => key a ha b hb
  let Ê := Subgroup.closure S
  let : CommGroup Ê := Subgroup.closureCommGroupOfComm hS
  have hcommÊ : ∀ a ∈ Ê, ∀ b ∈ Ê, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : Ê) ⟨b, hb⟩)
  have : Finite V := Module.finite_of_finite hK.fixedField
  have : Finite (V ≃ₗ[hK.fixedField] V) :=
    Finite.of_injective (fun e : V ≃ₗ[hK.fixedField] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set N := Nat.card E * (2 ^ n + 1) with hN
  have hNodd : Odd N := hodd.mul (by
    rw [Nat.odd_add_one, Nat.not_odd_iff_even]
    exact (Nat.even_pow' (by have := hK.one_le; omega)).mpr even_two)
  have hmωpow : ∀ k : ℕ, ∀ v, (mω ^ k) v = ω ^ k • v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, mul_smul]
      rfl
  have hpowS : ∀ a ∈ S, a ^ N = 1 := by
    rintro a (⟨x, hx, rfl⟩ | rfl)
    · rw [← map_pow, hN, pow_mul]
      have hx' : x ^ Nat.card E = 1 := by
        have := pow_card_eq_one' (G := E) (x := ⟨x, hx⟩)
        exact congrArg Subtype.val this
      rw [hx', one_pow, map_one]
    · rw [← map_pow, hN, mul_comm, pow_mul]
      have hm1 : mω ^ (2 ^ n + 1) = 1 := LinearEquiv.ext fun v => by
        rw [hmωpow, pow_succ, ← UnitaryFieldData.bar_apply hK, hωn, one_smul]
        rfl
      rw [hm1, one_pow, map_one]
  have hpowÊ : ∀ a ∈ Ê, a ^ N = 1 := fun a ha => by
    induction ha using Subgroup.closure_induction with
    | mem a ha => exact hpowS a ha
    | one => exact one_pow N
    | mul a b ha hb iha ihb => rw [(Commute.mul_pow (hcommÊ a ha b hb)), iha, ihb, one_mul]
    | inv a _ iha => rw [inv_pow, iha, inv_one]
  have hoddÊ : Odd (Nat.card Ê) := by
    rw [Nat.odd_iff]
    by_contra h2
    have h2' : 2 ∣ Nat.card Ê := by omega
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Ê) 2 h2'
    have hyN : y ^ N = 1 := Subtype.ext (by simpa using hpowÊ y y.2)
    have := orderOf_dvd_of_pow_eq_one hyN
    rw [hy] at this
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr this)
  have hisoÊ : ∀ a ∈ Ê, ∀ v w, traceForm hK hf (a v) (a w) = traceForm hK hf v w := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with ⟨x, hx, rfl⟩ | rfl
      · intro v w
        rw [traceForm_apply, traceForm_apply, restrictHom_apply, restrictHom_apply, hiso x hx]
      · intro v w
        rw [traceForm_apply, traceForm_apply, restrictHom_apply, restrictHom_apply]
        change Algebra.trace _ K (hf (ω • v) (ω • w)) = _
        rw [LinearMap.map_smul, LinearMap.map_smulₛₗ₂, smul_eq_mul, smul_eq_mul, ← mul_assoc,
          mul_comm ω, hωn, one_mul]
    | one => intro v w; rfl
    | mul a b _ _ iha ihb => intro v w; exact (iha (b v) (b w)).trans (ihb v w)
    | inv a _ iha =>
      intro v w
      have h := iha (a.symm v) (a.symm w)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
      exact h.symm
  obtain ⟨g, hg, hconj, -⟩ := exists_isometry_conj_eq_pow_card (traceForm hK hf)
    (traceForm_symm hK hf hherm) (traceForm_nondeg hK hf hnd) hcommÊ hoddÊ hisoÊ
  obtain ⟨J, hJ, hJconj, -⟩ := exists_isometry_conj_eq_inv (traceForm hK hf)
    (traceForm_symm hK hf hherm) (traceForm_nondeg hK hf hnd) hcommÊ hoddÊ hisoÊ
  have hgx : ∀ a ∈ Ê, ∀ v, g (a v) = (a ^ 2 ^ n) (g v) := fun a ha v => by
    have h := congrArg (fun f : V ≃ₗ[hK.fixedField] V => f (g v)) (hconj a ha)
    simpa [hK0] using h
  have hJx : ∀ a ∈ Ê, ∀ v, J (a v) = a⁻¹ (J v) := fun a ha v => by
    have h := congrArg (fun f : V ≃ₗ[hK.fixedField] V => f (J v)) (hJconj a ha)
    simpa using h
  have hρpow : ∀ (x : V ≃ₗ[K] V) (k : ℕ) (v : V), (ρ x ^ k) v = (x ^ k) v := fun x k v => by
    rw [← map_pow]
    rfl
  have hρinv : ∀ (x : V ≃ₗ[K] V) (v : V), (ρ x)⁻¹ v = x⁻¹ v := fun x v => by
    rw [← map_inv]
    rfl
  have hsemi : ∀ G : V ≃ₗ[hK.fixedField] V, (∀ v, G (ω • v) = hK.bar ω • G v) →
      ∀ (c : K) (v : V), G (c • v) = hK.bar c • G v := fun G hG c v => by
    obtain ⟨a, b, rfl⟩ := exists_add_mul_of_not_mem hK hωK0 c
    have ha : ∀ u, G ((a : K) • u) = (a : K) • G u := fun u => by
      rw [← Subfield.smul_def, map_smul, Subfield.smul_def]
    have hb : ∀ u, G ((b : K) • u) = (b : K) • G u := fun u => by
      rw [← Subfield.smul_def, map_smul, Subfield.smul_def]
    rw [add_smul, mul_smul, map_add, ha, hb, hG, map_add, map_mul,
      show hK.bar (a : K) = a from a.2, show hK.bar (b : K) = b from b.2, add_smul, mul_smul]
  have hgsemi := hsemi g fun v => by
    have h := hgx (ρ mω) (Subgroup.subset_closure (Or.inr rfl)) v
    rw [hρpow, hmωpow, ← UnitaryFieldData.bar_apply hK] at h
    exact h
  have hωinv : ω⁻¹ = hK.bar ω := (eq_inv_of_mul_eq_one_left hωn).symm
  have hJsemi := hsemi J fun v => by
    have h := hJx (ρ mω) (Subgroup.subset_closure (Or.inr rfl)) v
    rw [hρinv] at h
    change J ((ρ mω) v) = _
    rw [h, ← hωinv]
    rfl
  let T : V ≃ₗ[K] V :=
    { toFun := fun v => g (J v)
      map_add' := fun v w => by rw [map_add, map_add]
      map_smul' := fun c v => by rw [hJsemi, hgsemi, hK.bar_bar, RingHom.id_apply]
      invFun := fun v => J.symm (g.symm v)
      left_inv := fun v => by simp
      right_inv := fun v => by simp }
  have hT : ∀ v, T v = g (J v) := fun _ => rfl
  refine ⟨T, fun v w => ?_, fun x hx => ?_⟩
  ·
    have h0 : hf (T v) (T w) - hf v w = 0 := eq_zero_of_trace_mul_eq_zero hK fun c => by
      rw [sub_mul, map_sub, mul_comm, ← smul_eq_mul, ← LinearMap.map_smul, ← map_smul T,
        mul_comm, ← smul_eq_mul, ← LinearMap.map_smul, ← traceForm_apply, ← traceForm_apply,
        hT, hT, hg, hJ, sub_self]
    exact sub_eq_zero.mp h0
  · refine LinearEquiv.ext fun v => ?_
    change T (x (T.symm v)) = (x⁻¹ ^ 2 ^ n) v
    obtain ⟨u, rfl⟩ := T.surjective v
    rw [LinearEquiv.symm_apply_apply, hT, hT]
    have h1 := hJx (ρ x) (Subgroup.subset_closure (Or.inl ⟨x, hx, rfl⟩)) u
    have h2 := hgx (ρ x⁻¹) (Subgroup.subset_closure (Or.inl ⟨_, inv_mem hx, rfl⟩)) (J u)
    rw [restrictHom_apply, hρinv] at h1
    rw [restrictHom_apply, hρpow] at h2
    rw [h1, h2]

end CFSG.LinearAlgebra
