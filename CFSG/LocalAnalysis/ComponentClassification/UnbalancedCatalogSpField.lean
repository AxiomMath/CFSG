module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpDescent

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CatalogueBAlternatingIsometry CatalogueBSymplecticB
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace SpChain

theorem oddCore_centralizer_conj_eq_bot {M : Type*} [Group M] {H : Subgroup M} {b : M}
    (hb : b ∈ H) {x : M} (h : CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {x}) = ⊥) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {b * x * b⁻¹}) = ⊥ := by
  have hmap : (H ⊓ Subgroup.centralizer {x}).map (MulAut.conj b).toMonoidHom =
      H ⊓ Subgroup.centralizer {b * x * b⁻¹} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzH, hzC⟩ := Subgroup.mem_inf.mp hz
      have hzC' := Subgroup.mem_centralizer_singleton_iff.mp hzC
      refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hb hzH) (H.inv_mem hb),
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc b * z * b⁻¹ * (b * x * b⁻¹) = b * (z * x) * b⁻¹ := by group
        _ = b * (x * z) * b⁻¹ := by rw [hzC']
        _ = b * x * b⁻¹ * (b * z * b⁻¹) := by group
    · intro hy
      obtain ⟨hyH, hyC⟩ := Subgroup.mem_inf.mp hy
      have hyC' := Subgroup.mem_centralizer_singleton_iff.mp hyC
      refine ⟨b⁻¹ * y * b, Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem (H.inv_mem hb) hyH) hb,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, ?_⟩
      · calc b⁻¹ * y * b * x = b⁻¹ * (y * (b * x * b⁻¹)) * b := by group
          _ = b⁻¹ * ((b * x * b⁻¹) * y) * b := by rw [hyC']
          _ = x * (b⁻¹ * y * b) := by group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv
    (((H ⊓ Subgroup.centralizer {x}).equivMapOfInjective _ (MulAut.conj b).injective).trans
      (MulEquiv.subgroupCongr hmap)) h

section Field

variable {K : Type} [Field K]

theorem pow_map_comm {σ : K ≃+* K} {m : ℕ} (hσ : ∀ t, σ t = t ^ m) (φ : K ≃+* K) (t : K) :
    σ (φ t) = φ (σ t) := by
  rw [hσ, hσ, map_pow]

@[expose] def restrictDescent {σ : K ≃+* K} (hcomm : ∀ φ : K ≃+* K, ∀ t, σ (φ t) = φ (σ t))
    (φ : K ≃+* K) : descentField σ ≃+* descentField σ where
  toFun x := ⟨φ (x : K), by rw [mem_descentField, hcomm, coe_descentField_fixed]⟩
  invFun x := ⟨φ.symm (x : K), by rw [mem_descentField, hcomm, coe_descentField_fixed]⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x)
  right_inv x := Subtype.ext (φ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul φ (x : K) y)
  map_add' x y := Subtype.ext (map_add φ (x : K) y)

theorem coe_restrictDescent {σ : K ≃+* K} (hcomm : ∀ φ : K ≃+* K, ∀ t, σ (φ t) = φ (σ t))
    (φ : K ≃+* K) (x : descentField σ) : (restrictDescent hcomm φ x : K) = φ x :=
  rfl

@[expose] def restrictDescentHom {σ : K ≃+* K}
    (hcomm : ∀ φ : K ≃+* K, ∀ t, σ (φ t) = φ (σ t)) :
    (K ≃+* K) →* (descentField σ ≃+* descentField σ) where
  toFun := restrictDescent hcomm
  map_one' := RingEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := RingEquiv.ext fun _ => Subtype.ext rfl

theorem mem_zpowers_of_forall_fixed {f : ℕ} (hf : 2 ≤ f) (hfe : Even f)
    (hK : Nat.card K = 2 ^ f) {σ : K ≃+* K} (hσ : ∀ t, σ t = t ^ 2 ^ (f / 2)) :
    σ * σ = 1 ∧ σ ≠ 1 ∧
      ∀ φ : K ≃+* K, (∀ t ∈ descentField σ, φ t = t) → φ ∈ Subgroup.zpowers σ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨φ₀, hφ₀, hord, -, -, hfix⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
  obtain ⟨m, hm⟩ := hfe
  have hf2 : f / 2 = m := by omega
  have hσφ : σ = φ₀ ^ m := RingEquiv.ext fun t => by
    rw [hσ, ringAut_pow_apply_of_sq hφ₀, hf2]
  have hσσ : σ * σ = 1 := by
    rw [hσφ, ← pow_add, show m + m = f by omega, ← hord, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [hσφ] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h2
    exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
  refine ⟨hσσ, hσ1, fun φ hφ => ?_⟩
  obtain ⟨-, -, hcardk⟩ := ringEquiv_involution_facts (by omega) hK hσσ hσ1
  have : Finite (K ≃+* K) := Finite.of_injective (fun ψ : K ≃+* K => (ψ : K → K))
    fun ψ χ h => RingEquiv.ext (congrFun h)
  let A : Subgroup (K ≃+* K) :=
    { carrier := {ψ | ∀ t ∈ descentField σ, ψ t = t}
      mul_mem' := fun {ψ χ} hψ hχ t ht => by
        change ψ (χ t) = t
        rw [hχ t ht, hψ t ht]
      one_mem' := fun _ _ => rfl
      inv_mem' := fun {ψ} hψ t ht => by
        change ψ.symm t = t
        conv_lhs => rw [← hψ t ht]
        exact ψ.symm_apply_apply t }
  have hσA : Subgroup.zpowers σ ≤ A := by
    rw [Subgroup.zpowers_le]
    exact fun t ht => mem_descentField.mp ht
  obtain ⟨hAdvd, S, hS, hcardS⟩ := hfix A
  have hkS : Nat.card (descentField σ) ≤ Nat.card S := by
    refine Nat.card_mono (Set.toFinite _) fun t ht => ?_
    rw [hS]
    exact fun τ hτ => hτ t ht
  rw [hcardk, hcardS] at hkS
  have hle := (Nat.pow_le_pow_iff_right (by norm_num)).mp hkS
  obtain ⟨c, hc⟩ := hAdvd
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, mul_zero] at hc; omega
    · exact h0
  have hdiv : f / Nat.card A = c := by
    rw [hc, Nat.mul_div_cancel_left _ hApos]
  rw [hdiv, hf2] at hle
  have hA2 : Nat.card A ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have : 3 * c ≤ Nat.card A * c := Nat.mul_le_mul_right c hlt
    omega
  have hσcard : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq, hσσ]) hσ1
  have hAeq : Subgroup.zpowers σ = A :=
    Subgroup.eq_of_le_of_card_ge hσA (by rw [hσcard]; exact hA2)
  rw [hAeq]
  exact hφ

end Field

section Inclusion

variable {r : ℕ} {K : Type} [Field K]

variable (r) in
@[expose] def subfieldSpHom (k : Subfield K) : StatedSp r k →* StatedSp r K :=
  ((GeneralLinearGroup.map k.subtype).comp (StatedSp r k).subtype).codRestrict (StatedSp r K)
    fun g => UnitaryHigher.map_mem_statedSp k.subtype g.2

theorem spMat_subfieldSpHom (k : Subfield K) (g : StatedSp r k) :
    spMat (subfieldSpHom r k g) = (spMat g).map k.subtype :=
  rfl

theorem subfieldSpHom_injective (k : Subfield K) : Function.Injective (subfieldSpHom r k) := by
  intro g h hgh
  have h1 := congrArg spMat hgh
  rw [spMat_subfieldSpHom, spMat_subfieldSpHom] at h1
  exact Subtype.ext (Units.ext (Matrix.map_injective Subtype.val_injective h1))

theorem exists_subfieldSpHom_eq_of_mem (k : Subfield K) {g : StatedSp r K}
    (hg : ∀ i j, spMat g i j ∈ k) (hg' : ∀ i j, spMat g⁻¹ i j ∈ k) :
    ∃ g₀ : StatedSp r k, subfieldSpHom r k g₀ = g := by
  set M₀ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k := Matrix.of fun i j => ⟨spMat g i j, hg i j⟩
  set M₁ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k :=
    Matrix.of fun i j => ⟨spMat g⁻¹ i j, hg' i j⟩
  have hM₀ : M₀.map k.subtype = spMat g := rfl
  have hM₁ : M₁.map k.subtype = spMat g⁻¹ := rfl
  have hinj : Function.Injective (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k =>
      M.map k.subtype) := Matrix.map_injective Subtype.val_injective
  have h01 : M₀ * M₁ = 1 := hinj (by
    change (M₀ * M₁).map k.subtype = (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).map k.subtype
    rw [Matrix.map_mul, hM₀, hM₁, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (g : GL (Fin r ⊕ Fin r) K).mul_inv)
  have h10 : M₁ * M₀ = 1 := hinj (by
    change (M₁ * M₀).map k.subtype = (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).map k.subtype
    rw [Matrix.map_mul, hM₀, hM₁, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (g : GL (Fin r ⊕ Fin r) K).inv_mul)
  set G₀ : GL (Fin r ⊕ Fin r) k := ⟨M₀, M₁, h01, h10⟩
  have hG₀ : G₀ ∈ StatedSp r k := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff]
    apply hinj
    change (M₀ᵀ * fromBlocks 0 1 (-1) 0 * M₀).map k.subtype =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).map k.subtype
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hM₀,
      UnitaryHigher.formJ_map_ringHom]
    exact SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
  exact ⟨⟨G₀, hG₀⟩, Subtype.ext (Units.ext rfl)⟩

end Inclusion

section Fixed

variable {r : ℕ} {K : Type} [Field K] {σ : K ≃+* K}

theorem exists_subfieldSpHom_eq {g : StatedSp r K} (hg : fieldSp r K σ g = g) :
    ∃ g₀ : StatedSp r (descentField σ), subfieldSpHom r (descentField σ) g₀ = g := by
  have hfix : ∀ x : StatedSp r K, fieldSp r K σ x = x → ∀ i j, spMat x i j ∈ descentField σ := by
    intro x hx i j
    rw [mem_descentField]
    have h1 := congrArg (fun y : StatedSp r K => spMat y i j) hx
    exact h1
  refine exists_subfieldSpHom_eq_of_mem _ (hfix g hg) (hfix g⁻¹ ?_)
  rw [map_inv, hg]

theorem fieldSp_subfieldSpHom (g : StatedSp r (descentField σ)) :
    fieldSp r K σ (subfieldSpHom r (descentField σ) g) = subfieldSpHom r (descentField σ) g :=
  Subtype.ext (Units.ext (Matrix.ext fun i j => coe_descentField_fixed (spMat g i j)))

end Fixed

theorem spInner_mul_fieldAut_not_mem_inner_iff {r : ℕ} {K : Type} [Field K] [NeZero r]
    [CharP K 2] (g : StatedSp r K) (φ : K ≃+* K) :
    spInner r K g * fieldAut r K φ ∉ inner (StatedProj (StatedSp r K)) ↔ φ ≠ 1 := by
  constructor
  · rintro hI rfl
    rw [map_one, mul_one] at hI
    exact hI (spInner_mem_inner g)
  · intro hφ hI
    rw [← range_spInner] at hI
    obtain ⟨h, hh⟩ := hI
    have h1 : spInner r K h * fieldAut r K 1 = spInner r K g * fieldAut r K φ := by
      rw [map_one, mul_one, hh]
    exact hφ (spInner_mul_fieldAut_inj h1).2.symm

end SpChain

open SpChain

theorem even_symplectic_field_centralizers_and_intermediate_odd_cores {r f : ℕ} (hr : 2 ≤ r)
    (hf : 2 ≤ f) (hfe : Even f) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f)
    (σ : K ≃+* K) (hσ : ∀ t, σ t = t ^ 2 ^ (f / 2)) :
    ((spInner r K).comp (subfieldSpHom r (descentField σ))).range ≤
      inner (StatedProj (StatedSp r K)) ∧
    Function.Injective (subfieldSpHom r (descentField σ)) ∧
    Function.Injective ((spInner r K).comp (subfieldSpHom r (descentField σ))) ∧
    (∃ act : (K ≃+* K) →* MulAut (StatedSp r (descentField σ)),
      (∀ φ g, subfieldSpHom r (descentField σ) (act φ g) =
        fieldSp r K φ (subfieldSpHom r (descentField σ) g)) ∧
      ∃ Θ : StatedSp r (descentField σ) ⋊[act] (K ≃+* K) ≃*
          ↥(spSemilinearAutGroup r K ⊓ Subgroup.centralizer {fieldAut r K σ}),
        ∀ g φ, (Θ ⟨g, φ⟩ : MulAut (StatedProj (StatedSp r K))) =
          spInner r K (subfieldSpHom r (descentField σ) g) * fieldAut r K φ) ∧
    spSemilinearAutGroup r K ⊓ Subgroup.centralizer
        (((spInner r K).comp (subfieldSpHom r (descentField σ))).range :
          Set (MulAut (StatedProj (StatedSp r K)))) =
      Subgroup.zpowers (fieldAut r K σ) ∧
    ∀ H : Subgroup (MulAut (StatedProj (StatedSp r K))), inner (StatedProj (StatedSp r K)) ≤ H →
      H ≤ spSemilinearAutGroup r K → ∀ a ∈ H, orderOf a = 2 →
      a ∉ inner (StatedProj (StatedSp r K)) →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {a}) = ⊥ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  set k := descentField σ with hkdef
  set j := subfieldSpHom r k with hjdef
  set ιj := (spInner r K).comp j with hιjdef
  set N := ιj.range with hNdef
  set E := spSemilinearAutGroup r K with hEdef
  have hιinj := spInner_injective (r := r) (K := K)
  have hjinj : Function.Injective j := subfieldSpHom_injective k
  have hιjinj : Function.Injective ιj := hιinj.comp hjinj
  obtain ⟨hσσ, hσ1, hfixσ⟩ := mem_zpowers_of_forall_fixed hf hfe hK hσ
  have hcomm : ∀ φ : K ≃+* K, ∀ t, σ (φ t) = φ (σ t) := pow_map_comm hσ
  have hσφ : ∀ φ : K ≃+* K, σ * φ = φ * σ := fun φ => RingEquiv.ext fun t => hcomm φ t
  set act : (K ≃+* K) →* MulAut (StatedSp r k) :=
    (fieldSp r k).comp (restrictDescentHom hcomm) with hactdef
  have hact : ∀ φ g, j (act φ g) = fieldSp r K φ (j g) := fun φ g =>
    Subtype.ext (Units.ext (Matrix.ext fun _ _ => rfl))
  have hfσN : ∀ g, fieldAut r K σ * ιj g * (fieldAut r K σ)⁻¹ = ιj g := by
    intro g
    change fieldAut r K σ * spInner r K (j g) * _ = spInner r K (j g)
    rw [fieldAut_mul_spInner_mul_inv, fieldSp_subfieldSpHom]
  have hNσ : ∀ g, ιj g * fieldAut r K σ = fieldAut r K σ * ιj g := fun g => by
    calc ιj g * fieldAut r K σ
        _ = fieldAut r K σ * ιj g * (fieldAut r K σ)⁻¹ * fieldAut r K σ := by rw [hfσN]
        _ = fieldAut r K σ * ιj g := by group
  set Φ : StatedSp r k ⋊[act] (K ≃+* K) →* MulAut (StatedProj (StatedSp r K)) :=
    SemidirectProduct.lift ιj (fieldAut r K) fun φ => MonoidHom.ext fun g => by
      change spInner r K (j (act φ g)) =
        fieldAut r K φ * spInner r K (j g) * (fieldAut r K φ)⁻¹
      rw [fieldAut_mul_spInner_mul_inv, hact] with hΦdef
  have hΦ : ∀ g φ, Φ ⟨g, φ⟩ = spInner r K (j g) * fieldAut r K φ := fun _ _ => rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨g, φ⟩ h1
    rw [hΦ, show (1 : MulAut (StatedProj (StatedSp r K))) = spInner r K 1 * fieldAut r K 1 by
      rw [map_one, map_one, one_mul]] at h1
    obtain ⟨hg, hφ⟩ := spInner_mul_fieldAut_inj h1
    exact SemidirectProduct.ext (hjinj (by rw [hg, SemidirectProduct.one_left, map_one])) hφ
  have hΦrange : Φ.range = E ⊓ Subgroup.centralizer {fieldAut r K σ} := by
    apply le_antisymm
    · rintro _ ⟨⟨g, φ⟩, rfl⟩
      rw [hΦ]
      refine Subgroup.mem_inf.mpr ⟨mul_mem (spInner_mem_spSemilinearAutGroup _)
        (fieldAut_mem_spSemilinearAutGroup φ), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc spInner r K (j g) * fieldAut r K φ * fieldAut r K σ
          _ = spInner r K (j g) * fieldAut r K (σ * φ) := by rw [hσφ, map_mul, mul_assoc]
          _ = spInner r K (fieldSp r K σ (j g)) * fieldAut r K (σ * φ) := by
            rw [fieldSp_subfieldSpHom]
          _ = fieldAut r K σ * (spInner r K (j g) * fieldAut r K φ) := by
            rw [← fieldAut_mul_spInner_mul_inv, map_mul]
            group
    · intro α hα
      obtain ⟨hαE, hαC⟩ := Subgroup.mem_inf.mp hα
      obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut hαE
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hαC
      have h1 : spInner r K g * fieldAut r K (φ * σ) =
          spInner r K (fieldSp r K σ g) * fieldAut r K (σ * φ) := by
        calc spInner r K g * fieldAut r K (φ * σ)
            _ = spInner r K g * fieldAut r K φ * fieldAut r K σ := by rw [map_mul, mul_assoc]
            _ = fieldAut r K σ * (spInner r K g * fieldAut r K φ) := hc
            _ = fieldAut r K σ * spInner r K g * (fieldAut r K σ)⁻¹ * fieldAut r K (σ * φ) := by
              rw [map_mul]
              group
            _ = _ := by rw [fieldAut_mul_spInner_mul_inv]
      obtain ⟨hgσ, -⟩ := spInner_mul_fieldAut_inj h1
      obtain ⟨g₀, rfl⟩ := exists_subfieldSpHom_eq hgσ.symm
      exact ⟨⟨g₀, φ⟩, rfl⟩
  have hcentN : E ⊓ Subgroup.centralizer (N : Set (MulAut (StatedProj (StatedSp r K)))) =
      Subgroup.zpowers (fieldAut r K σ) := by
    apply le_antisymm
    · intro α hα
      obtain ⟨hαE, hαC⟩ := Subgroup.mem_inf.mp hα
      obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut hαE
      have hcj : ∀ g₀, g * fieldSp r K φ (j g₀) * g⁻¹ = j g₀ := by
        intro g₀
        have h1 := Subgroup.mem_centralizer_iff.mp hαC (ιj g₀) ⟨g₀, rfl⟩
        have h2 : spInner r K g * fieldAut r K φ * spInner r K (j g₀) *
            (spInner r K g * fieldAut r K φ)⁻¹ = spInner r K (j g₀) := by
          change _ * _ * ιj g₀ * _ = ιj g₀
          rw [← h1, mul_inv_cancel_right]
        rw [conj_spInner] at h2
        exact hιinj h2
      have hg1 : g = 1 := by
        have hcent : (g : GL (Fin r ⊕ Fin r) K) ∈
            Subgroup.centralizer (UnitaryHigher.primeFieldSp r K : Set (GL (Fin r ⊕ Fin r) K)) := by
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          have hhS : h ∈ StatedSp r K := UnitaryHigher.primeFieldSp_le hh
          obtain ⟨g₀, hg₀⟩ := exists_subfieldSpHom_eq (σ := σ) (g := ⟨h, hhS⟩)
            (Subtype.ext (UnitaryHigher.glFieldEquiv_primeFieldSp σ hh))
          have hfixφ : fieldSp r K φ (j g₀) = j g₀ := by
            rw [hg₀]
            exact Subtype.ext (UnitaryHigher.glFieldEquiv_primeFieldSp φ hh)
          have h3 := hcj g₀
          rw [hfixφ, hg₀] at h3
          have h4 : (g : GL (Fin r ⊕ Fin r) K) * h * (g : GL (Fin r ⊕ Fin r) K)⁻¹ = h :=
            congrArg Subtype.val h3
          calc h * g = (g * h * (g : GL (Fin r ⊕ Fin r) K)⁻¹) * g := by rw [h4]
            _ = g * h := by group
        rw [UnitaryHigher.centralizer_primeFieldSp] at hcent
        have hz : g ∈ spScalars r K := Subgroup.mem_subgroupOf.mpr hcent
        rwa [UnitaryHigher.spScalars_eq_bot_of_charTwo, Subgroup.mem_bot] at hz
      subst hg1
      have hφk : ∀ t ∈ k, φ t = t := by
        intro t ht
        set t' : k := ⟨t, ht⟩
        have hC : (t' • single (0 : Fin r) (0 : Fin r) (1 : k))ᵀ = t' • single 0 0 1 := by
          rw [transpose_smul, transpose_single]
        have h1 := hcj (upperUnipotentSp r k hC)
        rw [one_mul, inv_one, mul_one] at h1
        have h2 := congrArg (fun x : StatedSp r K => spMat x (Sum.inl 0) (Sum.inr 0)) h1
        change φ ((spMat (upperUnipotentSp r k hC) (Sum.inl 0) (Sum.inr 0) : k) : K) =
          ((spMat (upperUnipotentSp r k hC) (Sum.inl 0) (Sum.inr 0) : k) : K) at h2
        simpa [t'] using h2
      rw [map_one, one_mul]
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hfixσ φ hφk)
      exact ⟨n, by rw [map_zpow]⟩
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_inf.mpr ⟨fieldAut_mem_spSemilinearAutGroup σ,
        Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨g, rfl⟩
      exact hNσ g
  refine ⟨fun x hx => ?_, hjinj, hιjinj, ⟨act, hact, (MonoidHom.ofInjective hΦinj).trans
    (MulEquiv.subgroupCongr hΦrange), fun _ _ => rfl⟩, hcentN, ?_⟩
  · obtain ⟨g, rfl⟩ := hx
    exact spInner_mem_inner _
  intro H hIH hHE a haH ha2 haI
  obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut (hHE haH)
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at haI
    exact haI (spInner_mem_inner g)
  have haa : (spInner r K g * fieldAut r K φ) * (spInner r K g * fieldAut r K φ) = 1 := by
    rw [← sq, ← ha2, pow_orderOf_eq_one]
  obtain ⟨-, hφform, -, -, -, -, -, -, -, -, h, hh⟩ :=
    even_symplectic_quadratic_involution_descent (by omega) (by omega) hK haa g φ rfl hφ1
  have hφσ : φ = σ := RingEquiv.ext fun t => by rw [hφform, hσ]
  subst hφσ
  rw [← spInner_apply] at hh
  rw [hh]
  refine oddCore_centralizer_conj_eq_bot (hIH (spInner_mem_inner h)) ?_
  have hNC : N ≤ H ⊓ Subgroup.centralizer {fieldAut r K φ} := by
    rintro _ ⟨g₀, rfl⟩
    exact Subgroup.mem_inf.mpr ⟨hIH (spInner_mem_inner _),
      Subgroup.mem_centralizer_singleton_iff.mpr (hNσ g₀)⟩
  have hfσ2 : fieldAut r K φ ^ 2 = 1 := by rw [sq, ← map_mul, hσσ, map_one]
  refine oddCore_eq_bot_of_centralizer hNC ?_ ?_ ?_
  · intro c hc n hn
    obtain ⟨hcH, hcC⟩ := Subgroup.mem_inf.mp hc
    have hcR : c ∈ Φ.range := hΦrange ▸ Subgroup.mem_inf.mpr ⟨hHE hcH, hcC⟩
    obtain ⟨⟨g₁, φ₁⟩, rfl⟩ := hcR
    obtain ⟨g₀, rfl⟩ := hn
    refine ⟨g₁ * act φ₁ g₀ * g₁⁻¹, ?_⟩
    change spInner r K (j (g₁ * act φ₁ g₀ * g₁⁻¹)) =
      spInner r K (j g₁) * fieldAut r K φ₁ * spInner r K (j g₀) *
        (spInner r K (j g₁) * fieldAut r K φ₁)⁻¹
    rw [conj_spInner]
    congr 1
    rw [map_mul, map_mul, map_inv, hact]
  · intro X hXN hXn hodd
    refine eq_bot_of_oddCore_eq_bot ?_ hXN hXn hodd
    have hk2 : Nat.card k = 2 ^ (f / 2) :=
      (ringEquiv_involution_facts (by omega) hK hσσ hσ1).2.2
    have hSk := (even_symplectic_odd_core_including_field_two_rank_two hr
      (by omega : 1 ≤ f / 2) hk2).1
    exact EvenCatalog.oddCore_eq_bot_of_mulEquiv (MonoidHom.ofInjective hιjinj) hSk
  · intro c hc hcN
    obtain ⟨hcH, -⟩ := Subgroup.mem_inf.mp hc
    have hmem : c ∈ E ⊓ Subgroup.centralizer (N : Set (MulAut (StatedProj (StatedSp r K)))) :=
      Subgroup.mem_inf.mpr ⟨hHE hcH, Subgroup.mem_centralizer_iff.mpr fun n hn =>
        (hcN n hn).symm⟩
    rw [hcentN] at hmem
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨1, ?_⟩
    rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hfσ2,
      _root_.one_zpow]

end CFSG.ComponentClassification.UnbalancedCatalog
