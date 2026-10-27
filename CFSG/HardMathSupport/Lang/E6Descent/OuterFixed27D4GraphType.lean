module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4GraphAmbient
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.D4Three
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem graphType_fixedSubgroup_inv {G : Type*} [Group G] (β : MulAut G) :
    fixedSubgroup β⁻¹ = fixedSubgroup β := by
  ext x
  change β⁻¹ x = x ↔ β x = x
  constructor
  · intro h
    have h1 : β (β⁻¹ x) = β x := congrArg (fun y => β y) h
    rw [MulAut.apply_inv_self] at h1
    exact h1.symm
  · intro h
    have h1 : β⁻¹ (β x) = β⁻¹ x := congrArg (fun y => β⁻¹ y) h
    rw [MulAut.inv_apply_self] at h1
    exact h1.symm


theorem graphType_baseChange_normalForm {K : Type} [Field K] (L : Type) [Field L] (ι : K →+* L)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (T : K ≃+* K) (ε : ℕ)
    (u : adjointGroup Tag.D4 K) :
    baseChangeGL ι ((MulAut.conj g * (exactNormalAut Tag.D4 K a T 0 * d4Graph K ε)) u :
        ModGL Tag.D4 K) =
      baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
        baseChangeGL ι (Subtype.val (twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u) :
          ModGL Tag.D4 K) *
          (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a))⁻¹ := by
  have hP : Units.map (entrywiseHom (τ := Tag.D4) T.toRingHom) (d4P K ^ ε) = d4P K ^ ε := by
    rw [map_pow]
    exact congrArg (· ^ ε) (units_map_entrywiseHom_diagramMap (t := TwistTag.D4) T.toRingHom)
  have h1 : (Subtype.val (twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u) : ModGL Tag.D4 K) =
      d4P K ^ ε * Units.map (entrywiseHom T.toRingHom) (u : ModGL Tag.D4 K) * (d4P K ^ ε)⁻¹ := by
    have h := coe_twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u
    rw [zpow_natCast] at h
    exact h
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero, coe_d4Graph, h1]
  simp only [map_mul, map_inv, hP, mul_one, inv_one]
  group

theorem graphType_exists_ext {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) :
    ∃ (K₃ : Type) (_ : Field K₃) (_ : Finite K₃) (_ : CharP K₃ ℓ) (_ : Algebra K K₃),
      Nat.card K₃ = (ℓ ^ f) ^ 3 ∧ ∃ Fr : K₃ ≃+* K₃, ∀ c, Fr c = c ^ (ℓ ^ f) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  let _ : Algebra (ZMod ℓ) K := ZMod.algebra K ℓ
  have hfin : Module.finrank (ZMod ℓ) K = f := by
    have : Fintype K := Fintype.ofFinite K
    have h1 := Module.card_eq_pow_finrank (K := ZMod ℓ) (V := K)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK] at h1
    exact (Nat.pow_right_injective hℓ.two_le h1).symm
  have hf3 : f * 3 ≠ 0 := by omega
  have hdvd : Module.finrank (ZMod ℓ) K ∣ Module.finrank (ZMod ℓ) (GaloisField ℓ (f * 3)) := by
    rw [hfin, GaloisField.finrank ℓ hf3]
    exact Dvd.intro 3 rfl
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdvd
  let _ : Algebra K (GaloisField ℓ (f * 3)) := φ.toRingHom.toAlgebra
  refine ⟨GaloisField ℓ (f * 3), inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [GaloisField.card ℓ (f * 3) hf3, pow_mul]
  · have hinj : Function.Injective (iterateFrobenius (GaloisField ℓ (f * 3)) ℓ f) :=
      (iterateFrobenius (GaloisField ℓ (f * 3)) ℓ f).injective
    refine ⟨RingEquiv.ofBijective _ ⟨hinj, Finite.surjective_of_injective hinj⟩, fun c => ?_⟩
    exact iterateFrobenius_def ℓ f c

theorem graphType_baseChangeGL_d4P {K L : Type} [Field K] [Field L] (ι : K →+* L) :
    baseChangeGL ι (d4P K) = d4P L := baseChangeGL_diagramMap ι TwistTag.D4


section Cube

theorem graphType_cube_expand {G : Type*} [Group G] (x Q : G) :
    (x * Q) ^ 3 = x * (Q * x * Q⁻¹) * (Q * (Q * x * Q⁻¹) * Q⁻¹) * Q ^ 3 := by
  rw [pow_three']
  group

theorem graphType_cube_mem {F : Type} [Field F] (ε : ℕ) {x : ModGL Tag.D4 F}
    (hx : x ∈ adjointGroup Tag.D4 F) :
    (x * d4P F ^ ε) ^ 3 ∈ adjointGroup Tag.D4 F := by
  have hconj : ∀ y ∈ adjointGroup Tag.D4 F, d4P F ^ ε * y *
      (d4P F ^ ε)⁻¹ ∈ adjointGroup Tag.D4 F := fun y hy =>
    conj_mem_adjointGroup_of_map_eq (map_conj_pow_of_map_conj (d4P F)
      (map_conj_diagramMap TwistTag.D4 F (Or.inl rfl)) ε) y hy
  have hP3 : (d4P F ^ ε) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, show d4P F ^ 3 = 1 from
      diagramMap_pow_order TwistTag.D4 F, one_pow]
  rw [graphType_cube_expand, hP3, mul_one]
  exact mul_mem (mul_mem hx (hconj _ hx)) (hconj _ (hconj _ hx))

theorem graphType_cube_eq_one {K L : Type} [Field K] [Finite K] [Field L] (ι : K →+* L)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ)
    (hx : baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) ∈ adjointGroup Tag.D4 L)
    (hM : ∀ u : adjointGroup Tag.D4 K, baseChangeGL ι (α u : ModGL Tag.D4 K) =
      (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) * d4P L ^ ε) *
        baseChangeGL ι (u : ModGL Tag.D4 K) *
          (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
            d4P L ^ ε)⁻¹) :
    (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
      d4P L ^ ε) ^ 3 = 1 := by
  classical
  set M := baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
    d4P L ^ ε with hMdef
  have hcomm : ∀ w ∈ (adjointGroup Tag.D4 K).map (baseChangeGL ι), M ^ 3 * w = w * M ^ 3 := by
    rintro _ ⟨w', hw', rfl⟩
    set u : adjointGroup Tag.D4 K := ⟨w', hw'⟩ with hu
    have h3 : α (α (α u)) = u := by
      have : (α ^ 3) u = u := by rw [hα3]; rfl
      rwa [pow_three, MulAut.mul_apply, MulAut.mul_apply] at this
    have e' : M * (M * (M * baseChangeGL ι w' * M⁻¹) * M⁻¹) * M⁻¹ = baseChangeGL ι w' := by
      have := congrArg (fun y : adjointGroup Tag.D4 K => baseChangeGL ι (y : ModGL Tag.D4 K)) h3
      rw [hM (α (α u)), hM (α u), hM u] at this
      exact this
    have e'' : (M * M * M) * baseChangeGL ι w' * (M * M * M)⁻¹ = baseChangeGL ι w' := by
      calc (M * M * M) * baseChangeGL ι w' * (M * M * M)⁻¹ =
          M * (M * (M * baseChangeGL ι w' * M⁻¹) * M⁻¹) * M⁻¹ := by group
        _ = baseChangeGL ι w' := e'
    rw [pow_three']
    exact mul_inv_eq_iff_eq_mul.mp e''
  have hNad : M ^ 3 ∈ adjointGroup Tag.D4 L := graphType_cube_mem ε hx
  rcases lt_or_ge 2 (Nat.card K) with h2 | h2
  · obtain ⟨-, -, hfaith, -⟩ := Chevalley_large_finite_root_centralizer_faithfulness Tag.D4 K
      (by simpa using h2) L ι
    exact hfaith _ hNad hcomm
  ·
    have hK2 : Nat.card K = 2 := by
      have := Finite.one_lt_card (α := K)
      omega
    have : Fintype K := Fintype.ofFinite K
    have hu1 : ∀ u : Kˣ, u = 1 := by
      have h1 : Fintype.card Kˣ = 1 := by
        rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK2]
      intro u
      exact Fintype.card_le_one_iff.mp (le_of_eq h1) u 1
    have ha : a = 1 := funext fun i => hu1 (a i)
    rw [ha, rootDiagUnit_one, mul_one] at hMdef hx
    set n : ModGL Tag.D4 K := ((g : ModGL Tag.D4 K) * d4P K ^ ε) ^ 3 with hn
    have hMn : M ^ 3 = baseChangeGL ι n := by
      rw [hMdef, hn, map_pow, map_mul, map_pow, graphType_baseChangeGL_d4P]
    have hnad : n ∈ adjointGroup Tag.D4 K := graphType_cube_mem ε g.2
    have hcen : (⟨n, hnad⟩ : adjointGroup Tag.D4 K) ∈ Subgroup.center (adjointGroup Tag.D4 K) := by
      rw [Subgroup.mem_center_iff]
      intro u
      have := hcomm (baseChangeGL ι (u : ModGL Tag.D4 K)) ⟨u, u.2, rfl⟩
      rw [hMn, ← map_mul, ← map_mul] at this
      exact Subtype.ext (baseChangeGL_injective ι (by simpa using this.symm))
    rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcen
    have hn1 : n = 1 := congrArg Subtype.val hcen
    rw [hMn, hn1, map_one]

end Cube

section Inverse

variable {K : Type} [Field K]

theorem graphType_coe_normalForm (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ)
    (u : adjointGroup Tag.D4 K) :
    ((MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) u : ModGL Tag.D4 K) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε) * (u : ModGL Tag.D4 K) *
        ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε)⁻¹ := by
  have h1 : ∀ w : ModGL Tag.D4 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) w = w := by
    intro w
    have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
    rw [e1]
    exact Units.ext (entrywise_id (R := K) _)
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero, coe_d4Graph, h1]
  group

theorem graphType_baseChange_normalForm_one {L : Type} [Field L] (ι : K →+* L)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ) (u : adjointGroup Tag.D4 K) :
    baseChangeGL ι ((MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) u :
        ModGL Tag.D4 K) =
      (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) * d4P L ^ ε) *
        baseChangeGL ι (u : ModGL Tag.D4 K) *
          (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) * d4P L ^ ε)⁻¹ := by
  rw [graphType_coe_normalForm]
  simp only [map_mul, map_inv, map_pow, graphType_baseChangeGL_d4P]

theorem graphType_inv_normalForm (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) :
    ∃ (g' : adjointGroup Tag.D4 K) (a' : Fin Tag.D4.rank → Kˣ),
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 2))⁻¹ =
        MulAut.conj g' * (exactNormalAut Tag.D4 K a' 1 0 * d4Graph K 1) := by
  set a' : Fin Tag.D4.rank → Kˣ := fun i => (a (d4Rho.symm i))⁻¹ with ha'
  set g' : adjointGroup Tag.D4 K := exactNormalAut Tag.D4 K a' 1 0 (d4Graph K 1 g⁻¹) with hg'
  refine ⟨g', a', ?_⟩
  have hP3 : d4P K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  have hd : rootDiagUnit Tag.D4 a' = d4P K * (rootDiagUnit Tag.D4 a)⁻¹ * (d4P K)⁻¹ := by
    have hinv : rootDiagUnit Tag.D4 a⁻¹ = (rootDiagUnit Tag.D4 a)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← rootDiagUnit_mul, inv_mul_cancel, rootDiagUnit_one])
    have h : d4P K * rootDiagUnit Tag.D4 a⁻¹ = rootDiagUnit Tag.D4 a' * d4P K :=
      diagramMap_mul_rootDiagUnit (t := TwistTag.D4) (K := K) a⁻¹
    rw [hinv] at h
    calc rootDiagUnit Tag.D4 a' = (rootDiagUnit Tag.D4 a' * d4P K) * (d4P K)⁻¹ := by group
      _ = _ := by rw [← h]
  have hg'c : (g' : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 a' * (d4P K * (g : ModGL Tag.D4 K)⁻¹ * (d4P K)⁻¹) *
        (rootDiagUnit Tag.D4 a')⁻¹ := by
    have h1 : ∀ w : ModGL Tag.D4 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) w = w := by
      intro w
      have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
      rw [e1]
      exact Units.ext (entrywise_id (R := K) _)
    rw [hg', coe_exactNormalAut, exactQ_zero, coe_d4Graph, h1]
    simp only [Subgroup.coe_inv, pow_one, inv_one, mul_one]
  have hprod : ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ 2) *
      ((g' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a' * d4P K ^ 1) = 1 := by
    rw [hg'c, hd]
    calc _ = (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ 3 *
          (rootDiagUnit Tag.D4 a)⁻¹ * (g : ModGL Tag.D4 K)⁻¹ := by group
      _ = 1 := by rw [hP3]; group
  refine inv_eq_of_mul_eq_one_right (MulEquiv.ext fun u => Subtype.ext ?_)
  rw [MulAut.mul_apply, graphType_coe_normalForm, graphType_coe_normalForm, MulAut.one_apply]
  have hinv : ((g' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a' * d4P K ^ 1) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  rw [hinv]
  group

end Inverse

section Graph

theorem twentySeven_dvd_card_fixedSubgroup_graph_one {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨K₃, _, _, _, _, hK₃, Fr, hFr⟩ := graphType_exists_ext hf K hK
  set L := AlgebraicClosure K₃ with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K₃ L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₃
  set ιK : K →+* K₃ := algebraMap K K₃ with hιK
  set ιL : K₃ →+* L := algebraMap K₃ L with hιL
  set ιLK : K →+* L := ιL.comp ιK with hιLK
  set x : ModGL Tag.D4 L := baseChangeGL ιLK ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a)
    with hxdef
  have hx : x ∈ adjointGroup Tag.D4 L := by
    rw [hxdef, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2)
      (exceptional_Lang_adjoint_diagonal_lift Tag.D4 L _).1
  have hFrc : (iterateFrobenius L ℓ f).comp ιLK = ιLK := by
    ext c
    simp only [RingHom.comp_apply, iterateFrobenius_def, hιLK, ← map_pow]
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hxF : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x := by
    rw [hxdef, units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hFrc]
  have hM : ∀ u : adjointGroup Tag.D4 K, baseChangeGL ιLK (α u : ModGL Tag.D4 K) =
      (x * d4P L ^ 1) * baseChangeGL ιLK (u : ModGL Tag.D4 K) * (x * d4P L ^ 1)⁻¹ := by
    intro u
    have h := graphType_baseChange_normalForm_one ιLK g a 1 u
    rw [← hα] at h
    exact h
  have hαx : ∀ u : adjointGroup Tag.D4 K, baseChangeGL ιLK (α u : ModGL Tag.D4 K) =
      x * (d4P L * baseChangeGL ιLK (u : ModGL Tag.D4 K) * (d4P L)⁻¹) * x⁻¹ := by
    intro u
    rw [hM u, pow_one]
    group
  have hxP : (x * d4P L) ^ 3 = 1 := by
    have := graphType_cube_eq_one ιLK α hα3 g a 1 hx hM
    rwa [pow_one] at this
  set g₃ : adjointGroup Tag.D4 K₃ := ⟨baseChangeGL ιK (g : ModGL Tag.D4 K),
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2⟩ with hg₃
  set a₃ : Fin Tag.D4.rank → K₃ˣ := fun i => Units.map ιK.toMonoidHom (a i) with ha₃
  have hx3' : (g₃ : ModGL Tag.D4 K₃) * rootDiagUnit Tag.D4 a₃ =
      baseChangeGL ιK ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) := by
    rw [map_mul, baseChangeGL_rootDiagUnit]
  have hx3 : baseChangeGL ιL ((g₃ : ModGL Tag.D4 K₃) * rootDiagUnit Tag.D4 a₃) = x := by
    rw [hx3', hxdef, baseChangeGL_baseChangeGL]
  exact twentySeven_dvd_card_fixedSubgroup_graph_ambient hf K hK K₃ hK₃ Fr hFr L x hx hxF hxP
    (MulAut.conj g₃ * (exactNormalAut Tag.D4 K₃ a₃ Fr 0 * d4Graph K₃ 1))
    (fun u => by
      have h := graphType_baseChange_normalForm L ιL g₃ a₃ Fr 1 u
      rw [hx3] at h
      exact h)
    α hαx

theorem twentySeven_dvd_card_fixedSubgroup_graph {ℓ f : ℕ} [Fact ℓ.Prime]
    (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (_h3 : ¬ 3 ∣ ℓ)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ) (hε : ε < 3) (hε0 : ε ≠ 0)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  have hf : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, hf0, pow_zero] at this
    omega
  interval_cases ε
  · exact absurd rfl hε0
  · exact twentySeven_dvd_card_fixedSubgroup_graph_one hf K hK α hα3 g a hα
  · obtain ⟨g', a', hinv⟩ := graphType_inv_normalForm g a
    rw [← hα] at hinv
    have h3' : α⁻¹ ^ 3 = 1 := by rw [inv_pow, hα3, inv_one]
    rw [← graphType_fixedSubgroup_inv α]
    exact twentySeven_dvd_card_fixedSubgroup_graph_one hf K hK α⁻¹ h3' g' a' hinv

end Graph

end CFSG.HardMathSupport.Lang.E6Descent
