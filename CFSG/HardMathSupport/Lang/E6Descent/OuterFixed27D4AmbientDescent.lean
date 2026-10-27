module

public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LieType.Chevalley.ChevalleyLargeRootCentralizerFaithful

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.GroupTheory


section Aut

variable (t : TwistTag) {K : Type} [Field K]

@[expose] def twistedEntrywiseAut (j : ℤ) (σ : K ≃+* K) : MulAut (adjointGroup t.tag K) :=
  diagramConjAut t K ^ j * entrywiseAdjointAut t.tag σ

theorem coe_twistedEntrywiseAut (j : ℤ) (σ : K ≃+* K) (u : adjointGroup t.tag K) :
    (twistedEntrywiseAut t j σ u : ModGL t.tag K) = diagramMap t K ^ j *
      Units.map (entrywiseHom σ.toRingHom) (u : ModGL t.tag K) * (diagramMap t K ^ j)⁻¹ := by
  rw [twistedEntrywiseAut, MulAut.mul_apply, coe_diagramConjAut_zpow, coe_entrywiseAdjointAut]

theorem units_map_entrywiseHom_diagramMap_zpow (σ : K →+* K) (j : ℤ) :
    Units.map (entrywiseHom σ) (diagramMap t K ^ j) = diagramMap t K ^ j := by
  rw [map_zpow, units_map_entrywiseHom_diagramMap]

theorem diagramConjAut_zpow_comm (j : ℤ) (σ : K ≃+* K) :
    Commute (diagramConjAut t K ^ j) (entrywiseAdjointAut t.tag σ) := by
  refine MulEquiv.ext fun u => Subtype.ext ?_
  change ((diagramConjAut t K ^ j) (entrywiseAdjointAut t.tag σ u) : ModGL t.tag K) =
    (entrywiseAdjointAut t.tag σ ((diagramConjAut t K ^ j) u) : ModGL t.tag K)
  rw [coe_diagramConjAut_zpow, coe_entrywiseAdjointAut, coe_entrywiseAdjointAut,
    coe_diagramConjAut_zpow, map_mul, map_mul, map_inv, units_map_entrywiseHom_diagramMap_zpow]

theorem twistedEntrywiseAut_pow (j : ℤ) (σ : K ≃+* K) (n : ℕ) :
    twistedEntrywiseAut t j σ ^ n = diagramConjAut t K ^ (j * n) * entrywiseAdjointAut t.tag (σ ^ n) := by
  unfold twistedEntrywiseAut
  rw [(diagramConjAut_zpow_comm t j σ).mul_pow, ← zpow_natCast, ← zpow_mul,
    entrywiseAdjointAut_pow]

theorem twistedEntrywiseAut_pow_order (j : ℤ) (σ : K ≃+* K) (hσ : σ ^ t.order = 1) :
    twistedEntrywiseAut t j σ ^ t.order = 1 := by
  rw [twistedEntrywiseAut_pow, hσ, entrywiseAdjointAut_one, mul_one]
  have h1 : diagramMap t K ^ (j * (t.order : ℤ)) = 1 := by
    rw [mul_comm, zpow_mul, zpow_natCast, diagramMap_pow_order, one_zpow]
  refine MulEquiv.ext fun u => Subtype.ext ?_
  rw [coe_diagramConjAut_zpow, MulAut.one_apply, h1]
  group

end Aut

section Descent

theorem exists_conj_eq_twistedEntrywiseAut_of_ambient (t : TwistTag) {ℓ f e : ℕ} [Fact ℓ.Prime]
    (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e) (hef : e * t.order = f) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ e)) (j : ℤ) (L : Type) [Field L] [CharP L ℓ] [Algebra K L]
    [IsAlgClosure K L]
    (x : ModGL t.tag L) (hx : x ∈ adjointGroup t.tag L) (β : MulAut (adjointGroup t.tag K))
    (hβ : ∀ u : adjointGroup t.tag K, baseChangeGL (algebraMap K L) (β u : ModGL t.tag K) =
      x * baseChangeGL (algebraMap K L) (twistedEntrywiseAut t j T u : ModGL t.tag K) * x⁻¹)
    (hβm : β ^ t.order = 1) :
    ∃ (ψ : MulAut (adjointGroup t.tag K)) (h : adjointGroup t.tag L),
      Units.map (entrywiseHom ((iterateFrobenius L ℓ e) ^ t.order)) (h : ModGL t.tag L) = h ∧
      (∀ u : adjointGroup t.tag K, baseChangeGL (algebraMap K L) (ψ u : ModGL t.tag K) =
        (h : ModGL t.tag L) * baseChangeGL (algebraMap K L) (u : ModGL t.tag K) *
          (h : ModGL t.tag L)⁻¹) ∧
      ψ * β * ψ⁻¹ = twistedEntrywiseAut t j T := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hm1 : 1 ≤ t.order := by cases t <;> decide
  have hTm : T ^ t.order = 1 := by
    refine RingEquiv.ext fun c => ?_
    rw [ringEquiv_pow_apply, RingAut.one_apply]
    have hit : ∀ n : ℕ, (⇑T)^[n] c = c ^ ((ℓ ^ e) ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Function.iterate_succ_apply', ih, hT, pow_succ, pow_mul]
    rw [hit, ← pow_mul, hef, ← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  obtain ⟨S, hS, hLang⟩ := (exceptional_all_characteristic_field_Lang_surjectivity ℓ L e he).2 t j
  let ι : adjointGroup t.tag K →* adjointGroup t.tag L :=
    ((baseChangeGL (algebraMap K L)).comp (adjointGroup t.tag K).subtype).codRestrict
      (adjointGroup t.tag L) fun u => baseChangeGL_mem_adjointGroup (algebraMap K L) u.2
  have hι : ∀ u, (ι u : ModGL t.tag L) = baseChangeGL (algebraMap K L) u := fun _ => rfl
  have hFrc : (iterateFrobenius L ℓ e).comp (algebraMap K L) =
      (algebraMap K L).comp T.toRingHom := by
    ext c
    simp [iterateFrobenius_def, hT, map_pow]
  have hFι : ∀ w : ModGL t.tag K, Units.map (entrywiseHom (iterateFrobenius L ℓ e))
      (baseChangeGL (algebraMap K L) w) =
        baseChangeGL (algebraMap K L) (Units.map (entrywiseHom T.toRingHom) w) := fun w => by
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hFrc]
  have hQ : baseChangeGL (algebraMap K L) (diagramMap t K ^ j) = diagramMap t L ^ j := by
    rw [map_zpow, baseChangeGL_diagramMap]
  have hSι : ∀ u, S (ι u) = ι (twistedEntrywiseAut t j T u) := fun u => Subtype.ext (by
    rw [hS, hι, hι, coe_twistedEntrywiseAut, hFι, map_mul, map_mul, map_inv, hQ])
  have hSpow : ∀ (n : ℕ) (u : adjointGroup t.tag K),
      (S ^ n) (ι u) = ι ((twistedEntrywiseAut t j T ^ n) u) := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      rw [pow_succ', MulAut.mul_apply, ih, hSι, pow_succ', MulAut.mul_apply]
  let x' : adjointGroup t.tag L := ⟨x, hx⟩
  have hx'v : (x' : ModGL t.tag L) = x := rfl
  have hext : ∀ u, (MulAut.conj x' * S) (ι u) = ι (β u) := fun u => Subtype.ext (by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hSι, hι, hι, hβ, hx'v])
  have hextpow : ∀ (n : ℕ) (u : adjointGroup t.tag K),
      ((MulAut.conj x' * S) ^ n) (ι u) = ι ((β ^ n) u) := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      rw [pow_succ', MulAut.mul_apply, ih, hext, pow_succ', MulAut.mul_apply]
  set N := ((List.range t.order).map fun i => (S ^ i) x').prod with hN
  have hNc : ∀ u, N * ι u * N⁻¹ = ι u := by
    intro u
    have h1 := hextpow t.order u
    rw [hβm, MulAut.one_apply, conj_mul_pow, MulAut.mul_apply, MulAut.conj_apply, hSpow,
      twistedEntrywiseAut_pow_order t j T hTm, MulAut.one_apply] at h1
    exact h1
  have hN1 : N = 1 := by
    obtain ⟨-, -, hfaith, -⟩ :=
      Chevalley_large_finite_root_centralizer_faithfulness_of_four_le t.tag K hK4 L
        (algebraMap K L)
    refine Subtype.ext (hfaith _ N.2 fun w hw => ?_)
    obtain ⟨u, hu, rfl⟩ := hw
    have h1 : (N : ModGL t.tag L) * baseChangeGL (algebraMap K L) u * (N : ModGL t.tag L)⁻¹ =
        baseChangeGL (algebraMap K L) u := congrArg Subtype.val (hNc ⟨u, hu⟩)
    calc (N : ModGL t.tag L) * baseChangeGL (algebraMap K L) u =
        (N : ModGL t.tag L) * baseChangeGL (algebraMap K L) u * (N : ModGL t.tag L)⁻¹ * N := by
          group
      _ = baseChangeGL (algebraMap K L) u * N := by rw [h1]
  have hiter : ∀ (i : ℕ) (y : adjointGroup t.tag L), (⇑S.toMonoidHom)^[i] y = (S ^ i) y := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih =>
      intro y
      rw [Function.iterate_succ_apply', ih, pow_succ', MulAut.mul_apply]
      rfl
  have hnorm : ((List.range t.order).map fun i => (⇑S.toMonoidHom)^[i] x').prod = 1 :=
    (congrArg List.prod (List.map_congr_left fun i _ => hiter i x')).trans hN1
  obtain ⟨h, hR, hxh, -⟩ := exceptional_Lang_norm_one_descent S.toMonoidHom hm1 hLang x' hnorm
  have hFrK : ∀ c : L, ((iterateFrobenius L ℓ e) ^ t.order) c = c ^ Nat.card K := by
    intro c
    rw [RingHom.coe_pow]
    have hit : ∀ n : ℕ, (⇑(iterateFrobenius L ℓ e))^[n] c = c ^ ((ℓ ^ e) ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih, iterateFrobenius_def, pow_succ, pow_mul]
    rw [hit, ← pow_mul, hef, hK]
  have hFrQ : Units.map (entrywiseHom (iterateFrobenius L ℓ e)) (diagramMap t L ^ j) =
      diagramMap t L ^ j := units_map_entrywiseHom_diagramMap_zpow t _ j
  have hiterS : ∀ (n : ℕ) (g : adjointGroup t.tag L), (((⇑S.toMonoidHom)^[n] g :
      adjointGroup t.tag L) : ModGL t.tag L) = (diagramMap t L ^ j) ^ n *
        Units.map (entrywiseHom ((iterateFrobenius L ℓ e) ^ n)) g * ((diagramMap t L ^ j) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro g
      rw [Function.iterate_zero, id_eq, pow_zero, pow_zero, inv_one, one_mul, mul_one]
      refine Units.ext ?_
      rw [Units.coe_map, RingHom.one_def]
      exact (entrywise_id (R := L) _).symm
    | succ n ih =>
      intro g
      have hS1 : ∀ g, ((S.toMonoidHom g : adjointGroup t.tag L) : ModGL t.tag L) =
          diagramMap t L ^ j * Units.map (entrywiseHom (iterateFrobenius L ℓ e)) g *
            (diagramMap t L ^ j)⁻¹ := hS
      rw [Function.iterate_succ_apply', hS1, ih, map_mul, map_mul, map_inv, map_pow, hFrQ]
      have hcomp : Units.map (entrywiseHom (iterateFrobenius L ℓ e))
          (Units.map (entrywiseHom ((iterateFrobenius L ℓ e) ^ n)) (g : ModGL t.tag L)) =
            Units.map (entrywiseHom ((iterateFrobenius L ℓ e) ^ (n + 1))) (g : ModGL t.tag L) := by
        refine Units.ext ?_
        rw [Units.coe_map, Units.coe_map, Units.coe_map, pow_succ', RingHom.mul_def]
        exact entrywise_entrywise (R := L) _ _ _
      rw [hcomp, pow_succ']
      group
  have hhfix : (h : ModGL t.tag L) ∈ adjointGroup t.tag L ⊓
      (Units.map (entrywiseHom ((iterateFrobenius L ℓ e) ^ t.order))).eqLocus
        (MonoidHom.id _) := by
    refine ⟨h.2, ?_⟩
    have h1 := hiterS t.order h
    rw [mem_iterateFixedSubgroup.1 hR, diagramMap_zpow_pow_order t j] at h1
    simp only [inv_one, one_mul, mul_one] at h1
    exact h1.symm
  obtain ⟨-, -, hnorml⟩ := Chevalley_Frobenius_fixed_ambient_normalizer t.tag K L _ hFrK
  have hmap : ((adjointGroup t.tag K).map (baseChangeGL (algebraMap K L))).map
      (MulAut.conj (h : ModGL t.tag L)).toMonoidHom =
        (adjointGroup t.tag K).map (baseChangeGL (algebraMap K L)) :=
    map_conj_eq_of_mem_normalizer (hnorml hhfix)
  let eH : adjointGroup t.tag K ≃* (adjointGroup t.tag K).map (baseChangeGL (algebraMap K L)) :=
    Subgroup.equivMapOfInjective (adjointGroup t.tag K) (baseChangeGL (algebraMap K L))
      (baseChangeGL_injective _)
  have heH : ∀ u, ((eH u : (adjointGroup t.tag K).map (baseChangeGL (algebraMap K L))) :
      ModGL t.tag L) = baseChangeGL (algebraMap K L) u := fun u =>
    Subgroup.coe_equivMapOfInjective_apply _ _ _ _
  let δ : MulAut (adjointGroup t.tag K) :=
    eH.trans ((mulAutRestrict _ (MulAut.conj (h : ModGL t.tag L)) hmap).trans eH.symm)
  have hδ : ∀ u, baseChangeGL (algebraMap K L) (δ u : ModGL t.tag K) =
      (h : ModGL t.tag L) * baseChangeGL (algebraMap K L) u * (h : ModGL t.tag L)⁻¹ := by
    intro u
    rw [← heH, ← heH]
    change ((eH (eH.symm (mulAutRestrict _ (MulAut.conj (h : ModGL t.tag L)) hmap (eH u))) :
      (adjointGroup t.tag K).map (baseChangeGL (algebraMap K L))) : ModGL t.tag L) = _
    rw [MulEquiv.apply_symm_apply, coe_mulAutRestrict, MulAut.conj_apply]
  have hδ' : ∀ u, ι (δ u) = h * ι u * h⁻¹ := fun u => Subtype.ext (by
    rw [hι, hδ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hι])
  refine ⟨δ, h, ?_, hδ, MulEquiv.ext fun u => ?_⟩
  · have h1 := hiterS t.order h
    rw [mem_iterateFixedSubgroup.1 hR, diagramMap_zpow_pow_order t j] at h1
    simp only [inv_one, one_mul, mul_one] at h1
    exact h1.symm
  · obtain ⟨v, rfl⟩ : ∃ v, δ v = u := ⟨δ⁻¹ u, by rw [MulAut.apply_inv_self]⟩
    have hι_inj : Function.Injective ι := fun a b hab => Subtype.ext
      (baseChangeGL_injective (algebraMap K L) (by rw [← hι, ← hι, hab]))
    apply hι_inj
    change ι (δ (β (δ⁻¹ (δ v)))) = ι (twistedEntrywiseAut t j T (δ v))
    have hxh' : x' = h⁻¹ * S h := hxh
    rw [MulAut.inv_apply_self, hδ', ← hext, MulAut.mul_apply, MulAut.conj_apply, hxh',
      ← hSι, hδ', map_mul, map_mul, map_inv]
    group

theorem exists_conj_eq_twistedEntrywiseAut (t : TwistTag) {ℓ f e : ℕ} [Fact ℓ.Prime]
    (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e) (hef : e * t.order = f) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ e)) (j : ℤ) (L : Type) [Field L] [CharP L ℓ] [Algebra K L]
    [IsAlgClosure K L]
    (x : ModGL t.tag L) (hx : x ∈ adjointGroup t.tag L) (β : MulAut (adjointGroup t.tag K))
    (hβ : ∀ u : adjointGroup t.tag K, baseChangeGL (algebraMap K L) (β u : ModGL t.tag K) =
      x * baseChangeGL (algebraMap K L) (twistedEntrywiseAut t j T u : ModGL t.tag K) * x⁻¹)
    (hβm : β ^ t.order = 1) :
    ∃ ψ : MulAut (adjointGroup t.tag K), ψ * β * ψ⁻¹ = twistedEntrywiseAut t j T := by
  obtain ⟨ψ, -, -, -, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_ambient t K hK hK4 he hef T hT j
    L x hx β hβ hβm
  exact ⟨ψ, hψ⟩

end Descent

end CFSG.HardMathSupport.Lang.E6Descent
