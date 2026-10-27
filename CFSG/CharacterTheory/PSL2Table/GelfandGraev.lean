module

public import CFSG.CharacterTheory.PSL2Table.Norms

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups
open CFSG.TwoRankLowerBound.Helpers

section ClassFormula

variable {K : Type} [Group K] [Fintype K]

omit [Fintype K] in
theorem card_conjugators' (g h : K) [Decidable (IsConj g h)] :
    Nat.card {x : K // x⁻¹ * g * x = h} =
      if IsConj g h then Nat.card (Subgroup.centralizer {g} : Subgroup K) else 0 := by
  by_cases hgh : IsConj g h
  · rw [ite_eq_left hgh]
    obtain ⟨k, hk⟩ := isConj_iff.mp hgh
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1 * k, ?_⟩
        invFun := fun c => ⟨c.1 * k⁻¹, ?_⟩
        left_inv := fun x => Subtype.ext (mul_inv_cancel_right _ _)
        right_inv := fun c => Subtype.ext (inv_mul_cancel_right _ _) }
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hx : x.1⁻¹ * g * x.1 = k * g * k⁻¹ := x.2.trans hk.symm
      calc x.1 * k * g = x.1 * (k * g * k⁻¹) * k := by group
        _ = x.1 * (x.1⁻¹ * g * x.1) * k := by rw [hx]
        _ = g * (x.1 * k) := by group
    · have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2
      rw [← hk]
      calc (c.1 * k⁻¹)⁻¹ * g * (c.1 * k⁻¹) = k * (c.1⁻¹ * (g * c.1)) * k⁻¹ := by group
        _ = k * g * k⁻¹ := by rw [← hc]; group
  · rw [ite_eq_right hgh, Nat.card_eq_zero]
    left
    exact ⟨fun x => hgh (isConj_iff.mpr ⟨x.1⁻¹, by rw [inv_inv]; exact x.2⟩)⟩

theorem inducedFunction_eq_sum_isConj' (H : Subgroup K) [Fintype H] (ρ : H → ℂ) (g : K)
    [∀ h : H, Decidable (IsConj g (h : K))] :
    inducedFunction H ρ g = (Nat.card (Subgroup.centralizer {g} : Subgroup K) : ℂ) /
      Nat.card H * ∑ h : H, if IsConj g (h : K) then ρ h else 0 := by
  classical
  rw [CFSG.Wreathed.CentralSL2.inducedFunction_eq_extendByZero]
  have hext : ∀ y : K, CFSG.Wreathed.CentralSL2.extendByZero H ρ y =
      ∑ h : H, if (h : K) = y then ρ h else 0 := by
    intro y
    by_cases hy : y ∈ H
    · rw [CFSG.Wreathed.CentralSL2.extendByZero_of_mem H ρ hy, Finset.sum_eq_single ⟨y, hy⟩]
      · rw [ite_eq_left rfl]
      · intro h _ hne
        rw [ite_eq_right]
        intro h'
        exact hne (Subtype.ext h')
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [CFSG.Wreathed.CentralSL2.extendByZero_of_not_mem H ρ hy]
      symm
      refine Finset.sum_eq_zero fun h _ => ?_
      rw [ite_eq_right]
      rintro rfl
      exact hy h.2
  simp_rw [hext]
  rw [Finset.sum_comm]
  have hfib : ∀ h : H, (∑ x : K, if (h : K) = x⁻¹ * g * x then ρ h else 0) =
      (if IsConj g (h : K) then (Nat.card (Subgroup.centralizer {g} : Subgroup K) : ℂ) else 0) *
        ρ h := by
    intro h
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter fun x : K => (h : K) = x⁻¹ * g * x).card =
        Nat.card {x : K // x⁻¹ * g * x = h} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext x
      simp [eq_comm]
    rw [hcard, card_conjugators']
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun h _ => hfib h, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs <;> ring

end ClassFormula

variable {F : Type} [Field F]

@[expose] noncomputable def unipHom (F : Type) [Field F] : Multiplicative F →* unipotent F where
  toFun t := ⟨mk (unip t.toAdd), ⟨unip t.toAdd, unip_mem_unipSL _, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    simp [unip_zero]
  map_mul' s t := by
    apply Subtype.ext
    simp [unip_add]

theorem unipHom_apply (t : F) :
    ((unipHom F (Multiplicative.ofAdd t) : unipotent F) : PSL(2, F)) = mk (unip t) := rfl

@[expose] noncomputable def unipEquiv (hF : ringChar F ≠ 2) : Multiplicative F ≃* unipotent F :=
  MulEquiv.ofBijective (unipHom F)
    ⟨fun s t h => by
      have h' := congrArg Subtype.val h
      exact (mk_unip_eq_mk_unip_iff (Ring.two_ne_zero hF) _ _).mp h',
    fun x => by
      obtain ⟨t, ht⟩ := (mem_unipotent_iff_exists (x : PSL(2, F))).mp x.2
      exact ⟨Multiplicative.ofAdd t, Subtype.ext ht.symm⟩⟩

theorem unipEquiv_apply (hF : ringChar F ≠ 2) (t : F) :
    ((unipEquiv hF (Multiplicative.ofAdd t) : unipotent F) : PSL(2, F)) = mk (unip t) := rfl

@[expose] noncomputable def unipChar (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) : unipotent F →* ℂ :=
  ψ.toMonoidHom.comp (unipEquiv hF).symm.toMonoidHom

theorem unipEquiv_coe (hF : ringChar F ≠ 2) (u : Multiplicative F) :
    ((unipEquiv hF u : unipotent F) : PSL(2, F)) = mk (unip u.toAdd) := rfl

theorem unipChar_unipEquiv (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (u : Multiplicative F) :
    unipChar hF ψ (unipEquiv hF u) = ψ u.toAdd := by
  simp [unipChar, AddChar.toMonoidHom_apply]

theorem unipChar_apply (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (t : F) :
    unipChar hF ψ (unipEquiv hF (Multiplicative.ofAdd t)) = ψ t := by
  simp [unipChar, AddChar.toMonoidHom_apply]

theorem sum_unipotent (hF : ringChar F ≠ 2) [Fintype F] [DecidableEq F] (f : PSL(2, F) → ℂ) :
    ∑ x : unipotent F, f x = ∑ t : F, f (mk (unip t)) := by
  rw [← Fintype.sum_equiv (unipEquiv hF).toEquiv (fun t => f (mk (unip t.toAdd)))
    (fun x => f x) (fun t => rfl)]
  exact Fintype.sum_equiv Multiplicative.toAdd _ _ (fun _ => rfl)

section IndP

variable [Fintype F] [DecidableEq F]

@[expose] noncomputable def indUnip (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) : PSL(2, F) → ℂ :=
  inducedFunction (unipotent F) (fun x => unipChar hF ψ x)

theorem indUnip_mem_blocksVChar (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) :
    indUnip hF ψ ∈ BlocksVChar PSL(2, F) :=
  inducedFunction_mem_blocksVChar _ (AddSubgroup.subset_closure
    (CFSG.Wreathed.CentralSL2.monoidHom_mem_blocksIrr (unipChar hF ψ)))

omit [Fintype F] in
theorem isConj_unip_iff' (hF : ringChar F ≠ 2) {t : F} (ht : t ≠ 0) (s : F) :
    IsConj (mk (unip t)) (mk (unip s)) ↔ s ≠ 0 ∧ IsSquare (s * t) := by
  have h2 := Ring.two_ne_zero hF
  by_cases hs : s = 0
  · subst hs
    rw [unip_zero, map_one, isConj_one_left, mk_unip_eq_one_iff h2]
    simp [ht]
  · rw [isConj_unip_iff h2 ht hs, mul_comm]
    simp [hs]

theorem indUnip_unip (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) {t : F} (ht : t ≠ 0) :
    indUnip hF ψ (mk (unip t)) =
      ∑ s : F, if s ≠ 0 ∧ IsSquare (s * t) then ψ s else 0 := by
  classical
  have h2 := Ring.two_ne_zero hF
  rw [indUnip, inducedFunction_eq_sum_isConj', centralizer_mk_unip h2 ht, div_self
    (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]
  rw [← Fintype.sum_equiv (unipEquiv hF).toEquiv
    (fun u => if IsConj (mk (unip t)) (mk (unip u.toAdd)) then ψ u.toAdd else 0)
    (fun h => if IsConj (mk (unip t)) (h : PSL(2, F)) then unipChar hF ψ h else 0)
    (fun u => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
      rw [unipEquiv_coe, unipChar_unipEquiv])]
  rw [← Fintype.sum_equiv Multiplicative.toAdd.symm
    (fun s => if IsConj (mk (unip t)) (mk (unip s)) then ψ s else 0) _ (fun _ => rfl)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [isConj_unip_iff' hF ht]

end IndP

section Gauss

variable [Fintype F] [DecidableEq F]

@[expose] noncomputable def quadChar (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

theorem quadChar_apply (a : F) : quadChar F a = (quadraticChar F a : ℂ) := rfl

theorem quadChar_sq_of_ne_zero {a : F} (ha : a ≠ 0) : quadChar F a ^ 2 = 1 := by
  rw [quadChar_apply]
  rcases quadraticChar_dichotomy ha with h | h <;> simp [h]

theorem quadChar_isQuadratic : (quadChar F).IsQuadratic :=
  (quadraticChar_isQuadratic F).comp _

theorem quadChar_ne_one (hF : ringChar F ≠ 2) : quadChar F ≠ 1 := by
  intro h
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF
  have h1 := congrArg (fun χ : MulChar F ℂ => χ ν) h
  simp only [quadChar_apply, MulChar.one_apply (isUnit_iff_ne_zero.mpr
    (ne_zero_of_not_isSquare hν)), quadraticChar_neg_one_iff_not_isSquare.mpr hν] at h1
  norm_num at h1

@[expose] noncomputable def quadGauss (ψ : AddChar F ℂ) : ℂ := gaussSum (quadChar F) ψ

theorem sum_addChar_ne_zero' {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∑ t : F, (if t = 0 then 0 else ψ t) = -1 := by
  have h := AddChar.sum_eq_zero_of_ne_one hψ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), AddChar.map_zero_eq_one] at h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), ite_eq_left rfl, zero_add]
  rw [Finset.sum_congr rfl fun t ht => ite_eq_right (Finset.ne_of_mem_erase ht)]
  linear_combination h

theorem isSquare_indicator {s t : F} (hs : s ≠ 0) (ht : t ≠ 0) (z : ℂ) :
    (if IsSquare (s * t) then z else 0) = (1 + quadChar F s * quadChar F t) / 2 * z := by
  rw [← map_mul, quadChar_apply]
  by_cases h : IsSquare (s * t)
  · rw [ite_eq_left h, (quadraticChar_one_iff_isSquare (mul_ne_zero hs ht)).mpr h]
    push_cast
    ring
  · rw [ite_eq_right h, quadraticChar_neg_one_iff_not_isSquare.mpr h]
    push_cast
    ring

theorem sum_isSquare_addChar (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) {t : F} (ht : t ≠ 0) :
    (∑ s : F, if s ≠ 0 ∧ IsSquare (s * t) then ψ s else 0) =
      (quadChar F t * quadGauss ψ - 1) / 2 := by
  have hpt : ∀ s : F, (if s ≠ 0 ∧ IsSquare (s * t) then ψ s else 0) =
      (if s = 0 then 0 else ψ s) / 2 + quadChar F t * (quadChar F s * ψ s) / 2 := by
    intro s
    by_cases hs : s = 0
    · subst hs
      simp [MulChar.map_zero]
    · rw [ite_eq_right hs]
      simp only [ne_eq, hs, not_false_eq_true, true_and]
      rw [isSquare_indicator hs ht]
      ring
  rw [Finset.sum_congr rfl (fun s _ => hpt s), Finset.sum_add_distrib, ← Finset.sum_div,
    ← Finset.sum_div, ← Finset.mul_sum, sum_addChar_ne_zero' hψ]
  rw [quadGauss, gaussSum]
  ring

end Gauss

section GaussProps

variable [Fintype F] [DecidableEq F]

theorem quadChar_real (a : F) : starRingEnd ℂ (quadChar F a) = quadChar F a := by
  rw [quadChar_apply, map_intCast]

theorem conj_quadGauss (ψ : AddChar F ℂ) :
    starRingEnd ℂ (quadGauss ψ) = quadChar F (-1) * quadGauss ψ := by
  have hsq : quadChar F (-1) * quadChar F (-1) = 1 := by
    rw [← sq, quadChar_sq_of_ne_zero (neg_ne_zero.mpr one_ne_zero)]
  simp only [quadGauss, gaussSum, map_sum, map_mul, quadChar_real, ← AddChar.map_neg_eq_conj,
    Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.neg F) _ _ (fun s => ?_)
  have hχ : quadChar F (-s) = quadChar F (-1) * quadChar F s := by
    rw [← map_mul, neg_one_mul]
  simp only [Equiv.neg_apply]
  rw [hχ]
  linear_combination (-(quadChar F s * ψ (-s))) * hsq

theorem sum_quadChar (hF : ringChar F ≠ 2) : ∑ t : F, quadChar F t = 0 := by
  simp only [quadChar_apply]
  rw [← Int.cast_sum, quadraticChar_sum_zero hF, Int.cast_zero]

theorem quadGauss_sq (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    quadGauss ψ ^ 2 = quadChar F (-1) * Fintype.card F :=
  gaussSum_sq (quadChar_ne_one hF) quadChar_isQuadratic hψ

theorem quadGauss_mul_conj (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    quadGauss ψ * starRingEnd ℂ (quadGauss ψ) = Fintype.card F := by
  rw [conj_quadGauss, mul_left_comm, ← sq, quadGauss_sq hF hψ, ← mul_assoc,
    ← sq, quadChar_sq_of_ne_zero (neg_ne_zero.mpr one_ne_zero), one_mul]

theorem quadChar_of_not_isSquare {ν : F} (hν : ¬ IsSquare ν) : quadChar F ν = -1 := by
  rw [quadChar_apply, quadraticChar_neg_one_iff_not_isSquare.mpr hν]
  norm_num

theorem quadGauss_mulShift {ν : F} (hν : ¬ IsSquare ν) (ψ : AddChar F ℂ) :
    quadGauss (ψ.mulShift ν) = -quadGauss ψ := by
  have hν0 := ne_zero_of_not_isSquare hν
  have h := gaussSum_mulShift (quadChar F) ψ (Units.mk0 ν hν0)
  rw [Units.val_mk0, quadChar_of_not_isSquare hν] at h
  rw [quadGauss, quadGauss, ← h]
  ring

theorem quadChar_neg_one_eq :
    quadChar F (-1) = if IsSquare (-1 : F) then 1 else -1 := by
  split_ifs with h
  · rw [quadChar_apply, (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr h]
    norm_num
  · exact quadChar_of_not_isSquare h

end GaussProps

section Delta

variable [Fintype F] [DecidableEq F]

@[expose] noncomputable def ggDiff (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (ν : F) :
    PSL(2, F) → ℂ :=
  indUnip hF ψ - indUnip hF (ψ.mulShift ν)

theorem ggDiff_mem_blocksVChar (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (ν : F) :
    ggDiff hF ψ ν ∈ BlocksVChar PSL(2, F) :=
  AddSubgroup.sub_mem _ (indUnip_mem_blocksVChar hF ψ) (indUnip_mem_blocksVChar hF _)

theorem ggDiff_one (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (ν : F) : ggDiff hF ψ ν 1 = 0 := by
  rw [ggDiff, Pi.sub_apply, indUnip, indUnip, inducedFunction_apply_one,
    inducedFunction_apply_one, map_one, map_one, sub_self]

theorem ggDiff_unip (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {ν : F}
    (hν : ¬ IsSquare ν) {t : F} (ht : t ≠ 0) :
    ggDiff hF ψ ν (mk (unip t)) = quadChar F t * quadGauss ψ := by
  have hν0 := ne_zero_of_not_isSquare hν
  have hψ1 : ψ ≠ 1 := by
    have := hψ (one_ne_zero (α := F))
    rwa [AddChar.mulShift_one] at this
  have hψν : ψ.mulShift ν ≠ 1 := hψ hν0
  rw [ggDiff, Pi.sub_apply, indUnip_unip hF ψ ht, indUnip_unip hF _ ht,
    sum_isSquare_addChar ψ hψ1 ht, sum_isSquare_addChar _ hψν ht, quadGauss_mulShift hν]
  ring

theorem ggDiff_of_not_conj (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (ν : F) {y : PSL(2, F)}
    (hy : ∀ g : PSL(2, F), g⁻¹ * y * g ∉ unipotent F) : ggDiff hF ψ ν y = 0 := by
  rw [ggDiff, Pi.sub_apply, indUnip, indUnip, inducedFunction_apply_eq_zero _ hy,
    inducedFunction_apply_eq_zero _ hy, sub_zero]

theorem ggDiff_of_mem_splitTorus (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (ν : F)
    {x : PSL(2, F)} (hx : x ∈ splitTorus F) (hx1 : x ≠ 1) : ggDiff hF ψ ν x = 0 :=
  ggDiff_of_not_conj hF ψ ν (not_conj_mem_of_mem_conjSet
    (Nat.Coprime.symm (coprime_card_unipotent_splitTorus hF)) (mem_conjSet_of_mem hx hx1))

theorem ggDiff_of_mem_nonsplitTorus (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) {ν : F}
    (hν : ¬ IsSquare ν) {x : PSL(2, F)} (hx : x ∈ nonsplitTorus ν) (hx1 : x ≠ 1) :
    ggDiff hF ψ ν x = 0 :=
  ggDiff_of_not_conj hF ψ ν (not_conj_mem_of_mem_conjSet
    (Nat.Coprime.symm (coprime_card_unipotent_nonsplitTorus hF hν)) (mem_conjSet_of_mem hx hx1))

theorem ggDiff_inner_of_const (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {ν : F} (hν : ¬ IsSquare ν) {f : PSL(2, F) → ℂ}
    (hf : BlocksIsClassFunction f) (c : ℂ) (hfP : ∀ x ∈ unipotent F, x ≠ 1 → f x = c) :
    BlocksInnerProduct (ggDiff hF ψ ν) f = 0 := by
  have hΔ := blocksVChar_isClassFunction (ggDiff_mem_blocksVChar hF ψ ν)
  have hclass : ∀ g' x : PSL(2, F), ggDiff hF ψ ν (g' * x * g'⁻¹) *
      starRingEnd ℂ (f (g' * x * g'⁻¹)) = ggDiff hF ψ ν x * starRingEnd ℂ (f x) := by
    intro g' x
    rw [hΔ x g', hf x g']
  have h := sum_classFunction hF hq hν (fun x => ggDiff hF ψ ν x * starRingEnd ℂ (f x)) hclass
  have hT : ∑ x : splitTorus F, ggDiff hF ψ ν x * starRingEnd ℂ (f x) -
      ggDiff hF ψ ν 1 * starRingEnd ℂ (f 1) = 0 := by
    rw [sum_subgroup_of_const (H := splitTorus F)
      (h := fun x => ggDiff hF ψ ν x * starRingEnd ℂ (f x)) (c := 0) (fun x hx => by
      rw [ggDiff_of_mem_splitTorus hF ψ ν x.2 (fun h => hx (Subtype.ext h)), zero_mul]),
      mul_zero]
  have hS : ∑ x : nonsplitTorus ν, ggDiff hF ψ ν x * starRingEnd ℂ (f x) -
      ggDiff hF ψ ν 1 * starRingEnd ℂ (f 1) = 0 := by
    rw [sum_subgroup_of_const (H := nonsplitTorus ν)
      (h := fun x => ggDiff hF ψ ν x * starRingEnd ℂ (f x)) (c := 0) (fun x hx => by
      rw [ggDiff_of_mem_nonsplitTorus hF ψ hν x.2 (fun h => hx (Subtype.ext h)), zero_mul]),
      mul_zero]
  have hP : ∑ x : unipotent F, ggDiff hF ψ ν x * starRingEnd ℂ (f x) -
      ggDiff hF ψ ν 1 * starRingEnd ℂ (f 1) = 0 := by
    rw [sum_unipotent hF (fun x => ggDiff hF ψ ν x * starRingEnd ℂ (f x)), ggDiff_one, zero_mul,
      sub_zero]
    have hpt : ∀ t : F, ggDiff hF ψ ν (mk (unip t)) * starRingEnd ℂ (f (mk (unip t))) =
        (quadChar F t * (quadGauss ψ * starRingEnd ℂ c)) := by
      intro t
      by_cases ht : t = 0
      · subst ht
        rw [unip_zero, map_one, ggDiff_one, zero_mul, MulChar.map_zero, zero_mul]
      · rw [ggDiff_unip hF hψ hν ht, hfP _ ⟨unip t, unip_mem_unipSL t, rfl⟩
          (fun h => ht ((mk_unip_eq_one_iff (Ring.two_ne_zero hF) t).mp h))]
        ring
    rw [Finset.sum_congr rfl (fun t _ => hpt t), ← Finset.sum_mul, sum_quadChar hF, zero_mul]
  unfold BlocksInnerProduct
  rw [h, hP, hT, hS, ggDiff_one, zero_mul]
  ring

theorem ggDiff_inner_self (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {ν : F} (hν : ¬ IsSquare ν) :
    BlocksInnerProduct (ggDiff hF ψ ν) (ggDiff hF ψ ν) = 2 := by
  have hΔ := blocksVChar_isClassFunction (ggDiff_mem_blocksVChar hF ψ ν)
  have hclass : ∀ g' x : PSL(2, F), ggDiff hF ψ ν (g' * x * g'⁻¹) *
      starRingEnd ℂ (ggDiff hF ψ ν (g' * x * g'⁻¹)) =
        ggDiff hF ψ ν x * starRingEnd ℂ (ggDiff hF ψ ν x) := by
    intro g' x
    rw [hΔ x g']
  have h := sum_classFunction hF hq hν
    (fun x => ggDiff hF ψ ν x * starRingEnd ℂ (ggDiff hF ψ ν x)) hclass
  have hT : ∑ x : splitTorus F, ggDiff hF ψ ν x * starRingEnd ℂ (ggDiff hF ψ ν x) -
      ggDiff hF ψ ν 1 * starRingEnd ℂ (ggDiff hF ψ ν 1) = 0 := by
    rw [sum_subgroup_of_const (H := splitTorus F)
      (h := fun x => ggDiff hF ψ ν x * starRingEnd ℂ (ggDiff hF ψ ν x)) (c := 0) (fun x hx => by
      rw [ggDiff_of_mem_splitTorus hF ψ ν x.2 (fun h => hx (Subtype.ext h)), zero_mul]),
      mul_zero]
  have hS : ∑ x : nonsplitTorus ν, ggDiff hF ψ ν x * starRingEnd ℂ (ggDiff hF ψ ν x) -
      ggDiff hF ψ ν 1 * starRingEnd ℂ (ggDiff hF ψ ν 1) = 0 := by
    rw [sum_subgroup_of_const (H := nonsplitTorus ν)
      (h := fun x => ggDiff hF ψ ν x * starRingEnd ℂ (ggDiff hF ψ ν x)) (c := 0) (fun x hx => by
      rw [ggDiff_of_mem_nonsplitTorus hF ψ hν x.2 (fun h => hx (Subtype.ext h)), zero_mul]),
      mul_zero]
  have hP : ∑ x : unipotent F, ggDiff hF ψ ν x * starRingEnd ℂ (ggDiff hF ψ ν x) -
      ggDiff hF ψ ν 1 * starRingEnd ℂ (ggDiff hF ψ ν 1) =
        ((Fintype.card F : ℂ) - 1) * Fintype.card F := by
    rw [sum_unipotent hF (fun x => ggDiff hF ψ ν x * starRingEnd ℂ (ggDiff hF ψ ν x)),
      ggDiff_one, zero_mul, sub_zero]
    have hpt : ∀ t : F, ggDiff hF ψ ν (mk (unip t)) * starRingEnd ℂ (ggDiff hF ψ ν (mk (unip t))) =
        if t = 0 then 0 else (Fintype.card F : ℂ) := by
      intro t
      by_cases ht : t = 0
      · subst ht
        rw [unip_zero, map_one, ggDiff_one, zero_mul, ite_eq_left rfl]
      · rw [ite_eq_right ht, ggDiff_unip hF hψ hν ht, map_mul, quadChar_real,
          ← quadGauss_mul_conj hF hψ]
        have h1 := quadChar_sq_of_ne_zero (F := F) ht
        linear_combination (quadGauss ψ * starRingEnd ℂ (quadGauss ψ)) * h1
    rw [Finset.sum_congr rfl (fun t _ => hpt t), Finset.sum_ite, Finset.sum_const_zero, zero_add,
      Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter fun t : F => ¬ t = 0).card = Fintype.card F - 1 := by
      rw [Finset.filter_ne' Finset.univ (0 : F), Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ]
    rw [hcard, Nat.cast_sub Fintype.card_pos]
    push_cast
    ring
  have hG := card_PSL_complex hF (F := F)
  have hG0 : (Nat.card PSL(2, F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold BlocksInnerProduct
  rw [h, hP, hT, hS, ggDiff_one, zero_mul, inv_mul_eq_iff_eq_mul₀ hG0, hG]
  ring

end Delta

end CFSG.PSL2Table
