module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Module QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] def axisRadicalGens (a b : V) : Set (V ≃ₗ[K] V) :=
  {g | ∃ u w, u ∈ Submodule.span K {a, b} ∧ polar Q a w = 0 ∧ polar Q b w = 0 ∧ eichler Q u w = g}

variable (Q) in
@[expose] def axisRadical (a b : V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure (axisRadicalGens Q a b)

variable (Q) in
@[expose] def axisParabolic (P R : HypPair Q) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure (axisRadicalGens Q P.e R.e ∪ {eichler Q P.e R.f, eichler Q P.f R.e})

theorem axisRadical_le_axisParabolic (P R : HypPair Q) :
    axisRadical Q P.e R.e ≤ axisParabolic Q P R :=
  Subgroup.closure_mono Set.subset_union_left

theorem axisParabolic_le_elementaryGroup (P R : HypPair Q) :
    axisParabolic Q P R ≤ elementaryGroup Q := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ (⟨u, w, -, -, -, rfl⟩ | h)
  · exact eichler_mem_elementaryGroup Q u w
  · rcases h with rfl | rfl <;> exact eichler_mem_elementaryGroup Q _ _

theorem axisParabolic_le_centralizer {P R : HypPair Q} (h : P.Orth R) :
    axisParabolic Q P R ≤ Subgroup.centralizer {eichler Q P.e R.e} := by
  have key : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      eichler Q (g P.e) (g R.e) = eichler Q P.e R.e →
        g ∈ Subgroup.centralizer {eichler Q P.e R.e} := by
    intro g hg hgt
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := eichler_conj hg P.e R.e
    rw [hgt] at hc
    exact mul_inv_eq_iff_eq_mul.mp hc
  have hab : eichler Q (P.e + R.e) R.e = eichler Q P.e R.e := by
    have hQ' : Q (P.e + R.e) = 0 := by
      rw [QuadraticMap.map_add Q, P.Q_e, R.Q_e, h.ee]
      simp
    have hp : polar Q (P.e + R.e) R.e = 0 := by
      rw [polar_add_left, h.ee, R.polar_ee, add_zero]
    refine LinearEquiv.ext fun x => ?_
    rw [eichler_apply hQ' hp, eichler_apply P.Q_e h.ee, polar_add_right, R.Q_e]
    module
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ (⟨u, w, hu, ha, hb, rfl⟩ | hg)
  · refine key _ (eichler_mem_orthogonalGroup Q u w) ?_
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
    have hau : polar Q P.e (α • P.e + β • R.e) = 0 := by
      rw [polar_add_right, polar_smul_right, polar_smul_right, P.polar_ee, h.ee]
      simp
    have hbu : polar Q R.e (α • P.e + β • R.e) = 0 := by
      rw [polar_add_right, polar_smul_right, polar_smul_right, polar_comm Q R.e P.e, h.ee,
        R.polar_ee]
      simp
    rw [eichler_apply_of_polar_eq_zero hau ha, eichler_apply_of_polar_eq_zero hbu hb]
  · rcases hg with rfl | rfl
    · refine key _ (eichler_mem_orthogonalGroup Q _ _) ?_
      have h1 : eichler Q P.e R.f R.e = R.e + (-1 : K) • P.e := by
        rw [eichler_apply P.Q_e h.ef, polar_comm Q R.e P.e, h.ee, R.polar_ef, R.Q_f]
        module
      rw [eichler_apply_self, h1, eichler_add_smul_self P.Q_e]
    · refine key _ (eichler_mem_orthogonalGroup Q _ _) ?_
      have h1 : eichler Q P.f R.e P.e = P.e + R.e := by
        rw [eichler_apply P.Q_f h.fe, P.polar_ef, h.ee, R.Q_e]
        module
      have h2 : eichler Q P.f R.e R.e = R.e := by
        rw [eichler_apply P.Q_f h.fe, polar_comm Q R.e P.f, h.fe, R.polar_ee]
        module
      rw [h1, h2, hab]

private theorem eichler_mul_self_charTwo [CharP K 2] (u w : V) :
    eichler Q u w * eichler Q u w = 1 := by
  by_cases hw : polar Q u w = 0
  · rw [eichler_mul hw hw, ← two_smul K w, CharTwo.two_eq_zero, zero_smul, eichler_zero_right]
  · rw [eichler_of_polar_ne_zero hw, one_mul]

theorem closure_involutions_axisParabolic [CharP K 2] (P R : HypPair Q) :
    Subgroup.closure {g | g ∈ axisParabolic Q P R ∧ orderOf g = 2} = axisParabolic Q P R := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun g hg => hg.1) ((Subgroup.closure_le _).mpr ?_)
  have key : ∀ u w, eichler Q u w ∈ axisParabolic Q P R →
      eichler Q u w ∈ Subgroup.closure {g | g ∈ axisParabolic Q P R ∧ orderOf g = 2} := by
    intro u w hmem
    by_cases h1 : eichler Q u w = 1
    · rw [h1]
      exact one_mem _
    · refine Subgroup.subset_closure ⟨hmem, orderOf_eq_prime ?_ h1⟩
      rw [pow_two]
      exact eichler_mul_self_charTwo u w
  rintro _ (⟨u, w, hu, ha, hb, rfl⟩ | h)
  · exact key u w (Subgroup.subset_closure (Or.inl ⟨u, w, hu, ha, hb, rfl⟩))
  · rcases h with rfl | rfl
    · exact key _ _ (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
    · exact key _ _ (Subgroup.subset_closure (Or.inr (Or.inr rfl)))

private theorem polar_span_axis_eq_zero {a b w x : V} (hx : x ∈ Submodule.span K {a, b})
    (ha : polar Q a w = 0) (hb : polar Q b w = 0) : polar Q x w = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [polar_add_left, polar_smul_left, polar_smul_left, ha, hb]
  simp

private theorem axis_polar_eq_zero {P R : HypPair Q} (h : P.Orth R) {x : V}
    (hx : x ∈ Submodule.span K {P.e, R.e}) : polar Q P.e x = 0 ∧ polar Q R.e x = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  refine ⟨?_, ?_⟩
  · rw [polar_add_right, polar_smul_right, polar_smul_right, P.polar_ee, h.ee]
    simp
  · rw [polar_add_right, polar_smul_right, polar_smul_right, polar_comm Q R.e P.e, h.ee,
      R.polar_ee]
    simp

private theorem axis_map_eq_zero {P R : HypPair Q} (h : P.Orth R) {x : V}
    (hx : x ∈ Submodule.span K {P.e, R.e}) : Q x = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, P.Q_e, R.Q_e,
    polar_smul_left, polar_smul_right, h.ee]
  simp

private theorem conj_mem_axisRadical_of_preserves {a b : V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hS : ∀ x ∈ Submodule.span K {a, b}, g x ∈ Submodule.span K {a, b})
    (hS' : ∀ x ∈ Submodule.span K {a, b}, g⁻¹ x ∈ Submodule.span K {a, b})
    {r : V ≃ₗ[K] V} (hr : r ∈ axisRadical Q a b) : g * r * g⁻¹ ∈ axisRadical Q a b := by
  have hle : axisRadical Q a b ≤ (axisRadical Q a b).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨u, w, hu, hau, hbu, rfl⟩
    have key : ∀ y ∈ Submodule.span K {a, b}, polar Q y (g w) = 0 := fun y hy => by
      rw [← LinearEquiv.apply_inv_apply' g y, polar_map_of_mem hg]
      exact polar_span_axis_eq_zero (hS' y hy) hau hbu
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      eichler_conj hg]
    exact Subgroup.subset_closure ⟨g u, g w, hS u hu, key a (Submodule.subset_span (by simp)),
      key b (Submodule.subset_span (by simp)), rfl⟩
  exact hle hr

private theorem mem_normalizer_axisRadical_of_preserves {a b : V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hS : ∀ x ∈ Submodule.span K {a, b}, g x ∈ Submodule.span K {a, b})
    (hS' : ∀ x ∈ Submodule.span K {a, b}, g⁻¹ x ∈ Submodule.span K {a, b}) :
    g ∈ Subgroup.normalizer (axisRadical Q a b : Set (V ≃ₗ[K] V)) := by
  refine Subgroup.mem_normalizer_iff.mpr fun r =>
    ⟨conj_mem_axisRadical_of_preserves hg hS hS', fun hr => ?_⟩
  have h2 := conj_mem_axisRadical_of_preserves (inv_mem hg) hS'
    (fun x hx => by rw [inv_inv]; exact hS x hx) hr
  simpa [mul_assoc] using h2

private theorem eichler_inv_eq_eichler_neg (u w : V) : (eichler Q u w)⁻¹ = eichler Q u (-w) := by
  by_cases hw : polar Q u w = 0
  · exact eichler_inv hw
  · have hw' : polar Q u (-w) ≠ 0 := by rwa [polar_neg_right, neg_ne_zero]
    rw [eichler_of_polar_ne_zero hw, eichler_of_polar_ne_zero hw', inv_one]

private theorem eichler_apply_mem_axis {P R : HypPair Q} (h : P.Orth R) {u w x : V}
    (huw : u ∈ Submodule.span K {P.e, R.e} ∨ w ∈ Submodule.span K {P.e, R.e})
    (hx : x ∈ Submodule.span K {P.e, R.e}) : eichler Q u w x ∈ Submodule.span K {P.e, R.e} := by
  by_cases hE : Q u = 0 ∧ polar Q u w = 0
  · rw [eichler_apply hE.1 hE.2]
    rcases huw with hu | hw
    · have hxu : polar Q x u = 0 :=
        polar_span_axis_eq_zero hx (axis_polar_eq_zero h hu).1 (axis_polar_eq_zero h hu).2
      simp only [hxu, zero_smul, add_zero, mul_zero]
      exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hu)
    · have hxw : polar Q x w = 0 :=
        polar_span_axis_eq_zero hx (axis_polar_eq_zero h hw).1 (axis_polar_eq_zero h hw).2
      simp only [hxw, axis_map_eq_zero h hw, zero_mul, add_zero, zero_smul, sub_zero]
      exact Submodule.add_mem _ hx (Submodule.smul_mem _ _ hw)
  · rw [eichler_of_not hE]
    exact hx

private theorem eichler_mem_normalizer_axisRadical {P R : HypPair Q} (h : P.Orth R) {u w : V}
    (huw : u ∈ Submodule.span K {P.e, R.e} ∨ w ∈ Submodule.span K {P.e, R.e}) :
    eichler Q u w ∈ Subgroup.normalizer (axisRadical Q P.e R.e : Set (V ≃ₗ[K] V)) := by
  refine mem_normalizer_axisRadical_of_preserves (eichler_mem_orthogonalGroup Q u w)
    (fun x hx => eichler_apply_mem_axis h huw hx) (fun x hx => ?_)
  rw [eichler_inv_eq_eichler_neg]
  exact eichler_apply_mem_axis h (huw.imp id (Submodule.neg_mem _)) hx

theorem conj_mem_axisRadical {P R : HypPair Q} (h : P.Orth R) {p r : V ≃ₗ[K] V}
    (hp : p ∈ axisParabolic Q P R) (hr : r ∈ axisRadical Q P.e R.e) :
    p * r * p⁻¹ ∈ axisRadical Q P.e R.e := by
  have hle : axisParabolic Q P R ≤
      Subgroup.normalizer (axisRadical Q P.e R.e : Set (V ≃ₗ[K] V)) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ (⟨u, w, hu, -, -, rfl⟩ | hg)
    · exact eichler_mem_normalizer_axisRadical h (Or.inl hu)
    · rcases hg with rfl | rfl
      · exact eichler_mem_normalizer_axisRadical h (Or.inl (Submodule.subset_span (by simp)))
      · exact eichler_mem_normalizer_axisRadical h (Or.inr (Submodule.subset_span (by simp)))
  exact (Subgroup.mem_normalizer_iff.mp (hle hp) r).mp hr

variable (Q) in
private def IsAxisFlag (a b : V) (g : V ≃ₗ[K] V) : Prop :=
  (∀ x ∈ Submodule.span K {a, b}, g x = x) ∧
    (∀ x, polar Q a x = 0 → polar Q b x = 0 → g x - x ∈ Submodule.span K {a, b}) ∧
    ∀ x, polar Q a (g x - x) = 0 ∧ polar Q b (g x - x) = 0

private theorem isAxisFlag_one (a b : V) : IsAxisFlag Q a b 1 := by
  have h1 : ∀ x : V, (1 : V ≃ₗ[K] V) x - x = 0 := fun x => sub_eq_zero.mpr rfl
  refine ⟨fun _ _ => rfl, fun x _ _ => ?_, fun x => ?_⟩
  · rw [h1]
    exact Submodule.zero_mem _
  · rw [h1, polar_zero_right, polar_zero_right]
    exact ⟨rfl, rfl⟩

private theorem isAxisFlag_mul {a b : V} {g g' : V ≃ₗ[K] V} (hg : IsAxisFlag Q a b g)
    (hg' : IsAxisFlag Q a b g') : IsAxisFlag Q a b (g * g') := by
  obtain ⟨h1, h2, h3⟩ := hg
  obtain ⟨h1', h2', h3'⟩ := hg'
  have hsplit : ∀ x, (g * g') x - x = (g (g' x) - g' x) + (g' x - x) := fun x => by
    rw [LinearEquiv.mul_apply]
    abel
  refine ⟨fun x hx => by rw [LinearEquiv.mul_apply, h1' x hx, h1 x hx], fun x ha hb => ?_,
    fun x => ?_⟩
  · have ha' := (h3' x).1
    have hb' := (h3' x).2
    rw [polar_sub_right, ha, sub_zero] at ha'
    rw [polar_sub_right, hb, sub_zero] at hb'
    rw [hsplit]
    exact Submodule.add_mem _ (h2 _ ha' hb') (h2' x ha hb)
  · rw [hsplit, polar_add_right, polar_add_right, (h3 _).1, (h3' _).1, (h3 _).2, (h3' _).2,
      add_zero]
    exact ⟨rfl, rfl⟩

private theorem isAxisFlag_inv {a b : V} {g : V ≃ₗ[K] V} (hg : IsAxisFlag Q a b g) :
    IsAxisFlag Q a b g⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hd : ∀ x, g⁻¹ x - x = -(g (g⁻¹ x) - g⁻¹ x) := fun x => by
    rw [LinearEquiv.apply_inv_apply']
    abel
  refine ⟨fun x hx => ?_, fun x ha hb => ?_, fun x => ?_⟩
  · have := LinearEquiv.inv_apply_apply' g x
    rwa [h1 x hx] at this
  · have hy := h3 (g⁻¹ x)
    rw [LinearEquiv.apply_inv_apply', polar_sub_right, polar_sub_right, ha, hb, zero_sub,
      zero_sub, neg_eq_zero, neg_eq_zero] at hy
    have hm := h2 (g⁻¹ x) hy.1 hy.2
    rw [LinearEquiv.apply_inv_apply'] at hm
    rw [hd, LinearEquiv.apply_inv_apply']
    exact Submodule.neg_mem _ hm
  · rw [hd, polar_neg_right, polar_neg_right, (h3 _).1, (h3 _).2, neg_zero]
    exact ⟨rfl, rfl⟩

private theorem isAxisFlag_eichler {P R : HypPair Q} (h : P.Orth R) {u w : V}
    (hu : u ∈ Submodule.span K {P.e, R.e}) (ha : polar Q P.e w = 0) (hb : polar Q R.e w = 0) :
    IsAxisFlag Q P.e R.e (eichler Q u w) := by
  obtain ⟨hau, hbu⟩ := axis_polar_eq_zero h hu
  by_cases hE : Q u = 0 ∧ polar Q u w = 0
  · have hd : ∀ x, eichler Q u w x - x =
        polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u := fun x => by
      rw [eichler_apply hE.1 hE.2]
      abel
    refine ⟨fun x hx => ?_, fun x hax hbx => ?_, fun x => ?_⟩
    · exact eichler_apply_of_polar_eq_zero (polar_span_axis_eq_zero hx hau hbu)
        (polar_span_axis_eq_zero hx ha hb)
    · have hxu : polar Q x u = 0 := by
        rw [polar_comm]
        exact polar_span_axis_eq_zero hu hax hbx
      rw [hd, hxu]
      simp only [zero_smul, mul_zero, add_zero, zero_sub]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hu)
    · simp only [hd, polar_sub_right, polar_smul_right, ha, hb, hau, hbu, smul_zero, sub_self,
        and_self]
  · rw [eichler_of_not hE]
    exact isAxisFlag_one _ _

private theorem pow_four_of_isAxisFlag [CharP K 2] {a b : V} {g : V ≃ₗ[K] V}
    (hg : IsAxisFlag Q a b g) : g ^ 4 = 1 := by
  obtain ⟨h1, h2, h3⟩ := hg
  have h2v : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]
  have hsq : ∀ v, g (g v) - v ∈ Submodule.span K {a, b} := fun v => by
    have e : g (g v) - v = g (g v - v) - (g v - v) + ((g v - v) + (g v - v)) := by
      rw [map_sub]
      abel
    rw [e, h2v, add_zero]
    exact h2 _ (h3 v).1 (h3 v).2
  have hfix : ∀ x ∈ Submodule.span K {a, b}, g (g x) = x := fun x hx => by
    rw [h1 x hx, h1 x hx]
  refine LinearEquiv.ext fun v => ?_
  show (g ^ 4) v = v
  obtain ⟨y, hy, hym⟩ : ∃ y, g (g v) = v + y ∧ y ∈ Submodule.span K {a, b} :=
    ⟨g (g v) - v, by abel, hsq v⟩
  rw [pow_succ, pow_succ, pow_succ, pow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, hy, map_add, map_add, hfix y hym, hy, add_assoc, h2v, add_zero]

private theorem isAxisFlag_of_mem_axisRadical {P R : HypPair Q} (h : P.Orth R) {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.closure (axisRadicalGens Q P.e R.e)) : IsAxisFlag Q P.e R.e g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, w, hu, ha, hb, rfl⟩ := hx
    exact isAxisFlag_eichler h hu ha hb
  | one => exact isAxisFlag_one _ _
  | mul x y _ _ hx hy => exact isAxisFlag_mul hx hy
  | inv x _ hx => exact isAxisFlag_inv hx

theorem isPGroup_axisRadical [CharP K 2] {P R : HypPair Q} (h : P.Orth R) :
    IsPGroup 2 (axisRadical Q P.e R.e) := by
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  exact pow_four_of_isAxisFlag (isAxisFlag_of_mem_axisRadical h g.2)

private theorem axisRadical_le_commutator_exists_ne_zero [FiniteDimensional K V]
    {P R : HypPair Q} (hV : 6 ≤ finrank K V) :
    ∃ w : V, w ≠ 0 ∧ polar Q w P.e = 0 ∧ polar Q w P.f = 0 ∧
      polar Q w R.e = 0 ∧ polar Q w R.f = 0 := by
  let L : V →ₗ[K] (Fin 4 → K) := LinearMap.pi
    ![(LinearMap.flip (polarBilin Q)) P.e, (LinearMap.flip (polarBilin Q)) P.f,
      (LinearMap.flip (polarBilin Q)) R.e, (LinearMap.flip (polarBilin Q)) R.f]
  let W' : Submodule K V := LinearMap.ker L
  have hmem : ∀ x, x ∈ W' ↔ polar Q x P.e = 0 ∧ polar Q x P.f = 0 ∧
      polar Q x R.e = 0 ∧ polar Q x R.f = 0 := by
    intro x
    simp only [W', LinearMap.mem_ker, funext_iff, Pi.zero_apply]
    constructor
    · intro h
      exact ⟨h 0, h 1, h 2, h 3⟩
    · rintro ⟨h0, h1, h2, h3⟩ i
      fin_cases i <;> assumption
  have hfin : 2 ≤ finrank K W' := by
    change 2 ≤ finrank K (LinearMap.ker L)
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    have h2 : finrank K (LinearMap.range L) ≤ 4 := by
      have h3 : finrank K (Fin 4 → K) = 4 := by
        simp
      calc finrank K (LinearMap.range L) ≤ finrank K (Fin 4 → K) := Submodule.finrank_le _
        _ = 4 := h3
    omega
  have hne : W' ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hfin
    omega
  obtain ⟨w, hw0⟩ : ∃ w : W', w ≠ 0 := by
    by_contra h
    refine hne ((Submodule.eq_bot_iff W').mpr fun x hx => ?_)
    have hx0 : (⟨x, hx⟩ : W') = 0 := by
      by_contra hx1
      exact h ⟨⟨x, hx⟩, hx1⟩
    exact congrArg Subtype.val hx0
  obtain ⟨h0, h1, h2, h3⟩ := (hmem w).mp w.2
  exact ⟨w, fun h => hw0 (Subtype.ext h), h0, h1, h2, h3⟩

private theorem axisRadical_le_commutator_proj_mem {P R : HypPair Q} (h : P.Orth R)
    {v v' w : V}
    (hv' : v' = v - polar Q v P.f • P.e - polar Q v P.e • P.f -
      polar Q v R.f • R.e - polar Q v R.e • R.f)
    (hwe : polar Q w P.e = 0) (hwf : polar Q w P.f = 0)
    (hwb : polar Q w R.e = 0) (hwfR : polar Q w R.f = 0) :
    polar Q v' P.e = 0 ∧ polar Q v' P.f = 0 ∧ polar Q v' R.e = 0 ∧ polar Q v' R.f = 0 ∧
      polar Q v' w = polar Q v w := by
  subst hv'
  have hbe : polar Q R.e P.e = 0 := by rw [polar_comm, h.ee]
  have hbf : polar Q R.f P.e = 0 := by rw [polar_comm, h.ef]
  have hfb : polar Q R.e P.f = 0 := by rw [polar_comm, h.fe]
  have hff' : polar Q R.f P.f = 0 := by rw [polar_comm, h.ff]
  have hwe' : polar Q P.e w = 0 := by rw [polar_comm, hwe]
  have hwf' : polar Q P.f w = 0 := by rw [polar_comm, hwf]
  have hwb' : polar Q R.e w = 0 := by rw [polar_comm, hwb]
  have hwf'' : polar Q R.f w = 0 := by rw [polar_comm, hwfR]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [polar_sub_left, polar_smul_left_eq, P.polar_ee, P.polar_ff, P.polar_ef,
      P.polar_fe, R.polar_ee, R.polar_ff, R.polar_ef, R.polar_fe, h.ee, h.ef, h.fe, h.ff,
      hbe, hbf, hfb, hff', hwe', hwf', hwb', hwf''] <;>
    ring

private theorem axisRadical_le_commutator_exists_polar [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R)
    (hV : 6 ≤ finrank K V) (c : K) :
    ∃ w₁ w₂ : V, w₁ ≠ 0 ∧
      (polar Q w₁ P.e = 0 ∧ polar Q w₁ P.f = 0 ∧ polar Q w₁ R.e = 0 ∧ polar Q w₁ R.f = 0) ∧
      (polar Q w₂ P.e = 0 ∧ polar Q w₂ P.f = 0 ∧ polar Q w₂ R.e = 0 ∧ polar Q w₂ R.f = 0) ∧
      polar Q w₂ w₁ = c := by
  obtain ⟨w₁, hw₁ne, hw₁e, hw₁f, hw₁b, hw₁f'⟩ :=
    axisRadical_le_commutator_exists_ne_zero (Q := Q) (P := P) (R := R) hV
  obtain ⟨v, hv⟩ : ∃ v, polar Q w₁ v ≠ 0 := by
    by_contra h'
    exact hw₁ne (hQ.1 w₁ (by simpa using h'))
  rw [polar_comm] at hv
  let v' : V := v - polar Q v P.f • P.e - polar Q v P.e • P.f -
    polar Q v R.f • R.e - polar Q v R.e • R.f
  have hproj := axisRadical_le_commutator_proj_mem (Q := Q) h (v := v) (v' := v') (w := w₁)
    rfl hw₁e hw₁f hw₁b hw₁f'
  obtain ⟨hv'e, hv'f, hv'b, hv'f', hv'w⟩ := hproj
  have hv'wne : polar Q v' w₁ ≠ 0 := hv'w.symm ▸ hv
  let w₂ : V := (c / polar Q v' w₁) • v'
  have hw₂mem : polar Q w₂ P.e = 0 ∧ polar Q w₂ P.f = 0 ∧
      polar Q w₂ R.e = 0 ∧ polar Q w₂ R.f = 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [w₂, polar_smul_left_eq, hv'e, hv'f, hv'b, hv'f', mul_zero]
  have hw₂w₁ : polar Q w₂ w₁ = c := by
    rw [show w₂ = (c / polar Q v' w₁) • v' from rfl, polar_smul_left_eq, hv'w,
      div_mul_cancel₀ _ hv]
  exact ⟨w₁, w₂, hw₁ne, ⟨hw₁e, hw₁f, hw₁b, hw₁f'⟩, hw₂mem, hw₂w₁⟩

private theorem eichler_swap_span_pair {P R : HypPair Q} (h : P.Orth R) (c : K) :
    eichler Q R.e ((-c) • P.e) = eichler Q P.e (c • R.e) := by
  have hba : polar Q R.e P.e = 0 := by rw [polar_comm, h.ee]
  have h1 : polar Q R.e ((-c) • P.e) = 0 := by
    rw [polar_smul_right_eq, hba, mul_zero]
  have h2 : polar Q P.e (c • R.e) = 0 := by
    rw [polar_smul_right_eq, h.ee, mul_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply R.Q_e h1, eichler_apply P.Q_e h2]
  simp only [polar_smul_right_eq, QuadraticMap.map_smul, smul_eq_mul, R.Q_e, P.Q_e, mul_zero,
    zero_mul, add_zero]
  module

private theorem eichler_comm_eichler_root {P R : HypPair Q} (h : P.Orth R)
    {w₁ w₂ : V} (hw₁e : polar Q P.e w₁ = 0) (hw₁b : polar Q R.e w₁ = 0)
    (hw₂e : polar Q P.e w₂ = 0) (hw₂b : polar Q R.e w₂ = 0) :
    eichler Q P.e w₁ * eichler Q R.e w₂ * (eichler Q P.e w₁)⁻¹ *
        (eichler Q R.e w₂)⁻¹ = eichler Q P.e ((polar Q w₂ w₁) • R.e) := by
  have hba : polar Q R.e P.e = 0 := by rw [polar_comm, h.ee]
  have hneg : polar Q R.e ((-polar Q w₂ w₁) • P.e) = 0 := by
    rw [polar_smul_right_eq, hba, mul_zero]
  have hgb : eichler Q P.e w₁ R.e = R.e := by
    rw [eichler_apply P.Q_e hw₁e]
    simp [hba, hw₁b]
  have hgw₂ : eichler Q P.e w₁ w₂ = w₂ - (polar Q w₂ w₁) • P.e := by
    rw [eichler_apply P.Q_e hw₁e]
    simp only [polar_comm Q w₂ P.e, hw₂e, mul_zero, add_zero, zero_smul]
  have hconj := eichler_conj (eichler_mem_orthogonalGroup Q P.e w₁) R.e w₂
  rw [hgb, hgw₂] at hconj
  have hsum : w₂ - (polar Q w₂ w₁) • P.e = w₂ + (-polar Q w₂ w₁) • P.e := by
    rw [sub_eq_add_neg, neg_smul]
  have hAB : eichler Q R.e w₂ * eichler Q R.e ((-polar Q w₂ w₁) • P.e) =
      eichler Q R.e ((-polar Q w₂ w₁) • P.e) * eichler Q R.e w₂ := by
    rw [eichler_mul hw₂b hneg, eichler_mul hneg hw₂b, add_comm]
  rw [hconj, hsum, ← eichler_mul hw₂b hneg, hAB, mul_assoc, mul_inv_cancel, mul_one]
  exact eichler_swap_span_pair h (polar Q w₂ w₁)

private theorem axisRadical_le_commutator_eichler_root [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R)
    (hV : 6 ≤ finrank K V) (c : K) :
    eichler Q P.e (c • R.e) ∈ ⁅axisParabolic Q P R, axisParabolic Q P R⁆ := by
  obtain ⟨w₁, w₂, -, ⟨hw₁e, -, hw₁b, -⟩, ⟨hw₂e, -, hw₂b, -⟩, hcw⟩ :=
    axisRadical_le_commutator_exists_polar (Q := Q) hQ h hV c
  have hw₁e' : polar Q P.e w₁ = 0 := by rw [polar_comm Q P.e w₁, hw₁e]
  have hw₁b' : polar Q R.e w₁ = 0 := by rw [polar_comm Q R.e w₁, hw₁b]
  have hw₂e' : polar Q P.e w₂ = 0 := by rw [polar_comm Q P.e w₂, hw₂e]
  have hw₂b' : polar Q R.e w₂ = 0 := by rw [polar_comm Q R.e w₂, hw₂b]
  have hmem₁ : eichler Q P.e w₁ ∈ axisParabolic Q P R :=
    Subgroup.subset_closure (Or.inl ⟨P.e, w₁, Submodule.subset_span (by simp), hw₁e', hw₁b', rfl⟩)
  have hmem₂ : eichler Q R.e w₂ ∈ axisParabolic Q P R :=
    Subgroup.subset_closure (Or.inl ⟨R.e, w₂, Submodule.subset_span (by simp), hw₂e', hw₂b', rfl⟩)
  have hcomm := Subgroup.commutator_mem_commutator (H₁ := axisParabolic Q P R)
    (H₂ := axisParabolic Q P R) hmem₁ hmem₂
  rw [commutatorElement_def, eichler_comm_eichler_root (Q := Q) h hw₁e' hw₁b' hw₂e' hw₂b',
    hcw] at hcomm
  exact hcomm

private theorem eichler_pair_apply [CharP K 2] {P R : HypPair Q} (h : P.Orth R) :
    (eichler Q P.e R.f * eichler Q P.f R.e) P.e = R.e ∧
    (eichler Q P.e R.f * eichler Q P.f R.e) R.e = P.e + R.e ∧
    ∀ w, polar Q w P.e = 0 → polar Q w P.f = 0 → polar Q w R.e = 0 → polar Q w R.f = 0 →
      (eichler Q P.e R.f * eichler Q P.f R.e) w = w := by
  have h1 : eichler Q P.f R.e P.e = P.e + R.e := by
    rw [eichler_apply P.Q_f h.fe, P.polar_ef, h.ee, R.Q_e]
    simp
  have h2 : eichler Q P.f R.e R.e = R.e := by
    rw [eichler_apply P.Q_f h.fe, polar_comm Q R.e P.f, h.fe, R.polar_ee]
    simp
  have h3 : eichler Q P.e R.f P.e = P.e := eichler_apply_self P.e R.f
  have haa : P.e + P.e = 0 := by
    rw [← two_smul K P.e, CharTwo.two_eq_zero, zero_smul]
  have hneg : -P.e = P.e := by rw [neg_eq_iff_add_eq_zero, haa]
  have h4 : eichler Q P.e R.f R.e = R.e + P.e := by
    rw [eichler_apply P.Q_e h.ef, polar_comm Q R.e P.e, h.ee, R.polar_ef, R.Q_f]
    simp [sub_eq_add_neg, hneg]
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, h1, map_add, h3, h4]
    rw [add_comm R.e P.e, ← add_assoc, haa, zero_add]
  · rw [LinearEquiv.mul_apply, h2, h4, add_comm]
  · intro w hwe hwf hwb hwf'
    rw [LinearEquiv.mul_apply, eichler_apply_of_polar_eq_zero hwf hwb,
      eichler_apply_of_polar_eq_zero hwe hwf']

private theorem quadratic_eq_zero_of_mem_span_pair {P R : HypPair Q} (h : P.Orth R) {y : V}
    (hy : y ∈ Submodule.span K {P.e, R.e}) : Q y = 0 := by
  obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hy
  simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_left, polar_smul_right,
    smul_eq_mul, P.Q_e, R.Q_e, h.ee, mul_zero, add_zero]

private theorem polar_eq_zero_of_mem_span_pair {P R : HypPair Q} (h : P.Orth R) {y z : V}
    (hy : y ∈ Submodule.span K {P.e, R.e}) (hz : z ∈ Submodule.span K {P.e, R.e}) :
    polar Q y z = 0 := by
  obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hy
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul,
    P.polar_ee, R.polar_ee, h.ee, polar_comm Q R.e P.e, mul_zero, add_zero]

private theorem eichler_span_pair_eichler {P R : HypPair Q} (h : P.Orth R)
    (γ δ α β : K) :
    eichler Q (γ • P.e + δ • R.e) (α • P.e + β • R.e) =
      eichler Q P.e ((γ * β - α * δ) • R.e) := by
  have hu : Q (γ • P.e + δ • R.e) = 0 := by
    simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_left,
      polar_smul_right, smul_eq_mul, P.Q_e, R.Q_e, h.ee, mul_zero, add_zero]
  have huv : polar Q (γ • P.e + δ • R.e) (α • P.e + β • R.e) = 0 := by
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
      smul_eq_mul, P.polar_ee, R.polar_ee, h.ee, polar_comm Q R.e P.e, mul_zero, add_zero]
  have haw : polar Q P.e ((γ * β - α * δ) • R.e) = 0 := by
    rw [polar_smul_right_eq, h.ee, mul_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hu huv, eichler_apply P.Q_e haw]
  simp only [polar_smul_left, polar_add_right, polar_smul_right, smul_eq_mul,
    QuadraticMap.map_add Q, QuadraticMap.map_smul, P.Q_e, R.Q_e, h.ee, mul_zero, zero_mul]
  module

private theorem polar_eq_zero_of_mem_span_pair_right {P R : HypPair Q} {y w : V}
    (hy : y ∈ Submodule.span K {P.e, R.e})
    (hwe : polar Q w P.e = 0) (hwb : polar Q w R.e = 0) : polar Q y w = 0 := by
  obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hy
  simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_comm Q P.e w, hwe,
    polar_comm Q R.e w, hwb, mul_zero, add_zero]

private theorem eichler_pair_span [CharP K 2] {P R : HypPair Q} (h : P.Orth R) {y : V}
    (hy : y ∈ Submodule.span K {P.e, R.e}) :
    (eichler Q P.e R.f * eichler Q P.f R.e) y ∈ Submodule.span K {P.e, R.e} := by
  obtain ⟨hga, hgb, -⟩ := eichler_pair_apply (Q := Q) h
  obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hy
  rw [map_add, map_smul, map_smul, hga, hgb, smul_add]
  exact Submodule.add_mem _ (Submodule.smul_mem _ γ (Submodule.subset_span (by simp)))
    (Submodule.add_mem _ (Submodule.smul_mem _ δ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ δ (Submodule.subset_span (by simp))))

private theorem eichler_pair_span_add [CharP K 2] {P R : HypPair Q} (h : P.Orth R) {y : V}
    (hy : y ∈ Submodule.span K {P.e, R.e}) :
    (eichler Q P.e R.f * eichler Q P.f R.e)
        ((eichler Q P.e R.f * eichler Q P.f R.e) y) +
      (eichler Q P.e R.f * eichler Q P.f R.e) y = y := by
  obtain ⟨hga, hgb, -⟩ := eichler_pair_apply (Q := Q) h
  obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hy
  have h1 : (eichler Q P.e R.f * eichler Q P.f R.e) (γ • P.e + δ • R.e) =
      γ • R.e + δ • (P.e + R.e) := by
    rw [map_add, map_smul, map_smul, hga, hgb]
  have h2 : (eichler Q P.e R.f * eichler Q P.f R.e) (γ • R.e + δ • (P.e + R.e)) =
      γ • (P.e + R.e) + δ • (R.e + (P.e + R.e)) := by
    rw [map_add, map_smul, map_smul, hgb, map_add, hga, hgb]
  have h3 : (3 : K) = 1 := by
    linear_combination CharTwo.two_eq_zero (R := K)
  rw [h1, h2]
  match_scalars <;> ring_nf
  all_goals simp [CharTwo.two_eq_zero, h3]

private theorem axisRadical_le_commutator_eichler_span [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R)
    (hV : 6 ≤ finrank K V) {x y : V}
    (hx : x ∈ Submodule.span K {P.e, R.e}) (hy : y ∈ Submodule.span K {P.e, R.e}) :
    eichler Q x y ∈ ⁅axisParabolic Q P R, axisParabolic Q P R⁆ := by
  obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hy
  rw [eichler_span_pair_eichler h γ δ α β]
  exact axisRadical_le_commutator_eichler_root (Q := Q) hQ h hV (γ * β - α * δ)

private theorem eichler_mul_eichler_add [CharP K 2] {x y w : V}
    (hx : Q x = 0) (hy : Q y = 0) (hxy : polar Q x y = 0)
    (hxw : polar Q x w = 0) (hyw : polar Q y w = 0) :
    eichler Q x w * eichler Q y w = eichler Q (x + y) w * eichler Q x (Q w • y) := by
  have hxy' : Q (x + y) = 0 := by
    rw [QuadraticMap.map_add Q, hx, hy, hxy]
    simp
  have hxyw : polar Q (x + y) w = 0 := by
    rw [polar_add_left, hxw, hyw, add_zero]
  have hxsy : polar Q x (Q w • y) = 0 := by
    rw [polar_smul_right, hxy, smul_zero]
  refine LinearEquiv.ext fun z => ?_
  simp only [LinearEquiv.mul_apply]
  rw [eichler_apply hx hxw, eichler_apply hy hyw,
    eichler_apply hxy' hxyw, eichler_apply hx hxsy]
  simp only [polar_add_left, polar_sub_left, polar_smul_left, polar_add_right,
    polar_smul_right, smul_eq_mul, QuadraticMap.map_smul, hy,
    polar_self_eq_zero hx, polar_self_eq_zero hy, polar_comm Q w x, polar_comm Q y x,
    polar_self, CharTwo.two_nsmul, hxy, hxw, hyw, mul_zero, zero_mul, add_zero]
  match_scalars <;> ring_nf
  all_goals simp [CharTwo.two_eq_zero]

private theorem eichler_pair_comm_mem [CharP K 2] {P R : HypPair Q}
    {g : V ≃ₗ[K] V} (hg : g = eichler Q P.e R.f * eichler Q P.f R.e)
    (hgA : g ∈ axisParabolic Q P R) {x w' : V}
    (hx : eichler Q x w' ∈ axisParabolic Q P R) (hgw : g w' = w') :
    eichler Q (g x) w' * eichler Q x w' ∈ ⁅axisParabolic Q P R, axisParabolic Q P R⁆ := by
  subst hg
  have hgO : (eichler Q P.e R.f * eichler Q P.f R.e) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.mul_mem _ (eichler_mem_orthogonalGroup Q _ _) (eichler_mem_orthogonalGroup Q _ _)
  have hc := Subgroup.commutator_mem_commutator (H₁ := axisParabolic Q P R)
    (H₂ := axisParabolic Q P R) hgA hx
  rw [commutatorElement_def, eichler_conj hgO x w', hgw] at hc
  have hinv : (eichler Q x w')⁻¹ = eichler Q x w' := by
    rw [inv_eq_iff_mul_eq_one]
    exact eichler_mul_self_charTwo x w'
  rwa [hinv] at hc

private theorem axisRadical_le_commutator_eichler_compl [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R)
    (hV : 6 ≤ finrank K V) {u w' : V}
    (hu : u ∈ Submodule.span K {P.e, R.e})
    (hwe : polar Q w' P.e = 0) (hwf : polar Q w' P.f = 0)
    (hwb : polar Q w' R.e = 0) (hwf' : polar Q w' R.f = 0) :
    eichler Q u w' ∈ ⁅axisParabolic Q P R, axisParabolic Q P R⁆ := by
  set g : V ≃ₗ[K] V := eichler Q P.e R.f * eichler Q P.f R.e with hg
  have hgA : g ∈ axisParabolic Q P R := by
    rw [hg]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
      (Subgroup.subset_closure (Or.inr (Or.inr rfl)))
  obtain ⟨hga, hgb, hgw'⟩ := eichler_pair_apply (Q := Q) h
  rw [← hg] at hga hgb hgw'
  have hgw'' : g w' = w' := hgw' w' hwe hwf hwb hwf'
  set x : V := g u with hx
  have hxspan : x ∈ Submodule.span K {P.e, R.e} := by
    rw [hx]
    exact eichler_pair_span h hu
  have hgxspan : g x ∈ Submodule.span K {P.e, R.e} := eichler_pair_span h hxspan
  have hfix : g x + x = u := by
    rw [hx, hg]
    exact eichler_pair_span_add h hu
  have hQx : Q x = 0 := quadratic_eq_zero_of_mem_span_pair h hxspan
  have hQgx : Q (g x) = 0 := quadratic_eq_zero_of_mem_span_pair h hgxspan
  have hpxx : polar Q (g x) x = 0 := polar_eq_zero_of_mem_span_pair h hgxspan hxspan
  have hgxw : polar Q (g x) w' = 0 := polar_eq_zero_of_mem_span_pair_right hgxspan hwe hwb
  have hxw : polar Q x w' = 0 := polar_eq_zero_of_mem_span_pair_right hxspan hwe hwb
  have hprod := eichler_mul_eichler_add (Q := Q) (x := g x) (y := x) (w := w')
    hQgx hQx hpxx hgxw hxw
  have hxmem : eichler Q x w' ∈ axisParabolic Q P R := by
    refine Subgroup.subset_closure (Or.inl ⟨x, w', hxspan, ?_, ?_, rfl⟩)
    · rw [polar_comm Q P.e w', hwe]
    · rw [polar_comm Q R.e w', hwb]
  have hcomm := eichler_pair_comm_mem (Q := Q) hg hgA hxmem hgw''
  have hR : eichler Q (g x) (Q w' • x) ∈
      ⁅axisParabolic Q P R, axisParabolic Q P R⁆ :=
    axisRadical_le_commutator_eichler_span (Q := Q) hQ h hV hgxspan
      (Submodule.smul_mem _ (Q w') hxspan)
  have hmain : eichler Q u w' = eichler Q (g x) w' * eichler Q x w' *
      (eichler Q (g x) (Q w' • x))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← hfix]
    exact hprod.symm
  rw [hmain]
  exact Subgroup.mul_mem _ hcomm (Subgroup.inv_mem _ hR)

private theorem axisRadical_le_commutator_proj_w {P R : HypPair Q} (h : P.Orth R)
    {w : V} (haw : polar Q P.e w = 0) (hbw : polar Q R.e w = 0) :
    let w' : V := w - polar Q w P.f • P.e - polar Q w R.f • R.e
    polar Q w' P.e = 0 ∧ polar Q w' P.f = 0 ∧ polar Q w' R.e = 0 ∧ polar Q w' R.f = 0 := by
  have hfe : polar Q R.e P.f = 0 := by rw [polar_comm, h.fe]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [polar_sub_left, polar_smul_left_eq, P.polar_ee, P.polar_ef, R.polar_ee,
      R.polar_ef, h.ef, hfe, polar_comm Q w P.e, haw, polar_comm Q w R.e, hbw,
      polar_comm Q R.e P.e, h.ee, mul_zero, mul_one, sub_zero, sub_self]

theorem axisRadical_le_commutator [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R) (hV : 6 ≤ finrank K V) :
    axisRadical Q P.e R.e ≤ ⁅axisParabolic Q P R, axisParabolic Q P R⁆ := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨u, w, hu, haw, hbw, rfl⟩
  let w' : V := w - polar Q w P.f • P.e - polar Q w R.f • R.e
  let rest : V := polar Q w P.f • P.e + polar Q w R.f • R.e
  have hw'mem := axisRadical_le_commutator_proj_w (Q := Q) h haw hbw
  obtain ⟨hw'e, hw'f, hw'b, hw'f'⟩ := hw'mem
  have hrestspan : rest ∈ Submodule.span K {P.e, R.e} :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have huw' : eichler Q u w' ∈ ⁅axisParabolic Q P R, axisParabolic Q P R⁆ :=
    axisRadical_le_commutator_eichler_compl (Q := Q) hQ h hV hu hw'e hw'f hw'b hw'f'
  have hurest : eichler Q u rest ∈ ⁅axisParabolic Q P R, axisParabolic Q P R⁆ :=
    axisRadical_le_commutator_eichler_span (Q := Q) hQ h hV hu hrestspan
  have huw'p : polar Q u w' = 0 :=
    polar_eq_zero_of_mem_span_pair_right hu hw'e hw'b
  have hurestp : polar Q u rest = 0 :=
    polar_eq_zero_of_mem_span_pair h hu hrestspan
  have hmul : eichler Q u w = eichler Q u w' * eichler Q u rest := by
    rw [eichler_mul huw'p hurestp]
    congr 1
    simp only [w', rest]
    abel
  rw [hmul]
  exact Subgroup.mul_mem _ huw' hurest

private theorem exists_polar_eq_one (hQ : (polarBilin Q).Nondegenerate) {x : V} (hx : x ≠ 0) :
    ∃ v, polar Q v x = 1 := by
  obtain ⟨v, hv⟩ := exists_polar_ne_zero hQ hx
  have hv' : polar Q v x ≠ 0 := by rwa [polar_comm]
  exact ⟨(polar Q v x)⁻¹ • v, by rw [polar_smul_left_eq, inv_mul_cancel₀ hv']⟩

private theorem exists_polar_eq_one_and_eq_zero (hQ : (polarBilin Q).Nondegenerate) {x y : V}
    (hx : x ≠ 0) (hy : y ∉ Submodule.span K {x}) :
    ∃ v, polar Q v x = 1 ∧ polar Q v y = 0 := by
  obtain ⟨v₀, hv₀⟩ := exists_polar_eq_one hQ hx
  by_cases hc : polar Q v₀ y = 0
  · exact ⟨v₀, hv₀, hc⟩
  obtain ⟨u, hux, huy⟩ : ∃ u, polar Q u x = 0 ∧ polar Q u y ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ u, polar Q u x = 0 → polar Q u y = 0 := by
      intro u hu
      by_contra hne
      exact hcon ⟨u, hu, hne⟩
    have key : ∀ w, polar Q w y = polar Q w x * polar Q v₀ y := by
      intro w
      have hwx : polar Q (w - polar Q w x • v₀) x = 0 := by
        rw [polar_sub_left, polar_smul_left_eq, hv₀, mul_one, sub_self]
      have h1 : polar Q ((w - polar Q w x • v₀) + polar Q w x • v₀) y =
          polar Q (w - polar Q w x • v₀) y + polar Q (polar Q w x • v₀) y :=
        polar_add_left ..
      rw [show (w - polar Q w x • v₀) + polar Q w x • v₀ = w by abel] at h1
      rw [h1, hcon' _ hwx, polar_smul_left_eq, zero_add]
    refine hy (Submodule.mem_span_singleton.mpr ⟨polar Q v₀ y, ?_⟩)
    have h0 : y - polar Q v₀ y • x = 0 := by
      refine eq_zero_of_polar_eq_zero hQ fun w => ?_
      rw [polar_sub_left, polar_smul_left_eq, polar_comm Q y w, polar_comm Q x w, key w]
      ring
    exact (sub_eq_zero.mp h0).symm
  refine ⟨v₀ - (polar Q v₀ y / polar Q u y) • u, ?_, ?_⟩
  · rw [polar_sub_left, polar_smul_left_eq, hux, mul_zero, sub_zero]
    exact hv₀
  · rw [polar_sub_left, polar_smul_left_eq, div_mul_cancel₀ _ huy, sub_self]

private theorem ne_zero_of_linearIndependent_pair {x y : V}
    (h : LinearIndependent K ![x, y]) : x ≠ 0 := by
  intro hx
  have h1 := LinearIndependent.pair_iff.mp h 1 0 (by simp [hx])
  exact one_ne_zero h1.1

private theorem notMem_span_of_linearIndependent_pair {x y : V}
    (h : LinearIndependent K ![x, y]) : y ∉ Submodule.span K {x} := by
  intro hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have h1 := LinearIndependent.pair_iff.mp h (-c) 1 (by rw [neg_smul, one_smul]; abel)
  exact one_ne_zero h1.2

private theorem eichler_apply_sub_mem_span_pair (u w x : V) :
    eichler Q u w x - x ∈ Submodule.span K {u, w} := by
  obtain ⟨α, β, hα⟩ := eichler_apply_eq_add (Q := Q) u w x
  have h : eichler Q u w x - x = α • w + β • u := by rw [hα]; abel
  rw [h]
  exact Submodule.mem_span_pair.mpr ⟨β, α, add_comm _ _⟩

private theorem mem_span_pair_of_eichler_eq (hQ : (polarBilin Q).Nondegenerate) {x y u w : V}
    (hxy : LinearIndependent K ![x, y]) (hx : Q x = 0) (hpxy : polar Q x y = 0)
    (he : eichler Q x y = eichler Q u w) :
    x ∈ Submodule.span K {u, w} ∧ y ∈ Submodule.span K {u, w} := by
  have hxy' : LinearIndependent K ![y, x] := LinearIndependent.pair_symm_iff.mp hxy
  obtain ⟨v₁, hv₁x, hv₁y⟩ :=
    exists_polar_eq_one_and_eq_zero hQ (ne_zero_of_linearIndependent_pair hxy)
      (notMem_span_of_linearIndependent_pair hxy)
  obtain ⟨v₂, hv₂y, hv₂x⟩ :=
    exists_polar_eq_one_and_eq_zero hQ (ne_zero_of_linearIndependent_pair hxy')
      (notMem_span_of_linearIndependent_pair hxy')
  have h₁ : eichler Q x y v₁ = eichler Q u w v₁ := by rw [he]
  have h₂ : eichler Q x y v₂ = eichler Q u w v₂ := by rw [he]
  have hw₁ : eichler Q x y v₁ = v₁ + (y - Q y • x) := by
    rw [eichler_apply hx hpxy, hv₁x, hv₁y]
    simp only [one_smul, zero_add, mul_one]
    abel
  have hw₂ : eichler Q x y v₂ = v₂ - x := by
    rw [eichler_apply hx hpxy, hv₂x, hv₂y]
    simp only [zero_smul, one_smul, add_zero, mul_zero]
  have hneg : -x ∈ Submodule.span K {u, w} := by
    have h := eichler_apply_sub_mem_span_pair (Q := Q) u w v₂
    rw [← h₂, hw₂] at h
    simpa using h
  have hx₂ : x ∈ Submodule.span K {u, w} := by
    simpa using neg_mem hneg
  have hy₁ : y - Q y • x ∈ Submodule.span K {u, w} := by
    have h := eichler_apply_sub_mem_span_pair (Q := Q) u w v₁
    rw [← h₁, hw₁] at h
    simpa using h
  refine ⟨hx₂, ?_⟩
  have h4 : (y - Q y • x) + Q y • x ∈ Submodule.span K {u, w} :=
    add_mem hy₁ (Submodule.smul_mem _ _ hx₂)
  rwa [sub_add_cancel] at h4

private theorem eichler_conj_eq_of_mem_centralizer {z : V ≃ₗ[K] V}
    (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {a b : V}
    (hzc : z ∈ Subgroup.centralizer (axisRadical Q a b : Set (V ≃ₗ[K] V)))
    {u w : V} (hu : u ∈ Submodule.span K {a, b}) (ha : polar Q a w = 0)
    (hb : polar Q b w = 0) : eichler Q (z u) (z w) = eichler Q u w := by
  have hmem : eichler Q u w ∈ axisRadical Q a b :=
    Subgroup.subset_closure ⟨u, w, hu, ha, hb, rfl⟩
  have hcomm : eichler Q u w * z = z * eichler Q u w :=
    (Subgroup.mem_centralizer_iff.mp hzc) _ hmem
  have h := eichler_conj hz u w
  rw [← hcomm] at h
  simpa using h.symm

private theorem mem_span_pair_of_mem_centralizer (hQ : (polarBilin Q).Nondegenerate)
    {z : V ≃ₗ[K] V} (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {a b : V}
    (hzc : z ∈ Subgroup.centralizer (axisRadical Q a b : Set (V ≃ₗ[K] V)))
    {u w : V} (hu : u ∈ Submodule.span K {a, b}) (ha : polar Q a w = 0)
    (hb : polar Q b w = 0) (huw : LinearIndependent K ![u, w])
    (huQ : Q u = 0) (huw0 : polar Q u w = 0) :
    z u ∈ Submodule.span K {u, w} ∧ z w ∈ Submodule.span K {u, w} := by
  have he : eichler Q (z u) (z w) = eichler Q u w :=
    eichler_conj_eq_of_mem_centralizer hz hzc hu ha hb
  have hli : LinearIndependent K ![z u, z w] := by
    rw [LinearIndependent.pair_iff] at huw ⊢
    intro s t hst
    apply huw s t
    have h0 : z (s • u + t • w) = 0 := by rw [map_add, map_smul, map_smul, hst]
    exact z.injective (by rw [h0, map_zero])
  exact mem_span_pair_of_eichler_eq hQ hli (by rw [map_of_mem hz, huQ])
    (by rw [polar_map_of_mem hz, huw0]) he

private theorem Q_eq_zero_of_mem_span_pair {a b u : V} (ha : Q a = 0) (hb : Q b = 0)
    (hab : polar Q a b = 0) (hu : u ∈ Submodule.span K {a, b}) : Q u = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
    polar_smul_right_eq, ha, hb, hab]
  ring

private theorem polar_eq_zero_of_mem_span_pair_of_polar {a b w u : V}
    (hu : u ∈ Submodule.span K {a, b}) (haw : polar Q a w = 0) (hbw : polar Q b w = 0) :
    polar Q u w = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, haw, hbw]
  ring

private theorem inf_span_pair_eq_span_of_notMem {a b v : V}
    (hab : LinearIndependent K ![a, b]) (hv : v ∉ Submodule.span K {a, b}) :
    Submodule.span K {a, v} ⊓ Submodule.span K {b, v} = Submodule.span K {v} := by
  have hva : a ∈ Submodule.span K {a, b} :=
    Submodule.mem_span_pair.mpr ⟨1, 0, by rw [one_smul, zero_smul, add_zero]⟩
  have hvb : b ∈ Submodule.span K {a, b} :=
    Submodule.mem_span_pair.mpr ⟨0, 1, by rw [zero_smul, zero_add, one_smul]⟩
  refine le_antisymm ?_ (le_inf (Submodule.span_mono (Set.subset_insert a {v}))
    (Submodule.span_mono (Set.subset_insert b {v})))
  rintro x ⟨hxa, hxb⟩
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hxa
  obtain ⟨γ, δ, hγ⟩ := Submodule.mem_span_pair.mp hxb
  have h2 : α • a - γ • b = δ • v - β • v := by
    calc α • a - γ • b
        = (α • a + β • v) - (γ • b + β • v) := by abel
      _ = (γ • b + δ • v) - (γ • b + β • v) := by rw [hγ]
      _ = δ • v - β • v := by abel
  have hmem : (δ - β) • v ∈ Submodule.span K {a, b} := by
    rw [sub_smul, ← h2]
    exact Submodule.sub_mem (Submodule.span K {a, b})
      ((Submodule.span K {a, b}).smul_mem _ hva) ((Submodule.span K {a, b}).smul_mem _ hvb)
  have hdb : δ - β = 0 := by
    by_contra hne
    refine hv ?_
    have hv' : v = (δ - β)⁻¹ • ((δ - β) • v) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [hv']
    exact Submodule.smul_mem _ _ hmem
  have hα : α = 0 ∧ γ = 0 := by
    have h0 : δ • v - β • v = 0 := by rw [← sub_smul, hdb, zero_smul]
    exact hab.eq_zero_of_pair' (sub_eq_zero.mp (h2.trans h0))
  rw [hα.1, zero_smul, zero_add]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

private theorem eq_zero_of_mem_span_pair_of_polar_eq_zero {a f b f' x : V}
    (hfa : polar Q f a = 1) (hfb : polar Q f b = 0) (hf'a : polar Q f' a = 0)
    (hf'b : polar Q f' b = 1) (hx : x ∈ Submodule.span K {a, b})
    (h1 : polar Q f x = 0) (h2 : polar Q f' x = 0) : x = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hfa, hfb, mul_one, mul_zero,
    add_zero] at h1
  rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hf'a, hf'b, mul_zero, mul_one,
    zero_add] at h2
  rw [h1, h2, zero_smul, zero_smul, add_zero]

private theorem exists_mem_axisPerp_ne_zero [FiniteDimensional K V] {a f b f' : V}
    (hV : 6 ≤ finrank K V) :
    ∃ w : V, w ≠ 0 ∧ polar Q a w = 0 ∧ polar Q f w = 0 ∧ polar Q b w = 0 ∧
      polar Q f' w = 0 := by
  classical
  let φ : V →ₗ[K] (Fin 4 → K) :=
    { toFun := fun x => ![polar Q a x, polar Q f x, polar Q b x, polar Q f' x]
      map_add' := fun x y => by funext i; fin_cases i <;> simp [polar_add_right]
      map_smul' := fun c x => by
        funext i; fin_cases i <;> simp [polar_smul_right, smul_eq_mul] }
  have hφ : ∀ x, φ x = ![polar Q a x, polar Q f x, polar Q b x, polar Q f' x] := fun _ => rfl
  have hmem : ∀ x, x ∈ LinearMap.ker φ ↔ polar Q a x = 0 ∧ polar Q f x = 0 ∧
      polar Q b x = 0 ∧ polar Q f' x = 0 := by
    intro x
    refine ⟨fun hx => ⟨?_, ?_, ?_, ?_⟩, fun hx => ?_⟩
    · simpa [hφ] using congrFun (LinearMap.mem_ker.mp hx) 0
    · simpa [hφ] using congrFun (LinearMap.mem_ker.mp hx) 1
    · simpa [hφ] using congrFun (LinearMap.mem_ker.mp hx) 2
    · simpa [hφ] using congrFun (LinearMap.mem_ker.mp hx) 3
    · rw [LinearMap.mem_ker, hφ, funext_iff]
      rintro i
      fin_cases i
      · simpa using hx.1
      · simpa using hx.2.1
      · simpa using hx.2.2.1
      · simpa using hx.2.2.2
  have hfin : 2 ≤ finrank K (LinearMap.ker φ) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker φ
    have hle : finrank K (LinearMap.range φ) ≤ 4 := by
      simpa [Module.finrank_fin_fun] using (LinearMap.range φ).finrank_le
    omega
  have hne : LinearMap.ker φ ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hfin
    omega
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ LinearMap.ker φ, w ≠ 0 := by
    by_contra hcon
    apply hne
    rw [eq_bot_iff]
    intro y hy
    by_contra hy0
    exact hcon ⟨y, hy, hy0⟩
  exact ⟨w, hw0, (hmem w).mp hw⟩

private theorem exists_polar_ne_zero_of_mem_axisPerp (hQ : (polarBilin Q).Nondegenerate)
    {P R : HypPair Q} (h : P.Orth R) {z : V}
    (hz : polar Q P.e z = 0 ∧ polar Q P.f z = 0 ∧ polar Q R.e z = 0 ∧ polar Q R.f z = 0)
    (hz0 : z ≠ 0) :
    ∃ y, (polar Q P.e y = 0 ∧ polar Q P.f y = 0 ∧ polar Q R.e y = 0 ∧
      polar Q R.f y = 0) ∧ polar Q z y ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_polar_ne_zero hQ hz0
  refine ⟨v - polar Q v P.f • P.e - polar Q v P.e • P.f - polar Q v R.f • R.e -
    polar Q v R.e • R.f, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [polar_sub_right, polar_sub_right, polar_sub_right, polar_sub_right,
      polar_smul_right_eq, polar_smul_right_eq, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q P.e v, P.polar_ee, P.polar_ef, h.ee, h.ef]
    ring
  · rw [polar_sub_right, polar_sub_right, polar_sub_right, polar_sub_right,
      polar_smul_right_eq, polar_smul_right_eq, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q P.f v, P.polar_fe, P.polar_ff, h.fe, h.ff]
    ring
  · rw [polar_sub_right, polar_sub_right, polar_sub_right, polar_sub_right,
      polar_smul_right_eq, polar_smul_right_eq, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q R.e v, polar_comm Q R.e P.e, polar_comm Q R.e P.f, R.polar_ee,
      R.polar_ef, h.ee, h.fe]
    ring
  · rw [polar_sub_right, polar_sub_right, polar_sub_right, polar_sub_right,
      polar_smul_right_eq, polar_smul_right_eq, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q R.f v, polar_comm Q R.f P.e, polar_comm Q R.f P.f, R.polar_fe,
      R.polar_ff, h.ef, h.ff]
    ring
  · rw [polar_sub_right, polar_sub_right, polar_sub_right, polar_sub_right,
      polar_smul_right_eq, polar_smul_right_eq, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q z P.e, polar_comm Q z P.f, polar_comm Q z R.e, polar_comm Q z R.f,
      hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
    simpa using hv

private theorem exists_nonsingular_of_mem_axisPerp (hQ : (polarBilin Q).Nondegenerate)
    {P R : HypPair Q} (h : P.Orth R) {x : V} (hx0 : x ≠ 0)
    (hx : polar Q P.e x = 0 ∧ polar Q P.f x = 0 ∧ polar Q R.e x = 0 ∧ polar Q R.f x = 0) :
    ∃ w, polar Q P.e w = 0 ∧ polar Q P.f w = 0 ∧ polar Q R.e w = 0 ∧
      polar Q R.f w = 0 ∧ Q w ≠ 0 := by
  by_contra hcon
  have hall : ∀ w : V, (polar Q P.e w = 0 ∧ polar Q P.f w = 0 ∧ polar Q R.e w = 0 ∧
      polar Q R.f w = 0) → Q w = 0 := by
    intro w hw
    by_contra hw0
    exact hcon ⟨w, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, hw0⟩
  obtain ⟨y, hy, hxy⟩ := exists_polar_ne_zero_of_mem_axisPerp hQ h hx hx0
  have h1 : Q (x + y) = 0 := hall (x + y)
    ⟨by rw [polar_add_right, hx.1, hy.1, add_zero],
     by rw [polar_add_right, hx.2.1, hy.2.1, add_zero],
     by rw [polar_add_right, hx.2.2.1, hy.2.2.1, add_zero],
     by rw [polar_add_right, hx.2.2.2, hy.2.2.2, add_zero]⟩
  rw [QuadraticMap.map_add Q, hall x hx, hall y hy, zero_add, zero_add] at h1
  exact hxy h1

private theorem exists_nonsingular_mem_axisPerp [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R)
    (hV : 6 ≤ finrank K V) :
    ∃ w, polar Q P.e w = 0 ∧ polar Q P.f w = 0 ∧ polar Q R.e w = 0 ∧
      polar Q R.f w = 0 ∧ Q w ≠ 0 := by
  obtain ⟨x, hx0, hx⟩ := exists_mem_axisPerp_ne_zero (Q := Q) (a := P.e) (f := P.f) (b := R.e)
    (f' := R.f) hV
  exact exists_nonsingular_of_mem_axisPerp hQ h hx0 ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩

private theorem linearIndependent_apply {P R : HypPair Q} (h : P.Orth R) :
    LinearIndependent K ![P.e, R.e] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  constructor
  · have h1 : polar Q P.f (s • P.e + t • R.e) = 0 := by rw [hst, polar_zero_right]
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_fe, h.fe,
      mul_one, mul_zero, add_zero] at h1
    exact h1
  · have h1 : polar Q R.f (s • P.e + t • R.e) = 0 := by rw [hst, polar_zero_right]
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_comm Q R.f P.e,
      h.ef, R.polar_fe, mul_zero, mul_one, zero_add] at h1
    exact h1

private theorem apply_mem_span_self_of_mem_span_pair [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R)
    (hV : 6 ≤ finrank K V) {z : V ≃ₗ[K] V}
    (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hzc : z ∈ Subgroup.centralizer (axisRadical Q P.e R.e : Set (V ≃ₗ[K] V)))
    {v : V} (hvU : v ∈ Submodule.span K {P.e, R.e}) :
    z v ∈ Submodule.span K {v} := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  · obtain ⟨w, hw1, hw2, hw3, hw4, hQw⟩ := exists_nonsingular_mem_axisPerp hQ h hV
    have hvw : LinearIndependent K ![v, w] := by
      rw [LinearIndependent.pair_iff' hv0]
      intro c hc
      have hmem : w ∈ Submodule.span K {P.e, R.e} := hc ▸ Submodule.smul_mem _ _ hvU
      have h0 : w = 0 := eq_zero_of_mem_span_pair_of_polar_eq_zero P.polar_fe h.fe
        (by rw [polar_comm, h.ef]) R.polar_fe hmem hw2 hw4
      exact hQw (h0 ▸ QuadraticMap.map_zero Q)
    have hres := mem_span_pair_of_mem_centralizer hQ hz hzc hvU hw1 hw3 hvw
      (Q_eq_zero_of_mem_span_pair P.Q_e R.Q_e h.ee hvU)
      (polar_eq_zero_of_mem_span_pair_of_polar hvU hw1 hw3)
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hres.1
    have hQv : Q v = 0 := Q_eq_zero_of_mem_span_pair P.Q_e R.Q_e h.ee hvU
    have hβ : β = 0 := by
      have h2 : β ^ 2 * Q w = 0 := by
        have h0 : Q (z v) = 0 := by rw [map_of_mem hz, hQv]
        rw [← hαβ, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hQv,
          polar_smul_left_eq, polar_smul_right_eq,
          polar_eq_zero_of_mem_span_pair_of_polar hvU hw1 hw3] at h0
        simpa using h0
      by_contra hβ
      rcases mul_eq_zero.mp h2 with h | h
      · rw [pow_two] at h
        exact hβ ((mul_eq_zero.mp h).elim id id)
      · exact hQw h
    rw [hβ, zero_smul, add_zero] at hαβ
    rw [← hαβ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

private theorem apply_mem_span_self_of_notMem_span_pair (hQ : (polarBilin Q).Nondegenerate)
    {P R : HypPair Q} (h : P.Orth R) {z : V ≃ₗ[K] V}
    (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hzc : z ∈ Subgroup.centralizer (axisRadical Q P.e R.e : Set (V ≃ₗ[K] V)))
    {v : V} (hva : polar Q P.e v = 0) (hvb : polar Q R.e v = 0)
    (hvU : v ∉ Submodule.span K {P.e, R.e}) :
    z v ∈ Submodule.span K {v} := by
  have hspan_ae : P.e ∈ Submodule.span K {P.e, R.e} :=
    Submodule.mem_span_pair.mpr ⟨1, 0, by rw [one_smul, zero_smul, add_zero]⟩
  have hspan_be : R.e ∈ Submodule.span K {P.e, R.e} :=
    Submodule.mem_span_pair.mpr ⟨0, 1, by rw [zero_smul, zero_add, one_smul]⟩
  have hPev : LinearIndependent K ![P.e, v] := by
    rw [LinearIndependent.pair_iff' P.e_ne_zero]
    intro c hc
    exact hvU (hc ▸ (Submodule.span K {P.e, R.e}).smul_mem _ hspan_ae)
  have hRev : LinearIndependent K ![R.e, v] := by
    rw [LinearIndependent.pair_iff' R.e_ne_zero]
    intro c hc
    exact hvU (hc ▸ (Submodule.span K {P.e, R.e}).smul_mem _ hspan_be)
  have h1 := mem_span_pair_of_mem_centralizer hQ hz hzc hspan_ae hva hvb hPev P.Q_e hva
  have h2 := mem_span_pair_of_mem_centralizer hQ hz hzc hspan_be hva hvb hRev R.Q_e hvb
  have hmem : z v ∈ Submodule.span K {P.e, v} ⊓ Submodule.span K {R.e, v} := ⟨h1.2, h2.2⟩
  rwa [inf_span_pair_eq_span_of_notMem (linearIndependent_apply h) hvU] at hmem

private theorem apply_mem_span_self_of_mem_centralizer [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate)
    {P R : HypPair Q} (h : P.Orth R) (hV : 6 ≤ finrank K V) {z : V ≃ₗ[K] V}
    (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hzc : z ∈ Subgroup.centralizer (axisRadical Q P.e R.e : Set (V ≃ₗ[K] V)))
    {v : V} (hva : polar Q P.e v = 0) (hvb : polar Q R.e v = 0) :
    z v ∈ Submodule.span K {v} := by
  by_cases hvU : v ∈ Submodule.span K {P.e, R.e}
  · exact apply_mem_span_self_of_mem_span_pair hQ h hV hz hzc hvU
  · exact apply_mem_span_self_of_notMem_span_pair hQ h hz hzc hva hvb hvU

private theorem exists_eq_smul_of_mem_span_self {W : Submodule K V} {z : V →ₗ[K] V} {u v : V}
    (hu : u ∈ W) (hv : v ∈ W) (huv : LinearIndependent K ![u, v])
    (hspan : ∀ x ∈ W, z x ∈ Submodule.span K {x}) :
    ∃ μ : K, ∀ x ∈ W, z x = μ • x := by
  obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp (hspan u hu)
  obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp (hspan v hv)
  obtain ⟨c₃, hc₃⟩ := Submodule.mem_span_singleton.mp (hspan (u + v) (W.add_mem hu hv))
  have h12 : c₁ = c₂ := by
    have h : c₁ • u + c₂ • v = c₃ • u + c₃ • v := by
      rw [hc₁, hc₂, ← map_add, ← smul_add, ← hc₃]
    have h4 := huv.eq_of_pair h
    exact h4.1.trans h4.2.symm
  have hu0 : u ≠ 0 := ne_zero_of_linearIndependent_pair huv
  refine ⟨c₁, fun x hx => ?_⟩
  by_cases hxu : x ∈ Submodule.span K {u}
  · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hxu
    rw [map_smul, ← hc₁, smul_smul, smul_smul, mul_comm]
  · obtain ⟨cx, hcx⟩ := Submodule.mem_span_singleton.mp (hspan x hx)
    obtain ⟨c₄, hc₄⟩ := Submodule.mem_span_singleton.mp (hspan (x + u) (W.add_mem hx hu))
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hxu (Submodule.span K {u}).zero_mem
    have hxu' : LinearIndependent K ![x, u] := by
      rw [LinearIndependent.pair_iff' hx0]
      intro t ht
      by_cases ht0 : t = 0
      · subst ht0
        rw [zero_smul] at ht
        exact hu0 ht.symm
      · refine hxu ?_
        have hx' : x = t⁻¹ • u := by rw [← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
        rw [hx']
        exact (Submodule.span K {u}).smul_mem _ (Submodule.mem_span_singleton_self u)
    have h : cx • x + c₁ • u = c₄ • x + c₄ • u := by
      rw [hcx, hc₁, ← map_add, ← smul_add, ← hc₄]
    have h4 := hxu'.eq_of_pair h
    rw [← hcx, h4.1.trans h4.2.symm]

private theorem mem_span_pair_of_forall_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate)
    {P R : HypPair Q} (h : P.Orth R) {y : V}
    (hy : ∀ x, polar Q P.e x = 0 → polar Q R.e x = 0 → polar Q y x = 0) :
    y ∈ Submodule.span K {P.e, R.e} := by
  have hspan_ae : P.e ∈ Submodule.span K {P.e, R.e} :=
    Submodule.mem_span_pair.mpr ⟨1, 0, by rw [one_smul, zero_smul, add_zero]⟩
  have hspan_be : R.e ∈ Submodule.span K {P.e, R.e} :=
    Submodule.mem_span_pair.mpr ⟨0, 1, by rw [zero_smul, zero_add, one_smul]⟩
  set y₀ := y - polar Q y P.f • P.e - polar Q y R.f • R.e with hy₀
  have hm1 : polar Q P.e y₀ = 0 := by
    rw [hy₀, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q P.e y, P.polar_ee, h.ee, hy P.e P.polar_ee (by rw [polar_comm, h.ee])]
    ring
  have hm2 : polar Q P.f y₀ = 0 := by
    rw [hy₀, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q P.f y, P.polar_fe, h.fe]
    ring
  have hm3 : polar Q R.e y₀ = 0 := by
    rw [hy₀, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q R.e y, polar_comm Q R.e P.e, R.polar_ee, h.ee,
      hy R.e h.ee R.polar_ee]
    ring
  have hm4 : polar Q R.f y₀ = 0 := by
    rw [hy₀, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q R.f y, polar_comm Q R.f P.e, h.ef, R.polar_fe]
    ring
  have horth : ∀ x, polar Q P.e x = 0 → polar Q P.f x = 0 → polar Q R.e x = 0 →
      polar Q R.f x = 0 → polar Q y₀ x = 0 := by
    intro x hx1 hx2 hx3 hx4
    rw [hy₀, polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq,
      hy x hx1 hx3, hx1, hx3]
    ring
  have hy₀0 : y₀ = 0 := by
    by_contra h0
    obtain ⟨x, hx, hxy⟩ := exists_polar_ne_zero_of_mem_axisPerp hQ h ⟨hm1, hm2, hm3, hm4⟩ h0
    exact hxy (horth x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2)
  have hsub : y - polar Q y P.f • P.e = polar Q y R.f • R.e := by
    rw [hy₀] at hy₀0
    exact sub_eq_zero.mp hy₀0
  have hy_eq : y = polar Q y P.f • P.e + polar Q y R.f • R.e := by rw [← hsub]; abel
  rw [hy_eq]
  exact (Submodule.span K {P.e, R.e}).add_mem
    ((Submodule.span K {P.e, R.e}).smul_mem _ hspan_ae)
    ((Submodule.span K {P.e, R.e}).smul_mem _ hspan_be)

private theorem sub_apply_mem_span_pair_of_fixes_axisPerp (hQ : (polarBilin Q).Nondegenerate)
    {P R : HypPair Q} (h : P.Orth R) {z : V ≃ₗ[K] V}
    (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hzfix : ∀ v, polar Q P.e v = 0 → polar Q R.e v = 0 → z v = v) (x : V) :
    z x - x ∈ Submodule.span K {P.e, R.e} := by
  refine mem_span_pair_of_forall_polar_eq_zero hQ h fun w hw1 hw2 => ?_
  have hstep : polar Q (z x) w = polar Q x w := by
    conv_lhs => rw [← hzfix w hw1 hw2]
    rw [polar_map_of_mem hz]
  rw [polar_sub_left, hstep, sub_self]

private theorem Q_apply_add_smul_axis {P R : HypPair Q} (h : P.Orth R) (α β : K) :
    Q (P.f + α • P.e + β • R.e) = α := by
  simp only [QuadraticMap.map_add Q, map_smul_eq_sq, polar_add_left, polar_smul_left_eq,
    polar_smul_right_eq, P.Q_e, P.Q_f, R.Q_e, P.polar_fe, h.ee, h.fe, mul_zero, mul_one,
    add_zero, zero_add]

private theorem Q_apply_add_smul_axis' {P R : HypPair Q} (h : P.Orth R) (γ δ : K) :
    Q (R.f + γ • P.e + δ • R.e) = δ := by
  simp only [QuadraticMap.map_add Q, map_smul_eq_sq, polar_add_left, polar_smul_left_eq,
    polar_smul_right_eq, P.Q_e, R.Q_e, R.Q_f, polar_comm Q R.f P.e, h.ef, R.polar_fe,
    h.ee, mul_zero, mul_one, add_zero, zero_add]

private theorem polar_apply_add_smul_axis {P R : HypPair Q} (h : P.Orth R) {β γ : K} :
    polar Q (P.f + β • R.e) (R.f + γ • P.e) = γ + β := by
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    h.ff, P.polar_fe, R.polar_ef, polar_comm Q R.e P.e, h.ee, mul_one, mul_zero,
    add_zero, zero_add]
  ring

private theorem eichler_apply_axis_f {P R : HypPair Q} (h : P.Orth R) (d : K) :
    eichler Q P.e (d • R.e) P.f = P.f + d • R.e := by
  have hw : polar Q P.e (d • R.e) = 0 := by
    rw [QuadraticMap.polar_smul_right, h.ee, smul_zero]
  rw [eichler_apply P.Q_e hw]
  simp [QuadraticMap.polar_smul_right, h.fe, P.polar_fe, QuadraticMap.map_smul, R.Q_e]

private theorem eichler_apply_axis_f' [CharP K 2] {P R : HypPair Q} (h : P.Orth R) (d : K) :
    eichler Q P.e (d • R.e) R.f = R.f + d • P.e := by
  have hw : polar Q P.e (d • R.e) = 0 := by
    rw [QuadraticMap.polar_smul_right, h.ee, smul_zero]
  have hneg : R.f - d • P.e = R.f + d • P.e := by
    rw [sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
  rw [eichler_apply P.Q_e hw]
  simp only [QuadraticMap.polar_smul_right, polar_comm Q R.f P.e, h.ef, R.polar_fe,
    QuadraticMap.map_smul, R.Q_e, mul_zero, add_zero, zero_smul, smul_eq_mul, mul_one]
  exact hneg

private theorem eichler_eq_of_apply_eq [CharP K 2] {P R : HypPair Q} (h : P.Orth R)
    {z : V ≃ₗ[K] V} (hzfix : ∀ v, polar Q P.e v = 0 → polar Q R.e v = 0 → z v = v) {β : K}
    (hzf : z P.f = P.f + β • R.e) (hzf' : z R.f = R.f + β • P.e) :
    z = eichler Q P.e (β • R.e) := by
  refine LinearEquiv.ext fun v => ?_
  set v₀ := v - polar Q v P.e • P.f - polar Q v R.e • R.f with hv₀
  have hv₀1 : polar Q P.e v₀ = 0 := by
    rw [hv₀, polar_sub_right, polar_sub_right, polar_comm Q P.e v, polar_smul_right_eq,
      polar_smul_right_eq, P.polar_ef, h.ef]
    ring
  have hv₀2 : polar Q R.e v₀ = 0 := by
    rw [hv₀, polar_sub_right, polar_sub_right, polar_comm Q R.e v, polar_smul_right_eq,
      polar_smul_right_eq, polar_comm Q R.e P.f, h.fe, R.polar_ef]
    ring
  have hz0 : z v₀ = v₀ := hzfix v₀ hv₀1 hv₀2
  have he0 : eichler Q P.e (β • R.e) v₀ = v₀ := by
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [polar_comm, hv₀1]
    · rw [polar_smul_right_eq, polar_comm, hv₀2, mul_zero]
  have hsplit : v = v₀ + polar Q v P.e • P.f + polar Q v R.e • R.f := by rw [hv₀]; abel
  have hLHS : z v = v₀ + polar Q v P.e • (P.f + β • R.e) + polar Q v R.e • (R.f + β • P.e) := by
    conv_lhs => rw [hsplit]
    simp only [map_add, map_smul]
    rw [hz0, hzf, hzf']
  have hRHS : eichler Q P.e (β • R.e) v =
      v₀ + polar Q v P.e • (P.f + β • R.e) + polar Q v R.e • (R.f + β • P.e) := by
    conv_lhs => rw [hsplit]
    simp only [map_add, map_smul]
    rw [he0, eichler_apply_axis_f h β, eichler_apply_axis_f' h β]
  rw [hLHS, hRHS]

private theorem exists_eichler_eq_of_fixes_axisPerp [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R)
    {z : V ≃ₗ[K] V} (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hzfix : ∀ v, polar Q P.e v = 0 → polar Q R.e v = 0 → z v = v) :
    ∃ c : K, z = eichler Q P.e (c • R.e) := by
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp
    (sub_apply_mem_span_pair_of_fixes_axisPerp hQ h hz hzfix P.f)
  obtain ⟨γ, δ, hγδ⟩ := Submodule.mem_span_pair.mp
    (sub_apply_mem_span_pair_of_fixes_axisPerp hQ h hz hzfix R.f)
  have hzf : z P.f = P.f + α • P.e + β • R.e := by
    rw [sub_eq_iff_eq_add.mp hαβ.symm]; abel
  have hzf' : z R.f = R.f + γ • P.e + δ • R.e := by
    rw [sub_eq_iff_eq_add.mp hγδ.symm]; abel
  have hα : α = 0 := by
    rw [← Q_apply_add_smul_axis h α β, ← hzf, map_of_mem hz, P.Q_f]
  have hδ : δ = 0 := by
    rw [← Q_apply_add_smul_axis' h γ δ, ← hzf', map_of_mem hz, R.Q_f]
  have hzf2 : z P.f = P.f + β • R.e := by rw [hzf, hα, zero_smul]; abel
  have hzf'2 : z R.f = R.f + γ • P.e := by rw [hzf', hδ, zero_smul]; abel
  have hγ : γ = β := by
    have h1 : polar Q (P.f + β • R.e) (R.f + γ • P.e) = 0 := by
      rw [← hzf2, ← hzf'2, polar_map_of_mem hz, h.ff]
    rw [polar_apply_add_smul_axis h] at h1
    rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h1
  exact ⟨β, eichler_eq_of_apply_eq h hzfix hzf2 (hγ ▸ hzf'2)⟩

private theorem apply_eq_self_of_mem_centralizer [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R)
    (hV : 6 ≤ finrank K V) {z : V ≃ₗ[K] V}
    (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hzc : z ∈ Subgroup.centralizer (axisRadical Q P.e R.e : Set (V ≃ₗ[K] V))) :
    ∀ v, polar Q P.e v = 0 → polar Q R.e v = 0 → z v = v := by
  set W : Submodule K V :=
    LinearMap.ker (polarBilin Q P.e) ⊓ LinearMap.ker (polarBilin Q R.e) with hW
  have hWmem : ∀ x, x ∈ W ↔ polar Q P.e x = 0 ∧ polar Q R.e x = 0 := by
    intro x
    simp [hW]
  have hspanW : ∀ x ∈ W, z x ∈ Submodule.span K {x} := by
    intro x hx
    exact apply_mem_span_self_of_mem_centralizer hQ h hV hz hzc
      ((hWmem x).mp hx).1 ((hWmem x).mp hx).2
  have hPeW : P.e ∈ W := (hWmem P.e).mpr ⟨P.polar_ee, by rw [polar_comm, h.ee]⟩
  have hReW : R.e ∈ W := (hWmem R.e).mpr ⟨h.ee, R.polar_ee⟩
  obtain ⟨μ, hμ⟩ := exists_eq_smul_of_mem_span_self hPeW hReW (linearIndependent_apply h) hspanW
  obtain ⟨w, hw1, hw2, hw3, hw4, hQw⟩ := exists_nonsingular_mem_axisPerp hQ h hV
  have hzw : z w = μ • w := hμ w ((hWmem w).mpr ⟨hw1, hw3⟩)
  have hμ2 : μ ^ 2 = 1 := by
    have h1 : μ ^ 2 * Q w = Q w := by rw [← map_smul_eq_sq, ← hzw, map_of_mem hz]
    exact mul_right_cancel₀ hQw (by simpa using h1)
  have hμ1 : μ = 1 := by
    have h : (μ - 1) * (μ + 1) = 0 := by
      have h3 : (μ - 1) * (μ + 1) = μ ^ 2 - 1 := by ring
      rw [h3, hμ2, sub_self]
    rcases mul_eq_zero.mp h with h1 | h1
    · exact sub_eq_zero.mp h1
    · rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h1
      exact h1
  intro v h1 h2
  have h := hμ v ((hWmem v).mpr ⟨h1, h2⟩)
  rw [hμ1, one_smul] at h
  exact h

private theorem exists_eichler_eq_of_mem_centralizer [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R)
    (hV : 6 ≤ finrank K V) {z : V ≃ₗ[K] V}
    (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hzc : z ∈ Subgroup.centralizer (axisRadical Q P.e R.e : Set (V ≃ₗ[K] V))) :
    ∃ c : K, z = eichler Q P.e (c • R.e) :=
  exists_eichler_eq_of_fixes_axisPerp hQ h hz (apply_eq_self_of_mem_centralizer hQ h hV hz hzc)

private theorem mem_centralizer_eichler_axis {P R : HypPair Q} (h : P.Orth R) (c : K) :
    eichler Q P.e (c • R.e) ∈
      Subgroup.centralizer (axisRadical Q P.e R.e : Set (V ≃ₗ[K] V)) := by
  rw [axisRadical, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro g ⟨u, w, hu, ha, hb, rfl⟩
  have hz' : eichler Q P.e (c • R.e) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    eichler_mem_orthogonalGroup Q _ _
  have hb' : eichler Q P.e (c • R.e) R.e = R.e := by
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [polar_comm, h.ee]
    · rw [polar_smul_right_eq, R.polar_ee, mul_zero]
  have hu' : eichler Q P.e (c • R.e) u = u := by
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
    rw [map_add, map_smul, map_smul, eichler_apply_self, hb']
  have hw' : eichler Q P.e (c • R.e) w = w := by
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [polar_comm, ha]
    · rw [polar_smul_right_eq, polar_comm, hb, mul_zero]
  have hcomm := eichler_conj hz' u w
  rw [hu', hw'] at hcomm
  have h2 := congrArg (· * eichler Q P.e (c • R.e)) hcomm
  simpa [mul_assoc] using h2.symm

theorem mem_centralizer_axisRadical_iff [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R) (hV : 6 ≤ finrank K V)
    {z : V ≃ₗ[K] V} (hz : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    z ∈ Subgroup.centralizer (axisRadical Q P.e R.e : Set (V ≃ₗ[K] V)) ↔
      ∃ c : K, z = eichler Q P.e (c • R.e) := by
  constructor
  · exact exists_eichler_eq_of_mem_centralizer hQ h hV hz
  · rintro ⟨c, rfl⟩
    exact mem_centralizer_eichler_axis h c

theorem eichler_smul_injective {P R : HypPair Q} (h : P.Orth R) :
    Function.Injective fun c : K => eichler Q P.e (c • R.e) := by
  have key : ∀ d : K, eichler Q P.e (d • R.e) P.f = P.f + d • R.e := fun d => by
    have hw : polar Q P.e (d • R.e) = 0 := by
      rw [QuadraticMap.polar_smul_right, h.ee, smul_zero]
    rw [eichler_apply P.Q_e hw]
    simp [QuadraticMap.polar_smul_right, h.fe, P.polar_fe, QuadraticMap.map_smul, R.Q_e]
  intro c c' hcc
  have hcc' : eichler Q P.e (c • R.e) = eichler Q P.e (c' • R.e) := hcc
  have h1 : eichler Q P.e (c • R.e) P.f = eichler Q P.e (c' • R.e) P.f := by rw [hcc']
  rw [key, key] at h1
  exact smul_left_injective K R.e_ne_zero (add_left_cancel h1)

theorem centralizer_axisRadical_inf_eq [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R) (hV : 6 ≤ finrank K V) :
    ((Subgroup.centralizer (axisRadical Q P.e R.e : Set (V ≃ₗ[K] V)) ⊓ elementaryGroup Q :
        Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) =
      Set.range fun c : K => eichler Q P.e (c • R.e) := by
  ext z
  simp only [SetLike.mem_coe, Subgroup.mem_inf, Set.mem_range]
  constructor
  · rintro ⟨hzc, hzE⟩
    obtain ⟨c, rfl⟩ :=
      (mem_centralizer_axisRadical_iff hQ h hV (elementaryGroup_le_orthogonalGroup Q hzE)).1 hzc
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨(mem_centralizer_axisRadical_iff hQ h hV (eichler_mem_orthogonalGroup Q _ _)).2
      ⟨c, rfl⟩, eichler_mem_elementaryGroup Q _ _⟩

theorem card_centralizer_axisRadical_inf [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P R : HypPair Q} (h : P.Orth R) (hV : 6 ≤ finrank K V) :
    Nat.card ↥(Subgroup.centralizer (axisRadical Q P.e R.e : Set (V ≃ₗ[K] V)) ⊓
      elementaryGroup Q) = Nat.card K := by
  rw [← Nat.card_range_of_injective (eichler_smul_injective h),
    ← centralizer_axisRadical_inf_eq hQ h hV]
  rfl

end CFSG.ClassicalGroups.Orthogonal
