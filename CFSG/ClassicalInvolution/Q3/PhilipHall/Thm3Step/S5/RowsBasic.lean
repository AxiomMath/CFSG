module

public import Certificates.Data.S5Rows
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge Certificates.S5Rows

section Elementary

variable {G : Type*} [Group G]

theorem mem_commutator_of_threeCycle {i j y : G} (h₁ : y⁻¹ * i * y = j)
    (h₂ : y⁻¹ * j * y = i * j ∨ y⁻¹ * j * y = j * i) :
    i ∈ commutator G ∧ j ∈ commutator G := by
  have hc : ∀ a b : G, a⁻¹ * b⁻¹ * a * b ∈ commutator G := fun a b => by
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top a⁻¹) (Subgroup.mem_top b⁻¹)
    simpa [commutatorElement_def, commutator] using this
  have hij : i⁻¹ * j ∈ commutator G := by
    have := hc i y
    rw [← h₁]
    simpa [mul_assoc] using this
  have hjy : j⁻¹ * (y⁻¹ * j * y) ∈ commutator G := by
    have := hc j y
    simpa [mul_assoc] using this
  rcases h₂ with h | h
  · rw [h] at hjy
    have hji : j⁻¹ * i * j ∈ commutator G := by simpa [mul_assoc] using hjy
    have hi : i ∈ commutator G := by
      have := (commutator G).mul_mem hji (hc j i)
      have e : j⁻¹ * i * j * (j⁻¹ * i⁻¹ * j * i) = i := by group
      rwa [e] at this
    exact ⟨hi, by simpa using (commutator G).mul_mem hi hij⟩
  · rw [h] at hjy
    have hi : i ∈ commutator G := by simpa using hjy
    exact ⟨hi, by simpa using (commutator G).mul_mem hi hij⟩

theorem mem_commutator_of_conj_eq_mul {i j n : G}
    (h : n⁻¹ * j * n = j * i ∨ n⁻¹ * j * n = j * i⁻¹) : i ∈ commutator G := by
  have hc : j⁻¹ * (n⁻¹ * j * n) ∈ commutator G := by
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top j⁻¹) (Subgroup.mem_top n⁻¹)
    simpa [commutatorElement_def, commutator, mul_assoc] using this
  rcases h with h | h <;> rw [h] at hc
  · simpa using hc
  · simpa using (commutator G).inv_mem (by simpa using hc)

theorem false_of_lift_squares {T : Subgroup G} {t u x : G} (ht : t ∈ Subgroup.center G)
    (htT : t ∉ T) (hu : u ∈ Subgroup.normalizer (T : Set G)) (hx : x ∈ T)
    (h : (u * u = 1 ∧ (u * x) * (u * x) = t) ∨ (u * u = t ∧ (u * x) * (u * x) = 1)) :
    False := by
  have hux : u * x * u⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hu x).mp hx
  have hy : u * x * u⁻¹ * x ∈ T := T.mul_mem hux hx
  have key : (u * x) * (u * x) = (u * x * u⁻¹) * (u * u) * x := by group
  have hc := Subgroup.mem_center_iff.mp ht
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · apply htT
    rw [← h2, key, h1, mul_one]
    exact hy
  · have e : u * x * u⁻¹ * t * x = t * (u * x * u⁻¹ * x) := by
      rw [hc (u * x * u⁻¹)]
      simp only [mul_assoc]
    have h3 : t * (u * x * u⁻¹ * x) = 1 := by rw [← e, ← h1, ← key, h2]
    exact htT (by rw [eq_inv_of_mul_eq_one_left h3]; exact T.inv_mem hy)

end Elementary

section Pairs

variable {M : Type*} [Group M]

@[expose] def Q8Rel (i j : M) : Prop :=
  i ^ 4 = 1 ∧ i ^ 2 ≠ 1 ∧ i ^ 2 = j ^ 2 ∧ j⁻¹ * i * j = i⁻¹

instance [DecidableEq M] (i j : M) : Decidable (Q8Rel i j) := by
  unfold Q8Rel
  infer_instance

theorem q8RelB_eq_true_iff [DecidableEq M] {i j : M} : q8RelB i j = true ↔ Q8Rel i j := by
  simp [q8RelB, Q8Rel, and_assoc]

theorem mem_of_mem_q8Span {H : Subgroup M} {i j x : M} (hi : i ∈ H) (hj : j ∈ H)
    (hx : x ∈ q8Span i j) : x ∈ H := by
  simp only [q8Span, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact H.one_mem
  · exact H.pow_mem hi 2
  · exact hi
  · exact H.inv_mem hi
  · exact hj
  · exact H.inv_mem hj
  · exact H.mul_mem hi hj
  · exact H.mul_mem hj hi

variable {N : Type*} [Group N]

theorem map_q8Span (f : M →* N) (i j : M) : (q8Span i j).map f = q8Span (f i) (f j) := by
  simp [q8Span, map_pow, map_inv, map_mul]

theorem mem_q8Span_map (f : M →* N) {i j x : M} (hx : x ∈ q8Span i j) :
    f x ∈ q8Span (f i) (f j) := by
  rw [← map_q8Span]
  exact List.mem_map_of_mem hx

theorem exists_of_mem_q8Span_map (f : M →* N) {i j : M} {y : N}
    (hy : y ∈ q8Span (f i) (f j)) : ∃ x ∈ q8Span i j, f x = y := by
  rw [← map_q8Span] at hy
  exact List.mem_map.mp hy

theorem Q8Rel.map (f : M →* N) {i j : M} (h : Q8Rel i j) (hf : f (i ^ 2) ≠ 1) :
    Q8Rel (f i) (f j) :=
  ⟨by rw [← map_pow, h.1, map_one], by rwa [← map_pow], by rw [← map_pow, ← map_pow, h.2.2.1],
    by rw [← map_inv, ← map_mul, ← map_mul, h.2.2.2, map_inv]⟩

theorem q8Pair_of_mulEquiv {G : Type*} [Group G] {T : Subgroup G} (e : ↥T ≃* QuaternionGroup 2)
    {u v : QuaternionGroup 2} (huv : Q8Rel u v) (hspan : ∀ w, w ∈ q8Span u v) :
    Q8Rel ((e.symm u : T) : G) (e.symm v : T) ∧
      ∀ t ∈ T, t ∈ q8Span ((e.symm u : T) : G) (e.symm v : T) := by
  set f : QuaternionGroup 2 →* G := T.subtype.comp e.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  refine ⟨huv.map f fun h1 => huv.2.1 (hf (by rw [h1, map_one])), fun t ht => ?_⟩
  have h1 := mem_q8Span_map f (hspan (e ⟨t, ht⟩))
  have h2 : f (e ⟨t, ht⟩) = t := by simp [hfdef]
  rwa [h2] at h1

theorem q8_a_xa : Q8Rel (QuaternionGroup.a 1 : QuaternionGroup 2) (QuaternionGroup.xa 0) := by
  decide

theorem q8_span_a_xa : ∀ w : QuaternionGroup 2,
    w ∈ q8Span (QuaternionGroup.a 1 : QuaternionGroup 2) (QuaternionGroup.xa 0) := by
  decide

theorem q8_xa_a : Q8Rel (QuaternionGroup.xa 0 : QuaternionGroup 2) (QuaternionGroup.a 1) := by
  decide

theorem q8_span_xa_a : ∀ w : QuaternionGroup 2,
    w ∈ q8Span (QuaternionGroup.xa 0 : QuaternionGroup 2) (QuaternionGroup.a 1) := by
  decide

theorem q8_mul_xa : Q8Rel (QuaternionGroup.a 1 * QuaternionGroup.xa 0 : QuaternionGroup 2)
    (QuaternionGroup.xa 0) := by
  decide

theorem q8_span_mul_xa : ∀ w : QuaternionGroup 2,
    w ∈ q8Span (QuaternionGroup.a 1 * QuaternionGroup.xa 0 : QuaternionGroup 2)
      (QuaternionGroup.xa 0) := by
  decide

theorem exists_q8Pair {G : Type*} [Group G] {T : Subgroup G} (e : ↥T ≃* QuaternionGroup 2) :
    ∃ i ∈ T, ∃ j ∈ T, Q8Rel i j ∧ ∀ t ∈ T, t ∈ q8Span i j := by
  obtain ⟨h1, h2⟩ := q8Pair_of_mulEquiv e q8_a_xa q8_span_a_xa
  exact ⟨_, (e.symm _).2, _, (e.symm _).2, h1, h2⟩

theorem exists_q8Pair_of_index_two {G : Type*} [Group G] {T : Subgroup G}
    (e : ↥T ≃* QuaternionGroup 2) {p : G → Prop}
    (hp : ∀ x ∈ T, ∀ y ∈ T, (p (x * y) ↔ (p x ↔ p y))) (hout : ∃ t ∈ T, ¬ p t) :
    ∃ i ∈ T, ∃ j ∈ T, Q8Rel i j ∧ (∀ t ∈ T, t ∈ q8Span i j) ∧ p i ∧ ¬ p j := by
  set a : G := ((e.symm (QuaternionGroup.a 1) : T) : G) with ha
  set b : G := ((e.symm (QuaternionGroup.xa 0) : T) : G) with hb
  have haT : a ∈ T := (e.symm _).2
  have hbT : b ∈ T := (e.symm _).2
  have hp1 : p 1 := by
    have := hp 1 T.one_mem 1 T.one_mem
    rw [one_mul] at this
    exact this.mpr Iff.rfl
  have hpinv : ∀ x ∈ T, p x → p x⁻¹ := fun x hx hpx => by
    have := hp x hx x⁻¹ (T.inv_mem hx)
    rw [mul_inv_cancel] at this
    exact (this.mp hp1).mp hpx
  by_cases hpa : p a <;> by_cases hpb : p b
  · exfalso
    obtain ⟨t, ht, hpt⟩ := hout
    have hspan := (q8Pair_of_mulEquiv e q8_a_xa q8_span_a_xa).2 t ht
    rw [← ha, ← hb] at hspan
    simp only [q8Span, List.mem_cons, List.not_mem_nil, or_false] at hspan
    have hmul : ∀ x ∈ T, ∀ y ∈ T, p x → p y → p (x * y) := fun x hx y hy hx' hy' =>
      (hp x hx y hy).mpr (iff_of_true hx' hy')
    rcases hspan with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hpt hp1
    · exact hpt (by rw [sq]; exact hmul a haT a haT hpa hpa)
    · exact hpt hpa
    · exact hpt (hpinv a haT hpa)
    · exact hpt hpb
    · exact hpt (hpinv b hbT hpb)
    · exact hpt (hmul a haT b hbT hpa hpb)
    · exact hpt (hmul b hbT a haT hpb hpa)
  · obtain ⟨h1, h2⟩ := q8Pair_of_mulEquiv e q8_a_xa q8_span_a_xa
    exact ⟨a, haT, b, hbT, h1, h2, hpa, hpb⟩
  · obtain ⟨h1, h2⟩ := q8Pair_of_mulEquiv e q8_xa_a q8_span_xa_a
    exact ⟨b, hbT, a, haT, h1, h2, hpb, hpa⟩
  · obtain ⟨h1, h2⟩ := q8Pair_of_mulEquiv e q8_mul_xa q8_span_mul_xa
    have hab : ((e.symm (QuaternionGroup.a 1 * QuaternionGroup.xa 0) : T) : G) = a * b := by
      rw [map_mul, Subgroup.coe_mul]
    rw [hab] at h1 h2
    refine ⟨a * b, T.mul_mem haT hbT, b, hbT, h1, h2, ?_, hpb⟩
    exact (hp a haT b hbT).mpr (iff_of_false hpa hpb)

end Pairs

section Sound

variable {M : Type*} [Group M] [DecidableEq M]

theorem threeCycCheck_sound {L Y : List M} {p : M → Bool} (h : threeCycCheck L Y p = true)
    {i j : M} (hi : i ∈ L) (hj : j ∈ L) (hpi : p i = true) (hpj : p j = true)
    (hij : Q8Rel i j) :
    ∃ y ∈ Y, y⁻¹ * i * y = j ∧ (y⁻¹ * j * y = i * j ∨ y⁻¹ * j * y = j * i) := by
  simp only [threeCycCheck, List.all_eq_true] at h
  have h1 := h i hi j hj
  simp only [q8RelB_eq_true_iff.mpr hij, hpi, hpj, Bool.and_self, Bool.not_true,
    Bool.false_or, List.any_eq_true, threeCycB, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h1
  exact h1

theorem conjMulCheck_sound {L Y : List M} {p : M → Bool} (h : conjMulCheck L Y p = true)
    {i j : M} (hi : i ∈ L) (hj : j ∈ L) (hpi : p i = true) (hpj : p j = false)
    (hij : Q8Rel i j) :
    ∃ n ∈ Y, n⁻¹ * i * n ∈ q8Span i j ∧ (n⁻¹ * j * n = j * i ∨ n⁻¹ * j * n = j * i⁻¹) := by
  simp only [conjMulCheck, List.all_eq_true] at h
  have h1 := h i hi j hj
  simp only [q8RelB_eq_true_iff.mpr hij, hpi, hpj, Bool.and_self, Bool.not_false,
    Bool.and_true, Bool.not_true, Bool.false_or, List.any_eq_true, conjMulB, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at h1
  exact h1

theorem uniqueOuterCheck_sound {L : List M} {p : M → Bool} (h : uniqueOuterCheck L p = true)
    {i j i' j' : M} (hi : i ∈ L) (hj : j ∈ L) (hi' : i' ∈ L) (hj' : j' ∈ L) (hij : Q8Rel i j)
    (hij' : Q8Rel i' j') (hp : (p i && p j) = false) (hp' : (p i' && p j') = false) :
    i ∈ q8Span i' j' ∧ j ∈ q8Span i' j' := by
  have hmem : ∀ {a b : M}, a ∈ L → b ∈ L → Q8Rel a b → (p a && p b) = false →
      (a, b) ∈ outerPairs L p := fun {a b} ha hb hab hpab => by
    simp only [outerPairs, List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq]
    exact ⟨a, ha, b, ⟨hb, by simp [q8RelB_eq_true_iff.mpr hab, hpab]⟩, rfl, rfl⟩
  simp only [uniqueOuterCheck, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h _ (hmem hi hj hij hp) _ (hmem hi' hj' hij' hp')

theorem invPairCheck_sound {L : List M} {f : M → ℕ} (h : invPairCheck L f = true) {i j : M}
    (hi : i ∈ L) (hj : j ∈ L) (hij : Q8Rel i j) :
    ∃ u ∈ L, ∃ x ∈ q8Span i j, u * u = 1 ∧ u ≠ 1 ∧ u⁻¹ * i * u ∈ q8Span i j ∧
      u⁻¹ * j * u ∈ q8Span i j ∧ u * x * (u * x) = 1 ∧ u * x ≠ 1 ∧ f u ≠ f (u * x) := by
  simp only [invPairCheck, List.all_eq_true] at h
  have h1 := h i hi j hj
  simp only [q8RelB_eq_true_iff.mpr hij, Bool.not_true, Bool.false_or, List.any_eq_true,
    invPairB, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
    and_assoc] at h1
  exact h1

end Sound

section Rho

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {K Q : Subgroup G}
  {X : Type*} [Group X] {ρ : G →* X}

theorem S5Hyp.eq_of_rho (h : S5Hyp Φ K Q) (hker : ρ.ker = Q) {T : Subgroup G}
    (hT : T ∈ RSet Φ) {a b : G} (ha : a ∈ T) (hb : b ∈ T) (hab : ρ a = ρ b) : a = b := by
  have h1 : a⁻¹ * b ∈ T ⊓ Q := Subgroup.mem_inf.mpr ⟨T.mul_mem (T.inv_mem ha) hb, by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]⟩
  rw [h.inf_eq_bot_RSet hT, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp h1

theorem S5Hyp.eq_of_map_rho_le (h : S5Hyp Φ K Q) (hker : ρ.ker = Q) {T T' : Subgroup G}
    (hT : T ∈ RSet Φ) (hT' : T' ∈ RSet Φ) (hle : T.map ρ ≤ T'.map ρ) : T = T' := by
  rw [Subgroup.map_le_map_iff, hker] at hle
  exact h.eq_of_le_sup_RSet hT hT' hle

theorem S5Hyp.exists_lift_normalizer (h : S5Hyp Φ K Q) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Q) {T : Subgroup G} (hT : T ∈ RSet Φ) {i j : G} (hi : i ∈ T) (hj : j ∈ T)
    (hspan : ∀ t ∈ T, t ∈ q8Span i j) {y : X} (hyi : y⁻¹ * ρ i * y ∈ T.map ρ)
    (hyj : y⁻¹ * ρ j * y ∈ T.map ρ) :
    ∃ y₀ : G, ρ y₀ = y ∧ (∀ t ∈ T, y₀⁻¹ * t * y₀ ∈ T) ∧
      y₀ ∈ Subgroup.normalizer (T : Set G) := by
  obtain ⟨y₀, rfl⟩ := hρ y
  set c : X →* X := (MulAut.conj (ρ y₀)⁻¹).toMonoidHom with hc
  have hcx : ∀ x : X, c x = (ρ y₀)⁻¹ * x * ρ y₀ := fun x => by
    simp [hc, MulAut.conj_apply]
  have hT' : conjSub y₀⁻¹ T ∈ RSet Φ := h.conjSub_mem_RSet hT y₀⁻¹
  have hmem : ∀ t ∈ T, y₀⁻¹ * t * y₀ ∈ conjSub y₀⁻¹ T := fun t ht =>
    ⟨t, ht, by simp [MulAut.conj_apply]⟩
  have hle : (conjSub y₀⁻¹ T).map ρ ≤ T.map ρ := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have h1 : ρ ((MulAut.conj y₀⁻¹).toMonoidHom t) = c (ρ t) := by
      simp [hcx, MulAut.conj_apply]
    rw [h1]
    have h2 := mem_q8Span_map (c.comp ρ) (hspan t ht)
    simp only [MonoidHom.comp_apply] at h2
    refine mem_of_mem_q8Span ?_ ?_ h2
    · rw [hcx]
      exact hyi
    · rw [hcx]
      exact hyj
  have heq := h.eq_of_map_rho_le hker hT' hT hle
  refine ⟨y₀, rfl, fun t ht => heq ▸ hmem t ht, ?_⟩
  have h3 : y₀⁻¹ ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_iff_conjSub_eq.mpr heq
  simpa using (Subgroup.normalizer (T : Set G)).inv_mem h3

theorem S5Hyp.le_commutator_of_threeCycle (h : S5Hyp Φ K Q) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Q) {T : Subgroup G} (hT : T ∈ RSet Φ) {i j : G} (hi : i ∈ T) (hj : j ∈ T)
    (hspan : ∀ t ∈ T, t ∈ q8Span i j) {y : X} (h₁ : y⁻¹ * ρ i * y = ρ j)
    (h₂ : y⁻¹ * ρ j * y = ρ i * ρ j ∨ y⁻¹ * ρ j * y = ρ j * ρ i) : T ≤ commutator G := by
  have hTi : ρ i ∈ T.map ρ := Subgroup.mem_map_of_mem ρ hi
  have hTj : ρ j ∈ T.map ρ := Subgroup.mem_map_of_mem ρ hj
  have hyj : y⁻¹ * ρ j * y ∈ T.map ρ := by
    rcases h₂ with h₂ | h₂ <;> rw [h₂]
    · exact (T.map ρ).mul_mem hTi hTj
    · exact (T.map ρ).mul_mem hTj hTi
  obtain ⟨y₀, rfl, hy₀, -⟩ :=
    h.exists_lift_normalizer hρ hker hT hi hj hspan (h₁ ▸ hTj) hyj
  have e₁ : y₀⁻¹ * i * y₀ = j :=
    h.eq_of_rho hker hT (hy₀ i hi) hj (by simp only [map_mul, map_inv]; exact h₁)
  have e₂ : y₀⁻¹ * j * y₀ = i * j ∨ y₀⁻¹ * j * y₀ = j * i := by
    rcases h₂ with h₂ | h₂
    · exact Or.inl (h.eq_of_rho hker hT (hy₀ j hj) (T.mul_mem hi hj)
        (by simp only [map_mul, map_inv]; exact h₂))
    · exact Or.inr (h.eq_of_rho hker hT (hy₀ j hj) (T.mul_mem hj hi)
        (by simp only [map_mul, map_inv]; exact h₂))
  obtain ⟨hic, hjc⟩ := mem_commutator_of_threeCycle e₁ e₂
  exact fun t ht => mem_of_mem_q8Span hic hjc (hspan t ht)

theorem S5Hyp.mem_commutator_of_conjMul (h : S5Hyp Φ K Q) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Q) {T : Subgroup G} (hT : T ∈ RSet Φ) {i j : G} (hi : i ∈ T) (hj : j ∈ T)
    (hspan : ∀ t ∈ T, t ∈ q8Span i j) {n : X} (hni : n⁻¹ * ρ i * n ∈ T.map ρ)
    (hnj : n⁻¹ * ρ j * n = ρ j * ρ i ∨ n⁻¹ * ρ j * n = ρ j * (ρ i)⁻¹) :
    i ∈ commutator G := by
  have hTi : ρ i ∈ T.map ρ := Subgroup.mem_map_of_mem ρ hi
  have hTj : ρ j ∈ T.map ρ := Subgroup.mem_map_of_mem ρ hj
  have hnj' : n⁻¹ * ρ j * n ∈ T.map ρ := by
    rcases hnj with h₂ | h₂ <;> rw [h₂]
    · exact (T.map ρ).mul_mem hTj hTi
    · exact (T.map ρ).mul_mem hTj ((T.map ρ).inv_mem hTi)
  obtain ⟨n₀, rfl, hn₀, -⟩ := h.exists_lift_normalizer hρ hker hT hi hj hspan hni hnj'
  refine mem_commutator_of_conj_eq_mul (n := n₀) (j := j) ?_
  rcases hnj with h₂ | h₂
  · exact Or.inl (h.eq_of_rho hker hT (hn₀ j hj) (T.mul_mem hj hi)
      (by simp only [map_mul, map_inv]; exact h₂))
  · exact Or.inr (h.eq_of_rho hker hT (hn₀ j hj) (T.mul_mem hj (T.inv_mem hi))
      (by simp only [map_mul, map_inv]; exact h₂))

theorem S5Hyp.commutator_eq_top (h : S5Hyp Φ K Q) (hall : ∀ T ∈ RSet Φ, T ≤ commutator G) :
    commutator G = ⊤ := by
  rw [eq_top_iff, ← h.iSup_RSet_eq_top]
  exact iSup₂_le hall

theorem S5Hyp.exists_mem_RSet (h : S5Hyp Φ K Q) : ∃ T, T ∈ RSet Φ := by
  obtain ⟨T, hT, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := K) IsPGroup.of_bot bot_le
  exact ⟨T, mem_RSet_of_isSylow2In h.mem hT⟩

theorem S5Hyp.nonempty_q8 (h : S5Hyp Φ K Q) {T : Subgroup G} (hT : T ∈ RSet Φ) :
    Nonempty (↥T ≃* QuaternionGroup 2) := by
  obtain ⟨J, hJ, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT
  exact h.typeR.sylow J hJ T hTJ

theorem isPGroup_two_of_mem_RSet {T : Subgroup G} (hT : T ∈ RSet Φ) : IsPGroup 2 T := by
  obtain ⟨J, -, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT
  exact hTJ.2.1

end Rho

section Model

theorem exists_conj_mem_of_isPGroup {M : Type*} [Group M] [Finite M] {P : Subgroup M}
    (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) {H : Subgroup M} (hH : IsPGroup 2 H) :
    ∃ g : M, ∀ x ∈ H, g⁻¹ * x * g ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M (hP.toSylow hidx) S'
  refine ⟨g, fun x hx => ?_⟩
  have hxS : x ∈ (S' : Subgroup M) := hS' hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxS
  obtain ⟨s, hs, rfl⟩ := hxS
  rw [IsPGroup.toSylow_coe] at hs
  rw [MulAut.smul_def, MulAut.conj_apply]
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hs

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {K Q : Subgroup G}
  {X : Type*} [Group X] {ρ : G →* X} {M : Type*} [Group M]

theorem S5Hyp.exists_model_pair (h : S5Hyp Φ K Q) (hker : ρ.ker = Q) (θ : X →* M)
    (hθ : Function.Injective θ) (P : Subgroup M)
    (hP : ∀ H : Subgroup M, IsPGroup 2 H → ∃ g : M, ∀ x ∈ H, g⁻¹ * x * g ∈ P)
    {T : Subgroup G} (hT : T ∈ RSet Φ) {i j : G} (hi : i ∈ T) (hij : Q8Rel i j) :
    ∃ g : M, (∀ t ∈ T, g⁻¹ * θ (ρ t) * g ∈ P) ∧
      Q8Rel (g⁻¹ * θ (ρ i) * g) (g⁻¹ * θ (ρ j) * g) := by
  have h2 : IsPGroup 2 (T.map (θ.comp ρ)) := (isPGroup_two_of_mem_RSet hT).map _
  obtain ⟨g, hg⟩ := hP _ h2
  refine ⟨g, fun t ht => hg _ (Subgroup.mem_map_of_mem _ ht), ?_⟩
  set φ : G →* M := (MulAut.conj g⁻¹).toMonoidHom.comp (θ.comp ρ) with hφ
  have hφx : ∀ x : G, φ x = g⁻¹ * θ (ρ x) * g := fun x => by
    simp [hφ, MulAut.conj_apply]
  have hne : φ (i ^ 2) ≠ 1 := by
    intro h1
    rw [hφx] at h1
    have h3 : θ (ρ (i ^ 2)) = 1 := by
      have : g * (g⁻¹ * θ (ρ (i ^ 2)) * g) * g⁻¹ = 1 := by rw [h1]; group
      simpa [mul_assoc] using this
    have h4 : ρ (i ^ 2) = ρ 1 := hθ (by rw [h3, map_one, map_one])
    exact hij.2.1 (h.eq_of_rho hker hT (T.pow_mem hi 2) T.one_mem h4)
  have key := hij.map φ hne
  rwa [hφx, hφx] at key

theorem S5Hyp.le_commutator_of_model (h : S5Hyp Φ K Q) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = Q) (θ : X ≃* M) (P : Subgroup M)
    (hP : ∀ H : Subgroup M, IsPGroup 2 H → ∃ g : M, ∀ x ∈ H, g⁻¹ * x * g ∈ P)
    (I : Subgroup M) [I.Normal]
    (hchk : ∀ i ∈ P, ∀ j ∈ P, i ∈ I → j ∈ I → Q8Rel i j →
      ∃ y : M, y⁻¹ * i * y = j ∧ (y⁻¹ * j * y = i * j ∨ y⁻¹ * j * y = j * i))
    {T : Subgroup G} (hT : T ∈ RSet Φ) (hTI : ∀ t ∈ T, θ (ρ t) ∈ I) : T ≤ commutator G := by
  obtain ⟨e⟩ := h.nonempty_q8 hT
  obtain ⟨i, hi, j, hj, hij, hspan⟩ := exists_q8Pair e
  obtain ⟨g, hgP, hq⟩ := h.exists_model_pair hker θ.toMonoidHom θ.injective P hP hT hi hij
  simp only [MulEquiv.coe_toMonoidHom] at hgP hq
  have hIc : ∀ x ∈ I, g⁻¹ * x * g ∈ I := fun x hx => by
    simpa using (inferInstance : I.Normal).conj_mem x hx g⁻¹
  obtain ⟨y, h₁, h₂⟩ := hchk _ (hgP i hi) _ (hgP j hj) (hIc _ (hTI i hi)) (hIc _ (hTI j hj)) hq
  set z : X := θ.symm (g * y * g⁻¹) with hz
  have hθz : θ z = g * y * g⁻¹ := by rw [hz, MulEquiv.apply_symm_apply]
  have hrel : ∀ a b : G, (y⁻¹ * (g⁻¹ * θ (ρ a) * g) * y = g⁻¹ * θ (ρ b) * g) →
      z⁻¹ * ρ a * z = ρ b := fun a b hab => by
    apply θ.injective
    rw [map_mul, map_mul, map_inv, hθz]
    calc (g * y * g⁻¹)⁻¹ * θ (ρ a) * (g * y * g⁻¹)
        = g * (y⁻¹ * (g⁻¹ * θ (ρ a) * g) * y) * g⁻¹ := by group
      _ = g * (g⁻¹ * θ (ρ b) * g) * g⁻¹ := by rw [hab]
      _ = θ (ρ b) := by group
  refine h.le_commutator_of_threeCycle hρ hker hT hi hj hspan (y := z) (hrel i j h₁) ?_
  rcases h₂ with h₂ | h₂
  · left
    rw [← map_mul]
    refine hrel j (i * j) ?_
    rw [h₂]
    simp only [map_mul]
    group
  · right
    rw [← map_mul]
    refine hrel j (j * i) ?_
    rw [h₂]
    simp only [map_mul]
    group

end Model

section Index

theorem commutator_eq_top_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (h : commutator G = ⊤) : commutator H = ⊤ := by
  have h1 := Subgroup.map_commutator (⊤ : Subgroup G) ⊤ f
  rw [Subgroup.map_top_of_surjective f hf] at h1
  have h2 : (⁅(⊤ : Subgroup G), ⊤⁆ : Subgroup G) = ⊤ := h
  rw [h2, Subgroup.map_top_of_surjective f hf] at h1
  exact h1.symm

theorem exists_index_two_of_isPGroup {Q : Type*} [Group Q] [Finite Q] (hQ2 : IsPGroup 2 Q)
    [Nontrivial Q] : ∃ H : Subgroup Q, H.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card (α := Q)).ne' hn
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := Q) 2 (n := n - 1)
    (by rw [hn]; exact pow_dvd_pow 2 (Nat.sub_le n 1))
  refine ⟨H, ?_⟩
  have h1 := Subgroup.card_mul_index H
  rw [hH, hn] at h1
  have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)]
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h1

end Index

section Small

variable {Y : Type} [Group Y]

noncomputable def secQuotTopEquiv' [Finite Y] (hO : classicalInvolutionOddCore Y = ⊥) :
    Y ≃* FrameAEmptyPf.SecQuot (⊤ : Subgroup Y) :=
  MulEquiv.ofBijective ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(⊤ : Subgroup Y))).comp
    Subgroup.topEquiv.symm.toMonoidHom) (by
      have hO' : classicalInvolutionOddCore ↥(⊤ : Subgroup Y) = ⊥ :=
        TL4.oddCore_eq_bot_of_normal hO inferInstance
      refine ⟨fun x y hxy => ?_, fun q => ?_⟩
      · have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(⊤ : Subgroup Y)))
            (Subgroup.topEquiv.symm x) = QuotientGroup.mk' _ (Subgroup.topEquiv.symm y) := hxy
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hO',
          Subgroup.mem_bot, inv_mul_eq_one] at h1
        exact Subgroup.topEquiv.symm.injective h1
      · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
        exact ⟨Subgroup.topEquiv x, rfl⟩)

theorem noNormalTwo_of_mulEquiv {Y' : Type} [Group Y'] (e : Y ≃* Y') (h : NoNormalTwo Y) :
    NoNormalTwo Y' := by
  intro P hP hP2
  have hc : (P.comap e.toMonoidHom).Normal := hP.comap _
  have hc2 : IsPGroup 2 (P.comap e.toMonoidHom) :=
    hP2.comap_of_injective e.toMonoidHom e.injective
  have h1 := h _ hc hc2
  rw [eq_bot_iff]
  intro x hx
  have hmem : e.symm x ∈ P.comap e.toMonoidHom := by
    simpa [Subgroup.mem_comap] using hx
  rw [h1, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  simpa using congrArg e hmem

theorem not_isL3E8_of_noNormalTwo (h : NoNormalTwo Y) : ¬ IsL3E8 Y := by
  rintro ⟨E, hE, -, hcard, -⟩
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  have := h E hE hE2
  rw [this, Subgroup.card_bot] at hcard
  exact absurd hcard (by norm_num)

theorem dihedral_r3_mem_center : (DihedralGroup.r 3 : DihedralGroup 6) ∈
    Subgroup.center (DihedralGroup 6) := by
  rw [Subgroup.mem_center_iff]
  decide

theorem not_noNormalTwo_dihedral : ¬ NoNormalTwo (DihedralGroup 6) := by
  intro h
  have hle : Subgroup.zpowers (DihedralGroup.r 3 : DihedralGroup 6) ≤
      Subgroup.center (DihedralGroup 6) :=
    Subgroup.zpowers_le.mpr dihedral_r3_mem_center
  have hN := Subgroup.normal_of_le_center hle
  have h2 : IsPGroup 2 (Subgroup.zpowers (DihedralGroup.r 3 : DihedralGroup 6)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, DihedralGroup.orderOf_r]; decide)
  have h3 := h _ hN h2
  have h4 : (DihedralGroup.r 3 : DihedralGroup 6) ∈ Subgroup.zpowers (DihedralGroup.r 3) :=
    Subgroup.mem_zpowers _
  rw [h3, Subgroup.mem_bot] at h4
  exact absurd h4 (by decide)

theorem not_thm3RowW_top [Finite Y] (hO : classicalInvolutionOddCore Y = ⊥) (h : NoNormalTwo Y)
    (Ω : Set (Subgroup Y)) : ¬ Thm3RowW Ω (⊤ : Subgroup Y) := by
  rintro ⟨W, hW, hWset, ⟨e⟩⟩
  haveI := hW
  have hS : NoNormalTwo (FrameAEmptyPf.SecQuot (⊤ : Subgroup Y)) :=
    noNormalTwo_of_mulEquiv (secQuotTopEquiv' hO) h
  have hWmem : W ∈ WSet (oddQuotientFamily (restrictFamily Ω ⊤)) := by
    rw [hWset]
    exact Set.mem_singleton W
  obtain ⟨η, ⟨S, hηS, -⟩, rfl⟩ := hWmem
  have hle : (⨆ U ∈ η, U) ≤ (S : Subgroup (FrameAEmptyPf.SecQuot (⊤ : Subgroup Y))) :=
    iSup₂_le fun U hU => (hηS.1 hU).2
  have hW2 : IsPGroup 2 (⨆ U ∈ η, U : Subgroup (FrameAEmptyPf.SecQuot (⊤ : Subgroup Y))) :=
    S.isPGroup'.to_le hle
  have hbot := hS _ hW hW2
  have e' : FrameAEmptyPf.SecQuot (⊤ : Subgroup Y) ≃* DihedralGroup 6 :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot).symm).trans e
  exact not_noNormalTwo_dihedral (noNormalTwo_of_mulEquiv e' hS)

end Small

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
