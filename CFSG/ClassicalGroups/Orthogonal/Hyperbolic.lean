module

public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] def PolarNondegOn (W : Submodule K V) : Prop :=
  ∀ x ∈ W, (∀ y ∈ W, polar Q x y = 0) → x = 0

theorem polarNondegOn_top (hQ : (polarBilin Q).Nondegenerate) : PolarNondegOn Q ⊤ :=
  fun _ _ hx => eq_zero_of_polar_eq_zero hQ fun y => hx y (Submodule.mem_top)

theorem PolarNondegOn.exists_polar_ne_zero {W : Submodule K V} (hW : PolarNondegOn Q W)
    {x : V} (hxW : x ∈ W) (hx : x ≠ 0) : ∃ y ∈ W, polar Q x y ≠ 0 := by
  by_contra! h
  exact hx (hW x hxW h)

@[expose] def HypPair.ofPolarEqOne {e h : V} (he : Q e = 0) (heh : polar Q e h = 1) : HypPair Q where
  e := e
  f := h - Q h • e
  Q_e := he
  Q_f := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, map_smul_eq_sq, he,
      polar_neg_right, polar_smul_right_eq, polar_comm, heh]
    ring
  polar_ef := by rw [polar_sub_right, polar_smul_right_eq, polar_self_eq_zero he, heh]; ring

@[simp] theorem HypPair.ofPolarEqOne_e {e h : V} (he : Q e = 0) (heh : polar Q e h = 1) :
    (HypPair.ofPolarEqOne he heh).e = e := rfl

@[simp] theorem HypPair.ofPolarEqOne_f {e h : V} (he : Q e = 0) (heh : polar Q e h = 1) :
    (HypPair.ofPolarEqOne he heh).f = h - Q h • e := rfl

theorem HypPair.polar_ofPolarEqOne_f {e h : V} (he : Q e = 0) (heh : polar Q e h = 1) {z : V}
    (hz : polar Q z e = 0) : polar Q z (HypPair.ofPolarEqOne he heh).f = polar Q z h := by
  rw [HypPair.ofPolarEqOne_f, polar_sub_right, polar_smul_right_eq, hz, mul_zero, sub_zero]

theorem exists_hypPair (hQ : (polarBilin Q).Nondegenerate) {e : V} (he : Q e = 0)
    (he0 : e ≠ 0) : ∃ P : HypPair Q, P.e = e := by
  obtain ⟨v, hv⟩ := exists_polar_ne_zero hQ he0
  have h1 : polar Q e ((polar Q e v)⁻¹ • v) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hv]
  exact ⟨HypPair.ofPolarEqOne he h1, rfl⟩

@[expose] def HypPair.perp (P : HypPair Q) : Submodule K V :=
  LinearMap.ker (polarBilin Q P.e) ⊓ LinearMap.ker (polarBilin Q P.f)

theorem HypPair.mem_perp {P : HypPair Q} {x : V} :
    x ∈ P.perp ↔ polar Q P.e x = 0 ∧ polar Q P.f x = 0 := by
  simp [HypPair.perp]

@[expose] def HypPair.proj (P : HypPair Q) (x : V) : V := x - polar Q x P.f • P.e - polar Q x P.e • P.f

theorem HypPair.proj_mem_perp (P : HypPair Q) (x : V) : P.proj x ∈ P.perp := by
  rw [HypPair.mem_perp, HypPair.proj]
  constructor
  · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_ee,
      P.polar_ef, polar_comm Q P.e x]
    ring
  · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, P.polar_fe,
      P.polar_ff, polar_comm Q P.f x]
    ring

theorem HypPair.eq_add_proj (P : HypPair Q) (x : V) :
    x = polar Q x P.f • P.e + polar Q x P.e • P.f + P.proj x := by
  rw [HypPair.proj]
  abel

theorem HypPair.polarNondegOn_perp (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q) :
    PolarNondegOn Q P.perp := by
  intro x hx hxW
  rw [HypPair.mem_perp] at hx
  apply eq_zero_of_polar_eq_zero hQ
  intro z
  rw [P.eq_add_proj z, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
    polar_comm Q x P.e, polar_comm Q x P.f, hx.1, hx.2, hxW _ (P.proj_mem_perp z)]
  ring

theorem PolarNondegOn.inf_perp {W : Submodule K V} (hW : PolarNondegOn Q W) (P : HypPair Q)
    (he : P.e ∈ W) (hf : P.f ∈ W) : PolarNondegOn Q (W ⊓ P.perp) := by
  intro x hx hxW
  rw [Submodule.mem_inf, HypPair.mem_perp] at hx
  apply hW x hx.1
  intro z hz
  have hpz : P.proj z ∈ W ⊓ P.perp := by
    refine ⟨?_, P.proj_mem_perp z⟩
    rw [HypPair.proj]
    exact W.sub_mem (W.sub_mem hz (W.smul_mem _ he)) (W.smul_mem _ hf)
  rw [P.eq_add_proj z, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
    polar_comm Q x P.e, polar_comm Q x P.f, hx.2.1, hx.2.2, hxW _ hpz]
  ring

theorem exists_dual_family [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    {t : Fin n → V} (ht : LinearIndependent K t) :
    ∃ g : Fin n → V, ∀ i j, polar Q (t i) (g j) = if i = j then 1 else 0 := by
  let φ : V →ₗ[K] (Fin n → K) := LinearMap.pi fun i => polarBilin Q (t i)
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro ℓ hℓ
    set a : Fin n → K := fun i => ℓ fun j => if i = j then 1 else 0
    have hsum : ∀ v, polar Q (∑ i, a i • t i) v = 0 := by
      intro v
      have h1 := LinearMap.congr_fun hℓ v
      rw [LinearMap.dualMap_apply, LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ] at h1
      rw [← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [φ, a, mul_comm]
    have ha : a = 0 := by
      funext i
      exact Fintype.linearIndependent_iff.mp ht a (eq_zero_of_polar_eq_zero hQ hsum) i
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : (ℓ fun j => if i = j then (1 : K) else 0) = a i := rfl
    rw [this, ha, Pi.zero_apply, smul_zero]
  choose g hg using fun j : Fin n => hφ fun i => if i = j then (1 : K) else 0
  refine ⟨g, fun i j => ?_⟩
  have := congrFun (hg j) i
  simpa [φ] using this

theorem exists_three_hypPairs_of_family [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {t : Fin 3 → V} (ht : LinearIndependent K t)
    (htQ : ∀ i, Q (t i) = 0) (htB : ∀ i j, polar Q (t i) (t j) = 0) :
    ∃ P₁ P₂ P₃ : HypPair Q, P₁.Orth P₂ ∧ P₁.Orth P₃ ∧ P₂.Orth P₃ := by
  obtain ⟨g, hg⟩ := exists_dual_family hQ ht
  have h00 : polar Q (t 0) (g 0) = 1 := by simpa using hg 0 0
  set P₁ := HypPair.ofPolarEqOne (htQ 0) h00 with hP₁
  have hB1 : ∀ i, polar Q (t i) P₁.f = polar Q (t i) (g 0) := fun i =>
    HypPair.polar_ofPolarEqOne_f (htQ 0) h00 (htB i 0)
  set h₁ := g 1 - polar Q (g 1) P₁.f • t 0 with hh₁
  have hth₁ : ∀ i, polar Q (t i) h₁ = polar Q (t i) (g 1) := fun i => by
    rw [hh₁, polar_sub_right, polar_smul_right_eq, htB, mul_zero, sub_zero]
  have h11 : polar Q (t 1) h₁ = 1 := by rw [hth₁]; simpa using hg 1 1
  set P₂ := HypPair.ofPolarEqOne (htQ 1) h11 with hP₂
  have hB2 : ∀ i, polar Q (t i) P₂.f = polar Q (t i) (g 1) := fun i => by
    rw [HypPair.polar_ofPolarEqOne_f (htQ 1) h11 (htB i 1), hth₁]
  set h₂ := g 2 - polar Q (g 2) P₁.f • t 0 - polar Q (g 2) P₂.f • t 1 with hh₂
  have hth₂ : ∀ i, polar Q (t i) h₂ = polar Q (t i) (g 2) := fun i => by
    rw [hh₂, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, htB, htB,
      mul_zero, mul_zero, sub_zero, sub_zero]
  have h22 : polar Q (t 2) h₂ = 1 := by rw [hth₂]; simpa using hg 2 2
  set P₃ := HypPair.ofPolarEqOne (htQ 2) h22 with hP₃
  have hB3 : ∀ i, polar Q (t i) P₃.f = polar Q (t i) (g 2) := fun i => by
    rw [HypPair.polar_ofPolarEqOne_f (htQ 2) h22 (htB i 2), hth₂]
  have hd : ∀ i j, i ≠ j → polar Q (t i) (g j) = 0 := fun i j hij => by
    simpa [hij] using hg i j
  have e1 : P₁.e = t 0 := rfl
  have e2 : P₂.e = t 1 := rfl
  have e3 : P₃.e = t 2 := rfl
  have f1t : ∀ i, i ≠ 0 → polar Q P₁.f (t i) = 0 := fun i hi => by
    rw [polar_comm, hB1, hd i 0 hi]
  have f2t : ∀ i, i ≠ 1 → polar Q P₂.f (t i) = 0 := fun i hi => by
    rw [polar_comm, hB2, hd i 1 hi]
  have f3t : ∀ i, i ≠ 2 → polar Q P₃.f (t i) = 0 := fun i hi => by
    rw [polar_comm, hB3, hd i 2 hi]
  have hP₁f : P₁.f = g 0 - Q (g 0) • t 0 := rfl
  have hf1t0 : polar Q P₁.f (t 0) = 1 := P₁.polar_fe
  have hf2t1 : polar Q P₂.f (t 1) = 1 := P₂.polar_fe
  have hP₂f : P₂.f = h₁ - Q h₁ • t 1 := rfl
  have hP₃f : P₃.f = h₂ - Q h₂ • t 2 := rfl
  have f12 : polar Q P₁.f P₂.f = 0 := by
    rw [hP₂f, polar_sub_right, polar_smul_right_eq, f1t 1 (by decide), mul_zero, sub_zero, hh₁,
      polar_sub_right, polar_smul_right_eq, hf1t0, polar_comm Q (g 1)]
    ring
  have f13 : polar Q P₁.f P₃.f = 0 := by
    rw [hP₃f, polar_sub_right, polar_smul_right_eq, f1t 2 (by decide), mul_zero, sub_zero, hh₂,
      polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hf1t0,
      f1t 1 (by decide), polar_comm Q (g 2)]
    ring
  have f23 : polar Q P₂.f P₃.f = 0 := by
    rw [hP₃f, polar_sub_right, polar_smul_right_eq, f2t 2 (by decide), mul_zero, sub_zero, hh₂,
      polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      f2t 0 (by decide), hf2t1, polar_comm Q (g 2) P₂.f]
    ring
  refine ⟨P₁, P₂, P₃, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [e1, e2, htB]
  · rw [e1, hB2, hd 0 1 (by decide)]
  · rw [e2, f1t 1 (by decide)]
  · exact f12
  · rw [e1, e3, htB]
  · rw [e1, hB3, hd 0 2 (by decide)]
  · rw [e3, f1t 2 (by decide)]
  · exact f13
  · rw [e2, e3, htB]
  · rw [e2, hB3, hd 1 2 (by decide)]
  · rw [e3, f2t 2 (by decide)]
  · exact f23

theorem exists_three_hypPairs [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {T : Submodule K V} (hT : 3 ≤ Module.finrank K T) (hTQ : ∀ x ∈ T, Q x = 0) :
    ∃ P₁ P₂ P₃ : HypPair Q, P₁.Orth P₂ ∧ P₁.Orth P₃ ∧ P₂.Orth P₃ := by
  let b := Module.finBasisOfFinrankEq K T rfl
  let t : Fin 3 → V := fun i => (b (Fin.castLE hT i) : V)
  have ht : LinearIndependent K t :=
    (b.linearIndependent.comp _ (Fin.castLE_injective hT)).map' T.subtype T.ker_subtype
  have hmem : ∀ i, t i ∈ T := fun i => (b (Fin.castLE hT i)).2
  refine exists_three_hypPairs_of_family hQ ht (fun i => hTQ _ (hmem i)) fun i j => ?_
  rw [polar, hTQ _ (T.add_mem (hmem i) (hmem j)), hTQ _ (hmem i), hTQ _ (hmem j), sub_zero,
    sub_zero]


theorem map_eq_zero_of_mem_span {S : Set V} (hS : ∀ u ∈ S, Q u = 0)
    (hB : ∀ u ∈ S, ∀ w ∈ S, polar Q u w = 0) {x : V} (hx : x ∈ Submodule.span K S) :
    Q x = 0 := by
  have step1 : ∀ y ∈ Submodule.span K S, ∀ w ∈ S, polar Q y w = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact fun w hw => hB y hy w hw
    | zero => exact fun w _ => polar_zero_left Q w
    | add y z _ _ hy hz => exact fun w hw => by rw [polar_add_left, hy w hw, hz w hw, add_zero]
    | smul a y _ hy => exact fun w hw => by rw [polar_smul_left_eq, hy w hw, mul_zero]
  have step2 : ∀ y ∈ Submodule.span K S, ∀ z ∈ Submodule.span K S, polar Q y z = 0 := by
    intro y hy z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact step1 y hy z hz
    | zero => exact polar_zero_right Q y
    | add z z' _ _ hz hz' => rw [polar_add_right, hz, hz', add_zero]
    | smul a z _ hz => rw [polar_smul_right_eq, hz, mul_zero]
  induction hx using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => exact QuadraticMap.map_zero Q
  | add y z hy hz ihy ihz => rw [QuadraticMap.map_add Q, ihy, ihz, step2 y hy z hz, add_zero, add_zero]
  | smul a y _ ihy => rw [map_smul_eq_sq, ihy, mul_zero]

theorem exists_totallySingular_of_hypPairs {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂)
    (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  set v : Fin 3 → V := ![P₁.e, P₂.e, P₃.e] with hv
  have he₂f₁ : polar Q P₂.e P₁.f = 0 := h₁₂.symm.ef
  have he₃f₁ : polar Q P₃.e P₁.f = 0 := h₁₃.symm.ef
  have he₁f₂ : polar Q P₁.e P₂.f = 0 := h₁₂.ef
  have he₃f₂ : polar Q P₃.e P₂.f = 0 := h₂₃.symm.ef
  have he₁f₃ : polar Q P₁.e P₃.f = 0 := h₁₃.ef
  have he₂f₃ : polar Q P₂.e P₃.f = 0 := h₂₃.ef
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    have h1 := congrArg (fun z => polar Q z P₁.f) hg
    have h2 := congrArg (fun z => polar Q z P₂.f) hg
    have h3 := congrArg (fun z => polar Q z P₃.f) hg
    simp only [hv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, polar_add_left, polar_smul_left_eq, polar_zero_left,
      P₁.polar_ef, P₂.polar_ef, P₃.polar_ef, he₂f₁, he₃f₁, he₁f₂, he₃f₂, he₁f₃, he₂f₃,
      mul_zero, mul_one, add_zero, zero_add] at h1 h2 h3
    intro i
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
  refine ⟨Submodule.span K (Set.range v), by rw [finrank_span_eq_card hli, Fintype.card_fin],
    fun x hx => map_eq_zero_of_mem_span ?_ ?_ hx⟩
  · rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact P₁.Q_e
    · exact P₂.Q_e
    · exact P₃.Q_e
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    fin_cases i <;> fin_cases j
    · exact P₁.polar_ee
    · exact h₁₂.ee
    · exact h₁₃.ee
    · exact h₁₂.symm.ee
    · exact P₂.polar_ee
    · exact h₂₃.ee
    · exact h₁₃.symm.ee
    · exact h₂₃.symm.ee
    · exact P₃.polar_ee

end CFSG.ClassicalGroups.Orthogonal
