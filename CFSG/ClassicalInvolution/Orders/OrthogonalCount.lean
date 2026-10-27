module

public import CFSG.Timmesfeld.Orders.ClassicalOrthogonal
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ClassicalInvolution

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Timmesfeld.ClassicalOrders Module

section Transitive

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem reflect_sub_apply_of_map_eq {x y : V} (hxy : Q x = Q y) (hne : Q (x - y) ≠ 0) :
    reflect Q (x - y) x = y := by
  let _ : Invertible (Q (x - y)) := invertibleOfNonzero hne
  rw [reflect_eq_reflection]
  exact TauCeti.QuadraticMap.reflection_sub_apply_eq_of_map_eq Q x y hxy

theorem map_sub_of_singular {x y : V} (hx : Q x = 0) (hy : Q y = 0) :
    Q (x - y) = - polar Q x y := by
  rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right, hx, hy]
  ring

theorem reflect_sub_apply_of_singular {x y : V} (hx : Q x = 0) (hy : Q y = 0)
    (hpol : polar Q x y ≠ 0) : reflect Q (x - y) x = y :=
  reflect_sub_apply_of_map_eq (hx.trans hy.symm)
    (by rw [map_sub_of_singular hx hy]; exact neg_ne_zero.mpr hpol)

theorem exists_singular_polar_ne_zero_of_nondegenerate (hQ : (polarBilin Q).Nondegenerate)
    {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hxy : polar Q x y = 0) : ∃ z, Q z = 0 ∧ polar Q x z ≠ 0 ∧ polar Q z y ≠ 0 := by
  obtain ⟨P, rfl⟩ := exists_hypPair hQ hx hx0
  obtain ⟨P', rfl⟩ := exists_hypPair hQ hy hy0
  by_cases h1 : polar Q P.f P'.e = 0
  · by_cases h3 : polar Q P.e P'.f = 0
    · refine ⟨P.f + P'.f - polar Q P.f P'.f • P.e, ?_, ?_, ?_⟩
      · rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_neg,
          map_smul_eq_sq, P.Q_f, P'.Q_f, P.Q_e, polar_neg_right, polar_smul_right_eq,
          polar_add_left, P.polar_fe, polar_comm Q P'.f P.e, h3]
        ring
      · rw [sub_eq_add_neg, polar_add_right, polar_add_right, polar_neg_right,
          polar_smul_right_eq, P.polar_ef, h3, polar_self_eq_zero P.Q_e]
        simp
      · rw [sub_eq_add_neg, polar_add_left, polar_add_left, polar_neg_left, polar_smul_left_eq,
          h1, P'.polar_fe, hxy]
        simp
    · exact ⟨P'.f, P'.Q_f, h3, by rw [P'.polar_fe]; exact one_ne_zero⟩
  · exact ⟨P.f, P.Q_f, by rw [P.polar_ef]; exact one_ne_zero, h1⟩

theorem exists_mem_orthogonalGroup_apply_eq_of_nondegenerate (hQ : (polarBilin Q).Nondegenerate)
    {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g x = y := by
  by_cases hxy : polar Q x y = 0
  · obtain ⟨z, hz, hxz, hzy⟩ :=
      exists_singular_polar_ne_zero_of_nondegenerate hQ hx hy hx0 hy0 hxy
    refine ⟨reflect Q (z - y) * reflect Q (x - z),
      mul_mem (reflect_mem_orthogonalGroup Q _) (reflect_mem_orthogonalGroup Q _), ?_⟩
    rw [LinearEquiv.mul_apply, reflect_sub_apply_of_singular hx hz hxz,
      reflect_sub_apply_of_singular hz hy hzy]
  · exact ⟨reflect Q (x - y), reflect_mem_orthogonalGroup Q _,
      reflect_sub_apply_of_singular hx hy hxy⟩

theorem exists_mem_orthogonalGroup_apply_pair_of_nondegenerate
    (hQ : (polarBilin Q).Nondegenerate) (P P' : HypPair Q) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g P.e = P'.e ∧ g P.f = P'.f := by
  obtain ⟨g, hg, hge⟩ :=
    exists_mem_orthogonalGroup_apply_eq_of_nondegenerate hQ P.Q_e P'.Q_e P.e_ne_zero
      P'.e_ne_zero
  have hQf : Q (g P.f) = Q P'.f := by rw [map_of_mem hg, P.Q_f, P'.Q_f]
  have hpol : polar Q P'.e (g P.f) = 1 := by rw [← hge, polar_map_of_mem hg, P.polar_ef]
  refine ⟨eichler Q P'.e ((1 : K)⁻¹ • (P'.f - g P.f)) * g,
    mul_mem (eichler_mem_orthogonalGroup Q _ _) hg, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hge, eichler_apply_self]
  · rw [LinearEquiv.mul_apply,
      eichler_apply_eq_of_polar_eq P'.Q_e hQf hpol P'.polar_ef one_ne_zero]

end Transitive

section HypSum

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {Q' : QuadraticForm K W}

theorem card_partners_hypSum (hQ' : (polarBilin Q').Nondegenerate)
    {x : (K × K) × W} (hx : hypSum Q' x = 0) (hx0 : x ≠ 0) :
    Nat.card {y : (K × K) × W // hypSum Q' y = 0 ∧ polar (hypSum Q') x y = 1} =
      Nat.card W := by
  obtain ⟨g, hg, hgx⟩ := exists_mem_orthogonalGroup_apply_eq_of_nondegenerate
    (nondegenerate_polarBilin_hypSum hQ') (hypPair Q').Q_e hx (hypPair Q').e_ne_zero hx0
  rw [← card_partners_hypPair_e Q']
  refine (Nat.card_congr (Equiv.subtypeEquiv g.toEquiv fun y => ?_)).symm
  change _ ↔ hypSum Q' (g y) = 0 ∧ polar (hypSum Q') x (g y) = 1
  rw [map_of_mem hg, ← hgx, polar_map_of_mem hg]
  rfl

variable [Finite K]

theorem card_hypPairs_hypSum [Finite W] (hQ' : (polarBilin Q').Nondegenerate) :
    Nat.card {p : ((K × K) × W) × ((K × K) × W) // hypSum Q' p.1 = 0 ∧ hypSum Q' p.2 = 0 ∧
      polar (hypSum Q') p.1 p.2 = 1} =
      (Nat.card {v : (K × K) × W // hypSum Q' v = 0} - 1) * Nat.card W := by
  classical
  have := Fintype.ofFinite K
  have := Fintype.ofFinite W
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun x y : (K × K) × W =>
    hypSum Q' x = 0 ∧ hypSum Q' y = 0 ∧ polar (hypSum Q') x y = 1), Nat.card_sigma]
  have hterm : ∀ x : (K × K) × W, Nat.card {y // hypSum Q' x = 0 ∧ hypSum Q' y = 0 ∧
      polar (hypSum Q') x y = 1} = if hypSum Q' x = 0 ∧ x ≠ 0 then Nat.card W else 0 := by
    intro x
    split_ifs with hx
    · rw [← card_partners_hypSum hQ' hx.1 hx.2]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [hx.1])
    · have : IsEmpty {y // hypSum Q' x = 0 ∧ hypSum Q' y = 0 ∧ polar (hypSum Q') x y = 1} := by
        refine ⟨fun y => hx ⟨y.2.1, fun h0 => ?_⟩⟩
        have h' := y.2.2.2
        subst h0
        rw [polar_zero_left] at h'
        exact zero_ne_one h'
      exact Nat.card_of_isEmpty
  rw [Fintype.sum_congr _ _ hterm, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
    add_zero, smul_eq_mul]
  congr 1
  rw [Nat.card_eq_fintype_card (α := {v : (K × K) × W // hypSum Q' v = 0}),
    Fintype.card_subtype]
  have hsplit : Finset.univ.filter (fun x : (K × K) × W => hypSum Q' x = 0) =
      insert 0 (Finset.univ.filter fun x : (K × K) × W => hypSum Q' x = 0 ∧ x ≠ 0) := by
    ext x
    by_cases hx : x = 0 <;> simp [hx]
  rw [hsplit, Finset.card_insert_of_notMem (by simp), Nat.add_sub_cancel]

theorem card_orthogonalGroup_hypSum_of_nondegenerate [Finite W]
    (hQ' : (polarBilin Q').Nondegenerate) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (hypSum Q')) =
      (Nat.card {v : (K × K) × W // hypSum Q' v = 0} - 1) * Nat.card W *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q') := by
  set O := TauCeti.QuadraticMap.orthogonalGroup (hypSum Q')
  have horbit : MulAction.orbit O ((hypPair Q').e, (hypPair Q').f) =
      {p | hypSum Q' p.1 = 0 ∧ hypSum Q' p.2 = 0 ∧ polar (hypSum Q') p.1 p.2 = 1} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨g, hg⟩
      rw [← hg]
      set g' : ((K × K) × W) ≃ₗ[K] ((K × K) × W) := ((g : O) : ((K × K) × W) ≃ₗ[K] ((K × K) × W))
      change hypSum Q' (g' (hypPair Q').e) = 0 ∧ hypSum Q' (g' (hypPair Q').f) = 0 ∧
        polar (hypSum Q') (g' (hypPair Q').e) (g' (hypPair Q').f) = 1
      rw [map_of_mem g.2, map_of_mem g.2, polar_map_of_mem g.2]
      exact ⟨(hypPair Q').Q_e, (hypPair Q').Q_f, (hypPair Q').polar_ef⟩
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨g, hg, hge, hgf⟩ := exists_mem_orthogonalGroup_apply_pair_of_nondegenerate
        (nondegenerate_polarBilin_hypSum hQ') (hypPair Q') ⟨x, y, hx, hy, hxy⟩
      exact ⟨⟨g, hg⟩, Prod.ext hge hgf⟩
  have hcard := (MulAction.stabilizer O ((hypPair Q').e, (hypPair Q').f)).card_mul_index
  rw [MulAction.index_stabilizer, horbit, ← Nat.card_coe_set_eq, card_stabilizer_hypPair] at hcard
  rw [← hcard, mul_comm]
  congr 1
  exact card_hypPairs_hypSum hQ'

section Congr

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem card_step_of_nondegenerate [Finite W] (e : Q.IsometryEquiv (hypSum Q'))
    (hQ' : (polarBilin Q').Nondegenerate) :
    Nat.card {v // Q v = 0} =
        Nat.card K * Nat.card {w // Q' w = 0} + (Nat.card K - 1) * Nat.card W ∧
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
        (Nat.card {v // Q v = 0} - 1) * Nat.card W *
          Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q') := by
  rw [card_singular_congr e, card_orthogonalGroup_congr e]
  exact ⟨card_singular_hypSum Q', card_orthogonalGroup_hypSum_of_nondegenerate hQ'⟩

end Congr

end HypSum

section OddSplit

variable (K : Type*) [Field K]

noncomputable def oddSplit (m : ℕ) :
    (Fin (m + 1) ⊕ Fin (m + 1) ⊕ Unit → K) ≃ₗ[K] (K × K) × (Fin m ⊕ Fin m ⊕ Unit → K) where
  toFun v := ((v (.inl 0), v (.inr (.inl 0))),
    fun s => v (Sum.map Fin.succ (Sum.map Fin.succ id) s))
  invFun p := Sum.elim (Fin.cons p.1.1 fun i => p.2 (.inl i))
    (Sum.elim (Fin.cons p.1.2 fun i => p.2 (.inr (.inl i))) fun k => p.2 (.inr (.inr k)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    funext s
    rcases s with i | i | k
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · rfl
  right_inv p := Prod.ext rfl (funext fun s => by rcases s with i | i | k <;> rfl)

noncomputable def oddIsometry (m : ℕ) :
    (quadOdd (m + 1) K).IsometryEquiv (hypSum (quadOdd m K)) :=
  { oddSplit K m with
    map_app' := fun (v : Fin (m + 1) ⊕ Fin (m + 1) ⊕ Unit → K) => by
      change hypSum (quadOdd m K) (oddSplit K m v) = quadOdd (m + 1) K v
      have hsum : ∑ i : Fin (m + 1), v (.inl i) * v (.inr (.inl i)) =
          v (.inl 0) * v (.inr (.inl 0)) + ∑ i : Fin m, v (.inl i.succ) * v (.inr (.inl i.succ)) :=
        Fin.sum_univ_succ _
      rw [hypSum_apply, quadOdd_apply, quadOdd_apply]
      change v (.inl 0) * v (.inr (.inl 0)) + (∑ i : Fin m, v (.inl i.succ) * v (.inr (.inl i.succ))
        + v (.inr (.inr ())) ^ 2) = ∑ i : Fin (m + 1), v (.inl i) * v (.inr (.inl i)) +
        v (.inr (.inr ())) ^ 2
      rw [hsum]
      ring }

end OddSplit

section Conic

variable {K : Type*} [Field K]

theorem conic_ne_zero_of_not_isSquare {δ : K} (hδ : ¬ IsSquare δ) (t : K) :
    δ * t ^ 2 - 1 ≠ 0 := by
  intro h
  have h1 : δ * t ^ 2 = 1 := sub_eq_zero.mp h
  have ht : t ≠ 0 := by
    rintro rfl
    simp at h1
  apply hδ
  refine ⟨t⁻¹, ?_⟩
  field_simp
  linear_combination h1

open scoped Classical in
noncomputable def conicEquiv (h4 : (4 : K) ≠ 0) {δ : K} (hδ : ¬ IsSquare δ) :
    K ⊕ Unit ≃ {p : K × K // p.1 ^ 2 - δ * p.2 ^ 2 = 4} where
  toFun := Sum.elim (fun t => ⟨(4 / (δ * t ^ 2 - 1) + 2, 4 / (δ * t ^ 2 - 1) * t), by
      have := conic_ne_zero_of_not_isSquare hδ t
      field_simp
      ring⟩) (fun _ => ⟨(2, 0), by ring⟩)
  invFun p := if p.1.1 = 2 then Sum.inr () else Sum.inl (p.1.2 / (p.1.1 - 2))
  left_inv := by
    rintro (t | ⟨⟩)
    · have hd := conic_ne_zero_of_not_isSquare hδ t
      have hs : 4 / (δ * t ^ 2 - 1) ≠ 0 := div_ne_zero h4 hd
      have h2 : 4 / (δ * t ^ 2 - 1) + 2 ≠ 2 := fun h => hs (by linear_combination h)
      simp only [Sum.elim_inl, h2, ite_false]
      congr 1
      rw [add_sub_cancel_right]
      field_simp
    · simp
  right_inv := by
    rintro ⟨⟨X, Y⟩, hp⟩
    by_cases hX : X = 2
    · subst hX
      have hδ0 : δ ≠ 0 := fun h => hδ ⟨0, by rw [h, mul_zero]⟩
      have hY : Y = 0 := by
        have : δ * Y ^ 2 = 0 := by linear_combination -hp
        have := (mul_eq_zero.mp this).resolve_left hδ0
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      subst hY
      simp
    · have hs : X - 2 ≠ 0 := sub_ne_zero.mpr hX
      obtain ⟨t, rfl⟩ : ∃ t, Y = (X - 2) * t := ⟨Y / (X - 2), by field_simp⟩
      simp only [hX, ite_false, Sum.elim_inl, mul_div_cancel_left₀ _ hs]
      have hd := conic_ne_zero_of_not_isSquare hδ t
      have hs4 : X - 2 = 4 / (δ * t ^ 2 - 1) := by
        rw [eq_div_iff hd]
        have h' : (X - 2) * ((X - 2) * (δ * t ^ 2 - 1) - 4) = 0 := by
          linear_combination -hp
        have := (mul_eq_zero.mp h').resolve_left hs
        linear_combination this
      apply Subtype.ext
      ext
      · simp only
        rw [← hs4]; ring
      · simp only
        rw [← hs4]

theorem card_conic [Finite K] (h4 : (4 : K) ≠ 0) {δ : K} (hδ : ¬ IsSquare δ) :
    Nat.card {p : K × K // p.1 ^ 2 - δ * p.2 ^ 2 = 4} = Nat.card K + 1 := by
  rw [← Nat.card_congr (conicEquiv h4 hδ), Nat.card_sum, Nat.card_unique (α := Unit)]

theorem card_binary_norm_eq_one [Finite K] (h2 : (2 : K) ≠ 0) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card {p : K × K // p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 = 1} = Nat.card K + 1 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hδ : ¬ IsSquare (b ^ 2 - 4 * c) := by
    rintro ⟨r, hr⟩
    apply hirr ((r - b) / 2)
    field_simp
    linear_combination -hr
  let e : K × K ≃ K × K :=
    { toFun := fun p => (2 * p.1 + b * p.2, p.2)
      invFun := fun p => ((p.1 - b * p.2) / 2, p.2)
      left_inv := fun p => Prod.ext (by
        change (2 * p.1 + b * p.2 - b * p.2) / 2 = p.1
        rw [add_sub_cancel_right]
        exact mul_div_cancel_left₀ _ h2) rfl
      right_inv := fun p => Prod.ext (by field_simp; ring) rfl }
  rw [← card_conic h4 hδ]
  refine Nat.card_congr (Equiv.subtypeEquiv e fun p => ?_)
  change _ ↔ (2 * p.1 + b * p.2) ^ 2 - (b ^ 2 - 4 * c) * p.2 ^ 2 = 4
  constructor
  · intro h
    linear_combination 4 * h
  · intro h
    have : 4 * (p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 - 1) = 0 := by linear_combination h
    have := (mul_eq_zero.mp this).resolve_left h4
    linear_combination this

def minusPlaneEquiv (K : Type*) : (Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → K) ≃ K × K where
  toFun v := (v (.inr (.inr 0)), v (.inr (.inr 1)))
  invFun p := Sum.elim (fun i => i.elim0) (Sum.elim (fun i => i.elim0) ![p.1, p.2])
  left_inv v := by
    funext k
    rcases k with i | i | j
    · exact i.elim0
    · exact i.elim0
    · fin_cases j <;> rfl
  right_inv p := rfl

theorem card_norm_eq_one_quadMinus_one [Finite K] (h2 : (2 : K) ≠ 0) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card {x : Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → K // quadMinus 1 K b c x = 1} =
      Nat.card K + 1 := by
  rw [← card_binary_norm_eq_one h2 hirr]
  refine Nat.card_congr (Equiv.subtypeEquiv (minusPlaneEquiv K) fun x => ?_)
  rw [quadMinus_apply, Finset.sum_eq_zero (fun i _ => (i : Fin 0).elim0), zero_add]
  rfl

end Conic

section Anisotropic

variable {K A : Type*} [Field K] [AddCommGroup A] [Module K A] {Q : QuadraticForm K A}

theorem card_orthogonalGroup_of_anisotropic_of_two_ne_zero [FiniteDimensional K A]
    (h2 : (2 : K) ≠ 0) (hA : finrank K A = 2) (hani : ∀ x, x ≠ 0 → Q x ≠ 0) {x₀ : A}
    (hx₀ : Q x₀ = 1) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * Nat.card {x : A // Q x = 1} := by
  classical
  have : NeZero (2 : K) := ⟨h2⟩
  set O := TauCeti.QuadraticMap.orthogonalGroup Q
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hx₀
    exact zero_ne_one hx₀
  have hxx : polar Q x₀ x₀ = 2 := by rw [polar_self_eq_two_mul, hx₀, mul_one]
  have horbit : MulAction.orbit O x₀ = {x | Q x = 1} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      change Q ((g : A ≃ₗ[K] A) x₀) = 1
      rw [map_of_mem g.2, hx₀]
    · intro hx
      have hx' : Q x = 1 := hx
      obtain ⟨f, hf⟩ := QuadraticMap.exists_isometryEquiv_apply_eq_of_map_eq Q
        (hx₀.trans hx'.symm) (by rw [hx']; exact one_ne_zero)
      exact ⟨⟨f.toLinearEquiv, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr f.map_app⟩, hf⟩
  obtain ⟨y, hy⟩ : ∃ y : A, y ∉ Submodule.span K {x₀} := by
    by_contra! h
    have htop : Submodule.span K {x₀} = ⊤ := Submodule.eq_top_iff'.mpr h
    have h1 := finrank_span_singleton (K := K) hx₀0
    rw [htop, finrank_top, hA] at h1
    omega
  set y₀ := y - (polar Q x₀ y / 2) • x₀ with hy₀def
  have hxy : polar Q x₀ y₀ = 0 := by
    rw [hy₀def, polar_sub_right, polar_smul_right_eq, hxx, div_mul_cancel₀ _ h2, sub_self]
  have hy₀ : y₀ ∉ Submodule.span K {x₀} := by
    intro h
    apply hy
    have hyy : y = y₀ + (polar Q x₀ y / 2) • x₀ := by rw [hy₀def, sub_add_cancel]
    rw [hyy]
    exact Submodule.add_mem _ h (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hy₀0 : y₀ ≠ 0 := fun h => hy₀ (h ▸ Submodule.zero_mem _)
  have hQy₀ : Q y₀ ≠ 0 := hani y₀ hy₀0
  have hyx : polar Q y₀ x₀ = 0 := by rw [polar_comm, hxy]
  have hli : LinearIndependent K ![x₀, y₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (polar Q x₀) hst
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hxx, hxy, polar_zero_right]
      at h1
    have hs : s = 0 := by
      have h' : s * 2 = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h').resolve_right h2
    subst hs
    rw [zero_smul, zero_add] at hst
    exact ⟨rfl, (smul_eq_zero.mp hst).resolve_right hy₀0⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hA])
  have hb0 : b 0 = x₀ := by simp [b]
  have hb1 : b 1 = y₀ := by simp [b]
  have hext : ∀ g h : A ≃ₗ[K] A, g x₀ = h x₀ → g y₀ = h y₀ → g = h := by
    intro g h hg0 hg1
    apply LinearEquiv.toLinearMap_injective
    refine b.ext fun i => ?_
    fin_cases i
    · simpa [hb0] using hg0
    · simpa [hb1] using hg1
  set s := reflect Q y₀ with hsdef
  have hsO : s ∈ O := reflect_mem_orthogonalGroup Q y₀
  have hs0 : s x₀ = x₀ := reflect_apply_of_polar_eq_zero hyx
  have hs1 : s y₀ = -y₀ := by
    rw [hsdef, reflect_apply hQy₀, polar_self_eq_two_mul, mul_div_cancel_right₀ _ hQy₀, two_smul]
    abel
  have hstab : ∀ g ∈ O, g x₀ = x₀ → g = 1 ∨ g = s := by
    intro g hg hgx
    have hz1 : polar Q x₀ (g y₀) = 0 := by
      nth_rewrite 1 [← hgx]
      rw [polar_map_of_mem hg, hxy]
    obtain ⟨α, β, hrepr⟩ : ∃ α β : K, g y₀ = α • x₀ + β • y₀ := by
      refine ⟨b.repr (g y₀) 0, b.repr (g y₀) 1, ?_⟩
      have := b.sum_repr (g y₀)
      rw [Fin.sum_univ_two, hb0, hb1] at this
      exact this.symm
    have hα : α = 0 := by
      rw [hrepr, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hxx, hxy] at hz1
      have h' : α * 2 = 0 := by linear_combination hz1
      exact (mul_eq_zero.mp h').resolve_right h2
    subst hα
    have hβ : β * β = 1 := by
      have h1 := map_of_mem hg y₀
      rw [hrepr, zero_smul, zero_add, map_smul_eq_sq] at h1
      have h' : (β ^ 2 - 1) * Q y₀ = 0 := by linear_combination h1
      have h'' := (mul_eq_zero.mp h').resolve_right hQy₀
      linear_combination h''
    rcases mul_self_eq_one_iff.mp hβ with rfl | rfl
    · left
      refine hext g 1 (by rw [hgx]; rfl) ?_
      rw [hrepr, zero_smul, zero_add, one_smul]
      rfl
    · right
      refine hext g s (by rw [hgx, hs0]) ?_
      rw [hrepr, zero_smul, zero_add, hs1, neg_one_smul]
  have hstab_card : Nat.card (MulAction.stabilizer O x₀) = 2 := by
    rw [Nat.card_eq_two_iff]
    have hsmem : (⟨s, hsO⟩ : O) ∈ MulAction.stabilizer O x₀ := by
      rw [MulAction.mem_stabilizer_iff]
      exact hs0
    refine ⟨1, ⟨⟨s, hsO⟩, hsmem⟩, fun h => ?_, ?_⟩
    · have := congrArg (fun g : MulAction.stabilizer O x₀ => ((g : O) : A ≃ₗ[K] A) y₀) h
      change y₀ = s y₀ at this
      rw [hs1] at this
      have h2y : (2 : K) • y₀ = 0 := by
        rw [two_smul]
        nth_rewrite 1 [this]
        exact neg_add_cancel y₀
      exact hy₀0 ((smul_eq_zero.mp h2y).resolve_left h2)
    · ext ⟨⟨g, hg⟩, hgstab⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      have hgx : g x₀ = x₀ := (MulAction.mem_stabilizer_iff.mp hgstab : _)
      rcases hstab g hg hgx with rfl | rfl
      · left
        rfl
      · right
        rfl
  have hcard := (MulAction.stabilizer O x₀).card_mul_index
  rw [MulAction.index_stabilizer, horbit, ← Nat.card_coe_set_eq, hstab_card] at hcard
  rw [← hcard]
  rfl

end Anisotropic

section MinusOne

variable {K : Type*} [Field K]

theorem quadMinus_one_ne_zero {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (v : Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → K) (hv : v ≠ 0) : quadMinus 1 K b c v ≠ 0 := by
  intro h0
  apply hv
  rw [quadMinus_apply, Finset.sum_eq_zero (fun i _ => (i : Fin 0).elim0), zero_add] at h0
  obtain ⟨hu, hw⟩ := binary_eq_zero_of_irreducible hirr h0
  funext k
  rcases k with i | i | j
  · exact i.elim0
  · exact i.elim0
  · fin_cases j
    · exact hu
    · exact hw

theorem card_orthogonalGroup_quadMinus_one [Finite K] (h2 : (2 : K) ≠ 0) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 1 K b c)) =
      2 * (Nat.card K + 1) := by
  have hA : finrank K (Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → K) = 2 := by simp
  have hx₀ : quadMinus 1 K b c (Pi.single (Sum.inr (Sum.inr 0)) 1 :
      Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → K) = 1 := by
    rw [quadMinus_apply, Finset.sum_eq_zero (fun i _ => (i : Fin 0).elim0)]
    simp
  rw [card_orthogonalGroup_of_anisotropic_of_two_ne_zero h2 hA (quadMinus_one_ne_zero hirr) hx₀,
    card_norm_eq_one_quadMinus_one h2 hirr]

end MinusOne

theorem card_coord_fun_odd {K : Type*} (m : ℕ) :
    Nat.card (Fin m ⊕ Fin m ⊕ Unit → K) = Nat.card K ^ (2 * m + 1) := by
  rw [card_coord_fun, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  ring_nf

section Odd

variable {K : Type*} [Field K] [Finite K]

omit [Finite K] in
theorem card_singular_and_orthogonalGroup_quadOdd_zero (h2 : (2 : K) ≠ 0) :
    Nat.card {v // quadOdd 0 K v = 0} = 1 ∧
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 0 K)) = 2 := by
  have : NeZero (2 : K) := ⟨h2⟩
  have hz : ∀ v : Fin 0 ⊕ Fin 0 ⊕ Unit → K, quadOdd 0 K v = 0 → v = 0 := by
    intro v hv
    rw [quadOdd_apply, Finset.sum_eq_zero (fun i _ => i.elim0), zero_add] at hv
    funext k
    rcases k with i | i | ⟨⟩
    · exact i.elim0
    · exact i.elim0
    · exact pow_eq_zero_iff two_ne_zero |>.mp hv
  refine ⟨Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => Subtype.ext ?_⟩,
    ⟨⟨0, QuadraticMap.map_zero _⟩⟩⟩, ?_⟩
  · rw [hz x.1 x.2, hz y.1 y.2]
  · refine TauCeti.QuadraticMap.card_orthogonalGroup_of_finrank_eq_one ?_ ?_
    · intro h
      have := congrArg (fun Q : QuadraticForm K (Fin 0 ⊕ Fin 0 ⊕ Unit → K) =>
        Q (Pi.single (Sum.inr (Sum.inr ())) 1)) h
      simp [quadOdd_apply] at this
    · simp

theorem card_singular_and_orthogonalGroup_quadOdd (h2 : (2 : K) ≠ 0) (n : ℕ) :
    (Nat.card {v // quadOdd n K v = 0} : ℤ) = (Nat.card K : ℤ) ^ (2 * n) ∧
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd n K)) : ℤ) =
        2 * (Nat.card K : ℤ) ^ (n ^ 2) *
          ∏ i ∈ Finset.Icc 1 n, ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  induction n with
  | zero =>
    obtain ⟨hS0, hO0⟩ := card_singular_and_orthogonalGroup_quadOdd_zero h2
    rw [hS0, hO0]
    simp
  | succ m ih =>
    obtain ⟨hS, hO⟩ := card_step_of_nondegenerate (oddIsometry K m)
      (nondegenerate_polarBilin_quadOdd m K h2)
    have hS1 := one_le_card_singular (quadOdd (m + 1) K)
    rw [card_coord_fun_odd] at hS hO
    obtain ⟨ihS, ihO⟩ := ih
    constructor
    · rw [hS]
      push_cast [hq]
      rw [ihS]
      ring
    · rw [hO]
      push_cast [hS1]
      rw [ihO, Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1), hS]
      push_cast [hq]
      rw [ihS]
      ring

end Odd

section Plus

variable {K : Type*} [Field K] [Finite K]

theorem card_singular_and_orthogonalGroup_quadPlus (m : ℕ) :
    (Nat.card {v // quadPlus (m + 1) K v = 0} : ℤ) =
        1 + ((Nat.card K : ℤ) ^ (m + 1) - 1) * ((Nat.card K : ℤ) ^ m + 1) ∧
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus (m + 1) K)) : ℤ) =
        2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) - 1) *
          ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hW : ∀ m, Nat.card (Fin m ⊕ Fin m → K) = Nat.card K ^ (2 * m) := fun m => by
    rw [card_coord_fun, Fintype.card_sum, Fintype.card_fin, two_mul]
  induction m with
  | zero =>
    obtain ⟨hS, hO⟩ := card_step_of_nondegenerate (plusIsometry K 0)
      (nondegenerate_polarBilin_quadPlus 0 K)
    obtain ⟨hS0, hO0⟩ := card_singular_and_orthogonalGroup_of_subsingleton (quadPlus 0 K)
    rw [hS0, hW 0] at hS
    rw [hW 0, hO0, hS] at hO
    simp only [mul_one] at hS hO
    have h1 : 1 ≤ Nat.card K + (Nat.card K - 1) := by omega
    constructor
    · rw [hS]
      push_cast [hq]
      ring
    · rw [hO]
      push_cast [hq, h1]
      simp
      ring
  | succ m ih =>
    obtain ⟨hS, hO⟩ := card_step_of_nondegenerate (plusIsometry K (m + 1))
      (nondegenerate_polarBilin_quadPlus (m + 1) K)
    have hS1 := one_le_card_singular (quadPlus (m + 1 + 1) K)
    rw [hW] at hS hO
    obtain ⟨ihS, ihO⟩ := ih
    constructor
    · rw [hS]
      push_cast [hq]
      rw [ihS]
      ring
    · rw [hO]
      push_cast [hS1]
      rw [ihO, Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1), hS]
      push_cast [hq]
      rw [ihS]
      ring

end Plus

section Minus

variable {K : Type*} [Field K] [Finite K]

theorem card_singular_and_orthogonalGroup_quadMinus (h2 : (2 : K) ≠ 0) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (m : ℕ) :
    (Nat.card {v // quadMinus (m + 1) K b c v = 0} : ℤ) =
        1 + ((Nat.card K : ℤ) ^ (m + 1) + 1) * ((Nat.card K : ℤ) ^ m - 1) ∧
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus (m + 1) K b c)) : ℤ) =
        2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) + 1) *
          ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hW : ∀ k, Nat.card (Fin k ⊕ Fin k ⊕ Fin 2 → K) = Nat.card K ^ (2 * k + 2) := fun k => by
    rw [card_coord_fun, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    ring_nf
  induction m with
  | zero =>
    have hS0 : Nat.card {v // quadMinus 1 K b c v = 0} = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => Subtype.ext (by
        rw [of_not_not fun h => quadMinus_one_ne_zero hirr x.1 h x.2,
          of_not_not fun h => quadMinus_one_ne_zero hirr y.1 h y.2])⟩,
        ⟨⟨0, QuadraticMap.map_zero _⟩⟩⟩
    constructor
    · rw [hS0]
      simp
    · rw [card_orthogonalGroup_quadMinus_one h2 hirr]
      push_cast
      simp
  | succ m ih =>
    obtain ⟨hS, hO⟩ := card_step_of_nondegenerate (minusIsometry K m b c)
      (nondegenerate_polarBilin_quadMinus_of_finite (m + 1) K hirr)
    have hS1 := one_le_card_singular (quadMinus (m + 1 + 1) K b c)
    have hWm : Nat.card (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) =
        Nat.card K ^ (2 * (m + 1)) := by
      rw [hW, Nat.add_sub_cancel]
      ring_nf
    rw [hWm] at hS hO
    obtain ⟨ihS, ihO⟩ := ih
    constructor
    · rw [hS]
      push_cast [hq]
      rw [ihS]
      ring
    · rw [hO]
      push_cast [hS1]
      rw [ihO, Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1), hS]
      push_cast [hq]
      rw [ihS]
      ring

end Minus

section Main

theorem card_orthogonalGroup_quadOdd_of_two_ne_zero {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) (n : ℕ) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd n K)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (n ^ 2) *
        ∏ i ∈ Finset.Icc 1 n, ((Nat.card K : ℤ) ^ (2 * i) - 1) :=
  (card_singular_and_orthogonalGroup_quadOdd h2 n).2

theorem card_orthogonalGroup_quadPlus_of_two_ne_zero {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) (m : ℕ) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus (m + 1) K)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) - 1) *
        ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  have _ := h2
  exact (card_singular_and_orthogonalGroup_quadPlus m).2

theorem card_orthogonalGroup_quadMinus_of_two_ne_zero {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (m : ℕ) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus (m + 1) K b c)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℤ) ^ (2 * i) - 1) :=
  (card_singular_and_orthogonalGroup_quadMinus h2 hirr m).2

theorem card_singular_quadOdd_of_two_ne_zero {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) (n : ℕ) :
    (Nat.card {v : Fin n ⊕ Fin n ⊕ Unit → K // quadOdd n K v = 0} : ℤ) =
      (Nat.card K : ℤ) ^ (2 * n) :=
  (card_singular_and_orthogonalGroup_quadOdd h2 n).1

theorem card_singular_quadPlus {K : Type} [Field K] [Finite K] (m : ℕ) :
    (Nat.card {v : Fin (m + 1) ⊕ Fin (m + 1) → K // quadPlus (m + 1) K v = 0} : ℤ) =
      1 + ((Nat.card K : ℤ) ^ (m + 1) - 1) * ((Nat.card K : ℤ) ^ m + 1) :=
  (card_singular_and_orthogonalGroup_quadPlus m).1

theorem card_singular_quadMinus_of_two_ne_zero {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (m : ℕ) :
    (Nat.card {v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K //
        quadMinus (m + 1) K b c v = 0} : ℤ) =
      1 + ((Nat.card K : ℤ) ^ (m + 1) + 1) * ((Nat.card K : ℤ) ^ m - 1) :=
  (card_singular_and_orthogonalGroup_quadMinus h2 hirr m).1

end Main

end CFSG.ClassicalInvolution
