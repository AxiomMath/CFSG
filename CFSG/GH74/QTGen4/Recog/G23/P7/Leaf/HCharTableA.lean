module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HCharTableEigen
public import CFSG.CharacterTheory.SteinbergBSExceptionalCharacterTools

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.HChar

open CFSG.GH74.QTGen4.Recog.G23.HCharData

@[expose] def InD {X : Type} [Group X] (z x : X) : Prop :=
  (x ^ 3 = 1 ∧ x ≠ 1) ∨ ∃ k : ℕ, 0 < k ∧ orderOf x = 2 * k ∧ x ^ k = z

structure TabHyp (X : Type) [Group X] (z : X) (rep : Fin 20 → X) : Prop where
  cover : ∀ x : X, ∃ j, IsConj (rep j) x
  distinct : ∀ i j, IsConj (rep i) (rep j) → i = j
  card_class : ∀ j, Nat.card {x : X // IsConj (rep j) x} = hcSize j
  rep_zero : rep 0 = 1
  rep_one : rep 1 = z
  order_rep : ∀ j, orderOf (rep j) = hcOrd j
  dflag : ∀ j, InD z (rep j) ↔ hcDfl j = true
  ct_z : Nat.card {u : X // orderOf u = 2 ∧ u ≠ z} = hcCt 1
  ct_other : ∀ j, j ≠ 1 →
    Nat.card {u : X // orderOf u = 2 ∧ u * rep j * u⁻¹ = (rep j)⁻¹} = hcCt j
  acount : ∀ (r : Fin 4) (j k : Fin 20),
    Nat.card {x : X // IsConj (rep (hcI r)) x ∧ IsConj (rep j) (x⁻¹ * rep k)} = hcA r j k

namespace TabHyp

variable {X : Type} [Group X] {z : X} {rep : Fin 20 → X}

theorem isConj_map_iff {Y : Type} [Group Y] (e : Y ≃* X) (a b : Y) :
    IsConj (e a) (e b) ↔ IsConj a b := by
  simp only [isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, e.injective ?_⟩
    simpa using hc
  · rintro ⟨c, hc⟩
    exact ⟨e c, by simpa using congrArg e hc⟩

theorem inD_map {Y : Type} [Group Y] (e : Y ≃* X) (z x : Y) : InD (e z) (e x) ↔ InD z x := by
  unfold InD
  simp only [← map_pow, ne_eq, MulEquiv.map_eq_one_iff, MulEquiv.orderOf_eq, e.injective.eq_iff]

theorem of_mulEquiv {Y : Type} [Group Y] (e : Y ≃* X) (h : TabHyp X z rep) :
    TabHyp Y (e.symm z) (fun j => e.symm (rep j)) := by
  have hc : ∀ (a : X) (y : Y), IsConj (e.symm a) y ↔ IsConj a (e y) := by
    intro a y
    rw [← isConj_map_iff e, MulEquiv.apply_symm_apply]
  refine
    { cover := fun y => ?_
      distinct := fun i j hij => h.distinct i j ?_
      card_class := fun j => ?_
      rep_zero := by simp [h.rep_zero]
      rep_one := by simp [h.rep_one]
      order_rep := fun j => by rw [MulEquiv.orderOf_eq, h.order_rep]
      dflag := fun j => ?_
      ct_z := ?_
      ct_other := fun j hj => ?_
      acount := fun r j k => ?_ }
  · obtain ⟨j, hj⟩ := h.cover (e y)
    exact ⟨j, (hc (rep j) y).2 hj⟩
  · simpa using (isConj_map_iff e _ _).2 hij
  · rw [← h.card_class j]
    exact Nat.card_congr (e.toEquiv.subtypeEquiv fun y => hc (rep j) y)
  · rw [← h.dflag j, ← inD_map e.symm]
  · rw [← h.ct_z]
    refine Nat.card_congr (e.toEquiv.subtypeEquiv fun u => ?_)
    show orderOf u = 2 ∧ u ≠ e.symm z ↔ orderOf (e u) = 2 ∧ e u ≠ z
    simp [MulEquiv.orderOf_eq, e.eq_symm_apply]
  · rw [← h.ct_other j hj]
    refine Nat.card_congr (e.toEquiv.subtypeEquiv fun u => ?_)
    show orderOf u = 2 ∧ u * e.symm (rep j) * u⁻¹ = (e.symm (rep j))⁻¹ ↔
      orderOf (e u) = 2 ∧ e u * rep j * (e u)⁻¹ = (rep j)⁻¹
    rw [MulEquiv.orderOf_eq, ← e.injective.eq_iff]
    simp
  · rw [← h.acount r j k]
    refine Nat.card_congr (e.toEquiv.subtypeEquiv fun y => ?_)
    show IsConj (e.symm (rep (hcI r))) y ∧ IsConj (e.symm (rep j)) (y⁻¹ * e.symm (rep k)) ↔
      IsConj (rep (hcI r)) (e y) ∧ IsConj (rep j) ((e y)⁻¹ * rep k)
    rw [hc, hc]
    simp

section Classes0

open Classical

@[expose] noncomputable def cls (h : TabHyp X z rep) (x : X) : Fin 20 :=
  Classical.choose (h.cover x)

theorem isConj_cls (h : TabHyp X z rep) (x : X) : IsConj (rep (h.cls x)) x :=
  Classical.choose_spec (h.cover x)

theorem cls_eq_iff (h : TabHyp X z rep) {x : X} {j : Fin 20} : h.cls x = j ↔ IsConj (rep j) x := by
  constructor
  · rintro rfl
    exact h.isConj_cls x
  · intro hj
    exact h.distinct _ _ ((h.isConj_cls x).trans hj.symm)

theorem cls_rep (h : TabHyp X z rep) (j : Fin 20) : h.cls (rep j) = j :=
  h.cls_eq_iff.2 (IsConj.refl _)

theorem cf_val (h : TabHyp X z rep) {f : X → ℂ} (hf : ∀ x g : X, f (g * x * g⁻¹) = f x) (x : X) :
    f x = f (rep (h.cls x)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (h.isConj_cls x)
  have := hf (rep (h.cls x)) c
  rw [hc] at this
  exact this

@[expose] noncomputable def tab (h : TabHyp X z rep) (F : Fin 20 → ℂ) : X → ℂ :=
  fun x => F (h.cls x)

theorem tab_rep (h : TabHyp X z rep) (F : Fin 20 → ℂ) (j : Fin 20) : h.tab F (rep j) = F j := by
  simp [tab, h.cls_rep]

end Classes0

section Classes

open Classical

variable [Fintype X]

theorem card_cls (h : TabHyp X z rep) (j : Fin 20) :
    (Finset.univ.filter fun x => h.cls x = j).card = hcSize j := by
  rw [← h.card_class j, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.card_bij (fun x _ => x) (fun x hx => by simpa [h.cls_eq_iff] using hx)
    (fun _ _ _ _ hh => hh) (fun x hx => ⟨x, by simpa [h.cls_eq_iff] using hx, rfl⟩)

theorem sum_cls {M : Type*} [AddCommMonoid M] (h : TabHyp X z rep) (F : Fin 20 → M) :
    ∑ x : X, F (h.cls x) = ∑ j : Fin 20, hcSize j • F j := by
  rw [← Finset.sum_fiberwise' Finset.univ h.cls F]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_const, h.card_cls]

theorem card_X (h : TabHyp X z rep) : Nat.card X = 576 := by
  have := h.sum_cls (fun _ => (1 : ℕ))
  simp only [smul_eq_mul, mul_one, sum_size] at this
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]
  exact this

theorem inner_tab (h : TabHyp X z rep) (F G : Fin 20 → ℂ) :
    CFSG.BlocksInnerProduct (h.tab F) (h.tab G) =
      (576 : ℂ)⁻¹ * ∑ j, (hcSize j : ℂ) * (F j * starRingEnd ℂ (G j)) := by
  unfold CFSG.BlocksInnerProduct
  rw [h.card_X]
  have := h.sum_cls (fun j => F j * starRingEnd ℂ (G j))
  simp only [nsmul_eq_mul] at this
  simp only [tab]
  rw [this]
  norm_num

end Classes

section Irreducible

open Classical

variable [Fintype X]

theorem irr_one {θ : X → ℂ} (hθ : θ ∈ CFSG.BlocksIrr X) : ∃ n : ℕ, 0 < n ∧ θ 1 = (n : ℂ) := by
  obtain ⟨ρ, hρ, hρθ⟩ := (Set.ext_iff.mp (CFSG.blocksIrr_eq_irreducible_characters X) θ).mp hθ
  have hdim : 0 < Module.finrank ℂ ρ.vector := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply CFSG.TwoRankLowerBound.Helpers.irreducible_character_degree_ne_zero ρ hρ
    rw [CFSG.TwoRankLowerBound.Helpers.FiniteComplexRepresentation.character,
      Representation.char_one, hzero, Nat.cast_zero]
  refine ⟨Module.finrank ℂ ρ.vector, hdim, ?_⟩
  rw [← hρθ, CFSG.TwoRankLowerBound.Helpers.FiniteComplexRepresentation.character,
    Representation.char_one]

theorem irr_orth (h : TabHyp X z rep) {θ χ : X → ℂ} (hθ : θ ∈ CFSG.BlocksIrr X)
    (hχ : χ ∈ CFSG.BlocksIrr X) :
    ∑ j, (hcSize j : ℂ) * (θ (rep j) * starRingEnd ℂ (χ (rep j))) =
      576 * (if θ = χ then 1 else 0) := by
  have h1 := CFSG.blocksInnerProduct_irreducible (⟨θ, hθ⟩ : CFSG.BlocksIrr X) ⟨χ, hχ⟩
  have h2 := h.inner_tab (fun j => θ (rep j)) (fun j => χ (rep j))
  have e1 : h.tab (fun j => θ (rep j)) = θ := by
    funext x
    exact (h.cf_val (CFSG.BlockSectionOrthogonality.Helpers.irreducible_isClassFunction hθ) x).symm
  have e2 : h.tab (fun j => χ (rep j)) = χ := by
    funext x
    exact (h.cf_val (CFSG.BlockSectionOrthogonality.Helpers.irreducible_isClassFunction hχ) x).symm
  rw [e1, e2] at h2
  simp only [Subtype.mk.injEq] at h1
  rw [h1] at h2
  have h3 : (576 : ℂ) * (576 : ℂ)⁻¹ = 1 := by norm_num
  calc ∑ j, (hcSize j : ℂ) * (θ (rep j) * starRingEnd ℂ (χ (rep j)))
      = 576 * ((576 : ℂ)⁻¹ * ∑ j, (hcSize j : ℂ) * (θ (rep j) * starRingEnd ℂ (χ (rep j)))) := by
        rw [← mul_assoc, h3, one_mul]
    _ = 576 * (if θ = χ then 1 else 0) := by rw [← h2]

end Irreducible

section Mult

open Classical

variable [Fintype X]

theorem card_filter_isConj (h : TabHyp X z rep) (j : Fin 20) :
    (Finset.univ.filter fun g : X => IsConj g (rep j)).card = hcSize j := by
  rw [← h.card_class j, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact congrArg Finset.card (Finset.filter_congr fun g _ => isConj_comm)

theorem card_pairs (h : TabHyp X z rep) (r : Fin 4) (j k : Fin 20) :
    ((((Finset.univ.filter fun g : X => IsConj g (rep (hcI r))) ×ˢ
        (Finset.univ.filter fun g : X => IsConj g (rep j))).filter
          fun q => q.1 * q.2 = rep k).card) = hcA r j k := by
  rw [← h.acount r j k, Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_bij (fun q _ => q.1) ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hq ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hq
    refine ⟨isConj_comm.1 h1, ?_⟩
    have : q.1⁻¹ * rep k = q.2 := by rw [← h3]; group
    rw [this]
    exact isConj_comm.1 h2
  · intro q hq q' hq' hqq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hq hq'
    obtain ⟨_, h3⟩ := hq
    obtain ⟨_, h3'⟩ := hq'
    refine Prod.ext hqq ?_
    have h4 : q.1 * q.2 = q.1 * q'.2 := by
      rw [h3]
      have := h3'
      rw [← hqq] at this
      exact this.symm
    exact mul_left_cancel h4
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨(x, x⁻¹ * rep k), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    exact ⟨⟨isConj_comm.1 hx.1, isConj_comm.1 hx.2⟩, by group⟩

theorem mult_formula (h : TabHyp X z rep) (r : Fin 4) (j k : Fin 20) :
    (hcA r j k : ℂ) = ((hcSize (hcI r) : ℂ) * (hcSize j : ℂ) / 576) *
      ∑ χ ∈ (CFSG.BlockSectionOrthogonality.Helpers.irreducibles_finite X).toFinset,
        χ (rep (hcI r)) * χ (rep j) * starRingEnd ℂ (χ (rep k)) / χ 1 := by
  have := (CFSG.CharacterTheory.SteinbergBS.class_multiplication_count
    (rep (hcI r)) (rep j) (rep k)).1
  rw [h.card_pairs, h.card_filter_isConj, h.card_filter_isConj, h.card_X] at this
  push_cast at this
  exact this

theorem central_rel (h : TabHyp X z rep) {θ : X → ℂ} (hθ : θ ∈ CFSG.BlocksIrr X) (r : Fin 4)
    (j : Fin 20) :
    (∑ k, (hcSize k : ℂ) * (hcA r j k : ℂ) * θ (rep k)) * θ 1 =
      (hcSize (hcI r) : ℂ) * θ (rep (hcI r)) * ((hcSize j : ℂ) * θ (rep j)) := by
  set 𝓘 := (CFSG.BlockSectionOrthogonality.Helpers.irreducibles_finite X).toFinset with h𝓘
  have hθI : θ ∈ 𝓘 := (Set.Finite.mem_toFinset _).2 hθ
  obtain ⟨n, hn, hθ1⟩ := irr_one hθ
  have hθ1' : θ 1 ≠ 0 := by
    rw [hθ1]
    exact_mod_cast hn.ne'
  set c : ℂ := (hcSize (hcI r) : ℂ) * (hcSize j : ℂ) / 576 with hc
  set G : (X → ℂ) → ℂ := fun χ => χ (rep (hcI r)) * χ (rep j) / χ 1 with hG
  have e1 : ∀ k, (hcSize k : ℂ) * (hcA r j k : ℂ) * θ (rep k) =
      c * ∑ χ ∈ 𝓘, G χ * ((hcSize k : ℂ) * (θ (rep k) * starRingEnd ℂ (χ (rep k)))) := by
    intro k
    rw [h.mult_formula r j k]
    have hsum : ∑ χ ∈ 𝓘, (hcSize k : ℂ) * θ (rep k) *
        (χ (rep (hcI r)) * χ (rep j) * starRingEnd ℂ (χ (rep k)) / χ 1) =
        ∑ χ ∈ 𝓘, G χ * ((hcSize k : ℂ) * (θ (rep k) * starRingEnd ℂ (χ (rep k)))) :=
      Finset.sum_congr rfl (fun χ _ => by simp only [hG]; ring)
    calc (hcSize k : ℂ) * (c * ∑ χ ∈ 𝓘, χ (rep (hcI r)) * χ (rep j) *
            starRingEnd ℂ (χ (rep k)) / χ 1) * θ (rep k)
        = c * ((hcSize k : ℂ) * θ (rep k) *
            ∑ χ ∈ 𝓘, χ (rep (hcI r)) * χ (rep j) * starRingEnd ℂ (χ (rep k)) / χ 1) := by ring
      _ = c * ∑ χ ∈ 𝓘, (hcSize k : ℂ) * θ (rep k) *
            (χ (rep (hcI r)) * χ (rep j) * starRingEnd ℂ (χ (rep k)) / χ 1) := by
          rw [Finset.mul_sum]
      _ = _ := by rw [hsum]
  have e2 : ∑ k, (hcSize k : ℂ) * (hcA r j k : ℂ) * θ (rep k) =
      c * ∑ χ ∈ 𝓘, G χ * ∑ k, (hcSize k : ℂ) * (θ (rep k) * starRingEnd ℂ (χ (rep k))) := by
    have hsum : ∑ χ ∈ 𝓘, ∑ k, G χ * ((hcSize k : ℂ) * (θ (rep k) * starRingEnd ℂ (χ (rep k)))) =
        ∑ χ ∈ 𝓘, G χ * ∑ k, (hcSize k : ℂ) * (θ (rep k) * starRingEnd ℂ (χ (rep k))) :=
      Finset.sum_congr rfl (fun χ _ => by rw [Finset.mul_sum])
    calc ∑ k, (hcSize k : ℂ) * (hcA r j k : ℂ) * θ (rep k)
        = ∑ k, c * ∑ χ ∈ 𝓘, G χ * ((hcSize k : ℂ) * (θ (rep k) * starRingEnd ℂ (χ (rep k)))) :=
          Finset.sum_congr rfl fun k _ => e1 k
      _ = c * ∑ k, ∑ χ ∈ 𝓘, G χ * ((hcSize k : ℂ) * (θ (rep k) * starRingEnd ℂ (χ (rep k)))) := by
          rw [← Finset.mul_sum]
      _ = c * ∑ χ ∈ 𝓘, ∑ k, G χ * ((hcSize k : ℂ) * (θ (rep k) * starRingEnd ℂ (χ (rep k)))) := by
          rw [Finset.sum_comm]
      _ = _ := by rw [hsum]
  have e3 : ∑ χ ∈ 𝓘, G χ * ∑ k, (hcSize k : ℂ) * (θ (rep k) * starRingEnd ℂ (χ (rep k))) =
      G θ * 576 := by
    rw [Finset.sum_eq_single θ]
    · rw [h.irr_orth hθ hθ]
      simp [mul_comm]
    · intro χ hχ hne
      rw [h.irr_orth hθ ((Set.Finite.mem_toFinset _).1 hχ)]
      simp [Ne.symm hne]
    · intro hnot
      exact absurd hθI hnot
  rw [e2, e3]
  simp only [hG, hc]
  field_simp

theorem irr_eq_row (h : TabHyp X z rep) {θ : X → ℂ} (hθ : θ ∈ CFSG.BlocksIrr X) :
    ∃ m : Fin 20, θ = h.tab (fun j => (hcT m j : ℂ)) := by
  obtain ⟨n, hn, hθ1⟩ := irr_one hθ
  have hθ0 : θ (rep 0) = (n : ℂ) := by rw [h.rep_zero, hθ1]
  have ht0 : θ (rep 0) ≠ 0 := by
    rw [hθ0]
    exact_mod_cast hn.ne'
  have hR : ∀ (r : Fin 4) (j : Fin 20),
      (∑ k, (hcSize k : ℂ) * (hcA r j k : ℂ) * (fun k => θ (rep k)) k) * (fun k => θ (rep k)) 0 =
        (hcSize (hcI r) : ℂ) * (fun k => θ (rep k)) (hcI r) *
          ((hcSize j : ℂ) * (fun k => θ (rep k)) j) := by
    intro r j
    have := h.central_rel hθ r j
    rw [← h.rep_zero] at this
    exact this
  obtain ⟨m, c, hc⟩ := eigen (fun k => θ (rep k)) ht0 hR
  have hTne : (hcT m 0 : ℂ) ≠ 0 := by exact_mod_cast (deg_pos m).ne'
  have hc1 : c * (hcT m 0 : ℂ) = (n : ℂ) := by rw [← hθ0, hc 0]
  have hcr : c = (n : ℂ) / (hcT m 0 : ℂ) := by
    field_simp
    exact hc1
  have hconj : starRingEnd ℂ c = c := by
    rw [hcr]
    simp [map_div₀]
  have hnorm : c * starRingEnd ℂ c = 1 := by
    have h1 := h.irr_orth hθ hθ
    simp only [if_true, mul_one] at h1
    have h2 : ∑ j, (hcSize j : ℂ) * (θ (rep j) * starRingEnd ℂ (θ (rep j))) =
        c * starRingEnd ℂ c * ∑ j, (hcSize j : ℂ) * (hcT m j : ℂ) * (hcT m j : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc j]
      simp only [map_mul, map_intCast]
      ring
    rw [h2, row_orth_c m m] at h1
    simp only [if_true] at h1
    have h576 : (576 : ℂ) ≠ 0 := by norm_num
    exact mul_right_cancel₀ h576 (by rw [one_mul]; exact h1)
  rw [hconj] at hnorm
  have hsq : (n : ℂ) ^ 2 = (hcT m 0 : ℂ) ^ 2 := by
    rw [← hc1]
    linear_combination (hcT m 0 : ℂ) ^ 2 * hnorm
  have hsqZ : (n : ℤ) ^ 2 = (hcT m 0) ^ 2 := by exact_mod_cast hsq
  have hnT : (n : ℤ) = hcT m 0 :=
    (sq_eq_sq₀ (by positivity) (le_of_lt (deg_pos m))).1 hsqZ
  have hc_one : c = 1 := by
    rw [hcr]
    have : (n : ℂ) = (hcT m 0 : ℂ) := by exact_mod_cast hnT
    rw [this]
    exact div_self hTne
  refine ⟨m, funext fun x => ?_⟩
  rw [h.cf_val (CFSG.BlockSectionOrthogonality.Helpers.irreducible_isClassFunction hθ) x, hc,
    hc_one, one_mul]
  rfl

theorem sum_irr_deg_sq (h : TabHyp X z rep) :
    ∑ χ ∈ (CFSG.BlockSectionOrthogonality.Helpers.irreducibles_finite X).toFinset,
      χ 1 * starRingEnd ℂ (χ 1) = 576 := by
  have hmult := (CFSG.CharacterTheory.SteinbergBS.class_multiplication_count (1 : X) 1 1).1
  have hC : (Finset.univ.filter fun g : X => IsConj g 1) = {1} := by
    ext g
    simp [isConj_comm (g := g), isConj_one_right]
  rw [hC, h.card_X] at hmult
  have hpair : ((({1} : Finset X) ×ˢ ({1} : Finset X)).filter
      fun q : X × X => q.1 * q.2 = 1).card = 1 := by
    rw [Finset.singleton_product_singleton, Finset.filter_singleton]
    simp
  rw [hpair] at hmult
  simp only [Finset.card_singleton, Nat.cast_one, one_mul] at hmult
  field_simp at hmult
  push_cast at hmult
  exact hmult.symm

theorem row_mem_irr (h : TabHyp X z rep) (m : Fin 20) :
    h.tab (fun j => (hcT m j : ℂ)) ∈ CFSG.BlocksIrr X := by
  set 𝓘 := (CFSG.BlockSectionOrthogonality.Helpers.irreducibles_finite X).toFinset with h𝓘
  have hex : ∀ θ ∈ 𝓘, ∃ m : Fin 20, θ = h.tab (fun j => (hcT m j : ℂ)) := fun θ hθ =>
    h.irr_eq_row ((Set.Finite.mem_toFinset _).1 hθ)
  choose! f hf using hex
  have hinj : ∀ θ ∈ 𝓘, ∀ θ' ∈ 𝓘, f θ = f θ' → θ = θ' := fun θ hθ θ' hθ' hff => by
    rw [hf θ hθ, hf θ' hθ', hff]
  have hcls1 : h.cls (1 : X) = 0 := by rw [← h.rep_zero, h.cls_rep]
  have hdeg : ∀ θ ∈ 𝓘, θ 1 = (hcT (f θ) 0 : ℂ) := by
    intro θ hθ
    have := congrFun (hf θ hθ) 1
    rw [this]
    simp [tab, hcls1]
  have hsumC : ∑ χ ∈ 𝓘, ((hcT (f χ) 0 : ℤ) : ℂ) ^ 2 = 576 := by
    rw [← h.sum_irr_deg_sq]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hdeg χ hχ, map_intCast]
    ring
  have hsumZ : ∑ χ ∈ 𝓘, (hcT (f χ) 0) ^ 2 = 576 := by exact_mod_cast hsumC
  have himg : ∑ m ∈ 𝓘.image f, (hcT m 0) ^ 2 = 576 := by
    rw [Finset.sum_image hinj]
    exact hsumZ
  by_cases hall : ∀ m, m ∈ 𝓘.image f
  · obtain ⟨θ, hθ, hθm⟩ := Finset.mem_image.1 (hall m)
    rw [← hθm, ← hf θ hθ]
    exact (Set.Finite.mem_toFinset _).1 hθ
  · exfalso
    push Not at hall
    obtain ⟨m₀, hm₀⟩ := hall
    have hlt : ∑ m ∈ 𝓘.image f, (hcT m 0) ^ 2 < ∑ m : Fin 20, (hcT m 0) ^ 2 :=
      Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ m₀) hm₀
        (by have := deg_pos m₀; positivity) (fun j _ _ => by positivity)
    rw [himg, sum_deg_sq] at hlt
    exact lt_irrefl _ hlt

end Mult

end TabHyp

end CFSG.GH74.QTGen4.Recog.G23.P7.HChar
