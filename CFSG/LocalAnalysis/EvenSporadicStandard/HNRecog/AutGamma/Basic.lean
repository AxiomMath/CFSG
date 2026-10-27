module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.SegevSections

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.Monster.GMS

variable {G : Type} [Group G] {a z : G}

open Classical in
@[expose] noncomputable def act (τ : Gamma a ≃g Gamma a) (x : G) : G :=
  if h : IsConj a x then ((τ ⟨x, h⟩ : ConjVert a) : G) else x

theorem act_of_isConj (τ : Gamma a ≃g Gamma a) {x : G} (hx : IsConj a x) :
    act τ x = ((τ ⟨x, hx⟩ : ConjVert a) : G) := by
  classical
  simp only [act, dif_pos hx]

theorem act_vertex (τ : Gamma a ≃g Gamma a) (v : ConjVert a) : act τ (v : G) = (τ v : G) := by
  rw [act_of_isConj τ v.2]

theorem isConj_act (τ : Gamma a ≃g Gamma a) {x : G} (hx : IsConj a x) :
    IsConj a (act τ x) := by
  rw [act_of_isConj τ hx]
  exact (τ ⟨x, hx⟩).2

theorem act_one (x : G) : act (1 : Gamma a ≃g Gamma a) x = x := by
  by_cases hx : IsConj a x
  · rw [act_of_isConj _ hx]
    rfl
  · classical
    simp only [act, dif_neg hx]

theorem act_mul (σ τ : Gamma a ≃g Gamma a) {x : G} (hx : IsConj a x) :
    act (σ * τ) x = act σ (act τ x) := by
  rw [act_of_isConj _ hx, act_of_isConj τ hx, act_of_isConj σ (τ ⟨x, hx⟩).2]
  rfl

theorem act_inv_act (τ : Gamma a ≃g Gamma a) {x : G} (hx : IsConj a x) :
    act τ⁻¹ (act τ x) = x := by
  rw [← act_mul _ _ hx, inv_mul_cancel, act_one]

theorem act_act_inv (τ : Gamma a ≃g Gamma a) {x : G} (hx : IsConj a x) :
    act τ (act τ⁻¹ x) = x := by
  rw [← act_mul _ _ hx, mul_inv_cancel, act_one]

theorem act_injOn (τ : Gamma a ≃g Gamma a) {x y : G} (hx : IsConj a x) (hy : IsConj a y)
    (h : act τ x = act τ y) : x = y := by
  rw [← act_inv_act τ hx, h, act_inv_act τ hy]

theorem eq_one_of_act (τ : Gamma a ≃g Gamma a) (h : ∀ x : G, IsConj a x → act τ x = x) :
    τ = 1 := by
  ext v
  have := h v v.2
  rw [act_vertex] at this
  exact congrArg (fun w : G => w) this

theorem adj_act_iff (τ : Gamma a ≃g Gamma a) {x y : G} (hx : IsConj a x) (hy : IsConj a y) :
    (act τ x ≠ act τ y ∧ IsConj a (act τ x * act τ y)) ↔ (x ≠ y ∧ IsConj a (x * y)) := by
  rw [act_of_isConj τ hx, act_of_isConj τ hy]
  have h := τ.map_rel_iff (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
  rw [gamma_adj_iff, gamma_adj_iff] at h
  simpa only [ne_eq, Subtype.ext_iff] using h

theorem act_gammaConj (g : G) {x : G} (hx : IsConj a x) : act (gammaConj a g) x = g * x * g⁻¹ := by
  rw [act_of_isConj _ hx]
  rfl

theorem mul_self_of_isConj (hF : IsF5Type a z) {x : G} (hx : IsConj a x) : x * x = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  have h2 : a * a = 1 := by rw [← sq, ← hF.orderOf_a]; exact pow_orderOf_eq_one a
  calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
    _ = 1 := by rw [h2]; group

theorem inv_eq_of_isConj (hF : IsF5Type a z) {x : G} (hx : IsConj a x) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (mul_self_of_isConj hF hx)

theorem ne_one_of_isConj (hF : IsF5Type a z) {x : G} (hx : IsConj a x) : x ≠ 1 := by
  rintro rfl
  have h1 : a = 1 := isConj_one_left.1 hx
  have := hF.orderOf_a
  rw [h1, orderOf_one] at this
  omega

theorem comm_of_adj (hF : IsF5Type a z) {x y : G} (hx : IsConj a x) (hy : IsConj a y)
    (hxy : IsConj a (x * y)) : x * y = y * x := by
  have h2 : x * y = (x * y)⁻¹ := (inv_eq_of_isConj hF hxy).symm
  rw [mul_inv_rev, inv_eq_of_isConj hF hx, inv_eq_of_isConj hF hy] at h2
  exact h2

theorem act_mem_gammaPerp (τ : Gamma a ≃g Gamma a) {S : Set G} (hS : ∀ q ∈ S, IsConj a q) {s : G}
    (hs : s ∈ gammaPerp a S) : act τ s ∈ gammaPerp a (act τ '' S) := by
  obtain ⟨hs1, hs2⟩ := hs
  refine ⟨isConj_act τ hs1, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  rcases hs2 q hq with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr ((adj_act_iff τ (hS q hq) hs1).2 h)

theorem gammaPerp_image (τ : Gamma a ≃g Gamma a) {S : Set G} (hS : ∀ q ∈ S, IsConj a q) :
    gammaPerp a (act τ '' S) = act τ '' gammaPerp a S := by
  ext s
  constructor
  · intro hs
    have hS' : ∀ q ∈ act τ '' S, IsConj a q := by
      rintro _ ⟨q, hq, rfl⟩
      exact isConj_act τ (hS q hq)
    have h1 := act_mem_gammaPerp τ⁻¹ hS' hs
    have h2 : act τ⁻¹ '' (act τ '' S) = S := by
      rw [Set.image_image]
      conv_rhs => rw [← Set.image_id S]
      exact Set.image_congr (fun q hq => act_inv_act τ (hS q hq))
    rw [h2] at h1
    exact ⟨act τ⁻¹ s, h1, act_act_inv τ hs.1⟩
  · rintro ⟨s', hs', rfl⟩
    exact act_mem_gammaPerp τ hS hs'

theorem act_mul_of_adj (hF : IsF5Type a z) (hlines : LinesFacts a z) (τ : Gamma a ≃g Gamma a)
    {x y : G} (hx : IsConj a x) (hy : IsConj a y) (hxy : IsConj a (x * y)) :
    act τ (x * y) = act τ x * act τ y := by
  have hne : x ≠ y := by
    rintro rfl
    rw [mul_self_of_isConj hF hx] at hxy
    exact ne_one_of_isConj hF hxy rfl
  have hadj := (adj_act_iff τ hx hy).2 ⟨hne, hxy⟩
  have hxy' : IsConj a (act τ x * act τ y) := hadj.2
  have hu := isConj_act τ hx
  have hv := isConj_act τ hy
  have hw := isConj_act τ hxy
  have h1 := hlines.unique_third x y hx hy hxy
  have h2 := hlines.unique_third (act τ x) (act τ y) hu hv hxy'
  have hmem : x * y ∈ {t | IsConj a t ∧ t ≠ x ∧ t ≠ y ∧ gammaPerp a {x, y, t} = {x, y, t}} := by
    rw [h1]; rfl
  obtain ⟨-, hne1, hne2, hperp⟩ := hmem
  have hS : ∀ q ∈ ({x, y, x * y} : Set G), IsConj a q := by
    intro q hq
    rcases hq with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hxy
  have himg : act τ '' ({x, y, x * y} : Set G) = {act τ x, act τ y, act τ (x * y)} := by
    simp only [Set.image_insert_eq, Set.image_singleton]
  have hperp' : gammaPerp a {act τ x, act τ y, act τ (x * y)} =
      {act τ x, act τ y, act τ (x * y)} := by
    rw [← himg, gammaPerp_image τ hS, hperp]
  have hmem' : act τ (x * y) ∈
      {t | IsConj a t ∧ t ≠ act τ x ∧ t ≠ act τ y ∧
        gammaPerp a {act τ x, act τ y, t} = {act τ x, act τ y, t}} := by
    refine ⟨hw, fun h => hne1 (act_injOn τ hxy hx h), fun h => hne2 (act_injOn τ hxy hy h), hperp'⟩
  rw [h2] at hmem'
  exact hmem'

theorem act_fix_mul (hF : IsF5Type a z) (hlines : LinesFacts a z) (τ : Gamma a ≃g Gamma a)
    {x y : G} (hx : IsConj a x) (hy : IsConj a y) (hxy : IsConj a (x * y)) (hfx : act τ x = x)
    (hfy : act τ y = y) : act τ (x * y) = x * y := by
  rw [act_mul_of_adj hF hlines τ hx hy hxy, hfx, hfy]

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
