module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

namespace JankoPTwoThree

open Janko JankoInvolution

theorem ybar_mul_sbar₂_ne : ybar * sbar₂ ≠ sbar₂ * ybar := fun h =>
  absurd (congrArg Subtype.val h) (by decide)

theorem tbar_mul_ybar_mul_sbar₂_ne : tbar * ybar * sbar₂ ≠ sbar₂ * (tbar * ybar) := fun h =>
  absurd (congrArg Subtype.val h) (by decide)

theorem conj_ne_one {X : Type*} [Group X] {b s : X} (hs : s ≠ 1) : b * s * b⁻¹ ≠ 1 := fun h =>
  hs (mul_eq_left.mp (mul_inv_eq_one.mp h))

theorem odd_orderOf_sbar₂ : Odd (orderOf sbar₂) := by
  rw [orderOf_sbar₂]
  exact ⟨1, rfl⟩

theorem mem_normalizer_zpowers {X : Type*} [Group X] {g s : X} (h₁ : g * s * g⁻¹ ∈ zpowers s)
    (h₂ : g⁻¹ * s * g⁻¹⁻¹ ∈ zpowers s) : g ∈ normalizer (zpowers s : Set X) := by
  have key : ∀ c : X, c * s * c⁻¹ ∈ zpowers s → ∀ y ∈ zpowers s, c * y * c⁻¹ ∈ zpowers s := by
    intro c hc y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [← conj_zpow]
    exact zpow_mem hc k
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g h₁ y, fun hy => ?_⟩
  have := key g⁻¹ h₂ _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this

theorem mem_normalizer_zpowers_of_conj_eq_inv {X : Type*} [Group X] {g s : X}
    (h : g * s * g⁻¹ = s⁻¹) : g ∈ normalizer (zpowers s : Set X) := by
  refine mem_normalizer_zpowers (by rw [h]; exact inv_mem (mem_zpowers s)) ?_
  have h' : g⁻¹ * s * g⁻¹⁻¹ = s⁻¹ := by
    calc g⁻¹ * s * g⁻¹⁻¹ = g⁻¹ * (s⁻¹)⁻¹ * g := by rw [inv_inv, inv_inv]
      _ = g⁻¹ * (g * s * g⁻¹)⁻¹ * g := by rw [h]
      _ = s⁻¹ := by group
  rw [h']
  exact inv_mem (mem_zpowers s)

theorem mem_normalizer_zpowers_of_commute {X : Type*} [Group X] {g s : X} (h : g * s = s * g) :
    g ∈ normalizer (zpowers s : Set X) := by
  refine mem_normalizer_zpowers (by rw [h, mul_inv_cancel_right]; exact mem_zpowers s) ?_
  rw [show g⁻¹ * s * g⁻¹⁻¹ = s by rw [inv_inv, mul_assoc, ← h, inv_mul_cancel_left]]
  exact mem_zpowers s

variable {J : Type*} [Group J] (hJ : IsTwoANine J) (e : J ⧸ center J ≃* alternatingGroup (Fin 9))

theorem proj_someLift_ℓbar_sq : proj e (someLift e ℓbar ^ 2) = ybar := by
  rw [map_pow, proj_someLift, ℓbar_sq]

include hJ

theorem conj_liftOdd_sbar₂_eq_inv :
    someLift e ℓbar ^ 2 * liftOdd e sbar₂ * (someLift e ℓbar ^ 2)⁻¹ = (liftOdd e sbar₂)⁻¹ :=
  hJ.conj_liftOdd_eq_inv e odd_orderOf_sbar₂
    (by rw [proj_someLift_ℓbar_sq]; exact ybar_conj_sbar₂)

theorem card_normalizer_liftOdd_sbar₂ :
    Nat.card (normalizer (zpowers (liftOdd e sbar₂) : Set J)) = 216 := by
  set s := liftOdd e sbar₂
  have hs : orderOf s = 3 := hJ.orderOf_liftOdd_sbar₂ e
  have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs; exact absurd hs (by norm_num)
  have hne : s⁻¹ ≠ s := fun h => by
    have h2 : s ^ 2 = 1 := by
      rw [sq]
      nth_rw 2 [← h]
      exact mul_inv_cancel s
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hs] at this
    exact absurd this (by norm_num)
  have h : ∀ b ∈ normalizer (zpowers s : Set J), b * s * b⁻¹ = s ∨ b * s * b⁻¹ = s⁻¹ :=
    fun b hb => eq_or_eq_inv_of_mem_zpowers hs ((mem_normalizer_iff.mp hb s).mp (mem_zpowers s))
      (conj_ne_one hs1)
  have h2 := card_eq_two_mul_card_inf_centralizer hne h
    (mem_normalizer_zpowers_of_conj_eq_inv (conj_liftOdd_sbar₂_eq_inv hJ e))
    (conj_liftOdd_sbar₂_eq_inv hJ e)
  have hle : centralizer ({s} : Set J) ≤ normalizer (zpowers s : Set J) := by
    rw [← centralizer_closure, ← zpowers_eq_closure]
    exact centralizer_le_normalizer _
  rw [inf_eq_right.mpr hle, hJ.card_centralizer_liftOdd_sbar₂ e] at h2
  exact h2

theorem zbar_mem_closure_t_y :
    zbar J ∈ closure ({someLift e tbar, someLift e ℓbar ^ 2} : Set J) := by
  rw [← hJ.sq_eq_zbar_of_cycleType_two_two e (x := someLift e ℓbar ^ 2)
    (by rw [proj_someLift_ℓbar_sq]; exact cycleType_ybar)]
  exact pow_mem (subset_closure (by simp)) 2

omit hJ in
theorem map_closure_t_y :
    (closure ({someLift e tbar, someLift e ℓbar ^ 2} : Set J)).map (proj e) =
      closure {tbar, ybar} := by
  rw [MonoidHom.map_closure, Set.image_pair, proj_someLift, proj_someLift_ℓbar_sq]

theorem card_closure_t_y :
    Nat.card (closure ({someLift e tbar, someLift e ℓbar ^ 2} : Set J)) = 8 := by
  rw [card_eq_two_mul_card_map hJ e (zbar_mem_closure_t_y hJ e), map_closure_t_y,
    card_closure_tbar_ybar]

omit hJ in
theorem proj_mem_of_mem_closure_t_y {x : J}
    (hx : x ∈ closure ({someLift e tbar, someLift e ℓbar ^ 2} : Set J)) :
    proj e x = 1 ∨ proj e x = tbar ∨ proj e x = ybar ∨ proj e x = tbar * ybar :=
  mem_closure_tbar_ybar (by rw [← map_closure_t_y e]; exact mem_map_of_mem _ hx)

theorem eq_of_mem_center_closure_t_y {x : J}
    (hx : x ∈ closure ({someLift e tbar, someLift e ℓbar ^ 2} : Set J))
    (hc : ∀ w ∈ closure ({someLift e tbar, someLift e ℓbar ^ 2} : Set J), x * w = w * x) :
    x = 1 ∨ x = zbar J := by
  set t := someLift e tbar
  set y := someLift e ℓbar ^ 2
  have ht : t ∈ closure ({t, y} : Set J) := subset_closure (by simp)
  have hy : y ∈ closure ({t, y} : Set J) := subset_closure (by simp)
  have hyp : proj e y = ybar := proj_someLift_ℓbar_sq e
  have hz1 := hJ.zbar_ne_one
  rcases proj_mem_of_mem_closure_t_y e hx with h | h | h | h
  · exact hJ.mem_center_iff.mp ((proj_eq_one_iff e).mp h)
  · have h1 := conj_eq_mul_zbar_of_proj_eq_ybar hJ e hyp h
    rw [← hc y hy, mul_inv_cancel_right] at h1
    exact absurd (mul_eq_left.mp h1.symm) hz1
  · have h1 := conj_eq_mul_zbar_of_proj_eq_ybar hJ e h (proj_someLift e tbar)
    rw [hc t ht, mul_inv_cancel_right] at h1
    exact absurd (mul_eq_left.mp h1.symm) hz1
  · have hxy : proj e (x * y⁻¹) = tbar := by
      rw [map_mul, map_inv, h, hyp, mul_inv_cancel_right]
    have h1 := conj_eq_mul_zbar_of_proj_eq_ybar hJ e hyp hxy
    rw [show y * (x * y⁻¹) * y⁻¹ = y * x * y⁻¹ * y⁻¹ by group, ← hc y hy,
      mul_inv_cancel_right] at h1
    exact absurd (mul_eq_left.mp h1.symm) hz1

theorem closure_t_y_inf_centralizer :
    closure ({someLift e tbar, someLift e ℓbar ^ 2} : Set J) ⊓ centralizer {liftOdd e sbar₂} =
      closure {someLift e tbar, zbar J} := by
  set t := someLift e tbar
  have hts : t * liftOdd e sbar₂ = liftOdd e sbar₂ * t :=
    (mem_centralizer_singleton_iff.mp
      (liftOdd_sbar₂_mem_centralizer hJ e (proj_someLift e tbar))).symm
  refine le_antisymm (fun x hx => ?_) ((closure_le _).mpr ?_)
  · obtain ⟨hxD, hxs⟩ := mem_inf.mp hx
    have hcomm : proj e x * sbar₂ = sbar₂ * proj e x := by
      have h := congrArg (proj e) (mem_centralizer_singleton_iff.mp hxs)
      rwa [map_mul, map_mul, hJ.proj_liftOdd e odd_orderOf_sbar₂] at h
    have hz : zbar J ∈ closure ({t, zbar J} : Set J) := subset_closure (by simp)
    have ht : t ∈ closure ({t, zbar J} : Set J) := subset_closure (by simp)
    rcases proj_mem_of_mem_closure_t_y e hxD with h | h | h | h
    · rcases hJ.mem_center_iff.mp ((proj_eq_one_iff e).mp h) with rfl | rfl
      · exact one_mem _
      · exact hz
    · rcases (hJ.proj_eq_proj_iff' e).mp ((proj_someLift e tbar).trans h.symm) with rfl | rfl
      · exact ht
      · exact mul_mem ht hz
    · rw [h] at hcomm
      exact absurd hcomm ybar_mul_sbar₂_ne
    · rw [h] at hcomm
      exact absurd hcomm tbar_mul_ybar_mul_sbar₂_ne
  · rintro x (rfl | rfl)
    · exact ⟨subset_closure (by simp), mem_centralizer_singleton_iff.mpr hts⟩
    · exact ⟨zbar_mem_closure_t_y hJ e,
        mem_centralizer_singleton_iff.mpr (hJ.commute_zbar _).eq.symm⟩

end JankoPTwoThree

namespace Janko

open JankoPTwoThree JankoInvolution

variable {G : Type*} [Group G] {z : G} (hH : IsTwoANine (centralizer ({z} : Set G)))
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))

private theorem closure_t_ℓ_sq_eq_map : closure {t e, ℓ e ^ 2} =
    (closure ({someLift e tbar, someLift e ℓbar ^ 2} : Set (centralizer ({z} : Set G)))).map
      (centralizer ({z} : Set G)).subtype := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

include hH

theorem D_le_normalizer : closure {t e, ℓ e ^ 2} ≤ normalizer (zpowers (s₂ e) : Set G) := by
  rw [closure_le]
  rintro x (rfl | rfl)
  · refine mem_normalizer_zpowers_of_commute ?_
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp
      (liftOdd_sbar₂_mem_centralizer hH e (proj_someLift e tbar))).symm
  · exact mem_normalizer_zpowers_of_conj_eq_inv
      (congrArg Subtype.val (conj_liftOdd_sbar₂_eq_inv hH e))

theorem card_normalizer_P₂ :
    Nat.card (normalizer (zpowers (s₂ e) : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) =
      216 := by
  rw [show zpowers (s₂ e) = (zpowers (liftOdd e sbar₂)).map (centralizer ({z} : Set G)).subtype
      by rw [MonoidHom.map_zpowers]; rfl,
    normalizer_map_inf_eq_map_subtype,
    card_map_of_injective (centralizer ({z} : Set G)).subtype_injective,
    card_normalizer_liftOdd_sbar₂ hH e]

theorem card_D : Nat.card (closure {t e, ℓ e ^ 2}) = 8 := by
  rw [closure_t_ℓ_sq_eq_map, card_map_of_injective (centralizer ({z} : Set G)).subtype_injective,
    card_closure_t_y hH e]

theorem D_center (hz : orderOf z = 2) : ∀ x ∈ closure {t e, ℓ e ^ 2},
    (∀ y ∈ closure {t e, ℓ e ^ 2}, x * y = y * x) → x = 1 ∨ x = z := by
  rw [closure_t_ℓ_sq_eq_map]
  rintro _ ⟨x, hx, rfl⟩ hc
  rcases eq_of_mem_center_closure_t_y hH e hx
    (fun w hw => Subtype.ext (hc _ ⟨w, hw, rfl⟩)) with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (coe_zbar_eq hz hH)

theorem D_inf_centralizer (hz : orderOf z = 2) :
    closure {t e, ℓ e ^ 2} ⊓ centralizer (zpowers (s₂ e) : Set G) = closure {t e, z} := by
  rw [closure_t_ℓ_sq_eq_map, zpowers_eq_closure, centralizer_closure,
    show s₂ e = ((liftOdd e sbar₂ : centralizer ({z} : Set G)) : G) from rfl,
    map_subtype_inf_centralizer, closure_t_y_inf_centralizer hH e, MonoidHom.map_closure,
    Set.image_pair, coe_subtype, coe_zbar_eq hz hH]
  rfl

end Janko

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
