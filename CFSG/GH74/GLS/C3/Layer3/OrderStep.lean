module

public import CFSG.Quasithin.Recognition.F4Fusion
public import CFSG.GH74.GLS.C3.Layer3.PatternClasses
public import CFSG.GH74.GLS.C3.Layer3.AltInvolutions

public section

namespace CFSG.GH74.GLS.Layer3

open Subgroup

theorem card_centralizer_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (a : X) :
    Nat.card (centralizer ({e a} : Set Y)) = Nat.card (centralizer ({a} : Set X)) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun z => ⟨e.symm z.1, ?_⟩
      invFun := fun z => ⟨e z.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hz := mem_centralizer_singleton_iff.1 z.2
    rw [mem_centralizer_singleton_iff]
    apply e.injective
    simpa using hz
  · have hz := mem_centralizer_singleton_iff.1 z.2
    rw [mem_centralizer_singleton_iff]
    simpa using congrArg e hz
  · intro z; ext; simp
  · intro z; ext; simp

theorem centralizer_le_of_card_eq {G : Type*} [Group G] [Finite G] (G₀ : Subgroup G) (x₀ : G₀)
    (hcard : Nat.card (centralizer ({(x₀ : G)} : Set G)) =
      Nat.card (centralizer ({x₀} : Set G₀))) :
    centralizer ({(x₀ : G)} : Set G) ≤ G₀ ∧
      (centralizer ({x₀} : Set G₀)).map G₀.subtype = centralizer ({(x₀ : G)} : Set G) := by
  have hle : (centralizer ({x₀} : Set G₀)).map G₀.subtype ≤ centralizer ({(x₀ : G)} : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    have := mem_centralizer_singleton_iff.1 hz
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val this
  have hcard' : Nat.card ((centralizer ({x₀} : Set G₀)).map G₀.subtype) =
      Nat.card (centralizer ({x₀} : Set G₀)) :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ _ G₀.subtype_injective).toEquiv.symm
  have heq : (centralizer ({x₀} : Set G₀)).map G₀.subtype = centralizer ({(x₀ : G)} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard', hcard])
  refine ⟨?_, heq⟩
  intro z hz
  rw [← heq] at hz
  obtain ⟨w, -, rfl⟩ := hz
  exact w.2

theorem eq_top_of_mulEquiv_alt {n : ℕ} (hn9 : 9 ≤ n) (hn11 : n ≤ 11) {G : Type*} [Group G]
    [Finite G] (hP : SameCentralizerOfInvolutionPattern G (alternatingGroup (Fin n)))
    (G₀ : Subgroup G) (e : G₀ ≃* alternatingGroup (Fin n)) : G₀ = ⊤ := by
  obtain ⟨a, b, ha, hb, hab, hcl, hnd1, hnd2⟩ := alt_involution_classes hn9 hn11
  obtain ⟨x, y, hx, hy, hxy, hclG, hcx, hcy⟩ := pattern_two_classes_card hP ha hb hab hcl
  set x₀ : G₀ := e.symm a with hx₀
  set y₀ : G₀ := e.symm b with hy₀
  have hex₀ : e x₀ = a := e.apply_symm_apply a
  have hey₀ : e y₀ = b := e.apply_symm_apply b
  have hx₀o : orderOf x₀ = 2 := by rw [← MulEquiv.orderOf_eq e, hex₀]; exact ha
  have hy₀o : orderOf y₀ = 2 := by rw [← MulEquiv.orderOf_eq e, hey₀]; exact hb
  have hx₀Go : orderOf (x₀ : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx₀o
  have hy₀Go : orderOf (y₀ : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy₀o
  have hxy₀ : ¬ IsConj x₀ y₀ := fun h => hab (by rw [← hex₀, ← hey₀]; exact (isConj_map_iff e).2 h)
  have hcl₀ : ∀ w : G₀, orderOf w = 2 → IsConj x₀ w ∨ IsConj y₀ w := by
    intro w hw
    have hw' : orderOf (e w) = 2 := by rw [MulEquiv.orderOf_eq]; exact hw
    rcases hcl _ hw' with h | h
    · left; rw [← hex₀] at h; exact (isConj_map_iff e).1 h
    · right; rw [← hey₀] at h; exact (isConj_map_iff e).1 h
  have hcX : Nat.card (centralizer ({x₀} : Set G₀)) =
      Nat.card (centralizer ({a} : Set (alternatingGroup (Fin n)))) := by
    rw [← card_centralizer_mulEquiv e x₀, hex₀]
  have hcY : Nat.card (centralizer ({y₀} : Set G₀)) =
      Nat.card (centralizer ({b} : Set (alternatingGroup (Fin n)))) := by
    rw [← card_centralizer_mulEquiv e y₀, hey₀]
  have hdvd : ∀ z : G₀, Nat.card (centralizer ({z} : Set G₀)) ∣
      Nat.card (centralizer ({(z : G)} : Set G)) := by
    intro z
    have hle : (centralizer ({z} : Set G₀)).map G₀.subtype ≤ centralizer ({(z : G)} : Set G) := by
      rintro _ ⟨w, hw, rfl⟩
      have := mem_centralizer_singleton_iff.1 hw
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val this
    have hcard' : Nat.card ((centralizer ({z} : Set G₀)).map G₀.subtype) =
        Nat.card (centralizer ({z} : Set G₀)) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ G₀.subtype_injective).toEquiv.symm
    rw [← hcard']
    exact Subgroup.card_dvd_of_le hle
  have hx₀x : IsConj x (x₀ : G) := by
    rcases hclG _ hx₀Go with h | h
    · exact h
    · exfalso
      have := hdvd x₀
      rw [← card_centralizer_eq_of_isConj h, hcy, hcX] at this
      exact hnd1 this
  have hy₀y : IsConj y (y₀ : G) := by
    rcases hclG _ hy₀Go with h | h
    · exfalso
      have := hdvd y₀
      rw [← card_centralizer_eq_of_isConj h, hcx, hcY] at this
      exact hnd2 this
    · exact h
  have hcardX : Nat.card (centralizer ({(x₀ : G)} : Set G)) =
      Nat.card (centralizer ({x₀} : Set G₀)) := by
    rw [← card_centralizer_eq_of_isConj hx₀x, hcx, hcX]
  have hcardY : Nat.card (centralizer ({(y₀ : G)} : Set G)) =
      Nat.card (centralizer ({y₀} : Set G₀)) := by
    rw [← card_centralizer_eq_of_isConj hy₀y, hcy, hcY]
  obtain ⟨hleX, -⟩ := centralizer_le_of_card_eq G₀ x₀ hcardX
  obtain ⟨hleY, -⟩ := centralizer_le_of_card_eq G₀ y₀ hcardY
  have hxy' : ¬ IsConj (x₀ : G) (y₀ : G) := fun h => hxy (hx₀x.trans (h.trans hy₀y.symm))
  have hclG' : ∀ w : G, orderOf w = 2 → IsConj (x₀ : G) w ∨ IsConj (y₀ : G) w := by
    intro w hw
    rcases hclG w hw with h | h
    · exact Or.inl (hx₀x.symm.trans h)
    · exact Or.inr (hy₀y.symm.trans h)
  have hconjG : ∀ w : G₀, orderOf w = 2 → (IsConj (x₀ : G) (w : G) ↔ IsConj x₀ w) := by
    intro w hw
    refine ⟨fun h => ?_, fun h => G₀.subtype.map_isConj h⟩
    rcases hcl₀ w hw with h' | h'
    · exact h'
    · exact absurd (h.trans (G₀.subtype.map_isConj h').symm) hxy'
  have hrange : ∀ (z₀ : G₀) (hle : centralizer ({(z₀ : G)} : Set G) ≤ G₀),
      (Subgroup.inclusion hle).range = centralizer ({z₀} : Set G₀) := by
    intro z₀ hle
    ext w
    rw [MonoidHom.mem_range, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨z, rfl⟩
      have := mem_centralizer_singleton_iff.1 z.2
      exact Subtype.ext this
    · intro h
      refine ⟨⟨(w : G), ?_⟩, rfl⟩
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val h
  have hX := CFSG.Quasithin.card_eq_of_two_class_data (t := (x₀ : G)) (u := (y₀ : G)) (t' := x₀) (u' := y₀)
    hx₀Go hy₀Go hxy' hclG' hx₀o hy₀o hxy₀ hcl₀ (Subgroup.inclusion hleX)
    (Subgroup.inclusion_injective hleX) (hrange x₀ hleX) (fun h => rfl) ?_
    (Subgroup.inclusion hleY) (Subgroup.inclusion_injective hleY) (hrange y₀ hleY)
    (fun h => rfl) ?_
  · exact (Subgroup.card_eq_iff_eq_top G₀).1 (by simpa using hX.symm)
  · intro z hz
    have hz2 : orderOf z = 2 := by rw [← Subgroup.orderOf_coe]; exact hz
    have hz' : orderOf (Subgroup.inclusion hleX z) = 2 := by
      rw [orderOf_injective _ (Subgroup.inclusion_injective hleX) z]; exact hz2
    exact hconjG _ hz'
  · intro z hz
    have hz2 : orderOf z = 2 := by rw [← Subgroup.orderOf_coe]; exact hz
    have hz' : orderOf (Subgroup.inclusion hleY z) = 2 := by
      rw [orderOf_injective _ (Subgroup.inclusion_injective hleY) z]; exact hz2
    exact hconjG _ hz'


theorem nonempty_mulEquiv_of_subgroup_alt {n : ℕ} (hn9 : 9 ≤ n) (hn11 : n ≤ 11) {G : Type*}
    [Group G] [Finite G] (hP : SameCentralizerOfInvolutionPattern G (alternatingGroup (Fin n)))
    (G₀ : Subgroup G) (e : G₀ ≃* alternatingGroup (Fin n)) :
    Nonempty (G ≃* alternatingGroup (Fin n)) := by
  have h := eq_top_of_mulEquiv_alt hn9 hn11 hP G₀ e
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr h.symm)).trans e⟩

end CFSG.GH74.GLS.Layer3
