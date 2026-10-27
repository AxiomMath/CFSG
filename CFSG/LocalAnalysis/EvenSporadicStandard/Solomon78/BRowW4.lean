module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowAbstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowComponent
public import CFSG.Monster.GMS.BabyCover

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

@[expose] def BabyF4Subgroup : Prop :=
  ∀ X : B, BabyInv 3 X → ∃ F : Subgroup B, F ≤ centralizer ({X} : Set B) ∧ IsSimpleGroup F ∧
    Nat.card F = 3311126603366400

theorem exists_noncomm_of_isSimpleGroup {F : Type*} [Group F] [Finite F] [IsSimpleGroup F]
    (h : ¬ (Nat.card F).Prime) : ∃ x y : F, x * y ≠ y * x := by
  by_contra hcon
  have hcomm : ∀ x y : F, x * y = y * x := fun x y => by
    by_contra hxy
    exact hcon ⟨x, y, hxy⟩
  let _ : CommGroup F := { ‹Group F› with mul_comm := hcomm }
  exact h (IsSimpleGroup.prime_card (α := F))

theorem commute_of_mul_self_eq_one_aux {Y : Type*} [Group Y] {r s : Y} (hr : r * r = 1)
    (hs : s * s = 1) (h : r * s * (r * s) = 1) : r * s = s * r := by
  have h1 : r * s = (r * s)⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hr, inv_eq_of_mul_eq_one_right hs]

theorem commute_of_conj_eq_aux {Y : Type*} [Group Y] {g a : Y} (h : g * a * g⁻¹ = a) :
    g * a = a * g :=
  mul_inv_eq_iff_eq_mul.1 h

theorem baby_mul_self_eq_one {x : B} (h : orderOf x = 2) : x * x = 1 :=
  mul_self_eq_one_of_orderOf_eq_two' (Y := B) h

theorem baby_ne_one {x : B} (h : orderOf x = 2) : x ≠ 1 :=
  ne_one_of_orderOf_eq_two (G := B) h

theorem centerInvAt_babyInv_three [Finite B] (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hF1 : BabyW1Commute) (hF : BabyF4Subgroup) {a : B} (ha : BabyInv 3 a) : CenterInvAt a := by
  obtain ⟨r, hr, -⟩ := hF1 a ha.1
  obtain ⟨-, hconj, hcard⟩ := hT4 r hr
  have hne : ({s : B | BabyInv 0 s ∧ BabyOrbit 1 r s} : Set B).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hcard 1]
    norm_num [babyOrbitSize]
  obtain ⟨s, hs, hrs⟩ := hne
  have hrs3 : BabyInv 3 (r * s) := hrs
  refine CenterInvAt.of_isConj (hT3.2 3 a (r * s) ha hrs3) ?_
  have hr2 : r * r = 1 := baby_mul_self_eq_one hr.1
  have hs2 : s * s = 1 := baby_mul_self_eq_one hs.1
  have hrsrs : r * s * (r * s) = 1 := baby_mul_self_eq_one hrs3.1
  have hcomm : r * s = s * r := commute_of_mul_self_eq_one_aux (Y := B) hr2 hs2 hrsrs
  have hrs_ne : r ≠ s := fun h => baby_ne_one hrs3.1 (by rw [← h]; exact hr2)
  obtain ⟨F, hFle, hFs, hFcard⟩ := hF (r * s) hrs3
  have hFnab : ∃ x y : F, x * y ≠ y * x := by
    have := hFs
    refine exists_noncomm_of_isSimpleGroup (F := F) ?_
    rw [hFcard]
    norm_num
  have hcardC : Nat.card (centralizer ({r * s} : Set B)) = 8 * Nat.card F := by
    rw [hrs3.2, hFcard]
    norm_num [babyCentOrder]
  have hcardD : Nat.card (centralizer ({r * s} : Set B)) =
      2 * Nat.card (centralizer ({r} : Set B) ⊓ centralizer ({s} : Set B) : Subgroup B) := by
    have horb : ({y | ∃ h ∈ centralizer ({r} : Set B), h * s * h⁻¹ = y} : Set B) =
        {y | BabyInv 0 y ∧ BabyOrbit 1 r y} := by
      ext y
      constructor
      · rintro ⟨h, hh, rfl⟩
        have hhr : h * r = r * h := (mem_centralizer_singleton_iff (G := B)).1 hh
        refine ⟨hs.of_isConj (isConj_iff.2 ⟨h, rfl⟩), ?_⟩
        show BabyInv 3 (r * (h * s * h⁻¹))
        refine hrs3.of_isConj (isConj_iff.2 ⟨h, ?_⟩)
        have e : h * r * h⁻¹ = r := by rw [hhr]; group
        calc h * (r * s) * h⁻¹ = (h * r * h⁻¹) * (h * s * h⁻¹) := by group
          _ = r * (h * s * h⁻¹) := by rw [e]
      · rintro ⟨hy, hyo⟩
        exact hconj 1 s y hs hy hrs hyo
    have hmul := card_inf_centralizer_mul_ncard_conj (centralizer ({r} : Set B)) s
    rw [horb, hcard 1, hr.2] at hmul
    rw [hrs3.2]
    norm_num [babyOrbitSize, babyCentOrder] at hmul ⊢
    omega
  have hswap : ∃ g, g * (r * s) = (r * s) * g ∧ g * r * g⁻¹ = s := by
    obtain ⟨c, hc⟩ := isConj_iff.1 (hT3.2 0 r s hr hs)
    have ht : BabyInv 0 (c * s * c⁻¹) := hs.of_isConj (isConj_iff.2 ⟨c, rfl⟩)
    have hst : BabyOrbit 1 s (c * s * c⁻¹) := by
      show BabyInv 3 (s * (c * s * c⁻¹))
      have e : s * (c * s * c⁻¹) = c * (r * s) * c⁻¹ := by rw [← hc]; group
      rw [e]
      exact hrs3.of_isConj (isConj_iff.2 ⟨c, rfl⟩)
    have hsr : BabyOrbit 1 s r := by
      show BabyInv 3 (s * r)
      rw [← hcomm]
      exact hrs3
    obtain ⟨g, hg, hgt⟩ := (hT4 s hs).2.1 1 (c * s * c⁻¹) r ht hr hst hsr
    have hgs : g * s = s * g := (mem_centralizer_singleton_iff (G := B)).1 hg
    have e1 : g * s * g⁻¹ = s := by rw [hgs]; group
    refine ⟨g * c, ?_, ?_⟩
    · have hconjrs : g * c * (r * s) * (g * c)⁻¹ = r * s := by
        calc g * c * (r * s) * (g * c)⁻¹
            = g * (c * r * c⁻¹) * (c * s * c⁻¹) * g⁻¹ := by group
          _ = g * s * (c * s * c⁻¹) * g⁻¹ := by rw [hc]
          _ = (g * s * g⁻¹) * (g * (c * s * c⁻¹) * g⁻¹) := by group
          _ = s * r := by rw [e1, hgt]
          _ = r * s := hcomm.symm
      exact commute_of_conj_eq_aux (Y := B) hconjrs
    · calc g * c * r * (g * c)⁻¹ = g * (c * r * c⁻¹) * g⁻¹ := by group
        _ = g * s * g⁻¹ := by rw [hc]
        _ = s := e1
  exact centerInvAt_of_simple_subgroup (baby_ne_one hr.1)
    (baby_ne_one hs.1) hrs_ne hr2 hs2 hcomm rfl hFnab hFle hcardC hcardD hswap

end CFSG.EvenSporadicStandard.Solomon78
