module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Omega
public import CFSG.ClassicalGroups.Orthogonal.Lines

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.Sec2Omega

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal MulAction

theorem eichler_apply_qMinus {u w : Fin 6 → ZMod 2} (hu : qMinus u = 0)
    (hw : polarMinus u w = 0) (x : Fin 6 → ZMod 2) :
    eichler qMinusForm u w x =
      x + polarMinus x u • w + (polarMinus x w + qMinus w * polarMinus x u) • u := by
  rw [eichler_apply (by rwa [qMinusForm_apply]) (by rwa [polar_qMinusForm]), polar_qMinusForm,
    polar_qMinusForm, qMinusForm_apply, sub_eq_add_neg, ← neg_smul, ZMod.neg_eq_self_mod_two]

theorem eichler_mem_of_map_eq_one {u w : Fin 6 → ZMod 2} (hu : qMinus u = 0)
    (huw : polarMinus u w = 0) (hw : qMinus w = 1) :
    eichler qMinusForm u w ∈ Open.timmesfeldOmega qMinus := by
  rw [eichler_eq_reflect_mul_reflect (by decide) (by rwa [qMinusForm_apply])
    (by rwa [polar_qMinusForm]) (by rwa [qMinusForm_apply])]
  refine reflect_mul_reflect_mem_timmesfeldOmega hw ?_
  rw [← qMinusForm_apply, QuadraticMap.map_add qMinusForm w u, qMinusForm_apply,
    qMinusForm_apply, hw, hu, QuadraticMap.polar_comm, polar_qMinusForm, huw]
  decide

theorem eichler_mem_timmesfeldOmega (u w : Fin 6 → ZMod 2) :
    eichler qMinusForm u w ∈ Open.timmesfeldOmega qMinus := by
  by_cases h : qMinusForm u = 0 ∧ QuadraticMap.polar qMinusForm u w = 0
  · obtain ⟨hu, huw⟩ := h
    rw [qMinusForm_apply] at hu
    rw [polar_qMinusForm] at huw
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (qMinus w) with hw | hw
    · obtain ⟨a, hua, hwa, ha⟩ := exists_polar_eq_zero_map_ne_zero qMinusForm_nondegenerate
        (by rw [finrank_fin_six]; norm_num) u w
      rw [polar_qMinusForm] at hua hwa
      have ha1 : qMinus a = 1 := by
        rw [← qMinusForm_apply]
        exact zmod_two_eq_one_of_ne_zero ha
      have hwa1 : qMinus (w + a) = 1 := by
        rw [← qMinusForm_apply, QuadraticMap.map_add qMinusForm w a, qMinusForm_apply,
          qMinusForm_apply, hw, ha1, polar_qMinusForm, hwa]
        decide
      have huwa : polarMinus u (w + a) = 0 := by
        rw [← polar_qMinusForm, QuadraticMap.polar_add_right, polar_qMinusForm, polar_qMinusForm,
          huw, hua, add_zero]
      have h2a : a + a = 0 := by
        funext k
        exact CharTwo.add_self_eq_zero (a k)
      have e : eichler qMinusForm u w = eichler qMinusForm u a * eichler qMinusForm u (w + a) := by
        rw [eichler_mul (by rwa [polar_qMinusForm]) (by rwa [polar_qMinusForm])]
        congr 1
        rw [add_comm a (w + a), add_assoc, h2a, add_zero]
      rw [e]
      exact mul_mem (eichler_mem_of_map_eq_one hu hua ha1) (eichler_mem_of_map_eq_one hu huwa hwa1)
    · exact eichler_mem_of_map_eq_one hu huw hw
  · rw [eichler_of_not h]
    exact one_mem _

theorem elementaryGroup_le_timmesfeldOmega :
    elementaryGroup qMinusForm ≤ Open.timmesfeldOmega qMinus :=
  elementaryGroup_le_of_eichler_mem fun u w _ _ => eichler_mem_timmesfeldOmega u w

theorem timmesfeldOmega_le_orthogonalGroup :
    Open.timmesfeldOmega qMinus ≤ TauCeti.QuadraticMap.orthogonalGroup qMinusForm := by
  rw [timmesfeldOmega_qMinus, Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem qMinus_apply_of_mem {g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)}
    (hg : g ∈ Open.timmesfeldOmega qMinus) (v : Fin 6 → ZMod 2) : qMinus (g v) = qMinus v := by
  rw [← qMinusForm_apply, map_of_mem (timmesfeldOmega_le_orthogonalGroup hg), qMinusForm_apply]

theorem polarMinus_apply_of_mem {g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)}
    (hg : g ∈ Open.timmesfeldOmega qMinus) (u v : Fin 6 → ZMod 2) :
    polarMinus (g u) (g v) = polarMinus u v := by
  rw [← polar_qMinusForm, polar_map_of_mem (timmesfeldOmega_le_orthogonalGroup hg),
    polar_qMinusForm]

theorem exists_mem_timmesfeldOmega_apply_eq {v w : Fin 6 → ZMod 2} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : qMinus v = qMinus w) : ∃ g ∈ Open.timmesfeldOmega qMinus, g v = w := by
  obtain ⟨g, hg, hgv⟩ := exists_mem_elementaryGroup_apply_eq (Q := qMinusForm)
    (P := ⟨![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], by rw [qMinusForm_apply]; decide,
      by rw [qMinusForm_apply]; decide, by rw [polar_qMinusForm]; decide⟩)
    (P' := ⟨![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], by rw [qMinusForm_apply]; decide,
      by rw [qMinusForm_apply]; decide, by rw [polar_qMinusForm]; decide⟩)
    qMinusForm_nondegenerate
    ⟨(by rw [polar_qMinusForm]; decide), (by rw [polar_qMinusForm]; decide),
      (by rw [polar_qMinusForm]; decide), (by rw [polar_qMinusForm]; decide)⟩
    hv hw (by rw [qMinusForm_apply, qMinusForm_apply, hvw])
  exact ⟨g, elementaryGroup_le_timmesfeldOmega hg, hgv⟩

theorem ncard_qMinusForm_eq_zero : {v : Fin 6 → ZMod 2 | qMinusForm v = 0}.ncard = 28 := by
  rw [show {v : Fin 6 → ZMod 2 | qMinusForm v = 0} =
      ↑(Finset.univ.filter fun v : Fin 6 → ZMod 2 => qMinus v = 0) by
    ext v
    simp [qMinusForm_apply], Set.ncard_coe_finset]
  decide +kernel

theorem card_timmesfeldOmega : Nat.card (Open.timmesfeldOmega qMinus) = 25920 := by
  have h1 := LargeExtraspecial.S12DW.card_orthogonalGroup_mul_ncard_eq qMinusForm_nondegenerate
    (m := 3) (by rw [finrank_fin_six])
  have h3 : 2 ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, (2 ^ (2 * j) - 1) = 1451520 := by decide
  rw [ncard_qMinusForm_eq_zero, h3] at h1
  have h2 := LargeExtraspecial.S12DW.card_orthogonalGroup_eq qMinusForm_nondegenerate
  have h4 : Open.timmesfeldOmega qMinus =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup qMinusForm qMinusForm_nondegenerate := by
    rw [← coe_qMinusForm]
    exact LargeExtraspecial.s12_timmesfeldOmega_eq _ _
  rw [h4]
  omega

theorem ncard_singular : {v : Fin 6 → ZMod 2 | v ≠ 0 ∧ qMinus v = 0}.ncard = 27 := by
  rw [show {v : Fin 6 → ZMod 2 | v ≠ 0 ∧ qMinus v = 0} =
      ↑(Finset.univ.filter fun v : Fin 6 → ZMod 2 => v ≠ 0 ∧ qMinus v = 0) by
    ext v
    simp, Set.ncard_coe_finset]
  decide +kernel

theorem orbit_eq {p : Fin 6 → ZMod 2} (hp : p ≠ 0) (hq : qMinus p = 0) :
    orbit ↥(Open.timmesfeldOmega qMinus) p = {v | v ≠ 0 ∧ qMinus v = 0} := by
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨fun h => hp ?_, ?_⟩
    · exact ((g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)).map_eq_zero_iff).mp h
    · change qMinus ((g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) p) = 0
      rw [qMinus_apply_of_mem g.2, hq]
  · rintro ⟨hv, hvq⟩
    obtain ⟨g, hg, hgv⟩ := exists_mem_timmesfeldOmega_apply_eq hp hv (by rw [hq, hvq])
    exact ⟨⟨g, hg⟩, hgv⟩

theorem card_stabilizer {p : Fin 6 → ZMod 2} (hp : p ≠ 0) (hq : qMinus p = 0) :
    Nat.card (stabilizer ↥(Open.timmesfeldOmega qMinus) p) = 960 := by
  have h1 := index_stabilizer ↥(Open.timmesfeldOmega qMinus) p
  rw [orbit_eq hp hq, ncard_singular] at h1
  have h2 := Subgroup.card_mul_index (stabilizer ↥(Open.timmesfeldOmega qMinus) p)
  rw [h1, card_timmesfeldOmega] at h2
  omega

theorem exists_mem_fix_apply_eq_of_polar_ne_zero {e x y : Fin 6 → ZMod 2} (he : qMinus e = 0)
    (hx : qMinus x = 0) (hy : qMinus y = 0) (hex : polarMinus e x ≠ 0)
    (hey : polarMinus e y ≠ 0) :
    ∃ g ∈ Open.timmesfeldOmega qMinus, g e = e ∧ g x = y := by
  obtain ⟨g, hg, hge, c, hgc⟩ := exists_fix_apply_eq_smul_of_polar_ne_zero (Q := qMinusForm)
    (e := e) (x := x) (y := y) (by rwa [qMinusForm_apply]) (by rwa [qMinusForm_apply])
    (by rwa [qMinusForm_apply]) (by rwa [polar_qMinusForm]) (by rwa [polar_qMinusForm])
  refine ⟨g, elementaryGroup_le_timmesfeldOmega hg, hge, ?_⟩
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one c with rfl | rfl
  · exfalso
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at hgc
    apply hex
    rw [hgc]
    simp [polarMinus]
  · rwa [one_smul] at hgc

theorem eq_ten {q : Fin 6 → ZMod 2} (hq : qMinus q = 0) (hpol : polarMinus ![1, 0, 0, 0, 0, 0] q = 0)
    (h0 : q ≠ 0) (h1 : q ≠ ![1, 0, 0, 0, 0, 0]) :
    q = ![0, 0, 0, 1, 0, 0] ∨ q = ![0, 0, 1, 1, 1, 0] ∨ q = ![0, 0, 1, 1, 0, 1] ∨
      q = ![0, 0, 1, 1, 1, 1] ∨ q = ![0, 0, 1, 0, 0, 0] ∨ q = ![1, 0, 0, 1, 0, 0] ∨
      q = ![1, 0, 1, 1, 1, 0] ∨ q = ![1, 0, 1, 1, 0, 1] ∨ q = ![1, 0, 1, 1, 1, 1] ∨
      q = ![1, 0, 1, 0, 0, 0] := by
  revert q
  decide

theorem exists_mem_fix_apply_eq_e₃ {q : Fin 6 → ZMod 2} (hq : qMinus q = 0)
    (hpol : polarMinus ![1, 0, 0, 0, 0, 0] q = 0) (h0 : q ≠ 0) (h1 : q ≠ ![1, 0, 0, 0, 0, 0]) :
    ∃ g ∈ Open.timmesfeldOmega qMinus, g ![1, 0, 0, 0, 0, 0] = ![1, 0, 0, 0, 0, 0] ∧
      g ![0, 0, 0, 1, 0, 0] = q := by
  have hE : ∀ u w : Fin 6 → ZMod 2, eichler qMinusForm u w ∈ Open.timmesfeldOmega qMinus :=
    eichler_mem_timmesfeldOmega
  have ev : ∀ (u w x : Fin 6 → ZMod 2), qMinus u = 0 → polarMinus u w = 0 →
      eichler qMinusForm u w x =
        x + polarMinus x u • w + (polarMinus x w + qMinus w * polarMinus x u) • u :=
    fun u w x hu hw => eichler_apply_qMinus hu hw x
  rcases eq_ten hq hpol h0 h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, rfl, rfl⟩
  · refine ⟨eichler qMinusForm ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 1, 0], hE _ _, ?_, ?_⟩ <;>
      rw [ev ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 1, 0] _ (by decide) (by decide)] <;> decide
  · refine ⟨eichler qMinusForm ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 0, 1], hE _ _, ?_, ?_⟩ <;>
      rw [ev ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 0, 1] _ (by decide) (by decide)] <;> decide
  · refine ⟨eichler qMinusForm ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 1, 1], hE _ _, ?_, ?_⟩ <;>
      rw [ev ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 1, 1] _ (by decide) (by decide)] <;> decide
  · refine ⟨eichler qMinusForm ![0, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 1, 0] *
      eichler qMinusForm ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 1, 0], mul_mem (hE _ _) (hE _ _), ?_,
      ?_⟩ <;> rw [LinearEquiv.mul_apply,
        ev ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 1, 0] _ (by decide) (by decide),
        ev ![0, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 1, 0] _ (by decide) (by decide)] <;> decide
  · refine ⟨eichler qMinusForm ![1, 0, 0, 0, 0, 0] ![0, 0, 1, 0, 1, 0], hE _ _, ?_, ?_⟩ <;>
      rw [ev ![1, 0, 0, 0, 0, 0] ![0, 0, 1, 0, 1, 0] _ (by decide) (by decide)] <;> decide
  · refine ⟨eichler qMinusForm ![1, 0, 0, 0, 0, 0] ![0, 0, 1, 0, 1, 0] *
      eichler qMinusForm ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 1, 0], mul_mem (hE _ _) (hE _ _), ?_,
      ?_⟩ <;> rw [LinearEquiv.mul_apply,
        ev ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 1, 0] _ (by decide) (by decide),
        ev ![1, 0, 0, 0, 0, 0] ![0, 0, 1, 0, 1, 0] _ (by decide) (by decide)] <;> decide
  · refine ⟨eichler qMinusForm ![1, 0, 0, 0, 0, 0] ![0, 0, 1, 0, 0, 1] *
      eichler qMinusForm ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 0, 1], mul_mem (hE _ _) (hE _ _), ?_,
      ?_⟩ <;> rw [LinearEquiv.mul_apply,
        ev ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 0, 1] _ (by decide) (by decide),
        ev ![1, 0, 0, 0, 0, 0] ![0, 0, 1, 0, 0, 1] _ (by decide) (by decide)] <;> decide
  · refine ⟨eichler qMinusForm ![1, 0, 0, 0, 0, 0] ![0, 0, 1, 0, 1, 1] *
      eichler qMinusForm ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 1, 1], mul_mem (hE _ _) (hE _ _), ?_,
      ?_⟩ <;> rw [LinearEquiv.mul_apply,
        ev ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 1, 1] _ (by decide) (by decide),
        ev ![1, 0, 0, 0, 0, 0] ![0, 0, 1, 0, 1, 1] _ (by decide) (by decide)] <;> decide
  · refine ⟨eichler qMinusForm ![1, 0, 0, 0, 0, 0] ![0, 0, 0, 1, 1, 0] *
      (eichler qMinusForm ![0, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 1, 0] *
        eichler qMinusForm ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 1, 0]),
      mul_mem (hE _ _) (mul_mem (hE _ _) (hE _ _)), ?_, ?_⟩ <;>
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        ev ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 1, 0] _ (by decide) (by decide),
        ev ![0, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 1, 0] _ (by decide) (by decide),
        ev ![1, 0, 0, 0, 0, 0] ![0, 0, 0, 1, 1, 0] _ (by decide) (by decide)] <;> decide

theorem card_sixteen :
    (insert ![1, 0, 0, 0, 0, 0] (Finset.univ.filter fun y : Fin 6 → ZMod 2 =>
      qMinus y = 0 ∧ polarMinus ![1, 0, 0, 0, 0, 0] y ≠ 0)).card = 17 := by
  decide +kernel

theorem card_ten :
    (insert ![1, 0, 0, 0, 0, 0] (Finset.univ.filter fun y : Fin 6 → ZMod 2 =>
      qMinus y = 0 ∧ polarMinus ![1, 0, 0, 0, 0, 0] y = 0 ∧ y ≠ 0 ∧
        y ≠ ![1, 0, 0, 0, 0, 0])).card = 11 := by
  decide +kernel

theorem inv_apply_eq_of_apply_eq {x : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)}
    {v : Fin 6 → ZMod 2} (h : x v = v) : x⁻¹ v = v := by
  conv_lhs => rw [← h]
  rw [← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id]

theorem eq_of_stabilizer_le_e₀ {Y : Subgroup ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))}
    (hYΩ : Y ≤ Open.timmesfeldOmega qMinus)
    (hXY : ∀ h ∈ Open.timmesfeldOmega qMinus,
      h ![1, 0, 0, 0, 0, 0] = ![1, 0, 0, 0, 0, 0] → h ∈ Y)
    {g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)} (hgY : g ∈ Y)
    (hg : g ![1, 0, 0, 0, 0, 0] ≠ ![1, 0, 0, 0, 0, 0]) : Y = Open.timmesfeldOmega qMinus := by
  classical
  have : Finite ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :=
    Finite.of_injective (fun f : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) => (f : _ → _))
      fun _ _ h => LinearEquiv.ext (congrFun h)
  have he₀0 : (![1, 0, 0, 0, 0, 0] : Fin 6 → ZMod 2) ≠ 0 := by decide
  have he₀q : qMinus ![1, 0, 0, 0, 0, 0] = 0 := by decide
  set B := orbit ↥Y (![1, 0, 0, 0, 0, 0] : Fin 6 → ZMod 2) with hB
  have hstab : Nat.card (stabilizer ↥Y (![1, 0, 0, 0, 0, 0] : Fin 6 → ZMod 2)) = 960 := by
    rw [← card_stabilizer he₀0 he₀q]
    exact Nat.card_congr
      { toFun := fun h => ⟨⟨h.1.1, hYΩ h.1.2⟩, h.2⟩
        invFun := fun h => ⟨⟨h.1.1, hXY h.1.1 h.1.2 h.2⟩, h.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcard : 960 * B.ncard = Nat.card Y := by
    rw [← hstab, hB, ← index_stabilizer]
    exact Subgroup.card_mul_index _
  have hdvd : Nat.card Y ∣ 960 * 27 := by
    have h1 := Subgroup.card_dvd_of_le hYΩ
    rw [card_timmesfeldOmega] at h1
    exact (by norm_num : (25920 : ℕ) = 960 * 27) ▸ h1
  have hBdvd : B.ncard ∣ 27 := by
    rw [← hcard] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hmem : ∀ x ∈ Open.timmesfeldOmega qMinus, x ![1, 0, 0, 0, 0, 0] = ![1, 0, 0, 0, 0, 0] →
      ∀ v ∈ B, x v ∈ B := by
    rintro x hx hxe _ ⟨h, rfl⟩
    exact ⟨⟨x, hXY x hx hxe⟩ * h, rfl⟩
  have hgB : g ![1, 0, 0, 0, 0, 0] ∈ B := ⟨⟨g, hgY⟩, rfl⟩
  have he₀B : (![1, 0, 0, 0, 0, 0] : Fin 6 → ZMod 2) ∈ B := mem_orbit_self _
  have hq₁ : qMinus (g ![1, 0, 0, 0, 0, 0]) = 0 := by rw [qMinus_apply_of_mem (hYΩ hgY), he₀q]
  have hq₁0 : g ![1, 0, 0, 0, 0, 0] ≠ 0 := fun h => he₀0 ((LinearEquiv.map_eq_zero_iff g).mp h)
  have hBfin : B.Finite := Set.toFinite B
  have h11 : 11 ≤ B.ncard := by
    by_cases hpol : polarMinus ![1, 0, 0, 0, 0, 0] (g ![1, 0, 0, 0, 0, 0]) = 0
    ·
      obtain ⟨x₁, hx₁, hx₁e, hx₁q⟩ := exists_mem_fix_apply_eq_e₃ hq₁ hpol hq₁0 hg
      have he₃B : (![0, 0, 0, 1, 0, 0] : Fin 6 → ZMod 2) ∈ B := by
        have h1 := hmem x₁⁻¹ (inv_mem hx₁) (inv_apply_eq_of_apply_eq hx₁e) _ hgB
        rwa [← hx₁q, ← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id] at h1
      rw [← card_ten, ← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard (fun y hy => ?_) hBfin
      rw [Finset.mem_coe, Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact he₀B
      · rw [Finset.mem_filter] at hy
        obtain ⟨x, hx, hxe, hxy⟩ :=
          exists_mem_fix_apply_eq_e₃ hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2
        rw [← hxy]
        exact hmem x hx hxe _ he₃B
    ·
      have h17 : 17 ≤ B.ncard := by
        rw [← card_sixteen, ← Set.ncard_coe_finset]
        refine Set.ncard_le_ncard (fun y hy => ?_) hBfin
        rw [Finset.mem_coe, Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact he₀B
        · rw [Finset.mem_filter] at hy
          obtain ⟨x, hx, hxe, hxy⟩ :=
            exists_mem_fix_apply_eq_of_polar_ne_zero he₀q hq₁ hy.2.1 hpol hy.2.2
          rw [← hxy]
          exact hmem x hx hxe _ hgB
      omega
  have h27 : B.ncard = 27 := by
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show B.ncard ∣ 3 ^ 3 by simpa using hBdvd)
    have hk3 : k = 3 := by
      by_contra hne
      have hk2 : k ≤ 2 := by omega
      have h9 : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      omega
    rw [hkeq, hk3]
    norm_num
  refine Subgroup.eq_of_le_of_card_ge hYΩ ?_
  rw [card_timmesfeldOmega, ← hcard, h27]

theorem eq_of_stabilizer_le {p : Fin 6 → ZMod 2} (hp : p ≠ 0) (hq : qMinus p = 0)
    {Y : Subgroup ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))}
    (hYΩ : Y ≤ Open.timmesfeldOmega qMinus)
    (hXY : ∀ h ∈ Open.timmesfeldOmega qMinus, h p = p → h ∈ Y)
    {g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)} (hgY : g ∈ Y) (hg : g p ≠ p) :
    Y = Open.timmesfeldOmega qMinus := by
  obtain ⟨k, hk, hkp⟩ := exists_mem_timmesfeldOmega_apply_eq (v := ![1, 0, 0, 0, 0, 0]) (w := p)
    (by decide) hp (by rw [hq]; decide)
  set Y' := Y.map (MulAut.conj k⁻¹).toMonoidHom with hY'
  have hmemY' : ∀ x, x ∈ Y' ↔ k * x * k⁻¹ ∈ Y := fun x => by
    rw [hY', Subgroup.mem_map_equiv]
    simp
  have hY'Ω : Y' ≤ Open.timmesfeldOmega qMinus := fun x hx => by
    have h1 := mul_mem (mul_mem (inv_mem hk) (hYΩ ((hmemY' x).mp hx))) hk
    simpa [mul_assoc] using h1
  have hXY' : ∀ h ∈ Open.timmesfeldOmega qMinus,
      h ![1, 0, 0, 0, 0, 0] = ![1, 0, 0, 0, 0, 0] → h ∈ Y' := fun h hh he =>
    (hmemY' h).mpr (hXY _ (mul_mem (mul_mem hk hh) (inv_mem hk)) (by
      rw [← hkp, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← LinearEquiv.mul_apply k⁻¹ k,
        inv_mul_cancel, LinearEquiv.coe_one, id, he]))
  have hg' : k⁻¹ * g * k ∈ Y' := (hmemY' _).mpr (by simpa [mul_assoc] using hgY)
  have hmove : (k⁻¹ * g * k) ![1, 0, 0, 0, 0, 0] ≠ ![1, 0, 0, 0, 0, 0] := by
    intro h
    apply hg
    have h1 := congrArg k h
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hkp, ← LinearEquiv.mul_apply,
      mul_inv_cancel, LinearEquiv.coe_one, id] at h1
    exact h1
  have hY'eq := eq_of_stabilizer_le_e₀ hY'Ω hXY' hg' hmove
  refine le_antisymm hYΩ fun x hx => ?_
  have h1 : k⁻¹ * x * k ∈ Y' := by
    rw [hY'eq]
    exact mul_mem (mul_mem (inv_mem hk) hx) hk
  have h2 := (hmemY' _).mp h1
  simpa [mul_assoc] using h2

theorem exists_mem_fix_apply_ne {p p' : Fin 6 → ZMod 2} (hp : p ≠ 0) (hq : qMinus p = 0)
    (hp' : p' ≠ 0) (hq' : qMinus p' = 0) (hne : p ≠ p') :
    ∃ x ∈ Open.timmesfeldOmega qMinus, x p' = p' ∧ x p ≠ p := by
  classical
  obtain ⟨k, hk, hkp⟩ := exists_mem_timmesfeldOmega_apply_eq (v := ![1, 0, 0, 0, 0, 0]) (w := p')
    (by decide) hp' (by rw [hq']; decide)
  set q := k⁻¹ p with hqdef
  have hkq : k q = p := by
    rw [hqdef, ← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id]
  have hqs : qMinus q = 0 := by rw [hqdef, qMinus_apply_of_mem (inv_mem hk), hq]
  have hq0 : q ≠ 0 := fun h => hp (by rw [← hkq, h, map_zero])
  have hqe : q ≠ ![1, 0, 0, 0, 0, 0] := fun h => hne (by rw [← hkq, h, hkp])
  obtain ⟨x, hx, hxe, hxq⟩ : ∃ x ∈ Open.timmesfeldOmega qMinus,
      x ![1, 0, 0, 0, 0, 0] = ![1, 0, 0, 0, 0, 0] ∧ x q ≠ q := by
    by_cases hpol : polarMinus ![1, 0, 0, 0, 0, 0] q = 0
    · obtain ⟨y, hy, hyq⟩ := Finset.exists_mem_ne
        (s := Finset.univ.filter fun y : Fin 6 → ZMod 2 => qMinus y = 0 ∧
          polarMinus ![1, 0, 0, 0, 0, 0] y = 0 ∧ y ≠ 0 ∧ y ≠ ![1, 0, 0, 0, 0, 0])
        (by decide +kernel) q
      rw [Finset.mem_filter] at hy
      obtain ⟨x₁, hx₁, hx₁e, hx₁q⟩ := exists_mem_fix_apply_eq_e₃ hqs hpol hq0 hqe
      obtain ⟨x₂, hx₂, hx₂e, hx₂y⟩ :=
        exists_mem_fix_apply_eq_e₃ hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2
      refine ⟨x₂ * x₁⁻¹, mul_mem hx₂ (inv_mem hx₁), ?_, ?_⟩
      · rw [LinearEquiv.mul_apply, inv_apply_eq_of_apply_eq hx₁e, hx₂e]
      · have he₃ : x₁⁻¹ q = ![0, 0, 0, 1, 0, 0] := by
          rw [← hx₁q, ← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id]
        rw [LinearEquiv.mul_apply, he₃, hx₂y]
        exact hyq
    · obtain ⟨y, hy, hyq⟩ := Finset.exists_mem_ne
        (s := Finset.univ.filter fun y : Fin 6 → ZMod 2 =>
          qMinus y = 0 ∧ polarMinus ![1, 0, 0, 0, 0, 0] y ≠ 0)
        (by decide +kernel) q
      rw [Finset.mem_filter] at hy
      obtain ⟨x, hx, hxe, hxy⟩ :=
        exists_mem_fix_apply_eq_of_polar_ne_zero (by decide) hqs hy.2.1 hpol hy.2.2
      exact ⟨x, hx, hxe, by rw [hxy]; exact hyq⟩
  refine ⟨k * x * k⁻¹, mul_mem (mul_mem hk hx) (inv_mem hk), ?_, ?_⟩
  · rw [← hkp, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← LinearEquiv.mul_apply k⁻¹ k,
      inv_mul_cancel, LinearEquiv.coe_one, id, hxe]
  · intro h
    apply hxq
    have h1 := congrArg (fun v => k⁻¹ v) h
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← LinearEquiv.mul_apply k⁻¹ k,
      inv_mul_cancel, LinearEquiv.coe_one, id] at h1
    exact h1

end CFSG.ComponentClassification.AS81.Sec2Omega
