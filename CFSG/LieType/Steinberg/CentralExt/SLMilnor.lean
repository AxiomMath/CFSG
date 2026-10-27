module

public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed

public section

open Matrix
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SLClosed

variable {m : ℕ} {F : Type} [Field F]

theorem commutatorElement_assoc {G : Type*} [Group G] {a b c : G} (hac : a * c = c * a)
    (h1 : ⁅a, b⁆ * ⁅b, c⁆ = ⁅b, c⁆ * ⁅a, b⁆) (h2 : ⁅⁅a, b⁆, c⁆ * ⁅b, c⁆ = ⁅b, c⁆ * ⁅⁅a, b⁆, c⁆) :
    ⁅a, ⁅b, c⁆⁆ = ⁅⁅a, b⁆, c⁆ := by
  have hc : a * c * a⁻¹ = c := by rw [hac, mul_inv_cancel_right]
  have hb : a * b * a⁻¹ = ⁅a, b⁆ * b := by
    rw [commutatorElement_def]
    group
  have e1 : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ * ⁅⁅a, b⁆, c⁆ := by
    rw [conjugate_commutatorElement, hc, hb, RootLift.commutatorElement_mul_left_conj, h1,
      mul_inv_cancel_right]
  calc ⁅a, ⁅b, c⁆⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅b, c⁆⁻¹ := commutatorElement_def _ _
    _ = ⁅b, c⁆ * ⁅⁅a, b⁆, c⁆ * ⁅b, c⁆⁻¹ := by rw [e1]
    _ = ⁅⁅a, b⁆, c⁆ := by rw [← h2, mul_inv_cancel_right]

open _root_.Classical in
@[expose] noncomputable def mid (i j : Fin (m + 1)) : Fin (m + 1) :=
  if h : ∃ o : Fin (m + 1), o ≠ i ∧ o ≠ j then h.choose else i

theorem mid_spec (hm : 2 ≤ m) (i j : Fin (m + 1)) : mid i j ≠ i ∧ mid i j ≠ j := by
  classical
  have h := exists_ne_ne hm i j
  rw [mid, dite_eq_left h]
  exact h.choose_spec

section Lift

variable {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin (m + 1)) F}
  (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)

include hcen hπ in
theorem lift_commute (hm : 4 ≤ m) {i j k l : Fin (m + 1)} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) {a b : E} {s t : F} (ha : π a = tv F i j s)
    (hb : π b = tv F k l t) : a * b = b * a := by
  obtain ⟨h, hhi, hhj, hhk, hhl⟩ := exists_ne4 hm i j k l
  obtain ⟨c, hc⟩ := hπ (tv F i h s)
  obtain ⟨e, he⟩ := hπ (tv F h j 1)
  have hce : π ⁅c, e⁆ = π a := by
    rw [map_commutatorElement, hc, he, tv_chain hhi.symm hhj hij, mul_one, ha]
  have hz : ⁅c, e⁆⁻¹ * a ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hce, inv_mul_cancel]
  have hzc := Subgroup.mem_center_iff.1 (hcen hz)
  have hb' : b * ⁅c, e⁆ = ⁅c, e⁆ * b := commute_commutatorElement hcen
    (by rw [hb, hc]; exact tv_commute hkl hhi.symm hli hhk t s)
    (by rw [hb, he]; exact tv_commute hkl hhj hhl.symm hjk t 1)
  calc a * b = ⁅c, e⁆ * (⁅c, e⁆⁻¹ * a) * b := by group
    _ = ⁅c, e⁆ * b * (⁅c, e⁆⁻¹ * a) := by rw [mul_assoc, ← hzc b, ← mul_assoc]
    _ = b * ⁅c, e⁆ * (⁅c, e⁆⁻¹ * a) := by rw [hb']
    _ = b * a := by group

include hcen hπ in
theorem commutatorElement_eq_of_fourth (hm : 4 ≤ m) {i j k l : Fin (m + 1)} (hij : i ≠ j)
    (hjl : j ≠ l) (hil : i ≠ l) (hki : k ≠ i) (hkj : k ≠ j) (hkl : k ≠ l) {a b c e : E}
    {s t : F} (ha : π a = tv F i j s) (hb : π b = tv F j l t) (hc : π c = tv F i k (s * t))
    (he : π e = tv F k l 1) : ⁅a, b⁆ = ⁅c, e⁆ := by
  obtain ⟨b1, hb1⟩ := hπ (tv F j k t)
  obtain ⟨b2, hb2⟩ := hπ (tv F k l 1)
  have hb12 : π ⁅b1, b2⁆ = π b := by
    rw [map_commutatorElement, hb1, hb2, tv_chain hkj.symm hkl hjl, mul_one, hb]
  have hab1 : π ⁅a, b1⁆ = tv F i k (s * t) := by
    rw [map_commutatorElement, ha, hb1, tv_chain hij hkj.symm hki.symm]
  have hab12 : π ⁅⁅a, b1⁆, b2⁆ = tv F i l (s * t) := by
    rw [map_commutatorElement, hab1, hb2, tv_chain hki.symm hkl hil, mul_one]
  rw [TorusLift.commutatorElement_eq_of_map_eq hcen rfl hb12.symm,
    commutatorElement_assoc
      (lift_commute hcen hπ hm hij hkl hkj.symm (fun e => hil e.symm) ha hb2)
      (lift_commute hcen hπ hm hki.symm hjl hkj (fun e => hil e.symm) hab1 (hb12.trans hb))
      (lift_commute hcen hπ hm hil hjl (fun e => hjl e.symm) (fun e => hil e.symm) hab12
        (hb12.trans hb))]
  exact TorusLift.commutatorElement_eq_of_map_eq hcen (hab1.trans hc.symm) (hb2.trans he.symm)

@[expose] noncomputable def XM (i j : Fin (m + 1)) (s : F) : E :=
  ⁅TorusLift.lift hπ (tv F i (mid i j) s), TorusLift.lift hπ (tv F (mid i j) j 1)⁆

theorem map_XM (hm : 2 ≤ m) {i j : Fin (m + 1)} (h : i ≠ j) (s : F) :
    π (XM hπ i j s) = tv F i j s := by
  obtain ⟨h1, h2⟩ := mid_spec hm i j
  rw [XM, map_commutatorElement, TorusLift.map_lift, TorusLift.map_lift, tv_chain h1.symm h2 h,
    mul_one]

variable (hm : 4 ≤ m)
include hcen hm

theorem XM_commute {i j k l : Fin (m + 1)} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (s t : F) : XM hπ i j s * XM hπ k l t = XM hπ k l t * XM hπ i j s :=
  lift_commute hcen hπ hm hij hkl hjk hli (map_XM hπ (by omega) hij s) (map_XM hπ (by omega) hkl t)

theorem XM_add {i j : Fin (m + 1)} (h : i ≠ j) (s s' : F) :
    XM hπ i j (s + s') = XM hπ i j s * XM hπ i j s' := by
  obtain ⟨h1, h2⟩ := mid_spec (by omega) i j
  have hsum : XM hπ i j (s + s') = ⁅TorusLift.lift hπ (tv F i (mid i j) s) *
      TorusLift.lift hπ (tv F i (mid i j) s'), TorusLift.lift hπ (tv F (mid i j) j 1)⁆ := by
    rw [XM]
    refine TorusLift.commutatorElement_eq_of_map_eq hcen ?_ rfl
    rw [map_mul, TorusLift.map_lift, TorusLift.map_lift, TorusLift.map_lift, tv_add h1.symm]
  have hcomm : TorusLift.lift hπ (tv F i (mid i j) s) * XM hπ i j s' =
      XM hπ i j s' * TorusLift.lift hπ (tv F i (mid i j) s) :=
    lift_commute hcen hπ hm h1.symm h h1 (Ne.symm h) (TorusLift.map_lift hπ _)
      (map_XM hπ (by omega) h s')
  rw [hsum, RootLift.commutatorElement_mul_left_conj]
  change TorusLift.lift hπ (tv F i (mid i j) s) * XM hπ i j s' *
    (TorusLift.lift hπ (tv F i (mid i j) s))⁻¹ * XM hπ i j s = _
  rw [hcomm, mul_inv_cancel_right]
  exact XM_commute hcen hπ hm h h (Ne.symm h) (Ne.symm h) s' s

theorem XM_chain {i j l : Fin (m + 1)} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (s t : F) :
    ⁅XM hπ i j s, XM hπ j l t⁆ = XM hπ i l (s * t) := by
  obtain ⟨h1, h2⟩ := mid_spec (by omega) i l
  have ha := map_XM hπ (by omega) hij s
  have hb := map_XM hπ (by omega) hjl t
  by_cases hmj : mid i l = j
  ·
    obtain ⟨k, hki, hkj, hkl⟩ := exists_ne3 (by omega) i j l
    rw [commutatorElement_eq_of_fourth hcen hπ hm hij hjl hil hki hkj hkl ha hb
      (TorusLift.map_lift hπ (tv F i k (s * t))) (TorusLift.map_lift hπ (tv F k l 1))]
    refine commutatorElement_eq_of_fourth hcen hπ hm hki.symm hkl hil (Ne.symm hij)
      (Ne.symm hkj) hjl (TorusLift.map_lift hπ _) (TorusLift.map_lift hπ _) ?_ ?_
    · rw [TorusLift.map_lift, hmj, mul_one]
    · rw [TorusLift.map_lift, hmj]
  · exact commutatorElement_eq_of_fourth hcen hπ hm hij hjl hil h1 hmj h2 ha hb
      (TorusLift.map_lift hπ _) (TorusLift.map_lift hπ _)

end Lift

theorem sl_exists_section_of_four_le [Finite F] (hm : 4 ≤ m) {E : Type*} [Group E]
    {π : E →* SpecialLinearGroup (Fin (m + 1)) F} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : SpecialLinearGroup (Fin (m + 1)) F →* E, ∀ g, π (σ g) = g :=
  exists_section_of_lifts (XM hπ) (fun _ _ h => XM_add hcen hπ hm h)
    (fun _ _ _ _ hij hkl hjk hli => XM_commute hcen hπ hm hij hkl hjk hli)
    (fun _ _ _ hij hjl hil s t => by rw [one_mul]; exact XM_chain hcen hπ hm hij hjl hil s t)
    (fun _ _ h => map_XM hπ (by omega) h) (by omega)

theorem sl_hopfMultiplier_mulEquiv_ker_of_four_le [Finite F] (hm : 4 ≤ m) {X : Type} [Group X]
    (q : SpecialLinearGroup (Fin (m + 1)) F →* X) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) :
    Nonempty (CFSG.RankThree.PerfectCover.hopfMultiplier X ≃* q.ker) :=
  sl_hopfMultiplier_mulEquiv_ker_of_split (by omega)
    (fun _ _ _ hπ hcen => sl_exists_section_of_four_le hm hπ hcen) q hq hker

end CFSG.LieType.Steinberg.CentralExt.SLClosed
