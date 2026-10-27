module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs
import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Embed

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.HoltFree

open Subgroup
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)

variable {X Ω : Type} [Group X] [Group Ω] {L : Subgroup X} {ψ : normalizer (L : Set X) →* Ω}

theorem exists_liftE {M₀ : Subgroup Ω} (hψ : IsActionHom L M₀ ψ)
    (hZ : Odd (Nat.card (center ↥L))) {E₀ : Subgroup Ω}
    (hE₀c : ∀ y ∈ E₀, ∀ y' ∈ E₀, y * y' = y' * y) :
    ∃ E : Subgroup X, ∀ e, e ∈ E ↔ ∃ he : e ∈ L, ψ ⟨e, le_normalizer he⟩ ∈ E₀ ∧ e * e = 1 := by
  refine ⟨{ carrier := {e | ∃ he : e ∈ L, ψ ⟨e, le_normalizer he⟩ ∈ E₀ ∧ e * e = 1}
            mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun e => Iff.rfl⟩
  · rintro a b ⟨ha, hψa, ha2⟩ ⟨hb, hψb, hb2⟩
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha2, one_mul]
    have hψa2 : ψ ⟨a, le_normalizer ha⟩ * ψ ⟨a, le_normalizer ha⟩ = 1 := by
      rw [← map_mul]
      exact (congrArg ψ (Subtype.ext ha2 : (⟨a, le_normalizer ha⟩ * ⟨a, le_normalizer ha⟩ :
        normalizer (L : Set X)) = 1)).trans (map_one ψ)
    have hψb2 : ψ ⟨b, le_normalizer hb⟩ * ψ ⟨b, le_normalizer hb⟩ = 1 := by
      rw [← map_mul]
      exact (congrArg ψ (Subtype.ext hb2 : (⟨b, le_normalizer hb⟩ * ⟨b, le_normalizer hb⟩ :
        normalizer (L : Set X)) = 1)).trans (map_one ψ)
    have hcL : a * b * a * b ∈ L := L.mul_mem (L.mul_mem (L.mul_mem ha hb) ha) hb
    have hcC : a * b * a * b ∈ centralizer (L : Set X) := by
      have h1 : ψ (⟨a, le_normalizer ha⟩ * ⟨b, le_normalizer hb⟩ * ⟨a, le_normalizer ha⟩ *
          ⟨b, le_normalizer hb⟩) = 1 := by
        rw [map_mul, map_mul, map_mul, hE₀c _ hψa _ hψb, mul_assoc (ψ ⟨b, le_normalizer hb⟩),
          hψa2, mul_one, hψb2]
      exact (hψ.eq_one_iff _).mp h1
    have hinv : a * (a * b * a * b) * a⁻¹ = (a * b * a * b)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hai, hbi]
      simp only [mul_assoc, ha']
    have hcomm : a * (a * b * a * b) = a * b * a * b * a := mem_centralizer_iff.mp hcC a ha
    rw [hcomm, mul_inv_cancel_right] at hinv
    have hcc : a * b * a * b * (a * b * a * b) = 1 := mul_eq_one_iff_eq_inv.mpr hinv
    have hc1 : a * b * a * b = 1 := by
      obtain ⟨k, hk⟩ := AS81.odd_orderOf_of_mem_inf hZ hcL hcC
      have h2 : orderOf (a * b * a * b) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hcc)
      have := Nat.le_of_dvd (by norm_num) h2
      exact orderOf_eq_one_iff.mp (by omega)
    refine ⟨L.mul_mem ha hb, ?_, by rw [← mul_assoc]; exact hc1⟩
    show ψ (⟨a, le_normalizer ha⟩ * ⟨b, le_normalizer hb⟩) ∈ E₀
    rw [map_mul]
    exact E₀.mul_mem hψa hψb
  · refine ⟨L.one_mem, ?_, mul_one 1⟩
    show ψ 1 ∈ E₀
    rw [map_one]
    exact E₀.one_mem
  · rintro a ⟨ha, hψa, ha2⟩
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    refine ⟨L.inv_mem ha, ?_, by rw [hai]; exact ha2⟩
    show ψ (⟨a, le_normalizer ha⟩⁻¹) ∈ E₀
    rw [map_inv]
    exact E₀.inv_mem hψa

theorem twoC_lift (hψ : IsActionHom L ⊤ ψ) (hZ : Odd (Nat.card (center ↥L)))
    {z : X} (hz : z ∈ L) (hz2 : z * z = 1)
    (huniq : ∀ g : X, g * z * g⁻¹ ∈ L → g ∈ normalizer (L : Set X)) {u : X} (hu : u ∈ L)
    (hu2 : u * u = 1) {E₀ : Subgroup Ω} {p₀ ea₀ eb₀ ef₀ : Ω}
    (hvE₀ : ψ ⟨u, le_normalizer hu⟩ ∈ E₀) (hE₀2 : ∀ y ∈ E₀, y * y = 1)
    (hE₀c : ∀ y ∈ E₀, ∀ y' ∈ E₀, y * y' = y' * y) (hE₀card : Nat.card E₀ = 2048)
    (hE₀n : ∀ g : Ω, g * ψ ⟨u, le_normalizer hu⟩ = ψ ⟨u, le_normalizer hu⟩ * g →
      ∀ y ∈ E₀, g * y * g⁻¹ ∈ E₀)
    (hp₀v : p₀ * ψ ⟨u, le_normalizer hu⟩ = ψ ⟨u, le_normalizer hu⟩ * p₀) (hp₀11 : p₀ ^ 11 = 1)
    (hp₀fix : ∀ y ∈ E₀, p₀ * y = y * p₀ → y = 1 ∨ y = ψ ⟨u, le_normalizer hu⟩)
    (hea₀ : ea₀ ∈ E₀) (heb₀ : eb₀ ∈ E₀) (hef₀ : ef₀ ∈ E₀)
    (hwb₀1 : eb₀ * (p₀ * eb₀ * p₀⁻¹) ≠ 1)
    (ha₀ : IsConj (ea₀ * (p₀ * ea₀ * p₀⁻¹)) (ψ ⟨z, le_normalizer hz⟩))
    (hf₀ : IsConj (ef₀ * (p₀ * ef₀ * p₀⁻¹)) (ψ ⟨z, le_normalizer hz⟩))
    (haf₀ : IsConj (ea₀ * (p₀ * ea₀ * p₀⁻¹) * (ef₀ * (p₀ * ef₀ * p₀⁻¹)))
      (ψ ⟨z, le_normalizer hz⟩))
    (hb₀ : ¬ IsConj (eb₀ * (p₀ * eb₀ * p₀⁻¹)) (ψ ⟨z, le_normalizer hz⟩))
    (hbu₀ : ¬ IsConj (eb₀ * (p₀ * eb₀ * p₀⁻¹) * ψ ⟨u, le_normalizer hu⟩)
      (ψ ⟨z, le_normalizer hz⟩)) :
    ∃ (E : Subgroup X) (x ea eb ef : X), E ≤ L ∧ u ∈ E ∧ (∀ e ∈ E, e * e = 1) ∧
      Nat.card E = 2048 ∧
      (∀ c ∈ normalizer (L : Set X), c * u = u * c → ∀ e ∈ E, c * e * c⁻¹ ∈ E) ∧
      x ∈ L ∧ x * u = u * x ∧ (∀ e ∈ E, x * e * x⁻¹ ∈ E) ∧
      (∀ e ∈ E, x ^ 11 * e * (x ^ 11)⁻¹ = e) ∧ (∀ e ∈ E, x * e * x⁻¹ = e ↔ e = 1 ∨ e = u) ∧
      ea ∈ E ∧ eb ∈ E ∧ ef ∈ E ∧
      (∃ l ∈ L, ea * (x * ea * x⁻¹) = l * z * l⁻¹) ∧
      (∃ l ∈ L, ef * (x * ef * x⁻¹) = l * z * l⁻¹) ∧
      (∃ l ∈ L, ea * (x * ea * x⁻¹) * (ef * (x * ef * x⁻¹)) = l * z * l⁻¹) ∧
      eb * (x * eb * x⁻¹) ≠ 1 ∧ ¬ IsConj z (eb * (x * eb * x⁻¹)) ∧
      ¬ IsConj z (eb * (x * eb * x⁻¹) * u) := by
  have hLN : L ≤ normalizer (L : Set X) := le_normalizer
  obtain ⟨E, hmemE⟩ := exists_liftE hψ hZ hE₀c
  have hEL : E ≤ L := fun e he => ((hmemE e).mp he).1
  have hE2 : ∀ e ∈ E, e * e = 1 := fun e he => ((hmemE e).mp he).2.2
  have hψE : ∀ e (he : e ∈ E), ψ ⟨e, le_normalizer (hEL he)⟩ ∈ E₀ := fun e he =>
    ((hmemE e).mp he).2.1
  have hinjE : ∀ a b (ha : a ∈ E) (hb : b ∈ E),
      ψ ⟨a, le_normalizer (hEL ha)⟩ = ψ ⟨b, le_normalizer (hEL hb)⟩ → a = b := by
    intro a b ha hb hab
    have hd : a⁻¹ * b ∈ E := E.mul_mem (E.inv_mem ha) hb
    have hdC : a⁻¹ * b ∈ centralizer (L : Set X) := by
      have h1 : ψ (⟨a, le_normalizer (hEL ha)⟩⁻¹ * ⟨b, le_normalizer (hEL hb)⟩) = 1 := by
        rw [map_mul, map_inv, hab, inv_mul_cancel]
      exact (hψ.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := AS81.odd_orderOf_of_mem_inf hZ (hEL hd) hdC
    have h2 : orderOf (a⁻¹ * b) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hE2 _ hd)
    have := Nat.le_of_dvd (by norm_num) h2
    exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp (by omega))
  have hlift : ∀ y ∈ E₀, ∃ e, ∃ he : e ∈ E, ψ ⟨e, le_normalizer (hEL he)⟩ = y := by
    intro y hy
    obtain ⟨a, ha, hψa⟩ := hψ.exists_eq y (mem_top y)
    have ha2C : a * a ∈ centralizer (L : Set X) := by
      have h1 : ψ (⟨a, le_normalizer ha⟩ * ⟨a, le_normalizer ha⟩) = 1 := by
        rw [map_mul, hψa, hE₀2 y hy]
      exact (hψ.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := AS81.odd_orderOf_of_mem_inf hZ (L.mul_mem ha ha) ha2C
    have heL : a ^ orderOf (a * a) ∈ L := pow_mem ha _
    have he2 : a ^ orderOf (a * a) * a ^ orderOf (a * a) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, sq, pow_orderOf_eq_one]
    have hψe : ψ ⟨a ^ orderOf (a * a), le_normalizer heL⟩ = y := by
      have e1 : (⟨a ^ orderOf (a * a), le_normalizer heL⟩ : normalizer (L : Set X)) =
          ⟨a, le_normalizer ha⟩ ^ orderOf (a * a) := Subtype.ext (by simp)
      rw [e1, map_pow, hψa, hk, pow_succ, pow_mul, sq, hE₀2 y hy, one_pow, one_mul]
    exact ⟨_, (hmemE _).mpr ⟨heL, by rw [hψe]; exact hy, he2⟩, hψe⟩
  have hEcard : Nat.card E = 2048 := by
    rw [← hE₀card]
    refine Nat.card_eq_of_bijective
      (fun e : E => (⟨ψ ⟨e, le_normalizer (hEL e.2)⟩, hψE _ e.2⟩ : E₀)) ⟨?_, ?_⟩
    · intro a b hab
      exact Subtype.ext (hinjE _ _ a.2 b.2 (congrArg Subtype.val hab))
    · intro y
      obtain ⟨e, he, hey⟩ := hlift y y.2
      exact ⟨⟨e, he⟩, Subtype.ext hey⟩
  have huE : u ∈ E := (hmemE u).mpr ⟨hu, hvE₀, hu2⟩
  have hEn : ∀ c ∈ normalizer (L : Set X), c * u = u * c → ∀ e ∈ E, c * e * c⁻¹ ∈ E := by
    intro c hc hcu e he
    have hψc : ψ ⟨c, hc⟩ * ψ ⟨u, le_normalizer hu⟩ = ψ ⟨u, le_normalizer hu⟩ * ψ ⟨c, hc⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext hcu)
    have hceL : c * e * c⁻¹ ∈ L := (mem_normalizer_iff.mp hc e).mp (hEL he)
    refine (hmemE _).mpr ⟨hceL, ?_, ?_⟩
    · have e1 : (⟨c * e * c⁻¹, le_normalizer hceL⟩ : normalizer (L : Set X)) =
          ⟨c, hc⟩ * ⟨e, le_normalizer (hEL he)⟩ * ⟨c, hc⟩⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_inv]
      exact hE₀n _ hψc _ (hψE e he)
    · rw [show c * e * c⁻¹ * (c * e * c⁻¹) = c * (e * e) * c⁻¹ by group, hE2 e he, mul_one,
        mul_inv_cancel]
  obtain ⟨x, hxL, hψx, hxu⟩ := AS81.exists_lift_commute hψ hZ (t := ⟨u, le_normalizer hu⟩)
    (by rw [sq]; exact hu2) (mem_top p₀) hp₀v
  have hxE : ∀ e ∈ E, x * e * x⁻¹ ∈ E := hEn x (hLN hxL) hxu
  have hx11 : ∀ e ∈ E, x ^ 11 * e * (x ^ 11)⁻¹ = e := by
    have hx11C : x ^ 11 ∈ centralizer (L : Set X) := by
      have h1 : ψ (⟨x, le_normalizer hxL⟩ ^ 11) = 1 := by rw [map_pow, hψx, hp₀11]
      have h2 := (hψ.eq_one_iff _).mp h1
      simpa using h2
    intro e he
    rw [← mem_centralizer_iff.mp hx11C e (hEL he), mul_inv_cancel_right]
  have hfix : ∀ e ∈ E, x * e * x⁻¹ = e ↔ e = 1 ∨ e = u := by
    intro e he
    constructor
    · intro h1
      have h2 : p₀ * ψ ⟨e, le_normalizer (hEL he)⟩ = ψ ⟨e, le_normalizer (hEL he)⟩ * p₀ := by
        rw [← hψx, ← map_mul, ← map_mul]
        refine congrArg ψ (Subtype.ext ?_)
        show x * e = e * x
        calc x * e = x * e * x⁻¹ * x := by group
          _ = e * x := by rw [h1]
      rcases hp₀fix _ (hψE e he) h2 with h3 | h3
      · exact Or.inl (hinjE _ _ he E.one_mem (h3.trans (map_one ψ).symm))
      · exact Or.inr (hinjE _ _ he huE h3)
    · rintro (rfl | rfl)
      · group
      · rw [hxu, mul_inv_cancel_right]
  obtain ⟨ea, hea, hψea⟩ := hlift ea₀ hea₀
  obtain ⟨eb, heb, hψeb⟩ := hlift eb₀ heb₀
  obtain ⟨ef, hef, hψef⟩ := hlift ef₀ hef₀
  have hwE : ∀ e ∈ E, e * (x * e * x⁻¹) ∈ E := fun e he => E.mul_mem he (hxE e he)
  have hψw : ∀ e (he : e ∈ E), ψ ⟨e * (x * e * x⁻¹), le_normalizer (hEL (hwE e he))⟩ =
      ψ ⟨e, le_normalizer (hEL he)⟩ * (p₀ * ψ ⟨e, le_normalizer (hEL he)⟩ * p₀⁻¹) := by
    intro e he
    rw [← hψx]
    show ψ (⟨e, le_normalizer (hEL he)⟩ * (⟨x, le_normalizer hxL⟩ * ⟨e, le_normalizer (hEL he)⟩ *
      ⟨x, le_normalizer hxL⟩⁻¹)) = _
    rw [map_mul, map_mul, map_mul, map_inv]
  have hconjz : ∀ w (hw : w ∈ E), IsConj (ψ ⟨w, le_normalizer (hEL hw)⟩) (ψ ⟨z, le_normalizer hz⟩) →
      ∃ l ∈ L, w = l * z * l⁻¹ := by
    intro w hw hc
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    exact AS81.exists_conj_of_map_conj hψ hZ hz (hEL hw) (by rw [sq]; exact hz2)
      (by rw [sq]; exact hE2 w hw) (mem_top c⁻¹) (by rw [← hc]; group)
  have hnotz : ∀ w (hw : w ∈ L),
      ¬ IsConj (ψ ⟨w, le_normalizer hw⟩) (ψ ⟨z, le_normalizer hz⟩) → ¬ IsConj z w := by
    intro w hw hn hc
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    have hgN : g ∈ normalizer (L : Set X) := huniq g (by rw [hg]; exact hw)
    refine hn (isConj_iff.mpr ⟨(ψ ⟨g, hgN⟩)⁻¹, ?_⟩)
    have e1 : (⟨w, le_normalizer hw⟩ : normalizer (L : Set X)) =
        ⟨g, hgN⟩ * ⟨z, le_normalizer hz⟩ * ⟨g, hgN⟩⁻¹ := Subtype.ext hg.symm
    rw [e1, map_mul, map_mul, map_inv]
    group
  refine ⟨E, x, ea, eb, ef, hEL, huE, hE2, hEcard, hEn, hxL, hxu, hxE, hx11, hfix, hea, heb, hef,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hconjz _ (hwE ea hea) (by rw [hψw ea hea, hψea]; exact ha₀)
  · exact hconjz _ (hwE ef hef) (by rw [hψw ef hef, hψef]; exact hf₀)
  · refine hconjz _ (E.mul_mem (hwE ea hea) (hwE ef hef)) ?_
    show IsConj (ψ (⟨_, le_normalizer (hEL (hwE ea hea))⟩ * ⟨_, le_normalizer (hEL (hwE ef hef))⟩))
      _
    rw [map_mul, hψw ea hea, hψw ef hef, hψea, hψef]
    exact haf₀
  · intro h1
    apply hwb₀1
    rw [← hψeb, ← hψw eb heb]
    exact (congrArg ψ (Subtype.ext h1 : (⟨_, le_normalizer (hEL (hwE eb heb))⟩ :
      normalizer (L : Set X)) = 1)).trans (map_one ψ)
  · exact hnotz _ (hEL (hwE eb heb)) (by rw [hψw eb heb, hψeb]; exact hb₀)
  · refine hnotz _ (hEL (E.mul_mem (hwE eb heb) huE)) ?_
    show ¬ IsConj (ψ (⟨_, le_normalizer (hEL (hwE eb heb))⟩ * ⟨u, le_normalizer hu⟩)) _
    rw [map_mul, hψw eb heb, hψeb]
    exact hbu₀

end CFSG.ComponentClassification.RankTwoExceptional.HoltFree
