module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K3010

theorem false_of_five_mem {M : Type*} [AddCommGroup M] [Finite M] {V : AddSubgroup M}
    (hV : Nat.card V ≤ 4) {a b c d e : M} (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hd : d ∈ V)
    (he : e ∈ V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : False := by
  let F : Fin 5 → V := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨e, he⟩]
  have hF : Function.Injective F := by
    intro i j hij
    rw [Subtype.ext_iff] at hij
    fin_cases i <;> fin_cases j <;> simp_all [F]
  have h5 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h5
  omega

theorem false_of_inverted {M : Type*} [AddCommGroup M] [Finite M] (h2 : ∀ x : M, x + x = 0)
    (Y Φ κ : M →+ M) (hY3 : ∀ x, Y (Y (Y x)) = x) (hΦi : Function.Injective Φ)
    (hκi : Function.Injective κ) (hΦfp : ∀ x, Φ x = x → x = 0)
    (hYΦ : ∀ x, Y (Φ x) = Φ (Y x)) (hκΦ : ∀ x, κ (Φ x) = Φ (κ x))
    (hκY : ∀ x, Y (κ (Y x)) = κ x) (hcard : Nat.card M = 4 * Nat.card {x : M // Y x = x})
    {x₀ : M} (hx₀ : Y x₀ ≠ x₀) : False := by
  let V : AddSubgroup M := (AddMonoidHom.id M + Y + Y.comp Y).ker
  have hmemV : ∀ x, x ∈ V ↔ x + Y x + Y (Y x) = 0 := fun x => by
    simp [V, AddMonoidHom.mem_ker]
  have hVfix : ∀ x ∈ V, Y x = x → x = 0 := by
    intro x hx hYx
    rw [hmemV, hYx, hYx, h2, zero_add] at hx
    exact hx
  have hVcard : Nat.card V ≤ 4 := by
    have hinj : Function.Injective (fun p : V × {x : M // Y x = x} => (p.1 : M) + p.2.1) := by
      rintro ⟨⟨v, hv⟩, ⟨c, hc⟩⟩ ⟨⟨v', hv'⟩, ⟨c', hc'⟩⟩ h
      simp only at h
      have hvc : v - v' = c' - c := by
        rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
      have hfix : Y (v - v') = v - v' := by rw [hvc, map_sub, hc, hc']
      have hvv : v = v' := sub_eq_zero.1 (hVfix _ (V.sub_mem hv hv') hfix)
      subst hvv
      exact Prod.ext rfl (Subtype.ext (add_left_cancel h))
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hcard] at h1
    haveI : Nonempty {x : M // Y x = x} := ⟨⟨0, map_zero Y⟩⟩
    exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  have hYi : Function.Injective Y := fun a b h => by rw [← hY3 a, ← hY3 b, h]
  have hYV : ∀ x ∈ V, Y x ∈ V := by
    intro x hx
    rw [hmemV] at hx ⊢
    rw [hY3, ← hx]
    abel
  have hΦV : ∀ x ∈ V, Φ x ∈ V := by
    intro x hx
    rw [hmemV] at hx ⊢
    rw [hYΦ, hYΦ, ← map_add, ← map_add, hx, map_zero]
  have hκV : ∀ x ∈ V, κ x ∈ V := by
    intro x hx
    rw [hmemV] at hx ⊢
    have e1 : Y (κ x) = κ (Y (Y x)) := by rw [← hκY (Y (Y x)), hY3]
    have e2 : Y (Y (κ x)) = κ (Y x) := by rw [e1, hκY]
    rw [e2, e1, ← map_add, ← map_add, show x + Y (Y x) + Y x = x + Y x + Y (Y x) by abel, hx,
      map_zero]
  obtain ⟨v, hvV, hv0⟩ : ∃ v ∈ V, v ≠ 0 := by
    refine ⟨Y x₀ - x₀, ?_, sub_ne_zero.2 hx₀⟩
    rw [hmemV]
    simp only [map_sub, hY3]
    abel
  have hneg : -v = v := neg_eq_of_add_eq_zero_left (h2 v)
  have hΦv0 : Φ v ≠ 0 := fun h => hv0 (hΦi (h.trans (map_zero Φ).symm))
  have hvΦ : v ≠ Φ v := fun h => hv0 (hΦfp v h.symm)
  have hs0 : v + Φ v ≠ 0 := fun h =>
    hv0 (hΦfp v ((eq_neg_of_add_eq_zero_right h).trans hneg))
  have hvs : v ≠ v + Φ v := fun h => hΦv0 (left_eq_add.1 h)
  have hΦs : Φ v ≠ v + Φ v := fun h => hv0 (right_eq_add.1 h)
  have hYv0 : Y v ≠ 0 := fun h => hv0 (hYi (h.trans (map_zero Y).symm))
  have hYvv : Y v ≠ v := fun h => hv0 (hVfix v hvV h)
  have hΦvV := hΦV v hvV
  have hsV : v + Φ v ∈ V := V.add_mem hvV hΦvV
  have key : ∀ u ∈ V, Y (κ u) = κ (Y u) := by
    by_cases hA : Y v = Φ v
    · have hall : ∀ u ∈ V, Y u = Φ u := by
        intro u hu
        by_contra hne
        refine false_of_five_mem hVcard V.zero_mem hvV hΦvV hsV hu hv0.symm hΦv0.symm hs0.symm
          ?_ hvΦ hvs ?_ hΦs ?_ ?_
        · rintro rfl
          exact hne (by simp)
        · rintro rfl
          exact hne hA
        · rintro rfl
          exact hne (by rw [hYΦ, hA])
        · rintro rfl
          exact hne (by rw [map_add, map_add, hA, hYΦ, hA])
      intro u hu
      rw [hall _ (hκV u hu), hall u hu, hκΦ]
    · have hB : Y v = v + Φ v := by
        by_contra hB
        exact false_of_five_mem hVcard V.zero_mem hvV hΦvV hsV (hYV v hvV) hv0.symm hΦv0.symm
          hs0.symm (Ne.symm hYv0) hvΦ hvs (Ne.symm hYvv) hΦs (Ne.symm hA) (Ne.symm hB)
      have hall : ∀ u ∈ V, Y u = u + Φ u := by
        intro u hu
        by_contra hne
        refine false_of_five_mem hVcard V.zero_mem hvV hΦvV hsV hu hv0.symm hΦv0.symm hs0.symm
          ?_ hvΦ hvs ?_ hΦs ?_ ?_
        · rintro rfl
          exact hne (by simp)
        · rintro rfl
          exact hne hB
        · rintro rfl
          exact hne (by rw [hYΦ, hB, map_add])
        · rintro rfl
          exact hne (by rw [map_add Y, hB, hYΦ, hB])
      intro u hu
      rw [hall _ (hκV u hu), hall u hu, map_add, hκΦ]
  have h1 : Y (Y (κ v)) = κ v := by
    rw [key v hvV]
    exact hκY v
  have h3 : Y (κ v) = κ v := by
    calc Y (κ v) = Y (Y (Y (κ v))) := by rw [h1]
      _ = κ v := hY3 _
  exact hv0 (hκi ((hVfix _ (hκV v hvV) h3).trans (map_zero κ).symm))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K3010
