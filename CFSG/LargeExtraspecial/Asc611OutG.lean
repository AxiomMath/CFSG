module

public import CFSG.LargeExtraspecial.Asc611OutF

public section

namespace CFSG.LargeExtraspecial.Asc611

open Subgroup Matrix CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem eq_of_add_eq_zero_K {x y : Fin m → K} (h : x + y = 0) : x = y := by
  linear_combination (norm := module) h - two_eq_zero • y

section Core

variable {S : (Fin m → K) → Fin m → K} (hS : SemiInv S) {U : Subgroup (PG m)}
  (hU : IsPGroup 2 U)
  (hnorm : ∀ v : Fin m → K, S v = v → v ≠ 0 → herm frob v v = 0 →
    ∀ u ∈ U, tq v * u * (tq v)⁻¹ ∈ U)
  (hDG : ∀ u ∈ U, u ∉ DG m)
include hS hU hnorm hDG

theorem eq_one_of_lift (hm : 5 ≤ m) {g : SUid frob m} (hgU : (QuotientGroup.mk g : PG m) ∈ U)
    (hgS : ∀ x, S (g • x) = g • S x) : (QuotientGroup.mk g : PG m) = 1 := by
  have hm3 : 3 ≤ m := by omega
  have hstar : ∀ v v'' : Fin m → K, S v = v → herm frob v v = 0 → S v'' = v'' →
      herm frob v'' v'' = 0 → herm frob v'' (g • v) = herm frob v'' v := by
    intro v v'' hvS hv hv''S hv''
    by_cases hv0 : v = 0
    · rw [hv0, smul_zero]
    by_cases hv''0 : v'' = 0
    · rw [hv''0, herm_zero_left, herm_zero_left]
    exact herm_smul_eq_of_fix hS hU hnorm hm3 hgU hgS hvS hv0 hv hv''S hv''0 hv''
  have hdfix : ∀ v, S v = v → S (g • v + v) = g • v + v := fun v hvS => by
    rw [hS.add, hgS, hvS]
  have hdorth : ∀ v, S v = v → herm frob v v = 0 → ∀ v'', S v'' = v'' →
      herm frob v'' v'' = 0 → herm frob v'' (g • v + v) = 0 := fun v hvS hv v'' hv''S hv'' => by
    rw [herm_add_right, hstar v v'' hvS hv hv''S hv'', add_self_K]
  have hid : (∀ x, S x = x → g • x = x) → (QuotientGroup.mk g : PG m) = 1 := fun h => by
    rw [hS.eq_of_fix (g := g) (g' := 1) fun x hx => by rw [h x hx, one_smul],
      QuotientGroup.mk_one]
  by_cases hA : ∀ v, S v = v → herm frob v v = 0 → g • v = v
  · by_cases hq : ∀ x, S x = x → herm frob x x = 0
    · exact hid fun x hx => hA x hx (hq x hx)
    push Not at hq
    obtain ⟨x₀, hx₀S, hx₀ne⟩ := hq
    have hx₀ : herm frob x₀ x₀ = 1 := (herm_self_eq_zero_or_one x₀).resolve_left hx₀ne
    set y := g • x₀ + x₀ with hy
    have hyS : S y = y := hdfix x₀ hx₀S
    have hyorth : ∀ v, S v = v → herm frob v v = 0 → herm frob v y = 0 := by
      intro v hvS hv
      have h1 : herm frob v (g • x₀) = herm frob v x₀ := by
        conv_lhs => rw [← hA v hvS hv]
        exact herm_smul_smul _ g v x₀
      rw [hy, herm_add_right, h1, add_self_K]
    rcases hS.eq_zero_or_char hyS hyorth with hy0 | hychar
    · have hgx₀ : g • x₀ = x₀ := eq_of_add_eq_zero_K hy0
      refine hid fun x hxS => ?_
      rcases herm_self_eq_zero_or_one x with h0 | h1
      · exact hA x hxS h0
      · have hfix : S (x + x₀) = x + x₀ := by rw [hS.add, hxS, hx₀S]
        have hiso : herm frob (x + x₀) (x + x₀) = 0 := by
          rw [hS.herm_add_add hxS hx₀S, h1, hx₀, add_self_K]
        have h2 := hA _ hfix hiso
        rw [smul_add, hgx₀] at h2
        exact add_right_cancel h2
    · exfalso
      have hgx₀ : g • x₀ = x₀ + y := by
        rw [hy, add_comm x₀, add_assoc, ← two_smul K x₀, two_eq_zero, zero_smul, add_zero]
      have hyy : herm frob y y = 0 := by
        have h1 : herm frob (g • x₀) (g • x₀) = 1 := by rw [herm_smul_smul, hx₀]
        rw [hgx₀, hS.herm_add_add hx₀S hyS, hx₀] at h1
        linear_combination h1
      have hy0 : y ≠ 0 := by
        intro h0
        have h1 := hychar x₀ hx₀S
        rw [h0, herm_zero_right, hx₀] at h1
        exact zero_ne_one h1
      have hshape : IsShape S y x₀ y g := ⟨fun v hvS hv => by
        rw [hA v hvS hv, hychar v hvS, hv, zero_smul, add_zero], hgx₀⟩
      have hgy := IsShape.eq_tvU hS hyS hychar hyy hx₀S hx₀ hshape
      exact hDG _ hgU (by rw [hgy]; exact tq_mem_DG hy0 hyy)
  · push Not at hA
    obtain ⟨v₁, hv₁S, hv₁, hgv₁⟩ := hA
    exfalso
    set c := g • v₁ + v₁ with hcdef
    have hc0 : c ≠ 0 := fun h => hgv₁ (eq_of_add_eq_zero_K h)
    have hcS : S c = c := hdfix v₁ hv₁S
    have hcchar : ∀ x, S x = x → herm frob x c = herm frob x x :=
      (hS.eq_zero_or_char hcS (hdorth v₁ hv₁S hv₁)).resolve_left hc0
    have hgv₁' : g • v₁ = c + v₁ := by
      rw [hcdef, add_assoc, ← two_smul K v₁, two_eq_zero, zero_smul, add_zero]
    have hcc : herm frob c c = 0 := by
      have h1 : herm frob (g • v₁) (g • v₁) = 0 := by rw [herm_smul_smul, hv₁]
      rw [hgv₁', hS.herm_add_add hcS hv₁S, hv₁, add_zero] at h1
      exact h1
    have hgv : ∀ v, S v = v → herm frob v v = 0 → g • v = v ∨ g • v = v + c := by
      intro v hvS hv
      rcases hS.eq_zero_or_char (hdfix v hvS) (hdorth v hvS hv) with h0 | hch
      · exact Or.inl (eq_of_add_eq_zero_K h0)
      · right
        have h1 := hS.char_unique (hdfix v hvS) hcS hch hcchar
        rw [← h1, add_comm (g • v) v, ← add_assoc, ← two_smul K v, two_eq_zero, zero_smul,
          zero_add]
    obtain ⟨x₀, hx₀S, hx₀⟩ : ∃ x₀, S x₀ = x₀ ∧ herm frob x₀ x₀ = 1 := by
      by_contra hno
      push Not at hno
      apply hc0
      refine hS.eq_zero_of_herm fun x hx => ?_
      rw [hcchar x hx]
      exact (herm_self_eq_zero_or_one x).resolve_right (hno x hx)
    set y := g • x₀ + x₀ with hy
    have hyS : S y = y := hdfix x₀ hx₀S
    have hgx₀ : g • x₀ = x₀ + y := by
      rw [hy, add_comm x₀, add_assoc, ← two_smul K x₀, two_eq_zero, zero_smul, add_zero]
    clear_value y
    have hyy : herm frob y y = 0 := by
      have h1 : herm frob (g • x₀) (g • x₀) = 1 := by rw [herm_smul_smul, hx₀]
      rw [hgx₀, hS.herm_add_add hx₀S hyS, hx₀] at h1
      linear_combination h1
    have hcx₀ : herm frob c x₀ = 1 := by rw [hS.herm_symm hx₀S hcS, hcchar x₀ hx₀S, hx₀]
    have hcy : herm frob c y = 0 := by rw [hS.herm_symm hyS hcS, hcchar y hyS, hyy]
    have hshape : IsShape S c x₀ y g := by
      refine ⟨fun v hvS hv => ?_, hgx₀⟩
      have hunit : herm frob (g • v) (g • x₀) = herm frob v x₀ := herm_smul_smul _ g v x₀
      rcases hgv v hvS hv with h | h
      · have h1 : herm frob v y = 0 := by
          rw [h, hgx₀, herm_add_right] at hunit
          linear_combination hunit
        rw [h, h1, zero_smul, add_zero]
      · have h1 : herm frob v y = 1 := by
          rw [h, hgx₀, herm_add_left, herm_add_right, herm_add_right, hcx₀, hcy] at hunit
          linear_combination hunit - two_eq_zero
        rw [h, h1, one_smul]
    have hv₁y : herm frob v₁ y = 1 := by
      rcases hS.herm_fix hv₁S hyS with h0 | h1
      · exfalso
        apply hgv₁
        rw [hshape.1 v₁ hv₁S hv₁, h0, zero_smul, add_zero]
      · exact h1
    obtain ⟨s, s', hsS, hs'S, hss, hs's', hsy, hs'y, hss'⟩ :=
      hS.exists_pair hm hx₀S hx₀ hv₁S hv₁ hyS hv₁y
    have ht : ∀ w, S w = w → herm frob w w = 0 → herm frob w y = 1 →
        (QuotientGroup.mk (tvU (w + c) * tvU w) : PG m) ∈ U ∧
          IsShape S c x₀ (w + (herm frob w x₀ + 1) • c) (tvU (w + c) * tvU w) := by
      intro w hwS hw hwy
      have hw0 : w ≠ 0 := by
        rintro rfl
        rw [herm_zero_left] at hwy
        exact zero_ne_one hwy
      have hgw : g • w = w + c := by rw [hshape.1 w hwS hw, hwy, one_smul]
      refine ⟨?_, isShape_tvU hS hcS hcchar hcc hx₀S hx₀ hwS hw⟩
      have h1 := (herm_smul_eq_zero_of_fix hU hnorm hm3 hgU hwS hw0 hw).1
      rw [hgw] at h1
      rw [QuotientGroup.mk_mul]
      exact h1
    have hF : ∀ w, S w = w → (herm frob w x₀ + 1 = 0 ∨ herm frob w x₀ + 1 = 1) :=
      fun w hwS => add_mem_F2 (hS.herm_fix hwS hx₀S) (Or.inr rfl)
    have hfixadd : ∀ a b : Fin m → K, S a = a → S b = b → S (a + b) = a + b :=
      fun a b ha hb => by rw [hS.add, ha, hb]
    have hisoadd : ∀ a b : Fin m → K, S a = a → S b = b → herm frob a a = 0 →
        herm frob b b = 0 → herm frob (a + b) (a + b) = 0 := fun a b ha hb h1 h2 => by
      rw [hS.herm_add_add ha hb, h1, h2, add_zero]
    have hyadd : ∀ a b : Fin m → K, herm frob a y = 1 → herm frob b y = 0 →
        herm frob (a + b) y = 1 := fun a b h1 h2 => by rw [herm_add_left, h1, h2, add_zero]
    have h₂S := hfixadd v₁ s hv₁S hsS
    have h₂ := hisoadd v₁ s hv₁S hsS hv₁ hss
    have h₂y := hyadd v₁ s hv₁y hsy
    have h₃S := hfixadd v₁ s' hv₁S hs'S
    have h₃ := hisoadd v₁ s' hv₁S hs'S hv₁ hs's'
    have h₃y := hyadd v₁ s' hv₁y hs'y
    have h₄S := hfixadd (v₁ + s') s h₃S hsS
    have h₄ := hisoadd (v₁ + s') s h₃S hsS h₃ hss
    have h₄y := hyadd (v₁ + s') s h₃y hsy
    obtain ⟨hU₁, hT₁⟩ := ht v₁ hv₁S hv₁ hv₁y
    obtain ⟨hU₂, hT₂⟩ := ht (v₁ + s) h₂S h₂ h₂y
    obtain ⟨hU₃, hT₃⟩ := ht (v₁ + s') h₃S h₃ h₃y
    obtain ⟨hU₄, hT₄⟩ := ht (v₁ + s' + s) h₄S h₄ h₄y
    have he₁ := IsShape.mul_norm hS hcS hcchar hcc hv₁S hv₁ (hF v₁ hv₁S) h₂S h₂
      (hF _ h₂S) hT₁ hT₂
    have he₂ := IsShape.mul_norm hS hcS hcchar hcc h₃S h₃ (hF _ h₃S) h₄S h₄ (hF _ h₄S) hT₃ hT₄
    have hα₁ := add_mem_F2 (add_mem_F2 (hF v₁ hv₁S) (hF _ h₂S)) (hS.herm_fix h₂S hv₁S)
    have hα₂ := add_mem_F2 (add_mem_F2 (hF _ h₃S) (hF _ h₄S)) (hS.herm_fix h₄S h₃S)
    have he := IsShape.mul_norm hS hcS hcchar hcc (hfixadd _ _ hv₁S h₂S)
      (hisoadd _ _ hv₁S h₂S hv₁ h₂) hα₁ (hfixadd _ _ h₃S h₄S) (hisoadd _ _ h₃S h₄S h₃ h₄) hα₂
      he₁ he₂
    have hvsum : v₁ + (v₁ + s) + (v₁ + s' + (v₁ + s' + s)) = 0 := by
      linear_combination (norm := module) two_eq_zero • (v₁ + v₁ + s' + s)
    have hsym : herm frob v₁ s' = herm frob s' v₁ := hS.herm_symm hs'S hv₁S
    have hscal : herm frob v₁ x₀ + 1 + (herm frob (v₁ + s) x₀ + 1) + herm frob (v₁ + s) v₁ +
        (herm frob (v₁ + s') x₀ + 1 + (herm frob (v₁ + s' + s) x₀ + 1) +
          herm frob (v₁ + s' + s) (v₁ + s')) +
        herm frob (v₁ + s' + (v₁ + s' + s)) (v₁ + (v₁ + s)) = 1 := by
      simp only [herm_add_left, herm_add_right]
      linear_combination 6 * hv₁ + hs's' + hss + hss' + hsym +
        (2 * herm frob v₁ x₀ + herm frob s x₀ + herm frob s' x₀ + 2 + 2 * herm frob s v₁ +
          3 * herm frob s' v₁ + herm frob v₁ s + herm frob s' s) * two_eq_zero
    rw [hvsum, hscal, zero_add, one_smul] at he
    have heq := IsShape.eq_tvU hS hcS hcchar hcc hx₀S hx₀ he
    have hmem : (QuotientGroup.mk (tvU (v₁ + c) * tvU v₁ * (tvU (v₁ + s + c) * tvU (v₁ + s)) *
        (tvU (v₁ + s' + c) * tvU (v₁ + s') * (tvU (v₁ + s' + s + c) * tvU (v₁ + s' + s)))) :
          PG m) ∈ U := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact U.mul_mem (U.mul_mem hU₁ hU₂) (U.mul_mem hU₃ hU₄)
    exact hDG _ hmem (by rw [heq]; exact tq_mem_DG hc0 hcc)

end Core

end CFSG.LargeExtraspecial.Asc611
