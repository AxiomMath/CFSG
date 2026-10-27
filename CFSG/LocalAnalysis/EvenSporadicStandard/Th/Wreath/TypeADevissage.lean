module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.TypeA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.MartineauConj

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

private noncomputable def layerSection (X : Subgroup G) (ψ : G → G) : G → G :=
  fun a => by
    classical
    exact if h : ∃ x ∈ X, ψ x = a then Classical.choose h else 1

private theorem layerSection_mem {X : Subgroup G} {ψ : G → G} {a : G}
    (h : ∃ x ∈ X, ψ x = a) : layerSection X ψ a ∈ X := by
  rw [layerSection, dif_pos h]
  exact (Classical.choose_spec h).1

private theorem layerSection_val {X : Subgroup G} {ψ : G → G} {a : G}
    (h : ∃ x ∈ X, ψ x = a) : ψ (layerSection X ψ a) = a := by
  rw [layerSection, dif_pos h]
  exact (Classical.choose_spec h).2

private theorem IsLayer.map_eq_one_of_mem {Z₁ Z₂ : Subgroup G} {χ : G → G}
    (hχ : IsLayer L A Z₁ Z₂ χ) {z : G} (hz : z ∈ Z₁) :
    χ z = 1 :=
  (hχ.eq_one_iff z (hχ.le hz)).2 hz

private theorem IsLayer.map_mul_ker {Z₁ Z₂ : Subgroup G} {χ : G → G}
    (hχ : IsLayer L A Z₁ Z₂ χ) {p q z : G}
    (hp : p ∈ Z₂) (hq : q ∈ Z₂) (hz : z ∈ Z₁) : χ (p * q * z) = χ p * χ q := by
  rw [hχ.map_mul (p * q) (Z₂.mul_mem hp hq) z (hχ.le hz),
    hχ.map_mul p hp q hq, hχ.map_eq_one_of_mem hz, mul_one]

private theorem IsLayer.bilinear_conj_left {X₀ X Y₂ Z₀ Z₁ Z₂ : Subgroup G} {ψ χ : G → G}
    (hX : IsLayer L A X₀ X ψ) (hχ : IsLayer L A Z₁ Z₂ χ) {β : G → G → G}
    (hβl : ∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y₂, (β x y * β x' y)⁻¹ * β (x * x') y ∈ Z₀)
    (hβX₀ : ∀ x ∈ X₀, ∀ y ∈ Y₂, β x y ∈ Z₀) {x x' y : G} (hx : x ∈ X) (hx' : x' ∈ X)
    (hψ : ψ x = ψ x') (hy : y ∈ Y₂) (hβx'y : β x' y ∈ Z₂) (hZ : Z₀ ≤ Z₁) :
    χ (β x y) = χ (β x' y) := by
  have hu : x * x'⁻¹ ∈ X₀ := hX.inf_mem_of_map_eq hx hx' hψ
  obtain ⟨z, hz, hzdef⟩ : ∃ z ∈ Z₀, β x y = β (x * x'⁻¹) y * β x' y * z := by
    refine ⟨(β (x * x'⁻¹) y * β x' y)⁻¹ * β ((x * x'⁻¹) * x') y, ?_, ?_⟩
    · exact hβl _ (hX.le hu) x' hx' y hy
    · have e : (x * x'⁻¹) * x' = x := by group
      rw [e]
      group
  have hβu : β (x * x'⁻¹) y ∈ Z₀ := hβX₀ _ hu y hy
  rw [hzdef, hχ.map_mul_ker (hχ.le (hZ hβu)) hβx'y (hZ hz),
    hχ.map_eq_one_of_mem (hZ hβu), one_mul]

private theorem IsLayer.bilinear_conj_right {X Y₁ Y₂ Z₀ Z₁ Z₂ : Subgroup G} {ψY χ : G → G}
    (hY : IsLayer L A Y₁ Y₂ ψY) (hχ : IsLayer L A Z₁ Z₂ χ) {β : G → G → G}
    (hβr : ∀ x ∈ X, ∀ y ∈ Y₂, ∀ y' ∈ Y₂, (β x y * β x y')⁻¹ * β x (y * y') ∈ Z₀)
    (hβY₁ : ∀ x ∈ X, ∀ y ∈ Y₁, β x y ∈ Z₀) {x y y' : G} (hx : x ∈ X) (hy : y ∈ Y₂)
    (hy' : y' ∈ Y₂) (hψ : ψY y = ψY y') (hβxy' : β x y' ∈ Z₂) (hZ : Z₀ ≤ Z₁) :
    χ (β x y) = χ (β x y') := by
  have hv : y * y'⁻¹ ∈ Y₁ := hY.inf_mem_of_map_eq hy hy' hψ
  obtain ⟨z, hz, hzdef⟩ : ∃ z ∈ Z₀, β x y = β x (y * y'⁻¹) * β x y' * z := by
    refine ⟨(β x (y * y'⁻¹) * β x y')⁻¹ * β x ((y * y'⁻¹) * y'), ?_, ?_⟩
    · exact hβr _ hx _ (hY.le hv) _ hy'
    · have e : (y * y'⁻¹) * y' = y := by group
      rw [e]
      group
  have hβv : β x (y * y'⁻¹) ∈ Z₀ := hβY₁ _ hx _ hv
  rw [hzdef, hχ.map_mul_ker (hχ.le (hZ hβv)) hβxy' (hZ hz),
    hχ.map_eq_one_of_mem (hZ hβv), one_mul]

private theorem IsLayer.bilinear_mem_single (W : ThLocalIn L S A B z)
    {X₀ X Y₁ Y₂ Z₀ Z : Subgroup G} {ψ ψY : G → G} (hX : IsLayer L A X₀ X ψ)
    (hY : IsLayer L A Y₁ Y₂ ψY) (hZ : IsTypeA L A Z₀ Z) (β : G → G → G)
    (hβZ : ∀ x ∈ X, ∀ y ∈ Y₂, β x y ∈ Z)
    (hβX₀ : ∀ x ∈ X₀, ∀ y ∈ Y₂, β x y ∈ Z₀)
    (hβY₁ : ∀ x ∈ X, ∀ y ∈ Y₁, β x y ∈ Z₀)
    (hβl : ∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y₂, (β x y * β x' y)⁻¹ * β (x * x') y ∈ Z₀)
    (hβr : ∀ x ∈ X, ∀ y ∈ Y₂, ∀ y' ∈ Y₂, (β x y * β x y')⁻¹ * β x (y * y') ∈ Z₀)
    (hβH : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ x ∈ X, ∀ y ∈ Y₂,
      β (n * x * n⁻¹) (n * y * n⁻¹) = n * β x y * n⁻¹) :
    ∀ x ∈ X, ∀ y ∈ Y₂, β x y ∈ Z₀ := by
  revert hβZ
  refine IsTypeA.rec (motive := fun Z _ => (∀ x ∈ X, ∀ y ∈ Y₂, β x y ∈ Z) →
    ∀ x ∈ X, ∀ y ∈ Y₂, β x y ∈ Z₀) ?_ ?_ hZ
  · intro hZnorm hβZ x hx y hy
    exact hβZ x hx y hy
  · intro Z₁ Z₂ χ hZ' hχ ih hβZ
    classical
    let sX : G → G := layerSection X ψ
    let sY : G → G := layerSection Y₂ ψY
    have hsX_mem : ∀ a ∈ A, sX a ∈ X := fun a ha => layerSection_mem (hX.surj a ha)
    have hsX_val : ∀ a ∈ A, ψ (sX a) = a := fun a ha => layerSection_val (hX.surj a ha)
    have hsY_mem : ∀ a ∈ A, sY a ∈ Y₂ := fun a ha => layerSection_mem (hY.surj a ha)
    have hsY_val : ∀ a ∈ A, ψY (sY a) = a := fun a ha => layerSection_val (hY.surj a ha)
    let γ : G → G → G := fun a a' => χ (β (sX a) (sY a'))
    have hγA : ∀ a ∈ A, ∀ a' ∈ A, γ a a' ∈ A := by
      intro a ha a' ha'
      exact hχ.mem _ (hβZ _ (hsX_mem a ha) _ (hsY_mem a' ha'))
    have hγl : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ a' ∈ A, γ (a₁ * a₂) a' = γ a₁ a' * γ a₂ a' := by
      intro a₁ ha₁ a₂ ha₂ a' ha'
      have hx₁ : sX a₁ ∈ X := hsX_mem a₁ ha₁
      have hx₂ : sX a₂ ∈ X := hsX_mem a₂ ha₂
      have hx : sX (a₁ * a₂) ∈ X := hsX_mem (a₁ * a₂) (A.mul_mem ha₁ ha₂)
      have hx₁₂ : sX a₁ * sX a₂ ∈ X := X.mul_mem hx₁ hx₂
      have hy' : sY a' ∈ Y₂ := hsY_mem a' ha'
      have hψ : ψ (sX (a₁ * a₂)) = ψ (sX a₁ * sX a₂) := by
        rw [hsX_val (a₁ * a₂) (A.mul_mem ha₁ ha₂), hX.map_mul (sX a₁) hx₁ (sX a₂) hx₂,
          hsX_val a₁ ha₁, hsX_val a₂ ha₂]
      have hstep1 : χ (β (sX (a₁ * a₂)) (sY a')) =
          χ (β (sX a₁ * sX a₂) (sY a')) :=
        hX.bilinear_conj_left hχ hβl hβX₀ hx hx₁₂ hψ hy'
          (hβZ _ hx₁₂ _ hy') hZ'.le
      have hstep2 : χ (β (sX a₁ * sX a₂) (sY a')) =
          χ (β (sX a₁) (sY a')) * χ (β (sX a₂) (sY a')) := by
        obtain ⟨z, hz, hzdef⟩ : ∃ z ∈ Z₀, β (sX a₁ * sX a₂) (sY a') =
            β (sX a₁) (sY a') * β (sX a₂) (sY a') * z := by
          refine ⟨(β (sX a₁) (sY a') * β (sX a₂) (sY a'))⁻¹ *
            β (sX a₁ * sX a₂) (sY a'), ?_, ?_⟩
          · exact hβl _ hx₁ _ hx₂ _ hy'
          · group
        rw [hzdef, hχ.map_mul_ker (hβZ _ hx₁ _ hy') (hβZ _ hx₂ _ hy') (hZ'.le hz)]
      show χ (β (sX (a₁ * a₂)) (sY a')) =
        χ (β (sX a₁) (sY a')) * χ (β (sX a₂) (sY a'))
      exact hstep1.trans hstep2
    have hγr : ∀ a ∈ A, ∀ a₁ ∈ A, ∀ a₂ ∈ A, γ a (a₁ * a₂) = γ a a₁ * γ a a₂ := by
      intro a ha a₁ ha₁ a₂ ha₂
      have hx : sX a ∈ X := hsX_mem a ha
      have hy₁ : sY a₁ ∈ Y₂ := hsY_mem a₁ ha₁
      have hy₂ : sY a₂ ∈ Y₂ := hsY_mem a₂ ha₂
      have hy : sY (a₁ * a₂) ∈ Y₂ := hsY_mem (a₁ * a₂) (A.mul_mem ha₁ ha₂)
      have hy₁₂ : sY a₁ * sY a₂ ∈ Y₂ := Y₂.mul_mem hy₁ hy₂
      have hψ : ψY (sY (a₁ * a₂)) = ψY (sY a₁ * sY a₂) := by
        rw [hsY_val (a₁ * a₂) (A.mul_mem ha₁ ha₂), hY.map_mul (sY a₁) hy₁ (sY a₂) hy₂,
          hsY_val a₁ ha₁, hsY_val a₂ ha₂]
      have hstep1 : χ (β (sX a) (sY (a₁ * a₂))) =
          χ (β (sX a) (sY a₁ * sY a₂)) :=
        hY.bilinear_conj_right hχ hβr hβY₁ hx hy hy₁₂ hψ
          (hβZ _ hx _ hy₁₂) hZ'.le
      have hstep2 : χ (β (sX a) (sY a₁ * sY a₂)) =
          χ (β (sX a) (sY a₁)) * χ (β (sX a) (sY a₂)) := by
        obtain ⟨z, hz, hzdef⟩ : ∃ z ∈ Z₀, β (sX a) (sY a₁ * sY a₂) =
            β (sX a) (sY a₁) * β (sX a) (sY a₂) * z := by
          refine ⟨(β (sX a) (sY a₁) * β (sX a) (sY a₂))⁻¹ *
            β (sX a) (sY a₁ * sY a₂), ?_, ?_⟩
          · exact hβr _ hx _ hy₁ _ hy₂
          · group
        rw [hzdef, hχ.map_mul_ker (hβZ _ hx _ hy₁) (hβZ _ hx _ hy₂) (hZ'.le hz)]
      show χ (β (sX a) (sY (a₁ * a₂))) =
        χ (β (sX a) (sY a₁)) * χ (β (sX a) (sY a₂))
      exact hstep1.trans hstep2
    have hγn : ∀ n ∈ L, (∀ a ∈ A, n * a * n⁻¹ ∈ A) → ∀ a ∈ A, ∀ a' ∈ A,
        γ (n * a * n⁻¹) (n * a' * n⁻¹) = n * γ a a' * n⁻¹ := by
      intro n hnL hnA a ha a' ha'
      have hnH : n ∈ L ⊓ normalizer (A : Set G) :=
        W.mem_inf_normalizer_of_forall_conj_mem hnL hnA
      have hna : n * a * n⁻¹ ∈ A := hnA a ha
      have hna' : n * a' * n⁻¹ ∈ A := hnA a' ha'
      have hx₁ : sX (n * a * n⁻¹) ∈ X := hsX_mem _ hna
      have hx₂ : n * sX a * n⁻¹ ∈ X := hX.conj_mem n hnH _ (hsX_mem a ha)
      have hψX : ψ (sX (n * a * n⁻¹)) = ψ (n * sX a * n⁻¹) := by
        rw [hsX_val _ hna, hX.conj n hnH (sX a) (hsX_mem a ha), hsX_val a ha]
      have hy₁ : sY (n * a' * n⁻¹) ∈ Y₂ := hsY_mem _ hna'
      have hstepX : χ (β (sX (n * a * n⁻¹)) (sY (n * a' * n⁻¹))) =
          χ (β (n * sX a * n⁻¹) (sY (n * a' * n⁻¹))) :=
        hX.bilinear_conj_left hχ hβl hβX₀ hx₁ hx₂ hψX hy₁
          (hβZ _ hx₂ _ hy₁) hZ'.le
      have hy₂ : n * sY a' * n⁻¹ ∈ Y₂ := hY.conj_mem n hnH _ (hsY_mem a' ha')
      have hψY : ψY (sY (n * a' * n⁻¹)) = ψY (n * sY a' * n⁻¹) := by
        rw [hsY_val _ hna', hY.conj n hnH (sY a') (hsY_mem a' ha'), hsY_val a' ha']
      have hstepY : χ (β (n * sX a * n⁻¹) (sY (n * a' * n⁻¹))) =
          χ (β (n * sX a * n⁻¹) (n * sY a' * n⁻¹)) :=
        hY.bilinear_conj_right hχ hβr hβY₁ hx₂ hy₁ hy₂ hψY
          (hβZ _ hx₂ _ hy₂) hZ'.le
      have hstepH : χ (β (n * sX a * n⁻¹) (n * sY a' * n⁻¹)) =
          n * χ (β (sX a) (sY a')) * n⁻¹ := by
        rw [hβH n hnH (sX a) (hsX_mem a ha) (sY a') (hsY_mem a' ha')]
        exact hχ.conj n hnH _ (hβZ _ (hsX_mem a ha) _ (hsY_mem a' ha'))
      show χ (β (sX (n * a * n⁻¹)) (sY (n * a' * n⁻¹))) =
        n * χ (β (sX a) (sY a')) * n⁻¹
      exact hstepX.trans (hstepY.trans hstepH)
    have hγeq : ∀ a ∈ A, ∀ a' ∈ A, γ a a' = 1 :=
      ThLocalIn.martineau_conj W γ hγA hγl hγr hγn
    have hβZ₁ : ∀ x ∈ X, ∀ y ∈ Y₂, β x y ∈ Z₁ := by
      intro x hx y hy
      have hχβ : χ (β x y) = 1 := by
        have h1 : γ (ψ x) (ψY y) = 1 :=
          hγeq (ψ x) (hX.mem x hx) (ψY y) (hY.mem y hy)
        have hx' : sX (ψ x) ∈ X := hsX_mem _ (hX.mem x hx)
        have hy' : sY (ψY y) ∈ Y₂ := hsY_mem _ (hY.mem y hy)
        have hψX : ψ (sX (ψ x)) = ψ x := by rw [hsX_val _ (hX.mem x hx)]
        have hψY : ψY (sY (ψY y)) = ψY y := by rw [hsY_val _ (hY.mem y hy)]
        have e1 : χ (β (sX (ψ x)) (sY (ψY y))) = χ (β x (sY (ψY y))) :=
          hX.bilinear_conj_left hχ hβl hβX₀ hx' hx hψX hy' (hβZ _ hx _ hy') hZ'.le
        have e2 : χ (β x (sY (ψY y))) = χ (β x y) :=
          hY.bilinear_conj_right hχ hβr hβY₁ hx hy' hy hψY (hβZ _ hx _ hy) hZ'.le
        exact (e2.symm.trans e1.symm).trans h1
      exact (hχ.eq_one_iff _ (hβZ x hx y hy)).1 hχβ
    exact fun x hx y hy => ih hβZ₁ x hx y hy

theorem IsTypeA.bilinear_mem (W : ThLocalIn L S A B z)
    {X₀ X Y₀ Y Z₀ Z : Subgroup G} {ψ : G → G} (hX : IsLayer L A X₀ X ψ)
    (hY : IsTypeA L A Y₀ Y) (hZ : IsTypeA L A Z₀ Z) (β : G → G → G)
    (hβZ : ∀ x ∈ X, ∀ y ∈ Y, β x y ∈ Z)
    (hβX₀ : ∀ x ∈ X₀, ∀ y ∈ Y, β x y ∈ Z₀)
    (hβY₀ : ∀ x ∈ X, ∀ y ∈ Y₀, β x y ∈ Z₀)
    (hβl : ∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y, (β x y * β x' y)⁻¹ * β (x * x') y ∈ Z₀)
    (hβr : ∀ x ∈ X, ∀ y ∈ Y, ∀ y' ∈ Y, (β x y * β x y')⁻¹ * β x (y * y') ∈ Z₀)
    (hβH : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ x ∈ X, ∀ y ∈ Y,
      β (n * x * n⁻¹) (n * y * n⁻¹) = n * β x y * n⁻¹) :
    ∀ x ∈ X, ∀ y ∈ Y, β x y ∈ Z₀ := by
  revert hβZ hβX₀ hβl hβr hβH
  refine IsTypeA.rec (motive := fun Y _ =>
    (∀ x ∈ X, ∀ y ∈ Y, β x y ∈ Z) →
    (∀ x ∈ X₀, ∀ y ∈ Y, β x y ∈ Z₀) →
    (∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y, (β x y * β x' y)⁻¹ * β (x * x') y ∈ Z₀) →
    (∀ x ∈ X, ∀ y ∈ Y, ∀ y' ∈ Y, (β x y * β x y')⁻¹ * β x (y * y') ∈ Z₀) →
    (∀ n ∈ L ⊓ normalizer (A : Set G), ∀ x ∈ X, ∀ y ∈ Y,
      β (n * x * n⁻¹) (n * y * n⁻¹) = n * β x y * n⁻¹) →
    ∀ x ∈ X, ∀ y ∈ Y, β x y ∈ Z₀) ?_ ?_ hY
  · intro hYnorm hβZ hβX₀ hβl hβr hβH x hx y hy
    exact hβY₀ x hx y hy
  · intro Y₁ Y₂ ψY hY' hψ ih hβZ hβX₀ hβl hβr hβH x hx y hy
    have hβZ₁ : ∀ x ∈ X, ∀ y ∈ Y₁, β x y ∈ Z := fun x hx y hy => hβZ x hx y (hψ.le hy)
    have hβX₀₁ : ∀ x ∈ X₀, ∀ y ∈ Y₁, β x y ∈ Z₀ :=
      fun x hx y hy => hβX₀ x hx y (hψ.le hy)
    have hβl₁ : ∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y₁,
        (β x y * β x' y)⁻¹ * β (x * x') y ∈ Z₀ :=
      fun x hx x' hx' y hy => hβl x hx x' hx' y (hψ.le hy)
    have hβr₁ : ∀ x ∈ X, ∀ y ∈ Y₁, ∀ y' ∈ Y₁,
        (β x y * β x y')⁻¹ * β x (y * y') ∈ Z₀ :=
      fun x hx y hy y' hy' => hβr x hx y (hψ.le hy) y' (hψ.le hy')
    have hβH₁ : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ x ∈ X, ∀ y ∈ Y₁,
        β (n * x * n⁻¹) (n * y * n⁻¹) = n * β x y * n⁻¹ :=
      fun n hn x hx y hy => hβH n hn x hx y (hψ.le hy)
    have hbase : ∀ x ∈ X, ∀ y ∈ Y₁, β x y ∈ Z₀ := ih hβZ₁ hβX₀₁ hβl₁ hβr₁ hβH₁
    exact IsLayer.bilinear_mem_single W hX hψ hZ β hβZ hβX₀ hbase hβl hβr hβH x hx y hy

end CFSG.EvenSporadicStandard.ThStd

end
