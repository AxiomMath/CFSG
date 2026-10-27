module

public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedSplit
public import CFSG.GH74.Uniqueness.Section174Frame
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.StronglyEmbedded.UniqueCosetBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.GH74.Uniqueness CFSG.StronglyEmbedded.UniqueCoset
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3

namespace T8

section FourGen

variable {G : Type} [Group G]

private theorem mul_self_of_commute_gen {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : x * y * (x * y) = 1 := by
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hxy]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx, hy]; group

private theorem mul_ne_one_of_ne_gen {x y : G} (hx : x * x = 1) (hxy : x ≠ y) : x * y ≠ 1 := by
  intro h
  apply hxy
  calc x = x * 1 := (mul_one x).symm
    _ = x * (x * y) := by rw [h]
    _ = y := by rw [← mul_assoc, hx, one_mul]

private theorem commute_mul_conj_gen {d r : G} (hd : d * d = 1)
    (hr : r * (d * r * d⁻¹) = (d * r * d⁻¹) * r) :
    d * (r * (d * r * d⁻¹)) = (r * (d * r * d⁻¹)) * d := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  rw [hdi] at hr ⊢
  calc d * (r * (d * r * d)) = d * ((d * r * d) * r) := by rw [hr]
    _ = (d * d) * r * (d * r) := by group
    _ = r * (d * r) := by rw [hd, one_mul]
    _ = r * (d * r * (d * d)) := by rw [hd, mul_one]
    _ = (r * (d * r * d)) * d := by group

variable [Finite G] {Ω : Set (Subgroup G)}

theorem exists_four_group_gen {K : Subgroup G} {S' : Sylow 2 G} {R : Subgroup G} {z t g : G}
    (hconj : ConjInvariant Ω) (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hRΩ : R ∈ RSet Ω) (hRsyl : IsSylow2In R K) (hRS' : R ≤ (S' : Subgroup G))
    (hex : ∀ {M : Subgroup G}, M ∈ Ω → ∃ y : G, IsUniqueInvolution M y)
    (hzt : z * t * (z * t) = 1)
    (hfree₀ : ∀ {X M : Subgroup G} {x : G}, X ≤ (S' : Subgroup G) → M ∈ Ω → IsSylow2In X M →
      X ∈ RSet Ω → IsUniqueInvolution M x → conjSub (g⁻¹ * (z * t) * g) X ≠ X)
    (hcomm : ∀ {X Y : Subgroup G}, X ∈ RSet Ω → Y ∈ RSet Ω → X ≤ (S' : Subgroup G) →
      Y ≤ (S' : Subgroup G) → X ≠ Y → Commutes X Y)
    (hmem : ∀ {X : Subgroup G} {x : G}, X ∈ RSet Ω →
      (∃ M ∈ Ω, IsSylow2In X M ∧ IsUniqueInvolution M x) → x ∈ X)
    (hne : ∀ {X Y : Subgroup G} {x y : G},
      (∃ M ∈ Ω, IsSylow2In X M ∧ IsUniqueInvolution M x) →
      (∃ M ∈ Ω, IsSylow2In Y M ∧ IsUniqueInvolution M y) → X ≠ Y → Commutes X Y → x ≠ y)
    (hdS : g⁻¹ * (z * t) * g ∈ (S' : Subgroup G))
    (hcount : 8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S' : Subgroup G)}) :
    ∃ u v : G, u ∈ (S' : Subgroup G) ∧ v ∈ (S' : Subgroup G) ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧
      u * u = 1 ∧ v * v = 1 ∧ u * v = v * u ∧
      (g⁻¹ * (z * t) * g) * u = u * (g⁻¹ * (z * t) * g) ∧
      (g⁻¹ * (z * t) * g) * v = v * (g⁻¹ * (z * t) * g) ∧
      (∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, u * y = y * u) ∧
      (∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, v * y = y * v) := by
  classical
  have hFIconj : ∀ {X : Subgroup G} {x : G},
      (∃ M ∈ Ω, IsSylow2In X M ∧ IsUniqueInvolution M x) → ∀ n : G,
      ∃ M ∈ Ω, IsSylow2In (conjSub n X) M ∧ IsUniqueInvolution M (n * x * n⁻¹) := by
    rintro X x ⟨M, hM, hXM, hx⟩ n
    exact ⟨conjSub n M, hconj n M hM, hXM.conj n, hx.conj n⟩
  have hFIcentral : ∀ {X : Subgroup G} {x : G},
      (∃ M ∈ Ω, IsSylow2In X M ∧ IsUniqueInvolution M x) → ∀ {y : G}, y ∈ X → x * y = y * x := by
    rintro X x ⟨M, hM, hXM, hx⟩ y hy
    have h1 := hx.conj_eq (n := y) (conjSub_eq_self_of_mem (hXM.1 hy))
    calc x * y = (y * x * y⁻¹) * y := by rw [h1]
      _ = y * x := by group
  obtain ⟨d, hd⟩ : ∃ d, d = g⁻¹ * (z * t) * g := ⟨_, rfl⟩
  have hfree : ∀ {X M : Subgroup G} {x : G}, X ≤ (S' : Subgroup G) → M ∈ Ω → IsSylow2In X M →
      X ∈ RSet Ω → IsUniqueInvolution M x → conjSub d X ≠ X := by
    intro X M x hXS hM hXM hXΩ hx
    rw [hd]
    exact hfree₀ hXS hM hXM hXΩ hx
  rw [← hd] at hdS ⊢
  have hdd : d * d = 1 := by
    rw [hd]
    calc g⁻¹ * (z * t) * g * (g⁻¹ * (z * t) * g) = g⁻¹ * (z * t * (z * t)) * g := by group
      _ = 1 := by rw [hzt]; group
  have hdd' : ∀ X : Subgroup G, conjSub d (conjSub d X) = X := by
    intro X
    rw [← conjSub_mul, hdd, conjSub_one]
  have hSmem : ∀ {X : Subgroup G}, X ≤ (S' : Subgroup G) → conjSub d X ≤ (S' : Subgroup G) := by
    intro X hX
    have := conjSub_mono (n := d) hX
    rwa [conjSub_eq_self_of_mem hdS] at this
  have hz₁ : ∃ M ∈ Ω, IsSylow2In R M ∧ IsUniqueInvolution M z := ⟨K, hK, hRsyl, hz⟩
  have hR'Ω : conjSub d R ∈ RSet Ω := RSet.conj hconj hRΩ d
  have hR'S := hSmem hRS'
  have hRR' : conjSub d R ≠ R := hfree hRS' hK hRsyl hRΩ hz
  obtain ⟨X₂, hX₂Ω, hX₂S, hX₂R, hX₂R'⟩ : ∃ X₂ : Subgroup G, X₂ ∈ RSet Ω ∧
      X₂ ≤ (S' : Subgroup G) ∧ X₂ ≠ R ∧ X₂ ≠ conjSub d R := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective
        (fun X : {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S' : Subgroup G)} => decide (X.1 = R)) := by
      intro X Y hXY
      simp only [decide_eq_decide] at hXY
      by_cases hX : X.1 = R
      · exact Subtype.ext (hX.trans (hXY.1 hX).symm)
      · have hY : Y.1 ≠ R := fun h => hX (hXY.2 h)
        exact Subtype.ext ((hcon X.1 X.2.1 X.2.2 hX).trans (hcon Y.1 Y.2.1 Y.2.2 hY).symm)
    have := Nat.card_le_card_of_injective _ hinj
    simp at this
    omega
  obtain ⟨M₂, hM₂, hX₂M₂⟩ := exists_isSylow2In_of_mem_RSet hX₂Ω
  obtain ⟨z₂, hz₂⟩ := hex hM₂
  have hz₂F : ∃ M ∈ Ω, IsSylow2In X₂ M ∧ IsUniqueInvolution M z₂ := ⟨M₂, hM₂, hX₂M₂, hz₂⟩
  have hX₂X₂' : conjSub d X₂ ≠ X₂ := hfree hX₂S hM₂ hX₂M₂ hX₂Ω hz₂
  have hX₂'Ω : conjSub d X₂ ∈ RSet Ω := RSet.conj hconj hX₂Ω d
  have hX₂'S := hSmem hX₂S
  have hz₁' : ∃ M ∈ Ω, IsSylow2In (conjSub d R) M ∧ IsUniqueInvolution M (d * z * d⁻¹) :=
    hFIconj hz₁ d
  have hz₂' : ∃ M ∈ Ω, IsSylow2In (conjSub d X₂) M ∧ IsUniqueInvolution M (d * z₂ * d⁻¹) :=
    hFIconj hz₂F d
  have hRX₂' : R ≠ conjSub d X₂ := by
    intro h
    apply hX₂R'
    calc X₂ = conjSub d (conjSub d X₂) := (hdd' X₂).symm
      _ = conjSub d R := by rw [← h]
  have hR'X₂' : conjSub d R ≠ conjSub d X₂ := by
    intro h
    apply hX₂R
    calc X₂ = conjSub d (conjSub d X₂) := (hdd' X₂).symm
      _ = conjSub d (conjSub d R) := by rw [h]
      _ = R := hdd' R
  have hcm : ∀ {X Y : Subgroup G}, X ∈ RSet Ω → Y ∈ RSet Ω → X ≤ (S' : Subgroup G) →
      Y ≤ (S' : Subgroup G) → X ≠ Y → Commutes X Y := fun hX hY hXS hYS hXY =>
    hcomm hX hY hXS hYS hXY
  have hcent : ∀ {X : Subgroup G} {x : G}, X ∈ RSet Ω → X ≤ (S' : Subgroup G) →
      (∃ M ∈ Ω, IsSylow2In X M ∧ IsUniqueInvolution M x) → ∀ Y ∈ RSet Ω,
      Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, x * y = y * x := by
    intro X x hX hXS hx Y hY hYS y hy
    by_cases hXY : X = Y
    · subst hXY
      exact hFIcentral hx hy
    · exact hcm hX hY hXS hYS hXY x (hmem hX hx) y hy
  have hcentmul : ∀ {x w y : G}, x * y = y * x → w * y = y * w → (x * w) * y = y * (x * w) := by
    intro x w y h1 h2
    calc x * w * y = x * (w * y) := by group
      _ = x * (y * w) := by rw [h2]
      _ = (x * y) * w := by group
      _ = (y * x) * w := by rw [h1]
      _ = y * (x * w) := by group
  obtain ⟨z₁', hz₁'def⟩ : ∃ z₁', z₁' = d * z * d⁻¹ := ⟨_, rfl⟩
  obtain ⟨z₂', hz₂'def⟩ : ∃ z₂', z₂' = d * z₂ * d⁻¹ := ⟨_, rfl⟩
  rw [← hz₁'def] at hz₁'
  rw [← hz₂'def] at hz₂'
  have hzsq : z * z = 1 := hz.sq
  have hz₂sq : z₂ * z₂ = 1 := hz₂.sq
  have hz₁'sq : z₁' * z₁' = 1 := by rw [hz₁'def]; exact (hz.conj d).sq
  have hz₂'sq : z₂' * z₂' = 1 := by rw [hz₂'def]; exact (hz₂.conj d).sq
  have hzS : z ∈ (S' : Subgroup G) := hRS' (hmem hRΩ hz₁)
  have hz₁'S : z₁' ∈ (S' : Subgroup G) := hR'S (hmem hR'Ω hz₁')
  have hz₂S : z₂ ∈ (S' : Subgroup G) := hX₂S (hmem hX₂Ω hz₂F)
  have hz₂'S : z₂' ∈ (S' : Subgroup G) := hX₂'S (hmem hX₂'Ω hz₂')
  have c1 : z * z₁' = z₁' * z := hcm hRΩ hR'Ω hRS' hR'S (Ne.symm hRR') z (hmem hRΩ hz₁) z₁'
    (hmem hR'Ω hz₁')
  have c2 : z * z₂ = z₂ * z := hcm hRΩ hX₂Ω hRS' hX₂S (Ne.symm hX₂R) z (hmem hRΩ hz₁) z₂
    (hmem hX₂Ω hz₂F)
  have c3 : z * z₂' = z₂' * z := hcm hRΩ hX₂'Ω hRS' hX₂'S hRX₂' z (hmem hRΩ hz₁) z₂'
    (hmem hX₂'Ω hz₂')
  have c4 : z₁' * z₂ = z₂ * z₁' := hcm hR'Ω hX₂Ω hR'S hX₂S (Ne.symm hX₂R') z₁'
    (hmem hR'Ω hz₁') z₂ (hmem hX₂Ω hz₂F)
  have c5 : z₁' * z₂' = z₂' * z₁' := hcm hR'Ω hX₂'Ω hR'S hX₂'S hR'X₂' z₁' (hmem hR'Ω hz₁') z₂'
    (hmem hX₂'Ω hz₂')
  have c6 : z₂ * z₂' = z₂' * z₂ := hcm hX₂Ω hX₂'Ω hX₂S hX₂'S (Ne.symm hX₂X₂') z₂
    (hmem hX₂Ω hz₂F) z₂' (hmem hX₂'Ω hz₂')
  have n1 : z ≠ z₁' := hne hz₁ hz₁' (Ne.symm hRR') (hcm hRΩ hR'Ω hRS' hR'S (Ne.symm hRR'))
  have n2 : z₂ ≠ z₂' := hne hz₂F hz₂' (Ne.symm hX₂X₂')
    (hcm hX₂Ω hX₂'Ω hX₂S hX₂'S (Ne.symm hX₂X₂'))
  have n3 : z ≠ z₂ := hne hz₁ hz₂F (Ne.symm hX₂R) (hcm hRΩ hX₂Ω hRS' hX₂S (Ne.symm hX₂R))
  have n4 : z₂ ≠ z₁' := hne hz₂F hz₁' hX₂R' (hcm hX₂Ω hR'Ω hX₂S hR'S hX₂R')
  have k1 : ∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, z * y = y * z :=
    hcent hRΩ hRS' hz₁
  have k1' : ∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, z₁' * y = y * z₁' :=
    hcent hR'Ω hR'S hz₁'
  have k2 : ∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, z₂ * y = y * z₂ :=
    hcent hX₂Ω hX₂S hz₂F
  have k2' : ∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, z₂' * y = y * z₂' :=
    hcent hX₂'Ω hX₂'S hz₂'
  have e1sq : z * z₁' * (z * z₁') = 1 := mul_self_of_commute_gen hzsq hz₁'sq c1
  have e2sq : z₂ * z₂' * (z₂ * z₂') = 1 := mul_self_of_commute_gen hz₂sq hz₂'sq c6
  have e1ne : z * z₁' ≠ 1 := mul_ne_one_of_ne_gen hzsq n1
  have e2ne : z₂ * z₂' ≠ 1 := mul_ne_one_of_ne_gen hz₂sq n2
  have hdc1 : d * (z * z₁') = (z * z₁') * d := by
    rw [hz₁'def]
    exact commute_mul_conj_gen hdd (by rw [← hz₁'def]; exact c1)
  have hdc2 : d * (z₂ * z₂') = (z₂ * z₂') * d := by
    rw [hz₂'def]
    exact commute_mul_conj_gen hdd (by rw [← hz₂'def]; exact c6)
  have e12 : (z * z₁') * (z₂ * z₂') = (z₂ * z₂') * (z * z₁') :=
    ((Commute.mul_right (show Commute z z₂ from c2) (show Commute z z₂' from c3)).mul_left
      (Commute.mul_right (show Commute z₁' z₂ from c4) (show Commute z₁' z₂' from c5)))
  have e1S : z * z₁' ∈ (S' : Subgroup G) := S'.mul_mem hzS hz₁'S
  have e2S : z₂ * z₂' ∈ (S' : Subgroup G) := S'.mul_mem hz₂S hz₂'S
  have ke1 : ∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, (z * z₁') * y = y * (z * z₁') :=
    fun Y hY hYS y hy => hcentmul (k1 Y hY hYS y hy) (k1' Y hY hYS y hy)
  have ke2 : ∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, (z₂ * z₂') * y = y * (z₂ * z₂') :=
    fun Y hY hYS y hy => hcentmul (k2 Y hY hYS y hy) (k2' Y hY hYS y hy)
  by_cases hee : z * z₁' = z₂ * z₂'
  ·
    have h1' : z₁' = z * (z₂ * z₂') := by
      calc z₁' = z * (z * z₁') := by rw [← mul_assoc, hzsq, one_mul]
        _ = z * (z₂ * z₂') := by rw [hee]
    have hA' : z₁' * z₂' = z * z₂ := by
      rw [h1']
      calc z * (z₂ * z₂') * z₂' = z * z₂ * (z₂' * z₂') := by group
        _ = z * z₂ := by rw [hz₂'sq, mul_one]
    have hdA : d * (z * z₂) = (z * z₂) * d := by
      calc d * (z * z₂) = (d * z * d⁻¹) * (d * z₂ * d⁻¹) * d := by group
        _ = (z₁' * z₂') * d := by rw [hz₁'def, hz₂'def]
        _ = (z * z₂) * d := by rw [hA']
    have hAv : z * z₂ * (z * z₁') = z * z₁' * (z * z₂) :=
      ((Commute.mul_right (Commute.refl z) (show Commute z z₁' from c1)).mul_left
        (Commute.mul_right (show Commute z₂ z from c2.symm) (show Commute z₂ z₁' from c4.symm)))
    refine ⟨z * z₂, z * z₁', S'.mul_mem hzS hz₂S, e1S, mul_ne_one_of_ne_gen hzsq n3, e1ne, ?_,
      mul_self_of_commute_gen hzsq hz₂sq c2, e1sq, hAv, hdA, hdc1,
      fun Y hY hYS y hy => hcentmul (k1 Y hY hYS y hy) (k2 Y hY hYS y hy), ke1⟩
    intro h
    exact n4 (mul_left_cancel h)
  · refine ⟨z * z₁', z₂ * z₂', e1S, e2S, e1ne, e2ne, hee, e1sq, e2sq, e12, hdc1, hdc2, ke1, ke2⟩

end FourGen

end T8

end CFSG.ClassicalInvolution.Asc77
