module

public import CFSG.LieType.Ree.LargeReeEightRelations
public import CFSG.LieType.Ree.LargeReeEightPairings
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesSplittingCommuting

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem coordRoot_two (f : Fin 4) : coordRoot (2, f) = fourRoot f 2 :=
  rfl

variable {K : Type} [Field K] [CharP K F4.prime]

theorem fourCoord_zero_zero
    (f : Fin 4) : fourCoord f (0 : K) 0 = 1 :=
  coordElt_zero (2, f)

variable [Finite K]

theorem fourCoord_zero_inv
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (f : Fin 4) (d : K) :
    (fourCoord f 0 d)⁻¹ = fourCoord f 0 (-d) := by
  rw [inv_eq_iff_mul_eq_one, ← fourCoord_zero_add hK, add_neg_cancel, fourCoord_zero_zero]

theorem fourCoord_zero_sq
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (f : Fin 4) (d : K) :
    fourCoord f 0 d ^ 2 = 1 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [sq, ← fourCoord_zero_add hK, CharTwo.add_self_eq_zero, fourCoord_zero_zero]

theorem torusPair_conj_fourCoord_zero
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (u : Kˣ × Kˣ)
    (f : Fin 4) (d : K) :
    torusPair 1 u * fourCoord f 0 d * (torusPair 1 u)⁻¹ =
      fourCoord f 0 ((torusWeight 1 (fourRoot f 2) u : K) * d) := by
  rw [torusPair_conj_fourCoord hK u f 0 d, mul_zero]

variable
    {E : Type*} [Group E] (η : E →* F4.reeGamma K 1)

theorem coe_map_commutatorElement
    (a b : E) :
    ((η ⁅a, b⁆ : F4.reeGamma K 1) : ModGL F4.tag K) =
      ⁅((η a : F4.reeGamma K 1) : ModGL F4.tag K), ((η b : F4.reeGamma K 1) : ModGL F4.tag K)⁆ := by
  simp only [commutatorElement_def, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

variable {η} (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E)
include hη hC

theorem lift_commute_central
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) {f f' : Fin 4}
    (hcomm : ∀ d d' : K, Commute (fourCoord f 0 d) (fourCoord f' 0 d')) (a y : E)
    (ha : ∃ d : K, ((η a : F4.reeGamma K 1) : ModGL F4.tag K) = fourCoord f 0 d)
    (hy : ∃ d' : K, ((η y : F4.reeGamma K 1) : ModGL F4.tag K) = fourCoord f' 0 d') :
    a * y = y * a := by
  have hK' : Nat.card K = F4.prime ^ (2 * 1 + 1) := hK
  have hmem : ∀ (g : Fin 4) (d : K), fourCoord g 0 d ∈ F4.reeGamma K 1 := fun g d =>
    fourCoord_mem_reeGamma hK g 0 d
  let Z : Fin 4 → Subgroup (F4.reeGamma K 1) := fun g =>
    { carrier := {x | ∃ d : K, (x : ModGL F4.tag K) = fourCoord g 0 d}
      mul_mem' := by
        rintro _ _ ⟨d, hd⟩ ⟨d', hd'⟩
        exact ⟨d + d', by rw [Subgroup.coe_mul, hd, hd', fourCoord_zero_add hK]⟩
      one_mem' := ⟨0, by rw [Subgroup.coe_one, fourCoord_zero_zero]⟩
      inv_mem' := by
        rintro _ ⟨d, hd⟩
        exact ⟨-d, by rw [Subgroup.coe_inv, hd, fourCoord_zero_inv hK]⟩ }
  have hZ : ∀ (g : Fin 4) (d : K), (⟨fourCoord g 0 d, hmem g d⟩ : F4.reeGamma K 1) ∈ Z g :=
    fun g d => ⟨d, rfl⟩
  have hZeq : ∀ (g : Fin 4) {x : F4.reeGamma K 1}, x ∈ Z g →
      ∃ d : K, x = ⟨fourCoord g 0 d, hmem g d⟩ := by
    rintro g x ⟨d, hd⟩
    exact ⟨d, Subtype.ext hd⟩
  let τΓ : Kˣ × Kˣ → F4.reeGamma K 1 := fun t => ⟨torusPair 1 t, torusPair_mem_reeGamma 1 hK' t⟩
  have hτ : ∀ (t : Kˣ × Kˣ) (g : Fin 4) (d : K),
      τΓ t * ⟨fourCoord g 0 d, hmem g d⟩ * (τΓ t)⁻¹ =
        ⟨fourCoord g 0 ((torusWeight 1 (fourRoot g 2) t : K) * d), hmem g _⟩ := fun t g d =>
    Subtype.ext (torusPair_conj_fourCoord_zero hK t g d)
  have hnd : ¬ Exceptional (2, f) (2, f') := by
    simp [Exceptional]
  have hnd' := coord_pair_check hnd
  rw [coordRoot_two, coordRoot_two] at hnd'
  refine lift_commute_of_form_eq_zero η hη hC τΓ (Z f) (Z f') (fun x hx x' hx' => ?_)
    (fun x hx => ?_) (fun b hb₁ hb₂ hbT x hx x' hx' => ?_) a y ha hy
  · obtain ⟨d, rfl⟩ := hZeq f hx
    obtain ⟨d', rfl⟩ := hZeq f' hx'
    exact Subtype.ext (hcomm d d').eq
  · obtain ⟨d, rfl⟩ := hZeq f hx
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, fourCoord_zero_sq hK])
  · obtain ⟨d, rfl⟩ := hZeq f hx
    obtain ⟨d', rfl⟩ := hZeq f' hx'
    refine torusWeight_form_eq_zero_of 1 hK hnd'
      (fun d d' => b ⟨fourCoord f 0 d, hmem f d⟩ ⟨fourCoord f' 0 d', hmem f' d'⟩)
      (fun d₁ d₂ d' => ?_) (fun d d₁ d₂ => ?_) (fun t d d' => ?_) d d'
    · have e : (⟨fourCoord f 0 (d₁ + d₂), hmem f _⟩ : F4.reeGamma K 1) =
          ⟨fourCoord f 0 d₁, hmem f d₁⟩ * ⟨fourCoord f 0 d₂, hmem f d₂⟩ :=
        Subtype.ext (fourCoord_zero_add hK f d₁ d₂)
      change b _ _ = b _ _ + b _ _
      rw [e]
      exact hb₁ _ (hZ f d₁) _ (hZ f d₂) _ (hZ f' d')
    · have e : (⟨fourCoord f' 0 (d₁ + d₂), hmem f' _⟩ : F4.reeGamma K 1) =
          ⟨fourCoord f' 0 d₁, hmem f' d₁⟩ * ⟨fourCoord f' 0 d₂, hmem f' d₂⟩ :=
        Subtype.ext (fourCoord_zero_add hK f' d₁ d₂)
      change b _ _ = b _ _ + b _ _
      rw [e]
      exact hb₂ _ (hZ f d) _ (hZ f' d₁) _ (hZ f' d₂)
    · rw [← hτ t f d, ← hτ t f' d']
      exact hbT t _ (hZ f d) _ (hZ f' d')

theorem lift_commute_three
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (x w : E)
    (hx : ∃ c d : K, ((η x : F4.reeGamma K 1) : ModGL F4.tag K) = fourCoord 3 c d)
    (hw : ∃ e : K, ((η w : F4.reeGamma K 1) : ModGL F4.tag K) = fourCoord 3 0 e) :
    x * w = w * x := by
  obtain ⟨c, d, hx⟩ := hx
  obtain ⟨e, hw⟩ := hw
  have hcen : ∀ z ∈ η.ker, ∀ g : E, z * g = g * z := fun z hz g =>
    ((Subgroup.mem_center_iff.1 (hC hz)) g).symm
  have hker : ∀ g : E, ((η g : F4.reeGamma K 1) : ModGL F4.tag K) = 1 → g ∈ η.ker :=
    fun g hg => (MonoidHom.mem_ker).2 (Subtype.ext hg)
  obtain ⟨y, hy⟩ := hη ⟨twoCoord 0 1, twoCoord_mem_reeGamma hK 0 1⟩
  obtain ⟨z, hz⟩ := hη ⟨fourCoord 2 0 e, fourCoord_mem_reeGamma hK 2 0 e⟩
  have hy' : ((η y : F4.reeGamma K 1) : ModGL F4.tag K) = twoCoord 0 1 := by rw [hy]
  have hz' : ((η z : F4.reeGamma K 1) : ModGL F4.tag K) = fourCoord 2 0 e := by rw [hz]
  have hyz : ((η ⁅y, z⁆ : F4.reeGamma K 1) : ModGL F4.tag K) = fourCoord 3 0 e := by
    rw [coe_map_commutatorElement, hy', hz', commutator_twoCoord_fourCoord, one_mul]
  set v := ⁅x, y⁆ with hvdef
  have hv : ((η v : F4.reeGamma K 1) : ModGL F4.tag K) = fourCoord 1 0 c := by
    rw [hvdef, coe_map_commutatorElement, hx, hy', commutator_fourCoord_twoCoord hK, mul_one]
  set c₁ := ⁅x, z⁆ with hc₁def
  have hc₁ : c₁ ∈ η.ker := hker _ (by
    rw [hc₁def, coe_map_commutatorElement, hx, hz', commutatorElement_eq_one_iff_mul_comm]
    exact (commute_fourCoord_three_two hK c d e).eq)
  have hvz : v * z = z * v := lift_commute_central hη hC hK commute_fourCoord_one_two v z
    ⟨c, hv⟩ ⟨e, hz'⟩
  have hvyz : v * ⁅y, z⁆ = ⁅y, z⁆ * v := lift_commute_central hη hC hK
    commute_fourCoord_one_three v ⁅y, z⁆ ⟨c, hv⟩ ⟨e, hyz⟩
  have hc₁' := hcen c₁ hc₁
  have e1 : x * y * x⁻¹ = v * y := by
    rw [hvdef, commutatorElement_def]
    group
  have e2 : x * z * x⁻¹ = c₁ * z := by
    rw [hc₁def, commutatorElement_def]
    group
  have key : x * ⁅y, z⁆ * x⁻¹ = ⁅y, z⁆ := by
    calc x * ⁅y, z⁆ * x⁻¹ =
        (x * y * x⁻¹) * (x * z * x⁻¹) * (x * y * x⁻¹)⁻¹ * (x * z * x⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = v * y * c₁ * z * (v * y)⁻¹ * z⁻¹ * c₁⁻¹ := by
          rw [e1, e2]
          group
      _ = c₁ * (v * y * z * (v * y)⁻¹ * z⁻¹) * c₁⁻¹ := by
          rw [← hc₁' (v * y)]
          group
      _ = v * ⁅y, z⁆ * v⁻¹ * (v * z * v⁻¹ * z⁻¹) := by
          rw [hc₁', commutatorElement_def]
          group
      _ = ⁅y, z⁆ := by
          rw [hvz, hvyz]
          group
  have hc₀ : w * ⁅y, z⁆⁻¹ ∈ η.ker := hker _ (by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hw, hyz, mul_inv_cancel])
  have hxyz : x * ⁅y, z⁆ = ⁅y, z⁆ * x := by
    calc x * ⁅y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * x := by group
      _ = ⁅y, z⁆ * x := by rw [key]
  calc x * w = x * (w * ⁅y, z⁆⁻¹) * ⁅y, z⁆ := by group
    _ = w * ⁅y, z⁆⁻¹ * (x * ⁅y, z⁆) := by rw [← hcen _ hc₀ x]; group
    _ = w * x := by rw [hxyz]; group

theorem lift_commute_four
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (f : Fin 4) (a y : E)
    (ha : ∃ e : K, ((η a : F4.reeGamma K 1) : ModGL F4.tag K) = fourCoord f 0 e)
    (hy : ∃ c : K, ((η y : F4.reeGamma K 1) : ModGL F4.tag K) = fourCoord f c 0) :
    a * y = y * a := by
  obtain ⟨e, ha⟩ := ha
  obtain ⟨c, hy⟩ := hy
  set n : ModGL F4.tag K := nFour K f * (nFour K 3)⁻¹ with hndef
  have hn : n ∈ F4.reeGamma K 1 := mul_mem (nFour_mem f) (inv_mem (nFour_mem 3))
  have hconj : ∀ c d : K, n⁻¹ * fourCoord f c d * n = fourCoord 3 c d := fun c d => by
    rw [hndef, fourCoord, fourCoord]
    group
  obtain ⟨m, hm⟩ := hη ⟨n, hn⟩
  have hm' : ((η m : F4.reeGamma K 1) : ModGL F4.tag K) = n := by rw [hm]
  have hconjE : ∀ g : E, ((η (m⁻¹ * g * m) : F4.reeGamma K 1) : ModGL F4.tag K) =
      n⁻¹ * ((η g : F4.reeGamma K 1) : ModGL F4.tag K) * n := fun g => by
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hm']
  have h := lift_commute_three hη hC hK (m⁻¹ * y * m) (m⁻¹ * a * m)
    ⟨c, 0, by rw [hconjE, hy, hconj]⟩ ⟨e, by rw [hconjE, ha, hconj]⟩
  have h' : m⁻¹ * (y * a) * m = m⁻¹ * (a * y) * m := by
    calc m⁻¹ * (y * a) * m = m⁻¹ * y * m * (m⁻¹ * a * m) := by group
      _ = m⁻¹ * a * m * (m⁻¹ * y * m) := h
      _ = m⁻¹ * (a * y) * m := by group
  have h'' := congrArg (fun g => m * g * m⁻¹) h'
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at h''
  exact h''.symm

end CFSG.LieType.Ree.LargeReeCover
