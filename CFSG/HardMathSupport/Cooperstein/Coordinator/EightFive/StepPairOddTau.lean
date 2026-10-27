module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolTransfer
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolFaith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolCount
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolShape

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.RankThree.PartTwo Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {V : Type} [CommGroup V] {m : ℕ}

theorem natShape_subtype_comp_of_natVia (hm : 5 ≤ m) {D : Subgroup (MulAut V)}
    (κ : ↥D →* Perm (Fin m)) {W : Subgroup V} (hDW : D ≤ stabSub W)
    (ψW : ↥(autSub D W) →* Perm (Fin m)) (hψW : ∀ d : ↥D, ψW (autSubHom hDW d) = κ d)
    (hnat : NatVia ψW (commV (autSub D W))) (e : alternatingGroup (Fin m) →* ↥D)
    (he : ∀ σ, κ (e σ) = σ) (hVW : ∀ σ v, (e σ : MulAut V) v * v⁻¹ ∈ W) :
    NatShape (D.subtype.comp e) (alternatingGroup (Fin m)).subtype := by
  have hrW : ∀ σ, ψW (((autSubHom hDW).comp e) σ) = (alternatingGroup (Fin m)).subtype σ :=
    fun σ => by rw [MonoidHom.comp_apply, hψW, he]; rfl
  have hshapeW := natShape_of_natVia ((autSubHom hDW).comp e) (alternatingGroup (Fin m)).subtype
    hrW (fun σ => σ.2) hnat
  exact natShape_of_natShape_subgroup
    (commutator_alternatingGroup_eq_top (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega))
    (D.subtype.comp e) _ (fun σ w => rfl) hVW hshapeW

theorem commV_le_fixV_of_natVia [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hm : 8 ≤ m)
    {D : Subgroup (MulAut V)} (κ : ↥D →* Perm (Fin m)) {t : MulAut V} (ht2 : t ^ 2 = 1)
    (htD : ∀ d ∈ D, d * t = t * d) {W : Subgroup V} (hWt : fixV (Subgroup.zpowers t) = W)
    (hDW : D ≤ stabSub W) (ψW : ↥(autSub D W) →* Perm (Fin m))
    (hψW : ∀ d : ↥D, ψW (autSubHom hDW d) = κ d) (hnat : NatVia ψW (commV (autSub D W)))
    (e : alternatingGroup (Fin m) →* ↥D) (he : ∀ σ, κ (e σ) = σ)
    {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) (hAD : A ≤ D)
    (hker : ∀ k : ↥D, κ k = 1 → (k : MulAut V) = 1 ∨ (k : MulAut V) = t)
    (hfix : ∀ i, ∃ a : ↥D, (a : MulAut V) ∈ A ∧ κ a i ≠ i) :
    ∀ σ v, (e σ : MulAut V) v * v⁻¹ ∈ W := by
  classical
  have : Finite (MulAut V) := Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨πW, hπW, hkerW, heqW⟩ := hnat
  set rW : alternatingGroup (Fin m) →* ↥(autSub D W) := (autSubHom hDW).comp e with hrWdef
  have hrW : ∀ σ, ψW (rW σ) = σ := fun σ => by
    rw [hrWdef, MonoidHom.comp_apply, hψW, he]
  set ρW : alternatingGroup (Fin m) →* MulAut ↥W := (autSub D W).subtype.comp rW with hρW
  have hρWapp : ∀ σ (w : ↥W), ((ρW σ w : ↥W) : V) = (e σ : MulAut V) w := fun σ w => rfl
  have hshapeW : NatShape ρW (alternatingGroup (Fin m)).subtype :=
    natShape_of_natVia rW _ (fun σ => by rw [hrW]; rfl) (fun σ => σ.2) ⟨πW, hπW, hkerW, heqW⟩
  set φ := commHom t with hφ
  have hinv : ∀ x : V, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (by rw [← pow_two, hV])
  have hφW : ∀ v, φ v ∈ W := fun v => by
    rw [← hWt, mem_fixV_zpowers_iff, hφ, commHom_apply, map_mul, map_inv]
    have h1 : t (t v) = v := by
      rw [← MulAut.mul_apply, ← pow_two, ht2, MulAut.one_apply]
    rw [h1, hinv, hinv]
    exact mul_comm _ _
  have hkerφ : φ.ker = W := (ker_commHom t).trans hWt
  have hφD : ∀ d ∈ D, ∀ v, φ (d v) = d (φ v) := fun d hd v => by
    have h1 : t (d v) = d (t v) := (congrArg (fun g : MulAut V => g v) (htD d hd)).symm
    rw [hφ, commHom_apply, commHom_apply, map_mul, map_inv, h1]
  by_contra hcon
  push Not at hcon
  obtain ⟨σ₀, v₀, hv₀⟩ := hcon
  have hmove : (e σ₀ : MulAut V) (φ v₀) ≠ φ v₀ := by
    intro h
    apply hv₀
    rw [← hkerφ, MonoidHom.mem_ker, map_mul, map_inv, hφD _ (e σ₀).2, h, mul_inv_cancel]
  set Y : Subgroup ↥W := φ.range.subgroupOf W with hY
  have hrA := (natShape_iff_natShapeA ρW (alternatingGroup (Fin m)).subtype).1 hshapeW
  have hYinv : ∀ g, ∀ y ∈ Subgroup.toAddSubgroup Y,
      (autToEnd.comp ρW) g y ∈ Subgroup.toAddSubgroup Y := by
    intro g y hy
    change ((ρW g (Additive.toMul y) : ↥W) : V) ∈ φ.range
    obtain ⟨v, hv⟩ := (show ((Additive.toMul y : ↥W) : V) ∈ φ.range from hy)
    rw [hρWapp, ← hv, ← hφD _ (e g).2]
    exact ⟨_, rfl⟩
  rcases shape_dichotomy (by omega) hrA _ hYinv with h1 | h2
  · apply hmove
    have := h1 σ₀ (Additive.ofMul ⟨φ v₀, hφW v₀⟩) ⟨v₀, rfl⟩
    exact congrArg (fun x : Additive ↥W => ((Additive.toMul x : ↥W) : V)) this
  have hEWle := range_subtype_comp_le rW
  have hP₁Y : commV ρW.range ≤ Y := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, ⟨σ, rfl⟩, w, rfl⟩
    have := h2 σ (Additive.ofMul w)
    change ρW σ w / w ∈ Y at this
    rwa [div_eq_mul_inv] at this
  have hsurj := surjective_comp_inclusion_commV (by omega) hπW heqW rW hrW
  have hkerP := ker_comp_inclusion_commV hkerW (commV_mono hEWle)
  set πP := πW.comp (Subgroup.inclusion (commV_mono hEWle)) with hπP
  set B : Subgroup (Perm (Fin m)) := (A.subgroupOf D).map κ with hB
  have hAW : A ≤ stabSub W := hAD.trans hDW
  have hAB : ∀ b ∈ B, ∃ a' ∈ autSub A W, ∀ u v : ↥(commV ρW.range), (v : ↥W) = a' u →
      Multiplicative.toAdd (πP v) = altAct b (Multiplicative.toAdd (πP u)) := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨autSubHom hDW a, mem_autSub.2 ⟨⟨a, hDW a.2⟩, ha, rfl⟩, fun u v huv => ?_⟩
    have := heqW (autSubHom hDW a) (Subgroup.inclusion (commV_mono hEWle) u)
      (Subgroup.inclusion (commV_mono hEWle) v) huv
    rwa [hψW] at this
  have n1 := card_mul_card_inf_fixV_le (Y := ⊤) inf_le_left le_top πP hsurj hkerP hAB
  have n2 := card_mul_card_inf_fixV_le (Y := Y) inf_le_left hP₁Y πP hsurj hkerP hAB
  have hfixAW : (fixV (autSub A W)).map W.subtype = W ⊓ fixV A := map_subtype_fixV_autSub hAW
  have hφle : φ.range ≤ W := by
    rintro _ ⟨v, rfl⟩
    exact hφW v
  have c1 : Nat.card ↥(⊤ : Subgroup ↥W) = Nat.card W := Subgroup.card_top
  have c2 : Nat.card ↥((⊤ : Subgroup ↥W) ⊓ fixV (autSub A W)) = Nat.card ↥(W ⊓ fixV A) := by
    rw [top_inf_eq, ← hfixAW, Subgroup.card_map_of_injective W.subtype_injective]
  have c3 : Nat.card Y = Nat.card φ.range :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hφle).toEquiv
  have c4 : Nat.card ↥(Y ⊓ fixV (autSub A W)) = Nat.card ↥(φ.range ⊓ fixV A) := by
    rw [← Subgroup.card_map_of_injective W.subtype_injective,
      Subgroup.map_inf_eq _ _ _ W.subtype_injective, hfixAW, hY,
      Subgroup.map_subgroupOf_eq_of_le hφle, ← inf_assoc, inf_eq_left.2 hφle]
  rw [c1, c2] at n1
  rw [c3, c4] at n2
  have k1 := card_fixV_le_card_ker_mul_card_range φ (A := A) fun a ha v => hφD a (hAD ha) v
  rw [hkerφ] at k1
  have k2 := Subgroup.card_ker_mul_card_range φ
  rw [hkerφ] at k2
  have o1 : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    have := hA.2.2.2 ⊥ bot_le
    rwa [B1.card_bot_mul_card_fixV] at this
  have ab : Nat.card A ≤ 2 * Nat.card B := by
    have e1 := B1More.card_map_mul_card_inf_ker (A.subgroupOf D) κ
    have e2 : Nat.card ↥(A.subgroupOf D) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAD).toEquiv
    have hker2 : Nat.card κ.ker ≤ 2 := by
      have hmem : ∀ k : ↥κ.ker, ((k : ↥D) : MulAut V) ∈ Subgroup.zpowers t := fun k => by
        rcases hker _ (MonoidHom.mem_ker.1 k.2) with h | h
        · rw [h]; exact Subgroup.one_mem _
        · rw [h]; exact Subgroup.mem_zpowers t
      have h1 := Nat.card_le_card_of_injective
        (fun k : ↥κ.ker => (⟨((k : ↥D) : MulAut V), hmem k⟩ : Subgroup.zpowers t))
        fun k₁ k₂ h => Subtype.ext (Subtype.ext
          (congrArg (fun x : Subgroup.zpowers t => (x : MulAut V)) h))
      rw [Nat.card_zpowers] at h1
      exact h1.trans (orderOf_le_of_pow_eq_one (by norm_num) ht2)
    have e3 : Nat.card ↥(A.subgroupOf D ⊓ κ.ker) ≤ 2 :=
      (Subgroup.card_le_of_le inf_le_right).trans hker2
    rw [e2] at e1
    calc Nat.card A = Nat.card B * Nat.card ↥(A.subgroupOf D ⊓ κ.ker) := e1.symm
      _ ≤ Nat.card B * 2 := Nat.mul_le_mul_left _ e3
      _ = 2 * Nat.card B := mul_comm _ _
  have hBsq : ∀ b ∈ B, b * b = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two]
      exact hA.2.2.1.2 _ ha)
    rw [this, map_one]
  have hBfix : ∀ i, ∃ b ∈ B, b i ≠ i := fun i => by
    obtain ⟨a, ha, hai⟩ := hfix i
    exact ⟨κ a, ⟨a, ha, rfl⟩, hai⟩
  have num := two_mul_card_mul_sq_lt hm hBsq hBfix
  have hcA : 0 < Nat.card (fixV A) := Nat.card_pos
  have s1 : Nat.card (altHeart m) ^ 2 * Nat.card (fixV A) ≤
      (Nat.card (altHeart m) * Nat.card ↥(W ⊓ fixV A)) *
        (Nat.card (altHeart m) * Nat.card ↥(φ.range ⊓ fixV A)) := by
    calc Nat.card (altHeart m) ^ 2 * Nat.card (fixV A)
        ≤ Nat.card (altHeart m) ^ 2 *
          (Nat.card ↥(W ⊓ fixV A) * Nat.card ↥(φ.range ⊓ fixV A)) :=
        Nat.mul_le_mul_left _ k1
      _ = _ := by ring
  have s2 := Nat.mul_le_mul n1 n2
  have s3 : Nat.card W * Nat.card (altFix m B) * (Nat.card φ.range * Nat.card (altFix m B)) =
      Nat.card V * Nat.card (altFix m B) ^ 2 := by
    rw [← k2]
    ring
  have s4 : Nat.card V * Nat.card (altFix m B) ^ 2 ≤
      Nat.card A * Nat.card (fixV A) * Nat.card (altFix m B) ^ 2 :=
    Nat.mul_le_mul_right _ o1
  have s5 : Nat.card A * Nat.card (fixV A) * Nat.card (altFix m B) ^ 2 ≤
      2 * Nat.card B * Nat.card (altFix m B) ^ 2 * Nat.card (fixV A) := by
    calc Nat.card A * Nat.card (fixV A) * Nat.card (altFix m B) ^ 2
        ≤ 2 * Nat.card B * Nat.card (fixV A) * Nat.card (altFix m B) ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ab)
      _ = _ := by ring
  have s6 : 2 * Nat.card B * Nat.card (altFix m B) ^ 2 * Nat.card (fixV A) <
      Nat.card (altHeart m) ^ 2 * Nat.card (fixV A) :=
    Nat.mul_lt_mul_of_pos_right num hcA
  exact lt_irrefl _ ((s1.trans (s2.trans (s3.le.trans (s4.trans s5)))).trans_lt s6)

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
