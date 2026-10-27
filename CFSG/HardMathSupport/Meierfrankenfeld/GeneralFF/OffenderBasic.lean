module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs


public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V} {A B : Subgroup G} {U U' : Submodule (ZMod 2) V}

theorem fixOn_top (ρ : Representation (ZMod 2) G V) (A : Subgroup G) :
    fixOn ρ A ⊤ = fixSub ρ A :=
  top_inf_eq _

theorem fixOn_le_left : fixOn ρ A U ≤ U := inf_le_left

theorem cenOn_le (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) : cenOn ρ A U ≤ A := fun _ h => h.1

theorem cenOn_mono_left (h : A ≤ B) : cenOn ρ A U ≤ cenOn ρ B U :=
  fun _ hg => ⟨h hg.1, hg.2⟩

theorem cenOn_anti_right (h : U' ≤ U) : cenOn ρ A U ≤ cenOn ρ A U' :=
  fun _ hg => ⟨hg.1, fun u hu => hg.2 u (h hu)⟩

theorem fixOn_anti_left (h : A ≤ B) : fixOn ρ B U ≤ fixOn ρ A U :=
  inf_le_inf_left _ (fixSub_antitone h)

theorem fixOn_mono_right (h : U' ≤ U) : fixOn ρ A U' ≤ fixOn ρ A U :=
  inf_le_inf_right _ h

theorem fixOn_eq_self (h : ∀ a ∈ A, ∀ u ∈ U, ρ a u = u) : fixOn ρ A U = U :=
  inf_eq_left.mpr fun u hu a ha => h a ha u hu

theorem fixOn_cenOn (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) : fixOn ρ (cenOn ρ A U) U = U :=
  fixOn_eq_self fun _ ha => ha.2

theorem cenOn_eq_inf_of_le (h : B ≤ A) :
    cenOn ρ B U = B ⊓ cenOn ρ A U := by
  ext g
  exact ⟨fun hg => ⟨hg.1, h hg.1, hg.2⟩, fun hg => ⟨hg.1, hg.2.2⟩⟩

theorem IsElemAbelianOn.mono_left (h : IsElemAbelianOn ρ A U) (hB : B ≤ A) :
    IsElemAbelianOn ρ B U :=
  fun a ha b hb => h a (hB ha) b (hB hb)

theorem IsElemAbelianOn.mono_right (h : IsElemAbelianOn ρ A U) (hU : U' ≤ U) :
    IsElemAbelianOn ρ A U' :=
  fun a ha b hb =>
    ⟨fun u hu => (h a ha b hb).1 u (hU hu), fun u hu => (h a ha b hb).2 u (hU hu)⟩

theorem card_le_of_le_submodule [Finite V] (h : U' ≤ U) : Nat.card U' ≤ Nat.card U :=
  Nat.card_le_card_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

theorem IsElemAbelianOn.comm_top (h : IsElemAbelianOn ρ A ⊤) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) (v : V) : ρ a (ρ b v) = ρ b (ρ a v) := by
  have h1 := (h a ha b hb).1 (ρ (b * a) v) Submodule.mem_top
  have e : ρ (a * b * a⁻¹ * b⁻¹) (ρ (b * a) v) = ρ (a * b) v := by
    rw [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  rw [e] at h1
  have e1 : ρ (a * b) v = ρ a (ρ b v) := by rw [map_mul]; rfl
  have e2 : ρ (b * a) v = ρ b (ρ a v) := by rw [map_mul]; rfl
  rw [e1, e2] at h1
  exact h1

theorem IsElemAbelianOn.isInvariant_fixSub (h : IsElemAbelianOn ρ A ⊤) (hB : B ≤ A) :
    IsInvariant ρ A (fixSub ρ B) := by
  intro a ha u hu b hb
  rw [h.comm_top (hB hb) ha, hu b hb]

theorem IsBestOffenderOn.isOffenderOn (h : IsBestOffenderOn ρ A U) : IsOffenderOn ρ A U := by
  refine ⟨h.1, ?_⟩
  have := h.2 (cenOn ρ A U) (cenOn_le _ _ _)
  rwa [fixOn_cenOn, mul_comm] at this

theorem weight_le_restrict [Finite V]
    (h : ∀ B : Subgroup G, B ≤ A → Nat.card B * Nat.card (fixOn ρ B U) ≤
      Nat.card A * Nat.card (fixOn ρ A U)) (hU' : U' ≤ U) :
    ∀ B : Subgroup G, B ≤ A → Nat.card B * Nat.card (fixOn ρ B U') ≤
      Nat.card A * Nat.card (fixOn ρ A U') := by
  intro B hB
  have h1 := h B hB
  have hsup : fixOn ρ B U' ⊔ fixOn ρ A U ≤ fixOn ρ B U :=
    sup_le (fixOn_mono_right hU') (fixOn_anti_left hB)
  have hinf : fixOn ρ B U' ⊓ fixOn ρ A U = fixOn ρ A U' := by
    ext v
    simp only [Submodule.mem_inf, mem_fixOn]
    exact ⟨fun hv => ⟨hv.1.1, hv.2.2⟩,
      fun hv => ⟨⟨hv.1, fun b hb => hv.2 b (hB hb)⟩, hU' hv.1, hv.2⟩⟩
  have hmod := card_inf_mul_card_sup (fixOn ρ B U') (fixOn ρ A U)
  rw [hinf] at hmod
  have hle : Nat.card ↥(fixOn ρ B U' ⊔ fixOn ρ A U) ≤ Nat.card (fixOn ρ B U) :=
    card_le_of_le_submodule hsup
  have key : Nat.card (fixOn ρ B U') * Nat.card (fixOn ρ A U) ≤
      Nat.card (fixOn ρ A U') * Nat.card (fixOn ρ B U) := by
    rw [← hmod]; exact Nat.mul_le_mul_left _ hle
  have hpos : 0 < Nat.card (fixOn ρ A U) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card B * Nat.card (fixOn ρ B U') * Nat.card (fixOn ρ A U)
      = Nat.card B * (Nat.card (fixOn ρ B U') * Nat.card (fixOn ρ A U)) := by ring
    _ ≤ Nat.card B * (Nat.card (fixOn ρ A U') * Nat.card (fixOn ρ B U)) :=
        Nat.mul_le_mul_left _ key
    _ = Nat.card (fixOn ρ A U') * (Nat.card B * Nat.card (fixOn ρ B U)) := by ring
    _ ≤ Nat.card (fixOn ρ A U') * (Nat.card A * Nat.card (fixOn ρ A U)) :=
        Nat.mul_le_mul_left _ h1
    _ = Nat.card A * Nat.card (fixOn ρ A U') * Nat.card (fixOn ρ A U) := by ring

theorem IsBestOffenderOn.restrict [Finite V] (h : IsBestOffenderOn ρ A U) (hU' : U' ≤ U) :
    IsBestOffenderOn ρ A U' :=
  ⟨h.1.mono_right hU', weight_le_restrict h.2 hU'⟩

theorem IsBestOffenderOn.isOffenderOn_of_le [Finite V] (h : IsBestOffenderOn ρ A ⊤)
    (U : Submodule (ZMod 2) V) : IsOffenderOn ρ A U :=
  (h.restrict le_top).isOffenderOn

theorem IsBestOffenderOn.forall_isInvariant_isOffenderOn [Finite V]
    (h : IsBestOffenderOn ρ A ⊤) :
    ∀ U : Submodule (ZMod 2) V, IsInvariant ρ A U → IsOffenderOn ρ A U :=
  fun U _ => h.isOffenderOn_of_le U

theorem isBestOffenderOn_top_of_forall [Finite G] (hA : IsElemAbelianOn ρ A ⊤)
    (h : ∀ U : Submodule (ZMod 2) V, IsInvariant ρ A U → IsOffenderOn ρ A U) :
    IsBestOffenderOn ρ A ⊤ := by
  refine ⟨hA, fun B hB => ?_⟩
  have hoff := (h (fixSub ρ B) (hA.isInvariant_fixSub hB)).2
  have hBc : B ≤ cenOn ρ A (fixSub ρ B) := fun b hb => ⟨hB hb, fun u hu => hu b hb⟩
  have hfix : fixOn ρ A (fixSub ρ B) = fixSub ρ A :=
    inf_eq_right.mpr (fixSub_antitone hB)
  rw [hfix] at hoff
  rw [fixOn_top, fixOn_top]
  calc Nat.card B * Nat.card (fixSub ρ B)
      ≤ Nat.card (cenOn ρ A (fixSub ρ B)) * Nat.card (fixSub ρ B) :=
        Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hBc)
    _ = Nat.card (fixSub ρ B) * Nat.card (cenOn ρ A (fixSub ρ B)) := mul_comm _ _
    _ ≤ Nat.card A * Nat.card (fixSub ρ A) := hoff

theorem isElemAbelianOn_top_iff (hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1) :
    CFSG.IsElementaryAbelian 2 A ↔ IsElemAbelianOn ρ A ⊤ := by
  constructor
  · intro hE a ha b hb
    have hcomm : a * b = b * a := by
      have := hE.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩
      exact congrArg Subtype.val this
    have hsq : a * a = 1 := by
      have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
      simpa [pow_two] using this
    refine ⟨fun u _ => ?_, fun u _ => ?_⟩
    · have : a * b * a⁻¹ * b⁻¹ = 1 := by
        rw [hcomm]; group
      rw [this]; simp
    · rw [hsq]; simp
  · intro h
    have hsq : ∀ a ∈ A, a * a = 1 := fun a ha =>
      hfaith _ (A.mul_mem ha ha) fun v => (h a ha a ha).2 v Submodule.mem_top
    have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
      intro a ha b hb
      have h1 : a * b * a⁻¹ * b⁻¹ = 1 :=
        hfaith _ (A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb))
          fun v => (h a ha b hb).1 v Submodule.mem_top
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    have : IsMulCommutative A :=
      ⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩
    refine ⟨?_⟩
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    exact Subtype.ext (by simpa [pow_two] using hsq x x.2)

theorem isBestOffender_iff_on (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1) :
    (CFSG.IsElementaryAbelian 2 A ∧ CFSG.RankThree.FFModules.IsBestOffender ρ A) ↔
      IsBestOffenderOn ρ A ⊤ := by
  rw [isElemAbelianOn_top_iff hfaith]
  unfold IsBestOffenderOn
  simp only [fixOn_top]
  rfl

section Product

open scoped Pointwise

theorem card_mul_card_le_sup_inf [Finite G] (B C : Subgroup G) :
    Nat.card B * Nat.card C ≤ Nat.card ↥(B ⊔ C) * Nat.card ↥(B ⊓ C) := by
  set D : Subgroup B := C.subgroupOf B with hD
  have h1 : Nat.card B = Nat.card (B ⧸ D) * Nat.card D :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup D
  have h2 : Nat.card D = Nat.card ↥(B ⊓ C) :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.1.2, x.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have h4 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient C (B : Set G)
  have h3 : Nat.card (B ⧸ D) ≤ Nat.card ((B : Set G).image ((↑) : G → G ⧸ C)) := by
    let f : B ⧸ D → ↥((B : Set G).image ((↑) : G → G ⧸ C)) :=
      Quotient.lift (s := QuotientGroup.leftRel D)
        (fun b : B => ⟨((b : G) : G ⧸ C), (b : G), b.2, rfl⟩) (by
          intro a b hab
          apply Subtype.ext
          change ((a : G) : G ⧸ C) = ((b : G) : G ⧸ C)
          rw [QuotientGroup.eq]
          exact (QuotientGroup.leftRel_apply (s := D)).mp hab)
    refine Nat.card_le_card_of_injective f ?_
    intro x y
    refine Quotient.inductionOn₂ x y fun a b hab => ?_
    have hab' : ((a : G) : G ⧸ C) = ((b : G) : G ⧸ C) := congrArg Subtype.val hab
    rw [QuotientGroup.eq] at hab'
    exact Quotient.sound ((QuotientGroup.leftRel_apply (s := D)).mpr hab')
  have h5 : Nat.card ((B : Set G) * (C : Set G) : Set G) ≤ Nat.card ↥(B ⊔ C) := by
    have hsub : ((B : Set G) * (C : Set G) : Set G) ⊆ ((B ⊔ C : Subgroup G) : Set G) := by
      rintro _ ⟨b, hb, c, hc, rfl⟩
      exact mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hc)
    exact Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  rw [h1, h2]
  calc Nat.card (B ⧸ D) * Nat.card ↥(B ⊓ C) * Nat.card C
      ≤ Nat.card ((B : Set G).image ((↑) : G → G ⧸ C)) * Nat.card ↥(B ⊓ C) * Nat.card C := by
        gcongr
    _ = Nat.card ((B : Set G) * (C : Set G) : Set G) * Nat.card ↥(B ⊓ C) := by
        rw [h4]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ h5

end Product

@[expose] noncomputable def jInv (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) : ℚ :=
  (Nat.card A * Nat.card (fixOn ρ A U) : ℚ) / (Nat.card U * Nat.card (cenOn ρ A U))

section J

variable [Finite G] [Finite V]

theorem jInv_denom_pos (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) : (0 : ℚ) < Nat.card U * Nat.card (cenOn ρ A U) := by
  have h1 : 0 < Nat.card U := Nat.card_pos
  have h2 : 0 < Nat.card (cenOn ρ A U) := Nat.card_pos
  positivity

theorem jInv_eq_div (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) :
    jInv ρ A U = ((Nat.card A : ℚ) / Nat.card (cenOn ρ A U)) /
      ((Nat.card U : ℚ) / Nat.card (fixOn ρ A U)) := by
  have h1 : (Nat.card U : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h2 : (Nat.card (cenOn ρ A U) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h3 : (Nat.card (fixOn ρ A U) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold jInv
  field_simp

theorem isOffenderOn_iff_one_le_jInv :
    IsOffenderOn ρ A U ↔ IsElemAbelianOn ρ A U ∧ 1 ≤ jInv ρ A U := by
  unfold IsOffenderOn
  refine and_congr_right fun _ => ?_
  unfold jInv
  rw [one_le_div (jInv_denom_pos ρ A U)]
  constructor <;> intro h <;> exact_mod_cast h

theorem jInv_eq_one_of_commOn_eq_bot (h : commOn ρ A U = ⊥) : jInv ρ A U = 1 := by
  have hfix : ∀ a ∈ A, ∀ u ∈ U, ρ a u = u := by
    intro a ha u hu
    have : ρ a u - u ∈ commOn ρ A U := Submodule.subset_span ⟨a, ha, u, hu, rfl⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have hc : cenOn ρ A U = A := le_antisymm (cenOn_le _ _ _) fun a ha => ⟨ha, hfix a ha⟩
  have hf : fixOn ρ A U = U := fixOn_eq_self hfix
  have h1 : (Nat.card U : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h2 : (Nat.card A : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold jInv
  rw [hc, hf]
  field_simp

theorem jInv_le_jInv_iff_of_cenOn_eq (hc : cenOn ρ B ⊤ = cenOn ρ A ⊤) :
    jInv ρ B ⊤ ≤ jInv ρ A ⊤ ↔
      Nat.card B * Nat.card (fixSub ρ B) ≤ Nat.card A * Nat.card (fixSub ρ A) := by
  unfold jInv
  rw [hc, fixOn_top, fixOn_top, div_le_div_iff_of_pos_right (jInv_denom_pos ρ A ⊤)]
  constructor <;> intro h <;> exact_mod_cast h

omit [Finite G] [Finite V] in
theorem cenOn_sup_cenOn_top (hB : B ≤ A) : cenOn ρ (B ⊔ cenOn ρ A ⊤) ⊤ = cenOn ρ A ⊤ := by
  refine le_antisymm (fun g hg => ⟨sup_le hB (cenOn_le _ _ _) hg.1, hg.2⟩) fun g hg => ?_
  exact ⟨Subgroup.mem_sup_right hg, hg.2⟩

omit [Finite G] [Finite V] in
theorem fixSub_sup_cenOn_top : fixSub ρ (B ⊔ cenOn ρ A ⊤) = fixSub ρ B := by
  rw [fixSub_sup]
  exact inf_eq_left.mpr fun v hv a ha => ha.2 v Submodule.mem_top

theorem jInv_le_jInv_sup_cenOn_top (hB : B ≤ A) :
    jInv ρ B ⊤ ≤ jInv ρ (B ⊔ cenOn ρ A ⊤) ⊤ := by
  have key := card_mul_card_le_sup_inf B (cenOn ρ A ⊤)
  have keyQ : (Nat.card B : ℚ) * Nat.card (cenOn ρ A ⊤) ≤
      Nat.card ↥(B ⊔ cenOn ρ A ⊤) * Nat.card ↥(B ⊓ cenOn ρ A ⊤) := by exact_mod_cast key
  have hT : 0 < Nat.card (⊤ : Submodule (ZMod 2) V) := Nat.card_pos
  have hc1 : 0 < Nat.card ↥(B ⊓ cenOn ρ A ⊤) := Nat.card_pos
  have hc2 : 0 < Nat.card (cenOn ρ A ⊤) := Nat.card_pos
  have hpos : (0 : ℚ) < Nat.card (⊤ : Submodule (ZMod 2) V) * Nat.card ↥(B ⊓ cenOn ρ A ⊤) := by
    positivity
  have hpos' : (0 : ℚ) < Nat.card (⊤ : Submodule (ZMod 2) V) * Nat.card (cenOn ρ A ⊤) := by
    positivity
  rw [jInv, jInv, fixOn_top, fixOn_top, cenOn_sup_cenOn_top hB, cenOn_eq_inf_of_le hB,
    fixSub_sup_cenOn_top, div_le_div_iff₀ hpos hpos']
  have hnn : (0 : ℚ) ≤ Nat.card (fixSub ρ B) * Nat.card (⊤ : Submodule (ZMod 2) V) := by positivity
  calc (Nat.card B : ℚ) * Nat.card (fixSub ρ B) *
        (Nat.card (⊤ : Submodule (ZMod 2) V) * Nat.card (cenOn ρ A ⊤))
      = ((Nat.card B : ℚ) * Nat.card (cenOn ρ A ⊤)) *
          (Nat.card (fixSub ρ B) * Nat.card (⊤ : Submodule (ZMod 2) V)) := by ring
    _ ≤ ((Nat.card ↥(B ⊔ cenOn ρ A ⊤) : ℚ) * Nat.card ↥(B ⊓ cenOn ρ A ⊤)) *
          (Nat.card (fixSub ρ B) * Nat.card (⊤ : Submodule (ZMod 2) V)) :=
        mul_le_mul_of_nonneg_right keyQ hnn
    _ = _ := by ring

theorem isBestOffenderOn_top_iff_jInv_le (hA : IsElemAbelianOn ρ A ⊤) :
    IsBestOffenderOn ρ A ⊤ ↔ ∀ B ≤ A, jInv ρ B ⊤ ≤ jInv ρ A ⊤ := by
  constructor
  · intro h B hB
    have hB' : B ⊔ cenOn ρ A ⊤ ≤ A := sup_le hB (cenOn_le _ _ _)
    refine (jInv_le_jInv_sup_cenOn_top hB).trans ?_
    rw [jInv_le_jInv_iff_of_cenOn_eq (cenOn_sup_cenOn_top hB)]
    have := h.2 _ hB'
    rwa [fixOn_top, fixOn_top] at this
  · intro h
    refine ⟨hA, fun B hB => ?_⟩
    have hB' : B ⊔ cenOn ρ A ⊤ ≤ A := sup_le hB (cenOn_le _ _ _)
    have h1 := h _ hB'
    rw [jInv_le_jInv_iff_of_cenOn_eq (cenOn_sup_cenOn_top hB), fixSub_sup_cenOn_top] at h1
    rw [fixOn_top, fixOn_top]
    exact le_trans (Nat.mul_le_mul_right _ (Subgroup.card_le_of_le le_sup_left)) h1

theorem exists_bestOffender_le {B : Subgroup G} (hB : IsOffenderOn ρ B ⊤) :
    ∃ B' ≤ B, IsBestOffenderOn ρ B' ⊤ ∧ jInv ρ B ⊤ ≤ jInv ρ B' ⊤ ∧
      (commOn ρ B' ⊤ ≠ ⊥ ∨ B' = B) := by
  classical
  let T : Finset (Subgroup G) := (Set.finite_univ (α := Subgroup G)).toFinset.filter (· ≤ B)
  have hT : T.Nonempty := ⟨B, by simp [T]⟩
  obtain ⟨B₁, hB₁T, hB₁max⟩ := T.exists_max_image (fun X => jInv ρ X ⊤) hT
  let T' : Finset (Subgroup G) := T.filter (fun X => jInv ρ X ⊤ = jInv ρ B₁ ⊤)
  have hT' : T'.Nonempty := ⟨B₁, by simp [T', hB₁T]⟩
  obtain ⟨B₂, hB₂T', hB₂max⟩ := T'.exists_max_image (fun X => Nat.card X) hT'
  have hB₂T : B₂ ∈ T := (Finset.mem_filter.mp hB₂T').1
  have hB₂j : jInv ρ B₂ ⊤ = jInv ρ B₁ ⊤ := (Finset.mem_filter.mp hB₂T').2
  have hB₂le : B₂ ≤ B := by simpa [T] using hB₂T
  have hmax : ∀ X ≤ B, jInv ρ X ⊤ ≤ jInv ρ B₂ ⊤ := fun X hX => by
    rw [hB₂j]; exact hB₁max X (by simpa [T] using hX)
  have hcard : ∀ X ≤ B, jInv ρ X ⊤ = jInv ρ B₂ ⊤ → Nat.card X ≤ Nat.card B₂ := fun X hX hj =>
    hB₂max X (Finset.mem_filter.mpr ⟨by simpa [T] using hX, by rw [hj, hB₂j]⟩)
  refine ⟨B₂, hB₂le, ?_, hmax B le_rfl, ?_⟩
  · exact (isBestOffenderOn_top_iff_jInv_le (hB.1.mono_left hB₂le)).mpr fun X hX =>
      hmax X (hX.trans hB₂le)
  · by_cases hc : commOn ρ B₂ ⊤ = ⊥
    · right
      have h1 : jInv ρ B₂ ⊤ = 1 := jInv_eq_one_of_commOn_eq_bot hc
      have h2 : 1 ≤ jInv ρ B ⊤ := (isOffenderOn_iff_one_le_jInv.mp hB).2
      have h3 : jInv ρ B ⊤ = jInv ρ B₂ ⊤ := le_antisymm (hmax B le_rfl) (h1 ▸ h2)
      exact Subgroup.eq_of_le_of_card_ge hB₂le (hcard B le_rfl h3)
    · exact Or.inl hc

end J

section Join

variable [Finite G] [Finite V]

theorem card_sup_inf_ge (A B : Subgroup G) :
    Nat.card A * Nat.card (fixSub ρ A) * (Nat.card B * Nat.card (fixSub ρ B)) ≤
      Nat.card ↥(A ⊔ B) * Nat.card (fixSub ρ (A ⊔ B)) *
        (Nat.card ↥(A ⊓ B) * Nat.card (fixSub ρ (A ⊓ B))) := by
  have h1 := card_mul_card_le_sup_inf A B
  have hsub : fixSub ρ A ⊔ fixSub ρ B ≤ fixSub ρ (A ⊓ B) :=
    sup_le (fixSub_antitone inf_le_left) (fixSub_antitone inf_le_right)
  have hle : Nat.card ↥(fixSub ρ A ⊔ fixSub ρ B) ≤ Nat.card (fixSub ρ (A ⊓ B)) :=
    card_le_of_le_submodule hsub
  have hCC := card_inf_mul_card_sup (fixSub ρ A) (fixSub ρ B)
  rw [← fixSub_sup] at hCC
  have h2 : Nat.card (fixSub ρ A) * Nat.card (fixSub ρ B) ≤
      Nat.card (fixSub ρ (A ⊔ B)) * Nat.card (fixSub ρ (A ⊓ B)) := by
    rw [← hCC]; exact Nat.mul_le_mul_left _ hle
  calc Nat.card A * Nat.card (fixSub ρ A) * (Nat.card B * Nat.card (fixSub ρ B))
      = (Nat.card A * Nat.card B) * (Nat.card (fixSub ρ A) * Nat.card (fixSub ρ B)) := by ring
    _ ≤ (Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)) *
          (Nat.card (fixSub ρ (A ⊔ B)) * Nat.card (fixSub ρ (A ⊓ B))) :=
        Nat.mul_le_mul h1 h2
    _ = _ := by ring

theorem jInv_mul_jInv_le (A B : Subgroup G) (hfaith : cenOn ρ (A ⊔ B) ⊤ = ⊥) :
    jInv ρ A ⊤ * jInv ρ B ⊤ ≤ jInv ρ (A ⊔ B) ⊤ * jInv ρ (A ⊓ B) ⊤ := by
  have hc : ∀ X : Subgroup G, X ≤ A ⊔ B → cenOn ρ X ⊤ = ⊥ := fun X hX =>
    eq_bot_iff.mpr (hfaith ▸ cenOn_mono_left hX)
  have hA := hc A le_sup_left
  have hB := hc B le_sup_right
  have hAB := hc (A ⊓ B) (inf_le_left.trans le_sup_left)
  unfold jInv
  rw [hA, hB, hfaith, hAB, fixOn_top, fixOn_top, fixOn_top, fixOn_top, Subgroup.card_bot,
    div_mul_div_comm, div_mul_div_comm]
  have hT : (0 : ℚ) < Nat.card (⊤ : Submodule (ZMod 2) V) := by
    exact_mod_cast Nat.card_pos
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast card_sup_inf_ge (ρ := ρ) A B

end Join

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
