module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylDefs
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8CaseThree
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child8

open Subgroup Weyl

section Iso

variable {X Y : Type*} [Group X] [Group Y]

theorem commutator_eq_top_of_mulEquiv (e : X ≃* Y) (h : commutator Y = ⊤) :
    commutator X = ⊤ := by
  have h1 := Subgroup.map_commutator (⊤ : Subgroup Y) ⊤ e.symm.toMonoidHom
  rw [map_top_of_surjective _ e.symm.surjective] at h1
  rw [commutator_def, ← h1, ← commutator_def, h, map_top_of_surjective _ e.symm.surjective]

theorem map_center_mulEquiv (e : X ≃* Y) : (center X).map e.toMonoidHom = center Y := by
  ext y
  rw [mem_map_equiv, mem_center_iff, mem_center_iff]
  constructor
  · intro hy g
    apply e.symm.injective
    rw [map_mul, map_mul, hy]
  · intro hy g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

end Iso

theorem inf_subgroupOf_eq {G : Type*} [Group G] (H K L : Subgroup G) :
    H.subgroupOf L ⊓ K.subgroupOf L = (H ⊓ K).subgroupOf L := by
  ext x
  simp only [mem_inf, mem_subgroupOf]

theorem card_subgroupOf_of_le {G : Type*} [Group G] {H L : Subgroup G} (hHL : H ≤ L) :
    Nat.card (H.subgroupOf L) = Nat.card H :=
  Nat.card_congr (subgroupOfEquivOfLe hHL).toEquiv

theorem sum_vec2 : ∀ i j : Fin 8, i ≠ j → ∑ k, vec2 i j k = 0 := by decide

theorem vec2_mem_evenSub {i j : Fin 8} (hij : i ≠ j) : vec2 i j ∈ evenSub :=
  mem_evenSub.2 (sum_vec2 i j hij)

@[expose] def kleinFour {G : Type*} [Group G] (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : Subgroup G where
  carrier := {1, a, b, a * b}
  mul_mem' {x y} hx hy := by
    have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have e2 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
    have e3 : a * b * a = b := by rw [hab, mul_assoc, ha, mul_one]
    have e4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have e5 : a * b * (a * b) = 1 := by rw [← mul_assoc, e3, hb]
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, one_mul, mul_one, ha, hb, e1, e2, e3,
        e4, e5, ← hab, true_or, or_true]
  one_mem' := Set.mem_insert _ _
  inv_mem' {x} hx := by
    have e5 : a * b * (a * b) = 1 := by
      rw [← mul_assoc, hab, mul_assoc b a a, ha, mul_one, hb]
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, inv_one, inv_eq_of_mul_eq_one_right ha,
        inv_eq_of_mul_eq_one_right hb, inv_eq_of_mul_eq_one_right e5, true_or, or_true]

theorem card_kleinFour {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (kleinFour a b ha hb hab) = 4 := by
  have hab1 : a * b ≠ 1 := fun h => hne (by
    rw [mul_eq_one_iff_eq_inv.1 h, inv_eq_of_mul_eq_one_right hb])
  have haab : a ≠ a * b := fun h => hb1 (mul_eq_left.mp h.symm)
  have hbab : b ≠ a * b := fun h => ha1 (mul_eq_right.mp h.symm)
  change Nat.card (({1, a, b, a * b} : Set G)) = 4
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_pair hbab]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, haab⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha1.symm, hb1.symm, hab1.symm⟩

theorem mul_self_of_kleinFour {G : Type*} [Group G] {a b : G} {ha : a * a = 1} {hb : b * b = 1}
    {hab : a * b = b * a} {x : G} (hx : x ∈ kleinFour a b ha hb hab) : x * x = 1 := by
  rcases hx with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact ha
  · exact hb
  · rw [← mul_assoc, hab, mul_assoc b a a, ha, mul_one, hb]

theorem mem_cosets_of_mem_sup {G : Type*} [Group G] {E : Subgroup G} {a b : G}
    (hna : ∀ k ∈ E, a * k * a⁻¹ ∈ E) (hnb : ∀ k ∈ E, b * k * b⁻¹ ∈ E) (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) {g : G} (hg : g ∈ E ⊔ closure {a, b}) :
    g ∈ E ∨ a⁻¹ * g ∈ E ∨ b⁻¹ * g ∈ E ∨ (a * b)⁻¹ * g ∈ E := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hab2 : a * b * (a * b) = 1 := by rw [← mul_assoc, hab, mul_assoc b a a, ha, mul_one, hb]
  have hab' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab2
  have hnab : ∀ k ∈ E, a * b * k * (a * b)⁻¹ ∈ E := fun k hk => by
    have e : a * b * k * (a * b)⁻¹ = a * (b * k * b⁻¹) * a⁻¹ := by group
    rw [e]
    exact hna _ (hnb k hk)
  set Q₁ := extTwo E a hna (ha ▸ E.one_mem) with hQ₁
  have hnQ : ∀ k ∈ Q₁, b * k * b⁻¹ ∈ Q₁ := by
    rintro k (hk | hk)
    · exact Or.inl (hnb k hk)
    · refine Or.inr ?_
      have e : b * k * b⁻¹ * a⁻¹ = b * (k * a⁻¹) * b⁻¹ := by
        rw [ha', hb']
        calc b * k * b * a = b * k * (b * a) := by group
          _ = b * k * (a * b) := by rw [hab]
          _ = b * (k * a) * b := by group
      rw [e]
      exact hnb _ hk
  set Q := extTwo Q₁ b hnQ (hb ▸ Q₁.one_mem) with hQ
  have hle : E ⊔ closure {a, b} ≤ Q := by
    refine sup_le (le_extTwo.trans le_extTwo) ((closure_le _).2 ?_)
    rintro x (rfl | rfl)
    · exact le_extTwo mem_extTwo_self
    · exact mem_extTwo_self
  have hleft : ∀ c, (∀ k ∈ E, c⁻¹ * k * c⁻¹⁻¹ ∈ E) → g * c⁻¹ ∈ E → c⁻¹ * g ∈ E := by
    intro c hc h1
    have e : c⁻¹ * g = c⁻¹ * (g * c⁻¹) * c⁻¹⁻¹ := by group
    rw [e]
    exact hc _ h1
  have hinv : ∀ c, c⁻¹ = c → (∀ k ∈ E, c * k * c⁻¹ ∈ E) → ∀ k ∈ E, c⁻¹ * k * c⁻¹⁻¹ ∈ E := by
    intro c hc hn k hk
    rw [hc]
    exact hn k hk
  rcases hle hg with (h1 | h1) | (h1 | h1)
  · exact Or.inl h1
  · exact Or.inr (Or.inl (hleft a (hinv a ha' hna) h1))
  · exact Or.inr (Or.inr (Or.inl (hleft b (hinv b hb' hnb) h1)))
  · refine Or.inr (Or.inr (Or.inr (hleft (a * b) (hinv _ hab' hnab) ?_)))
    have e : g * (a * b)⁻¹ = g * b⁻¹ * a⁻¹ := by group
    rw [e]
    exact h1

namespace Bridge

variable (h : WeylPackage)
include h

theorem signPerm_mem_eSub {v : FrameVec} (hv : v ∈ evenSub) : signPerm v ∈ eSub :=
  (h.coords.mem_eSub _).2 ⟨v, hv, rfl⟩

theorem eSub_le_wE8 : eSub ≤ wE8 := h.coords.eSub_le.trans inf_le_left

omit h in
theorem wPlus_le_wE8 : wPlus ≤ wE8 := inf_le_left

theorem signPerm_mem_wE8 {v : FrameVec} (hv : v ∈ evenSub) : signPerm v ∈ wE8 :=
  eSub_le_wE8 h (signPerm_mem_eSub h hv)

theorem frameElt_mem_e1Sub (v : FrameVec) : frameElt v ∈ e1Sub :=
  (h.coords.mem_e1Sub _).2 ⟨v, rfl⟩

theorem frameElt_mem_wE8 (v : FrameVec) : frameElt v ∈ wE8 :=
  h.coords.e1Sub_le (frameElt_mem_e1Sub h v)

theorem signPerm_zero : signPerm 0 = 1 := by
  have h1 := h.coords.signPerm_add 0 (zero_mem _) 0 (zero_mem _)
  rw [add_zero] at h1
  exact (mul_eq_left.mp h1.symm)

theorem frameElt_zero : frameElt 0 = 1 := by
  have h1 := h.coords.frameElt_add 0 0
  rw [add_zero] at h1
  exact (mul_eq_left.mp h1.symm)

@[expose] noncomputable def ιE : Multiplicative evenSub →* wE8 where
  toFun v := ⟨signPerm ((Multiplicative.toAdd v : evenSub) : FrameVec),
    signPerm_mem_wE8 h (Multiplicative.toAdd v).2⟩
  map_one' := Subtype.ext (signPerm_zero h)
  map_mul' a b := Subtype.ext (by
    change signPerm ((Multiplicative.toAdd (a * b) : evenSub) : FrameVec) =
      signPerm ((Multiplicative.toAdd a : evenSub) : FrameVec) *
        signPerm ((Multiplicative.toAdd b : evenSub) : FrameVec)
    rw [show ((Multiplicative.toAdd (a * b) : evenSub) : FrameVec) =
      ((Multiplicative.toAdd a : evenSub) : FrameVec) +
        ((Multiplicative.toAdd b : evenSub) : FrameVec) from rfl]
    exact h.coords.signPerm_add _ (Multiplicative.toAdd a).2 _ (Multiplicative.toAdd b).2)

@[expose] noncomputable def ιE1 : Multiplicative FrameVec →* wE8 where
  toFun v := ⟨frameElt (Multiplicative.toAdd v), frameElt_mem_wE8 h _⟩
  map_one' := Subtype.ext (frameElt_zero h)
  map_mul' a b := Subtype.ext (by
    change frameElt (Multiplicative.toAdd (a * b)) =
      frameElt (Multiplicative.toAdd a) * frameElt (Multiplicative.toAdd b)
    rw [show Multiplicative.toAdd (a * b) = Multiplicative.toAdd a + Multiplicative.toAdd b
      from rfl]
    exact h.coords.frameElt_add _ _)

theorem coe_ιE (v : Multiplicative evenSub) :
    (ιE h v : Equiv.Perm (Fin 240)) = signPerm ((Multiplicative.toAdd v : evenSub) : FrameVec) :=
  rfl

theorem coe_ιE1 (v : Multiplicative FrameVec) :
    (ιE1 h v : Equiv.Perm (Fin 240)) = frameElt (Multiplicative.toAdd v) := rfl

theorem mem_range_ιE {w : wE8} : w ∈ (ιE h).range ↔ (w : Equiv.Perm (Fin 240)) ∈ eSub := by
  rw [h.coords.mem_eSub]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, (Multiplicative.toAdd v).2, rfl⟩
  · rintro ⟨v, hv, hw⟩
    exact ⟨Multiplicative.ofAdd ⟨v, hv⟩, Subtype.ext hw⟩

theorem mem_range_ιE1 {w : wE8} : w ∈ (ιE1 h).range ↔ (w : Equiv.Perm (Fin 240)) ∈ e1Sub := by
  rw [h.coords.mem_e1Sub]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨v, hw⟩
    exact ⟨Multiplicative.ofAdd v, Subtype.ext hw⟩

theorem zPerm_mem_wE8 : zPerm ∈ wE8 := wPlus_le_wE8 (h.model.zPerm_mem)

theorem xPlane_mem_eSub : xPlane ∈ eSub := h.uArg.uSub_le_eSub h.uArg.xPlane_mem

theorem xPlane_mem_wE8 : xPlane ∈ wE8 := eSub_le_wE8 h (xPlane_mem_eSub h)

@[expose] noncomputable def wPlusEquiv : wPlus.subgroupOf wE8 ≃* wPlus :=
  subgroupOfEquivOfLe wPlus_le_wE8

omit h in
theorem coe_wPlusEquiv (x : wPlus.subgroupOf wE8) :
    ((wPlusEquiv x : wPlus) : Equiv.Perm (Fin 240)) = ((x : wE8) : Equiv.Perm (Fin 240)) := rfl

omit h in
theorem normal_wPlus : (wPlus.subgroupOf wE8).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  have hn' := Subgroup.mem_inf.1 hn
  rw [coe_mul, coe_mul, coe_inv]
  exact Subgroup.mem_inf.2 ⟨wE8.mul_mem (wE8.mul_mem g.2 hn'.1) (wE8.inv_mem g.2),
    (alternatingGroup.normal (α := Fin 240)).conj_mem _ hn'.2 g⟩

theorem perfect_wPlus : commutator (wPlus.subgroupOf wE8) = ⊤ :=
  commutator_eq_top_of_mulEquiv wPlusEquiv h.model.perfect

theorem card_center_wPlus : Nat.card (center (wPlus.subgroupOf wE8)) = 2 := by
  rw [← h.model.card_center, ← map_center_mulEquiv wPlusEquiv,
    card_map_of_injective wPlusEquiv.injective]

theorem lieModel_wPlus :
    CFSG.Blueprint.LieModel (wPlus.subgroupOf wE8 ⧸ center (wPlus.subgroupOf wE8))
      .POmegaPlus 4 2 1 :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.congr _ _ wPlusEquiv.symm
    (map_center_mulEquiv wPlusEquiv.symm)) h.model.lieModel

theorem aut_wPlus (φ : MulAut (wPlus.subgroupOf wE8)) :
    ∃ w : wE8, ∀ x : wPlus.subgroupOf wE8, (φ x : wE8) = w * x * w⁻¹ := by
  obtain ⟨w, hw, hφ⟩ := h.aut.conj (MulAut.congr wPlusEquiv φ)
  refine ⟨⟨w, hw⟩, fun x => Subtype.ext ?_⟩
  have h1 := hφ (wPlusEquiv x)
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    coe_wPlusEquiv, coe_wPlusEquiv] at h1
  exact h1

theorem fours_wPlus : FoursGroupCondition (wPlus.subgroupOf wE8) :=
  FoursGroupCondition.of_mulEquiv wPlusEquiv.symm h.aut.foursGroup

theorem sign_sZero : Equiv.Perm.sign sZero = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign sZero) with h1 | h1
  · exact absurd (Subgroup.mem_inf.2 ⟨h.model.sZero_mem, Equiv.Perm.mem_alternatingGroup.2 h1⟩)
      h.model.sZero_not_mem
  · exact h1

theorem mem_or_mul_mem_wPlus (w : wE8) :
    w ∈ wPlus.subgroupOf wE8 ∨ w * ⟨sZero, h.model.sZero_mem⟩ ∈ wPlus.subgroupOf wE8 := by
  rw [mem_subgroupOf, mem_subgroupOf]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (w : Equiv.Perm (Fin 240))) with h1 | h1
  · exact Or.inl (Subgroup.mem_inf.2 ⟨w.2, Equiv.Perm.mem_alternatingGroup.2 h1⟩)
  · refine Or.inr (Subgroup.mem_inf.2 ⟨mul_mem w.2 h.model.sZero_mem,
      Equiv.Perm.mem_alternatingGroup.2 ?_⟩)
    rw [coe_mul, Equiv.Perm.sign_mul, h1, sign_sZero h]
    decide

theorem mul_self_ne_wPlus (w : wE8) (hw : w ∈ wPlus.subgroupOf wE8) :
    w * ⟨sZero, h.model.sZero_mem⟩ * (w * ⟨sZero, h.model.sZero_mem⟩) ≠
      ⟨zPerm, zPerm_mem_wE8 h⟩ := fun he => by
  have h1 := h.model.sq_eq_zPerm ((w : Equiv.Perm (Fin 240)) * sZero)
    (mul_mem w.2 h.model.sZero_mem) (congrArg Subtype.val he)
  apply h.model.sZero_not_mem
  have h2 := mul_mem (inv_mem (mem_subgroupOf.1 hw)) h1
  rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2

theorem card_wE8 : Nat.card wE8 = 2 ^ 14 * 42525 := by
  rw [h.model.card_wE8]
  norm_num

theorem card_tSubW : Nat.card (tSub.subgroupOf wE8) = 2 ^ 14 := by
  rw [card_subgroupOf_of_le h.sylow.tSub_le, h.sylow.card_tSub]

theorem tSub_inf_wPlus :
    tSub.subgroupOf wE8 ⊓ wPlus.subgroupOf wE8 = tPlusSub.subgroupOf wE8 := by
  rw [inf_subgroupOf_eq, h.sylow.tPlusSub_eq]

theorem card_tPlusW : Nat.card (tSub.subgroupOf wE8 ⊓ wPlus.subgroupOf wE8 : Subgroup wE8) =
    2 ^ 13 := by
  rw [tSub_inf_wPlus h, card_subgroupOf_of_le (h.sylow.tPlusSub_eq ▸ inf_le_left.trans
    h.sylow.tSub_le), h.sylow.card_tPlusSub]

theorem center_tSubW (t : wE8) (ht : t ∈ tSub.subgroupOf wE8)
    (hc : ∀ u ∈ tSub.subgroupOf wE8, t * u = u * t) :
    t = 1 ∨ t = ⟨zPerm, zPerm_mem_wE8 h⟩ := by
  rcases h.sylow.center_tSub t (mem_subgroupOf.1 ht) (fun y hy => congrArg Subtype.val
    (hc ⟨y, h.sylow.tSub_le hy⟩ (mem_subgroupOf.2 hy))) with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

theorem center_tPlusW (t : wE8) (ht : t ∈ tSub.subgroupOf wE8 ⊓ wPlus.subgroupOf wE8)
    (hc : ∀ u ∈ tSub.subgroupOf wE8 ⊓ wPlus.subgroupOf wE8, t * u = u * t) :
    t = 1 ∨ t = ⟨zPerm, zPerm_mem_wE8 h⟩ := by
  rw [tSub_inf_wPlus h] at ht hc
  have hle : tPlusSub ≤ wE8 := h.sylow.tPlusSub_eq ▸ inf_le_left.trans h.sylow.tSub_le
  rcases h.sylow.center_tPlusSub t (mem_subgroupOf.1 ht) (fun y hy => congrArg Subtype.val
    (hc ⟨y, hle hy⟩ (mem_subgroupOf.2 hy))) with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

theorem ιE_injective : Function.Injective (ιE h) := fun a b hab => by
  have h1 := h.coords.signPerm_inj _ (Multiplicative.toAdd a).2 _ (Multiplicative.toAdd b).2
    (congrArg Subtype.val hab)
  exact Subtype.ext h1

theorem ιE_evenZ : ιE h (Multiplicative.ofAdd evenZ) = ⟨zPerm, zPerm_mem_wE8 h⟩ :=
  Subtype.ext h.coords.signPerm_frameZ

theorem ιE_mem (v : Multiplicative evenSub) :
    ιE h v ∈ tSub.subgroupOf wE8 ⊓ wPlus.subgroupOf wE8 := by
  rw [tSub_inf_wPlus h, mem_subgroupOf]
  exact h.sylow.eSub_le (signPerm_mem_eSub h (Multiplicative.toAdd v).2)

theorem mem_normalizer_eSub {w : wE8} (hw : ∀ v, w * ιE h v * w⁻¹ ∈ (ιE h).range) :
    (w : Equiv.Perm (Fin 240)) ∈ normalizer (eSub : Set (Equiv.Perm (Fin 240))) := by
  apply mem_normalizer_of_conj_mem
  intro x hx
  obtain ⟨v, hv, rfl⟩ := (h.coords.mem_eSub x).1 hx
  have h1 := (mem_range_ιE h).1 (hw (Multiplicative.ofAdd ⟨v, hv⟩))
  simp only [coe_mul, coe_inv, coe_ιE, toAdd_ofAdd] at h1
  exact h1

theorem E_up (w : wE8) (hw : w ∈ wPlus.subgroupOf wE8)
    (hn : ∀ v, w * ιE h v * w⁻¹ ∈ (ιE h).range) : ∃ σ ∈ alternatingGroup (Fin 8), ∀ v,
      w * ιE h v * w⁻¹ = ιE h (Multiplicative.ofAdd (evenPerm σ (Multiplicative.toAdd v))) := by
  obtain ⟨σ, hσ, hσ'⟩ := h.normalizers.normalizer_eSub w w.2 (mem_normalizer_eSub h hn)
  exact ⟨σ, hσ'.1 (mem_subgroupOf.1 hw), fun v => Subtype.ext (hσ _ (Multiplicative.toAdd v).2)⟩

theorem E_down (σ : Equiv.Perm (Fin 8)) (hσ : σ ∈ alternatingGroup (Fin 8)) :
    ∃ w ∈ wPlus.subgroupOf wE8, ∀ v,
      w * ιE h v * w⁻¹ = ιE h (Multiplicative.ofAdd (evenPerm σ (Multiplicative.toAdd v))) := by
  obtain ⟨h1, -, h3⟩ := h.normalizers.permMat_mem σ
  exact ⟨⟨permMat σ, h1⟩, mem_subgroupOf.2 ((h.normalizers.permMat_mem_wPlus σ).2 hσ),
    fun v => Subtype.ext (h3 _ (Multiplicative.toAdd v).2)⟩

theorem centralizer_E (w : wE8) (hw : ∀ v, w * ιE h v = ιE h v * w) : w ∈ (ιE h).range := by
  rw [mem_range_ιE]
  refine h.sylow.centralizer_eSub w w.2 fun e he => ?_
  obtain ⟨v, hv, rfl⟩ := (h.coords.mem_eSub e).1 he
  exact congrArg Subtype.val (hw (Multiplicative.ofAdd ⟨v, hv⟩))

theorem ιE1_injective : Function.Injective (ιE1 h) := fun _ _ hab =>
  h.coords.frameElt_injective (congrArg Subtype.val hab)

theorem ιE1_frameZ : ιE1 h (Multiplicative.ofAdd frameZ) = ⟨zPerm, zPerm_mem_wE8 h⟩ :=
  Subtype.ext h.coords.frameElt_frameZ

theorem ιE1_mem_T (v : Multiplicative FrameVec) : ιE1 h v ∈ tSub.subgroupOf wE8 :=
  mem_subgroupOf.2 (h.sylow.e1Sub_le (frameElt_mem_e1Sub h _))

theorem ιE1_mem_iff (v : FrameVec) :
    ιE1 h (Multiplicative.ofAdd v) ∈ wPlus.subgroupOf wE8 ↔ v ∈ evenSub := by
  rw [mem_subgroupOf]
  constructor
  · intro hv
    have h1 : frameElt v ∈ e1PlusSub := by
      rw [h.coords.e1PlusSub_eq]
      exact ⟨frameElt_mem_e1Sub h v, hv⟩
    obtain ⟨u, hu, hu'⟩ := (h.coords.mem_e1PlusSub _).1 h1
    rwa [← h.coords.frameElt_injective hu']
  · intro hv
    have h1 : frameElt v ∈ e1PlusSub := (h.coords.mem_e1PlusSub _).2 ⟨v, hv, rfl⟩
    rw [h.coords.e1PlusSub_eq] at h1
    exact h1.2

theorem s_mem : (⟨sZero, h.model.sZero_mem⟩ : wE8) ∈ (ιE1 h).range :=
  ⟨Multiplicative.ofAdd (frameE 0), Subtype.ext h.coords.sZero_eq.1.symm⟩

theorem frame_gens (σ : Equiv.Perm (Fin 8)) (hσ : σ ∈ frameGens) :
    ∃ w ∈ wPlus.subgroupOf wE8, ∀ v : FrameVec,
      w * ιE1 h (Multiplicative.ofAdd v) * w⁻¹ = ιE1 h (Multiplicative.ofAdd (permVec σ v)) := by
  obtain ⟨w, hw, h1⟩ := h.normalizers.frameAut_realized σ (frameGens_subset_frameAut hσ)
  exact ⟨⟨w, wPlus_le_wE8 hw⟩, mem_subgroupOf.2 hw, fun v => Subtype.ext (h1 v)⟩

theorem frame_up (w : wE8) (hn : ∀ v, w * ιE1 h v * w⁻¹ ∈ (ιE1 h).range) :
    ∃ σ ∈ frameAut, ∀ v : FrameVec,
      w * ιE1 h (Multiplicative.ofAdd v) * w⁻¹ = ιE1 h (Multiplicative.ofAdd (permVec σ v)) := by
  have hN : (w : Equiv.Perm (Fin 240)) ∈ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) := by
    apply mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨v, rfl⟩ := (h.coords.mem_e1Sub x).1 hx
    have h1 := (mem_range_ιE1 h).1 (hn (Multiplicative.ofAdd v))
    simp only [coe_mul, coe_inv, coe_ιE1, toAdd_ofAdd] at h1
    exact h1
  obtain ⟨σ, hσ, h1⟩ := h.normalizers.normalizer_e1Sub w w.2 hN
  exact ⟨σ, hσ, fun v => Subtype.ext (h1 v)⟩

theorem centralizer_E1p (w : wE8)
    (hw : ∀ v ∈ evenSub, w * ιE1 h (Multiplicative.ofAdd v) = ιE1 h (Multiplicative.ofAdd v) * w) :
    w ∈ (ιE1 h).range := by
  rw [mem_range_ιE1]
  refine h.sylow.centralizer_e1PlusSub w w.2 fun e he => ?_
  obtain ⟨v, hv, rfl⟩ := (h.coords.mem_e1PlusSub e).1 he
  exact congrArg Subtype.val (hw v hv)

theorem reps_mem (v : FrameVec) (hv : v ∈ ({frameE 0 + frameE 1, blockVec {0, 1, 2, 3},
    frameZ + frameE 0 + frameE 1} : Set FrameVec)) :
    ιE1 h (Multiplicative.ofAdd v) ∈ (ιE h).range := by
  rw [mem_range_ιE, coe_ιE1, toAdd_ofAdd]
  have h01 : frameElt (vec2 0 1) = signPerm (vec2 0 1) :=
    (h.coords.signPerm_pair 0 (by decide)).symm
  have hv01 : vec2 0 1 ∈ evenSub := vec2_mem_evenSub (by decide)
  rcases hv with rfl | rfl | rfl
  · exact h01 ▸ signPerm_mem_eSub h hv01
  · rw [← h.involutions.xPlane_eq]
    exact xPlane_mem_eSub h
  · rw [add_assoc, h.coords.frameElt_add, h.coords.frameElt_frameZ,
      show frameE 0 + frameE 1 = vec2 0 1 from rfl, h01, ← h.coords.signPerm_frameZ]
    exact mul_mem (signPerm_mem_eSub h evenZ.2) (signPerm_mem_eSub h hv01)

theorem e1PlusSub_le_e1Sub : e1PlusSub ≤ e1Sub := h.coords.e1PlusSub_eq ▸ inf_le_left

theorem not_conj (w : wE8) (hw : w ∈ wPlus.subgroupOf wE8) :
    ¬ ∀ v, w * ιE h v * w⁻¹ ∈ (ιE1 h).range := by
  intro hall
  have hw' : (w : Equiv.Perm (Fin 240)) ∈ wPlus := mem_subgroupOf.1 hw
  have hsub : eSub.map (MulAut.conj (w : Equiv.Perm (Fin 240))).toMonoidHom ≤ e1PlusSub := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (h.coords.mem_eSub x).1 hx
    have h1 := (mem_range_ιE1 h).1 (hall (Multiplicative.ofAdd ⟨v, hv⟩))
    simp only [coe_mul, coe_inv, coe_ιE, toAdd_ofAdd] at h1
    rw [h.coords.e1PlusSub_eq]
    exact Subgroup.mem_inf.2 ⟨h1,
      mul_mem (mul_mem hw' (h.coords.eSub_le (signPerm_mem_eSub h hv))) (inv_mem hw')⟩
  have heq : eSub.map (MulAut.conj (w : Equiv.Perm (Fin 240))).toMonoidHom = e1PlusSub :=
    eq_of_le_of_card_ge hsub (by
      rw [card_map_of_injective (MulAut.conj _).injective, h.abelian.card_eSub,
        h.abelian.card_e1PlusSub])
  have hmap : (wPlus ⊓ normalizer (eSub : Set (Equiv.Perm (Fin 240)))).map
      (MulAut.conj (w : Equiv.Perm (Fin 240))).toMonoidHom ≤
        wPlus ⊓ normalizer (e1Sub : Set (Equiv.Perm (Fin 240))) := by
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.1 hn
    have hconj : (MulAut.conj (w : Equiv.Perm (Fin 240))).toMonoidHom n ∈ wPlus :=
      mul_mem (mul_mem hw' hn1) (inv_mem hw')
    refine Subgroup.mem_inf.2 ⟨hconj, ?_⟩
    rw [← h.normalizers.normalizer_e1PlusSub _ (wPlus_le_wE8 hconj)]
    apply mem_normalizer_of_conj_mem
    intro y hy
    rw [← heq] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨n * x * n⁻¹, (mem_normalizer_iff.1 hn2 x).1 hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have h1 := card_le_of_le hmap
  rw [card_map_of_injective (MulAut.conj _).injective,
    h.normalizers.card_normalizer_eSub_plus, h.normalizers.card_normalizer_e1Sub_plus] at h1
  norm_num at h1

theorem elem_Tp (B : Subgroup wE8) (hB : B ≤ tSub.subgroupOf wE8 ⊓ wPlus.subgroupOf wE8)
    (hB2 : ∀ b ∈ B, b * b = 1) (hBc : Nat.card B = 2 ^ 7) :
    B = (ιE h).range ∨ B = (ιE1 h).range ⊓ wPlus.subgroupOf wE8 := by
  rw [tSub_inf_wPlus h] at hB
  have hB'le : B.map wE8.subtype ≤ tPlusSub := by
    rintro _ ⟨b, hb, rfl⟩
    exact mem_subgroupOf.1 (hB hb)
  have hB'2 : ∀ b ∈ B.map wE8.subtype, b * b = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hB2 b hb)
  have hcomm : ∀ a ∈ B.map wE8.subtype, ∀ b ∈ B.map wE8.subtype, a * b = b * a :=
    fun a ha b hb => comm_of_mul_self (hB'2 a ha) (hB'2 b hb) (hB'2 _ (mul_mem ha hb))
  have key : ∀ b : wE8, b ∈ B ↔ (b : Equiv.Perm (Fin 240)) ∈ B.map wE8.subtype :=
    fun b => (mem_map_iff_mem wE8.subtype_injective).symm
  rcases h.abelian.abelian_tPlus _ hB'le hcomm
      (by rw [card_map_of_injective wE8.subtype_injective, hBc]) with h1 | h1 | h1
  · left
    ext b
    rw [key, h1, mem_range_ιE]
  · right
    ext b
    rw [key, h1, Subgroup.mem_inf, mem_range_ιE1, mem_subgroupOf, h.coords.e1PlusSub_eq,
      Subgroup.mem_inf]
  · exfalso
    obtain ⟨u, hu, hu1⟩ := h.abelian.not_sq_uPrimeSub
    exact hu1 (hB'2 u (h1 ▸ hu))

theorem elem_T (B : Subgroup wE8) (hB : B ≤ tSub.subgroupOf wE8) (hB2 : ∀ b ∈ B, b * b = 1)
    (hBc : Nat.card B = 2 ^ 8) : B = (ιE1 h).range := by
  have hB'le : B.map wE8.subtype ≤ tSub := by
    rintro _ ⟨b, hb, rfl⟩
    exact mem_subgroupOf.1 (hB hb)
  have hB'2 : ∀ b ∈ B.map wE8.subtype, b * b = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hB2 b hb)
  have h1 := h.abelian.abelian_t _ hB'le
    (fun a ha b hb => comm_of_mul_self (hB'2 a ha) (hB'2 b hb) (hB'2 _ (mul_mem ha hb)))
    (by rw [card_map_of_injective wE8.subtype_injective, hBc])
  ext b
  rw [← mem_map_iff_mem wE8.subtype_injective, h1, mem_range_ιE1]
  rfl

theorem inv_Wp (y : wE8) (hy : y ∈ wPlus.subgroupOf wE8) (hy2 : y * y = 1) :
    ∃ w ∈ wPlus.subgroupOf wE8, w * y * w⁻¹ ∈ (ιE1 h).range := by
  obtain ⟨g, hg, h1⟩ := h.involutions.conj_e1PlusSub y (mem_subgroupOf.1 hy)
    (congrArg Subtype.val hy2)
  exact ⟨⟨g, wPlus_le_wE8 hg⟩, mem_subgroupOf.2 hg,
    (mem_range_ιE1 h).2 (e1PlusSub_le_e1Sub h h1)⟩

theorem inv_W (y : wE8) (hy2 : y * y = 1) : ∃ w : wE8, w * y * w⁻¹ ∈ (ιE1 h).range := by
  obtain ⟨g, hg, h1⟩ := h.involutions.conj_e1Sub y y.2 (congrArg Subtype.val hy2)
  exact ⟨⟨g, hg⟩, (mem_range_ιE1 h).2 h1⟩

theorem signPerm_ne {u v : FrameVec} (hu : u ∈ evenSub) (hv : v ∈ evenSub) (huv : u ≠ v) :
    signPerm u ≠ signPerm v := fun he => huv (h.coords.signPerm_inj u hu v hv he)

omit h in
theorem xhat_mem : vec2 0 1 + vec2 2 3 ∈ evenSub :=
  add_mem (vec2_mem_evenSub (by decide)) (vec2_mem_evenSub (by decide))

theorem xPlane_ne_one : xPlane ≠ 1 := by
  rw [← signPerm_zero h]
  exact signPerm_ne h xhat_mem (zero_mem _) (by decide)

theorem xPlane_ne_zPerm : xPlane ≠ zPerm := by
  rw [← h.coords.signPerm_frameZ]
  exact signPerm_ne h xhat_mem evenZ.2 (by decide)

theorem mul_self_of_mem_eSub {x : Equiv.Perm (Fin 240)} (hx : x ∈ eSub) : x * x = 1 :=
  h.abelian.sq_eSub x hx

theorem comm_of_mem_eSub {x y : Equiv.Perm (Fin 240)} (hx : x ∈ eSub) (hy : y ∈ eSub) :
    x * y = y * x :=
  comm_of_mul_self (mul_self_of_mem_eSub h hx) (mul_self_of_mem_eSub h hy)
    (mul_self_of_mem_eSub h (mul_mem hx hy))

theorem zPerm_mem_eSub : zPerm ∈ eSub := h.coords.signPerm_frameZ ▸ signPerm_mem_eSub h evenZ.2

theorem mem_uSub_iff (u : Equiv.Perm (Fin 240)) :
    u ∈ uSub ↔ u = 1 ∨ u = xPlane ∨ u = zPerm ∨ u = xPlane * zPerm := by
  have hx := h.uArg.xPlane_mem
  have hz := h.uArg.zPerm_mem
  set V := kleinFour xPlane zPerm (mul_self_of_mem_eSub h (xPlane_mem_eSub h)) h.model.zPerm_sq
    (comm_of_mem_eSub h (xPlane_mem_eSub h) (zPerm_mem_eSub h)) with hV
  have hVU : V ≤ uSub := by
    rintro _ (rfl | rfl | rfl | rfl)
    exacts [one_mem _, hx, hz, mul_mem hx hz]
  have heq : V = uSub := eq_of_le_of_card_ge hVU (by
    rw [h.uArg.card_uSub, hV, card_kleinFour _ _ _ (xPlane_ne_one h) h.model.zPerm_ne_one
      (xPlane_ne_zPerm h)])
  rw [← heq]
  rfl

theorem normal_four (v : wE8) (hv : v ∈ tSub.subgroupOf wE8) (hv2 : v * v = 1)
    (ht : ∀ t ∈ tSub.subgroupOf wE8, t * v * t⁻¹ = v ∨ t * v * t⁻¹ = v * ⟨zPerm, zPerm_mem_wE8 h⟩) :
    v = 1 ∨ v = ⟨xPlane, xPlane_mem_wE8 h⟩ ∨ v = ⟨zPerm, zPerm_mem_wE8 h⟩ ∨
      v = ⟨xPlane, xPlane_mem_wE8 h⟩ * ⟨zPerm, zPerm_mem_wE8 h⟩ := by
  by_cases hv1 : v = 1
  · exact Or.inl hv1
  by_cases hvz : v = ⟨zPerm, zPerm_mem_wE8 h⟩
  · exact Or.inr (Or.inr (Or.inl hvz))
  have hv'2 : (v : Equiv.Perm (Fin 240)) * v = 1 := congrArg Subtype.val hv2
  have hvzc : (v : Equiv.Perm (Fin 240)) * zPerm = zPerm * v := h.model.zPerm_comm v v.2
  have hv1' : (v : Equiv.Perm (Fin 240)) ≠ 1 := fun h' => hv1 (Subtype.ext h')
  have hvz' : (v : Equiv.Perm (Fin 240)) ≠ zPerm := fun h' => hvz (Subtype.ext h')
  have hzT : zPerm ∈ tSub := h.sylow.e1Sub_le (h.coords.frameElt_frameZ ▸ frameElt_mem_e1Sub h _)
  have hvT : (v : Equiv.Perm (Fin 240)) ∈ tSub := mem_subgroupOf.1 hv
  have hVU := h.uArg.unique (kleinFour (v : Equiv.Perm (Fin 240)) zPerm hv'2 h.model.zPerm_sq hvzc)
    (by
      rintro _ (rfl | rfl | rfl | rfl)
      exacts [one_mem _, hvT, hzT, mul_mem hvT hzT])
    (card_kleinFour _ _ _ hv1' h.model.zPerm_ne_one hvz') (fun x hx => mul_self_of_kleinFour hx)
    (by
      intro t ht' x hx
      have htz : t * zPerm * t⁻¹ = zPerm := by
        rw [h.model.zPerm_comm t (h.sylow.tSub_le ht')]
        group
      have h1 : t * v * t⁻¹ = (v : Equiv.Perm (Fin 240)) ∨ t * v * t⁻¹ = v * zPerm := by
        rcases ht ⟨t, h.sylow.tSub_le ht'⟩ (mem_subgroupOf.2 ht') with h1 | h1
        · exact Or.inl (congrArg Subtype.val h1)
        · exact Or.inr (congrArg Subtype.val h1)
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl (by group)
      · rcases h1 with h1 | h1 <;> rw [h1]
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr rfl))
      · rw [htz]
        exact Or.inr (Or.inr (Or.inl rfl))
      · have e : t * (v * zPerm) * t⁻¹ = t * v * t⁻¹ * (t * zPerm * t⁻¹) := by group
        rw [e, htz]
        rcases h1 with h1 | h1 <;> rw [h1]
        · exact Or.inr (Or.inr (Or.inr rfl))
        · rw [mul_assoc, h.model.zPerm_sq, mul_one]
          exact Or.inr (Or.inl rfl))
  have hvU : (v : Equiv.Perm (Fin 240)) ∈ uSub := hVU ▸ (Or.inr (Or.inl rfl))
  rcases (mem_uSub_iff h _).1 hvU with h1 | h1 | h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Or.inl (Subtype.ext h1))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h1)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h1)))

theorem tPlusSub_le_tSub : tPlusSub ≤ tSub := h.sylow.tPlusSub_eq ▸ inf_le_left

theorem eSub_le_tSub : eSub ≤ tSub := h.sylow.eSub_le.trans (tPlusSub_le_tSub h)

theorem conj_mem_e1Sub {t : Equiv.Perm (Fin 240)} (ht : t ∈ tSub) {k : Equiv.Perm (Fin 240)}
    (hk : k ∈ e1Sub) : t * k * t⁻¹ ∈ e1Sub := by
  have hB := h.abelian.abelian_t (e1Sub.map (MulAut.conj t).toMonoidHom)
    (by
      rintro _ ⟨e, he, rfl⟩
      exact mul_mem (mul_mem ht (h.sylow.e1Sub_le he)) (inv_mem ht))
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc t * a * t⁻¹ * (t * b * t⁻¹) = t * (a * b) * t⁻¹ := by group
        _ = t * (b * a) * t⁻¹ := by rw [h.abelian.comm_e1Sub a ha b hb]
        _ = t * b * t⁻¹ * (t * a * t⁻¹) := by group)
    (by rw [card_map_of_injective (MulAut.conj t).injective, h.abelian.card_e1Sub])
  rw [← hB]
  exact ⟨k, hk, rfl⟩

theorem mem_CW {y : wE8} : y ∈ tSub.subgroupOf wE8 ⊓ centralizer ({⟨xPlane, xPlane_mem_wE8 h⟩} :
    Set wE8) ↔ (y : Equiv.Perm (Fin 240)) ∈ tSub ⊓ centralizer {xPlane} := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_subgroupOf, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  exact and_congr_right fun _ => ⟨fun h' => congrArg Subtype.val h', fun h' => Subtype.ext h'⟩

theorem CW_eq : tSub.subgroupOf wE8 ⊓ centralizer ({⟨xPlane, xPlane_mem_wE8 h⟩} : Set wE8) =
    (tSub ⊓ centralizer {xPlane}).subgroupOf wE8 := by
  ext y
  rw [mem_CW h, mem_subgroupOf]

theorem card_CW : Nat.card (tSub.subgroupOf wE8 ⊓
    centralizer ({⟨xPlane, xPlane_mem_wE8 h⟩} : Set wE8) : Subgroup wE8) = 2 ^ 13 := by
  rw [CW_eq h, card_subgroupOf_of_le (inf_le_left.trans h.sylow.tSub_le), h.uArg.card_cT]

theorem center_CW (c : wE8)
    (hc : c ∈ tSub.subgroupOf wE8 ⊓ centralizer ({⟨xPlane, xPlane_mem_wE8 h⟩} : Set wE8))
    (hcent : ∀ d ∈ tSub.subgroupOf wE8 ⊓ centralizer ({⟨xPlane, xPlane_mem_wE8 h⟩} : Set wE8),
      c * d = d * c) :
    c = 1 ∨ c = ⟨xPlane, xPlane_mem_wE8 h⟩ ∨ c = ⟨zPerm, zPerm_mem_wE8 h⟩ ∨
      c = ⟨xPlane, xPlane_mem_wE8 h⟩ * ⟨zPerm, zPerm_mem_wE8 h⟩ := by
  have h1 := (h.uArg.center_cT c ((mem_CW h).1 hc)).1 fun d hd =>
    congrArg Subtype.val (hcent ⟨d, h.sylow.tSub_le hd.1⟩ ((mem_CW h).2 hd))
  rcases (mem_uSub_iff h _).1 h1 with h2 | h2 | h2 | h2
  · exact Or.inl (Subtype.ext h2)
  · exact Or.inr (Or.inl (Subtype.ext h2))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h2)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h2)))

theorem S_mem_C {v : FrameVec} (hv : v ∈ evenSub) : signPerm v ∈ tSub ⊓ centralizer {xPlane} :=
  Subgroup.mem_inf.2 ⟨eSub_le_tSub h (signPerm_mem_eSub h hv), mem_centralizer_singleton_iff.2
    (comm_of_mem_eSub h (signPerm_mem_eSub h hv) (xPlane_mem_eSub h))⟩

omit h in
theorem v02_mem : vec2 0 2 ∈ evenSub := vec2_mem_evenSub (by decide)

omit h in
theorem v46_mem : vec2 4 6 ∈ evenSub := vec2_mem_evenSub (by decide)

theorem zc_S {v : FrameVec} (hv : v ∈ evenSub)
    (hS : signPerm v ∈ e1Sub ⊔ closure {signPerm (vec2 0 2), signPerm (vec2 4 6)}) (d : wE8)
    (hd : d ∈ tSub.subgroupOf wE8 ⊓ centralizer ({⟨xPlane, xPlane_mem_wE8 h⟩} : Set wE8)) :
    (⟨signPerm v, signPerm_mem_wE8 h hv⟩ : wE8) * d * ⟨signPerm v, signPerm_mem_wE8 h hv⟩⁻¹ *
      d⁻¹ ∈ (ιE1 h).range := by
  rw [mem_range_ιE1]
  exact (h.uArg.center_mod _ (S_mem_C h hv)).2 hS d ((mem_CW h).1 hd)

omit h in
theorem S02_mem_sup : signPerm (vec2 0 2) ∈ e1Sub ⊔ closure {signPerm (vec2 0 2),
    signPerm (vec2 4 6)} := mem_sup_right (subset_closure (Set.mem_insert _ _))

omit h in
theorem S46_mem_sup : signPerm (vec2 4 6) ∈ e1Sub ⊔ closure {signPerm (vec2 0 2),
    signPerm (vec2 4 6)} := mem_sup_right (subset_closure (Set.mem_insert_of_mem _ rfl))

theorem zc (c : wE8)
    (hc : c ∈ tSub.subgroupOf wE8 ⊓ centralizer ({⟨xPlane, xPlane_mem_wE8 h⟩} : Set wE8))
    (hcent : ∀ d ∈ tSub.subgroupOf wE8 ⊓ centralizer ({⟨xPlane, xPlane_mem_wE8 h⟩} : Set wE8),
      c * d * c⁻¹ * d⁻¹ ∈ (ιE1 h).range) :
    c ∈ (ιE1 h).range ∨ (⟨signPerm (vec2 0 2), signPerm_mem_wE8 h v02_mem⟩ : wE8)⁻¹ * c ∈
      (ιE1 h).range ∨ (⟨signPerm (vec2 4 6), signPerm_mem_wE8 h v46_mem⟩ : wE8)⁻¹ * c ∈
        (ιE1 h).range ∨ ((⟨signPerm (vec2 0 2), signPerm_mem_wE8 h v02_mem⟩ : wE8) *
          ⟨signPerm (vec2 4 6), signPerm_mem_wE8 h v46_mem⟩)⁻¹ * c ∈ (ιE1 h).range := by
  have h1 := (h.uArg.center_mod _ ((mem_CW h).1 hc)).1 fun d hd => by
    have h2 := hcent ⟨d, h.sylow.tSub_le hd.1⟩ ((mem_CW h).2 hd)
    rw [mem_range_ιE1] at h2
    exact h2
  have hT02 := eSub_le_tSub h (signPerm_mem_eSub h v02_mem)
  have hT46 := eSub_le_tSub h (signPerm_mem_eSub h v46_mem)
  rcases mem_cosets_of_mem_sup (fun k hk => conj_mem_e1Sub h hT02 hk)
      (fun k hk => conj_mem_e1Sub h hT46 hk) (mul_self_of_mem_eSub h (signPerm_mem_eSub h v02_mem))
      (mul_self_of_mem_eSub h (signPerm_mem_eSub h v46_mem))
      (comm_of_mem_eSub h (signPerm_mem_eSub h v02_mem) (signPerm_mem_eSub h v46_mem)) h1 with
    h2 | h2 | h2 | h2
  · exact Or.inl ((mem_range_ιE1 h).2 h2)
  · exact Or.inr (Or.inl ((mem_range_ιE1 h).2 h2))
  · exact Or.inr (Or.inr (Or.inl ((mem_range_ιE1 h).2 h2)))
  · exact Or.inr (Or.inr (Or.inr ((mem_range_ιE1 h).2 h2)))

theorem S01_ne_one : signPerm (vec2 0 1) ≠ 1 := by
  rw [← signPerm_zero h]
  exact signPerm_ne h (vec2_mem_evenSub (by decide)) (zero_mem _) (by decide)

theorem S45_ne_one : signPerm (vec2 4 5) ≠ 1 := by
  rw [← signPerm_zero h]
  exact signPerm_ne h (vec2_mem_evenSub (by decide)) (zero_mem _) (by decide)

theorem not_mem_e1Sub_of_comm {c g : Equiv.Perm (Fin 240)} (hg : g ≠ 1)
    (hcomm : ∃ e ∈ e1Sub, g = e * c * e⁻¹ * c⁻¹) : c ∉ e1Sub := fun hc => by
  obtain ⟨e, he, rfl⟩ := hcomm
  apply hg
  rw [h.abelian.comm_e1Sub e he c hc]
  group

theorem s₁_not_mem : (⟨signPerm (vec2 0 2), signPerm_mem_wE8 h v02_mem⟩ : wE8) ∉ (ιE1 h).range := by
  rw [mem_range_ιE1]
  exact not_mem_e1Sub_of_comm h (S01_ne_one h)
    ((h.uArg.comm_02 _).2 (subset_closure (Set.mem_insert _ _)))

theorem s₂_not_mem : (⟨signPerm (vec2 4 6), signPerm_mem_wE8 h v46_mem⟩ : wE8) ∉ (ιE1 h).range := by
  rw [mem_range_ιE1]
  exact not_mem_e1Sub_of_comm h (S45_ne_one h)
    ((h.uArg.comm_46 _).2 (subset_closure (Set.mem_insert _ _)))

theorem S02_mul_S46 : signPerm (vec2 0 2) * signPerm (vec2 4 6) = signPerm (vec2 0 2 + vec2 4 6) :=
  (h.coords.signPerm_add _ v02_mem _ v46_mem).symm

theorem inv_mul_not_mem : (⟨signPerm (vec2 0 2), signPerm_mem_wE8 h v02_mem⟩ : wE8)⁻¹ *
    ⟨signPerm (vec2 4 6), signPerm_mem_wE8 h v46_mem⟩ ∉ (ιE1 h).range := by
  rw [mem_range_ιE1]
  change (signPerm (vec2 0 2))⁻¹ * signPerm (vec2 4 6) ∉ e1Sub
  rw [inv_eq_of_mul_eq_one_right (mul_self_of_mem_eSub h (signPerm_mem_eSub h v02_mem)),
    S02_mul_S46 h]
  exact not_mem_e1Sub_of_comm h (S01_ne_one h)
    ((h.uArg.comm_0246 _).2 (subset_closure (Set.mem_insert _ _)))

theorem xPlane_eq_mul : xPlane = signPerm (vec2 0 1) * signPerm (vec2 2 3) :=
  h.coords.signPerm_add _ (vec2_mem_evenSub (by decide)) _ (vec2_mem_evenSub (by decide))

theorem comm_eq : ∃ e ∈ (ιE1 h).range, e * ⟨signPerm (vec2 0 2), signPerm_mem_wE8 h v02_mem⟩ *
    e⁻¹ * (⟨signPerm (vec2 0 2), signPerm_mem_wE8 h v02_mem⟩ : wE8)⁻¹ =
      ⟨xPlane, xPlane_mem_wE8 h⟩ := by
  obtain ⟨e, he, hx⟩ := (h.uArg.comm_02 xPlane).2 (by
    rw [xPlane_eq_mul h]
    exact mul_mem (subset_closure (Set.mem_insert _ _))
      (subset_closure (Set.mem_insert_of_mem _ rfl)))
  exact ⟨⟨e, h.coords.e1Sub_le he⟩, (mem_range_ιE1 h).2 he, Subtype.ext hx.symm⟩

theorem xz_ne_one : xPlane * zPerm ≠ 1 := fun he => xPlane_ne_zPerm h (by
  rw [mul_eq_one_iff_eq_inv.1 he, inv_eq_of_mul_eq_one_right h.model.zPerm_sq])

theorem comm_ne (e : wE8) (he : e ∈ (ιE1 h).range) :
    e * ⟨signPerm (vec2 0 2), signPerm_mem_wE8 h v02_mem⟩ * e⁻¹ *
        (⟨signPerm (vec2 0 2), signPerm_mem_wE8 h v02_mem⟩ : wE8)⁻¹ ≠ ⟨zPerm, zPerm_mem_wE8 h⟩ ∧
      e * ⟨signPerm (vec2 0 2), signPerm_mem_wE8 h v02_mem⟩ * e⁻¹ *
        (⟨signPerm (vec2 0 2), signPerm_mem_wE8 h v02_mem⟩ : wE8)⁻¹ ≠
          ⟨xPlane, xPlane_mem_wE8 h⟩ * ⟨zPerm, zPerm_mem_wE8 h⟩ := by
  have hcl := (h.uArg.comm_02 ((e : Equiv.Perm (Fin 240)) * signPerm (vec2 0 2) *
    (e : Equiv.Perm (Fin 240))⁻¹ * (signPerm (vec2 0 2))⁻¹)).1 ⟨e, (mem_range_ιE1 h).1 he, rfl⟩
  constructor
  · intro h1
    have h2 := congrArg Subtype.val h1
    change (e : Equiv.Perm (Fin 240)) * signPerm (vec2 0 2) * (e : Equiv.Perm (Fin 240))⁻¹ *
      (signPerm (vec2 0 2))⁻¹ = zPerm at h2
    rw [h2] at hcl
    rcases (h.uArg.inf_uSub zPerm h.uArg.zPerm_mem).1 hcl with h3 | h3
    · exact h.model.zPerm_ne_one h3
    · exact xPlane_ne_zPerm h h3.symm
  · intro h1
    have h2 := congrArg Subtype.val h1
    change (e : Equiv.Perm (Fin 240)) * signPerm (vec2 0 2) * (e : Equiv.Perm (Fin 240))⁻¹ *
      (signPerm (vec2 0 2))⁻¹ = xPlane * zPerm at h2
    rw [h2] at hcl
    rcases (h.uArg.inf_uSub _ (mul_mem h.uArg.xPlane_mem h.uArg.zPerm_mem)).1 hcl with h3 | h3
    · exact xz_ne_one h h3
    · exact h.model.zPerm_ne_one (by simpa using h3)

end Bridge

end CFSG.EvenSmallLie.OmegaEight.Child8
