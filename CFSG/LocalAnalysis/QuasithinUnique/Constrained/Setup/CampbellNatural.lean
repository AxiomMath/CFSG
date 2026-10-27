module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSL2
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Matrix Module CFSG.SL2MinimalFaithful
open scoped LinearAlgebra.Projectivization Pointwise

section NatPlane

variable {k : Type*} [Field k] {E : Type*} [CommGroup E]

@[expose] def actDiff (act : SpecialLinearGroup (Fin 2) k →* MulAut E)
    (a : SpecialLinearGroup (Fin 2) k) : E →* E where
  toFun e := act a e * e⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem actDiff_apply (act : SpecialLinearGroup (Fin 2) k →* MulAut E)
    (a : SpecialLinearGroup (Fin 2) k) (e : E) : actDiff act a e = act a e * e⁻¹ := rfl

@[expose] def fixedSub (act : SpecialLinearGroup (Fin 2) k →* MulAut E)
    (S : Set (SpecialLinearGroup (Fin 2) k)) : Subgroup E where
  carrier := {e | ∀ a ∈ S, act a e = e}
  one_mem' := fun a _ => map_one _
  mul_mem' := fun ha hb a hS => by rw [map_mul, ha a hS, hb a hS]
  inv_mem' := fun ha a hS => by rw [map_inv, ha a hS]

theorem mem_fixedSub {act : SpecialLinearGroup (Fin 2) k →* MulAut E}
    {S : Set (SpecialLinearGroup (Fin 2) k)} {e : E} :
    e ∈ fixedSub act S ↔ ∀ a ∈ S, act a e = e := Iff.rfl

@[expose] def commSub (act : SpecialLinearGroup (Fin 2) k →* MulAut E)
    (S : Set (SpecialLinearGroup (Fin 2) k)) (X : Subgroup E) : Subgroup E :=
  Subgroup.closure {x | ∃ a ∈ S, ∃ e ∈ X, x = act a e * e⁻¹}

@[expose] def lineMult (p : ℙ k (Fin 2 → k)) : Subgroup (Multiplicative (Fin 2 → k)) where
  carrier := {x | Multiplicative.toAdd x ∈ p.submodule}
  one_mem' := p.submodule.zero_mem
  mul_mem' := fun ha hb => p.submodule.add_mem ha hb
  inv_mem' := fun ha => p.submodule.neg_mem ha

theorem mem_lineMult {p : ℙ k (Fin 2 → k)} {x : Multiplicative (Fin 2 → k)} :
    x ∈ lineMult p ↔ Multiplicative.toAdd x ∈ p.submodule := Iff.rfl

structure IsNatPlane (act : SpecialLinearGroup (Fin 2) k →* MulAut E)
    (φ : E →* Multiplicative (Fin 2 → k)) : Prop where
  exp_two : ∀ e : E, e * e = 1
  surj : Function.Surjective φ
  equiv : ∀ (g : SpecialLinearGroup (Fin 2) k) (e : E),
    φ (act g e) = Multiplicative.ofAdd (g • Multiplicative.toAdd (φ e))
  ker_fixed : ∀ (g : SpecialLinearGroup (Fin 2) k), ∀ e ∈ φ.ker, act g e = e

@[expose] def natAct (g : SpecialLinearGroup (Fin 2) k) : MulAut (Multiplicative (Fin 2 → k)) where
  toFun x := Multiplicative.ofAdd (g • Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (g⁻¹ • Multiplicative.toAdd x)
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by
    simp [smul_add]

theorem lift_mul {E V : Type*} [CommGroup E] [CommGroup V] (hE : ∀ e : E, e * e = 1)
    (b : MulAut E) (hb : ∀ e, b (b e) = e) (φ : E →* V) (hφ : Function.Surjective φ)
    (c : MulAut V) (hbc : ∀ e, φ (b e) = c (φ e)) (hker : ∀ z ∈ φ.ker, b z = z) {e : E}
    (he : ∃ v : V, φ e = c v * v⁻¹) : b e = e := by
  obtain ⟨v, hv⟩ := he
  obtain ⟨x, rfl⟩ := hφ v
  set d : E := b x * x⁻¹ with hd
  have hφd : φ d = φ e := by
    rw [hd, map_mul, map_inv, hbc, hv]
  have hz : e * d⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφd, mul_inv_cancel]
  have hbz : b (e * d⁻¹) = e * d⁻¹ := hker _ hz
  have hdd : d⁻¹ = d := by
    rw [inv_eq_iff_mul_eq_one]; exact hE d
  have hbd : b d = d⁻¹ := by
    rw [hd, map_mul, map_inv, hb, mul_inv, inv_inv, mul_comm]
  have : b e = e := by
    have h1 : b e = b (e * d⁻¹) * b d := by
      rw [← map_mul, inv_mul_cancel_right]
    rw [h1, hbz, hbd, hdd, mul_assoc, hE d, mul_one]
  exact this


namespace IsNatPlane

variable {act : SpecialLinearGroup (Fin 2) k →* MulAut E} {φ : E →* Multiplicative (Fin 2 → k)}

theorem toAdd_smul_eq (h : IsNatPlane act φ) (g : SpecialLinearGroup (Fin 2) k) (e : E) :
    Multiplicative.toAdd (φ (act g e)) = g • Multiplicative.toAdd (φ e) := by
  rw [h.equiv]; rfl

theorem fixedSub_univ (h : IsNatPlane act φ) : fixedSub act Set.univ = φ.ker := by
  ext e
  constructor
  · intro he
    rw [MonoidHom.mem_ker]
    have hfix : ∀ g : SpecialLinearGroup (Fin 2) k,
        g • Multiplicative.toAdd (φ e) = Multiplicative.toAdd (φ e) := by
      intro g
      rw [← h.toAdd_smul_eq g e, he g (Set.mem_univ g)]
    have h0 := eq_zero_of_forall_smul_eq hfix
    exact Multiplicative.toAdd.injective (by simpa using h0)
  · intro he a _
    exact h.ker_fixed a e he

theorem act_mul_self [CharP k 2] (act : SpecialLinearGroup (Fin 2) k →* MulAut E)
    {p : ℙ k (Fin 2 → k)} {t : SpecialLinearGroup (Fin 2) k} (ht : t ∈ rootGrp p) (e : E) :
    act t (act t e) = e := by
  have : act t (act t e) = act (t * t) e := by rw [map_mul]; rfl
  rw [this, mul_self_eq_one_of_mem_rootGrp ht, map_one]; rfl

theorem mem_fixedSub_rootGrp_iff [CharP k 2] [Finite k] (h : IsNatPlane act φ)
    (p : ℙ k (Fin 2 → k)) (e : E) :
    e ∈ fixedSub act (rootGrp p : Set (SpecialLinearGroup (Fin 2) k)) ↔ φ e ∈ lineMult p := by
  constructor
  · intro he
    obtain ⟨t, ht, ht1⟩ := exists_ne_one_mem_rootGrp p
    have h3 : t • Multiplicative.toAdd (φ e) = Multiplicative.toAdd (φ e) := by
      rw [← h.toAdd_smul_eq t e, he t ht]
    exact (smul_eq_self_iff_mem_of_mem_rootGrp ht ht1 _).mp h3
  · intro hφe t ht
    by_cases ht1 : t = 1
    · rw [ht1]; simp
    · refine lift_mul h.exp_two (act t) (fun e => act_mul_self act ht e) φ h.surj (natAct t)
        (fun e => h.equiv t e) (fun z hz => h.ker_fixed t z hz) ?_
      obtain ⟨w, hw⟩ := exists_smul_sub_eq ht ht1 (mem_lineMult.mp hφe)
      refine ⟨Multiplicative.ofAdd w, ?_⟩
      apply Multiplicative.toAdd.injective
      simp [natAct]
      rw [← sub_eq_add_neg]
      exact hw.symm

theorem fixedSub_rootGrp_eq [CharP k 2] [Finite k] (h : IsNatPlane act φ) (p : ℙ k (Fin 2 → k)) :
    fixedSub act (rootGrp p : Set (SpecialLinearGroup (Fin 2) k)) = (lineMult p).comap φ := by
  ext e
  rw [Subgroup.mem_comap]
  exact h.mem_fixedSub_rootGrp_iff p e

theorem fixedSub_singleton_eq [CharP k 2] [Finite k] (h : IsNatPlane act φ) {p : ℙ k (Fin 2 → k)}
    {t : SpecialLinearGroup (Fin 2) k} (ht : t ∈ rootGrp p) (ht1 : t ≠ 1) :
    fixedSub act ({t} : Set (SpecialLinearGroup (Fin 2) k)) =
      fixedSub act (rootGrp p : Set (SpecialLinearGroup (Fin 2) k)) := by
  ext e
  rw [h.mem_fixedSub_rootGrp_iff p e, mem_fixedSub]
  constructor
  · intro he
    have h3 : t • Multiplicative.toAdd (φ e) = Multiplicative.toAdd (φ e) := by
      rw [← h.toAdd_smul_eq t e, he t rfl]
    exact (smul_eq_self_iff_mem_of_mem_rootGrp ht ht1 _).mp h3
  · intro hφe a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact (h.mem_fixedSub_rootGrp_iff p e).mpr hφe a ht


theorem toAdd_actDiff (h : IsNatPlane act φ) (t : SpecialLinearGroup (Fin 2) k) (e : E) :
    Multiplicative.toAdd (φ (actDiff act t e)) =
      t • Multiplicative.toAdd (φ e) - Multiplicative.toAdd (φ e) := by
  rw [actDiff_apply, map_mul, map_inv, toAdd_mul, toAdd_inv, h.toAdd_smul_eq]
  abel

theorem ker_actDiff (t : SpecialLinearGroup (Fin 2) k) :
    (actDiff act t).ker = fixedSub act ({t} : Set (SpecialLinearGroup (Fin 2) k)) := by
  ext e
  rw [MonoidHom.mem_ker, actDiff_apply, mul_inv_eq_one, mem_fixedSub]
  constructor
  · intro h a ha; rw [Set.mem_singleton_iff] at ha; rw [ha]; exact h
  · intro h; exact h t rfl

theorem map_range_actDiff [CharP k 2] [Finite k] (h : IsNatPlane act φ) {p : ℙ k (Fin 2 → k)}
    {t : SpecialLinearGroup (Fin 2) k} (ht : t ∈ rootGrp p) (ht1 : t ≠ 1) :
    (actDiff act t).range.map φ = lineMult p := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, ⟨e, rfl⟩, rfl⟩
    rw [mem_lineMult, h.toAdd_actDiff]
    exact (mem_rootGrp.mp ht) _
  · intro hx
    obtain ⟨w, hw⟩ := exists_smul_sub_eq ht ht1 (mem_lineMult.mp hx)
    obtain ⟨e, he⟩ := h.surj (Multiplicative.ofAdd w)
    refine ⟨actDiff act t e, ⟨e, rfl⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [h.toAdd_actDiff, he, toAdd_ofAdd, hw]

theorem card_lineMult [Finite k] (p : ℙ k (Fin 2 → k)) : Nat.card (lineMult p) = Nat.card k := by
  rw [← card_submodule_line p]
  exact Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, x.2⟩
      invFun := fun w => ⟨Multiplicative.ofAdd w.1, w.2⟩
      left_inv := fun x => rfl
      right_inv := fun w => rfl }

theorem index_lineMult [Finite k] (p : ℙ k (Fin 2 → k)) : (lineMult p).index = Nat.card k := by
  have h1 := (lineMult p).index_mul_card
  have h2 : Nat.card (Multiplicative (Fin 2 → k)) = Nat.card k ^ 2 := by
    rw [← card_fin_two_pi]; exact Nat.card_congr Multiplicative.toAdd
  rw [card_lineMult, h2] at h1
  have hq : 0 < Nat.card k := Nat.card_pos
  have : (lineMult p).index * Nat.card k = Nat.card k * Nat.card k := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hq this

theorem index_fixedSub_rootGrp [CharP k 2] [Finite k] (h : IsNatPlane act φ)
    (p : ℙ k (Fin 2 → k)) : (fixedSub act (rootGrp p : Set (SpecialLinearGroup (Fin 2) k))).index =
      Nat.card k := by
  rw [h.fixedSub_rootGrp_eq p, Subgroup.index_comap_of_surjective _ h.surj, index_lineMult]

theorem card_range_actDiff [CharP k 2] [Finite k] [Finite E] (h : IsNatPlane act φ)
    {p : ℙ k (Fin 2 → k)} {t : SpecialLinearGroup (Fin 2) k} (ht : t ∈ rootGrp p) (ht1 : t ≠ 1) :
    Nat.card (actDiff act t).range = Nat.card k := by
  have h1 : Nat.card (E ⧸ (actDiff act t).ker) = Nat.card (actDiff act t).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (actDiff act t)).toEquiv
  rw [← h1, ker_actDiff, h.fixedSub_singleton_eq ht ht1, ← Subgroup.index]
  exact h.index_fixedSub_rootGrp p

theorem range_actDiff_inf_ker [CharP k 2] [Finite k] [Finite E] (h : IsNatPlane act φ)
    {p : ℙ k (Fin 2 → k)} {t : SpecialLinearGroup (Fin 2) k} (ht : t ∈ rootGrp p) (ht1 : t ≠ 1) :
    (actDiff act t).range ⊓ φ.ker = ⊥ := by
  set R := (actDiff act t).range with hR
  let f : R →* Multiplicative (Fin 2 → k) := φ.comp R.subtype
  have hfr : f.range = lineMult p := by
    have : f.range = R.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this, hR, h.map_range_actDiff ht ht1]
  have hcard : Nat.card f.range = Nat.card R := by
    rw [hfr, card_lineMult, hR, h.card_range_actDiff ht ht1]
  have hker : Nat.card f.ker = 1 := by
    have h1 := Subgroup.card_mul_index f.ker
    have h2 : f.ker.index = Nat.card f.range :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv)
    rw [h2, hcard] at h1
    have hpos : 0 < Nat.card R := Nat.card_pos
    have : Nat.card f.ker * Nat.card R = 1 * Nat.card R := by rw [h1, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rw [eq_bot_iff]
  intro x ⟨hxR, hxk⟩
  have hf1 : (⟨x, hxR⟩ : R) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    exact hxk
  have hbot : f.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ hker
  rw [hbot, Subgroup.mem_bot] at hf1
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hf1)

theorem fixedSub_rootGrp_eq_sup [CharP k 2] [Finite k] (h : IsNatPlane act φ)
    {p : ℙ k (Fin 2 → k)} {t : SpecialLinearGroup (Fin 2) k} (ht : t ∈ rootGrp p) (ht1 : t ≠ 1) :
    fixedSub act (rootGrp p : Set (SpecialLinearGroup (Fin 2) k)) = (actDiff act t).range ⊔ φ.ker := by
  apply le_antisymm
  · intro x hx
    rw [h.fixedSub_rootGrp_eq p, Subgroup.mem_comap] at hx
    have hx' : φ x ∈ (actDiff act t).range.map φ := by rw [h.map_range_actDiff ht ht1]; exact hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    have : x = y * (y⁻¹ * x) := by group
    rw [this]
    refine mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right ?_)
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  · refine sup_le ?_ ?_
    · rintro _ ⟨e, rfl⟩
      rw [h.fixedSub_rootGrp_eq p, Subgroup.mem_comap, mem_lineMult, h.toAdd_actDiff]
      exact (mem_rootGrp.mp ht) _
    · intro x hx
      rw [h.fixedSub_rootGrp_eq p, Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
      exact one_mem _


theorem lineMult_inf {p m : ℙ k (Fin 2 → k)} (h : p ≠ m) : lineMult p ⊓ lineMult m = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hp, hm⟩
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  simpa using submodule_inf_eq_bot h (mem_lineMult.mp hp) (mem_lineMult.mp hm)

@[expose] def dispSub (act : SpecialLinearGroup (Fin 2) k →* MulAut E) (X : Subgroup E) :
    Subgroup (SpecialLinearGroup (Fin 2) k) where
  carrier := {g | ∀ x : E, act g x * x⁻¹ ∈ X}
  one_mem' := fun x => by simp
  mul_mem' := fun {a b} ha hb x => by
    have : act (a * b) x * x⁻¹ = (act a (act b x) * (act b x)⁻¹) * (act b x * x⁻¹) := by
      rw [map_mul, MulAut.mul_apply]; group
    rw [this]
    exact mul_mem (ha _) (hb _)
  inv_mem' := fun {a} ha x => by
    have hy : act a (act a⁻¹ x) = x := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    have : act a⁻¹ x * x⁻¹ = (act a (act a⁻¹ x) * (act a⁻¹ x)⁻¹)⁻¹ := by
      rw [hy]; group
    rw [this]
    exact inv_mem (ha _)

theorem commSub_univ_le_sup (hEL : commSub act Set.univ ⊤ = ⊤) (p m : ℙ k (Fin 2 → k))
    (hpm : p ≠ m) :
    commSub act (rootGrp p : Set _) ⊤ ⊔ commSub act (rootGrp m : Set _) ⊤ = ⊤ := by
  set X := commSub act (rootGrp p : Set _) ⊤ ⊔ commSub act (rootGrp m : Set _) ⊤ with hX
  have hp : rootGrp p ≤ dispSub act X := fun a ha x =>
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨a, ha, x, Subgroup.mem_top x, rfl⟩)
  have hm : rootGrp m ≤ dispSub act X := fun a ha x =>
    Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, ha, x, Subgroup.mem_top x, rfl⟩)
  have htop : dispSub act X = ⊤ := by
    rw [eq_top_iff, ← rootGrp_sup_rootGrp hpm]
    exact sup_le hp hm
  rw [eq_top_iff, ← hEL]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨a, -, e, -, rfl⟩
  have : a ∈ dispSub act X := htop ▸ Subgroup.mem_top a
  exact this e

theorem commSub_le_comap (h : IsNatPlane act φ) (q : ℙ k (Fin 2 → k)) :
    commSub act (rootGrp q : Set _) ⊤ ≤ (lineMult q).comap φ := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨a, ha, e, -, rfl⟩
  show φ (act a e * e⁻¹) ∈ lineMult q
  rw [mem_lineMult, map_mul, map_inv, toAdd_mul, toAdd_inv, h.toAdd_smul_eq]
  have := (mem_rootGrp.mp ha) (Multiplicative.toAdd (φ e))
  simpa [sub_eq_add_neg] using this

omit [Field k] in
theorem act_inv_act' {k : Type*} [Field k] (act : SpecialLinearGroup (Fin 2) k →* MulAut E)
    (g : SpecialLinearGroup (Fin 2) k) (e : E) : act (g⁻¹) (act g e) = e := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem act_act_inv' {k : Type*} [Field k] (act : SpecialLinearGroup (Fin 2) k →* MulAut E)
    (g : SpecialLinearGroup (Fin 2) k) (e : E) : act g (act (g⁻¹) e) = e := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl

theorem act_mul' {k : Type*} [Field k] (act : SpecialLinearGroup (Fin 2) k →* MulAut E)
    (x y : SpecialLinearGroup (Fin 2) k) (e : E) : act (x * y) e = act x (act y e) := by
  rw [map_mul]; rfl

theorem act_conj_displ {k : Type*} [Field k] (act : SpecialLinearGroup (Fin 2) k →* MulAut E)
    (g a : SpecialLinearGroup (Fin 2) k) (e : E) :
    act g (act a e * e⁻¹) = act (g * a * g⁻¹) (act g e) * (act g e)⁻¹ := by
  rw [act_mul', act_mul', act_inv_act', map_mul, map_inv]

theorem commSub_smul (g : SpecialLinearGroup (Fin 2) k) (p : ℙ k (Fin 2 → k)) :
    commSub act (rootGrp (g • p) : Set _) ⊤ = (commSub act (rootGrp p : Set _) ⊤).map
      (act g).toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a', ha', e, -, rfl⟩
    have ha : g⁻¹ * a' * g ∈ rootGrp p := mem_rootGrp_smul_iff.mp ha'
    refine ⟨act (g⁻¹ * a' * g) (act (g⁻¹) e) * (act (g⁻¹) e)⁻¹,
      ⟨g⁻¹ * a' * g, ha, act (g⁻¹) e, Subgroup.mem_top _, rfl⟩, ?_⟩
    show act g (act (g⁻¹ * a' * g) (act (g⁻¹) e) * (act (g⁻¹) e)⁻¹) = act a' e * e⁻¹
    rw [act_conj_displ, act_act_inv']
    have : g * (g⁻¹ * a' * g) * g⁻¹ = a' := by group
    rw [this]
  · rintro ⟨_, ⟨a, ha, e, -, rfl⟩, rfl⟩
    refine ⟨g * a * g⁻¹, ?_, act g e, Subgroup.mem_top _, ?_⟩
    · have e : g⁻¹ * (g * a * g⁻¹) * g = a := by group
      refine mem_rootGrp_smul_iff.mpr ?_
      rw [e]; exact ha
    · exact act_conj_displ act g a e


theorem ker_inf_commSub_eq (h : IsNatPlane act φ) (g : SpecialLinearGroup (Fin 2) k)
    (p : ℙ k (Fin 2 → k)) :
    commSub act (rootGrp p : Set _) ⊤ ⊓ φ.ker = commSub act (rootGrp (g • p) : Set _) ⊤ ⊓ φ.ker := by
  rw [commSub_smul]
  ext x
  constructor
  · rintro ⟨hxA, hxk⟩
    exact ⟨⟨x, hxA, h.ker_fixed g x hxk⟩, hxk⟩
  · rintro ⟨⟨y, hy, rfl⟩, hxk⟩
    refine ⟨?_, hxk⟩
    have h1 : act (g⁻¹) (act g y) = y := act_inv_act' act g y
    have h2 : act (g⁻¹) (act g y) = act g y := h.ker_fixed (g⁻¹) _ hxk
    have : act g y = y := by rw [← h2, h1]
    show act g y ∈ commSub act (rootGrp p : Set _) ⊤
    rw [this]; exact hy

theorem ker_le_commSub [CharP k 2] [Finite k] (h : IsNatPlane act φ)
    (hEL : commSub act Set.univ ⊤ = ⊤) (p : ℙ k (Fin 2 → k)) :
    φ.ker ≤ commSub act (rootGrp p : Set _) ⊤ := by
  obtain ⟨m, hm⟩ := exists_ne_point p
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) k) p m
  subst hg
  set A := commSub act (rootGrp p : Set _) ⊤ with hA
  set B := commSub act (rootGrp (g • p) : Set _) ⊤ with hB
  have hAB : A ⊔ B = ⊤ := commSub_univ_le_sup hEL p (g • p) hm.symm
  intro c hc
  have hc' : c ∈ A ⊔ B := hAB ▸ Subgroup.mem_top c
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hc'
  have h1 : φ a * φ b = 1 := by rw [← map_mul, hab]; exact hc
  have hAφ : φ a ∈ lineMult p := commSub_le_comap h p ha
  have hBφ : φ b ∈ lineMult (g • p) := commSub_le_comap h (g • p) hb
  have hbinv : φ a = (φ b)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have ha1 : φ a = 1 := by
    have hBφ' : (φ b)⁻¹ ∈ lineMult (g • p) := (lineMult (g • p)).inv_mem hBφ
    have : φ a ∈ lineMult p ⊓ lineMult (g • p) := ⟨hAφ, by rw [hbinv]; exact hBφ'⟩
    rw [lineMult_inf hm.symm, Subgroup.mem_bot] at this
    exact this
  have hb1 : φ b = 1 := by rw [ha1, one_mul] at h1; exact h1
  have hbA : b ∈ A := by
    have : b ∈ A ⊓ φ.ker := by
      rw [ker_inf_commSub_eq h g p]; exact ⟨hb, hb1⟩
    exact this.1
  rw [← hab]
  exact mul_mem ha hbA

theorem commSub_rootGrp_eq [CharP k 2] [Finite k] (h : IsNatPlane act φ)
    (hEL : commSub act Set.univ ⊤ = ⊤) (p : ℙ k (Fin 2 → k)) :
    commSub act (rootGrp p : Set _) ⊤ = (lineMult p).comap φ := by
  apply le_antisymm (commSub_le_comap h p)
  intro x hx
  obtain ⟨t, ht, ht1⟩ := exists_ne_one_mem_rootGrp p
  have hx' : φ x ∈ (actDiff act t).range.map φ := by
    rw [h.map_range_actDiff ht ht1]; exact hx
  obtain ⟨y, ⟨e, rfl⟩, hyx⟩ := Subgroup.mem_map.mp hx'
  have hyA : actDiff act t e ∈ commSub act (rootGrp p : Set _) ⊤ :=
    Subgroup.subset_closure ⟨t, ht, e, Subgroup.mem_top e, rfl⟩
  have hker : (actDiff act t e)⁻¹ * x ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  have : x = actDiff act t e * ((actDiff act t e)⁻¹ * x) := by group
  rw [this]
  exact mul_mem hyA (ker_le_commSub h hEL p hker)

theorem commSub_commSub_eq_bot [CharP k 2] [Finite k] (h : IsNatPlane act φ)
    (hEL : commSub act Set.univ ⊤ = ⊤) (p : ℙ k (Fin 2 → k)) :
    commSub act (rootGrp p : Set _) (commSub act (rootGrp p : Set _) ⊤) = ⊥ := by
  rw [commSub_rootGrp_eq h hEL p]
  rw [eq_bot_iff]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨a, ha, e, he, rfl⟩
  have : e ∈ fixedSub act (rootGrp p : Set (SpecialLinearGroup (Fin 2) k)) := by
    rw [h.fixedSub_rootGrp_eq p]; exact he
  show act a e * e⁻¹ ∈ (⊥ : Subgroup E)
  rw [Subgroup.mem_bot, this a ha, mul_inv_cancel]

theorem ker_eq_bot_of_card_two [CharP k 2] [Finite k] [Finite E] (h : IsNatPlane act φ)
    (hEL : commSub act Set.univ ⊤ = ⊤) (hq : Nat.card k = 2) : φ.ker = ⊥ := by
  obtain ⟨t, ht, ht1⟩ := exists_ne_one_mem_rootGrp (pt0 : ℙ k (Fin 2 → k))
  have hcard : Nat.card (rootGrp (pt0 : ℙ k (Fin 2 → k))) = 2 := (card_rootGrp _).trans hq
  have hall : ∀ a ∈ rootGrp (pt0 : ℙ k (Fin 2 → k)), a = 1 ∨ a = t := by
    intro a ha
    by_cases ha1 : a = 1
    · left; exact ha1
    · right
      obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : rootGrp (pt0 : ℙ k (Fin 2 → k)))).mp hcard
      have h1 := huniq ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
      have h2 := huniq ⟨t, ht⟩ (fun h => ht1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (h1.trans h2.symm)
  have hcomm : commSub act (rootGrp (pt0 : ℙ k (Fin 2 → k)) : Set _) ⊤ ≤ (actDiff act t).range := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨a, ha, e, -, rfl⟩
    rcases hall a ha with rfl | rfl
    · exact ⟨1, by simp [actDiff_apply]⟩
    · exact ⟨e, rfl⟩
  have hker := ker_le_commSub h hEL (pt0 : ℙ k (Fin 2 → k))
  have hinf := h.range_actDiff_inf_ker ht ht1
  rw [eq_bot_iff, ← hinf]
  exact fun x hx => ⟨hcomm (hker hx), hx⟩

theorem stabilizer_eq_rootGrp [CharP k 2] [Finite k] (h : IsNatPlane act φ) (e : E)
    (hw : Multiplicative.toAdd (φ e) ≠ 0) (g : SpecialLinearGroup (Fin 2) k) :
    act g e = e ↔ g ∈ rootGrp (Projectivization.mk k (Multiplicative.toAdd (φ e)) hw) := by
  constructor
  · intro hg
    refine mem_rootGrp_mk_of_smul_eq hw ?_
    rw [← h.toAdd_smul_eq, hg]
  · intro hg
    have : e ∈ fixedSub act (rootGrp (Projectivization.mk k (Multiplicative.toAdd (φ e)) hw) :
        Set (SpecialLinearGroup (Fin 2) k)) := by
      rw [h.mem_fixedSub_rootGrp_iff]
      rw [mem_lineMult, Projectivization.submodule_mk]
      exact Submodule.mem_span_singleton_self _
    exact this g hg

end IsNatPlane


theorem saturated_natural_plane_root_fixed_space [Finite k] [Finite E] {n : ℕ} (hn : 1 ≤ n)
    (hk : Nat.card k = 2 ^ n) {act : SpecialLinearGroup (Fin 2) k →* MulAut E}
    {φ : E →* Multiplicative (Fin 2 → k)} (h : IsNatPlane act φ)
    (hEL : commSub act Set.univ ⊤ = ⊤) :
    φ.ker = fixedSub act Set.univ ∧
    ∀ p : ℙ k (Fin 2 → k),
      fixedSub act (rootGrp p : Set (SpecialLinearGroup (Fin 2) k)) = (lineMult p).comap φ ∧
      (lineMult p).comap φ = commSub act (rootGrp p : Set (SpecialLinearGroup (Fin 2) k)) ⊤ ∧
      commSub act (rootGrp p : Set (SpecialLinearGroup (Fin 2) k))
        (commSub act (rootGrp p : Set (SpecialLinearGroup (Fin 2) k)) ⊤) = ⊥ ∧
      (∀ t ∈ rootGrp p, t ≠ 1 →
        fixedSub act ({t} : Set (SpecialLinearGroup (Fin 2) k)) =
          fixedSub act (rootGrp p : Set (SpecialLinearGroup (Fin 2) k)) ∧
        (fixedSub act (rootGrp p : Set (SpecialLinearGroup (Fin 2) k))).index = Nat.card k ∧
        fixedSub act (rootGrp p : Set (SpecialLinearGroup (Fin 2) k)) =
          (actDiff act t).range ⊔ φ.ker ∧ (actDiff act t).range ⊓ φ.ker = ⊥) ∧
      (Nat.card k = 2 → φ.ker = ⊥) ∧
      (∀ e : E, ∀ hw : Multiplicative.toAdd (φ e) ≠ 0, ∀ g : SpecialLinearGroup (Fin 2) k,
        act g e = e ↔ g ∈ rootGrp (Projectivization.mk k (Multiplicative.toAdd (φ e)) hw)) := by
  have : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hk
  refine ⟨(h.fixedSub_univ).symm, fun p => ⟨h.fixedSub_rootGrp_eq p,
    (IsNatPlane.commSub_rootGrp_eq h hEL p).symm, IsNatPlane.commSub_commSub_eq_bot h hEL p,
    fun t ht ht1 => ⟨h.fixedSub_singleton_eq ht ht1, h.index_fixedSub_rootGrp p,
      h.fixedSub_rootGrp_eq_sup ht ht1, h.range_actDiff_inf_ker ht ht1⟩,
    IsNatPlane.ker_eq_bot_of_card_two h hEL, fun e hw g => h.stabilizer_eq_rootGrp e hw g⟩⟩

end NatPlane

end CFSG.QuasithinUnique.Setup.Campbell
