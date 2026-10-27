module

public import CFSG.Goldschmidt.Steps.G211
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma38Core
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.ComponentClassification.Asc75Lemma31

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.Goldschmidt.G2
open scoped Pointwise commutatorElement

section Defs

variable {G : Type*} [Group G]

abbrev fixGrp (V : Subgroup G) (y : G) : Subgroup G := V ⊓ centralizer ({y} : Set G)

abbrev comGrp (V : Subgroup G) (y : G) : Subgroup G := ⁅V, zpowers y⁆

end Defs

variable {G : Type} [Group G] [Finite G]

structure Hyp (V X : Subgroup G) (y : G) : Prop where
  elem : IsElemAbelian 2 V
  le : X ≤ normalizer (V : Set G)
  mem : y ∈ X
  odd : Odd (orderOf y)
  not_mem : y ∉ centralizer (V : Set G)
  ne_bot : V ⊓ centralizer ({y} : Set G) ≠ ⊥
  trans : ∀ b ∈ ⁅V, zpowers y⁆, ∀ c ∈ ⁅V, zpowers y⁆, b ≠ 1 → c ≠ 1 →
    ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c
  ti : ∀ x ∈ X, conjSub x (V ⊓ centralizer ({y} : Set G)) ≠ V ⊓ centralizer ({y} : Set G) →
    V ⊓ centralizer ({y} : Set G) ⊓ conjSub x (V ⊓ centralizer ({y} : Set G)) = ⊥

namespace Hyp

variable {V X : Subgroup G} {y : G} (h : Hyp V X y)
include h

omit [Finite G] in
theorem onanHyp (hirr : ∀ M : Subgroup G, M ≤ V → X ≤ normalizer (M : Set G) → M = ⊥ ∨ M = V) :
    ONanHyp V X y :=
  ⟨h.elem, h.le, hirr, h.mem, h.odd, h.not_mem, h.ne_bot, h.trans, h.ti⟩

omit [Finite G] in
theorem comGrp_le : comGrp V y ≤ V := by
  rw [comGrp, commutator_le]
  intro v hv z hz
  have hzV : z ∈ normalizer (V : Set G) := h.le ((zpowers_le.mpr h.mem) hz)
  rw [commutatorElement_def]
  have h1 : z * v⁻¹ * z⁻¹ ∈ V := (mem_normalizer_iff.mp hzV v⁻¹).mp (inv_mem hv)
  simpa [mul_assoc] using mul_mem hv h1

omit [Finite G] in
theorem conj_mem_comGrp {w z : G} (hw : w ∈ comGrp V y) (hz : z ∈ zpowers y) :
    z⁻¹ * w * z ∈ comGrp V y := by
  have hzV : z ∈ normalizer (V : Set G) := h.le ((zpowers_le.mpr h.mem) hz)
  have heq : conjSub z (comGrp V y) = comGrp V y := by
    rw [comGrp, conjSub, map_commutator]
    change ⁅conjSub z V, conjSub z (zpowers y)⁆ = _
    rw [conjSub_eq_of_mem_normalizer hzV,
      conjSub_eq_of_mem_normalizer (le_normalizer hz)]
  have h1 := conj_mem_conjSub (g := z) hw
  rwa [heq] at h1

section Linear

variable [Fact (IsElemAbelian 2 V)]

theorem linHyp : LinHyp (conjRep h.le).range (conjRep h.le ⟨y, h.mem⟩) where
  mem := ⟨⟨y, h.mem⟩, rfl⟩
  odd := by
    have h1 : orderOf (conjRep h.le ⟨y, h.mem⟩) ∣ orderOf (⟨y, h.mem⟩ : X) := orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat h.odd h1
  ne_one := by
    rw [Ne, conjRep_eq_one_iff]
    exact h.not_mem
  fixSp_ne_bot := by
    rw [fixSp_conjRep, Ne, sub_eq_bot_iff]
    exact h.ne_bot
  trans := by
    intro b hb c hc hb0 hc0
    have hb' := comSp_le_sub h.le _ hb
    have hc' := comSp_le_sub h.le _ hc
    rw [mem_sub] at hb' hc'
    have hb1 : ((Additive.toMul b : V) : G) ≠ 1 := fun h1 => hb0 (by
      apply Additive.toMul.injective
      exact Subtype.ext h1)
    have hc1 : ((Additive.toMul c : V) : G) ≠ 1 := fun h1 => hc0 (by
      apply Additive.toMul.injective
      exact Subtype.ext h1)
    obtain ⟨k, hk⟩ := h.trans _ hb' _ hc' hb1 hc1
    have h1 : (conjRep h.le ⟨y, h.mem⟩ ^ k)⁻¹ b = c := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [← conjRep_pow, conjRep_inv_apply]
      simpa using hk
    obtain ⟨k', hk'⟩ := exists_pow_eq_of_mem_zpowers
      (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers (conjRep h.le ⟨y, h.mem⟩) k))
    exact ⟨k', by rw [hk']; exact h1⟩
  ti := by
    rintro _ ⟨x, rfl⟩ hne
    rw [fixSp_conjRep, conjRep_smul_sub] at hne ⊢
    rw [← G2.sub_inf, sub_eq_bot_iff]
    rw [Ne, sub_eq_sub_iff] at hne
    have hxA : conjSub (x : G)⁻¹ V = V := conjSub_eq_of_mem_normalizer (h.le (X.inv_mem x.2))
    have hne' : conjSub (x : G)⁻¹ (V ⊓ centralizer ({y} : Set G)) ≠
        V ⊓ centralizer ({y} : Set G) := by
      rwa [conjSub_inf, hxA]
    have := h.ti _ (X.inv_mem x.2) hne'
    rw [conjSub_inf, hxA] at this
    rw [← this]
    ext g
    simp only [Subgroup.mem_inf]
    tauto

theorem sub_comGrp : sub V (comGrp V y) = comSp (conjRep h.le ⟨y, h.mem⟩) := by
  refine le_antisymm (fun v hv => ?_) (comSp_le_sub h.le _)
  set η := conjRep h.le ⟨y, h.mem⟩
  have hL := h.linHyp
  have hle : comGrp V y ≤ subOf (comSp η) := by
    rw [comGrp, commutator_le]
    intro a ha z hz
    have hzX : z ∈ X := (zpowers_le.mpr h.mem) hz
    have hzη : conjRep h.le ⟨z, hzX⟩ ∈ zpowers η := by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz
      have : (⟨y ^ j, hzX⟩ : X) = (⟨y, h.mem⟩ : X) ^ j := Subtype.ext (by simp)
      rw [this, map_zpow]
      exact zpow_mem_zpowers η j
    have hmem := hL.sub_mem_comSp hzη (Additive.ofMul ⟨a, ha⟩)
    have hcV : ⁅a, z⁆ ∈ V := by
      rw [commutatorElement_def]
      have h1 : z * a⁻¹ * z⁻¹ ∈ V :=
        (mem_normalizer_iff.mp (h.le hzX) a⁻¹).mp (inv_mem ha)
      simpa [mul_assoc] using mul_mem ha h1
    have hval : Additive.ofMul (⟨⁅a, z⁆, hcV⟩ : V) =
        -((conjRep h.le ⟨z, hzX⟩) (Additive.ofMul ⟨a, ha⟩) - Additive.ofMul ⟨a, ha⟩) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [neg_sub, toMul_sub, Subgroup.coe_div, div_eq_mul_inv, conjRep_apply]
      simp only [toMul_ofMul, commutatorElement_def]
      group
    exact ⟨hcV, hval ▸ (comSp η).neg_mem hmem⟩
  have hv' := mem_sub.mp hv
  exact (mem_iff_mem_subOf v).mpr (hle hv')

end Linear

theorem inf_eq_bot : fixGrp V y ⊓ comGrp V y = ⊥ := by
  have : Fact (IsElemAbelian 2 V) := ⟨h.elem⟩
  have hc := h.linHyp.isCompl.inf_eq_bot
  rw [← h.sub_comGrp, fixSp_conjRep, ← G2.sub_inf, sub_eq_bot_iff] at hc
  rw [fixGrp, inf_assoc, inf_comm (centralizer _), hc]

theorem exists_mul {v : G} (hv : v ∈ V) : ∃ u ∈ fixGrp V y, ∃ w ∈ comGrp V y, v = u * w := by
  have : Fact (IsElemAbelian 2 V) := ⟨h.elem⟩
  obtain ⟨d, hd, f, hf, hdf⟩ := h.linHyp.exists_add (Additive.ofMul (⟨v, hv⟩ : V))
  rw [← h.sub_comGrp, mem_sub] at hd
  rw [fixSp_conjRep, mem_sub] at hf
  refine ⟨_, ⟨(Additive.toMul f : V).2, hf⟩, _, hd, ?_⟩
  have h1 := congrArg (fun x : Additive V => ((Additive.toMul x : V) : G)) hdf
  simp only [toMul_add, Subgroup.coe_mul, toMul_ofMul] at h1
  rw [← h1]
  exact congrArg Subtype.val (mul_comm (Additive.toMul d) (Additive.toMul f))

theorem sup_eq : fixGrp V y ⊔ comGrp V y = V := by
  refine le_antisymm (sup_le inf_le_left h.comGrp_le) fun v hv => ?_
  obtain ⟨u, hu, w, hw, rfl⟩ := h.exists_mul hv
  exact mul_mem (mem_sup_left hu) (mem_sup_right hw)

end Hyp

omit [Finite G] in
theorem le_normalizer_of_le {p : ℕ} {V A B : Subgroup G} (hV : IsElemAbelian p V) (hA : A ≤ V)
    (hB : B ≤ V) : B ≤ normalizer (A : Set G) := by
  intro b hb
  have hbV := hB hb
  have hcomm : ∀ a ∈ V, b * a * b⁻¹ = a := fun a ha => by
    have hc : b * a = a * b := congrArg Subtype.val (hV.1.is_comm.comm ⟨b, hbV⟩ ⟨a, ha⟩)
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [hcomm a (hA ha)]
    exact ha
  · intro ha
    have haV : a ∈ V := by
      have h1 := mul_mem (mul_mem (inv_mem hbV) (hA ha)) hbV
      simpa [mul_assoc] using h1
    rwa [hcomm a haV] at ha

namespace Hyp

variable {V X : Subgroup G} {y : G} (h : Hyp V X y)
include h

theorem card_eq : Nat.card V = Nat.card (fixGrp V y) * Nat.card (comGrp V y) := by
  rw [← AS76b.card_sup_eq_mul (le_normalizer_of_le h.elem inf_le_left h.comGrp_le) h.inf_eq_bot,
    h.sup_eq]

theorem mem_centralizer_of_conj_eq {z w : G} (hz : z ∈ zpowers y) (hw : w ∈ comGrp V y)
    (hw1 : w ≠ 1) (hzw : z⁻¹ * w * z = w) : z ∈ centralizer (V : Set G) := by
  have : Fact (IsElemAbelian 2 V) := ⟨h.elem⟩
  have hzX : z ∈ X := (zpowers_le.mpr h.mem) hz
  set η := conjRep h.le ⟨y, h.mem⟩
  have hzη : conjRep h.le ⟨z, hzX⟩ ∈ zpowers η := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz
    have : (⟨y ^ j, hzX⟩ : X) = (⟨y, h.mem⟩ : X) ^ j := Subtype.ext (by simp)
    rw [this, map_zpow]
    exact zpow_mem_zpowers η j
  have hwV : w ∈ V := h.comGrp_le hw
  have hd : Additive.ofMul (⟨w, hwV⟩ : V) ∈ comSp η := by
    rw [← h.sub_comGrp, mem_sub]
    exact hw
  have hd0 : Additive.ofMul (⟨w, hwV⟩ : V) ≠ 0 := fun h0 =>
    hw1 (congrArg Subtype.val (ofMul_eq_zero.mp h0))
  have hfix : conjRep h.le ⟨z, hzX⟩ (Additive.ofMul (⟨w, hwV⟩ : V)) =
      Additive.ofMul (⟨w, hwV⟩ : V) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [conjRep_apply]
    simp only [toMul_ofMul]
    calc z * w * z⁻¹ = z * (z⁻¹ * w * z) * z⁻¹ := by rw [hzw]
      _ = w := by group
  rw [← conjRep_eq_one_iff h.le ⟨z, hzX⟩]
  exact h.linHyp.eq_one_of_apply_eq hzη hd hd0 hfix

end Hyp

theorem card_mul_le {ι : Type*} [Finite ι] {V W : Subgroup G} (hWV : W ≤ V)
    (H : ι → Subgroup G) (hti : ∀ i j, i ≠ j → H i ⊓ H j = ⊥) (hV : ∀ i, H i ≤ V)
    (hW : ∀ i, H i ⊓ W = ⊥) {c : ℕ} (hc : ∀ i, Nat.card (H i) = c) :
    Nat.card ι * (c - 1) ≤ Nat.card V - Nat.card W ∧
      (Nat.card ι * (c - 1) = Nat.card V - Nat.card W →
        ∀ v ∈ V, v ∉ W → ∃ i, v ∈ H i) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fintype ι := Fintype.ofFinite ι
  rw [Nat.card_eq_fintype_card (α := ι)]
  have hcard : ∀ K : Subgroup G, (Finset.univ.filter (· ∈ K)).card = Nat.card K := by
    intro K
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let t : ι → Finset G := fun i => Finset.univ.filter (fun g => g ∈ H i ∧ g ≠ 1)
  let D : Finset G := Finset.univ.filter (fun g => g ∈ V ∧ g ∉ W)
  have ht : ∀ i, (t i).card = c - 1 := by
    intro i
    have h1 : t i = (Finset.univ.filter (· ∈ H i)).erase 1 := by
      ext g
      simp [t, and_comm]
    rw [h1, Finset.card_erase_of_mem (by simp [one_mem]), hcard, hc]
  have hD : D.card = Nat.card V - Nat.card W := by
    have h1 : D = Finset.univ.filter (· ∈ V) \ Finset.univ.filter (· ∈ W) := by
      ext g
      simp [D]
    rw [h1, Finset.card_sdiff, Finset.inter_eq_left.mpr (fun g hg => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      exact hWV hg), hcard, hcard]
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint t := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro g hgi hgj
    simp only [Finset.mem_filter, t] at hgi hgj
    have : g ∈ H i ⊓ H j := ⟨hgi.2.1, hgj.2.1⟩
    rw [hti i j hij, mem_bot] at this
    exact hgi.2.2 this
  have hsub : Finset.univ.biUnion t ⊆ D := by
    intro g hg
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, t] at hg
    obtain ⟨i, hgi, hg1⟩ := hg
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hV i hgi, fun hgW => hg1 ?_⟩
    have : g ∈ H i ⊓ W := ⟨hgi, hgW⟩
    rwa [hW i, mem_bot] at this
  have hU : (Finset.univ.biUnion t).card = Fintype.card ι * (c - 1) := by
    rw [Finset.card_biUnion hdisj]
    simp [ht]
  refine ⟨hU ▸ hD ▸ Finset.card_le_card hsub, fun heq v hv hvW => ?_⟩
  have hEq : Finset.univ.biUnion t = D :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hU, hD, heq])
  have hvD : v ∈ D := by simp [D, hv, hvW]
  rw [← hEq] at hvD
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, t] at hvD
  obtain ⟨i, hvi, -⟩ := hvD
  exact ⟨i, hvi⟩

end CFSG.ComponentClassification.Asc75Lemma31
