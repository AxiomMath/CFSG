module

public import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer2.L5FinInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5FinInputs
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Certificates.Certificate5072
public import Certificates.Certificate5092

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem imp_eq_true {a b : Bool} : imp a b = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp [imp]

theorem E5list_mul_chk :
    E5list.all (fun a => E5list.all fun b => decide (a * b ∈ E5list)) = true := by
  decide +kernel

theorem E5list_mul : ∀ a ∈ E5list, ∀ b ∈ E5list, a * b ∈ E5list := by
  have h := E5list_mul_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem E5list_inv_chk :
    E5list.all (fun a => decide (a⁻¹ ∈ E5list)) = true := by
  decide +kernel

theorem E5list_inv : ∀ a ∈ E5list, a⁻¹ ∈ E5list := by
  have h := E5list_inv_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

@[expose] def E5 : Subgroup (Amb 5) where
  carrier := {p | p ∈ E5list}
  one_mem' := by simp [E5list]
  mul_mem' := fun {a b} ha hb => E5list_mul a ha b hb
  inv_mem' := fun {a} ha => E5list_inv a ha

theorem mem_E5 {p : Amb 5} : p ∈ E5 ↔ p ∈ E5list := Iff.rfl

theorem E5list_T5_chk : E5list.all T5b = true := by
  decide +kernel

theorem E5list_T5 : ∀ p ∈ E5list, T5b p = true := by
  have h := E5list_T5_chk
  simpa only [List.all_eq_true] using h

theorem E5_le_T5
    : E5 ≤ T5 := fun p hp => mem_T5_of_b (E5list_T5 p (mem_E5.1 hp))

theorem E5_comm_chk :
    E5list.all (fun a => E5list.all fun b => decide (a * b = b * a)) = true := by
  decide +kernel

theorem E5_comm_aux : ∀ a ∈ E5list, ∀ b ∈ E5list, a * b = b * a := by
  have h := E5_comm_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem E5_comm : ∀ a ∈ E5, ∀ b ∈ E5, a * b = b * a :=
  fun a ha b hb => E5_comm_aux a (mem_E5.1 ha) b (mem_E5.1 hb)

theorem E5_sq_chk : E5list.all (fun a => decide (a * a = 1)) = true := by
  decide +kernel

theorem E5_sq_aux : ∀ a ∈ E5list, a * a = 1 := by
  have h := E5_sq_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem E5_sq : ∀ a ∈ E5, a * a = 1 := fun a ha => E5_sq_aux a (mem_E5.1 ha)

theorem E5list_nodup : E5list.Nodup := by
  decide +kernel

theorem card_E5 : Nat.card E5 = 8 := by
  rw [natCard_eq_length E5 E5list E5list_nodup (fun p => Iff.rfl)]
  rfl

theorem vhat5_mem_E5 : vhat5 ∈ E5 := by simp [mem_E5, E5list]

theorem f1_mem_E5 : f1 ∈ E5 := by simp [mem_E5, E5list]

theorem e1_mem_E5 : e1 ∈ E5 := by simp [mem_E5, E5list]

theorem T5_norm_E5_chk :
    allT5.all (fun t => E5list.all fun e => decide (t * e * t⁻¹ ∈ E5list)) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.1

theorem T5_norm_E5_aux :
    ∀ t ∈ allT5, ∀ e ∈ E5list, t * e * t⁻¹ ∈ E5list := by
  have h := T5_norm_E5_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem E5_norm
    {t : Amb 5} (ht : t ∈ T5) {e : Amb 5} (he : e ∈ E5) : t * e * t⁻¹ ∈ E5 :=
  mem_E5.2 (T5_norm_E5_aux t (mem_allT5.2 ht) e (mem_E5.1 he))

theorem centT_E5_chk :
    allT5.all (fun t => imp (E5list.all fun e => decide (t * e = e * t)) (decide (t ∈ E5list))) =
      true := by
  decide +kernel

theorem centT_E5_aux :
    ∀ t ∈ allT5, (∀ e ∈ E5list, t * e = e * t) → t ∈ E5list := by
  have h := centT_E5_chk
  simpa only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] using h

theorem centT_E5 {t : Amb 5} (ht : t ∈ T5) (hc : ∀ e ∈ E5, t * e = e * t) : t ∈ E5 :=
  mem_E5.2 (centT_E5_aux t (mem_allT5.2 ht) (fun e he => hc e (mem_E5.2 he)))


namespace FgrpFiveE8

section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem E5_le_Fgrp : E5 ≤ Fgrp 5 := E5_le_T5.trans T5_le_Fgrp

instance E5_isElementaryAbelian : CFSG.IsElementaryAbelian 2 E5 where
  is_comm := ⟨fun a b => Subtype.ext (E5_comm a a.2 b b.2)⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    apply Subtype.ext
    rw [pow_two]
    simpa using E5_sq a a.2

@[expose] def E5F : Subgroup (Fgrp 5) := E5.subgroupOf (Fgrp 5)

theorem card_E5F : Nat.card E5F = 8 := by
  change Nat.card (E5.subgroupOf (Fgrp 5)) = 8
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe E5_le_Fgrp).toEquiv, card_E5]

theorem E5F_comm : ∀ a ∈ E5F, ∀ b ∈ E5F, a * b = b * a := by
  intro a ha b hb
  apply Subtype.ext
  simpa using E5_comm a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb)

instance E5F_isElementaryAbelian : CFSG.IsElementaryAbelian 2 E5F :=
  CFSG.IsElementaryAbelian.subgroupOf (H := E5) (K := Fgrp 5) E5_le_Fgrp

theorem factorization_Fgrp5_two : (Nat.card (Fgrp 5)).factorization 2 = 5 := by
  rw [card_Fgrp_eq, Nat.factorization_def _ Nat.prime_two]
  decide +kernel

theorem card_T5_subgroupOf :
    Nat.card (T5.subgroupOf (Fgrp 5)) = 2 ^ (Nat.card (Fgrp 5)).factorization 2 := by
  rw [factorization_Fgrp5_two,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe T5_le_Fgrp).toEquiv, card_T5]
  norm_num

@[expose] noncomputable def T5sylow : Sylow 2 (Fgrp 5) :=
  Sylow.ofCard (T5.subgroupOf (Fgrp 5)) card_T5_subgroupOf

theorem T5sylow_map :
    ((T5sylow : Subgroup (Fgrp 5)).map (Fgrp 5).subtype) = T5 := by
  change (((Sylow.ofCard (T5.subgroupOf (Fgrp 5)) card_T5_subgroupOf :
    Sylow 2 (Fgrp 5)) : Subgroup (Fgrp 5)).map (Fgrp 5).subtype) = T5
  rw [Sylow.coe_ofCard]
  exact Subgroup.map_subgroupOf_eq_of_le T5_le_Fgrp

theorem mem_T5sylow {x : Fgrp 5} :
    x ∈ (T5sylow : Subgroup (Fgrp 5)) ↔ ((x : Fgrp 5) : Amb 5) ∈ T5 := by
  rw [← T5sylow_map]
  exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective (Fgrp 5))).symm

theorem T5sylow_isSylowOf : IsSylowOf 2 (T5sylow : Subgroup (Fgrp 5)) ⊤ := by
  rw [isSylowOf_iff]
  refine ⟨le_top, T5sylow.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact T5sylow.not_dvd_index

theorem E5F_le_T5sylow : E5F ≤ (T5sylow : Subgroup (Fgrp 5)) := by
  intro x hx
  rw [mem_T5sylow]
  exact E5_le_T5 (Subgroup.mem_subgroupOf.mp hx)

theorem E5F_cent {y : Fgrp 5} (hy : y ∈ (T5sylow : Subgroup (Fgrp 5)))
    (hc : ∀ a ∈ E5F, y * a = a * y) : y ∈ E5F := by
  rw [E5F, Subgroup.mem_subgroupOf]
  refine centT_E5 (mem_T5sylow.mp hy) ?_
  intro e he
  have hye : y * ⟨e, E5_le_Fgrp he⟩ = ⟨e, E5_le_Fgrp he⟩ * y :=
    hc ⟨e, E5_le_Fgrp he⟩ (Subgroup.mem_subgroupOf.mpr he)
  exact congrArg Subtype.val hye

theorem cent_T5_E5F :
    Subgroup.centralizer (E5F : Set (Fgrp 5)) ⊓ (T5sylow : Subgroup (Fgrp 5)) = E5F := by
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_inf] at hy
    exact E5F_cent hy.2 (fun a ha => (Subgroup.mem_centralizer_iff.mp hy.1 a ha).symm)
  · intro y hy
    rw [Subgroup.mem_inf]
    exact ⟨Subgroup.mem_centralizer_iff.mpr (fun a ha => E5F_comm a ha y hy),
      E5F_le_T5sylow hy⟩

theorem sylow_isSylowOf (T : Sylow 2 (Fgrp 5)) :
    IsSylowOf 2 (T : Subgroup (Fgrp 5)) ⊤ := by
  rw [isSylowOf_iff]
  refine ⟨le_top, T.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact T.not_dvd_index

theorem exists_isElementaryAbelian_eight_sylow (T : Sylow 2 (Fgrp 5)) :
    ∃ E : Subgroup (Fgrp 5), E ≤ (T : Subgroup (Fgrp 5)) ∧
      CFSG.IsElementaryAbelian 2 E ∧
      Nat.card E = 8 ∧
      Subgroup.centralizer (E : Set (Fgrp 5)) ⊓ (T : Subgroup (Fgrp 5)) = E := by
  obtain ⟨g, -, hconj⟩ := T5sylow_isSylowOf.exists_mem_conj (sylow_isSylowOf T)
  let E : Subgroup (Fgrp 5) := E5F.map (MulAut.conj g).toMonoidHom
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    change (g * x * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * x * g⁻¹)
    calc (g * x * g⁻¹) * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [E5F_comm x hx y hy]
      _ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
  have hET : E ≤ (T : Subgroup (Fgrp 5)) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxT5 : x ∈ (T5sylow : Subgroup (Fgrp 5)) := E5F_le_T5sylow hx
    have hyT : g * x * g⁻¹ ∈ (T : Subgroup (Fgrp 5)) := by
      exact (hconj (g * x * g⁻¹)).mpr (by
        have h : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rwa [h])
    simpa [MulAut.conj_apply] using hyT
  have hEcent : ∀ y ∈ (T : Subgroup (Fgrp 5)),
      (∀ a ∈ E, y * a = a * y) → y ∈ E := by
    intro y hy hc
    have hyT5 : g⁻¹ * y * g ∈ (T5sylow : Subgroup (Fgrp 5)) := (hconj y).mp hy
    have hcent : ∀ x ∈ E5F, (g⁻¹ * y * g) * x = x * (g⁻¹ * y * g) := by
      intro x hx
      have hxE : (MulAut.conj g) x ∈ E := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      have hcomm := hc ((MulAut.conj g) x) hxE
      rw [MulAut.conj_apply] at hcomm
      calc (g⁻¹ * y * g) * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hcomm]
        _ = x * (g⁻¹ * y * g) := by group
    have hxE5F : g⁻¹ * y * g ∈ E5F := E5F_cent hyT5 hcent
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * y * g, hxE5F, ?_⟩
    show g * (g⁻¹ * y * g) * g⁻¹ = y
    group
  have hcard : Nat.card E = 8 := by
    change Nat.card (E5F.map (MulAut.conj g).toMonoidHom) = 8
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_E5F]
  have hcent_eq : Subgroup.centralizer (E : Set (Fgrp 5)) ⊓
      (T : Subgroup (Fgrp 5)) = E := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_inf] at hy
      exact hEcent y hy.2 (fun a ha => (Subgroup.mem_centralizer_iff.mp hy.1 a ha).symm)
    · intro y hy
      rw [Subgroup.mem_inf]
      exact ⟨Subgroup.mem_centralizer_iff.mpr (fun a ha => hEcomm a ha y hy), hET hy⟩
  refine ⟨E, hET, ?_, hcard, hcent_eq⟩
  exact CFSG.IsElementaryAbelian.map (A := E5F) (f := (MulAut.conj g).toMonoidHom)

theorem exists_isElementaryAbelian_eight_of_isSylowOf {T : Subgroup (Fgrp 5)}
    (hT : IsSylowOf 2 T ⊤) :
    ∃ E : Subgroup (Fgrp 5), E ≤ T ∧
      CFSG.IsElementaryAbelian 2 E ∧
      Nat.card E = 8 ∧
      Subgroup.centralizer (E : Set (Fgrp 5)) ⊓ T = E := by
  have hcardT : Nat.card T = 2 ^ (Nat.card (Fgrp 5)).factorization 2 := by
    have h := hT.card_eq
    rwa [Nat.card_congr (Subgroup.topEquiv (G := Fgrp 5)).toEquiv] at h
  let Ts : Sylow 2 (Fgrp 5) := Sylow.ofCard T hcardT
  have hTs : (Ts : Subgroup (Fgrp 5)) = T := Sylow.coe_ofCard T hcardT
  obtain ⟨E, hET, hEab, hcard, hcent⟩ := exists_isElementaryAbelian_eight_sylow Ts
  refine ⟨E, ?_, hEab, hcard, ?_⟩
  · rwa [hTs] at hET
  · rwa [hTs] at hcent

theorem exists_selfCentralizing_e8_of_isSylowOf {T : Subgroup (Fgrp 5)}
    (hT : IsSylowOf 2 T ⊤) :
    ∃ E : Subgroup (Fgrp 5), E ≤ T ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a * a = 1) ∧
      Nat.card E = 8 ∧
      (∀ y ∈ T, (∀ a ∈ E, y * a = a * y) → y ∈ E) := by
  obtain ⟨E, hET, hEab, hcard, hcent⟩ :=
    exists_isElementaryAbelian_eight_of_isSylowOf hT
  refine ⟨E, hET, ?_, ?_, hcard, ?_⟩
  · intro a ha b hb
    exact congrArg Subtype.val (hEab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · intro a ha
    have hEab' : CFSG.IsElementaryAbelian 2 E := hEab
    simpa [pow_two] using CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  · intro y hy hc
    have hycent : y ∈ Subgroup.centralizer (E : Set (Fgrp 5)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (hc a ha).symm
    have hyinf : y ∈ Subgroup.centralizer (E : Set (Fgrp 5)) ⊓ T := ⟨hycent, hy⟩
    rwa [hcent] at hyinf

end

end FgrpFiveE8

theorem E5_char_chk :
    allT5.all (fun u => imp (decide (u * u = 1)) (imp (decide (u ≠ 1))
    (decide ((u ∈ E5list ∧ u ≠ vhat5) ↔ (nmE u = 4 ∧ nmE (u * vhat5) = 4))))) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.1

theorem E5_char_aux : ∀ u ∈ allT5, u * u = 1 → u ≠ 1 →
    ((u ∈ E5list ∧ u ≠ vhat5) ↔ (nmE u = 4 ∧ nmE (u * vhat5) = 4)) := by
  have h := E5_char_chk
  simpa only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] using h

theorem E5_char
    {u : Amb 5} (hu : u ∈ T5) (hsq : u * u = 1) (h1 : u ≠ 1) :
    (u ∈ E5 ∧ u ≠ vhat5) ↔ (nmE u = 4 ∧ nmE (u * vhat5) = 4) := by
  rw [mem_E5]
  exact E5_char_aux u (mem_allT5.2 hu) hsq h1

theorem mem_F5list {g : Amb 5} : g ∈ F5list ↔ g ∈ Fgrp 5 := by
  rw [F5list, List.mem_filter, mem_Fgrp5]
  simp only [decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨mem_allAmb5 g, h⟩⟩

theorem cent_vhat5_chk :
    F5list.all (fun g => imp (decide (g * vhat5 = vhat5 * g)) (T5b g)) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.1

theorem cent_vhat5_aux :
    ∀ g ∈ F5list, g * vhat5 = vhat5 * g → T5b g = true := by
  have h := cent_vhat5_chk
  simpa only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] using h

theorem cent_vhat5
    {g : Amb 5} (hg : g ∈ Fgrp 5) (hc : g * vhat5 = vhat5 * g) : g ∈ T5 :=
  mem_T5_of_b (cent_vhat5_aux g (mem_F5list.2 hg) hc)

theorem T5_comm_vhat5_chk :
    allT5.all (fun t => decide (t * vhat5 = vhat5 * t)) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.1

theorem T5_comm_vhat5_aux : ∀ t ∈ allT5, t * vhat5 = vhat5 * t := by
  have h := T5_comm_vhat5_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem T5_comm_vhat5
    {t : Amb 5} (ht : t ∈ T5) : t * vhat5 = vhat5 * t :=
  T5_comm_vhat5_aux t (mem_allT5.2 ht)

theorem Hgrp_vhat5 : Hgrp 5 vhat5 = T5 := by
  ext g
  rw [Hgrp, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hgF, hgc⟩
    exact cent_vhat5 hgF hgc
  · intro hg
    exact ⟨T5_le_Fgrp hg, T5_comm_vhat5 hg⟩

theorem sigma5_chk :
    allT5.all (fun s => imp (decide (s * s = 1)) (imp (decide (s ≠ 1))
    (imp (decide (nmE s = 8)) (imp (decide (nmE (f1 * s) = 4))
      (F5list.any fun g => decide (g * s * g⁻¹ = vhat5)))))) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.1

theorem sigma5_aux :
    ∀ s ∈ allT5, s * s = 1 → s ≠ 1 → nmE s = 8 → nmE (f1 * s) = 4 →
    ∃ g ∈ F5list, g * s * g⁻¹ = vhat5 := by
  have h := sigma5_chk
  simpa only [List.all_eq_true, List.any_eq_true, imp_eq_true, decide_eq_true_eq] using h

theorem sigma5
    {s : Amb 5} (hs : s ∈ T5) (hsq : s * s = 1) (h1 : s ≠ 1) (h8 : nmE s = 8)
    (h4 : nmE (f1 * s) = 4) : ∃ g ∈ Fgrp 5, g * s * g⁻¹ = vhat5 := by
  obtain ⟨g, hg, hgs⟩ := sigma5_aux s (mem_allT5.2 hs) hsq h1 h8 h4
  exact ⟨g, mem_F5list.1 hg, hgs⟩

theorem nmE_vhat5 : nmE vhat5 = 8 :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem vhat5_sq : vhat5 * vhat5 = 1 :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem vhat5_ne_one : vhat5 ≠ 1 :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem vhat5_mem_T5 : vhat5 ∈ T5 := E5_le_T5 vhat5_mem_E5

theorem mem_R5list {s : Perm (Fin 9)} : s ∈ R5list ↔ s ∈ R5 := by
  rw [R5list, List.mem_map, mem_R5]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, mem_allT5.1 ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, mem_allT5.2 ht, rfl⟩

theorem S0_inv_chk :
    S0l.all (fun s => imp (decide (s * s = 1)) (imp (decide (s ≠ 1))
    (imp (decide (s ∉ R5list)) (decide (numMoved s = 8))))) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem S0_inv_aux :
    ∀ s ∈ S0l, s * s = 1 → s ≠ 1 → s ∉ R5list → numMoved s = 8 := by
  have h := S0_inv_chk
  simpa only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] using h

theorem S0_inv_nm8
    {s : Perm (Fin 9)} (hs : s ∈ S0) (hsq : s * s = 1) (h1 : s ≠ 1)
    (hR : s ∉ R5) : numMoved s = 8 :=
  S0_inv_aux s (mem_S0l.2 hs) hsq h1 (fun h => hR (mem_R5list.1 h))

theorem Z_S0_chk :
    S0l.all (fun s => imp (S0l.all fun t => decide (s * t = t * s))
    (decide (s = 1 ∨ s = yS))) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Z_S0_aux :
    ∀ s ∈ S0l, (∀ t ∈ S0l, s * t = t * s) → s = 1 ∨ s = yS := by
  have h := Z_S0_chk
  simpa only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] using h

theorem Z_S0
    {s : Perm (Fin 9)} (hs : s ∈ S0) (hc : ∀ t ∈ S0, s * t = t * s) :
    s = 1 ∨ s = yS :=
  Z_S0_aux s (mem_S0l.2 hs) (fun t ht => hc t (mem_S0l.1 ht))

theorem yS_mem_R5 : yS ∈ R5 := mem_R5.2 ⟨vhat5, vhat5_mem_T5, rfl⟩

theorem yS_mem_S0 : yS ∈ S0 := R5_le_S0 yS_mem_R5

theorem yS_sq : yS * yS = 1 :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem yS_ne_one : yS ≠ 1 :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem numMoved_yS : numMoved yS = 8 :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem yS_central_chk :
    S0l.all (fun t => decide (t * yS = yS * t)) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem yS_central
    {s : Perm (Fin 9)} (hs : s ∈ S0) : s * yS = yS * s := by
  have h := yS_central_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h s (mem_S0l.2 hs)

@[expose] def E9 : Subgroup (Perm (Fin 9)) := E5.map (emb 5)

theorem mem_E9
    {s : Perm (Fin 9)} : s ∈ E9 ↔ ∃ e ∈ E5, emb 5 e = s := by
  simp only [E9, Subgroup.mem_map]

theorem mem_E9l {s : Perm (Fin 9)} : s ∈ E9l ↔ s ∈ E9 := by
  rw [E9l, List.mem_map, mem_E9]
  rfl

theorem card_E9 : Nat.card E9 = 8 := by
  rw [E9, Subgroup.card_map_of_injective (emb_injective 5), card_E5]

theorem E9_le_R5 : E9 ≤ R5 := by
  rintro _ ⟨e, he, rfl⟩
  exact mem_R5.2 ⟨e, E5_le_T5 he, rfl⟩

theorem E9_le_S0 : E9 ≤ S0 := E9_le_R5.trans R5_le_S0

theorem yS_mem_E9 : yS ∈ E9 := ⟨vhat5, vhat5_mem_E5, rfl⟩

theorem emb_f1_mem_E9 : emb 5 f1 ∈ E9 := ⟨f1, f1_mem_E5, rfl⟩

theorem E9_comm_chk :
    E9l.all (fun a => E9l.all fun b => decide (a * b = b * a)) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem E9_comm_aux : ∀ a ∈ E9l, ∀ b ∈ E9l, a * b = b * a := by
  have h := E9_comm_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem E9_comm : ∀ a ∈ E9, ∀ b ∈ E9, a * b = b * a :=
  fun a ha b hb => E9_comm_aux a (mem_E9l.2 ha) b (mem_E9l.2 hb)

theorem E9_sq_chk :
    E9l.all (fun a => decide (a * a = 1)) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem E9_sq_aux : ∀ a ∈ E9l, a * a = 1 := by
  have h := E9_sq_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem E9_sq :
    ∀ a ∈ E9, a * a = 1 := fun a ha => E9_sq_aux a (mem_E9l.2 ha)

theorem S0_norm_E9_chk :
    S0l.all (fun s => E9l.all fun e => decide (s * e * s⁻¹ ∈ E9l)) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem S0_norm_E9_aux :
    ∀ s ∈ S0l, ∀ e ∈ E9l, s * e * s⁻¹ ∈ E9l := by
  have h := S0_norm_E9_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem S0_norm_E9
    {s : Perm (Fin 9)} (hs : s ∈ S0) {e : Perm (Fin 9)} (he : e ∈ E9) :
    s * e * s⁻¹ ∈ E9 :=
  mem_E9l.1 (S0_norm_E9_aux s (mem_S0l.2 hs) e (mem_E9l.2 he))

theorem E9_char_chk :
    S0l.all (fun u => imp (decide (u * u = 1)) (imp (decide (u ≠ 1))
    (decide ((u ∈ E9l ∧ u ≠ yS) ↔ (numMoved u = 4 ∧ numMoved (u * yS) = 4))))) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem E9_char_aux : ∀ u ∈ S0l, u * u = 1 → u ≠ 1 →
    ((u ∈ E9l ∧ u ≠ yS) ↔ (numMoved u = 4 ∧ numMoved (u * yS) = 4)) := by
  have h := E9_char_chk
  simpa only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] using h

theorem E9_char
    {u : Perm (Fin 9)} (hu : u ∈ S0) (hsq : u * u = 1) (h1 : u ≠ 1) :
    (u ∈ E9 ∧ u ≠ yS) ↔ (numMoved u = 4 ∧ numMoved (u * yS) = 4) := by
  have h := E9_char_aux u (mem_S0l.2 hu) hsq h1
  rw [mem_E9l] at h
  exact h

theorem Rc9list_mul_chk :
    Rc9list.all (fun a => Rc9list.all fun b => decide (a * b ∈ Rc9list)) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Rc9list_mul :
    ∀ a ∈ Rc9list, ∀ b ∈ Rc9list, a * b ∈ Rc9list := by
  have h := Rc9list_mul_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem Rc9list_inv_chk :
    Rc9list.all (fun a => decide (a⁻¹ ∈ Rc9list)) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Rc9list_inv : ∀ a ∈ Rc9list, a⁻¹ ∈ Rc9list := by
  have h := Rc9list_inv_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

@[expose] def Rc9 : Subgroup (Perm (Fin 9)) where
  carrier := {p | p ∈ Rc9list}
  one_mem' := by simp [Rc9list]
  mul_mem' := fun {a b} ha hb => Rc9list_mul a ha b hb
  inv_mem' := fun {a} ha => Rc9list_inv a ha

theorem mem_Rc9 {p : Perm (Fin 9)} : p ∈ Rc9 ↔ p ∈ Rc9list := Iff.rfl

theorem Rc9list_S0_chk :
    Rc9list.all (fun p => decide (p ∈ S0l)) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Rc9list_S0 : ∀ p ∈ Rc9list, p ∈ S0l := by
  have h := Rc9list_S0_chk
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem Rc9_le_S0 :
    Rc9 ≤ S0 := fun p hp => mem_S0l.1 (Rc9list_S0 p hp)

theorem Rc9_inter_chk :
    Rc9list.all (fun r => imp (decide (r ∈ E9l)) (decide (r = 1))) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Rc9_inter_aux : ∀ r ∈ Rc9list, r ∈ E9l → r = 1 := by
  have h := Rc9_inter_chk
  simpa only [List.all_eq_true, imp_eq_true, decide_eq_true_eq] using h

theorem E9_inf_Rc9 : E9 ⊓ Rc9 = ⊥ := by
  rw [eq_bot_iff]
  rintro r ⟨hE, hR⟩
  exact Subgroup.mem_bot.2 (Rc9_inter_aux r hR (mem_E9l.2 hE))

theorem S0_split_chk :
    S0l.all (fun s => E9l.any fun e => Rc9list.any fun r =>
    decide (s = e * r)) = true :=
  Certificates.certificate5072.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem S0_split_aux :
    ∀ s ∈ S0l, ∃ e ∈ E9l, ∃ r ∈ Rc9list, s = e * r := by
  have h := S0_split_chk
  simpa only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] using h

theorem E9_sup_Rc9 :
    E9 ⊔ Rc9 = S0 := by
  apply le_antisymm (sup_le E9_le_S0 Rc9_le_S0)
  intro s hs
  obtain ⟨e, he, r, hr, rfl⟩ := S0_split_aux s (mem_S0l.2 hs)
  exact mul_mem (mem_sup_left (mem_E9l.1 he)) (mem_sup_right hr)

end CFSG.GH74.GLS.C3.Layer2.L5
