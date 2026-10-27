
module

public import CFSG.Certificates.Kernel.TabBThreeL1.LevelsSound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeALocalBase
public import Certificates.Certificate17579
public import Certificates.Certificate17580
public import Certificates.Certificate17581
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Orb

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

open CFSG.Monster.B.Classical.E6Adjoint CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Fischer
open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std CFSG.Monster.B.E6.StdF4
open CFSG.LieType.Chevalley.C2E6Overlap (K barHom)

theorem ch17575_lev_zero : ∀ m : Fin 78, lev m = 0 → (m : ℕ) = 77 := by decide +kernel

theorem ch17575_orbs_facts : ∀ o ∈ orbs, 6 ≤ o.1 ∧ o.1 < 78 ∧ 6 ≤ o.2 ∧ o.2 < 78 ∧
    3 ≤ lev o.1 ∧ 3 ≤ lev o.2 := by
  decide +kernel

@[expose] def ch17575KSel : List ℕ := [75, 73, 70, 65, 66, 59, 60, 52, 56, 43, 47, 36, 25, 14, 0]

theorem ch17575_kSel_facts : ∀ j : Fin 15, j ≠ 14 →
    ch17575KSel.getD j 0 < 78 ∧ lev (ch17575KSel.getD j 0) = 1 ∧
      (brMask (orbAt j).1 77).testBit (ch17575KSel.getD j 0) = true ∧
      ∀ j' : Fin 15, (j' ≠ j → (brMask (orbAt j').1 77).testBit (ch17575KSel.getD j 0) = false) ∧
        ((orbAt j').1 ≠ (orbAt j').2 →
          (brMask (orbAt j').2 77).testBit (ch17575KSel.getD j 0) = false) := by
  decide +kernel

theorem ch17575_testB_facts : ∀ β ∈ testB, β < 78 ∧ lev β = 2 ∧ brMask 76 β = 0 ∧
    brMask 77 β = 0 ∧ fbit 76 β = false ∧ fbit 77 β = false := by
  decide +kernel

theorem ch17575_lev_negTheta : lev 77 = 0 := by decide +kernel

theorem ch17575_single_eq_eLab (a : Fin 78) :
    (Finsupp.single (lab a) 1 : RootModule Tag.E6 K) = eLab K a := rfl

theorem ch17575_pinnedX_apply {a : Fin 78} (ha : 6 ≤ (a : ℕ)) (d : K) (w : RootModule Tag.E6 K)
    (c : Fin 78) :
    ((pinnedX Tag.E6 K (labRoot a) d : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) w
        (lab c) =
      w (lab c) + d * (∑ k : Fin 78, if (brMask a k).testBit c then w (lab k) else 0) +
        if a = c then d ^ 2 * form K (eLab K a) w else 0 := by
  rw [labRoot, pinnedX_eq (isRoot_certRoot (by omega)), rootOp_apply, rootVec_lab ha,
    ch17575_single_eq_eLab, Finsupp.add_apply, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.smul_apply, Finsupp.smul_apply, ch17575_bracket_apply, ch17575_eLab_apply, smul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  split_ifs <;> ring

theorem ch17575_brMask_lev_of
    (hgr : ∀ a b c : Fin 78, bracket K (eLab K a) (eLab K b) (lab c) ≠ 0 →
      lev a + lev b = lev c + 2)
    {a b c : Fin 78} (h : (brMask a b).testBit c = true) : lev a + lev b = lev c + 2 :=
  hgr a b c (by
    rw [eLab, eLab, bracket_lab, ch17575_toVec_apply, if_pos h]
    exact one_ne_zero)

section Grading

variable (hgr : ∀ a b c : Fin 78, bracket K (eLab K a) (eLab K b) (lab c) ≠ 0 →
  lev a + lev b = lev c + 2)
include hgr

theorem ch17575_step {a : Fin 78} (ha : 6 ≤ (a : ℕ)) (hla : 3 ≤ lev a) (d : K)
    (w : RootModule Tag.E6 K) :
    ((pinnedX Tag.E6 K (labRoot a) d : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) w
        (lab 77) = w (lab 77) ∧
      ∀ k : Fin 78, lev k = 1 →
        ((pinnedX Tag.E6 K (labRoot a) d : ModGL Tag.E6 K) :
          Module.End K (RootModule Tag.E6 K)) w (lab k) =
          w (lab k) + d * if (brMask a 77).testBit k then w (lab 77) else 0 := by
  have h77 : lev 77 = 0 := ch17575_lev_negTheta
  refine ⟨?_, fun k hk => ?_⟩
  · rw [ch17575_pinnedX_apply ha, if_neg (fun h => by
      rw [h] at hla
      change 3 ≤ lev 77 at hla
      omega), add_zero, Finset.sum_eq_zero, mul_zero, add_zero]
    intro m _
    rw [if_neg]
    intro hb
    have := ch17575_brMask_lev_of hgr hb
    change lev a + lev m = lev 77 + 2 at this
    omega
  · rw [ch17575_pinnedX_apply ha, if_neg (fun h => by
      rw [h, hk] at hla
      omega), add_zero, Finset.sum_eq_single (77 : Fin 78)]
    · rfl
    · intro m _ hm
      rw [if_neg]
      intro hb
      have := ch17575_brMask_lev_of hgr hb
      exact hm (Fin.ext (ch17575_lev_zero m (by omega)))
    · simp

@[expose] noncomputable def ch17575Contrib (p : (ℕ × ℕ) × F4) (k : ℕ) : K :=
  toK p.2 * (if (brMask p.1.1 77).testBit k then 1 else 0) +
    if p.1.1 = p.1.2 then 0 else toK (p.2 * p.2) * (if (brMask p.1.2 77).testBit k then 1 else 0)

theorem ch17575_prod_apply : ∀ P : List ((ℕ × ℕ) × F4), (∀ p ∈ P, p.1 ∈ orbs) →
    (((P.map fun p => yElt p.1 p.2).prod : ModGL Tag.E6 K) :
      Module.End K (RootModule Tag.E6 K)) (eLab K 77) (lab 77) = 1 ∧
    ∀ k : Fin 78, lev k = 1 →
      (((P.map fun p => yElt p.1 p.2).prod : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) (eLab K 77) (lab k) =
        (P.map fun p => ch17575Contrib p k).sum
  | [], _ => by
    refine ⟨?_, fun k hk => ?_⟩
    · simp [ch17575_eLab_apply]
    · have hne : (77 : Fin 78) ≠ k := fun h => by
        rw [← h] at hk
        exact absurd hk (by decide)
      simp [ch17575_eLab_apply, hne]
  | p :: P, hP => by
    obtain ⟨h1, h1', h2, h2', l1, l2⟩ := ch17575_orbs_facts p.1 (hP p List.mem_cons_self)
    obtain ⟨ih77, ih⟩ := ch17575_prod_apply P fun q hq => hP q (List.mem_cons_of_mem _ hq)
    set w := (((P.map fun p => yElt p.1 p.2).prod : ModGL Tag.E6 K) :
      Module.End K (RootModule Tag.E6 K)) (eLab K 77) with hw
    have s1 := ch17575_step hgr (a := ⟨p.1.1, h1'⟩) h1 l1
    have s2 := ch17575_step hgr (a := ⟨p.1.2, h2'⟩) h2 l2
    rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, ← hw]
    by_cases ho : p.1.1 = p.1.2
    · rw [yElt, if_pos ho]
      refine ⟨(s1 _ w).1.trans ih77, fun k hk => ?_⟩
      rw [List.map_cons, List.sum_cons, (s1 _ w).2 k hk, ih k hk, ih77, ch17575Contrib, if_pos ho]
      split_ifs <;> simp [add_comm]
    · rw [yElt, if_neg ho, Units.val_mul, Module.End.mul_apply]
      refine ⟨((s1 _ _).1.trans (s2 _ w).1).trans ih77, fun k hk => ?_⟩
      rw [List.map_cons, List.sum_cons, (s1 _ _).2 k hk, (s2 _ w).2 k hk, (s2 _ w).1, ih k hk, ih77,
        ch17575Contrib, if_neg ho]
      split_ifs <;> simp only [mul_one, mul_zero, add_zero, zero_add] <;> ring

end Grading

theorem ch17575_prod_ofFn_last {G : Type*} [Monoid G] :
    ∀ (n : ℕ) (f : Fin (n + 1) → G), (∀ i : Fin (n + 1), i ≠ Fin.last n → f i = 1) →
      (List.ofFn f).prod = f (Fin.last n)
  | 0, f, _ => by simp
  | n + 1, f, h => by
    rw [List.ofFn_succ, List.prod_cons, h 0 (fun e => by simp [Fin.ext_iff] at e), one_mul,
      ch17575_prod_ofFn_last n (fun i => f i.succ) (fun i hi => h _ (fun e => hi (by
        rw [← Fin.succ_last] at e
        exact Fin.succ_injective _ e)))]
    rfl

@[expose] noncomputable def ch17575Proj1 (y : RootModule Tag.E6 K) : RootModule Tag.E6 K :=
  ∑ m : Fin 78, (if lev m = 1 then y (lab m) else 0) • eLab K m

theorem ch17575_proj1_apply (y : RootModule Tag.E6 K) (k : Fin 78) :
    ch17575Proj1 y (lab k) = if lev k = 1 then y (lab k) else 0 := by
  rw [ch17575Proj1, Finsupp.finset_sum_apply, Finset.sum_eq_single k]
  · rw [Finsupp.smul_apply, ch17575_eLab_apply, if_pos rfl, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [Finsupp.smul_apply, ch17575_eLab_apply, if_neg hj, smul_zero]
  · simp

theorem ch17575_lev1_eq_zero
    (hgr : ∀ a b c : Fin 78, bracket K (eLab K a) (eLab K b) (lab c) ≠ 0 →
      lev a + lev b = lev c + 2)
    (hsq : ∀ β k : Fin 78, (β : ℕ) ∈ testB → lev k = 1 →
      bracket K (eLab K β) (bracket K (eLab K β) (eLab K k)) = 0)
    (hker : ∀ y : RootModule Tag.E6 K, (∀ k : Fin 78, lev k ≠ 1 → y (lab k) = 0) →
      (∀ β : Fin 78, (β : ℕ) ∈ testB → bracket K (eLab K β) y = 0) → y = 0)
    (e : RootModule Tag.E6 K)
    (hβ : ∀ β : Fin 78, (β : ℕ) ∈ testB → ∀ k : Fin 78, lev k = 1 →
      bracket K (eLab K β) e (lab k) + form K (eLab K β) e * e (lab k) = 0) :
    ∀ k : Fin 78, lev k = 1 → e (lab k) = 0 := by
  set y := ch17575Proj1 e with hydef
  have hy : ∀ k : Fin 78, lev k ≠ 1 → y (lab k) = 0 := fun k hk => by
    rw [hydef, ch17575_proj1_apply, if_neg hk]
  have hbr : ∀ β : Fin 78, (β : ℕ) ∈ testB →
      bracket K (eLab K β) y = form K (eLab K β) e • y := by
    intro β hβB
    have hlβ : lev β = 2 := (ch17575_testB_facts β hβB).2.1
    refine ch17575_ext fun k => ?_
    rw [ch17575_bracket_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hk : lev k = 1
    · have hs : (∑ m : Fin 78, if (brMask β m).testBit k then y (lab m) else 0) =
          bracket K (eLab K β) e (lab k) := by
        rw [ch17575_bracket_apply]
        refine Finset.sum_congr rfl fun m _ => ?_
        split_ifs with hb
        · have := ch17575_brMask_lev_of hgr hb
          rw [hydef, ch17575_proj1_apply, if_pos (by omega)]
        · rfl
      rw [hs, hydef, ch17575_proj1_apply, if_pos hk, eq_neg_of_add_eq_zero_left (hβ β hβB k hk),
        CharTwo.neg_eq]
    · rw [hy k hk, mul_zero]
      refine Finset.sum_eq_zero fun m _ => ?_
      split_ifs with hb
      · have := ch17575_brMask_lev_of hgr hb
        exact hy m (by omega)
      · rfl
  have hsq' : ∀ β : Fin 78, (β : ℕ) ∈ testB → bracket K (eLab K β) (bracket K (eLab K β) y) = 0 := by
    intro β hβB
    rw [hydef, ch17575Proj1, map_sum, map_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [map_smul, map_smul]
    split_ifs with hm
    · rw [hsq β m hβB hm, smul_zero]
    · rw [zero_smul]
  have hor : ∀ β : Fin 78, (β : ℕ) ∈ testB → y = 0 ∨ bracket K (eLab K β) y = 0 := by
    intro β hβB
    have h := hsq' β hβB
    rw [hbr β hβB, map_smul, hbr β hβB, smul_smul] at h
    rcases smul_eq_zero.1 h with hs | hs
    · right
      rw [hbr β hβB, mul_self_eq_zero.1 hs, zero_smul]
    · left
      exact hs
  have hy0 : y = 0 := by
    by_contra hne
    exact hne (hker y hy fun β hβB => (hor β hβB).resolve_left hne)
  intro k hk
  have := congrArg (fun v => v (lab k)) hy0
  simp only [Finsupp.zero_apply] at this
  rw [hydef, ch17575_proj1_apply, if_pos hk] at this
  exact this

theorem ch17575_rootVec_theta : rootVec Tag.E6 K theta = eLab K 76 := by
  have h := rootVec_lab (a := ⟨76, by norm_num⟩) (by norm_num)
  rw [show e6Certificate.root (((⟨76, by norm_num⟩ : Fin 78) : ℕ) - 6) = theta from
    root_seventy] at h
  exact h

theorem ch17575_rootVec_negTheta : rootVec Tag.E6 K (-theta) = eLab K 77 := by
  have h := rootVec_lab (a := ⟨77, by norm_num⟩) (by norm_num)
  rw [show e6Certificate.root (((⟨77, by norm_num⟩ : Fin 78) : ℕ) - 6) = -theta from
    root_seventyOne] at h
  exact h

theorem ch17575_yElt_zero {o : ℕ × ℕ} : yElt o 0 = 1 := by
  have h0 : toK (0 * 0) = 0 := by rw [mul_zero, toK_zero]
  rw [yElt]
  split_ifs
  · rw [toK_zero, pinnedX_zero]
  · rw [toK_zero, h0, pinnedX_zero, one_mul, pinnedX_zero]

theorem ch17575_z_apply (y : RootModule Tag.E6 K) :
    (((rootInv * tMinus : stdGroup) : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) y =
      xOne K (eLab K 76) (xOne K (eLab K 77) y) := by
  rw [Subgroup.coe_mul, coe_rootInv, coe_tMinus, rootInvM, Units.val_mul, Module.End.mul_apply,
    pinnedX_eq isRoot_theta, pinnedX_eq isRoot_neg_theta, rootOp_apply, rootOp_apply,
    ch17575_rootVec_theta, ch17575_rootVec_negTheta]
  simp only [one_smul, one_pow, xOne]

theorem ch17575_eq_of_mem_conjOrbit_of_inverts
    (hgr : ∀ a b c : Fin 78, bracket K (eLab K a) (eLab K b) (lab c) ≠ 0 →
      lev a + lev b = lev c + 2)
    (hfix : ∀ y : RootModule Tag.E6 K, xOne K (eLab K 76) (xOne K (eLab K 77) y) = y →
      ∀ k : Fin 78, lev k = 1 → y (lab k) = 0)
    (hsq : ∀ β k : Fin 78, (β : ℕ) ∈ testB → lev k = 1 →
      bracket K (eLab K β) (bracket K (eLab K β) (eLab K k)) = 0)
    (hker : ∀ y : RootModule Tag.E6 K, (∀ k : Fin 78, lev k ≠ 1 → y (lab k) = 0) →
      (∀ β : Fin 78, (β : ℕ) ∈ testB → bracket K (eLab K β) y = 0) → y = 0)
    {x : stdGroup} (hx : x ∈ conjOrbit PJ tMinus)
    (hinv : x * (rootInv * tMinus) * x⁻¹ = (rootInv * tMinus)⁻¹) :
    x = tMinus ∨ x = rootInv * tMinus * rootInv := by
  obtain ⟨c, hc, hcx⟩ := hx
  have hc' : (c : ModGL Tag.E6 K) ∈ (nativeParabolic firstJ : Set (ModGL Tag.E6 K)) :=
    Subgroup.mem_subgroupOf.1 hc
  rw [coe_nativeParabolic_eq_mul subset_rfl] at hc'
  obtain ⟨q, hq, l, hl, hql⟩ := Set.mem_mul.1 hc'
  have hl' : l ∈ stdLevi firstJ := by
    rw [← leviParabolic_firstJ]
    exact hl
  have hlt : l * (tMinus : ModGL Tag.E6 K) = tMinus * l :=
    Subgroup.mem_centralizer_singleton_iff.1
      (groupA_le_centralizer_tMinus (stdLevi_firstJ_le_groupA hl'))
  have hqA : q ∈ adjointGroup Tag.E6 K :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).1 (Subgroup.mem_inf.1 hq).2).1
  have hx' : (x : ModGL Tag.E6 K) = q * pinnedX Tag.E6 K (-theta) 1 * q⁻¹ := by
    rw [← hcx, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hql, ← coe_tMinus]
    calc q * l * (tMinus : ModGL Tag.E6 K) * (q * l)⁻¹ = q * (l * tMinus) * l⁻¹ * q⁻¹ := by
          group
      _ = q * (tMinus * l) * l⁻¹ * q⁻¹ := by rw [hlt]
      _ = q * tMinus * q⁻¹ := by group
  obtain ⟨cs, hcs, hqcs⟩ := exists_params_of_mem_stdRadical hq
  have hzx : rootInv * tMinus * x = x * (rootInv * tMinus)⁻¹ := by
    calc rootInv * tMinus * x = (x * (rootInv * tMinus) * x⁻¹)⁻¹ * x := by
          rw [hinv, inv_inv]
      _ = x * (rootInv * tMinus)⁻¹ := by group
  set e := (q : Module.End K (RootModule Tag.E6 K)) (eLab K 77) with he
  have hβ : ∀ β : Fin 78, (β : ℕ) ∈ testB → ∀ k : Fin 78, lev k = 1 →
      bracket K (eLab K β) e (lab k) + form K (eLab K β) e * e (lab k) = 0 := by
    intro β hβB k hk
    obtain ⟨-, hlβ, h76, h77, f76, f77⟩ := ch17575_testB_facts β hβB
    have e76 := pinnedX_single_eq (a := ⟨76, by norm_num⟩) (b := β) (by norm_num) h76 f76
    have e77 := pinnedX_single_eq (a := ⟨77, by norm_num⟩) (b := β) (by norm_num) h77 f77
    rw [show e6Certificate.root (((⟨76, by norm_num⟩ : Fin 78) : ℕ) - 6) = theta from
      root_seventy] at e76
    rw [show e6Certificate.root (((⟨77, by norm_num⟩ : Fin 78) : ℕ) - 6) = -theta from
      root_seventyOne] at e77
    have hzβ : (((rootInv * tMinus : stdGroup) : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) (eLab K β) = eLab K β := by
      rw [eLab, Subgroup.coe_mul, coe_rootInv, coe_tMinus, rootInvM, Units.val_mul,
        Module.End.mul_apply, e77, e76]
    have hxβ : ((x : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (eLab K β) =
        eLab K β + bracket K e (eLab K β) + form K e (eLab K β) • e := by
      rw [hx', conj_pinnedX_one_apply hqA isRoot_neg_theta, ch17575_rootVec_negTheta]
    have hfixβ : xOne K (eLab K 76) (xOne K (eLab K 77)
        (((x : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (eLab K β))) =
        ((x : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (eLab K β) := by
      rw [← ch17575_z_apply, ← Module.End.mul_apply, ← Units.val_mul, ← Subgroup.coe_mul, hzx,
        Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, Subgroup.coe_inv,
        units_inv_apply_eq hzβ]
    have h0 := hfix _ hfixβ k hk
    have hne : β ≠ k := fun h => by
      rw [h] at hlβ
      omega
    rw [hxβ, Finsupp.add_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      ch17575_eLab_apply, if_neg hne, zero_add, bracket_comm, form_comm] at h0
    exact h0
  have he1 := ch17575_lev1_eq_zero hgr hsq hker e hβ
  have hprod := ch17575_prod_apply hgr (List.ofFn fun j => (orbAt j, cs j)) (by
    intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hp
    exact orbAt_mem j)
  have hPm : ((List.ofFn fun j => (orbAt j, cs j)).map fun p => yElt p.1 p.2) =
      List.ofFn fun j => yElt (orbAt j) (cs j) := by
    rw [List.map_ofFn]
    rfl
  rw [hPm, ← hqcs] at hprod
  have hcs0 : ∀ j : Fin 15, j ≠ Fin.last 14 → yElt (orbAt j) (cs j) = 1 := by
    intro j hj
    obtain ⟨hk78, hkl, hkb, hoth⟩ := ch17575_kSel_facts j hj
    have h := hprod.2 ⟨_, hk78⟩ hkl
    rw [← he, he1 _ hkl, List.map_ofFn, List.sum_ofFn, Finset.sum_eq_single j] at h
    · have hc0 : toK (cs j) = 0 := by
        simp only [Function.comp_apply, ch17575Contrib, hkb, if_true, mul_one] at h
        by_cases ho : (orbAt j).1 = (orbAt j).2
        · rw [if_pos ho, add_zero] at h
          exact h.symm
        · rw [if_neg ho, (hoth j).2 ho, if_neg Bool.false_ne_true, mul_zero, add_zero] at h
          exact h.symm
      have : cs j = 0 := hc0
      rw [this, ch17575_yElt_zero]
    · intro j' _ hj'
      obtain ⟨h1, h2⟩ := hoth j'
      simp only [Function.comp_apply, ch17575Contrib, h1 hj', Bool.false_eq_true, if_false,
        mul_zero, zero_add]
      by_cases ho : (orbAt j').1 = (orbAt j').2
      · rw [if_pos ho]
      · rw [if_neg ho, h2 ho, if_neg Bool.false_ne_true, mul_zero]
    · simp
  have hqeq : q = yElt (orbAt (Fin.last 14)) (cs (Fin.last 14)) := by
    rw [hqcs]
    exact ch17575_prod_ofFn_last 14 _ hcs0
  have h14 : orbAt (Fin.last 14) = (76, 76) := rfl
  have hc14 := hcs (Fin.last 14)
  rw [h14] at hc14 hqeq
  rw [yElt, if_pos rfl, labRoot, show e6Certificate.root (76 - 6) = theta from root_seventy] at hqeq
  have hch : choices (76, 76) = [0, 1] := rfl
  rw [hch, List.mem_cons, List.mem_singleton] at hc14
  rcases hc14 with h0 | h1
  · left
    rw [h0, toK_zero, pinnedX_zero] at hqeq
    apply Subtype.ext
    rw [hx', hqeq, one_mul, inv_one, mul_one, coe_tMinus]
  · right
    rw [h1, toK_one, ← rootInvM] at hqeq
    have hri : rootInvM⁻¹ = rootInvM := inv_eq_of_mul_eq_one_right rootInvM_mul_self
    apply Subtype.ext
    rw [hx', hqeq, hri, Subgroup.coe_mul, Subgroup.coe_mul, coe_rootInv, coe_tMinus]

theorem ch17575_eq_of_mem_rootClass_of_inverts
    (hgr : ∀ a b c : Fin 78, bracket K (eLab K a) (eLab K b) (lab c) ≠ 0 →
      lev a + lev b = lev c + 2)
    (hfix : ∀ y : RootModule Tag.E6 K, xOne K (eLab K 76) (xOne K (eLab K 77) y) = y →
      ∀ k : Fin 78, lev k = 1 → y (lab k) = 0)
    (hsq : ∀ β k : Fin 78, (β : ℕ) ∈ testB → lev k = 1 →
      bracket K (eLab K β) (bracket K (eLab K β) (eLab K k)) = 0)
    (hker : ∀ y : RootModule Tag.E6 K, (∀ k : Fin 78, lev k ≠ 1 → y (lab k) = 0) →
      (∀ β : Fin 78, (β : ℕ) ∈ testB → bracket K (eLab K β) y = 0) → y = 0)
    {x : stdGroup} (hx : x ∈ rootClass)
    (hinv : x * (rootInv * tMinus) * x⁻¹ = (rootInv * tMinus)⁻¹) :
    x = rootInv ∨ x = tMinus ∨ x = rootInv * tMinus * rootInv := by
  obtain ⟨g, rfl⟩ := (mem_rootClass_iff _).1 hx
  obtain ⟨i, hi⟩ := exists_repLevel g
  have hmem : rootMap g ∈ levPoints (repLevel i) := hi ▸ rootMap_mem_levPoints g
  have ho := orderOf_rootInv_mul_of_mem_levPoints hmem
  rcases (by decide : ∀ i : Fin 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) i with
    rfl | rfl | rfl | rfl | rfl
  · left
    have h1 : rootInv * rootMap g = 1 := orderOf_eq_one_iff.1 ho
    rw [← mul_left_cancel_iff (a := rootInv), h1, rootInv_mul_self]
  · exact absurd (not_inverts_of_orderOf hx hinv (Or.inl ho)) not_false
  · exact absurd (not_inverts_of_orderOf hx hinv (Or.inl ho)) not_false
  · exact absurd (not_inverts_of_orderOf hx hinv (Or.inr ho)) not_false
  · rw [← conjOrbit_PJ_tMinus] at hmem
    exact Or.inr (ch17575_eq_of_mem_conjOrbit_of_inverts hgr hfix hsq hker hmem hinv)

theorem ch17575_inverts_of_certificates {x : stdGroup} (hx : x ∈ rootClass)
    (hinv : x * (rootInv * tMinus) * x⁻¹ = (rootInv * tMinus)⁻¹) :
    x = rootInv ∨ x = tMinus ∨ x = rootInv * tMinus * rootInv :=
  ch17575_eq_of_mem_rootClass_of_inverts
    (fun a b c => (Certificates.certificate17579 K a b c).1)
    (Certificates.certificate17580 K) (Certificates.certificate17581 K).1
    (Certificates.certificate17581 K).2 hx hinv

end CFSG.HardMathSupport.Dickson.I271.TabBThreeL1
