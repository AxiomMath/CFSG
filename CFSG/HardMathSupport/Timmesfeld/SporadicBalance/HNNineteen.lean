module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PrimeCommute
public import CFSG.Sporadic.HNSchreier.Simple
public import CFSG.Sporadic.HNSchreier.Sylow3
public import CFSG.Sporadic.HNSchreier.FALocal
public import CFSG.Sporadic.HNSchreier.Separating
public import CFSG.Sporadic.HNOddCore.FiveA
public import CFSG.Certificates.Kernel.SporSch.HNNat
public import Certificates.Certificate2085
public import Certificates.Certificate13608
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open Equiv Subgroup MulAction Matrix
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

section Abstract

variable {G α : Type*} [Group G] [MulAction G α]

theorem ncard_fix_conj (g y : G) :
    {x : α | (g * y * g⁻¹) • x = x}.ncard = {x : α | y • x = x}.ncard := by
  have e : {x : α | (g * y * g⁻¹) • x = x} = (fun x => g • x) '' {x : α | y • x = x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨g⁻¹ • x, ?_, smul_inv_smul g x⟩
      rw [mul_smul, mul_smul] at h
      exact eq_inv_smul_iff.2 h
    · rintro ⟨z, hz, rfl⟩
      rw [mul_smul, mul_smul, inv_smul_smul, hz]
  rw [e, Set.ncard_image_of_injective _ (MulAction.injective g)]

theorem exists_fix_of_not_dvd [Finite α] {p : ℕ} [hp : Fact p.Prime] {y : G} (hy : orderOf y = p)
    (S : Set α) (hS : ∀ x, y • x ∈ S ↔ x ∈ S) (hn : ¬ p ∣ S.ncard) : ∃ x ∈ S, y • x = x := by
  have hz : ∀ k : ℤ, ∀ x, y ^ k • x ∈ S ↔ x ∈ S := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · intro x
      rw [zpow_zero, one_smul]
    · intro k ih x
      rw [_root_.zpow_add_one, mul_smul, ih, hS]
    · intro k ih x
      rw [_root_.zpow_sub_one, mul_smul, ih, ← hS, smul_inv_smul]
  let A : SubMulAction (zpowers y) α :=
    { carrier := S
      smul_mem' := fun g x hx => by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.1 g.2
        rw [Subgroup.smul_def, ← hk]
        exact (hz k x).2 hx }
  have hP : Nat.card (zpowers y) = p ^ 1 := by rw [Nat.card_zpowers, hy, pow_one]
  have : Finite (zpowers y) := Nat.finite_of_card_ne_zero (by rw [hP]; exact (pow_pos hp.out.pos 1).ne')
  have hmod := (IsPGroup.of_card hP).card_modEq_card_fixedPoints A
  by_contra hno
  simp only [not_exists, not_and] at hno
  have h0 : Nat.card (fixedPoints (zpowers y) A) = 0 := by
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun t => ?_⟩
    have h := (mem_fixedPoints.1 t.2) ⟨y, mem_zpowers y⟩
    exact hno t.1.1 t.1.2 (congrArg Subtype.val h)
  rw [h0] at hmod
  exact hn (Nat.modEq_zero_iff_dvd.1 hmod)

end Abstract

theorem cycleType_of_orderOf_five {σ : Perm (Fin 12)} (h : orderOf σ = 5) :
    σ.cycleType = {5} ∨ σ.cycleType = {5, 5} := by
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (by rw [h]; exact Nat.prime_five)
  rw [h] at hn
  have hs := Equiv.Perm.sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hs
  have hle := σ.support.card_le_univ
  rw [Fintype.card_fin] at hle
  have hn2 : n = 0 ∨ n = 1 := by omega
  rcases hn2 with rfl | rfl
  · left
    rw [hn]
    all_goals rfl
  · right
    rw [hn]
    all_goals rfl

theorem exists_alt_conj {σ τ : Perm (Fin 12)} (h : σ.cycleType = τ.cycleType)
    (hs : σ.support.card ≤ 10) : ∃ c ∈ alternatingGroup (Fin 12), c * σ * c⁻¹ = τ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 h)
  have hcard : 1 < σ.supportᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
  have ha' : σ a = a := by simpa [Equiv.Perm.mem_support] using ha
  have hb' : σ b = b := by simpa [Equiv.Perm.mem_support] using hb
  have hcomm : σ * swap a b = swap a b * σ := by
    rw [Equiv.mul_swap_eq_swap_mul, ha', hb']
  have hsw : swap a b * σ * swap a b = σ := by
    rw [← hcomm, mul_assoc, Equiv.swap_mul_self, mul_one]
  rcases Int.units_eq_one_or (Perm.sign c) with hsg | hsg
  · exact ⟨c, Equiv.Perm.mem_alternatingGroup.2 hsg, hc⟩
  · refine ⟨c * swap a b, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Perm.sign_mul, hsg, Perm.sign_swap hab]
      exact Int.units_mul_self _
    · calc c * swap a b * σ * (c * swap a b)⁻¹ = c * (swap a b * σ * swap a b) * c⁻¹ := by
            rw [_root_.mul_inv_rev, swap_inv]
            group
        _ = τ := by rw [hsw, hc]

@[expose] def sigmaF : Perm (Fin 12) := List.formPerm [(0 : Fin 12), 1, 2, 3, 4]

@[expose] def sigmaE : Perm (Fin 12) :=
  List.formPerm [(0 : Fin 12), 1, 7, 9, 3] * List.formPerm [(4 : Fin 12), 5, 6, 10, 11]

theorem fiveNat_eq : fiveNat = sigmaF := by
  unfold fiveNat sigmaF
  decide

theorem cycleType_five_cycle {l : List (Fin 12)} (hl : l.Nodup) (h2 : 2 ≤ l.length)
    (h5 : l.length = 5) : (List.formPerm l).cycleType = {5} := by
  rw [(List.isCycle_formPerm hl h2).cycleType,
    List.support_formPerm_of_nodup _ hl (fun x hx => by rw [hx] at h5; simp at h5),
    List.toFinset_card_of_nodup hl, h5]

theorem sigmaF_cycleType : sigmaF.cycleType = {5} :=
  cycleType_five_cycle (by decide) (by decide) (by decide)

theorem sigmaE_cycleType : sigmaE.cycleType = {5, 5} := by
  rw [sigmaE, Equiv.Perm.Disjoint.cycleType_mul (by change ∀ x, _ ∨ _; decide),
    cycleType_five_cycle (by decide) (by decide) (by decide),
    cycleType_five_cycle (by decide) (by decide) (by decide)]
  all_goals rfl

theorem natWord_e : natWord [2, 4, 5, 8, 5, 4, 2] = sigmaE := by
  have hp := prep_natWord (w := [2, 4, 5, 8, 5, 4, 2]) (by decide)
  rw [natStrongArr_eq] at hp
  have hv : ∀ x : Fin 12, ([2, 4, 5, 8, 5, 4, 2] : List ℤ).foldr
      (CFSG.KS.TW.GZ CFSG.KS.HNNat.natF CFSG.KS.HNNat.natFI) x.val = (sigmaE x).val := by
    unfold sigmaE
    decide +kernel
  refine Equiv.ext fun x => Fin.ext ?_
  rw [← hp x, CFSG.KS.HNNat.natWord_pt (by decide) x.isLt, hv]

theorem conj_five
    {z : JH} (hz : z ∈ HJ) (ho : orderOf z = 5) :
    ∃ k ∈ HJ, k * z * k⁻¹ = fJ ∨ k * z * k⁻¹ = hWordJ [2, 4, 5, 8, 5, 4, 2] := by
  set σ : Perm (Fin 12) := ↑(thetaJ ⟨z, hz⟩) with hσdef
  have hσ : orderOf σ = 5 := by
    have h := orderOf_injective thetaHom (Subtype.val_injective.comp thetaJ.injective) ⟨z, hz⟩
    rw [Subgroup.orderOf_mk] at h
    rw [← ho, ← h]
    rfl
  have hsupp : σ.support.card ≤ 10 := by
    rw [← Equiv.Perm.sum_cycleType]
    rcases cycleType_of_orderOf_five hσ with h | h <;> rw [h] <;> simp
  have key : ∀ w : HJ, (thetaJ w : Perm (Fin 12)).cycleType = σ.cycleType →
      ∃ k ∈ HJ, k * z * k⁻¹ = w := by
    intro w hw
    obtain ⟨c, hc, he⟩ := exists_alt_conj hw.symm hsupp
    refine ⟨(thetaJ.symm ⟨c, hc⟩ : HJ), (thetaJ.symm ⟨c, hc⟩).2, ?_⟩
    have h : thetaJ.symm ⟨c, hc⟩ * ⟨z, hz⟩ * (thetaJ.symm ⟨c, hc⟩)⁻¹ = w := by
      apply thetaJ.injective
      apply Subtype.ext
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv]
      exact he
    have h2 := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    exact h2
  rcases cycleType_of_orderOf_five hσ with h | h
  · obtain ⟨k, hk, he⟩ := key ⟨fJ, fJ_mem⟩ (by rw [thetaJ_fJ, fiveNat_eq, sigmaF_cycleType, h])
    exact ⟨k, hk, Or.inl he⟩
  · obtain ⟨k, hk, he⟩ := key (hWordH [2, 4, 5, 8, 5, 4, 2])
      (by rw [thetaJ_hWord, natWord_e, sigmaE_cycleType, h])
    exact ⟨k, hk, Or.inr he⟩

theorem ncard_fix_f : {x : X | fJ • x = x}.ncard = 50 := by
  have e : {x : X | fJ • x = x} = Set.range fun t : Fin 50 =>
      (⟨FAData.fFixed.getD t 0, CFSG.Sporadic.HNOddCore.fFixed_lt t t.2⟩ : X) := by
    ext x
    rw [Set.mem_setOf_eq, Certificates.certificate2085.1 x, Set.mem_range]
    constructor
    · intro hx
      obtain ⟨t, ht, he⟩ := List.getElem_of_mem hx
      have ht' : t < 50 := by rwa [CFSG.Sporadic.HNOddCore.fFixed_length] at ht
      refine ⟨⟨t, ht'⟩, Fin.ext ?_⟩
      change FAData.fFixed.getD t 0 = x.val
      rw [List.getD_eq_getElem _ _ ht]
      exact he
    · rintro ⟨t, rfl⟩
      have ht : (t : ℕ) < FAData.fFixed.length := by
        rw [CFSG.Sporadic.HNOddCore.fFixed_length]
        exact t.2
      change FAData.fFixed.getD t 0 ∈ FAData.fFixed
      rw [List.getD_eq_getElem _ _ ht]
      exact List.getElem_mem ht
  rw [e, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  intro a b h
  exact Fin.ext (CFSG.Sporadic.HNOddCore.fFixed_inj a a.2 b b.2 (congrArg Fin.val h))

@[expose] def g19 : Perm X := a0 * a1 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0 * a1 * a0

@[expose] def uP19 : Perm X := a0 * (g19⁻¹ * a1 * g19)

@[expose] def gJ19 : JH := aJ * bJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ

@[expose] def nineteenJ : JH := aJ * (gJ19⁻¹ * bJ * gJ19)

theorem permJ_nineteenJ : permJ nineteenJ = uP19 := by
  simp only [nineteenJ, gJ19, map_mul, map_inv, permJ_aJ, permJ_bJ, uP19, g19]

theorem orderOf_nineteenJ :
    orderOf nineteenJ = 19 := by
  have h := order_parts
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hP : orderOf uP19 = 19 := orderOf_eq_prime h.2.2.2.2.1 h.2.2.2.2.2
  rw [← orderOf_injective permJ permJ_injective nineteenJ, permJ_nineteenJ, hP]

@[expose] def qv (x : X) : ZMod 5 :=
  PK x.val ⬝ᵥ ((formM * (matJ nineteenJ + matJ nineteenJ ^ 2)) *ᵥ PK x.val)

theorem qv_eq (x : X) :
    qv x = PK x.val ⬝ᵥ (formM *ᵥ PK (nineteenJ • x).val) +
      PK x.val ⬝ᵥ (formM *ᵥ PK ((nineteenJ * nineteenJ) • x).val) := by
  rw [PK_smul, PK_smul, qv, sq, ← matJ_mul, Matrix.mul_add, Matrix.add_mulVec,
    dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem form_smul (g : JH) (i j : X) :
    PK (g • i).val ⬝ᵥ (formM *ᵥ PK (g • j).val) = PK i.val ⬝ᵥ (formM *ᵥ PK j.val) := by
  have h := beta_invariant (permJ_mem g) i j
  rw [beta_eq, beta_eq, permJ_apply, permJ_apply, vL_eq (g • i).isLt, vL_eq (g • j).isLt,
    vL_eq i.isLt, vL_eq j.isLt] at h
  exact h

theorem qv_smul {y : JH}
    (hc : y * nineteenJ = nineteenJ * y) (x : X) : qv (y • x) = qv x := by
  have hc2 : nineteenJ * nineteenJ * y = y * (nineteenJ * nineteenJ) := by
    rw [mul_assoc, ← hc, ← mul_assoc, ← hc, mul_assoc]
  have e1 : nineteenJ • (y • x) = y • (nineteenJ • x) := by
    rw [← mul_smul, ← mul_smul, hc]
  have e2 : (nineteenJ * nineteenJ) • (y • x) = y • ((nineteenJ * nineteenJ) • x) := by
    rw [← mul_smul, ← mul_smul, hc2]
  rw [qv_eq, qv_eq, e1, e2, form_smul y x (nineteenJ • x),
    form_smul y x ((nineteenJ * nineteenJ) • x)]

theorem nineteenJ_smul_ne
    (x : X) : nineteenJ • x ≠ x := by
  intro hx
  have := hns_pretransitive
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq JH x0 x
  have hm : t⁻¹ * nineteenJ * t⁻¹⁻¹ ∈ HJ := by
    rw [mem_HJ_iff_fix, inv_inv, mul_smul, mul_smul, ht, hx, ← ht, inv_smul_smul]
  have ho : orderOf (⟨_, hm⟩ : HJ) = 19 := by
    rw [Subgroup.orderOf_mk, orderOf_conj_eq, orderOf_nineteenJ]
  have hd := orderOf_dvd_natCard (⟨_, hm⟩ : HJ)
  rw [ho, card_HJ] at hd
  norm_num at hd

theorem not_commute_nineteenJ
    {y : JH} (hy : orderOf y = 5) : y * nineteenJ ≠ nineteenJ * y := by
  intro hc
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hT : {x : X | qv x = 1}.ncard = 166459 := Certificates.certificate13608.1
  obtain ⟨p, -, hp⟩ := exists_fix_of_not_dvd hy {x : X | qv x = 1}
    (fun x => by rw [Set.mem_setOf_eq, Set.mem_setOf_eq, qv_smul hc]) (by rw [hT]; norm_num)
  have := hns_pretransitive
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq JH x0 p
  have hz : t⁻¹ * y * t⁻¹⁻¹ ∈ HJ := by
    rw [mem_HJ_iff_fix, inv_inv, mul_smul, mul_smul, ht, hp, ← ht, inv_smul_smul]
  obtain ⟨k, -, hk⟩ := conj_five hz (by rw [orderOf_conj_eq, hy])
  have hconj : (k * t⁻¹) * y * (k * t⁻¹)⁻¹ = k * (t⁻¹ * y * t⁻¹⁻¹) * k⁻¹ := by group
  have hF : {x : X | y • x = x}.ncard = 50 := by
    rw [← ncard_fix_conj (k * t⁻¹) y, hconj]
    rcases hk with he | he
    · rw [he, ncard_fix_f]
    · rw [he, Certificates.certificate13608.2]
  obtain ⟨x, hxy, hxu⟩ := exists_fix_of_not_dvd orderOf_nineteenJ {x : X | y • x = x}
    (fun x => by
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← mul_smul, hc, mul_smul, smul_left_cancel_iff])
    (by rw [hF]; norm_num)
  exact nineteenJ_smul_ne x hxu

theorem not_nineteen_dvd_card_centralizer
    {x : JH} (hx : orderOf x = 5) :
    ¬ 19 ∣ Nat.card (centralizer ({x} : Set JH)) := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  exact not_dvd_card_centralizer_of_not_commute (by rw [card_JH]; norm_num) orderOf_nineteenJ
    fun y hy => not_commute_nineteenJ (hy.trans hx)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
