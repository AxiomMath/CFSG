module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5E16
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.CGT.T75P.SylowSplit
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped Pointwise

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def omegaConj (hQ : Q.Nondegenerate) (s : OGroup Q) :
    MulAut ↥(omegaGroup hQ) :=
  MulAut.conjNormal s

theorem coe_omegaConj (hQ : Q.Nondegenerate) (s : OGroup Q) (p : ↥(omegaGroup hQ)) :
    ((omegaConj hQ s p : ↥(omegaGroup hQ)) : OGroup Q) = s * (p : OGroup Q) * s⁻¹ :=
  MulAut.conjNormal_apply s p

private theorem mem_fixSub_omegaConj_iff (hQ : Q.Nondegenerate) {s : OGroup Q} (hss : s * s = 1)
    (p : ↥(omegaGroup hQ)) :
    p ∈ fixSub (omegaConj hQ s) ↔ (p : OGroup Q) ∈ (blockHom hss).range := by
  rw [mem_fixSub_iff, range_blockHom hQ hss, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hcoe : s * (p : OGroup Q) * s⁻¹ = (p : OGroup Q) := by
      rw [← coe_omegaConj hQ s p, h]
    have hsp : s * (p : OGroup Q) = (p : OGroup Q) * s := by
      have h' := congrArg (fun x => x * s) hcoe
      rwa [mul_assoc, inv_mul_cancel, mul_one] at h'
    exact hsp.symm
  · intro hp
    apply Subtype.ext
    rw [coe_omegaConj]
    rw [← hp, mul_assoc, mul_inv_cancel, mul_one]

theorem t5_b5_geom (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {s : OGroup Q} (hss : s * s = 1) (hs1 : invDim s = 1) :
    ∃ K Bb : Subgroup ↥(omegaGroup hQ),
      K ≤ fixSub (omegaConj hQ s) ∧
      (∀ p ∈ fixSub (omegaConj hQ s), ∀ k ∈ K, p * k * p⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
      Bb ≤ fixSub (omegaConj hQ s) ∧ IsElemAb2 Bb 5 ∧
      ∀ π' : ↥(omegaGroup hQ), (π' : OGroup Q) = piOrth Q →
        π' ∈ Bb ∧ (∀ b ∈ Bb, b ∈ K ∨ π' * b ∈ K) ∧
          ∃ h : π' ∈ fixSub (omegaConj hQ s),
            (⟨π', h⟩ : ↥(fixSub (omegaConj hQ s))) ∉ commutator ↥(fixSub (omegaConj hQ s)) := by
  have hcdim : Module.finrank (ZMod 3) (commSp s) = 1 := hs1
  have hW5 : Module.finrank (ZMod 3) (fixSp s) = 5 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) s
    rw [hcdim, hdim] at h
    omega
  have hW : 2 ≤ Module.finrank (ZMod 3) (fixSp s) := by omega
  have hR := nondegenerate_restrict_fixSp hQ hss
  have hC := nondegenerate_restrict_commSp hQ hss
  let φW : OGroup (Q.restrict (fixSp s)) →* OGroup Q :=
    (blockHom hss).comp (MonoidHom.inl _ _)
  have hφinj : Function.Injective φW := by
    intro a b hab
    exact congrArg Prod.fst (blockHom_injective hss
      (show blockHom hss (a, 1) = blockHom hss (b, 1) from hab))
  have hpi_mem : piOrth Q ∈ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ]
    exact ⟨by rw [hdim]; decide, by rw [hdim, hsgn]; decide⟩
  let π₀ : ↥(omegaGroup hQ) := ⟨piOrth Q, hpi_mem⟩
  have hπ0coe : (π₀ : OGroup Q) = piOrth Q := rfl
  have hπ0_2 : π₀ * π₀ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hπ0coe, piOrth_mul_self, Subgroup.coe_one]
  have hπ0_1 : π₀ ≠ 1 := by
    intro h
    have h1 : (π₀ : OGroup Q) = 1 := by rw [h]; rfl
    rw [hπ0coe] at h1
    exact piOrth_ne_one (Q := Q) (by rw [hdim]; norm_num) h1
  have horder0 : orderOf π₀ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hπ0_2) hπ0_1
  have hπ0center : π₀ ∈ Subgroup.center ↥(omegaGroup hQ) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hπ0coe]
    exact Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) (g : OGroup Q)
  obtain ⟨E, hEsub, hEab⟩ := t5_exists_E16 hR hW5
  have hEcard : Nat.card E = 16 := by rw [hEab.2]; norm_num
  have hERmap : (omegaGroup hR).map φW ≤ omegaGroup hQ := by
    rintro x ⟨a, ha, rfl⟩
    exact blockHom_left_mem_omegaGroup hQ hss hW ha
  have hEle : E.map φW ≤ omegaGroup hQ := (Subgroup.map_mono hEsub).trans hERmap
  let Ē : Subgroup ↥(omegaGroup hQ) := (E.map φW).subgroupOf (omegaGroup hQ)
  have hĒeq : Ē = (E.map φW).subgroupOf (omegaGroup hQ) := rfl
  let K : Subgroup ↥(omegaGroup hQ) := ((omegaGroup hR).map φW).subgroupOf (omegaGroup hQ)
  have hKeq : K = ((omegaGroup hR).map φW).subgroupOf (omegaGroup hQ) := rfl
  let Bb : Subgroup ↥(omegaGroup hQ) := Ē ⊔ Subgroup.zpowers π₀
  have hBbeq : Bb = Ē ⊔ Subgroup.zpowers π₀ := rfl
  have hEK : Ē ≤ K := by
    intro x hx
    rw [hĒeq, Subgroup.mem_subgroupOf] at hx
    rw [hKeq, Subgroup.mem_subgroupOf]
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨a, hEsub ha, hax⟩
  have hπ0P : π₀ ∈ fixSub (omegaConj hQ s) := by
    rw [mem_fixSub_omegaConj_iff hQ hss π₀]
    rw [range_blockHom hQ hss, Subgroup.mem_centralizer_singleton_iff, hπ0coe]
    exact (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) s).symm
  have hKP : K ≤ fixSub (omegaConj hQ s) := by
    intro k hk
    rw [hKeq, Subgroup.mem_subgroupOf] at hk
    obtain ⟨a, ha, hak⟩ := Subgroup.mem_map.mp hk
    rw [mem_fixSub_omegaConj_iff hQ hss k]
    exact MonoidHom.mem_range.mpr ⟨(a, 1), hak⟩
  have hKnormal : ∀ p ∈ fixSub (omegaConj hQ s), ∀ k ∈ K, p * k * p⁻¹ ∈ K := by
    intro p hp k hk
    rw [hKeq, Subgroup.mem_subgroupOf] at hk ⊢
    obtain ⟨a, ha, hak⟩ := Subgroup.mem_map.mp hk
    obtain ⟨q, hq⟩ := (show (p : OGroup Q) ∈ (blockHom hss).range from
      (mem_fixSub_omegaConj_iff hQ hss p).mp hp)
    have hak' : blockHom hss (a, 1) = (k : OGroup Q) := hak
    refine Subgroup.mem_map.mpr ⟨q.1 * a * q.1⁻¹,
      (omegaGroup_normal hR).conj_mem a ha q.1, ?_⟩
    show blockHom hss (q.1 * a * q.1⁻¹, 1) =
      ((p * k * p⁻¹ : ↥(omegaGroup hQ)) : OGroup Q)
    rw [show ((p * k * p⁻¹ : ↥(omegaGroup hQ)) : OGroup Q) =
        (p : OGroup Q) * (k : OGroup Q) * (p : OGroup Q)⁻¹ from by simp,
      ← hak', ← hq]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext rfl (by simp)
  have hKq : CFSG.IsQuasisimple ↥K := by
    have eK : ↥(omegaGroup hR) ≃* ↥K :=
      (Subgroup.equivMapOfInjective (omegaGroup hR) φW hφinj).trans
        (Subgroup.subgroupOfEquivOfLe hERmap).symm
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eK (isQuasisimple_omegaGroup_five hR hW5)
  have hπC_ne : piOrth (Q.restrict (commSp s)) ≠ 1 :=
    piOrth_ne_one (Q := Q.restrict (commSp s)) (by rw [hcdim]; norm_num)
  have hπ0notK : π₀ ∉ K := by
    intro hmem
    rw [hKeq, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨a, ha, haπ⟩ := Subgroup.mem_map.mp hmem
    have hb : blockHom hss (a, 1) = blockHom hss (piOrth (Q.restrict (fixSp s)),
        piOrth (Q.restrict (commSp s))) := by
      rw [show blockHom hss (a, 1) = (π₀ : OGroup Q) from haπ, hπ0coe,
        ← blockHom_piOrth_piOrth]
    have hpair := blockHom_injective hss hb
    exact hπC_ne (congrArg Prod.snd hpair).symm
  have hπ0notE : π₀ ∉ Ē := fun h => hπ0notK (hEK h)
  have hĒel : CFSG.Open.IsElemAbelian 2 Ē := by
    rw [hĒeq]
    exact (hEab.1.map φW).subgroupOf (omegaGroup hQ)
  have hzpEl : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers π₀) :=
    CFSG.Open.isElemAbelian_zpowers (p := 2) (x := π₀) (by rw [pow_two]; exact hπ0_2)
  have hcomm : ∀ a ∈ Ē, ∀ b ∈ Subgroup.zpowers π₀, a * b = b * a := by
    intro a _ b hb
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two horder0).mp hb with rfl | rfl
    · rw [mul_one, one_mul]
    · exact Subgroup.mem_center_iff.mp hπ0center a
  have hinf : Ē ⊓ Subgroup.zpowers π₀ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two horder0).mp hx.2 with h1 | h1
    · exact Subgroup.mem_bot.mpr h1
    · exact absurd (h1 ▸ hx.1) hπ0notE
  have hcardE : Nat.card Ē = 16 := by
    have h1 : Nat.card Ē = Nat.card E := by
      rw [hĒeq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEle).toEquiv,
        Subgroup.card_map_of_injective (K := E) hφinj]
    rw [h1, hEcard]
  have hcardZ : Nat.card (Subgroup.zpowers π₀) = 2 := by
    rw [Nat.card_zpowers, horder0]
  have hBbEl : CFSG.Open.IsElemAbelian 2 Bb := by
    rw [hBbeq]
    exact CFSG.Open.IsElemAbelian.sup_of_commute hĒel hzpEl hcomm
  have hcardBb : Nat.card Bb = 2 ^ 5 := by
    rw [hBbeq, CFSG.CGT.T75P.card_sup_of_commute hcomm hinf, hcardE, hcardZ]
    norm_num
  have hBab : IsElemAb2 Bb 5 := ⟨hBbEl, hcardBb⟩
  have hBP : Bb ≤ fixSub (omegaConj hQ s) := by
    rw [hBbeq]
    exact sup_le (hEK.trans hKP) (Subgroup.zpowers_le_of_mem hπ0P)
  have hBBK : ∀ b ∈ Bb, b ∈ K ∨ π₀ * b ∈ K := by
    have hcen1 : Ē ≤ Subgroup.centralizer (Subgroup.zpowers π₀ : Set ↥(omegaGroup hQ)) :=
      fun a ha => Subgroup.mem_centralizer_iff.mpr (fun b hb => (hcomm a ha b hb).symm)
    have hcen : Ē ≤ Subgroup.normalizer (Subgroup.zpowers π₀ : Set ↥(omegaGroup hQ)) :=
      hcen1.trans (Subgroup.centralizer_le_normalizer _)
    have hmul : ((Ē ⊔ Subgroup.zpowers π₀ : Subgroup ↥(omegaGroup hQ)) :
        Set ↥(omegaGroup hQ)) = (Ē : Set ↥(omegaGroup hQ)) *
          (Subgroup.zpowers π₀ : Set ↥(omegaGroup hQ)) :=
      Subgroup.coe_mul_of_left_le_normalizer_right Ē (Subgroup.zpowers π₀) hcen
    intro b hb
    rw [hBbeq] at hb
    have hb' : b ∈ (Ē : Set ↥(omegaGroup hQ)) *
        (Subgroup.zpowers π₀ : Set ↥(omegaGroup hQ)) := by
      rw [← hmul]; exact hb
    obtain ⟨e, he, y, hy, hey⟩ := Set.mem_mul.mp hb'
    rw [← hey]
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two horder0).mp hy with hy1 | hy1
    · rw [hy1, mul_one]; exact Or.inl (hEK he)
    · rw [hy1]
      have hc : π₀ * e = e * π₀ := (Subgroup.mem_center_iff.mp hπ0center e).symm
      have hred : π₀ * (e * π₀) = e := by
        rw [← mul_assoc, hc, mul_assoc, hπ0_2, mul_one]
      rw [hred]; exact Or.inr (hEK he)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardC : Nat.card (OGroup (Q.restrict (commSp s))) = 2 :=
    natCard_oGroup_one hC hcdim
  haveI : IsCyclic (OGroup (Q.restrict (commSp s))) :=
    isCyclic_of_prime_card (p := 2) hcardC
  let e := MonoidHom.ofInjective (blockHom_injective hss)
  have hmemP : ∀ p : ↥(fixSub (omegaConj hQ s)),
      (p : OGroup Q) ∈ (blockHom hss).range :=
    fun p => (mem_fixSub_omegaConj_iff hQ hss p).mp p.2
  let ε : ↥(fixSub (omegaConj hQ s)) →* OGroup (Q.restrict (commSp s)) :=
    (MonoidHom.snd _ _).comp (e.symm.toMonoidHom.comp
      (((omegaGroup hQ).subtype.comp (fixSub (omegaConj hQ s)).subtype).codRestrict
        (blockHom hss).range (fun p => hmemP p)))
  have hεsymm : e.symm ⟨π₀, hmemP ⟨π₀, hπ0P⟩⟩ =
      (piOrth (Q.restrict (fixSp s)), piOrth (Q.restrict (commSp s))) := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    show (π₀ : OGroup Q) = blockHom hss (piOrth (Q.restrict (fixSp s)),
      piOrth (Q.restrict (commSp s)))
    rw [blockHom_piOrth_piOrth, hπ0coe]
  have hεπ : ε ⟨π₀, hπ0P⟩ = piOrth (Q.restrict (commSp s)) := by
    change (e.symm ⟨π₀, hmemP ⟨π₀, hπ0P⟩⟩).2 = piOrth (Q.restrict (commSp s))
    rw [hεsymm]
  have hcommker : commutator ↥(fixSub (omegaConj hQ s)) ≤ ε.ker := by
    change ⁅(⊤ : Subgroup ↥(fixSub (omegaConj hQ s))), ⊤⁆ ≤ ε.ker
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' (ε g₁) (ε g₂))
  have hnot : (⟨π₀, hπ0P⟩ : ↥(fixSub (omegaConj hQ s))) ∉
      commutator ↥(fixSub (omegaConj hQ s)) := by
    intro hmem
    have hker := hcommker hmem
    rw [MonoidHom.mem_ker, hεπ] at hker
    exact hπC_ne hker
  refine ⟨K, Bb, hKP, hKnormal, hKq, hBP, hBab, ?_⟩
  intro π' hπ'
  have hπ'eq : π' = π₀ := Subtype.ext (by rw [hπ', hπ0coe])
  rw [hπ'eq]
  exact ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers π₀), hBBK, ⟨hπ0P, hnot⟩⟩

end CFSG.OddStandard.SmallF3.Omega
