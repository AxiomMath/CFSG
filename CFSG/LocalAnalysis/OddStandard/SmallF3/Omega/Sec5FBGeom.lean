module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5B5Geom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5FBE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK1Aux1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem sec5fb_mem_fixSub_iff (hQ : Q.Nondegenerate) {s : OGroup Q} (hss : s * s = 1)
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

theorem sec5fb_geom_of_E16 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {s : OGroup Q} (hss : s * s = 1) (hs1 : invDim s = 1)
    {E : Subgroup (OGroup (Q.restrict (fixSp s)))}
    (hEsub : E ≤ omegaGroup (nondegenerate_restrict_fixSp hQ hss)) (hEab : IsElemAb2 E 4) :
    ∃ K Bb : Subgroup ↥(omegaGroup hQ),
      K ≤ fixSub (omegaConj hQ s) ∧
      (∀ p ∈ fixSub (omegaConj hQ s), ∀ k ∈ K, p * k * p⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
      Bb ≤ fixSub (omegaConj hQ s) ∧ IsElemAb2 Bb 5 ∧
      (∀ e ∈ E, ∀ e' : ↥(omegaGroup hQ), (e' : OGroup Q) = blockHom hss (e, 1) → e' ∈ Bb) ∧
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
    rw [sec5fb_mem_fixSub_iff hQ hss π₀]
    rw [range_blockHom hQ hss, Subgroup.mem_centralizer_singleton_iff, hπ0coe]
    exact (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) s).symm
  have hKP : K ≤ fixSub (omegaConj hQ s) := by
    intro k hk
    rw [hKeq, Subgroup.mem_subgroupOf] at hk
    obtain ⟨a, ha, hak⟩ := Subgroup.mem_map.mp hk
    rw [sec5fb_mem_fixSub_iff hQ hss k]
    exact MonoidHom.mem_range.mpr ⟨(a, 1), hak⟩
  have hKnormal : ∀ p ∈ fixSub (omegaConj hQ s), ∀ k ∈ K, p * k * p⁻¹ ∈ K := by
    intro p hp k hk
    rw [hKeq, Subgroup.mem_subgroupOf] at hk ⊢
    obtain ⟨a, ha, hak⟩ := Subgroup.mem_map.mp hk
    obtain ⟨q, hq⟩ := (show (p : OGroup Q) ∈ (blockHom hss).range from
      (sec5fb_mem_fixSub_iff hQ hss p).mp hp)
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
  have hEBb : ∀ e ∈ E, ∀ e' : ↥(omegaGroup hQ), (e' : OGroup Q) = blockHom hss (e, 1) →
      e' ∈ Bb := by
    intro e he e' he'
    have hmemĒ : e' ∈ Ē := by
      rw [hĒeq, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map.mpr ⟨e, he, he'.symm⟩
    rw [hBbeq]
    exact Subgroup.mem_sup_left hmemĒ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardC : Nat.card (OGroup (Q.restrict (commSp s))) = 2 :=
    natCard_oGroup_one hC hcdim
  haveI : IsCyclic (OGroup (Q.restrict (commSp s))) :=
    isCyclic_of_prime_card (p := 2) hcardC
  let e := MonoidHom.ofInjective (blockHom_injective hss)
  have hmemP : ∀ p : ↥(fixSub (omegaConj hQ s)),
      (p : OGroup Q) ∈ (blockHom hss).range :=
    fun p => (sec5fb_mem_fixSub_iff hQ hss p).mp p.2
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
  refine ⟨K, Bb, hKP, hKnormal, hKq, hBP, hBab, hEBb, ?_⟩
  intro π' hπ'
  have hπ'eq : π' = π₀ := Subtype.ext (by rw [hπ', hπ0coe])
  rw [hπ'eq]
  exact ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers π₀), hBBK, ⟨hπ0P, hnot⟩⟩

private theorem sec5fb_exists_left_block (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {s : OGroup Q}
    (hss : s * s = 1) (hs1 : invDim s = 1) {u : OGroup Q} (huu : u * u = 1)
    (hsu : s * u = u * s) (hu : invType u = (4, 1)) :
    ∃ u₁ : OGroup (Q.restrict (fixSp s)), u₁ * u₁ = 1 ∧
      (invType u₁ = (4, 1) ∨ invType u₁ = (2, -1)) ∧
      (blockHom hss (u₁, 1) = u ∨ blockHom hss (u₁, 1) = piOrth Q * u) := by
  have hcdim : Module.finrank (ZMod 3) (commSp s) = 1 := hs1
  have hC := nondegenerate_restrict_commSp hQ hss
  have hcardC : Nat.card (OGroup (Q.restrict (commSp s))) = 2 :=
    natCard_oGroup_one hC hcdim
  have hπC_ne : piOrth (Q.restrict (commSp s)) ≠ 1 :=
    piOrth_ne_one (Q := Q.restrict (commSp s)) (by rw [hcdim]; norm_num)
  have hrange : u ∈ (blockHom hss).range := by
    rw [range_blockHom hQ hss, Subgroup.mem_centralizer_singleton_iff]
    exact hsu.symm
  obtain ⟨⟨p₁, p₂⟩, hp⟩ := hrange
  have hp₂ : p₂ = 1 ∨ p₂ = piOrth (Q.restrict (commSp s)) := by
    by_cases h1 : p₂ = 1
    · exact Or.inl h1
    · right
      obtain ⟨y, _, hy⟩ := (Nat.card_eq_two_iff' (1 : OGroup (Q.restrict (commSp s)))).mp hcardC
      rw [hy p₂ h1, ← hy _ hπC_ne]
  have key : ∀ {a : OGroup (Q.restrict (fixSp s))} {w : OGroup Q}, blockHom hss (a, 1) = w →
      w * w = 1 → a * a = 1 ∧ invType a = invType w := by
    intro a w hw hww
    have haa : a * a = 1 := by
      have h1 : blockHom hss (a * a, 1) = blockHom hss 1 := by
        rw [map_one]
        have h2 : ((a * a, (1 : OGroup (Q.restrict (commSp s)))) :
            OGroup (Q.restrict (fixSp s)) × OGroup (Q.restrict (commSp s))) =
            (a, 1) * (a, 1) := by
          rw [Prod.mk_mul_mk, one_mul]
        rw [h2, map_mul, hw, hww]
      exact congrArg Prod.fst (blockHom_injective hss h1)
    exact ⟨haa, by rw [← hw]; exact (ff_invType_blockHom_inl hQ hss haa).symm⟩
  rcases hp₂ with h1 | h2
  · have hu_eq : blockHom hss (p₁, 1) = u := by rw [← hp, h1]
    obtain ⟨hpp, hpt⟩ := key hu_eq huu
    exact ⟨p₁, hpp, Or.inl (hpt.trans hu), Or.inl hu_eq⟩
  · have hpiu : blockHom hss (piOrth (Q.restrict (fixSp s)) * p₁, 1) = piOrth Q * u := by
      have h3 : ((piOrth (Q.restrict (fixSp s)) * p₁, (1 : OGroup (Q.restrict (commSp s)))) :
          OGroup (Q.restrict (fixSp s)) × OGroup (Q.restrict (commSp s))) =
          (piOrth (Q.restrict (fixSp s)), piOrth (Q.restrict (commSp s))) * (p₁, p₂) := by
        rw [Prod.mk_mul_mk, h2, piOrth_mul_self]
      rw [h3, map_mul, blockHom_piOrth_piOrth, hp]
    obtain ⟨hpp, hpt⟩ := key hpiu (piOrth_mul_mul_self huu)
    have hd : invDim u = 4 := congrArg Prod.fst hu
    have hs : invSign u = 1 := congrArg Prod.snd hu
    have htype : invType (piOrth Q * u) = (2, -1) := by
      rw [invType_piOrth_mul hQ huu, hdim, hsgn, hd, hs]
      decide
    exact ⟨_, hpp, Or.inr (hpt.trans htype), Or.inr hpiu⟩

theorem sec5fb_geom (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {s : OGroup Q} (hss : s * s = 1) (hs1 : invDim s = 1)
    {u : OGroup Q} (huu : u * u = 1) (hsu : s * u = u * s) (hu : invType u = (4, 1)) :
    ∃ K Bb : Subgroup ↥(omegaGroup hQ),
      K ≤ fixSub (omegaConj hQ s) ∧
      (∀ p ∈ fixSub (omegaConj hQ s), ∀ k ∈ K, p * k * p⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
      Bb ≤ fixSub (omegaConj hQ s) ∧ IsElemAb2 Bb 5 ∧
      (∀ u' : ↥(omegaGroup hQ), (u' : OGroup Q) = u → u' ∈ Bb) ∧
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
  obtain ⟨u₁, hu₁u₁, hu₁type, hu₁⟩ :=
    sec5fb_exists_left_block hQ hdim hsgn hss hs1 huu hsu hu
  obtain ⟨E, hEsub, hEab, hu₁E⟩ := sec5fb_exists_E16_mem hR hW5 hu₁u₁ hu₁type
  obtain ⟨K, Bb, hKP, hKn, hKq, hBP, hB, hEBb, hgeom⟩ :=
    sec5fb_geom_of_E16 hQ hdim hsgn hss hs1 hEsub hEab
  refine ⟨K, Bb, hKP, hKn, hKq, hBP, hB, ?_, hgeom⟩
  intro u' hu'
  rcases hu₁ with h1 | h2
  · exact hEBb u₁ hu₁E u' (hu'.trans h1.symm)
  · have hpi_mem : piOrth Q ∈ omegaGroup hQ := by
      rw [piOrth_mem_omegaGroup_iff hQ]
      exact ⟨by rw [hdim]; decide, by rw [hdim, hsgn]; decide⟩
    let π₀ : ↥(omegaGroup hQ) := ⟨piOrth Q, hpi_mem⟩
    have hmem' : blockHom hss (u₁, 1) ∈ omegaGroup hQ :=
      blockHom_left_mem_omegaGroup hQ hss hW (hEsub hu₁E)
    let e' : ↥(omegaGroup hQ) := ⟨blockHom hss (u₁, 1), hmem'⟩
    have hπB : π₀ ∈ Bb := (hgeom π₀ rfl).1
    have he'B : e' ∈ Bb := hEBb u₁ hu₁E e' rfl
    have hu'eq : u' = π₀ * e' := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hu']
      show u = piOrth Q * blockHom hss (u₁, 1)
      rw [h2, ← mul_assoc, piOrth_mul_self, one_mul]
    rw [hu'eq]
    exact Bb.mul_mem hπB he'B

end CFSG.OddStandard.SmallF3.Omega
