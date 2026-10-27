module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264B
public import CFSG.ClassicalInvolution.Q3.TL3T36
public import CFSG.ClassicalInvolution.Q3.TL4OddFrLinkP

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {P : Set (Subgroup G)} {n : ℕ}

theorem AEIdent.map_ker_eq (hn : 5 ≤ n) (I : AEIdent P n) (f : MulAut ↥(pSpan P)) :
    I.toModel.ker.map f.toMonoidHom = I.toModel.ker := by
  have hc : I.toModel.ker = Subgroup.center ↥(pSpan P) := by
    rw [I.ker_toModel]
    exact le_antisymm I.ker_le (I.center_le_ker hn)
  rw [hc]
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc', rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_center_iff] at hc' ⊢
    intro w
    have := hc' (f.symm w)
    show w * f c = f c * w
    calc w * f c = f (f.symm w * c) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = f (c * f.symm w) := by rw [this]
      _ = f c * w := by rw [map_mul, MulEquiv.apply_symm_apply]
  · intro hx
    refine Subgroup.mem_map.mpr ⟨f.symm x, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro w
    apply f.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx (f w)

@[expose] noncomputable def AEIdent.inducedAutOf (hn : 5 ≤ n) (I : AEIdent P n)
    (f : MulAut ↥(pSpan P)) : MulAut ↥(TL4.aeModel n) :=
  ((QuotientGroup.quotientKerEquivOfSurjective I.toModel I.toModel_surjective).symm.trans
    (QuotientGroup.congr I.toModel.ker I.toModel.ker f (I.map_ker_eq hn f))).trans
    (QuotientGroup.quotientKerEquivOfSurjective I.toModel I.toModel_surjective)

theorem AEIdent.inducedAutOf_apply (hn : 5 ≤ n) (I : AEIdent P n) (f : MulAut ↥(pSpan P))
    (x : ↥(pSpan P)) : I.inducedAutOf hn f (I.toModel x) = I.toModel (f x) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective I.toModel I.toModel_surjective).symm
      (I.toModel x) = (x : ↥(pSpan P) ⧸ I.toModel.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show (QuotientGroup.quotientKerEquivOfSurjective I.toModel I.toModel_surjective)
    (QuotientGroup.congr I.toModel.ker I.toModel.ker f (I.map_ker_eq hn f)
      ((QuotientGroup.quotientKerEquivOfSurjective I.toModel I.toModel_surjective).symm
        (I.toModel x))) = I.toModel (f x)
  rw [h1]
  rfl

theorem AEIdent.inducedAutOf_pow_apply (hn : 5 ≤ n) (I : AEIdent P n) (f : MulAut ↥(pSpan P))
    (k : ℕ) (x : ↥(pSpan P)) :
    (I.inducedAutOf hn f ^ k) (I.toModel x) = I.toModel ((f ^ k) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ' (I.inducedAutOf hn f) k, MulAut.mul_apply, ih, I.inducedAutOf_apply hn f,
      pow_succ' f k, MulAut.mul_apply]

theorem AEIdent.inducedAutOf_pow_eq_one (hn : 5 ≤ n) (I : AEIdent P n) {f : MulAut ↥(pSpan P)}
    {k : ℕ} (hk : f ^ k = 1) : I.inducedAutOf hn f ^ k = 1 := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := I.toModel_surjective y
  rw [I.inducedAutOf_pow_apply hn f, hk]
  rfl

end CFSG.ClassicalInvolution.Q3.TC.Thin

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent memBar_le_aeModel)

section Cit3


variable {r n m : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem map_linkGrp_secAct (hL : TightLargeHypR r n Y R S t) {y : Y}
    (hy : y ∈ Subgroup.centralizer ({t} : Set Y)) :
    (pSpan (coreLinkFam R t)).map
        (secAct (conjInvariant_conjClass (tightCore R)) hy).toMonoidHom =
      pSpan (coreLinkFam R t) := by
  set σ := secAct (conjInvariant_conjClass (tightCore R)) hy with hσ
  have hle : (pSpan (coreLinkFam R t)).map σ.toMonoidHom ≤ pSpan (coreLinkFam R t) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine TC.Thin.pSpan_le fun Lb hLb => ?_
    obtain ⟨J, hJ, rfl⟩ := hLb
    rw [← Subgroup.map_le_iff_le_comap, hσ,
      ← secImg_conjSub_eq_map (conjInvariant_conjClass (tightCore R)) hy J]
    exact le_pSpan ⟨conjSub y J, conjSub_mem_omegaNbr_core hL hJ hy, rfl⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  exact (Subgroup.card_map_of_injective (K := pSpan (coreLinkFam R t)) (f := σ.toMonoidHom)
    (fun a b hab => σ.injective hab)).ge

@[expose] noncomputable def linkAct (hL : TightLargeHypR r n Y R S t) {y : Y}
    (hy : y ∈ Subgroup.centralizer ({t} : Set Y)) : MulAut ↥(pSpan (coreLinkFam R t)) :=
  ((secAct (conjInvariant_conjClass (tightCore R)) hy).subgroupMap
    (pSpan (coreLinkFam R t))).trans (MulEquiv.subgroupCongr (map_linkGrp_secAct hL hy))

theorem coe_linkAct (hL : TightLargeHypR r n Y R S t) {y : Y}
    (hy : y ∈ Subgroup.centralizer ({t} : Set Y)) (x : ↥(pSpan (coreLinkFam R t))) :
    ((linkAct hL hy x : ↥(pSpan (coreLinkFam R t))) :
      SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      secAct (conjInvariant_conjClass (tightCore R)) hy x :=
  rfl

theorem coe_linkAct_pow (hL : TightLargeHypR r n Y R S t) {y : Y}
    (hy : y ∈ Subgroup.centralizer ({t} : Set Y)) (k : ℕ) (x : ↥(pSpan (coreLinkFam R t))) :
    (((linkAct hL hy ^ k) x : ↥(pSpan (coreLinkFam R t))) :
      SecQuot (CoreAssembly.conjClass (tightCore R)) t) =
      (secAct (conjInvariant_conjClass (tightCore R)) hy ^ k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ' (linkAct hL hy) k, MulAut.mul_apply, coe_linkAct, ih,
      pow_succ' (secAct (conjInvariant_conjClass (tightCore R)) hy) k, MulAut.mul_apply]

theorem linkAct_pow_eq_one (hL : TightLargeHypR r n Y R S t) {y : Y}
    (hy : y ∈ Subgroup.centralizer ({t} : Set Y)) {k : ℕ} (hk : y ^ k = 1) :
    linkAct hL hy ^ k = 1 := by
  have hσ : secAct (conjInvariant_conjClass (tightCore R)) hy ^ k = 1 := by
    show s26Act _ _ ^ k = 1
    rw [← map_pow]
    convert map_one (s26Act (layerY (CoreAssembly.conjClass (tightCore R)) t))
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hk)
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [coe_linkAct_pow, hσ]
  rfl

theorem inducedAutOf_linkAct_memberPerm (hL : TightLargeHypR r n Y R S t) (hm : 5 ≤ m)
    (I : AEIdent (coreLinkFam R t) m) {y : Y} (hy : y ∈ Subgroup.centralizer ({t} : Set Y))
    (α : Finset (Fin m)) (h : α.card = 4) (b : Bool) :
    ∃ (α' : Finset (Fin m)) (h' : α'.card = 4) (b' : Bool),
      ((AE.memBar α h b).subgroupOf ((AE.aeSub m).map (AE.mkQ m))).map
          (I.inducedAutOf hm (linkAct hL hy)).toMonoidHom =
        (AE.memBar α' h' b').subgroupOf ((AE.aeSub m).map (AE.mkQ m)) := by
  obtain ⟨_, ⟨L, hL', rfl⟩, hlab⟩ := I.label_surj α h b
  have hL₂ := conjSub_mem_omegaNbr_core hL hL' hy
  obtain ⟨α', h', b', hlab₂⟩ := I.label _ ⟨conjSub y L, hL₂, rfl⟩
  refine ⟨α', h', b', ?_⟩
  set β := I.inducedAutOf hm (linkAct hL hy) with hβ
  have hle : ((AE.memBar α h b).subgroupOf ((AE.aeSub m).map (AE.mkQ m))).map β.toMonoidHom ≤
      (AE.memBar α' h' b').subgroupOf ((AE.aeSub m).map (AE.mkQ m)) := by
    intro z hz
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    rw [← hlab] at hg
    obtain ⟨l, hl, hlg⟩ := hg
    have hgl : g = I.toModel l := Subtype.ext hlg.symm
    rw [hgl, MulEquiv.coe_toMonoidHom, hβ, I.inducedAutOf_apply hm, ← hlab₂]
    refine Subgroup.mem_map.mpr ⟨linkAct hL hy l, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, coe_linkAct,
      secImg_conjSub_eq_map (conjInvariant_conjClass (tightCore R)) hy L]
    exact ⟨(l : SecQuot (CoreAssembly.conjClass (tightCore R)) t),
      Subgroup.mem_subgroupOf.mp hl, rfl⟩
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  rw [Subgroup.card_map_of_injective (fun a b hab => β.injective hab),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (memBar_le_aeModel α' h' b')).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (memBar_le_aeModel α h b)).toEquiv,
    AE.natCard_memBar hm, AE.natCard_memBar hm]

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
