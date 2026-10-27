module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.CSideFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Subgroup
open scoped commutatorElement

private abbrev a5g : Type := alternatingGroup (Fin 5)

private abbrev c2g : Type := Multiplicative (ZMod 2)

private abbrev wrBase : Subgroup A5WrTwo := (RegularWreathProduct.rightHom : A5WrTwo →* c2g).ker

private lemma mem_wrBase (g : A5WrTwo) : g ∈ wrBase ↔ g.right = 1 :=
  MonoidHom.mem_ker

private def sigmaC2 : c2g := Multiplicative.ofAdd (1 : ZMod 2)

private lemma c2_cases (q : c2g) : q = 1 ∨ q = sigmaC2 := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]
    rfl

private lemma sigmaC2_ne_one : sigmaC2 ≠ 1 := by decide

private lemma sigmaC2_inv : sigmaC2⁻¹ = sigmaC2 := by decide

private lemma sigmaC2_mul_self : sigmaC2 * sigmaC2 = 1 := by decide

private theorem isThreeCycle_swap :
    Equiv.Perm.IsThreeCycle (Equiv.swap (1 : Fin 5) 0 * Equiv.swap (1 : Fin 5) 2) :=
  Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := (1 : Fin 5)) (b := (0 : Fin 5))
    (c := (2 : Fin 5)) (by decide) (by decide) (by decide)

private def threeCycleD5 : a5g :=
  ⟨Equiv.swap (1 : Fin 5) 0 * Equiv.swap (1 : Fin 5) 2, isThreeCycle_swap.mem_alternatingGroup⟩

private lemma threeCycleD5_ne_one : threeCycleD5 ≠ 1 := by
  intro hc
  refine isThreeCycle_swap.ne_one ?_
  have := congrArg (Subtype.val) hc
  simpa [threeCycleD5] using this

private lemma orderOf_threeCycleD5 : orderOf threeCycleD5 = 3 := by
  rw [threeCycleD5, Subgroup.orderOf_mk]
  exact isThreeCycle_swap.orderOf

private theorem not_isPGroup_two_a5g : ¬ IsPGroup 2 a5g := by
  intro h
  have hdvd : 2 ∣ orderOf threeCycleD5 := h.dvd_orderOf threeCycleD5_ne_one
  rw [orderOf_threeCycleD5] at hdvd
  norm_num at hdvd

private def baseCoordHom (x : c2g) : wrBase →* a5g where
  toFun b := (b : A5WrTwo).left x
  map_one' := rfl
  map_mul' b c := by
    have hb : (b : A5WrTwo).right = 1 := (mem_wrBase _).mp b.2
    show ((b : A5WrTwo) * (c : A5WrTwo)).left x =
      (b : A5WrTwo).left x * (c : A5WrTwo).left x
    rw [RegularWreathProduct.mul_left, Pi.mul_apply, hb]
    congr 1
    congr 1
    rcases c2_cases x with rfl | rfl <;> decide

private def constEmb (d : a5g) : A5WrTwo := ⟨fun _ => d, 1⟩

private lemma constEmb_right (d : a5g) : (constEmb d).right = 1 := rfl

private lemma constEmb_mem_wrBase (d : a5g) : constEmb d ∈ wrBase :=
  (mem_wrBase _).mpr (constEmb_right d)

private lemma mul_base_mul_inv_left (z b : A5WrTwo) (hb : b.right = 1) (x : c2g) :
    (z * b * z⁻¹).left x = z.left x * b.left (z.right⁻¹ * x) * (z.left x)⁻¹ := by
  rw [RegularWreathProduct.mul_left, RegularWreathProduct.mul_left,
    RegularWreathProduct.inv_left]
  simp only [RegularWreathProduct.mul_right, hb, mul_one, Pi.mul_apply, Pi.inv_apply]
  rw [← mul_assoc, mul_inv_cancel, one_mul]
  rfl

private lemma constEmb_conj_left (d : a5g) (m : A5WrTwo) (hm : m.right = 1) (x : c2g) :
    (constEmb d * m * (constEmb d)⁻¹).left x = d * m.left x * d⁻¹ := by
  rw [mul_base_mul_inv_left (constEmb d) m hm x]
  have harg : ((constEmb d).right)⁻¹ * x = x := by
    rw [show (constEmb d).right = 1 from rfl]
    rcases c2_cases x with rfl | rfl <;> decide
  rw [harg, show (constEmb d).left x = d from rfl]

theorem A5WrTwo.eq_bot_of_normal_isPGroup (N : Subgroup A5WrTwo) [N.Normal] (hN : IsPGroup 2 N) :
    N = ⊥ := by
  have hleft : ∀ x : c2g, ∀ m : ↥(N ⊓ wrBase), (m : A5WrTwo).left x = 1 := by
    intro x
    let ψ : ↥(N ⊓ wrBase) →* a5g := (baseCoordHom x).comp
      (Subgroup.inclusion (inf_le_right : N ⊓ wrBase ≤ wrBase))
    have hpg : IsPGroup 2 ψ.range :=
      (hN.to_le inf_le_left).of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    have hnormal : ψ.range.Normal := by
      refine ⟨fun y hy d => ?_⟩
      obtain ⟨m, rfl⟩ := hy
      refine ⟨⟨constEmb d * (m : A5WrTwo) * (constEmb d)⁻¹, ?_, ?_⟩, ?_⟩
      · exact (inferInstance : N.Normal).conj_mem (m : A5WrTwo) m.2.1 (constEmb d)
      · exact wrBase.mul_mem (wrBase.mul_mem (constEmb_mem_wrBase d) m.2.2)
          (wrBase.inv_mem (constEmb_mem_wrBase d))
      · show (constEmb d * (m : A5WrTwo) * (constEmb d)⁻¹).left x =
          d * (m : A5WrTwo).left x * d⁻¹
        exact constEmb_conj_left d (m : A5WrTwo) ((mem_wrBase _).mp m.2.2) x
    have hbot : ψ.range = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.range with h | h
      · exact h
      · exfalso
        have htop : IsPGroup 2 (⊤ : Subgroup a5g) := h ▸ hpg
        exact not_isPGroup_two_a5g (htop.of_equiv Subgroup.topEquiv)
    intro m
    have hmem : ψ m ∈ (⊥ : Subgroup a5g) := by rw [← hbot]; exact ⟨m, rfl⟩
    exact Subgroup.mem_bot.mp hmem
  have hMbot : N ⊓ wrBase = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro m hm
    apply RegularWreathProduct.ext
    · funext x
      rcases c2_cases x with rfl | rfl
      · exact hleft 1 ⟨m, hm⟩
      · exact hleft sigmaC2 ⟨m, hm⟩
    · exact (mem_wrBase m).mp hm.2
  rw [Subgroup.eq_bot_iff_forall]
  intro n hnN
  by_contra hn1
  have hnB : n ∉ wrBase := by
    intro hb
    have hmem : n ∈ (⊥ : Subgroup A5WrTwo) := by
      rw [← hMbot]; exact ⟨hnN, hb⟩
    exact hn1 (Subgroup.mem_bot.mp hmem)
  have hnr : n.right = sigmaC2 := by
    rcases c2_cases n.right with h | h
    · exact absurd ((mem_wrBase n).mpr h) hnB
    · exact h
  have hNsub : ∀ m ∈ N, m = 1 ∨ m = n := by
    intro m hmN
    by_cases hmB : m ∈ wrBase
    · left
      have hmem : m ∈ (⊥ : Subgroup A5WrTwo) := by
        rw [← hMbot]; exact ⟨hmN, hmB⟩
      exact Subgroup.mem_bot.mp hmem
    · right
      have hmr : m.right = sigmaC2 := by
        rcases c2_cases m.right with h | h
        · exact absurd ((mem_wrBase m).mpr h) hmB
        · exact h
      have hmn : m * n⁻¹ ∈ N ⊓ wrBase := by
        refine ⟨N.mul_mem hmN (N.inv_mem hnN), ?_⟩
        show (m * n⁻¹).right = 1
        rw [RegularWreathProduct.mul_right, RegularWreathProduct.inv_right, hmr, hnr,
          mul_inv_cancel]
      have hmem : m * n⁻¹ ∈ (⊥ : Subgroup A5WrTwo) := by rw [← hMbot]; exact hmn
      exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)
  have hcentral : n ∈ Subgroup.center A5WrTwo := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hgn : g * n * g⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem n hnN g
    rcases hNsub (g * n * g⁻¹) hgn with h | h
    · exfalso
      have : n = 1 := by
        calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [h]
          _ = 1 := by group
      exact hn1 this
    · have : g * n = n * g := by
        have hh := congrArg (fun t => t * g) h
        simpa [mul_assoc] using hh
      exact this
  let b : A5WrTwo := ⟨fun x => if x = 1 then threeCycleD5 else 1, 1⟩
  have hb_base : b.right = 1 := rfl
  have hb1 : b.left 1 = threeCycleD5 := by simp [b]
  have hbs : b.left sigmaC2 = 1 := by simp [b, sigmaC2_ne_one]
  have hconj : n * b * n⁻¹ = b := by
    have hcomm : n * b = b * n := ((Subgroup.mem_center_iff.mp hcentral) b).symm
    calc n * b * n⁻¹ = b * n * n⁻¹ := by rw [hcomm]
      _ = b := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have h1 := mul_base_mul_inv_left n b hb_base 1
  rw [hconj, hb1, hnr, sigmaC2_inv, mul_one, hbs] at h1
  exact threeCycleD5_ne_one (by simpa using h1)

theorem IsExtraspecialPlusByA5WrTwoWith.pCore_eq {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]
    (h : IsExtraspecialPlusByA5WrTwoWith C Q) : CFSG.pCore 2 C = Q := by
  refine le_antisymm ?_ ?_
  ·
    let π : C →* C ⧸ Q := QuotientGroup.mk' Q
    obtain ⟨e⟩ := h.quotient
    have hmap : (CFSG.pCore 2 C).map π = ⊥ := by
      have hsub : ((CFSG.pCore 2 C).map π).map e.toMonoidHom = ⊥ := by
        haveI : ((CFSG.pCore 2 C).map π).Normal :=
          Subgroup.Normal.map (inferInstance : (CFSG.pCore 2 C).Normal) π
            (QuotientGroup.mk'_surjective Q)
        haveI : (((CFSG.pCore 2 C).map π).map e.toMonoidHom).Normal :=
          Subgroup.Normal.map ‹((CFSG.pCore 2 C).map π).Normal› e.toMonoidHom e.surjective
        exact A5WrTwo.eq_bot_of_normal_isPGroup _
          (((CFSG.pCore_isPGroup (p := 2) (G := C)).map π).map e.toMonoidHom)
      rwa [Subgroup.map_eq_bot_iff_of_injective (H := (CFSG.pCore 2 C).map π) e.injective]
        at hsub
    rw [Subgroup.map_eq_bot_iff] at hmap
    rwa [QuotientGroup.ker_mk'] at hmap
  ·
    have hQpg : IsPGroup 2 Q :=
      IsPGroup.of_card (n := 9) (by
        have hc := h.plus.2.1
        norm_num at hc ⊢
        exact hc)
    rw [CFSG.pCore]
    exact le_sSup ⟨inferInstance, hQpg⟩

theorem exists_Qz_eq {G : Type} [Group G] {w : G}
    (hw : IsExtraspecialPlusByA5WrTwo (Subgroup.centralizer ({w} : Set G))) :
    ∃ (Q : Subgroup ↥(Gx w)) (_ : Q.Normal), IsExtraspecialPlusByA5WrTwoWith ↥(Gx w) Q ∧
      Qz w = Q.map (Gx w).subtype := by
  obtain ⟨Q, hQ, hQW⟩ := hw
  refine ⟨Q, hQ, hQW, ?_⟩
  change (CFSG.pCore 2 ↥(Gx w)).map (Gx w).subtype = Q.map (Gx w).subtype
  rw [IsExtraspecialPlusByA5WrTwoWith.pCore_eq hQW]

private lemma gxy_eq_map_centralizer {G : Type} [Group G] {a w : G} (ha : a ∈ Gx w) :
    Gxy a w = (Subgroup.centralizer ({(⟨a, ha⟩ : ↥(Gx w))} : Set ↥(Gx w))).map
      (Gx w).subtype := by
  ext g
  rw [mem_Gxy]
  constructor
  · intro hg
    refine Subgroup.mem_map_of_mem (f := (Gx w).subtype)
      (K := Subgroup.centralizer ({(⟨a, ha⟩ : ↥(Gx w))} : Set ↥(Gx w)))
      (x := ⟨g, hg.2⟩) ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact (mem_Gx.mp hg.1).symm
  · intro hg
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
    have hgval : (y : G) = g := hyg
    constructor
    · rw [mem_Gx]
      have hy' := congrArg (fun t : ↥(Gx w) => (t : G))
        (Subgroup.mem_centralizer_singleton_iff.mp hy)
      rw [← hgval]
      exact hy'.symm
    · rw [← hgval]; exact y.2

private noncomputable def gxyMulEquivCentralizer {G : Type} [Group G] {a w : G} (ha : a ∈ Gx w) :
    ↥(Gxy a w) ≃* ↥(Subgroup.centralizer ({(⟨a, ha⟩ : ↥(Gx w))} : Set ↥(Gx w))) :=
  (MulEquiv.subgroupCongr (gxy_eq_map_centralizer ha)).trans
    (Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({(⟨a, ha⟩ : ↥(Gx w))} : Set ↥(Gx w)))
      (Gx w).subtype Subtype.coe_injective).symm

theorem mem_Qz_of_shape (hC : CSideFacts) {G : Type} [Group G] {w a : G}
    (hw : IsExtraspecialPlusByA5WrTwo (Subgroup.centralizer ({w} : Set G))) (ha : a ∈ Gx w)
    (ha2 : a ^ 2 = 1) (hsh : IsShapeTwoTwoSixS5 ↥(Gxy a w)) : a ∈ Qz w := by
  obtain ⟨Q, hQ, hQW, hQz⟩ := exists_Qz_eq hw
  haveI : Q.Normal := hQ
  have haQ : (⟨a, ha⟩ : ↥(Gx w)) ∈ Q :=
    hC.mem_Q_of_cent ↥(Gx w) Q hQW ⟨a, ha⟩
      (by ext; simpa using ha2)
      (IsShapeTwoTwoSixS5.of_mulEquiv (gxyMulEquivCentralizer ha) hsh)
  rw [hQz]
  exact Subgroup.mem_map_of_mem (Gx w).subtype haQ

private lemma eq_of_mem_center_of_card_two {Q : Type*} [Group Q]
    (hcard : Nat.card (Subgroup.center Q) = 2) {u v : Q}
    (hu : u ∈ Subgroup.center Q) (hv : v ∈ Subgroup.center Q) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    u = v := by
  obtain ⟨m, hm, huniq⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center Q)).mp hcard
  exact Subtype.ext_iff.mp ((huniq ⟨u, hu⟩ (by simpa using hu1)).trans
    (huniq ⟨v, hv⟩ (by simpa using hv1)).symm)

theorem isConj_mul_of_mem_Qz {G : Type} [Group G] {w a : G}
    (hw : IsExtraspecialPlusByA5WrTwo (Subgroup.centralizer ({w} : Set G))) (hw2 : orderOf w = 2)
    (ha2 : orderOf a = 2) (haw : a ≠ w) (haQ : a ∈ Qz w) : IsConj a (a * w) := by
  obtain ⟨Q, hQ, hQW, hQz⟩ := exists_Qz_eq hw
  haveI : Q.Normal := hQ
  have hwmem : w ∈ Gx w := self_mem_Gx w
  have hwC_cent : (⟨w, hwmem⟩ : ↥(Gx w)) ∈ Subgroup.centralizer (Q : Set ↥(Gx w)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q _
    apply Subtype.ext
    exact (mem_Gx.mp q.2).symm
  have hwQmem : (⟨w, hwmem⟩ : ↥(Gx w)) ∈ Q := hQW.centralizer_le hwC_cent
  obtain ⟨q, hqQ, hqa⟩ := Subgroup.mem_map.mp (by rwa [hQz] at haQ)
  have haC : a ∈ Gx w := by rw [← hqa]; exact q.2
  have haQmem : (⟨a, haC⟩ : ↥(Gx w)) ∈ Q := by
    rw [show (⟨a, haC⟩ : ↥(Gx w)) = q from Subtype.ext hqa.symm]
    exact hqQ
  let Qgrp := ↥Q
  let wQ : Qgrp := ⟨⟨w, hwmem⟩, hwQmem⟩
  let aQ : Qgrp := ⟨⟨a, haC⟩, haQmem⟩
  haveI hExt : CFSG.IsExtraspecial 2 Qgrp := hQW.plus.1
  have hcard : Nat.card (Subgroup.center Qgrp) = 2 := hExt.center_order_p
  have hwQ_ne : wQ ≠ 1 := by
    intro h1
    have hw1 : w = 1 := by simpa [wQ] using congrArg (fun t : Qgrp => ((t : ↥(Gx w)) : G)) h1
    have : orderOf w = 1 := orderOf_eq_one_iff.mpr hw1
    omega
  have haQ_ne : aQ ≠ 1 := by
    intro h1
    have ha1 : a = 1 := by simpa [aQ] using congrArg (fun t : Qgrp => ((t : ↥(Gx w)) : G)) h1
    have : orderOf a = 1 := orderOf_eq_one_iff.mpr ha1
    omega
  have hwQ_cent : wQ ∈ Subgroup.center Qgrp := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact (mem_Gx.mp x.1.2).symm
  have haQ_not_cent : aQ ∉ Subgroup.center Qgrp := by
    intro h
    exact haw (by
      have hEq : aQ = wQ := eq_of_mem_center_of_card_two hcard h hwQ_cent haQ_ne hwQ_ne
      simpa [aQ, wQ] using congrArg (fun t : Qgrp => ((t : ↥(Gx w)) : G)) hEq)
  have hcomm_le : _root_.commutator Qgrp ≤ Subgroup.center Qgrp := by
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    haveI := hExt.quotient_elementary_abelian
    infer_instance
  have hex : ∃ z : Qgrp, ⁅z, aQ⁆ ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact haQ_not_cent (by
      rw [Subgroup.mem_center_iff]
      intro x
      rw [← commutatorElement_eq_one_iff_mul_comm]
      exact h x)
  obtain ⟨z, hz⟩ := hex
  have hz_center : ⁅z, aQ⁆ ∈ Subgroup.center Qgrp :=
    hcomm_le (Subgroup.commutator_mem_commutator (Subgroup.mem_top z) (Subgroup.mem_top aQ))
  have hz_eq : ⁅z, aQ⁆ = wQ :=
    eq_of_mem_center_of_card_two hcard hz_center hwQ_cent hz hwQ_ne
  rw [isConj_iff]
  refine ⟨((z : ↥(Gx w)) : G), ?_⟩
  have hconj : z * aQ * z⁻¹ = aQ * wQ := by
    rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul, hz_eq]
    exact (Subgroup.mem_center_iff.mp hwQ_cent aQ).symm
  have hcong : ((Gx w).subtype.comp Q.subtype) (z * aQ * z⁻¹) =
      ((Gx w).subtype.comp Q.subtype) (aQ * wQ) :=
    congrArg ((Gx w).subtype.comp Q.subtype) hconj
  simp only [map_mul, map_inv] at hcong
  simpa [aQ, wQ] using hcong

private lemma natCard_Elem2 (n : ℕ) : Nat.card (Elem2 n) = 2 ^ n := by
  rw [Elem2, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, Nat.card_zmod]

private theorem perm5_normal (M : Subgroup (Equiv.Perm (Fin 5))) [M.Normal] :
    M = ⊥ ∨ alternatingGroup (Fin 5) ≤ M := by
  by_cases h : M = ⊥
  · exact Or.inl h
  · exact Or.inr (Equiv.Perm.alternatingGroup_le_of_normal (by simp)
      ((Subgroup.nontrivial_iff_ne_bot M).2 h))

private theorem eq_bot_of_normal_isPGroup_perm5 (M : Subgroup (Equiv.Perm (Fin 5))) [M.Normal]
    (hM : IsPGroup 2 M) : M = ⊥ := by
  rcases perm5_normal M with h | h
  · exact h
  · exact absurd (IsPGroup.of_injective hM (Subgroup.inclusion h)
      (Subgroup.inclusion_injective h)) not_isPGroup_two_a5g

private lemma pCore_le_of_normal_quotient_perm5 {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (hq : Nonempty (X ⧸ N ≃* Equiv.Perm (Fin 5))) : CFSG.pCore 2 X ≤ N := by
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  obtain ⟨e⟩ := hq
  have hmap : (CFSG.pCore 2 X).map π = ⊥ := by
    haveI : ((CFSG.pCore 2 X).map π).Normal :=
      Subgroup.Normal.map (inferInstance : (CFSG.pCore 2 X).Normal) π
        (QuotientGroup.mk'_surjective N)
    have hsub : ((CFSG.pCore 2 X).map π).map e.toMonoidHom = ⊥ := by
      haveI : (((CFSG.pCore 2 X).map π).map e.toMonoidHom).Normal :=
        Subgroup.Normal.map ‹((CFSG.pCore 2 X).map π).Normal› e.toMonoidHom e.surjective
      exact eq_bot_of_normal_isPGroup_perm5 _
        (((CFSG.pCore_isPGroup (p := 2) (G := X)).map π).map e.toMonoidHom)
    rwa [Subgroup.map_eq_bot_iff_of_injective (H := (CFSG.pCore 2 X).map π) e.injective] at hsub
  rw [Subgroup.map_eq_bot_iff] at hmap
  rwa [QuotientGroup.ker_mk'] at hmap

private lemma card_centralizer_extraspecial {H : Type*} [Group H] [Finite H]
    (hcent : Nat.card (Subgroup.center H) = 2)
    (hcomm : _root_.commutator H ≤ Subgroup.center H)
    (hcard : Nat.card H = 2 ^ 9) {a : H} (ha_not_cent : a ∉ Subgroup.center H) :
    Nat.card (Subgroup.centralizer ({a} : Set H)) = 2 ^ 8 := by
  obtain ⟨w, hw, huniq⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center H)).mp hcent
  have hw1 : (w : H) ≠ 1 := fun h => hw (Subtype.ext h)
  have hcenter : ∀ c : H, c ∈ Subgroup.center H → c ≠ 1 → c = (w : H) := fun c hc hc1 =>
    Subtype.ext_iff.mp (huniq ⟨c, hc⟩ (by simpa using hc1))
  have hcomm_u : ∀ c : H, c * a * c⁻¹ = a ∨ c * a * c⁻¹ = (w : H) * a := by
    intro c
    have hc : ⁅c, a⁆ ∈ Subgroup.center H :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top c) (Subgroup.mem_top a))
    have key : c * a * c⁻¹ = ⁅c, a⁆ * a := by
      rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]
    rcases eq_or_ne ⁅c, a⁆ 1 with h1 | h1
    · left; rw [key, h1, one_mul]
    · right; rw [key, hcenter _ hc h1]
  have hnc : ∃ c : H, c * a * c⁻¹ ≠ a := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    refine ha_not_cent ?_
    rw [Subgroup.mem_center_iff]
    intro x
    rw [← commutatorElement_eq_one_iff_mul_comm]
    have h := hcon x
    rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul] at h
    calc ⁅x, a⁆ = ⁅x, a⁆ * a * a⁻¹ := by group
      _ = a * a⁻¹ := by rw [h]
      _ = 1 := by group
  have hne : a ≠ (w : H) * a := by
    intro h
    have h1 : (w : H) = 1 := by
      have h' := congrArg (fun t => t * a⁻¹) h
      simpa [mul_assoc] using h'.symm
    exact hw1 h1
  have hclass : conjugatesOf a = {a, (w : H) * a} := by
    ext b
    constructor
    · intro hb
      obtain ⟨c, hc⟩ := isConj_iff.mp hb
      rcases hcomm_u c with h | h
      · left; exact hc.symm.trans h
      · right; exact hc.symm.trans h
    · intro hb
      rcases hb with rfl | rfl
      · exact mem_conjugatesOf_self
      · obtain ⟨c, hc⟩ := hnc
        rcases hcomm_u c with h | h
        · exact absurd h hc
        · exact isConj_iff.mpr ⟨c, h⟩
  have hindex : (Subgroup.centralizer ({a} : Set H)).index = 2 := by
    rw [Subgroup.index_centralizer_eq_ncard, hclass, Set.ncard_pair hne]
  have hmain := Subgroup.card_mul_index (Subgroup.centralizer ({a} : Set H))
  rw [hindex, hcard] at hmain
  omega

theorem pCoreOf_Gxy_eq {G : Type} [Group G] {w a : G}
    (hw : IsExtraspecialPlusByA5WrTwo (Subgroup.centralizer ({w} : Set G))) (hw2 : orderOf w = 2)
    (ha2 : orderOf a = 2) (haw : a ≠ w) (haQ : a ∈ Qz w) (hsh : IsShapeTwoTwoSixS5 ↥(Gxy a w)) :
    CFSG.Open.pCoreOf 2 (Gxy a w) = Qz w ⊓ Gx a := by
  obtain ⟨Q, hQ, hQW, hQz⟩ := exists_Qz_eq hw
  haveI : Q.Normal := hQ
  have hExtQ : CFSG.IsExtraspecial 2 ↥Q := hQW.plus.1
  have hQcard : Nat.card Q = 2 ^ 9 := by
    have hc := hQW.plus.2.1
    norm_num at hc ⊢
    exact hc
  have hwmem : w ∈ Gx w := self_mem_Gx w
  have hwC_cent : (⟨w, hwmem⟩ : ↥(Gx w)) ∈ Subgroup.centralizer (Q : Set ↥(Gx w)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q _
    apply Subtype.ext
    exact (mem_Gx.mp q.2).symm
  have hwQmem : (⟨w, hwmem⟩ : ↥(Gx w)) ∈ Q := hQW.centralizer_le hwC_cent
  have hwQz : w ∈ Qz w := by
    rw [hQz]
    exact Subgroup.mem_map_of_mem (Gx w).subtype hwQmem
  have hQz_le : Qz w ≤ Gx w := by
    rw [hQz]
    exact Subgroup.map_subtype_le (H := Gx w) Q
  have hExtQz : CFSG.IsExtraspecial 2 ↥(Qz w) := by
    rw [hQz]
    exact TwoHSData.isExtraspecial_of_mulEquiv
      (Subgroup.equivMapOfInjective Q (Gx w).subtype Subtype.coe_injective) hExtQ
  have hQzcard : Nat.card ↥(Qz w) = 2 ^ 9 := by
    rw [hQz, ← Nat.card_congr (Subgroup.equivMapOfInjective Q (Gx w).subtype
      Subtype.coe_injective).toEquiv]
    exact hQcard
  have hL_le : Qz w ⊓ Gx a ≤ Gxy a w := by
    calc Qz w ⊓ Gx a ≤ Gx w ⊓ Gx a := inf_le_inf hQz_le le_rfl
      _ = Gx a ⊓ Gx w := inf_comm _ _
      _ = Gxy a w := (Gxy_eq_inf a w).symm
  have hge : Qz w ⊓ Gx a ≤ CFSG.Open.pCoreOf 2 (Gxy a w) := by
    have hK_normal : ((Qz w ⊓ Gx a).subgroupOf (Gxy a w)).Normal := by
      refine ⟨fun k hk x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      refine ⟨?_, ?_⟩
      · have hxw : (x : G) ∈ Gx w := (mem_Gxy.mp x.2).2
        have hkw : (k : G) ∈ Gx w := hQz_le hk.1
        have hkp : (⟨k, hkw⟩ : ↥(Gx w)) ∈ Q := by
          rw [hQz] at hk
          obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp hk.1
          have hyk' : y = ⟨k, hkw⟩ := Subtype.ext hyk
          rwa [hyk'] at hy
        have hconjQ : (⟨x, hxw⟩ : ↥(Gx w)) * ⟨k, hkw⟩ * (⟨x, hxw⟩ : ↥(Gx w))⁻¹ ∈ Q :=
          hQ.conj_mem _ hkp _
        rw [hQz]
        exact Subgroup.mem_map_of_mem (Gx w).subtype hconjQ
      · exact (Gx a).mul_mem ((Gx a).mul_mem (mem_Gxy.mp x.2).1 hk.2)
          ((Gx a).inv_mem (mem_Gxy.mp x.2).1)
    have hK_pg : IsPGroup 2 ((Qz w ⊓ Gx a).subgroupOf (Gxy a w)) := by
      have hQz_pg : IsPGroup 2 (Qz w) := by
        rw [hQz]
        exact hExtQ.isPGroup.map (Gx w).subtype
      have hKmap_le : ((Qz w ⊓ Gx a).subgroupOf (Gxy a w)).map (Gxy a w).subtype ≤ Qz w := by
        rw [Subgroup.subgroupOf_map_subtype]
        exact le_trans inf_le_left inf_le_left
      have hKmap_pg : IsPGroup 2 (((Qz w ⊓ Gx a).subgroupOf (Gxy a w)).map
          (Gxy a w).subtype) := hQz_pg.to_le hKmap_le
      exact hKmap_pg.of_equiv (Subgroup.equivMapOfInjective _ (Gxy a w).subtype
        Subtype.coe_injective).symm
    have hK_le : (Qz w ⊓ Gx a).subgroupOf (Gxy a w) ≤ CFSG.pCore 2 ↥(Gxy a w) := by
      rw [CFSG.pCore]
      exact le_sSup ⟨hK_normal, hK_pg⟩
    have hmap := Subgroup.map_mono (f := (Gxy a w).subtype) hK_le
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hL_le] at hmap
    exact hmap
  have hle : CFSG.Open.pCoreOf 2 (Gxy a w) ≤ Qz w ⊓ Gx a := by
    obtain ⟨V, N, hVnorm, hNnorm, hVN, hVshape, hNVshape, hXshape⟩ := hsh
    haveI : V.Normal := hVnorm
    haveI : N.Normal := hNnorm
    have hpCoreN : CFSG.pCore 2 ↥(Gxy a w) ≤ N :=
      pCore_le_of_normal_quotient_perm5 hXshape
    have hNcard : Nat.card N = 2 ^ 8 := by
      have hVcard : Nat.card V = 2 ^ 2 := by
        obtain ⟨e⟩ := hVshape
        rw [Nat.card_congr e.toEquiv, natCard_Elem2]
      have hNVcard : Nat.card (N ⧸ V.subgroupOf N) = 2 ^ 6 := by
        obtain ⟨e⟩ := hNVshape
        rw [Nat.card_congr e.toEquiv, natCard_Elem2]
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf N)
      have hVsub : Nat.card (V.subgroupOf N) = Nat.card V :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv
      rw [h1, hNVcard, hVsub, hVcard]
      norm_num
    have hNmap_card : Nat.card (N.map (Gxy a w).subtype) = 2 ^ 8 := by
      rw [← hNcard]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective N (Gxy a w).subtype
        Subtype.coe_injective).toEquiv).symm
    have hRle : CFSG.Open.pCoreOf 2 (Gxy a w) ≤ N.map (Gxy a w).subtype :=
      Subgroup.map_mono (f := (Gxy a w).subtype) hpCoreN
    have hLcard : Nat.card ↥(Qz w ⊓ Gx a) = 2 ^ 8 := by
      haveI : Finite ↥(Qz w) := Nat.finite_of_card_ne_zero (by rw [hQzcard]; norm_num)
      have hcentQz : Nat.card (Subgroup.center ↥(Qz w)) = 2 := hExtQz.center_order_p
      have hcommQz : _root_.commutator ↥(Qz w) ≤ Subgroup.center ↥(Qz w) := by
        rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
        haveI := hExtQz.quotient_elementary_abelian
        infer_instance
      have hwHz : (⟨w, hwQz⟩ : ↥(Qz w)) ∈ Subgroup.center ↥(Qz w) := by
        rw [Subgroup.mem_center_iff]
        intro x
        apply Subtype.ext
        exact (mem_Gx.mp (hQz_le x.2)).symm
      have hwHz1 : (⟨w, hwQz⟩ : ↥(Qz w)) ≠ 1 := by
        intro h
        have h1 : w = 1 := by simpa using congrArg (fun t : ↥(Qz w) => (t : G)) h
        have : orderOf w = 1 := orderOf_eq_one_iff.mpr h1
        omega
      have haW1 : (⟨a, haQ⟩ : ↥(Qz w)) ≠ 1 := by
        intro h
        have h1 : a = 1 := by simpa using congrArg (fun t : ↥(Qz w) => (t : G)) h
        have : orderOf a = 1 := orderOf_eq_one_iff.mpr h1
        omega
      have haW_not_cent : (⟨a, haQ⟩ : ↥(Qz w)) ∉ Subgroup.center ↥(Qz w) := by
        intro hmem
        have heq : (⟨a, haQ⟩ : ↥(Qz w)) = ⟨w, hwQz⟩ :=
          eq_of_mem_center_of_card_two hcentQz hmem hwHz haW1 hwHz1
        have h1 : a = w := by simpa using congrArg (fun t : ↥(Qz w) => (t : G)) heq
        exact haw h1
      have hcent_card := card_centralizer_extraspecial hcentQz hcommQz hQzcard haW_not_cent
      have hLmap : Qz w ⊓ Gx a =
          (Subgroup.centralizer ({(⟨a, haQ⟩ : ↥(Qz w))} : Set ↥(Qz w))).map
            (Qz w).subtype := by
        ext g
        constructor
        · intro hg
          refine Subgroup.mem_map_of_mem (f := (Qz w).subtype)
            (K := Subgroup.centralizer ({(⟨a, haQ⟩ : ↥(Qz w))} : Set ↥(Qz w)))
            (x := ⟨g, hg.1⟩) ?_
          rw [Subgroup.mem_centralizer_singleton_iff]
          apply Subtype.ext
          exact (mem_Gx.mp hg.2).symm
        · intro hg
          obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
          have hgval : (y : G) = g := hyg
          exact ⟨by rw [← hgval]; exact y.2, by
            rw [← hgval]
            have hy' := congrArg (fun t : ↥(Qz w) => (t : G))
              (Subgroup.mem_centralizer_singleton_iff.mp hy)
            exact mem_Gx.mpr hy'.symm⟩
      rw [hLmap, ← Nat.card_congr (Subgroup.equivMapOfInjective
        (Subgroup.centralizer ({(⟨a, haQ⟩ : ↥(Qz w))} : Set ↥(Qz w)))
        (Qz w).subtype Subtype.coe_injective).toEquiv]
      exact hcent_card
    haveI : Finite ↥(N.map (Gxy a w).subtype) :=
      Nat.finite_of_card_ne_zero (by rw [hNmap_card]; norm_num)
    haveI : Finite ↥(CFSG.Open.pCoreOf 2 (Gxy a w)) :=
      Finite.of_injective (Subgroup.inclusion hRle) (Subgroup.inclusion_injective hRle)
    have hRcard_le : Nat.card ↥(CFSG.Open.pCoreOf 2 (Gxy a w)) ≤ Nat.card ↥(Qz w ⊓ Gx a) := by
      rw [hLcard]
      exact le_trans (Subgroup.card_le_of_le hRle) (le_of_eq hNmap_card)
    exact le_of_eq (Subgroup.eq_of_le_of_card_ge hge hRcard_le).symm
  exact le_antisymm hle hge

end CFSG.EvenSporadicStandard.HNRecog.Section3
