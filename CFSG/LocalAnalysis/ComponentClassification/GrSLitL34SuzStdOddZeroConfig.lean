module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroClean
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2Conj

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

omit [Finite G] in
private theorem exists_mem_ne_one_of_card_four {V : Subgroup G} (hV : Nat.card V = 4) :
    ∃ v ∈ V, v ≠ 1 := by
  have hne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hV
    omega
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨v, hv, fun h => hv1 (Subtype.ext h)⟩

omit [Finite G] in
private theorem isQuasisimple_left_of_l34SuzOddZero {P : Subgroup G}
    (hD : L34SuzOddData A V K y)
    (hcomp : ∀ v ∈ V, v ≠ 1 → P ≤ centralizer ({v} : Set G) ∧
      IsComponent (P.subgroupOf (centralizer ({v} : Set G)))) :
    IsQuasisimple ↥P := by
  obtain ⟨v, hv, hv1⟩ := exists_mem_ne_one_of_card_four hD.card_V
  exact (IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe (hcomp v hv hv1).1)).mp
    (hcomp v hv hv1).2.1

omit [Finite G] in
private theorem isQuasisimple_right_of_l34SuzOddZero {P : Subgroup G}
    (hPq : IsQuasisimple ↥P) :
    IsQuasisimple ↥(P.map (MulAut.conj t).toMonoidHom) :=
  (IsQuasisimple.congr (P.equivMapOfInjective (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective)).mp hPq

omit [Finite G] in
private theorem odd_card_center_right_of_l34SuzOddZero {P : Subgroup G}
    (hodd : Odd (Nat.card (center ↥P))) :
    Odd (Nat.card (center ↥(P.map (MulAut.conj t).toMonoidHom))) := by
  let e : ↥P ≃* ↥(P.map (MulAut.conj t).toMonoidHom) :=
    P.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
  rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact hodd

omit [Finite G] in
private theorem isL34Type_right_of_l34SuzOddZero {P : Subgroup G}
    (h : IsL34Type (↥P ⧸ center ↥P)) :
    IsL34Type (↥(P.map (MulAut.conj t).toMonoidHom) ⧸
      center ↥(P.map (MulAut.conj t).toMonoidHom)) := by
  let e : ↥P ≃* ↥(P.map (MulAut.conj t).toMonoidHom) :=
    P.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
  exact LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr (Subgroup.center ↥P)
      (Subgroup.center ↥(P.map (MulAut.conj t).toMonoidHom)) e (Subgroup.map_center_eq e)) h

omit [Finite G] in
private theorem isL34Type_left_of_l34SuzOddZero {P : Subgroup G}
    (hD : L34SuzOddData A V K y)
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hK : K = (HarrisLit.swapDiag P t hc).range) (hPq : IsQuasisimple ↥P) :
    IsL34Type (↥P ⧸ center ↥P) := by
  obtain ⟨e⟩ :=
    CFSG.OddStandard.HigherRank.F3.nonempty_quotCenter_equiv_swapDiag hc hPq
  rw [← hK] at e
  exact LieType.CurtisTits.lieModel_of_mulEquiv e.symm hD.l34

private theorem le_centralizer_right_of_l34SuzOddZero {P : Subgroup G}
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    (hV : V ≤ centralizer (P : Set G)) :
    V ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hq
  have hvt : t * v = v * t :=
    (Subgroup.mem_centralizer_iff.mp hS.t_mem v (hD.le_A hv)).symm
  have hvp : v * p = p * v :=
    (Subgroup.mem_centralizer_iff.mp (hV hv) p hp).symm
  have hvt' : t⁻¹ * v = v * t⁻¹ := (Commute.inv_left hvt).eq
  show (t * p * t⁻¹) * v = v * (t * p * t⁻¹)
  calc (t * p * t⁻¹) * v = t * p * (t⁻¹ * v) := by group
    _ = t * p * (v * t⁻¹) := by rw [hvt']
    _ = t * (p * v) * t⁻¹ := by group
    _ = t * (v * p) * t⁻¹ := by rw [hvp]
    _ = (t * v) * p * t⁻¹ := by group
    _ = (v * t) * p * t⁻¹ := by rw [hvt]
    _ = v * (t * p * t⁻¹) := by group

private theorem isComponent_right_of_l34SuzOddZero {P : Subgroup G}
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    (hV : V ≤ centralizer (P : Set G))
    (hcomp : ∀ v ∈ V, v ≠ 1 → P ≤ centralizer ({v} : Set G) ∧
      IsComponent (P.subgroupOf (centralizer ({v} : Set G)))) :
    ∀ v ∈ V, v ≠ 1 →
      (P.map (MulAut.conj t).toMonoidHom : Subgroup G) ≤ centralizer ({v} : Set G) ∧
        IsComponent ((P.map (MulAut.conj t).toMonoidHom).subgroupOf
          (centralizer ({v} : Set G))) := by
  intro v hv hv1
  have hQv : (P.map (MulAut.conj t).toMonoidHom : Subgroup G) ≤
      centralizer ({v} : Set G) := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp
        (le_centralizer_right_of_l34SuzOddZero hS hD hV hv) x hx)
  have htv : t * v = v * t :=
    (Subgroup.mem_centralizer_iff.mp hS.t_mem v (hD.le_A hv)).symm
  have htN : t ∈ Subgroup.normalizer (Subgroup.centralizer ({v} : Set G) : Set G) := by
    refine CFSG.GroupTheory.mem_normalizer_of_conj_mem fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hvt' : t⁻¹ * v = v * t⁻¹ := (Commute.inv_left htv).eq
    calc t * x * t⁻¹ * v = t * x * (t⁻¹ * v) := by group
      _ = t * x * (v * t⁻¹) := by rw [hvt']
      _ = t * (x * v) * t⁻¹ := by group
      _ = t * (v * x) * t⁻¹ := by rw [hx]
      _ = (t * v) * x * t⁻¹ := by group
      _ = (v * t) * x * t⁻¹ := by rw [htv]
      _ = v * (t * x * t⁻¹) := by group
  exact ⟨hQv, CFSG.GroupTheory.isComponent_map_conj_subgroupOf htN
    (hcomp v hv hv1).1 (hcomp v hv hv1).2⟩

omit [Finite G] in
private theorem wGroup_right_of_l34SuzOddZero {P : Subgroup G}
    (hW : ∀ I : Subgroup G, I ≤ P → Open.IsElemAbelian 2 I → 8 ≤ Nat.card I →
      wGroup I = ⊥)
    {I : Subgroup G} (hIQ : I ≤ P.map (MulAut.conj t).toMonoidHom)
    (hI : Open.IsElemAbelian 2 I) (hI8 : 8 ≤ Nat.card I) :
    wGroup I = ⊥ := by
  let f : G ≃* G := MulAut.conj t
  let I' : Subgroup G := I.map f.symm.toMonoidHom
  have hI'P : I' ≤ P := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Subgroup.mem_map.mp hx
    obtain ⟨p, hp, hzp⟩ := Subgroup.mem_map.mp (hIQ hz)
    rw [← hxz, ← hzp]
    change f.symm (f p) ∈ P
    rw [f.symm_apply_apply]
    exact hp
  have hI'e : Open.IsElemAbelian 2 I' := Open.IsElemAbelian.map hI f.symm.toMonoidHom
  have hI'8 : 8 ≤ Nat.card I' := by
    rw [Subgroup.card_map_of_injective f.symm.injective]
    exact hI8
  have hI'bot : wGroup I' = ⊥ := hW I' hI'P hI'e hI'8
  have hIeq : I'.map f.toMonoidHom = I := by
    simpa [I', f] using CFSG.LocalCores.map_map_symm f.symm I
  calc wGroup I = wGroup (I'.map f.toMonoidHom) := by rw [hIeq]
    _ = (wGroup I').map f.toMonoidHom := by
      simpa [f] using wGroup_map_conj t I'
    _ = ⊥ := by rw [hI'bot, Subgroup.map_bot]

theorem l34PartnerConfig_of_l34SuzOddZero
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hC4 : SuzONanNotProperFixedCatalog) (hSV : L34SuzSignalizerVanishing)
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y) {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hne : P.map (MulAut.conj t).toMonoidHom ≠ P) (hK : K = (HarrisLit.swapDiag P t hc).range)
    (hV : V ≤ centralizer (P : Set G)) (hodd : Odd (Nat.card (center ↥P)))
    (hcomp : ∀ v ∈ V, v ≠ 1 → P ≤ centralizer ({v} : Set G) ∧
      IsComponent (P.subgroupOf (centralizer ({v} : Set G)))) :
    L34PartnerConfig V P (P.map (MulAut.conj t).toMonoidHom) := by
  have hPq : IsQuasisimple ↥P := isQuasisimple_left_of_l34SuzOddZero hD hcomp
  have hQq : IsQuasisimple ↥(P.map (MulAut.conj t).toMonoidHom) :=
    isQuasisimple_right_of_l34SuzOddZero hPq
  have hoddQ : Odd (Nat.card (center ↥(P.map (MulAut.conj t).toMonoidHom))) :=
    odd_card_center_right_of_l34SuzOddZero hodd
  have htypeP : IsL34Type (↥P ⧸ center ↥P) :=
    isL34Type_left_of_l34SuzOddZero hD hc hK hPq
  have htypeQ : IsL34Type (↥(P.map (MulAut.conj t).toMonoidHom) ⧸
      center ↥(P.map (MulAut.conj t).toMonoidHom)) :=
    isL34Type_right_of_l34SuzOddZero htypeP
  have hWleft : ∀ I : Subgroup G, I ≤ P → Open.IsElemAbelian 2 I → 8 ≤ Nat.card I →
      wGroup I = ⊥ := fun I hIP hI hI8 =>
    wGroup_eq_bot_of_le_of_l34SuzOddZero hSch hC4 hSV hS hD hc hK hodd hIP hI hI8
  refine
    { ne := hne
      le_centralizer := hc
      isQuasisimple_left := hPq
      isQuasisimple_right := hQq
      odd_card_center_left := hodd
      odd_card_center_right := hoddQ
      isL34Type_left := htypeP
      isL34Type_right := htypeQ
      card_V := hD.card_V
      mul_self := hD.mul_self
      le_centralizer_left := hV
      le_centralizer_right := le_centralizer_right_of_l34SuzOddZero hS hD hV
      isComponent_left := hcomp
      isComponent_right := isComponent_right_of_l34SuzOddZero hS hD hV hcomp
      wGroup_left := hWleft
      wGroup_right := fun I hIQ hI hI8 => wGroup_right_of_l34SuzOddZero hWleft hIQ hI hI8 }

end CFSG.ComponentClassification.GrSLit.L34Sec5S
