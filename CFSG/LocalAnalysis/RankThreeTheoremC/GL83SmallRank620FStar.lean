module

public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

private theorem fstar_not_solvable {Y : Type*} [Group Y] {Kb : Subgroup Y}
    (hKs : IsSimpleGroup ↥Kb) (hKab : ∃ a ∈ Kb, ∃ c ∈ Kb, a * c ≠ c * a) :
    ¬ Group.IsSolvable ↥Kb := by
  intro h
  obtain ⟨a, ha, c, hc, hne⟩ := hKab
  exact hne (congrArg Subtype.val
    ((IsSimpleGroup.comm_iff_isSolvable (G := ↥Kb)).2 h ⟨a, ha⟩ ⟨c, hc⟩))

private theorem fstar_center_eq_bot {Y : Type*} [Group Y] {Kb : Subgroup Y}
    (hKs : IsSimpleGroup ↥Kb) (hKab : ∃ a ∈ Kb, ∃ c ∈ Kb, a * c ≠ c * a) :
    center ↥Kb = ⊥ := by
  rcases hKs.eq_bot_or_eq_top_of_normal (center ↥Kb) with h | h
  · exact h
  · have : IsMulCommutative ↥Kb := Subgroup.center_eq_top_iff.mp h
    exact (fstar_not_solvable hKs hKab inferInstance).elim

private theorem fstar_inf_centralizer {Y : Type*} [Group Y] {Kb : Subgroup Y}
    (hKs : IsSimpleGroup ↥Kb) (hKab : ∃ a ∈ Kb, ∃ c ∈ Kb, a * c ≠ c * a) :
    Kb ⊓ centralizer (Kb : Set Y) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hxK : (⟨x, hx.1⟩ : ↥Kb) ∈ center ↥Kb := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
  rw [fstar_center_eq_bot hKs hKab, Subgroup.mem_bot] at hxK
  exact congrArg Subtype.val hxK

private theorem fstar_card_le_three {Y : Type*} [Group Y] [Finite Y] {Kb T : Subgroup Y}
    (h3K : 3 ∣ Nat.card Kb) (hKC : Kb ⊓ centralizer (Kb : Set Y) = ⊥)
    (h3 : ∀ P : Subgroup Y, IsPGroup 3 P → Nat.card P ≤ 9)
    (hTC : T ≤ centralizer (Kb : Set Y)) (hT3 : IsPGroup 3 T) : Nat.card T ≤ 3 := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 h3K
  have hord : orderOf (a : Y) = 3 := by simpa using ha
  have hAcard : Nat.card (zpowers (a : Y)) = 3 := by rw [Nat.card_zpowers, hord]
  have hA3 : IsPGroup 3 (zpowers (a : Y)) := IsPGroup.of_card (n := 1) (by simpa using hAcard)
  have hAK : zpowers (a : Y) ≤ Kb := (Subgroup.zpowers_le).2 a.2
  have hAT : zpowers (a : Y) ≤ normalizer (T : Set Y) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp (hTC ht) g (hAK hg)).symm
  have hsup : IsPGroup 3 (T ⊔ zpowers (a : Y) : Subgroup Y) := hT3.to_sup_of_normal_left' hA3 hAT
  have hle9 := h3 _ hsup
  have hne : T ≠ T ⊔ zpowers (a : Y) := by
    intro h
    have haT : (a : Y) ∈ T := by
      have : (a : Y) ∈ T ⊔ zpowers (a : Y) := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      rwa [← h] at this
    have h1 : (a : Y) ∈ Kb ⊓ centralizer (Kb : Set Y) := ⟨a.2, hTC haT⟩
    rw [hKC, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hord
    omega
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.1 hT3
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hsup
  have hij : i < j := by
    by_contra hlt
    have hge := not_lt.1 hlt
    have hdvd : Nat.card (T ⊔ zpowers (a : Y) : Subgroup Y) ∣ Nat.card T := by
      rw [hi, hj]
      exact pow_dvd_pow 3 hge
    have hpos : 0 < Nat.card T := Nat.card_pos
    exact hne (Subgroup.eq_of_le_of_card_ge le_sup_left (Nat.le_of_dvd hpos hdvd))
  have h3pow : 3 ^ (i + 1) ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hij
  rw [pow_succ, ← hj] at h3pow
  rw [hi]
  rw [← hi] at h3pow
  omega

private theorem fstar_fitting_map_eq {Y : Type*} [Group Y] [Finite Y] (C Bb : Subgroup Y)
    [hCn : C.Normal] [hsolv : Group.IsSolvable ↥C] (hBb : Nat.card Bb = 3) (hBc : Bb ≤ C)
    (hO3 : ∀ N : Subgroup Y, N.Normal → Nat.Coprime 3 (Nat.card N) → N = ⊥)
    (h3C : ∀ T : Subgroup Y, T ≤ C → IsPGroup 3 T → Nat.card T ≤ 3) :
    (CFSG.fittingSubgroup ↥C).map C.subtype = Bb := by
  have hcore : CFSG.pPrimeCore 3 ↥C = ⊥ := by
    have hn : ((CFSG.pPrimeCore 3 ↥C).map C.subtype).Normal := inferInstance
    have hcop : Nat.Coprime 3 (Nat.card ((CFSG.pPrimeCore 3 ↥C).map C.subtype)) := by
      rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 (hO3 _ hn hcop)
  have hFp : IsPGroup 3 (CFSG.fittingSubgroup ↥C) :=
    CFSG.isPGroup_of_nilpotent_normal _ CFSG.fittingSubgroup_normal
      CFSG.fittingSubgroup_nilpotent hcore
  have hFn : ((CFSG.fittingSubgroup ↥C).map C.subtype).Normal := inferInstance
  have hFp' : IsPGroup 3 ((CFSG.fittingSubgroup ↥C).map C.subtype) := hFp.map C.subtype
  have hFC : (CFSG.fittingSubgroup ↥C).map C.subtype ≤ C := Subgroup.map_subtype_le _
  have hBp : IsPGroup 3 Bb := IsPGroup.of_card (n := 1) (by simpa using hBb)
  have hsup : IsPGroup 3 ((CFSG.fittingSubgroup ↥C).map C.subtype ⊔ Bb : Subgroup Y) :=
    hFp'.to_sup_of_normal_left hBp
  have hcard := h3C _ (sup_le hFC hBc) hsup
  have hBeq : Bb = (CFSG.fittingSubgroup ↥C).map C.subtype ⊔ Bb :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by omega)
  have hFle : (CFSG.fittingSubgroup ↥C).map C.subtype ≤ Bb := hBeq ▸ le_sup_left
  have hCcard : Nat.card ↥C ≠ 1 := by
    intro h1
    have := Subgroup.card_dvd_of_le hBc
    rw [hBb, h1] at this
    omega
  have hFne : CFSG.fittingSubgroup ↥C ≠ ⊥ := fun h =>
    hCcard ((CFSG.fitting_eq_bot_iff_card_eq_one_of_solvable ↥C).1 h)
  have hFne' : (CFSG.fittingSubgroup ↥C).map C.subtype ≠ ⊥ := fun h =>
    hFne ((Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 h)
  have hdvd := Subgroup.card_dvd_of_le hFle
  rw [hBb] at hdvd
  have hne1 : Nat.card ((CFSG.fittingSubgroup ↥C).map C.subtype) ≠ 1 := fun h =>
    hFne' (Subgroup.card_eq_one.1 h)
  have h3 : Nat.card ((CFSG.fittingSubgroup ↥C).map C.subtype) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left hne1
  exact Subgroup.eq_of_le_of_card_ge hFle (by omega)

private theorem fstar_genFittingFitting_eq {Y : Type*} [Group Y] [Finite Y] {Kb Bb : Subgroup Y}
    (hKn : Kb.Normal) (hKs : IsSimpleGroup ↥Kb) (hKab : ∃ a ∈ Kb, ∃ c ∈ Kb, a * c ≠ c * a)
    (hBn : Bb.Normal) (hBnil : Group.IsNilpotent ↥Bb)
    (hF : (CFSG.fittingSubgroup ↥(centralizer (Kb : Set Y))).map
      (centralizer (Kb : Set Y)).subtype = Bb) :
    CFSG.Open.genFittingFitting Y = Bb := by
  refine le_antisymm (sSup_le ?_) (le_sSup ⟨hBn, hBnil⟩)
  rintro N ⟨hNn, hNnil⟩
  have hNK : N ⊓ Kb = ⊥ := by
    have hnorm : ((N ⊓ Kb).subgroupOf Kb).Normal := inferInstance
    rcases hKs.eq_bot_or_eq_top_of_normal ((N ⊓ Kb).subgroupOf Kb) with h | h
    · refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      have hx' : (⟨x, hx.2⟩ : ↥Kb) ∈ (N ⊓ Kb).subgroupOf Kb := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact congrArg Subtype.val hx'
    · exfalso
      have hKN : Kb ≤ N := (Subgroup.subgroupOf_eq_top.1 h).trans inf_le_left
      have hnil : Group.IsNilpotent (Kb.subgroupOf N) := Subgroup.isNilpotent _
      have : Group.IsNilpotent ↥Kb := Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKN)
      exact fstar_not_solvable hKs hKab inferInstance
  have hcomm : ⁅N, Kb⁆ = ⊥ := by
    have h : ⁅N, Kb⁆ ≤ N ⊓ Kb :=
      le_inf (Subgroup.commutator_le_left N Kb) (Subgroup.commutator_le_right N Kb)
    rw [hNK] at h
    exact le_bot_iff.1 h
  have hNC : N ≤ centralizer (Kb : Set Y) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hnil' : Group.IsNilpotent (N.subgroupOf (centralizer (Kb : Set Y))) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNC).symm
  have hle : N.subgroupOf (centralizer (Kb : Set Y)) ≤
      CFSG.fittingSubgroup ↥(centralizer (Kb : Set Y)) := le_sSup ⟨inferInstance, hnil'⟩
  rw [← hF, ← Subgroup.map_subgroupOf_eq_of_le hNC]
  exact Subgroup.map_mono hle

private theorem fstar_isComponentOf {Y : Type*} [Group Y] {Kb : Subgroup Y}
    (hKn : Kb.Normal) (hKs : IsSimpleGroup ↥Kb) (hKab : ∃ a ∈ Kb, ∃ c ∈ Kb, a * c ≠ c * a) :
    CFSG.Open.IsComponentOf Kb ⊤ := by
  refine ⟨le_top, ?_, ?_, ?_⟩
  · exact CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl _)
  · rcases hKs.eq_bot_or_eq_top_of_normal (_root_.commutator ↥Kb) with h | h
    · have : IsMulCommutative ↥Kb := (commutator_eq_bot_iff ↥Kb).1 h
      exact (fstar_not_solvable hKs hKab inferInstance).elim
    · exact h
  · have e : ↥Kb ⧸ center ↥Kb ≃* ↥Kb :=
      (QuotientGroup.quotientMulEquivOfEq (fstar_center_eq_bot hKs hKab)).trans
        QuotientGroup.quotientBot
    exact e.isSimpleGroup

private theorem fstar_isComponent_of_open {Y : Type*} [Group Y] {L : Subgroup Y}
    (h : CFSG.Open.IsComponentOf L ⊤) : CFSG.IsComponent L := by
  obtain ⟨-, hsub, hperf, hsimple⟩ := h
  have hP : Group.IsPerfect ↥L := ⟨hperf⟩
  refine ⟨⟨hP, hsimple, ?_⟩, ?_⟩
  · by_contra hcon
    have : IsMulCommutative (↥L ⧸ center ↥L) :=
      isMulCommutative_iff.2 fun a b => by_contra fun hne => hcon ⟨a, b, hne⟩
    exact Group.IsPerfect.not_isMulCommutative (↥L ⧸ center ↥L) this
  · have key : ∀ H K : Subgroup Y, CFSG.Open.IsSubnormal H K → K = ⊤ → H.IsSubnormal := by
      intro H K h
      induction h with
      | refl H => rintro rfl; exact Subgroup.IsSubnormal.top
      | step hHM hN _ ih => intro hK; exact Subgroup.IsSubnormal.step _ _ hHM (ih hK) hN
    exact key L ⊤ hsub rfl

private theorem fstar_genFittingLayer_eq {Y : Type*} [Group Y] [Finite Y] {Kb : Subgroup Y}
    (hKn : Kb.Normal) (hKs : IsSimpleGroup ↥Kb) (hKab : ∃ a ∈ Kb, ∃ c ∈ Kb, a * c ≠ c * a)
    (hsolv : Group.IsSolvable ↥(centralizer (Kb : Set Y))) :
    CFSG.Open.genFittingLayer Y = Kb := by
  refine le_antisymm (sSup_le ?_) (le_sSup (fstar_isComponentOf hKn hKs hKab))
  intro L hL
  have hcomp : CFSG.IsComponent L := fstar_isComponent_of_open hL
  rcases CFSG.LocalCores.component_normal_subgroup hcomp hKn with h | h
  · exact h
  · exfalso
    have hLC : L ≤ centralizer (Kb : Set Y) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLC)
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hcomp.1
    have : Group.IsPerfect ↥L := hcomp.1.1
    exact Group.IsPerfect.not_isSolvable ↥L inferInstance

theorem genFittingFStar_eq_sup_of_centralizer_solvable {Y : Type*} [Group Y] [Finite Y]
    (Kb Bb : Subgroup Y) (hKn : Kb.Normal) (hKs : IsSimpleGroup ↥Kb)
    (hKab : ∃ a ∈ Kb, ∃ c ∈ Kb, a * c ≠ c * a) (h3K : 3 ∣ Nat.card Kb)
    (hBb : Nat.card Bb = 3) (hBc : Bb ≤ centralizer (Kb : Set Y))
    (hO3 : ∀ N : Subgroup Y, N.Normal → Nat.Coprime 3 (Nat.card N) → N = ⊥)
    (h3 : ∀ P : Subgroup Y, IsPGroup 3 P → Nat.card P ≤ 9)
    (hsolv : Group.IsSolvable ↥(centralizer (Kb : Set Y))) :
    Bb.Normal ∧ CFSG.Open.genFittingFStar Y = Kb ⊔ Bb := by
  have := hKn
  have := hsolv
  have hCn : (centralizer (Kb : Set Y)).Normal := inferInstance
  have hF : (CFSG.fittingSubgroup ↥(centralizer (Kb : Set Y))).map
      (centralizer (Kb : Set Y)).subtype = Bb :=
    fstar_fitting_map_eq (centralizer (Kb : Set Y)) Bb hBb hBc hO3
      (fun _ hT hT3 => fstar_card_le_three h3K (fstar_inf_centralizer hKs hKab) h3 hT hT3)
  have hBn : Bb.Normal := hF ▸ inferInstance
  have hBp : IsPGroup 3 Bb := IsPGroup.of_card (n := 1) (by simpa using hBb)
  refine ⟨hBn, ?_⟩
  simp only [CFSG.Open.genFittingFStar.eq_sup]
  rw [fstar_genFittingFitting_eq hKn hKs hKab hBn hBp.isNilpotent hF,
    fstar_genFittingLayer_eq hKn hKs hKab hsolv, sup_comm]

end CFSG.LocalAnalysis.RankThreeTheoremC
