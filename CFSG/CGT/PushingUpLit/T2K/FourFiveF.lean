module

public import CFSG.CGT.PushingUpLit.T2K.FourFiveE

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T A : Subgroup G} {n : ℕ}

namespace Hyp45

variable (H : Hyp45 L M T A n)
include H

theorem tOf_mem_bGrp_of_centralizes (hZ : blockZ L = ⊥)
    (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) (a : ↥A)
    (ha : (a : G) ∈ Subgroup.centralizer (blockU L : Set G)) :
    (H.lOf a)⁻¹ * (a : G) ∈ bGrp L A := by
  have hr : H.lOf a ∈ oTwoIn L := by
    rw [← H.block.inf_centralizer_blockU]
    refine ⟨H.lOf_mem a, ?_⟩
    have e : H.lOf a = (a : G) * ((H.lOf a)⁻¹ * (a : G))⁻¹ := by group
    rw [e]
    exact (Subgroup.centralizer (blockU L : Set G)).mul_mem ha
      ((Subgroup.centralizer (blockU L : Set G)).inv_mem (H.tOf_mem a).2)
  have hrB := H.oTwoIn_le_bGrp hZ hS hr
  have haB : (a : G) ∈ bGrp L A :=
    (le_sup_left : A ⊓ Subgroup.centralizer (blockU L : Set G) ≤ bGrp L A) ⟨a.2, ha⟩
  exact (bGrp L A).mul_mem ((bGrp L A).inv_mem hrB) haB

theorem centralizes_of_tOf_mem_bGrp (hO : oTwoIn L ≠ blockU L) (a : ↥A)
    (ht : (H.lOf a)⁻¹ * (a : G) ∈ bGrp L A) :
    (a : G) ∈ Subgroup.centralizer (blockU L : Set G) := by
  have ht2 : ((H.lOf a)⁻¹ * (a : G)) ^ 2 = 1 := H.B_isElemAbelian.2 _ ht
  obtain ⟨w, hw, hrel⟩ := H.sq_rel a
  rw [ht2, mul_one] at hrel
  have hr2 : (H.lOf a) ^ 2 ∈ blockU L := by
    have : (H.lOf a) ^ 2 = w⁻¹ := mul_eq_one_iff_eq_inv.1 hrel
    rw [this]
    exact (blockU L).inv_mem hw
  have hrO : H.lOf a ∈ oTwoIn L := by
    by_contra hnot
    exact hO (H.block.oTwoIn_eq_blockU_of_sq_mem (H.lOf_mem a) hnot hr2)
  have hrC : H.lOf a ∈ Subgroup.centralizer (blockU L : Set G) := by
    rw [← H.block.inf_centralizer_blockU] at hrO
    exact hrO.2
  have e : (a : G) = H.lOf a * ((H.lOf a)⁻¹ * (a : G)) := by group
  rw [e]
  exact mul_mem hrC (H.tOf_mem a).2

theorem mem_bGrp_of_sq_eq_one (hZ : blockZ L = ⊥)
    (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) (hO : oTwoIn L ≠ blockU L)
    {p : G} (hp : p ∈ T ⊓ Subgroup.centralizer (blockU L : Set G)) (hp2 : p ^ 2 = 1) :
    p ∈ bGrp L A := by
  classical
  set P : Subgroup G := T ⊓ Subgroup.centralizer (blockU L : Set G) with hPdef
  set B : Subgroup G := bGrp L A with hBdef
  have hBP : B ≤ P := H.B_le_P
  let B' : Subgroup ↥P := B.subgroupOf P
  have hB'n : B'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hg : ((g : G))⁻¹ ∈ P := P.inv_mem g.2
    have h1 := H.conj_mem_bGrp hS hg (b := (x : G)) hx
    rw [inv_inv] at h1
    exact h1
  let Θ : ↥A →* ↥P ⧸ B' := MonoidHom.mk'
    (fun a => QuotientGroup.mk ⟨(H.lOf a)⁻¹ * (a : G), H.tOf_mem a⟩) (by
      intro a a'
      show QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
      rw [← QuotientGroup.mk_mul]
      symm
      rw [QuotientGroup.eq]
      exact H.tOf_mul_mem hZ hS a a')
  have hker : Θ.ker = (A ⊓ Subgroup.centralizer (blockU L : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      have h' : (⟨(H.lOf a)⁻¹ * (a : G), H.tOf_mem a⟩ : ↥P) ∈ B' := (QuotientGroup.eq_one_iff _).1 h
      exact ⟨a.2, H.centralizes_of_tOf_mem_bGrp hO a h'⟩
    · intro h
      exact (QuotientGroup.eq_one_iff _).2 (H.tOf_mem_bGrp_of_centralizes hZ hS a h.2)
  have hcard : Nat.card Θ.range = 2 ^ n := by
    have e := QuotientGroup.quotientKerEquivRange Θ
    rw [← Nat.card_congr e.toEquiv, hker]
    exact H.index_centralizer
  have hidx : Nat.card (↥P ⧸ B') ≤ Nat.card Θ.range := by
    rw [hcard, ← Subgroup.index_eq_card]
    exact H.relIndex_bGrp_le hS
  have hrange : Θ.range = ⊤ := Subgroup.eq_top_of_le_card _ hidx
  obtain ⟨a, ha⟩ := MonoidHom.range_eq_top.1 hrange (QuotientGroup.mk ⟨p, hp⟩)
  have hab : (⟨(H.lOf a)⁻¹ * (a : G), H.tOf_mem a⟩ : ↥P)⁻¹ * ⟨p, hp⟩ ∈ B' :=
    QuotientGroup.eq.1 ha
  have hb : ((H.lOf a)⁻¹ * (a : G))⁻¹ * p ∈ B := hab
  set t := (H.lOf a)⁻¹ * (a : G) with htdef
  set b := t⁻¹ * p with hbdef
  have hpb : p = t * b := by rw [hbdef]; group
  have hbt : b * t = t * b := H.tOf_comm_B hS a b hb
  have hb2 : b ^ 2 = 1 := H.B_isElemAbelian.2 b hb
  have hp2' : p ^ 2 = t ^ 2 := by
    rw [hpb, (show Commute t b from hbt.symm).mul_pow, hb2, mul_one]
  have ht2 : t ^ 2 = 1 := by rw [← hp2', hp2]
  have haC : (a : G) ∈ Subgroup.centralizer (blockU L : Set G) := by
    refine H.centralizes_of_tOf_mem_bGrp hO a ?_
    exact mem_of_isMaxElemAbelian H.isMaxElemAbelian_B (H.tOf_mem a).1 ht2
      (H.tOf_comm_B hS a)
  have htB : t ∈ B := H.tOf_mem_bGrp_of_centralizes hZ hS a haC
  rw [hpb]
  exact B.mul_mem htB hb

theorem eq_bGrp_of_isMaxElemAbelian_P (hZ : blockZ L = ⊥)
    (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) (hO : oTwoIn L ≠ blockU L)
    {D : Subgroup G} (hD : IsMaxElemAbelian (T ⊓ Subgroup.centralizer (blockU L : Set G)) D) :
    D = bGrp L A := by
  have hDB : D ≤ bGrp L A := fun d hd =>
    H.mem_bGrp_of_sq_eq_one hZ hS hO (hD.1 hd) (hD.2.1.2 d hd)
  exact (Subgroup.eq_of_le_of_card_ge hDB
    (hD.2.2 _ H.B_le_P H.B_isElemAbelian))

theorem four_five_six (hZ : blockZ L = ⊥)
    (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) :
    (oTwoIn L = blockU L ∧
      (∀ a ∈ A, ∃ c ∈ A ⊓ L, ∃ s ∈ T ⊓ Subgroup.centralizer (L : Set G), a = c * s) ∧
      ∀ A' : Subgroup G, IsMaxElemAbelian T A' →
        ¬ A' ≤ Subgroup.centralizer (blockU L : Set G) → A' = A) ∨
    (oTwoIn L ≠ blockU L ∧ n = 2 ∧
      ∀ D : Subgroup G, IsMaxElemAbelian (T ⊓ Subgroup.centralizer (blockU L : Set G)) D →
        D = bGrp L A) := by
  by_cases hO : oTwoIn L = blockU L
  · refine Or.inl ⟨hO, fun a ha => H.exists_mul_of_oTwoIn_eq hZ hS hO ⟨a, ha⟩, ?_⟩
    intro A' hA' hA'V
    exact H.eq_of_isMaxElemAbelian hZ hS hO hA' hA'V
  · refine Or.inr ⟨hO, ?_, fun D hD => H.eq_bGrp_of_isMaxElemAbelian_P hZ hS hO hD⟩
    by_contra hn
    exact hO (H.block.oTwoIn_eq_blockU_of_three_le (by have := H.block.two_le; omega))

end Hyp45

end CFSG.CGT.PushingUpLit.T2K
