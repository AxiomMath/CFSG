module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairBlocks
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary
import CFSG.Assembly.Defs

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

section PCoreModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isPGroup_two_EA_subgroupOf : IsPGroup 2 ((EA ι).subgroupOf (NA ι)) := by
  intro g
  refine ⟨1, ?_⟩
  have hg : ((g : NA ι) : AltB ι) ∈ EA ι := g.2
  rw [pow_one, pow_two]
  exact Subtype.ext (Subtype.ext (EA_mul_self hg))

theorem pCore_NA (hι : 5 ≤ Fintype.card ι) :
    CFSG.pCore 2 ↥(NA ι) = (EA ι).subgroupOf (NA ι) := by
  have hnorm : ((EA ι).subgroupOf (NA ι)).Normal := by
    rw [← ker_blockAction]; infer_instance
  apply le_antisymm
  · exact le_EA_of_normal_isPGroup hι CFSG.pCore_isPGroup
  · exact le_sSup ⟨hnorm, isPGroup_two_EA_subgroupOf⟩

noncomputable def quotientPCoreNA (hι : 5 ≤ Fintype.card ι) :
    ↥(NA ι) ⧸ CFSG.pCore 2 ↥(NA ι) ≃* Perm ι :=
  (QuotientGroup.quotientMulEquivOfEq (by rw [pCore_NA hι, ← ker_blockAction])).trans
    (QuotientGroup.quotientKerEquivOfSurjective blockAction blockAction_surjective)

end PCoreModel

section Transport

variable {Q : Type*} [Group Q]

@[expose] noncomputable def sectionEquiv {C B : Subgroup Q} (hBC : B ≤ C) {M : Type*} [Group M]
    (φ : ↥C ≃* M) (N : Subgroup M) (hN : (B.subgroupOf C).map φ.toMonoidHom = N) :
    ↥B ≃* ↥N :=
  (Subgroup.subgroupOfEquivOfLe hBC).symm.trans
    ((φ.subgroupMap (B.subgroupOf C)).trans (MulEquiv.subgroupCongr hN))

theorem sectionEquiv_coe {C B : Subgroup Q} (hBC : B ≤ C) {M : Type*} [Group M]
    (φ : ↥C ≃* M) (N : Subgroup M) (hN : (B.subgroupOf C).map φ.toMonoidHom = N) (b : ↥B) :
    ((sectionEquiv hBC φ N hN b : ↥N) : M) = φ ⟨b.1, hBC b.2⟩ := rfl

theorem mem_iff_of_map_eq {C A : Subgroup Q} {M : Type*} [Group M] (φ : ↥C ≃* M)
    {E : Subgroup M} (hE : (A.subgroupOf C).map φ.toMonoidHom = E) (a : ↥C) :
    φ a ∈ E ↔ (a : Q) ∈ A := by
  rw [← hE]
  constructor
  · rintro ⟨a', ha', h⟩
    have : a' = a := φ.injective h
    subst this
    exact ha'
  · intro h
    exact ⟨a, h, rfl⟩

theorem pairModel_core {C A B : Subgroup Q} (hAB : A ≤ B) (hBC : B ≤ C) {n : ℕ} (hn : 5 ≤ n)
    (φ : ↥C ≃* AltB (Fin n))
    (hA : (A.subgroupOf C).map φ.toMonoidHom = EA (Fin n))
    (hB : (B.subgroupOf C).map φ.toMonoidHom = NA (Fin n)) :
    A = CFSG.Open.pCoreOf 2 B ∧ CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 2 ^ (n - 1) ∧
      Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Perm (Fin n)) := by
  have hι : 5 ≤ Fintype.card (Fin n) := by simpa using hn
  have hAC : A ≤ C := hAB.trans hBC
  set ψ := sectionEquiv hBC φ (NA (Fin n)) hB with hψ
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hpc : (CFSG.pCore 2 ↥B).map ψ.toMonoidHom = (EA (Fin n)).subgroupOf (NA (Fin n)) := by
      rw [CFSG.pCore_map_iso 2 ψ, pCore_NA hι]
    unfold CFSG.Open.pCoreOf
    refine le_antisymm ?_ ?_
    · intro y hy
      have hyB : y ∈ B := hAB hy
      refine ⟨⟨y, hyB⟩, ?_, rfl⟩
      have hmem : ψ ⟨y, hyB⟩ ∈ (EA (Fin n)).subgroupOf (NA (Fin n)) :=
        (mem_iff_of_map_eq φ hA ⟨y, hAC hy⟩).2 hy
      rw [← hpc] at hmem
      obtain ⟨b, hb, hbψ⟩ := hmem
      have : b = ⟨y, hyB⟩ := ψ.injective hbψ
      rwa [this] at hb
    · rintro y ⟨b, hb, rfl⟩
      have hb' : ψ b ∈ (EA (Fin n)).subgroupOf (NA (Fin n)) := by
        rw [← hpc]; exact ⟨b, hb, rfl⟩
      have h1 : φ ⟨b.1, hBC b.2⟩ ∈ EA (Fin n) := hb'
      exact (mem_iff_of_map_eq φ hA _).1 h1
  ·
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have ha : φ ⟨a.1, hAC a.2⟩ ∈ EA (Fin n) := (mem_iff_of_map_eq φ hA _).2 a.2
      have hb : φ ⟨b.1, hAC b.2⟩ ∈ EA (Fin n) := (mem_iff_of_map_eq φ hA _).2 b.2
      have := EA_mul_comm ha hb
      rw [← map_mul, ← map_mul] at this
      have h2 := φ.injective this
      exact Subtype.ext (congrArg (fun z : ↥C => (z : Q)) h2)
    · have hx' : φ ⟨x, hAC hx⟩ ∈ EA (Fin n) := (mem_iff_of_map_eq φ hA _).2 hx
      have := EA_mul_self hx'
      rw [← map_mul, ← map_one φ] at this
      have h2 := φ.injective this
      rw [pow_two]
      exact congrArg (fun z : ↥C => (z : Q)) h2
  ·
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have h1 : Nat.card A = Nat.card (A.subgroupOf C) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv).symm
    have h2 : Nat.card (A.subgroupOf C) = Nat.card ((A.subgroupOf C).map φ.toMonoidHom) :=
      (Subgroup.card_map_of_injective φ.injective).symm
    rw [h1, h2, hA, card_EA, Fintype.card_fin]
  ·
    refine ⟨?_⟩
    have hmap : (CFSG.pCore 2 ↥B).map ψ.toMonoidHom = CFSG.pCore 2 ↥(NA (Fin n)) :=
      CFSG.pCore_map_iso 2 ψ
    exact (QuotientGroup.congr (CFSG.pCore 2 ↥B) (CFSG.pCore 2 ↥(NA (Fin n))) ψ hmap).trans
      (quotientPCoreNA hι)

end Transport

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
