module

public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.OddStandard.AltStdBalDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasicConj
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasicZStar

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup AltStdBal CFSG.OddStandard.Solomon75
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def CycTwoBigFullPairFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 9 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) → 4 ≤ Nat.card S →
          ∀ (Q T : Subgroup G) (g : G), Q ≤ centralizer (L : Set G) → IsPGroup 2 Q →
            Nat.card Q = Nat.card S → g ∉ normalizer (L : Set G) →
            T ≤ CFSG.conjugate (centralizer (L : Set G)) g → IsPGroup 2 T →
            Nat.card T = Nat.card S → Q ≤ centralizer (T : Set G) → False

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {Q : Subgroup G} {z : G}

theorem eq_of_mem_cent_of_commute (d : Cyc L Q z) {a : G}
    (haK : a ∈ centralizer (L : Set G)) (ha2 : orderOf a = 2) (hcomm : a * z = z * a) :
    a = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf (centralizer (L : Set G))) :=
    d.pgroup.of_equiv (subgroupOfEquivOfLe d.le).symm
  let S : Sylow 2 (centralizer (L : Set G)) := hQ'.toSylow d.odd_index
  have hS : IsCyclic S := by
    have h : IsCyclic (Q.subgroupOf (centralizer (L : Set G))) :=
      (subgroupOfEquivOfLe d.le).isCyclic.2 d.cyclic
    exact h
  exact eq_of_commute_of_orderOf_eq_two
    (fun P hPC hP => (isCyclic_and_card_le_of_le S hS hPC hP).1) haK (d.le d.mem) ha2 d.order
    hcomm

theorem exists_zstar_partner (hS : StandardSetting G L) (d : Cyc L Q z) :
    ∃ g : G, g⁻¹ * z * g ≠ z ∧ (g⁻¹ * z * g) * z = z * (g⁻¹ * z * g) ∧
      g⁻¹ * z * g ∉ centralizer (L : Set G) ∧
      z ∉ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
  have := hS.simple
  obtain ⟨g, hne, hcomm⟩ := exists_commuting_conj hS.nonab d.order
  have hord : orderOf (g⁻¹ * z * g) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
    rw [MulAut.conj_apply] at this
    simpa using this.trans d.order
  have haK : g⁻¹ * z * g ∉ centralizer (L : Set G) := fun haK =>
    hne (eq_of_mem_cent_of_commute d haK hord hcomm)
  refine ⟨g, hne, hcomm, haK, fun hzK' => ?_⟩
  rw [centralizer_conjugate] at hzK'
  have hz1 : z ∈ (centralizer (L : Set G)).map (MulAut.conj (1 : G)).toMonoidHom := by
    simpa using d.le d.mem
  have hzg : z ∈ (centralizer (L : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := hzK'
  have hgN := mem_normalizer_of_even_orderOf_mem hS.standard (a := 1) (b := g⁻¹) (x := z)
    (by rw [d.order]; exact even_two) hz1 hzg
  have hgN' : g⁻¹ ∈ normalizer (centralizer (L : Set G) : Set G) := by simpa using hgN
  apply haK
  have := (mem_normalizer_iff.1 hgN' z).1 (d.le d.mem)
  simpa using this

end CFSG.OddStandard.AltStdCycTwo
