module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.SetupModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.DictOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.OrbV

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.CSide
open CFSG.EvenSporadicStandard.HNRecog.Fpf
open CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

theorem cSideFacts_inv_classes :
    ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → CIrreducible C Q →
      ∃ S : Fin 2 → Set C, IsOrbitPartition (⊤ : Subgroup C)
          {q | q ∈ Q ∧ q ^ 2 = 1 ∧ q ∉ centerOf Q} S ∧
        Nat.card ↥(S 0) = 150 ∧ Nat.card ↥(S 1) = 120 := by
  intro C _ Q hQn hE hI
  have hC : WeakHyp C Q := WeakHyp.of_cIrreducible hE hI
  haveI : Finite C := hC.finite
  haveI : Finite Q := hC.finite_Q
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hC.isExtraspecialPGroup
  haveI : Finite (Additive (Abelianization Q)) := by
    change Finite (Q ⧸ _root_.commutator Q)
    infer_instance
  obtain ⟨S⟩ := hC.nonempty_setup
  let q := extraspecialQuadForm hC.isExtraspecialPGroup
  obtain ⟨O, hcover, hdisj, hinv, htrans, h0, h1⟩ := (S.model hC).orbits
  have hq : ∀ c : C, ∀ v : Additive (Abelianization Q), q (conjLinEquiv hQn c v) = q v := by
    intro c v
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1
      (conjLinEquiv_mem hC.isExtraspecialPGroup hQn c) v
  have hf : ∀ c : C, ∀ g : A5 × A5, ∃ g' : A5 × A5,
      conjLinEquiv hQn c * S.σ g * (conjLinEquiv hQn c)⁻¹ = S.σ g' := by
    intro c g
    obtain ⟨l, hl⟩ := S.surj g
    let l' : ↥(commutator C) := ⟨c * (l : C) * c⁻¹,
      (inferInstance : (commutator C).Normal).conj_mem (l : C) l.2 c⟩
    refine ⟨S.θ l', ?_⟩
    rw [← hl, S.sigma_eq l, S.sigma_eq l']
    dsimp only [l']
    rw [map_mul, map_mul, map_inv]
  have htrans' : ∀ i : Fin 2, ∀ v ∈ O i, ∀ w ∈ O i, ∃ c : C, conjLinEquiv hQn c v = w := by
    intro i v hv w hw
    obtain ⟨g, hg⟩ := htrans i v hv w hw
    obtain ⟨l, hl⟩ := S.surj g
    refine ⟨(l : C), ?_⟩
    rw [← S.sigma_eq l, hl]
    exact hg
  have hinv' : ∀ i : Fin 2, ∀ c : C, ∀ v ∈ O i, conjLinEquiv hQn c v ∈ O i := by
    intro i c v hv
    exact cSide_orbit_invariant q S.σ O hcover hdisj hinv htrans h0 h1
      (conjLinEquiv hQn c) (hq c) (hf c) i v hv
  have hO0 : (O 0).Nonempty := by
    have hpos : 0 < Nat.card (O 0) := by rw [h0]; norm_num
    exact Set.nonempty_coe_sort.mp (Nat.card_pos_iff.mp hpos).1
  have hO1 : (O 1).Nonempty := by
    have hpos : 0 < Nat.card (O 1) := by rw [h1]; norm_num
    exact Set.nonempty_coe_sort.mp (Nat.card_pos_iff.mp hpos).1
  have hne : ∀ i : Fin 2, (O i).Nonempty := by
    intro i
    fin_cases i
    · exact hO0
    · exact hO1
  obtain ⟨S', hpart, hsize⟩ :=
    cSide_orbit_partition hC.isExtraspecialPGroup O hcover hdisj hne hinv' htrans'
  exact ⟨S', hpart, by rw [hsize 0, h0], by rw [hsize 1, h1]⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
