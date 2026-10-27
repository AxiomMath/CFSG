module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Low
public import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.ClassicalInvolution.ModelFacts.OddCover.ThreeQ
public import CFSG.Permutation.UnitaryThreeRecognition.ModelFinite

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartOne.Sec66T CFSG.PGLModel
open CFSG.HardMathSupport.Dickson.Sec6.I923

theorem not_isCyclic_of_elemAbelian_27 {Q : Type} [Group Q] {E : Subgroup Q}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) : ¬ IsCyclic E := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have h1 : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : ((g : E) : Q) ^ 3 = 1 := hE.2 g g.2
  have h3 : g ^ 3 = 1 := Subtype.ext (by simpa using h2)
  have h4 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [h1, hc] at h4
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem noE27_of_cyclic_sylow {P : Type} [Group P] [Finite P] (hS : ∀ S : Sylow 3 P, IsCyclic S) :
    NoE27 P := by
  rintro ⟨E, hE, hc⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hES⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_le_sylow
  haveI := hS S
  have hcyc : IsCyclic E := by
    have h1 : IsCyclic (E.subgroupOf (S : Subgroup P)) := inferInstance
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hES).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hES).surjective
  exact not_isCyclic_of_elemAbelian_27 hE hc hcyc

theorem isCyclic_sylow_of_surjective {G P : Type} [Group G] [Finite G] [Group P] [Finite P]
    (π : G →* P) (hπ : Function.Surjective π) (hS : ∀ S : Sylow 3 G, IsCyclic S)
    (Q : Sylow 3 P) : IsCyclic Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hπ 3 Q
  have := hS S
  rw [Sylow.coe_mapSurjective]
  exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)

theorem NoE27.of_mulEquiv {P Q : Type} [Group P] [Group Q] (e : P ≃* Q) (h : NoE27 Q) :
    NoE27 P := by
  rintro ⟨E, hE, hc⟩
  refine h ⟨E.map e.toMonoidHom, CFSG.Open.IsElemAbelian.map hE e.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective e.injective, hc]

theorem noE27_pslGoodThree : NoE27At FamPslGoodThree := by
  intro P _ _ t n p f hadm ht hF hm
  obtain ⟨rfl, rfl, hcop, hp3⟩ := hF
  have hC : StatedClassicalModel P .PSL 3 p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  have hp : p.Prime := hadm.1
  have h3 : ¬ 3 ∣ p ^ f := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have h1 : ¬ 3 ∣ p ^ f - 1 := by
    intro h
    have : Nat.gcd 3 (p ^ f - 1) = 3 := Nat.gcd_eq_left h
    rw [this] at hcop
    exact absurd hcop (by decide)
  have hpos : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hK2 : Nat.card K % 3 = 2 := by rw [hK]; omega
  let e : P ≃* projSL 3 K := e0.trans (projSLEquivStatedProj 3 K).symm
  exact NoE27.of_mulEquiv e (noE27_of_cyclic_sylow fun Q => isCyclic_sylow_three_projSL hK2 Q)

theorem noE27_psuGoodThree : NoE27At FamPsuGoodThree := by
  intro P _ _ t n p f hadm ht hF hm
  obtain ⟨rfl, rfl, hnd, hp3⟩ := hF
  have hC : StatedClassicalModel P .PSU 3 p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  have hp : p.Prime := hadm.1
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : 1 ≤ f := hadm.2.1
  haveI : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (k := f * 2) (by omega) (by rw [hK, ← pow_mul])
  have hre : ¬ 3 ∣ p ^ f + 1 := fun h => hnd (by rw [Nat.gcd_eq_left h])
  have hsyl : ∀ S : Sylow 3 (StatedSU 3 (p ^ f) K), IsCyclic S := fun S =>
    CFSG.ClassicalInvolution.ModelFacts.OddCover.statedSU_three_isCyclic_sylow hK (by norm_num)
      (fun h => hp3 h.symm) hre S
  let π : StatedSU 3 (p ^ f) K →* StatedProj (StatedSU 3 (p ^ f) K) :=
    QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K))
  exact NoE27.of_mulEquiv e0 (noE27_of_cyclic_sylow fun Q =>
    isCyclic_sylow_of_surjective π (QuotientGroup.mk'_surjective _) hsyl Q)

end CFSG.HardMathSupport.Dickson.Sec6.I1431
