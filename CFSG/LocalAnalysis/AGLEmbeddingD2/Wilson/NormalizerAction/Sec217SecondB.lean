module

public import CFSG.RankThree.PartTwo.KFacts.K71Residual
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217U0

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_of_simple_nc {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) : IsQuasisimple Q := by
  obtain ⟨a, b, hab⟩ := hQ
  have hc : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a) hab
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hne : e.symm a * e.symm b ≠ e.symm b * e.symm a := by
    rw [← map_mul, ← map_mul]
    exact fun h => hab (e.symm.injective h)
  have : Nontrivial (Q ⧸ Subgroup.center Q) :=
    ⟨⟨e.symm a, e.symm b, fun h => hne (by rw [h])⟩⟩
  refine ⟨⟨?_⟩, IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective,
    e.symm a, e.symm b, hne⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · exfalso
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator Q :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · exact h

theorem isQuasisimple_quot_theta_of_simple {P : Type*} [Group P] [Finite P] [IsSimpleGroup P]
    (hna : ∃ a b : P, a * b ≠ b * a) : IsQuasisimple (P ⧸ aschbacherSolvableCore 3 P) := by
  obtain ⟨hθs, hθch, -⟩ := solvable_prime_complement_core_characterization (H := P) Nat.prime_three
  have : (aschbacherSolvableCore 3 P).Normal := Subgroup.normal_of_characteristic _
  have hbot : aschbacherSolvableCore 3 P = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 P) with h | h
    · exact h
    · exfalso
      have hs : Group.IsSolvable P := by
        have : Group.IsSolvable (⊤ : Subgroup P) := h ▸ hθs
        exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := P)).toMonoidHom)
          (Subgroup.topEquiv (G := P)).surjective
      obtain ⟨a, b, hab⟩ := hna
      have := IsSimpleGroup.comm_iff_isSolvable.2 hs
      exact hab (this a b)
  have e : P ⧸ aschbacherSolvableCore 3 P ≃* P := (QuotientGroup.quotientMulEquivOfEq hbot).trans
    QuotientGroup.quotientBot
  exact LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_of_simple_nc hna)

theorem not_isSolvable_of_isQuasisimple'' {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  intro hs
  obtain ⟨-, hsimple, a, b, hab⟩ := hQ
  have : Group.IsSolvable (Q ⧸ Subgroup.center Q) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (Subgroup.center Q))
      (QuotientGroup.mk'_surjective _)
  have hc := IsSimpleGroup.comm_iff_isSolvable.2 this
  exact hab (hc a b)

theorem eq_of_commutator_eq_of_le {a : G} {K K' U₀ : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 a) (hK' : K' ∈ thetaComponentsAt 3 a) (hU₀ : U₀ ≤ K')
    (hKU : ⁅K, U₀⁆ = K) : K = K' := by
  by_contra hne
  have hcomm := Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK hK' hne
  have hKle : K ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
    refine le_trans ?_ hcomm
    rw [← hKU]
    exact (Subgroup.commutator_mono le_rfl hU₀).trans (by rw [hKU])
  obtain ⟨T, hT, rfl⟩ := hK
  obtain ⟨hθs, -, -⟩ := solvable_prime_complement_core_characterization
    (H := ↥(Subgroup.centralizer ({a} : Set G))) Nat.prime_three
  have hTle : T ≤ aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)) :=
    (Subgroup.map_le_map_iff_of_injective (Subgroup.subtype_injective _)).1 hKle
  have hTs : Group.IsSolvable ↥T := by
    have : Group.IsSolvable ↥(T.subgroupOf (aschbacherSolvableCore 3
        ↥(Subgroup.centralizer ({a} : Set G)))) := inferInstance
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.inclusion hTle)) (Subgroup.inclusion_injective hTle)
  obtain ⟨hTperf, -, hTq⟩ := hT
  have hs : Group.IsSolvable (↥T ⧸ aschbacherSolvableCore 3 ↥T) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥T))
      (QuotientGroup.mk'_surjective _)
  exact not_isSolvable_of_isQuasisimple'' hTq hs

@[expose] def Sec217SecondB : Prop :=
  ∀ (A E U : Subgroup G) (c : G) (L : Subgroup G), Cover217 A E U c L → ∀ a : G,
    Frame217 E c L a → ∀ U₀ ∈ fourGroupsMinus E, U₀ ≤ iCore L a →
      ∀ K ∈ lThreeStarAt A a, (a, K) ∈ lThreeStarPairs A E U₀ →
        (Nonempty (lBar K ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar K) NativeSporadic.J3) ∧
        iCore L a ≤ K

section Main

set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Cover217.exists_component_ge_iCore (h48 : Sec4.Item4_8) {A E U : Subgroup G} {c : G}
    {L : Subgroup G} (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L)
    {a : G} (hfr : Frame217 E c L a) :
    ∃ K' ∈ thetaComponentsAt 3 a, iCore L a ≤ K' := by
  have hEA : E ≤ A := h.pair.mem_E.2
  have ha := hfr.valid hEA
  obtain ⟨a', I', ha'G, -, -, -, ⟨φ⟩, hI, -⟩ := h.local_frame hθ hAL ha
  have hpair := mem_lThreeStarPairs_iff.mp h.pair.mem_pair
  have hcE : c ∈ E := hpair.1.1
  have hc1 : c ≠ 1 := hpair.2.1
  have ha1 : a ≠ 1 := fun h1 => hfr.not_mem (h1 ▸ Subgroup.one_mem _)
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({a} : Set G)) :=
    h.pair.toSec21Std.standing.toTheoremFourHyp.sectionFourHyp
      (Sec6.centralizer_ne_top_of_ne_one h.pair.toSec21Std.standing.toTheoremFourHyp ha1)
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpair.2.2.1
  have hE27 := Late.isE27_of_mem_partTwoE h.pair.mem_E.1
  obtain ⟨hJperf0, -⟩ : Group.IsPerfect ↥(perfectResidual ↥(L ⊓ Subgroup.centralizer ({a} : Set G))) ∧
      True := ⟨(perfect_residual_characterization
        (G := ↥(L ⊓ Subgroup.centralizer ({a} : Set G)))).2.2.1, trivial⟩
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) with hJ
  have hJperf : Group.IsPerfect ↥J :=
    Group.IsPerfect.ofSurjective
      (f := ((perfectResidual ↥(L ⊓ Subgroup.centralizer ({a} : Set G))).equivMapOfInjective _
        (Subgroup.subtype_injective _)).toMonoidHom) (MulEquiv.surjective _)
  have hJC : J ≤ Subgroup.centralizer ({a} : Set G) ⊓ L := by
    rw [inf_comm]; exact Subgroup.map_subtype_le _
  have hJle : J ≤ iCore L a := le_sSup ⟨hJC, (isPerfect_iff_commutator_eq J).1 hJperf⟩
  have hIperf : ⁅I', I'⁆ = I' := by
    have := perfect_of_equiv_alt6 I' φ
    exact this
  have hIle : iCore L a ≤ J := by
    rw [hI]
    refine KFacts.le_inSubgroup_perfectResidual ?_ ?_
    · refine (isPerfect_iff_commutator_eq _).2 ?_
      rw [← Subgroup.map_commutator, hIperf]
    · have hIC : iCore L a ≤ L ⊓ Subgroup.centralizer ({a} : Set G) := by
        rw [inf_comm]; exact sSup_le fun _ hK => hK.1
      rwa [hI] at hIC
  have hJI : J = iCore L a := le_antisymm hJle hIle
  have hJq : IsQuasisimple (↥J ⧸ aschbacherSolvableCore 3 ↥J) := by
    have e : ↥J ≃* alternatingGroup (Fin 6) :=
      (MulEquiv.subgroupCongr (hJI.trans hI)).trans
        (((I'.equivMapOfInjective L.subtype L.subtype_injective).symm).trans φ)
    have hA6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    have : IsSimpleGroup ↥J := @MulEquiv.isSimpleGroup _ _ _ _ hA6 e
    refine isQuasisimple_quot_theta_of_simple ?_
    by_contra hcomm
    push Not at hcomm
    letI : CommGroup ↥J := { (inferInstance : Group ↥J) with mul_comm := hcomm }
    have hp := IsSimpleGroup.prime_card (α := ↥J)
    have hcard : Nat.card ↥J = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    rw [hcard] at hp
    exact absurd hp (by norm_num)
  obtain ⟨K', hK', hJK'⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4 hE27 hcE
    hfr.mem hc1 hLc hJq
  exact ⟨K', hK', hJI ▸ hJK'⟩

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
