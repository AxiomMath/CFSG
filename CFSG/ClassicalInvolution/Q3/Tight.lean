module

public import CFSG.ClassicalInvolution.Q3.Closing
public import CFSG.ClassicalInvolution.SmallCases.Partition
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

theorem isSolvable_sl2Three : Group.IsSolvable SL(2, ZMod 3) := by
  have hp : IsPGroup 2 sl2ThreeQ :=
    IsPGroup.of_card (n := 3) (by rw [natCard_sl2ThreeQ]; norm_num)
  have : Group.IsNilpotent sl2ThreeQ := hp.isNilpotent
  have := sl2ThreeQ_normal
  have : Group.IsSolvable (SL(2, ZMod 3) ⧸ sl2ThreeQ) := by
    have hc : Nat.card (SL(2, ZMod 3) ⧸ sl2ThreeQ) = 3 := by
      have := sl2ThreeQ_index
      rw [Subgroup.index] at this
      exact this
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have : IsCyclic (SL(2, ZMod 3) ⧸ sl2ThreeQ) := isCyclic_of_prime_card hc
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient sl2ThreeQ

section Member

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {z : Y}

theorem IsClassicalMember3.isSolvable (h : IsClassicalMember3 L z) : Group.IsSolvable L := by
  obtain ⟨e⟩ := h.nonempty_equiv
  have hO : Group.IsSolvable (classicalInvolutionOddCore L) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card L)
  have hq : Group.IsSolvable (L ⧸ classicalInvolutionOddCore L) :=
    have := isSolvable_sl2Three
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.isSolvable_of_subgroup_quotient (classicalInvolutionOddCore L)

omit [Finite Y] in
theorem IsClassicalMember3.witness (h : IsClassicalMember3 L z) : classicalInvolutionWitness L := by
  obtain ⟨e⟩ := h.nonempty_equiv
  have hcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  obtain ⟨e'⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hcard
  exact Or.inl ⟨3, 1, ⟨Nat.prime_three⟩, by norm_num, one_pos, ⟨e.trans e'.symm⟩⟩

end Member

@[expose] def TightLift3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    ∀ t : G, t ∈ (S : Subgroup R).map R.subtype → orderOf t = 2 →
    R ≤ Subgroup.centralizer ({t} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal →
    IsPGroup 2 (R ⧸ classicalInvolutionOddCore R) →
    ∃ J : Subgroup G, R ≤ J ∧ IsClassicalMember3 J t

abbrev NormalOddByQuaternionLarge : Prop :=
  NormalOddByQuaternionUnder fun {G} _ _ _ => ¬ TwoSubgroupsFourGenerated (genFittingFStar G)

theorem normalOddByQuaternionLarge_of_cit3Inductive (h : CIT3Inductive) (h0 : ModelClauseZero)
    (hM : M11Facts) (hlift : TightLift3) : NormalOddByQuaternionLarge := by
  intro G _ _ _ hFnonab R S hS t ht hto hRC hRn h2 hlarge
  obtain ⟨J, -, hJ⟩ := hlift G hFnonab hlarge R S hS t ht hto hRC hRn h2
  obtain ⟨hC, hO⟩ := centralizer_fstar_eq_bot_and_oddCore_eq_bot hFnonab
  have : (genFittingFStar G).Normal := genFittingFStar_normal G
  have := oddLieType_or_isSporadic_of_aschbacherCIT3 (aschbacherCIT3_of_cit3Inductive h h0 hM)
    (genFittingFStar G) hFnonab hC hO hJ.orderOf_eq_two hJ.mem hJ.subnormal hJ.isSolvable
    hJ.witness
  exact this.elim Or.inl fun h => Or.inr (Or.inl h)

end CFSG.ClassicalInvolution.Q3
