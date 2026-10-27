module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.MinimalSimpleProperSubgroupPLengthOne
import CFSG.FeitThompson.Local.ElementaryMaximalPLengthOneConstraint
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem card_eq_pow_elementaryAbelianPRank_of_isElementaryAbelianSubgroup (hp : p.Prime)
    {A : Subgroup G} (hA : IsElementaryAbelianSubgroup p A) :
    Nat.card ↥A = p ^ elementaryAbelianPRank p ↥A := by
  have := Fact.mk hp
  obtain ⟨d, hd⟩ := hA.isPGroup.exists_card_eq
  have := hA.isMulCommutative
  rw [hd, elementaryAbelianPRank_eq_of_card_eq hp hA.pow_eq_one hd]

theorem exists_normalPComplement_commutator_of_maximal_plane [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hp : p.Prime)
    {R A X : Subgroup G} (hR : Nat.card ↥R = p ^ (Nat.card G).factorization p) (hAR : A ≤ R)
    (hAcard : Nat.card ↥A = p ^ 2) (hAmax : Maximal (IsElementaryAbelianSubgroup p) A)
    (hX : X ≠ ⊤) (hRX : R ≤ X) :
    (pComplCore p ↥X ⊓ commutator ↥X).map X.subtype ≤ ⁅X, X⁆ ∧
      (⁅X, X⁆ : Subgroup G) ≤ normalizer (((pComplCore p ↥X ⊓ commutator ↥X).map X.subtype :
          Subgroup G) : Set G) ∧
      ¬ p ∣ Nat.card ↥((pComplCore p ↥X ⊓ commutator ↥X).map X.subtype) ∧
      ∃ n : ℕ, ((pComplCore p ↥X ⊓ commutator ↥X).map X.subtype).relIndex ⁅X, X⁆ = p ^ n := by
  have := Fact.mk hp
  have hXsolv : Group.IsSolvable ↥X := hsolv X hX
  have hoddX : Odd (Nat.card ↥X) := hodd.of_dvd_nat X.card_subgroup_dvd_card
  have hpX : p ∣ Nat.card ↥X :=
    ((dvd_pow_self p two_ne_zero).trans (hAcard ▸ dvd_refl _)).trans
      (card_dvd_of_le (hAR.trans hRX))
  have hfact : (Nat.card ↥X).factorization p = (Nat.card G).factorization p :=
    le_antisymm
      ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
        ((Nat.ordProj_dvd (Nat.card ↥X) p).trans X.card_subgroup_dvd_card))
      ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (hR ▸ card_dvd_of_le hRX))
  have hP : Nat.card ↥(R.subgroupOf X) = p ^ (Nat.card ↥X).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRX).toEquiv, hR, hfact]
  have hV : ¬ p ∣ (pComplPCore p ↥X).index :=
    hasPLengthLeOne_iff_not_dvd_index_pComplPCore.1
      (hasPLengthLeOne_of_ne_top hna hodd hsolv hX hp)
  have halt : IsCyclic ↥(R.subgroupOf X) ∨
      ∃ B : Subgroup ↥(R.subgroupOf X),
        Maximal (IsElementaryAbelian p) B ∧ Nat.card ↥B = p ^ 2 := by
    refine Or.inr ⟨(A.subgroupOf R).map (subgroupOfEquivOfLe hRX).symm.toMonoidHom, ?_, ?_⟩
    · exact (maximal_congr fun _ => isElementaryAbelian_iff_isElementaryAbelianSubgroup).2
        (maximal_isElementaryAbelianSubgroup_map _
          (maximal_isElementaryAbelianSubgroup_subgroupOf hAmax hAR))
    · rw [Subgroup.card_map_of_injective (MulEquiv.injective _),
        Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv, hAcard]
  have key := isNormalPComplement_inf_commutator (X := ↥X) (P := R.subgroupOf X)
    hp hoddX hpX hP hV halt
  have hNnormal : (pComplCore p ↥X ⊓ commutator ↥X).Normal := Subgroup.normal_inf_normal _ _
  have hcardN : Nat.card ↥((pComplCore p ↥X ⊓ commutator ↥X).subgroupOf (commutator ↥X))
      = Nat.card ↥(pComplCore p ↥X ⊓ commutator ↥X) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (pComplCore p ↥X ⊓ commutator ↥X).map X.subtype
        ≤ (commutator ↥X).map X.subtype := map_mono inf_le_right
      _ = ⁅X, X⁆ := map_subtype_commutator X
  · exact (commutator_le_self X).trans (le_normalizer_map_subtype_of_normal hNnormal)
  · rw [Subgroup.card_map_of_injective X.subtype_injective, ← hcardN]
    exact key.not_dvd_natCard
  · obtain ⟨n, hn⟩ := key.exists_index_eq_pow
    refine ⟨n, ?_⟩
    rw [← map_subtype_commutator X, relIndex_map_map_of_injective _ _ X.subtype_injective]
    exact hn

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson

universe u

theorem FNI_ambient_maximal_plane_derived_prime_complement :
    Statements.FNI_ambient_maximal_plane_derived_prime_complement.{u} := by
  intro G _ _ hG p R A hp hR hAR hA hArank hAmax X hX hRX
  have := hG.isSimpleGroup
  have hAcard : Nat.card ↥A = p ^ 2 := by
    rw [card_eq_pow_elementaryAbelianPRank_of_isElementaryAbelianSubgroup hp hA, hArank]
  have hAmax' : Maximal (IsElementaryAbelianSubgroup p) A :=
    ⟨hA, fun B hB hAB => (hAmax B hB hAB).le⟩
  exact ⟨_, exists_normalPComplement_commutator_of_maximal_plane hG.not_isMulCommutative
    hG.odd_natCard hG.forall_isSolvable hp hR hAR hAcard hAmax' hX.ne hRX⟩

end

end CFSG.FeitThompson.Proofs
