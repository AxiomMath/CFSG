module

public import CFSG.LocalAnalysis.RankThreeTheoremC.OuterSylowGlue
import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
import CFSG.LieType.SeitzGeneration.ExcParabolicReeG2
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
import CFSG.LieType.SeitzGeneration.ExcPlaneModel
import CFSG.LocalAnalysis.AGLEmbeddingD2.SeitzTitsThree
import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalOuter
import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.ComponentClassification.OuterAutomorphisms

theorem sylow_normal_outer_suzuki
    {p : ℕ} (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    ∀ S : Sylow p (Outer (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group)).Normal := by
  haveI : IsCyclic (Outer (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group) :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} _ 2 (2 * m + 1)
      (CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv)).1.1
  exact fun S => sylow_normal_of_isCyclic S

theorem sylow_normal_outer_reeF4
    {p : ℕ} (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) :
    ∀ S : Sylow p (Outer (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group)).Normal := by
  haveI : IsCyclic (Outer (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) :=
    (CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_model_field_outer_group_and_inner_involutions
      _ 2 (2 * m + 1) (CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv)).2.2.2.1
  exact fun S => sylow_normal_of_isCyclic S

theorem sylow_normal_outer_reeG2
    {p : ℕ} (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) :
    ∀ S : Sylow p (Outer (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group)).Normal := by
  have hm : 1 ≤ m := by
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  obtain ⟨X, _, _, _, hX, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat_G2 hv
  have := (CFSG.ComponentClassification.LiteratureLocal.SmallRee.outer_reeGamma_cyclic hm hX).1
  haveI : IsCyclic (Outer (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group) :=
    isCyclic_of_surjective (equivalence e).symm.toMonoidHom (equivalence e).symm.surjective
  exact fun S => sylow_normal_of_isCyclic S

theorem sylow_normal_outer_G2
    {p : ℕ} (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (h3 : 3 ≤ q.p ^ q.exponent) :
    ∀ S : Sylow p (Outer (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group)).Normal := by
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := CFSG.RankThree.PartOne.CTP.exists_adjointG2_model
    (q := q) (K := (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) ⟨hv, ⟨MulEquiv.refl _⟩⟩
  have := GL83.I713.isCyclic_outer_adjointGroup_G2_of_card q.prime_p q.exponent_pos h3 hX
  haveI : IsCyclic (Outer (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) :=
    isCyclic_of_surjective (equivalence e).symm.toMonoidHom (equivalence e).symm.surjective
  exact fun S => sylow_normal_of_isCyclic S

theorem sylow_normal_outer_tits
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hv : TauCeti.LieTypeIndex.tits.Valid) :
    ∀ S : Sylow p (Outer (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group),
      (S : Subgroup (Outer (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group)).Normal := by
  have h2 : Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) = 2 :=
    CFSG.AGLEmbeddingD2.card_outer_tits_of_mulEquiv ⟨.tits, hv⟩ rfl (MulEquiv.refl _)
  haveI : Finite (Outer (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; norm_num)
  refine fun S => sylow_normal_of_not_dvd ?_ S
  rw [h2]
  intro hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp hd)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
