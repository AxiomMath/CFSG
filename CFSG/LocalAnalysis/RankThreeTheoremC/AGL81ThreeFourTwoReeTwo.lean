module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryOvergroup
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoInf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeWhole

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup CFSG.LieType.Ree CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


private theorem isSimpleGroup_reeGamma {a : ℕ} (ha : 1 ≤ a) :
    IsSimpleGroup (ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a) := by
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨hDs, -, -, htop, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components a
      (GaloisField 3 (2 * a + 1)) hK
  exact (MulEquiv.isSimpleGroup_congr
    ((MulEquiv.subgroupCongr (htop ha)).trans Subgroup.topEquiv)).1 hDs

theorem reeTwo_catalog_facts {m : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : d.1 = .reeG2 m) :
    IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group ∧
      (∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a) ∧
      Group.IsSolvable (Outer (TauCeti.CFSGIndex.lie d).Group) := by
  have hdR : IsReeGTwoIndex 3 d := ⟨rfl, m, hd⟩
  obtain ⟨a, ha, -, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hdR ⟨MulEquiv.refl _⟩
  haveI := isSimpleGroup_reeGamma ha
  haveI : Finite (ModGL ReeTag.G2.tag (GaloisField 3 (2 * a + 1))) :=
    CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.symm.toEquiv
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := (MulEquiv.isSimpleGroup_congr e).2 ‹_›
  refine ⟨inferInstance, ?_, kFactReeOuterSolvable _ d hdR ⟨MulEquiv.refl _⟩⟩
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  refine exists_mul_ne_of_sq_dvd_card Nat.prime_three ?_ Nat.card_pos.ne'
  rw [Nat.card_congr e.toEquiv, (ReeModel.std_facts hK).2.2.2, mul_assoc]
  refine Dvd.dvd.mul_right ?_ _
  rw [← pow_mul]
  exact pow_dvd_pow 3 (by omega)

theorem reeTwo_isSolvable_of_sylow_le {m : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : d.1 = .reeG2 m) {L : Type} [Group L] [Finite L]
    (hL : Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) (T : Sylow 3 L) (H : Subgroup L)
    (hTH : (T : Subgroup L) ≤ H) (hH : H ≠ ⊤) : Group.IsSolvable H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha, -, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma ⟨rfl, m, hd⟩ hL
  set F := GaloisField 3 (2 * a + 1)
  have hK : Nat.card F = 3 ^ (2 * a + 1) := GaloisField.card 3 (2 * a + 1) (by omega)
  haveI : Finite (ModGL ReeTag.G2.tag F) := CFSG.LieType.Chevalley.finite_modGL
  haveI := isSimpleGroup_reeGamma ha
  obtain ⟨⟨P, hP⟩, hNU, -, hcard⟩ := ReeModel.std_facts hK
  obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq e T P
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, -, hreg, -, -, -, -, hstab, -⟩ :=
    small_Ree_Borel_coset_Sylow_action a F hK w₀ hw₀
  have hU : ReeModel.stdU a F ≠ ⊥ := by
    rw [← hP]
    refine P.ne_bot_of_dvd_card ?_
    rw [hcard]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (dvd_pow (dvd_pow_self 3 (by omega)) three_ne_zero) _) _
  letI : MulAction (ReeTag.G2.reeGamma F a) (ReeTag.G2.reeGamma F a ⧸
      (ReeTag.G2.reeFixedBorel F a).subgroupOf (ReeTag.G2.reeGamma F a)) :=
    MulAction.quotient _ _
  have hle : H.map e'.toMonoidHom ≤ MulAction.stabilizer (ReeTag.G2.reeGamma F a)
      (QuotientGroup.mk 1 : ReeTag.G2.reeGamma F a ⧸
        (ReeTag.G2.reeFixedBorel F a).subgroupOf (ReeTag.G2.reeGamma F a)) := by
    refine UnitaryModel.le_stabilizer_of_isSimpleGroup hU (hstab.trans hNU.symm).le
      (fun β γ hβ hγ => ?_) ?_ ?_
    · obtain ⟨u, hu, -⟩ := hreg β γ hβ hγ
      exact ⟨u, u.2, hu⟩
    · rw [← hP, ← he']
      exact map_mono hTH
    · intro htop
      apply hH
      have h := congrArg (Subgroup.comap e'.toMonoidHom) htop
      rwa [Subgroup.comap_map_eq_self_of_injective e'.injective, Subgroup.comap_top] at h
  rw [hstab] at hle
  haveI : Group.IsSolvable
      ((ReeTag.G2.reeFixedBorel F a).subgroupOf (ReeTag.G2.reeGamma F a)) :=
    ReeModel.isSolvable_stdB
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.inclusion hle).comp
      (Subgroup.equivMapOfInjective H e'.toMonoidHom e'.injective).toMonoidHom)
    ((Subgroup.inclusion_injective hle).comp
      (Subgroup.equivMapOfInjective H e'.toMonoidHom e'.injective).injective)

theorem threeFourTwoReeTwo_inf {m : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : d.1 = .reeG2 m) {Y : Type} [Group Y] [Finite Y] {K Y₀ : Subgroup Y} (R : Sylow 3 Y)
    (hK : K.Normal) (hKX : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hRY₀ : (R : Subgroup Y) ≤ Y₀) (hKY₀ : ¬ K ≤ Y₀) : Group.IsSolvable (K ⊓ Y₀ : Subgroup Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isSolvable_inf_of_forall_sylow_le R
    (fun T H hTH hH => reeTwo_isSolvable_of_sylow_le hd hKX T H hTH hH) hRY₀ hKY₀

theorem threeFourTwoReeTwo_holds :
    ThreeFourTwoReeTwo := by
  intro m d hd
  obtain ⟨hX, hnab, hout⟩ := reeTwo_catalog_facts hd
  refine threeFourTwoNoneAt_of_inf hX hnab hout ?_
  intro Y _ _ K Y₀ E R _ _ hK hKX _ _ _ _ _ _ _ hRY₀ hKY₀
  exact Or.inl (threeFourTwoReeTwo_inf hd R hK hKX hRY₀ hKY₀)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
