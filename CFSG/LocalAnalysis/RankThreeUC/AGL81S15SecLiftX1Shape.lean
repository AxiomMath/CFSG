module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Lift
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Setting
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15C118Sub
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftLeaves

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC

theorem eq_of_isComponentOf_of_isSolvable_quotient {Y : Type} [Group Y] [Finite Y]
    {N K : Subgroup Y} [N.Normal] (hs : Group.IsSolvable (Y ⧸ N))
    (hN : CFSG.Open.IsComponentOf N ⊤) (hK : CFSG.Open.IsComponentOf K ⊤) : K = N := by
  haveI := hs
  haveI : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
  exact CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le
    (CFSG.Assembly.isComponentOf_iff_open.2 hK) (CFSG.Assembly.isComponentOf_iff_open.2 hN)
    (CFSG.ComponentClassification.CatalogueBLinearTwo.perfect_le_normal_of_solvable_quotient N K)

private theorem nonempty_mulEquiv_quotient_center_of_surjective {P Q : Type} [Group P] [Group Q]
    (hP : CFSG.Open.IsQuasisimple P) (hQ : CFSG.Open.IsQuasisimple Q) {ψ : P →* Q}
    (hψ : Function.Surjective ψ) :
    Nonempty ((P ⧸ Subgroup.center P) ≃* (Q ⧸ Subgroup.center Q)) := by
  have hc : Subgroup.center P ≤ (Subgroup.center Q).comap ψ := fun a ha => by
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro b
    obtain ⟨a', rfl⟩ := hψ b
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 ha a']
  have hs : Function.Surjective (QuotientGroup.map _ _ ψ hc) := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, rfl⟩ := hψ b
    exact ⟨a, rfl⟩
  haveI := hP.2
  haveI := hQ.2.toNontrivial
  exact ⟨MulEquiv.ofBijective _
    ⟨CFSG.QuasithinUnique.SQTK.injective_of_isSimpleGroup_of_surjective _ hs, hs⟩⟩

variable {X : Type} [Group X] [Finite X]

private theorem exists_surjective_map_toStar_subgroupOf {T L M : Subgroup X} (hTM : T ≤ M)
    (hLM : L ≤ M) :
    ∃ ψ : ↥(L.map (toStar T)) →* ↥((L.subgroupOf M).map (toStar (T.subgroupOf M))),
      Function.Surjective ψ := by
  let ρ : ↥L →* ↥(L.map (toStar T)) := (toStar T).subgroupMap L
  let ρ₁ : ↥L →* ↥((L.subgroupOf M).map (toStar (T.subgroupOf M))) :=
    ((toStar (T.subgroupOf M)).subgroupMap (L.subgroupOf M)).comp
      (Subgroup.subgroupOfEquivOfLe hLM).symm.toMonoidHom
  have hker : ρ.ker ≤ ρ₁.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, Subtype.ext_iff] at hx ⊢
    change (QuotientGroup.mk (x : X) : X ⧸ gnC T) = 1 at hx
    change (QuotientGroup.mk (⟨x, hLM x.2⟩ : ↥M) : ↥M ⧸ gnC (T.subgroupOf M)) = 1
    rw [QuotientGroup.eq_one_iff] at hx
    rw [QuotientGroup.eq_one_iff, gnC_subgroupOf_eq hTM, Subgroup.mem_subgroupOf]
    exact gnC_le_centralizer_uCore M T hx
  obtain ⟨ψ, -, hψ, -⟩ := CFSG.AGLEmbedding.exists_surjective_comp_eq ρ
    (MonoidHom.subgroupMap_surjective _ _) ρ₁ ((MonoidHom.subgroupMap_surjective _ _).comp
      (Subgroup.subgroupOfEquivOfLe hLM).symm.surjective) hker
  exact ⟨ψ, hψ⟩

theorem nonempty_mulEquiv_quotient_center_map_toStar_subgroupOf {T L M : Subgroup X}
    (hTM : T ≤ M) (hLM : L ≤ M) (hq : CFSG.Open.IsQuasisimple ↥(L.map (toStar T)))
    (hq₁ : CFSG.Open.IsQuasisimple ↥((L.subgroupOf M).map (toStar (T.subgroupOf M)))) :
    Nonempty ((↥((L.subgroupOf M).map (toStar (T.subgroupOf M))) ⧸
        Subgroup.center ↥((L.subgroupOf M).map (toStar (T.subgroupOf M)))) ≃*
      (↥(L.map (toStar T)) ⧸ Subgroup.center ↥(L.map (toStar T)))) := by
  obtain ⟨ψ, hψ⟩ := exists_surjective_map_toStar_subgroupOf hTM hLM
  obtain ⟨e⟩ := nonempty_mulEquiv_quotient_center_of_surjective hq hq₁ hψ
  exact ⟨e.symm⟩

theorem nonempty_mulEquiv_map_toStar_subgroupOf_of_isSimpleGroup {T L M : Subgroup X}
    (hTM : T ≤ M) (hLM : L ≤ M) [IsSimpleGroup ↥(L.map (toStar T))]
    [Nontrivial ↥((L.subgroupOf M).map (toStar (T.subgroupOf M)))] :
    Nonempty (↥((L.subgroupOf M).map (toStar (T.subgroupOf M))) ≃* ↥(L.map (toStar T))) := by
  obtain ⟨ψ, hψ⟩ := exists_surjective_map_toStar_subgroupOf hTM hLM
  exact ⟨(MulEquiv.ofBijective ψ
    ⟨CFSG.QuasithinUnique.SQTK.injective_of_isSimpleGroup_of_surjective ψ hψ, hψ⟩).symm⟩

private theorem isSolvable_quotient_map_toStar_sup {T L : Subgroup X} (hT : IsPGroup 2 T)
    (hLn : L.Normal) [((L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T)))).Normal] :
    Group.IsSolvable ((↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T))) ⧸
      (L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T)))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ((↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T))) ⧸
      (L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T)))) := by
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := exists_pow_two_pow_mem_of_mem_normal_sup hLn hT m.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine Subgroup.mem_map_of_mem _ ?_
    rw [Subgroup.mem_subgroupOf, SubgroupClass.coe_pow]
    exact hk
  haveI := hp.isNilpotent
  infer_instance

theorem gnShape_sup_of_normal {T T₁ T₂ L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hX : GNSetting X T) (hg : GNGood T T₁ T₂) (hcomp : GNYComponent T T₁ T₂ Ls)
    (hlift : LiftOf T L Ls) (hLn : L.Normal) :
    GNShape (T.subgroupOf (L ⊔ T)) (T₁.subgroupOf (L ⊔ T)) (T₂.subgroupOf (L ⊔ T)) := by
  obtain ⟨hC2, rfl⟩ := hlift
  have hgn₁ := gnSetting_sup_of_normal hX hLn
  have hc := CFSG.Quasithin.IsC118Pair.subgroupOf (le_sup_right : T ≤ L ⊔ T) hg.c118
  have hLs₁ : CFSG.Open.IsComponentOf
      ((L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T)))) ⊤ :=
    isComponentOf_map_toStar_subgroupOf le_sup_right le_sup_left hLn hgn₁ hC2
      (not_le_gnC_of_liftOf hcomp.1 ⟨hC2, rfl⟩)
  haveI := hLn
  haveI : ((L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T)))).Normal :=
    (Subgroup.normal_subgroupOf : (L.subgroupOf (L ⊔ T)).Normal).map _
      (QuotientGroup.mk'_surjective _)
  intro K hK
  have hKe : K = (L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T))) :=
    eq_of_isComponentOf_of_isSolvable_quotient
      (isSolvable_quotient_map_toStar_sup hX.sylow.2.1 hLn) hLs₁ hK.1
  subst hKe
  refine ⟨CFSG.AGLEmbeddingD2.GN.commutator_eq_of_gnYComponent hgn₁ hc.2.1 hc.2.2.2.2.1
    hc.2.2.2.2.2.1 hK, ?_⟩
  have hq := hcomp.1.2.2
  have hq₁ := hLs₁.2.2
  rcases (hg.shape _ hcomp).2 with ⟨hcl, hro⟩ | ⟨n, hn, ⟨e⟩⟩
  · obtain ⟨e⟩ := nonempty_mulEquiv_quotient_center_map_toStar_subgroupOf
      (le_sup_right : T ≤ L ⊔ T) (le_sup_left : L ≤ L ⊔ T) hq hq₁
    exact Or.inl ⟨isClassicalTwoOrG2_of_mulEquiv e hcl, fun h => hro (rankOneChevTwo_of_equiv e h)⟩
  · have h5 : 5 ≤ Nat.card (Fin n) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      rcases hn with rfl | ⟨h8, -⟩ <;> omega
    haveI := alternatingGroup.isSimpleGroup h5
    haveI : IsSimpleGroup ↥(L.map (toStar T)) := e.isSimpleGroup
    haveI : Nontrivial ↥((L.subgroupOf (L ⊔ T)).map (toStar (T.subgroupOf (L ⊔ T)))) := by
      haveI := hq₁.2.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center _)).nontrivial
    obtain ⟨e₁⟩ := nonempty_mulEquiv_map_toStar_subgroupOf_of_isSimpleGroup
      (le_sup_right : T ≤ L ⊔ T) (le_sup_left : L ≤ L ⊔ T)
    exact Or.inr ⟨n, hn, ⟨e₁.trans e⟩⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
