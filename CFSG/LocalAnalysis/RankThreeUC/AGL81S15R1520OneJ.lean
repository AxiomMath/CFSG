module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.E1Sections
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneI
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem pRank_pComponent_le_one_of_compositionFactor {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hS : ∀ (S : Type) [Group S] [Finite S], CFSG.Quasithin.E1.IsCompositionFactor X S →
      ¬ Group.IsSolvable S → CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1)
    {I : Subgroup X} (hI : CFSG.IsPComponent p I) : CFSG.Open.pRank p I ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK, hIsub, hIK, -⟩ := hI
  subst hIK
  set π := QuotientGroup.mk' (CFSG.pPrimeCore p X)
  set ψ := π.subgroupMap I
  have hψ : Function.Surjective ψ := π.subgroupMap_surjective I
  have hker : ¬ p ∣ Nat.card ψ.ker := by
    have hle : ψ.ker.map I.subtype ≤ CFSG.pPrimeCore p X := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : π (x : X) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
        simpa [ψ] using this
      exact (QuotientGroup.eq_one_iff _).1 h1
    intro hdvd
    rw [← Subgroup.card_map_of_injective I.subtype_injective] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
      (hdvd.trans (Subgroup.card_dvd_of_le hle))
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup ↥(I.map π)) = CFSG.Open.pRank p I := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup I,
      ← CFSG.SectionRank.pRank_quotient_eq ψ.ker hker]
    exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).symm
  by_contra hgt
  push Not at hgt
  haveI : Group.IsPerfect ↥(I.map π) := hK.1.1
  haveI : IsSimpleGroup (↥(I.map π) ⧸ Subgroup.center ↥(I.map π)) := hK.1.2.1
  have h2 := two_le_pRank_quotient_center (K := ↥(I.map π)) hp hp2 (by omega)
  have hns : ¬ Group.IsSolvable (↥(I.map π) ⧸ Subgroup.center ↥(I.map π)) := fun hs => by
    obtain ⟨a, b, hab⟩ := hK.1.2.2
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 hs a b)
  set θ := (QuotientGroup.mk' (Subgroup.center ↥(I.map π))).comp ψ
  have hθ : Function.Surjective θ := (QuotientGroup.mk'_surjective _).comp hψ
  have hBI : (θ.ker.map I.subtype).subgroupOf I = θ.ker :=
    Subgroup.comap_map_eq_self_of_injective I.subtype_injective _
  haveI : ((θ.ker.map I.subtype).subgroupOf I).Normal := by
    rw [hBI]
    infer_instance
  let e := (QuotientGroup.quotientMulEquivOfEq hBI).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθ)
  have hcf : CFSG.Quasithin.E1.IsCompositionFactor X
      (↥(I.map π) ⧸ Subgroup.center ↥(I.map π)) :=
    ⟨θ.ker.map I.subtype, I, inferInstance, Subgroup.map_subtype_le _,
      (Subgroup.Normal.isSubnormal inferInstance).trans' hIsub, hIsub, e.isSimpleGroup, ⟨e⟩⟩
  have := hS _ hcf hns
  omega

end CFSG.LocalAnalysis.RankThreeUC.S15
