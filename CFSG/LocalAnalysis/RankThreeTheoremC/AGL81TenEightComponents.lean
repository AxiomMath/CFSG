module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.ComponentsK
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34Of
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenClaimOf
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem IsTwoPrimeComponent.of_le {M X J : Subgroup G} (hJ : IsTwoPrimeComponent M J)
    (hJX : J ≤ X) (hXM : X ≤ M) : IsTwoPrimeComponent X J := by
  have hsub : IsSubnormal J X :=
    CFSG.AGLEmbeddingD2.isSubnormal_of_le_of_isSubnormal hJ.subnormal hJX hXM
  have hX : J ⊓ pCoreOf 2 X = pCoreOf 2 J := by
    apply le_antisymm
    · refine normal_pGroup_le_pCoreOf 2 _ J inf_le_left ?_
        ((pCoreOf_isPGroup 2 X).to_le inf_le_right)
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      exact common_normalizer_le_normalizer_inf J J _ Subgroup.le_normalizer
        (hJX.trans (localGroup_le_normalizer_pCoreOf 2 X))
    · exact le_inf (pCoreOf_le 2 J) (cfsg_subnormal_pCoreOf_le 2 hsub)
  obtain ⟨e⟩ := CFSG.AGLEmbeddingD2.nonempty_mulEquiv_barM_of_inf_eq hJX hJ.le
    (hX.trans hJ.inf_twoCore.symm)
  refine ⟨hJX, hsub, hJ.perfect, le_top, ?_, ?_⟩
  · have h1 := cfsg_isSubnormal_comap X.subtype hsub
    rw [show X.comap X.subtype = ⊤ from Subgroup.subgroupOf_self X] at h1
    have h2 := cfsg_isSubnormal_map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) h1
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e hJ.component.2.2

omit [Finite G] in
theorem IsTwoPrimeComponent.map_mulAut {M J : Subgroup G} (hJ : IsTwoPrimeComponent M J)
    (φ : MulAut G) :
    IsTwoPrimeComponent (M.map φ.toMonoidHom) (J.map φ.toMonoidHom) := by
  set ψ : ↥M ≃* ↥(M.map φ.toMonoidHom) := MulEquiv.subgroupMap φ M with hψ
  have hcore : (CFSG.pCore 2 ↥M).map ψ.toMonoidHom =
      CFSG.pCore 2 ↥(M.map φ.toMonoidHom) := CFSG.pCore_map_iso 2 ψ
  set θ := QuotientGroup.congr (CFSG.pCore 2 ↥M) (CFSG.pCore 2 ↥(M.map φ.toMonoidHom)) ψ hcore
    with hθ
  have hsub : (J.subgroupOf M).map ψ.toMonoidHom =
      (J.map φ.toMonoidHom).subgroupOf (M.map φ.toMonoidHom) := by
    ext ⟨z, hz⟩
    constructor
    · rintro ⟨⟨x, hxM⟩, hxJ, hxz⟩
      exact ⟨x, hxJ, congrArg Subtype.val hxz⟩
    · intro hzJ
      obtain ⟨x, hxJ, rfl⟩ := hzJ
      exact ⟨⟨x, hJ.le hxJ⟩, hxJ, Subtype.ext rfl⟩
  have hbar : (barM M J).map θ.toMonoidHom =
      barM (M.map φ.toMonoidHom) (J.map φ.toMonoidHom) := by
    rw [barM, barM, Subgroup.map_map, ← hsub, Subgroup.map_map]
    exact congrArg (fun f => Subgroup.map f (J.subgroupOf M)) (MonoidHom.ext fun x => rfl)
  refine ⟨Subgroup.map_mono hJ.le, cfsg_isSubnormal_map φ.toMonoidHom hJ.subnormal, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hJ.perfect]
  · rw [← hbar]
    exact (CFSG.ComponentClassification.LocalComponents.equiv_iff θ _).mpr hJ.component

theorem exists_noncentral_of_two_component {X A : Subgroup G} (hA : IsTwoPrimeComponent X A)
    (h3 : 3 ∣ Nat.card A) :
    ∃ e ∈ barM X A, e ^ 3 = 1 ∧
      e ∉ Subgroup.centralizer (barM X A : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  have hAA : IsTwoPrimeComponent A A := IsTwoPrimeComponent.of_le hA le_rfl hA.le
  have hperf : CFSG.ComponentClassification.AS76b.oUpperTwo A = A :=
    SevenFourL34.oUpperTwo_eq_of_perfect hA.perfect
  obtain ⟨e, he, he3, hnc⟩ := TenTenClaim.exists_noncentral (M := X) (L := A) (X := A) (I₀ := A)
    hA.le ⟨le_rfl, IsSubnormal.refl A, Or.inl hAA⟩ le_rfl (by rwa [hperf])
  exact ⟨e, by rwa [hperf] at he, he3, hnc⟩

theorem two_le_pRank_three_of_two_components {X A B : Subgroup G}
    (hA : IsTwoPrimeComponent X A) (hB : IsTwoPrimeComponent X B) (hAB : A ≠ B)
    (h3A : 3 ∣ Nat.card A) (h3B : 3 ∣ Nat.card B) : 2 ≤ CFSG.Open.pRank 3 X := by
  obtain ⟨eA, heA, heA3, hncA⟩ := exists_noncentral_of_two_component hA h3A
  obtain ⟨eB, heB, heB3, hncB⟩ := exists_noncentral_of_two_component hB h3B
  obtain ⟨E, -, hE, hcard⟩ := TenTenClaim.exists_elemAbelian_of_family 2
    ![barM X A, barM X B] ![eA, eB]
    (fun i j hij => by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact TenTenClaim.barM_le_centralizer hA hB hAB
      · exact TenTenClaim.barM_le_centralizer hB hA hAB.symm
      · exact absurd rfl hij)
    (fun i => by
      fin_cases i
      exacts [heA, heB])
    (fun i => by
      fin_cases i
      exacts [heA3, heB3])
    (fun i => by
      fin_cases i
      exacts [hncA, hncB])
  obtain ⟨E', hE'X, hE', hcard'⟩ := TenTenClaim.exists_elemAbelian_lift le_rfl hE
    ((TenTenClaim.barM_self X).symm ▸ le_top)
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hE'X hE' (hcard'.trans hcard)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenEight
