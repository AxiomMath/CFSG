module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Pair2E6Image

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.ClassicalInvolution.RouteD (path6 path6_ne theta6)
open scoped MatrixGroups

section Normal

variable {k : Type} [Field k] [Finite k]

theorem normal_range_theta6 (hF : ringChar k ≠ 2) (hε : Function.Injective (e6Isogeny k))
    {Θ : SL(6, k) →* ↥(e6Data_valid.minGroup k)}
    (hrange : Θ.range = ⨆ i : Fin 5, CFSG.LieType.CurtisTits.rankOne
      (e6Datum k).rootGroup (path6 i))
    {u : ↥(e6Data_valid.minGroup k)}
    (hu : e6EpsK k u = rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : kˣ))) :
    (Θ.range.subgroupOf (Subgroup.centralizer ({u} : Set ↥(e6Data_valid.minGroup k)))).Normal := by
  have hmap : Θ.range.map (e6EpsK k) = subsystemGroup .E6 k JE6 := by
    rw [hrange]
    exact map_iSup_rankOne_e6K
  have hcomm : ∀ y ∈ ⨆ i : Fin 5, CFSG.LieType.CurtisTits.rankOne
      (e6Datum k).rootGroup (path6 i),
      ∀ r ∈ (e6Datum k).rootGroup theta6 ⊔ (e6Datum k).rootGroup (-theta6),
        y * r = r * y :=
    commutes_iSup_rankOne_theta_e6K
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have hgu := Subgroup.mem_centralizer_singleton_iff.1 g.2
  have hcg : rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : kˣ)) * e6EpsK k ↑g =
      e6EpsK k ↑g * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : kˣ)) := by
    rw [← hu, ← map_mul, ← map_mul, hgu]
  obtain ⟨n, hn, A, hA⟩ := exists_levi_form_e6 hF (e6Isogeny k ↑g).2 hcg
  replace hA : e6EpsK k ↑g = n * rootSL2 .E6 k thetaE6 A := hA
  have hρ : (⟨rootSL2 .E6 k thetaE6 A,
      CFSG.LieType.Chevalley.rootSL2_mem_adjointGroup thetaE6 A⟩ :
      ↥(adjointGroup .E6 k)) ∈ stdRankOne (e6AdjDatum k) thetaE6 :=
    (mem_stdRankOne_e6_iff_gen isRoot_thetaE6 _).2 ⟨A, rfl⟩
  rw [← map_stdRankOne_e6_genK isRoot_thetaE6] at hρ
  obtain ⟨r, hr, hre⟩ := Subgroup.mem_map.1 hρ
  have hr' : r ∈ (e6Datum k).rootGroup theta6 ⊔ (e6Datum k).rootGroup (-theta6) :=
    Eq.mp (congrArg (fun t : Fin (Tag.rank .E6) → ℤ => r ∈ (e6Datum k).rootGroup t ⊔
      (e6Datum k).rootGroup (-t)) thetaE6_eq_theta6) hr
  have hρe : e6EpsK k r = rootSL2 .E6 k thetaE6 A := congrArg Subtype.val hre
  have hcρ : e6EpsK k r * e6EpsK k ↑x = e6EpsK k ↑x * e6EpsK k r := by
    rw [← map_mul, ← map_mul, (hcomm ↑x (by rw [← hrange]; exact hx) r hr').symm]
  have hxN : e6EpsK k ↑x ∈ subsystemGroup .E6 k JE6 := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hx
  have hnN : n * e6EpsK k ↑x * n⁻¹ ∈ subsystemGroup .E6 k JE6 :=
    (Subgroup.mem_normalizer_iff.1 (parabolicLevi_le_normalizer_subsystemGroup_e6 JE6 hn)
      _).1 hxN
  rw [← hmap] at hnN
  obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.1 hnN
  have hzeq : z = ↑g * ↑x * (↑g)⁻¹ := by
    refine e6EpsK_injective hε ?_
    rw [hze, map_mul, map_mul, map_inv, hA, ← hρe]
    calc n * e6EpsK k ↑x * n⁻¹ =
        n * (e6EpsK k r * e6EpsK k ↑x) * (e6EpsK k r)⁻¹ * n⁻¹ := by
          rw [hcρ]; group
      _ = _ := by group
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hzeq]
  exact hz

end Normal

end CFSG.OddStandard.HigherRank.F3
