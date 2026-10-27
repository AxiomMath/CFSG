module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Main

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Universal
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi

section Torus

variable {K : Type} [Field K]

theorem rootTorusSL2_eq_thetaDiag_e6 {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (c : Kˣ) : rootTorusSL2 .E6 K γ c = rootDiagUnit .E6 (thetaDiag γ c) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport .E6 K hγ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single .E6 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit .E6 a : ModGL .E6 K) : Module.End K (RootModule .E6 K))
      (rootVec .E6 K (Pi.single i 1))) = ((a i : Kˣ) : K) • rootVec .E6 K (Pi.single i 1) := by
    change rootDiag a (rootVec .E6 K (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single .E6 i), hs]
  rw [h2] at h1
  have hne : rootVec .E6 K (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single .E6 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective K hne h1
  have h4 : 2 * iform γ (Pi.single i 1) / iform γ γ = iform γ (Pi.single i 1) := by
    rw [iform_self_isRoot_E6 hγ]
    omega
  rw [h4] at h3
  exact Units.ext h3

end Torus

section Adjoint

variable {K : Type} [Field K]

theorem mem_stdRankOne_e6_iff_gen {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (r : ↥(adjointGroup .E6 K)) :
    r ∈ stdRankOne (e6AdjDatum K) γ ↔
      ∃ A : SL2 K, (r : ModGL .E6 K) = rootSL2 .E6 K γ A := by
  have hb := subgroupOf_rootSubgroup_sup_eq (K := K) (rootOperatorFamily .E6) hγ
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E6 K hγ).1
  change r ∈ rootGroup (rootOperatorFamily .E6) K γ ⊔
    rootGroup (rootOperatorFamily .E6) K (-γ) ↔ _
  rw [← hb, Subgroup.mem_subgroupOf, ← hL, rootRankOneGroup, MonoidHom.mem_range]
  exact exists_congr fun A => eq_comm

theorem central_stdRankOne_e6_gen (hK : ringChar K ≠ 2) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) {z : ↥(adjointGroup .E6 K)} (hz : z ∈ stdRankOne (e6AdjDatum K) γ)
    (hzc : ∀ r ∈ stdRankOne (e6AdjDatum K) γ, z * r = r * z) :
    (z : ModGL .E6 K) = 1 ∨
      (z : ModGL .E6 K) = rootDiagUnit .E6 (thetaDiag γ (-1 : Kˣ)) := by
  obtain ⟨A, hA⟩ := (mem_stdRankOne_e6_iff_gen hγ z).1 hz
  have hinj : Function.Injective (rootSL2 .E6 K γ) :=
    ((exceptional_Lang_root_rank_one_data .E6 K γ).2.2.2.2.2.2.2.1 hK).1
  have hcomm : ∀ B : SL2 K, A * B = B * A := fun B => by
    apply hinj
    have hB : (⟨rootSL2 .E6 K γ B, rootSL2_mem_adjointGroup _ _⟩ :
        ↥(adjointGroup .E6 K)) ∈ stdRankOne (e6AdjDatum K) γ :=
      (mem_stdRankOne_e6_iff_gen hγ _).2 ⟨B, rfl⟩
    have := congrArg Subtype.val (hzc _ hB)
    simp only [Subgroup.coe_mul] at this
    rw [hA] at this
    rw [map_mul, map_mul]
    exact this
  rcases eq_one_or_HSL_neg_one_of_forall_commute hcomm with h | h
  · left
    rw [hA, h, map_one]
  · right
    rw [hA, h]
    exact rootTorusSL2_eq_thetaDiag_e6 hγ (-1)

theorem map_stdRankOne_e6_gen {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) :
    (stdRankOne (e6Datum (GaloisField 3 1)) γ).map (e6Isogeny (GaloisField 3 1)) =
      stdRankOne (e6AdjDatum (GaloisField 3 1)) γ := by
  change ((e6Datum (GaloisField 3 1)).rootGroup γ ⊔
      (e6Datum (GaloisField 3 1)).rootGroup (-γ)).map (e6Isogeny (GaloisField 3 1)) =
    rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) γ ⊔
      rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) (-γ)
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (map_e6Isogeny_rootGroup _ hγ)
    (map_e6Isogeny_rootGroup _ (IsRoot.neg hγ))

end Adjoint

end CFSG.OddStandard.HigherRank.F3
