module

public import CFSG.ClassicalInvolution.Q3.Q3ZModel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.Q3W

theorem lieModel_psp3_of_surjective {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (ψ : StatedSp 3 (GaloisField 3 1) →* G)
    (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 3 (GaloisField 3 1))) :
    CFSG.Blueprint.LieModel G .PSp 3 3 1 := by
  have hZ : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hcen : Subgroup.center (StatedSp 3 (GaloisField 3 1)) ≤ ψ.ker := fun k hk => by
    have h : ψ k ∈ Subgroup.center G := Subgroup.map_center_le_center hsurj ⟨k, hk, rfl⟩
    rw [hZ, Subgroup.mem_bot] at h
    exact h
  have hkerEq : ψ.ker = Subgroup.center (StatedSp 3 (GaloisField 3 1)) := le_antisymm hker hcen
  let e : StatedSp 3 (GaloisField 3 1) ⧸ Subgroup.center (StatedSp 3 (GaloisField 3 1)) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)
  have hmodel : CFSG.Blueprint.LieModel
      (StatedSp 3 (GaloisField 3 1) ⧸ Subgroup.center (StatedSp 3 (GaloisField 3 1))) .PSp 3 3 1 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
      CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient 3 (GaloisField 3 1)
        statedLieAdmissible_psp3 (by rw [card_gf3, pow_one])⟩
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hmodel


theorem oddLieType_of_psi_psp3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 1 (CompData.model .PSp 2) (conjClass3 K) z)
    (hO3 : LocalOddThreeFree3 (conjClass3 K) z)
    (ψ : StatedSp 3 (GaloisField 3 1) →* G)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 3 (GaloisField 3 1)))
    (hlong : (Models.SymplecticPairs.longBlock (GaloisField 3 1) 3 2).range.map ψ ∈
      conjClass3 K) :
    Blueprint.OddLieType G := by
  obtain ⟨M⟩ := nonempty_extModel3_psp
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hΩψ : ∀ R ∈ fundamentalSubgroups .PSp (modelUniv .PSp 3 3 1 Nat.prime_three).D,
      R.map ψ ∈ conjClass3 K := by
    intro R hRf
    obtain ⟨P, hP, rfl⟩ := (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff
      statedLieAdmissible_psp3 R).1 hRf
    obtain ⟨g, hg⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP (Fin.last 2)
    rw [hg, CFSG.LieType.Steinberg.map_map_conj]
    exact hR.inClass.conjInvariant _ _ hlong
  obtain ⟨hsurj, -⟩ := routeD_core3 (le_refl 1) fundamentalSingleClass_psp3 finite_psp2 M
    hR.inClass hex hK hsingle hconn hR.cls hshape hP1 hO3 ψ hker hΩψ
  exact ⟨.PSp, 3, 3, 1, Nat.prime_three, by norm_num, statedLieAdmissible_psp3,
    lieModel_psp3_of_surjective hnab ψ hsurj hker⟩

end CFSG.ClassicalInvolution.Q3.Q3Z
