module

public import CFSG.Assembly.E6FourNeighbourModel

import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Aut
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Holds

public section

namespace CFSG.Assembly

open Subgroup

section Holds

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped MatrixGroups
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.LocalAnalysis.GLTheoremA


theorem e6FourTwoLocalFive_holds : E6FourTwoLocalFive := by
  intro J _ _ hJ hZ
  obtain ⟨K, iF, iFin, iC, hK, ⟨e⟩⟩ := e6FourMark_exists_adjointGroup hJ hZ
  obtain ⟨ι, U, hι, hc, hU0, hU2, hN⟩ := E6CartanRankFourAux.e6_levi_witness (K := K)
  let ψ : Fin 4 → SL(2, K) →* J := fun i => e.toMonoidHom.comp (ι i)
  have hψ : ∀ i, Function.Injective (ψ i) := fun i => e.injective.comp (hι i)
  have hψc : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B) := fun i j hij A B => by
    show e (ι i A) * e (ι j B) = e (ι j B) * e (ι i A)
    rw [← map_mul, ← map_mul, hc i j hij A B]
  obtain ⟨w, -, hw⟩ := TwE6FourRankAux.exists_sq_add_add_one (F := K) (by rw [hK]; norm_num)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨E, hEel, hEcard, hEN⟩ := exists_elemAbelian_pow_of_commuting_sl2 (p := 5) (c5Mat w)
    (c5Mat_pow_five hw) (c5Mat_ne_one w) ψ hψ hψc
  have hU0' : U.map e.toMonoidHom ≠ ⊥ := fun h =>
    hU0 ((Subgroup.map_eq_bot_iff_of_injective U (f := e.toMonoidHom) e.injective).1 h)
  have hU2' : IsPGroup 2 ↥(U.map e.toMonoidHom) := hU2.map _
  have hEU : E ≤ Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup J) : Set J) :=
    hEN _ fun i => Subgroup.le_normalizer_map e.toMonoidHom
      (Subgroup.mem_map_of_mem _ (hN i (c5Mat w)))
  exact ⟨E, U.map e.toMonoidHom, hEel, hEcard, hU0', hU2', hEU⟩

theorem e6FourSylowFive_holds : E6FourSylowFive := by
  intro J _ _ hJ hZ P
  obtain ⟨E, U, -, hEcard, -, -, -⟩ := e6FourTwoLocalFive_holds J hJ hZ
  have hdvd : 5 ^ 4 ∣ Nat.card J := hEcard ▸ Subgroup.card_subgroup_dvd_card E
  have hnotdvd : ¬ 5 ^ 5 ∣ Nat.card J := by
    obtain ⟨K, iF, iFin, iC, hK, ⟨e⟩⟩ := e6FourMark_exists_adjointGroup hJ hZ
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.LocalAnalysis.GLTheoremA.not_pow_five_dvd_E6_four hK
  have hJ0 : Nat.card J ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card J).factorization 5 = 4 := by
    have hle : 4 ≤ (Nat.card J).factorization 5 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five hJ0).mp hdvd
    have hlt : ¬ 5 ≤ (Nat.card J).factorization 5 := fun h5 =>
      hnotdvd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five hJ0).mpr h5)
    omega
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Sylow.card_eq_multiplicity, hfac]

end Holds

end CFSG.Assembly

end
