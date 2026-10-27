module

public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenCyclotomicTori

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieG2E

open CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley


theorem g2e_inner_not73 (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 8)
    (g : adjointGroup .G2 K) (hg : orderOf g = 3) :
    ¬ 73 ∣ Nat.card ↥(Subgroup.centralizer ({g} : Set (adjointGroup .G2 K))) := by
  intro h73
  haveI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' 73 h73
  set x : adjointGroup .G2 K := (x' : adjointGroup .G2 K) with hx
  have hx73 : orderOf x = 73 := by rw [hx, Subgroup.orderOf_coe]; exact hx'
  have hxg : g ∈ Subgroup.centralizer ({x} : Set (adjointGroup .G2 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := x'.2
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this.symm
  obtain ⟨T, -, -, -, -, hT⟩ := even_G2_cyclotomic_three_six_tori_and_prime_centralizers K 1
    (Or.inr rfl) 73 (by rw [hK]; norm_num) (by norm_num) (by norm_num) (dvd_refl 73)
  obtain ⟨-, -, -, hc, -⟩ := hT x hx73
  have h3 : orderOf g ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) := by
    have := orderOf_dvd_natCard
      (⟨g, hxg⟩ : ↥(Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))))
    rwa [Subgroup.orderOf_mk] at this
  rw [hc, hg] at h3
  omega

end CFSG.LocalAnalysis.GLTheoremA.LevelLieG2E
