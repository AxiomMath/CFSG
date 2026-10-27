module

public import CFSG.LieType.SeitzGeneration.ExcTorusAmbient
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicThreeTorus
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicFourTorus
public import CFSG.RankThree.Chevalley.SteinbergCFF4CyclotomicSix

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley


theorem sylowTorus_F4_three (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1) : SylowTorus (adjointGroup .F4 K) p 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨F, hF⟩ := exists_ringHom_pow_card K (AlgebraicClosure K)
  obtain ⟨⟨g, hg, hgn⟩, hmain⟩ := F4_cyclotomic_three_torus_and_regular_prime_centralizers K
    (AlgebraicClosure K) F hF _ rfl
  obtain ⟨-, ⟨eT⟩, hTr, -, hp', -⟩ := hmain g hg hgn _ _ _ rfl rfl rfl
  obtain ⟨-, hconj, ⟨V, hV, hVc, -⟩, -⟩ := hp' p hp hp3 hpd
  exact sylowTorus_of_torus_data K (AlgebraicClosure K) rfl
    (isMulCommutative_of_mulEquiv_prod eT) hTr hconj hV hVc

theorem sylowTorus_F4_four (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 2 + 1) : SylowTorus (adjointGroup .F4 K) p 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨F, hF⟩ := exists_ringHom_pow_card K (AlgebraicClosure K)
  obtain ⟨⟨g, hg, hgn⟩, hmain⟩ := F4_cyclotomic_four_torus_and_regular_prime_centralizers K
    (AlgebraicClosure K) F hF _ rfl
  obtain ⟨-, ⟨eT⟩, hTr, hp', -⟩ := hmain g hg hgn _ _ _ rfl rfl rfl
  obtain ⟨-, hconj, ⟨V, hV, hVc, -⟩, -⟩ := hp' p hp hp3 hpd
  exact sylowTorus_of_torus_data K (AlgebraicClosure K) rfl
    (isMulCommutative_of_mulEquiv_prod eT) hTr hconj hV hVc

theorem sylowTorus_F4_six (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K ^ 2 - Nat.card K + 1) : SylowTorus (adjointGroup .F4 K) p 2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨F, hF⟩ := exists_ringHom_pow_card K (AlgebraicClosure K)
  obtain ⟨-, -, -, ⟨g, hg, hgn⟩, hmain⟩ := F4_cyclotomic_six_torus_and_surviving_A2_kernels K
    (AlgebraicClosure K) F hF _ rfl
  obtain ⟨-, ⟨eT⟩, hTr, -, hp', -⟩ := hmain g hg hgn _ _ _ rfl rfl rfl
  obtain ⟨-, hconj, ⟨V, hV, hVc, -⟩, -⟩ := hp' p hp hp3 hpd
  exact sylowTorus_of_torus_data K (AlgebraicClosure K) rfl
    (isMulCommutative_of_mulEquiv_prod eT) hTr hconj hV hVc

end CFSG.LieType.SeitzGeneration
