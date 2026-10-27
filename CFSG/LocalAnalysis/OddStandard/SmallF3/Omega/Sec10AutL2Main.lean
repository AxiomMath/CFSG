module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10AutL2Core

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.AutL2Facts CFSG.GorensteinWalter Subgroup

theorem aut_psl281_abelian_two_le_16 {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Blueprint.LieModel Y .PSL 2 3 4) (X : Subgroup (MulAut Y))
    (hp : IsPGroup 2 X) (hc : IsMulCommutative X) : Nat.card X ≤ 16 := by
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hH : HarrisHyp F :=
    harrisHyp_of Nat.prime_three (by norm_num) hF (by decide) (by norm_num)
  let Φ : MulAut Y ≃* PGammaL2 F := autEquiv e
  have hcomm : ∀ x ∈ X.map Φ.toMonoidHom, ∀ y ∈ X.map Φ.toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (isMulCommutative_iff.mp hc ⟨x, hx⟩ ⟨y, hy⟩))
  have h := AutL2.card_le_sixteen_of_isPGroup hH hF (hp.map Φ.toMonoidHom) hcomm
  rwa [Subgroup.card_map_of_injective Φ.injective] at h

end CFSG.OddStandard.SmallF3.Omega
