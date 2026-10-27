module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueCover
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520L4
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSL
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3CPSix67
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalar

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520L

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.ModelFacts.TG3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

theorem model1520_psl_aux {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (ψ : SL(4, 𝔽₃) →* ↥X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center SL(4, 𝔽₃)) {R : Subgroup SL(4, 𝔽₃)}
    (e : R ≃* SL(2, 𝔽₃)) (hLR : IsLongRootSL2 (show 2 ≤ 4 by norm_num) R (sl2Inv e)) :
    Model1520 X ((ψ (sl2Inv e) : ↥X) : G) := by
  have hodd := odd_natCard_galoisField_three
  obtain ⟨g, -, hig⟩ := hLR
  have hperf : Group.IsPerfect SL(4, 𝔽₃) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  have hπker : (proj 4 𝔽₃).ker = Subgroup.center SL(4, 𝔽₃) := by
    rw [ker_proj]
    exact scalars_eq_center 4 𝔽₃
  obtain ⟨e₀, he₀⟩ := exists_equiv_of_covers hperf ψ hψ hker (proj 4 𝔽₃) (proj_surjective 4 𝔽₃)
    hπker
  let e₁ : ↥X ⧸ Subgroup.center ↥X ≃* projectiveSL 4 𝔽₃ :=
    e₀.trans (MulAut.conj (proj 4 𝔽₃ g)⁻¹)
  have hsq : ((ψ (sl2Inv e) : ↥X) : G) * ((ψ (sl2Inv e) : ↥X) : G) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, sl2Inv_mul_self hodd e, map_one, Subgroup.coe_one]
  refine model1520_of_PSL (ψ (sl2Inv e)).2 hsq natCard_galoisField_three e₁ ?_
  show (MulAut.conj (proj 4 𝔽₃ g)⁻¹) (e₀ (QuotientGroup.mk (ψ (sl2Inv e)))) = _
  rw [he₀, hig, MulAut.conj_apply]
  simp only [map_mul, map_inv, inv_inv]
  group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520L
