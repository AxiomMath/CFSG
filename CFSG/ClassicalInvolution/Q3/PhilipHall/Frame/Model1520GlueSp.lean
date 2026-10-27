module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueCover
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Sp4
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSp
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpStd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3CPSix67
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalar

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Sp

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.ModelFacts.TG3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

theorem isPerfect_sp4_three : Group.IsPerfect (StatedSp 2 𝔽₃) := by
  have : Group.IsPerfect (TauCeti.GLSymplecticFin 2 𝔽₃) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin 𝔽₃ 2
      (Or.inr (Or.inl ⟨natCard_galoisField_three, le_refl 2⟩))
  let e : TauCeti.GLSymplecticFin 2 𝔽₃ ≃* StatedSp 2 𝔽₃ :=
    (TauCeti.GLSymplecticFin.mulEquivGLSymplectic 2 𝔽₃).trans
      (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
        (n := 2) (K := 𝔽₃)).symm)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem model1520_psp_aux {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (ψ : StatedSp 2 𝔽₃ →* ↥X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 𝔽₃)) {R : Subgroup (StatedSp 2 𝔽₃)}
    (e : R ≃* SL(2, 𝔽₃)) (hLR : IsLongRootSp2 R (sl2Inv e)) :
    Model1520 X ((ψ (sl2Inv e) : ↥X) : G) := by
  have hodd := odd_natCard_galoisField_three
  obtain ⟨k, g, -, hig⟩ := hLR
  have hπker : (proj 2 𝔽₃).ker = Subgroup.center (StatedSp 2 𝔽₃) := by
    rw [ker_proj]
    exact (CFSG.LieType.Universal.Symplectic.center_eq 2 𝔽₃).symm
  obtain ⟨e₀, he₀⟩ := exists_equiv_of_covers isPerfect_sp4_three ψ hψ hker (proj 2 𝔽₃)
    (QuotientGroup.mk'_surjective _) hπker
  let e₁ : ↥X ⧸ Subgroup.center ↥X ≃* StatedProj (StatedSp 2 𝔽₃) :=
    e₀.trans (MulAut.conj (proj 2 𝔽₃ g)⁻¹)
  have hsq : ((ψ (sl2Inv e) : ↥X) : G) * ((ψ (sl2Inv e) : ↥X) : G) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, sl2Inv_mul_self hodd e, map_one, Subgroup.coe_one]
  refine model1520_of_PSp (ψ (sl2Inv e)).2 hsq natCard_galoisField_three e₁ ?_
  show (MulAut.conj (proj 2 𝔽₃ g)⁻¹) (e₀ (QuotientGroup.mk (ψ (sl2Inv e)))) = _
  rw [he₀, hig]
  have hk : proj 2 𝔽₃ (longInv 𝔽₃ 2 k) = proj 2 𝔽₃ (longInv 𝔽₃ 2 0) := by
    fin_cases k
    · rfl
    · have h1 : longInv 𝔽₃ 2 ⟨1, by norm_num⟩ = longInv 𝔽₃ 2 1 := rfl
      have hz : proj 2 𝔽₃ (CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp.zneg 𝔽₃) = 1 := by
        rw [← MonoidHom.mem_ker, hπker]
        exact CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp.zneg_mem_center
      show proj 2 𝔽₃ (longInv 𝔽₃ 2 1) = _
      rw [← CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp.zneg_mul_x0_eq_longInv, map_mul, hz,
        one_mul]
      rfl
  rw [MulAut.conj_apply]
  simp only [map_mul, map_inv, inv_inv]
  rw [← hk]
  group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Sp
