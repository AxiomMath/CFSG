module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoLang
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.QuadExt
public import CFSG.LieType.SeitzGeneration.Defs

public section

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

theorem three_dvd_sq_sub_one {q : ℕ} (h3 : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  refine Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq ?_)
  have h : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rw [Nat.pow_mod]
  rcases h with h | h <;> rw [h]


theorem card_le_nine_of_isElemAbelian_three (K : Type) [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K) (F : Subgroup ↥(adjointGroup .G2 K)) (hF : IsElemAbelian 3 F) :
    Nat.card F ≤ 3 ^ 2 := by
  obtain ⟨K₂, _, _, hdeg, -⟩ := UnitaryEmbedding.exists_quadratic_frobenius_all K
  have : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  have : Finite K₂ := Module.finite_of_finite K
  have h3₂ : 3 ∣ Nat.card K₂ - 1 := by
    rw [natCard_eq_sq_of_finrank_eq_two hdeg]
    exact three_dvd_sq_sub_one h3
  have hΓY : conjEntrywiseImage K (1 : ModGL .G2 K₂) ≤ adjointGroup .G2 K₂ := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using baseChangeGL_mem_adjointGroup (algebraMap K K₂) hx
  have : CFSG.IsElementaryAbelian 3 F :=
    { toIsMulCommutative := hF.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hF.2 g g.2) }
  obtain ⟨y, hy⟩ := exists_planeImage_conj_le hΓY h3₂ F
  let f : F → torusTorsion K₂ 3 := fun e =>
    ⟨(y : ModGL .G2 K₂) * twistEmb 1 (e : ↥(adjointGroup .G2 K)) * (y : ModGL .G2 K₂)⁻¹,
      hy e e.2⟩
  have hf : Function.Injective f := fun e₁ e₂ h => by
    have h' : twistEmb (K := K) (1 : ModGL .G2 K₂) (e₁ : ↥(adjointGroup .G2 K)) =
        twistEmb (K := K) (1 : ModGL .G2 K₂) (e₂ : ↥(adjointGroup .G2 K)) := by
      simpa [f] using congrArg Subtype.val h
    exact Subtype.ext (twistEmb_injective 1 h')
  calc Nat.card F ≤ Nat.card (torusTorsion K₂ 3) := Nat.card_le_card_of_injective f hf
    _ = Nat.card (rootsOfUnity 3 K₂ × rootsOfUnity 3 K₂) :=
        (Nat.card_congr (torusTorsionEquiv K₂ 3).toEquiv).symm
    _ = Nat.card (rootsOfUnity 3 K₂) * Nat.card (rootsOfUnity 3 K₂) := Nat.card_prod _ _
    _ ≤ 3 * 3 := Nat.mul_le_mul (card_rootsOfUnity K₂ 3) (card_rootsOfUnity K₂ 3)
    _ = 3 ^ 2 := by norm_num

theorem rankLE2_three_adjointGroup_G2 (K : Type) [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K) : CFSG.LieType.SeitzGeneration.RankLE2 3 ↥(adjointGroup .G2 K) :=
  fun F hF => card_le_nine_of_isElemAbelian_three K h3 F hF

end CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
