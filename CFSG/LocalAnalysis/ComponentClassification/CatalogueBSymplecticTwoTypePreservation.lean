module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoRadical

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticTwo

open Module Submodule Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher

variable {K : Type} [Field K]

theorem map_planeStabilizer_notMem_pointParabolics [Finite K] (hodd : ringChar K ≠ 2) (ℓ : ℕ)
    [Fact ℓ.Prime] [CharP K ℓ] (α : MulAut (StatedProj (StatedSp 2 K))) :
    (projStabilizer 2 K (flag 2 K 2)).map α.toMonoidHom ∉ pointParabolics K := by
  rintro ⟨L, hL, hαL⟩
  obtain ⟨g, hg⟩ := exists_statedSp_map_eq (isCompleteIsotropicFlag_flag.2.2 1 (by norm_num))
    (isTotallyIsotropic_of_finrank_eq_one hL) (by rw [finrank_flag (by norm_num), hL])
  set β := (MulAut.conj (proj 2 K g))⁻¹ * α with hβdef
  have hβ : (projStabilizer 2 K (flag 2 K 2)).map β.toMonoidHom =
      projStabilizer 2 K (flag 2 K 1) := by
    rw [hβdef, map_toMonoidHom_mul, hαL, ← hg, projStabilizer_map_spAct, ← map_toMonoidHom_mul,
      inv_mul_cancel, map_toMonoidHom_one]
  obtain ⟨A, -, hAnorm, hAp, hAcomm, hAcard⟩ :=
    exists_abelian_normal_le_planeStabilizer (K := K) ℓ
  refine not_abelian_normal_le_pointStabilizer hodd ℓ (A.map β.toMonoidHom) ?_ (hAp.map _) ?_ ?_
  · rw [← hβ, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hAnorm
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAcomm a ha b hb]
  · rw [Subgroup.card_map_of_injective β.injective]
    exact hAcard

theorem odd_symplectic_two_type_preservation [Finite K] (hodd : ringChar K ≠ 2) :
    (∀ α : MulAut (StatedProj (StatedSp 2 K)),
      (fun M => M.map α.toMonoidHom) '' pointParabolics K = pointParabolics K) ∧
    typeKernel K = ⊤ ∧
    ∀ α : MulAut (StatedProj (StatedSp 2 K)),
      (fun M => M.map α.toMonoidHom) '' pointParabolics K ≠ planeParabolics K := by
  classical
  obtain ⟨ℓ, hchar⟩ := CharP.exists K
  have hℓ : Fact ℓ.Prime := ⟨CharP.char_is_prime K ℓ⟩
  obtain ⟨hparts, -, -, -⟩ := type_kernel (K := K) ℓ
  obtain ⟨-, -, hdisj, hXne, -, -, -, -⟩ := extremal_parabolics (K := K) ℓ rfl
  have hX : ∀ α : MulAut (StatedProj (StatedSp 2 K)),
      (fun M => M.map α.toMonoidHom) '' pointParabolics K = pointParabolics K := by
    intro α
    obtain ⟨-, -, h⟩ := hparts α
    rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exfalso
      refine map_planeStabilizer_notMem_pointParabolics hodd ℓ α ?_
      rw [← h2]
      exact ⟨_, ⟨flag 2 K 2, isCompleteIsotropicFlag_flag.2.2 2 le_rfl,
        finrank_flag (by norm_num), rfl⟩, rfl⟩
  refine ⟨hX, eq_top_iff.mpr fun α _ => hX α, fun α h => ?_⟩
  obtain ⟨M, hM⟩ := hXne
  have hMY : M ∈ planeParabolics K := by
    rw [← h, hX α]
    exact hM
  exact Set.disjoint_left.mp hdisj hM hMY

end CFSG.ComponentClassification.CatalogueBSymplecticTwo
