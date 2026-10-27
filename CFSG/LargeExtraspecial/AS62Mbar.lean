module

public import CFSG.LargeExtraspecial.AS62HSet
public import CFSG.LargeExtraspecial.AS62Fam2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions

namespace AS62

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem commSpace_rhoL_conj {m t : G} (hm : m ∈ S.M) (ht : t ∈ S.M)
    (hmt : m * t * m⁻¹ ∈ S.M) :
    commSpace (S.rhoL hmt) = (commSpace (S.rhoL ht)).map (S.rhoL hm : S.Qt →ₗ[ZMod 2] S.Qt) := by
  have h : S.rhoL hmt = S.rhoL hm * S.rhoL ht * (S.rhoL hm)⁻¹ := by
    unfold Setting.rhoL
    rw [show (⟨m * t * m⁻¹, hmt⟩ : S.M) = ⟨m, hm⟩ * ⟨t, ht⟩ * ⟨m, hm⟩⁻¹ from rfl, map_mul,
      map_mul, map_inv]
    rfl
  rw [h, CFSG.RankThree.OrthogonalInvolutions.commSpace_conj]

theorem mbar_ne_top (h22 : S14.AschbacherTwoTwoStmt) (h : W2Hyp S) : S.Mbar ≠ ⊤ := by
  intro htop
  obtain ⟨t₁, ht₁, h₁M⟩ := exists_mem_DSet h22 h
  obtain ⟨hA, -, -⟩ := S.fiveOne_two (sixFourConcl h22 h.hW) h.hW ht₁ h₁M
  have hℓ : commSpace (S.rhoL h₁M) ≠ ⊥ := by
    intro hb
    have h2 := hA.2.2.2.1
    rw [hb, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hℓ
  obtain ⟨σ, -, hσ⟩ := S.exists_mem_O_finrank_inf_map_eq_one hv0 hA.2.2.2.1 hA.2.2.2.2 hv
  have hσM : σ ∈ S.Mbar := by
    rw [htop]
    exact mem_top σ
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hσM
  have h₂M : (m : G) * t₁ * (m : G)⁻¹ ∈ S.M := mul_mem (mul_mem m.2 h₁M) (inv_mem m.2)
  have hline : commSpace (S.rhoL h₂M) =
      (commSpace (S.rhoL h₁M)).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
    rw [commSpace_rhoL_conj m.2 h₁M h₂M, ← hm]
    rfl
  exact false_of_two_lines h22 h ht₁ (S.conj_mem_DSet m.2 ht₁) h₁M h₂M (by rw [hline]; exact hσ)

end AS62

end CFSG.LargeExtraspecial
