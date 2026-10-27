module

public import CFSG.LargeExtraspecial.S8KQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

namespace Bad4

variable {D : Std H C ht ht1 hVQ} {τ : S.O} (B : Bad4 D τ)
include B

theorem E_le_Mbar : closure (insert τ (N1bar S g t τ : Set S.O)) ≤ S.Mbar := by
  rw [closure_le]
  intro x hx
  rcases hx with rfl | hx
  · exact B.mem.1
  · exact Rbar_le_Mbar (Nbar_le_Rbar ((B.red.N1bar_spec B.mem B.not_mem).1 hx))

theorem E_comm : ∀ a ∈ closure (insert τ (N1bar S g t τ : Set S.O)),
    ∀ b ∈ closure (insert τ (N1bar S g t τ : Set S.O)), a * b = b * a ∧ a * a = 1 := by
  have hs := (B.red.N1bar_spec B.mem B.not_mem)
  refine closure_comm_and_sq (fun a ha b hb => ?_) (fun a ha => ?_)
  · rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact (hs.2.2 b hb).symm
    · exact hs.2.2 a ha
    · exact (hs.2.1 a ha b hb).1
  · rcases ha with rfl | ha
    · exact mul_self_of_mem_conjCentM H ht B.mem
    · exact (hs.2.1 a ha a ha).2

theorem E_eq_closure : closure (insert τ (N1bar S g t τ : Set S.O)) =
    closure {d | d ∈ conjD S t ∧ commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)} := by
  have hττ : τ * τ = 1 := mul_self_of_mem_conjCentM H ht B.mem
  apply le_antisymm
  · rw [closure_le]
    rintro x (rfl | hx)
    · obtain ⟨-, -, y, hyM, hyτ⟩ := B.mem
      exact Subgroup.subset_closure ⟨⟨y, hyM, hyτ⟩, le_sup_right⟩
    · have hle : S9.Fbar S g t ⊔ (S9.Fbar S g t).map (MulAut.conj (S.ρ D.h)).toMonoidHom ≤
          Subgroup.closure {d | d ∈ conjD S t ∧ commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
            Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)} := by
        refine sup_le ?_ ?_
        · rw [S9.Fbar, closure_le]
          intro σ hσ
          obtain ⟨-, y, hyM, hyσ⟩ := id hσ
          exact Subgroup.subset_closure ⟨⟨y, hyM, hyσ⟩,
            B.commSpace_le_of_mem_N1bar (B.Fbar_le (Subgroup.subset_closure hσ))⟩
        · rw [S9.Fbar, MonoidHom.map_closure, closure_le]
          rintro _ ⟨σ, hσ, rfl⟩
          obtain ⟨-, y, hyM, hyσ⟩ := id hσ
          refine Subgroup.subset_closure ⟨⟨S.ρ D.h * y, mul_mem (Rbar_le_Mbar D.hh) hyM, ?_⟩,
            B.commSpace_le_of_mem_N1bar
              (B.conj_mem D.hh (B.Fbar_le (Subgroup.subset_closure hσ)))⟩
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [hyσ]
          group
      exact hle (B.N1bar_le_Fbar_sup hx)
  · rw [closure_le]
    rintro d ⟨⟨y, hyM, rfl⟩, hdY⟩
    have hVY : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
        Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [(commSpace_t_eq H C ht ht1 hVQ).1]
      exact le_sup_left
    have hdC := conj_mem_conjCentM ht hyM (commute_of_commSpace_le B.le_perp hdY hVY)
    by_cases hN : y * t * y⁻¹ ∈ Nbar S g t
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (B.mem_N1bar_of_mem_Nbar hdC hN))
    · have h1 := B.mul_mem_N1bar hdC hN
      have e : y * t * y⁻¹ = (y * t * y⁻¹ * τ) * τ := by rw [mul_assoc _ τ τ, hττ, mul_one]
      rw [e]
      exact mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ h1))
        (Subgroup.subset_closure (Set.mem_insert τ _))

omit B in
theorem map_inv_eq {gg : S.O}
    (hY : (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
      ((gg : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
        Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
      (((gg⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
        Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  conv_lhs => rw [← hY]
  rw [← Submodule.map_comp]
  convert Submodule.map_id _
  ext v
  exact inv_apply_apply_O gg v

theorem map_conj_E_of_map_eq {gg : S.O} (hgM : gg ∈ S.Mbar)
    (hY : (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
      ((gg : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
        Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (Subgroup.closure (insert τ (N1bar S g t τ : Set S.O))).map (MulAut.conj gg).toMonoidHom =
      Subgroup.closure (insert τ (N1bar S g t τ : Set S.O)) := by
  rw [B.E_eq_closure, MonoidHom.map_closure]
  refine congrArg Subgroup.closure (Set.ext fun d => ⟨?_, fun hd => ?_⟩)
  · rintro ⟨e, ⟨⟨y, hyM, rfl⟩, heY⟩, rfl⟩
    refine ⟨⟨gg * y, mul_mem hgM hyM, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [S7.commSpace_conj, ← hY]
    exact Submodule.map_mono heY
  · obtain ⟨⟨y, hyM, rfl⟩, hdY⟩ := hd
    refine ⟨gg⁻¹ * (y * t * y⁻¹) * gg⁻¹⁻¹, ⟨⟨gg⁻¹ * y, mul_mem (inv_mem hgM) hyM, by group⟩, ?_⟩,
      by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rw [S7.commSpace_conj, ← map_inv_eq hY]
    exact Submodule.map_mono hdY

end Bad4

end CFSG.LargeExtraspecial.S8
