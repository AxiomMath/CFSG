module

public import CFSG.GH74.GLS.IVK.Lifted.Lem52
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Prop61

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.ABGDGroups CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

section SqInn

variable {F : Type} [Field F] [Finite F]

theorem sq_mem_inn_of_field (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F))
    (h : (gammaOf hodd h3 (α * α)).right = 1) :
    α * α ∈
      (MulAut.conj : SpecialLinearGroup (Fin 2) F →* MulAut (SpecialLinearGroup (Fin 2) F)).range := by
  have hK := isOddPrimePower_card_of_odd hodd
  rw [mem_inn_iff hodd h3]
  refine ⟨h, ?_⟩
  rw [left_mem_range_toPGL_iff hK, map_mul, map_mul, ← pow_two]
  exact squareClass_sq _

end SqInn

section SqR

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem sqR_aux
    (h44 : II4_44) (h2A7 : II4_2A7) (hII : II4_4_4_center) (hC : Cfg5 G z S K₁ K₂)
    {A B : Subgroup G} (hAB : A = K₁ ∧ B = K₂ ∨ A = K₂ ∧ B = K₁) {b : G} (hbS : b ∈ S)
    (hbN : b ∈ normalizer (B : Set G)) (hbsq : b * b ∈ cSec B) : b * b ∈ Pof S A := by
  classical
  have hM := m4_of_std hII hC.std
  have hAc : A = K₁ ∨ A = K₂ := by
    rcases hAB with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hAmem : A ∈ ({K₁, K₂} : Set (Subgroup G)) := by simpa using hAc
  have hOK := std4_hatOK h44 hC.std hAmem
  have hbQ : b * b ∈ Qof S B := ⟨S.mul_mem hbS hbS, hbsq⟩
  by_cases hne : Qof S B = Pof S A
  · rw [← hne]
    exact hbQ
  · rcases sl_or_a7 hOK.sl2 with ⟨F, hFf, hFin, hodd, h3, ⟨e⟩⟩ | h7
    · have hbNA : b ∈ normalizer (A : Set G) :=
        (normalizer_AB hC.std hAB (hM.S_syl.1 hbS)).2 hbN
      have hbbN : b * b ∈ normalizer (A : Set G) := mul_mem hbNA hbNA
      have hσ := field_trivial52 hII hC hAB hne hodd h3 e (b * b) hbbN hbQ
      have hphi : phi A (b * b) hbbN = phi A b hbNA * phi A b hbNA := phi_mul A hbNA hbNA
      have hinn : MulAut.congr e (phi A b hbNA) * MulAut.congr e (phi A b hbNA) ∈
          (MulAut.conj : SpecialLinearGroup (Fin 2) F →*
            MulAut (SpecialLinearGroup (Fin 2) F)).range := by
        apply sq_mem_inn_of_field hodd h3
        rw [← map_mul, ← hphi]
        exact hσ
      have hinn' : phi A (b * b) hbbN ∈ innOf (Hat A) := by
        obtain ⟨s, hs⟩ := hinn
        refine ⟨e.symm s, ?_⟩
        apply (MulAut.congr e).injective
        rw [congr_conj, MulEquiv.apply_symm_apply, hs, hphi, map_mul]
      have hin : InducesInner (b * b) A := (phi_mem_inn_iff A hbbN).1 hinn'
      obtain ⟨k₀, hk₀, hk₀c⟩ := lift_inner_gen (hC.std.sylow.isPGroup)
        (std4_exists_sylow_P hC.std hAc) (sq_eq_one_of_card_center hOK.sl2.2) (S.mul_mem hbS hbS)
        hbbN hin
      have hzP : z ∈ Pof S A := ⟨hM.z_mem_S, hM.z_mem_comp hAc⟩
      have hPQ : Pof S A ≤ Qof S B := Pof_le_Qof hM hAB
      have hy : b * b * k₀⁻¹ ∈ Qof S B ⊓ Qof S A :=
        ⟨(Qof S B).mul_mem hbQ ((Qof S B).inv_mem (hPQ hk₀)), hk₀c⟩
      rw [Q_inf_Q5' hII hC hAB] at hy
      have h5 : b * b = (b * b * k₀⁻¹) * k₀ := by group
      rw [h5]
      exact (Pof S A).mul_mem (zpowers_le.2 hzP hy) hk₀
    · exact (a7_excluded52 h2A7 hII hC hAB hne h7).elim

theorem ivk_f_sq_R_of_II4
    (h44 : II4_44) (h2A7 : II4_2A7) (hII : II4_4_4_center)
    (h41 : Prop4_1) : CFSG.GH74.GLS.Stage1.Thm3.Sec6.IVK_f_sq_R := by
  intro G _ _ z S h hQ1 K hK b hbS hbF hbsq
  classical
  obtain ⟨hbN, -⟩ := hbF
  rcases h.cases with ⟨K₀, h1⟩ | ⟨K₁, K₂, h2⟩
  · have hKK : K = K₀ := by
      have hm : K ∈ {K' | IsRigidRankOneComp z K'} := hK
      rw [h1.comps] at hm
      exact hm
    subst hKK
    have hQ : Qz S z = S ⊓ cSec K := std6r1_Qz_eq h1
    have hbb : b * b ∈ Qz S z := by
      rw [hQ]
      exact ⟨S.mul_mem hbS hbS, hbsq⟩
    exact Subgroup.mem_sup_right hbb
  · have hC : Cfg5 G z S K₁ K₂ :=
      ⟨h2, (h41 G z S K₁ K₂ h2).1, hQ1 K₁ (h2.comp_rigid (Or.inl rfl)),
        hQ1 K₂ (h2.comp_rigid (Or.inr rfl))⟩
    have hKmem : K = K₁ ∨ K = K₂ := by
      have hm : K ∈ {K' | IsRigidRankOneComp z K'} := hK
      rw [h2.comps] at hm
      simpa using hm
    have hP : b * b ∈ Pz S z := by
      rcases hKmem with hKe | hKe
      · have := sqR_aux h44 h2A7 hII hC (A := K₂) (B := K) (Or.inr ⟨rfl, hKe⟩) hbS hbN hbsq
        refine ⟨this.1, ?_⟩
        rw [h2.rigidProduct_eq]
        exact (le_sup_right : K₂ ≤ K₁ ⊔ K₂) this.2
      · have := sqR_aux h44 h2A7 hII hC (A := K₁) (B := K) (Or.inl ⟨rfl, hKe⟩) hbS hbN hbsq
        refine ⟨this.1, ?_⟩
        rw [h2.rigidProduct_eq]
        exact (le_sup_left : K₁ ≤ K₁ ⊔ K₂) this.2
    exact Subgroup.mem_sup_left hP

end SqR

end CFSG.GH74.GLS.IVK.Lifted
