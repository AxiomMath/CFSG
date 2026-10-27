module

public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Levi

public noncomputable section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.LieType.Universal CFSG.LieType.CurtisTits MinData.Valid
open CFSG.ClassicalInvolution.Models.TwistedPairs
open scoped MatrixGroups

section Hom

variable {K : Type} [Field K] {H : Type*} [Group H]

theorem hom_ext_blockSL2 {n : ℕ} {f g : SL(n + 1, K) →* H}
    (h : ∀ i : Fin n, f.comp (blockSL2 K n i) = g.comp (blockSL2 K n i)) : f = g := by
  have hle : ⨆ i, (blockSL2 K n i).range ≤ MonoidHom.eqLocus f g := by
    refine iSup_le fun i => ?_
    rintro _ ⟨A, rfl⟩
    exact DFunLike.congr_fun (h i) A
  refine MonoidHom.ext fun x => hle ?_
  rw [iSup_range_blockSL2 n]
  exact Subgroup.mem_top x

end Hom

section Phi

variable {k : Type} [Field k]

theorem exists_phi4 [Finite k] :
    ∃ Φ : SL(4, k) →* e6Data_valid.minGroup k,
      Φ.comp (blockSL2 k 3 0) = e6Rank1 k (nd 2) ∧ Φ.comp (blockSL2 k 3 1) = e6Rank1 k (nd 3) ∧
        Φ.comp (blockSL2 k 3 2) = e6Rank1 k (nd 4) := by
  obtain ⟨Ψ₀, -, h00, h01⟩ := exists_e6Sl3 (k := k) (a := nd 2) (b := nd 3) (by decide)
    (by decide) (by decide)
  obtain ⟨Ψ₁, -, h10, h11⟩ := exists_e6Sl3 (k := k) (a := nd 3) (b := nd 4) (by decide)
    (by decide) (by decide)
  let F : CTFamily k (e6Data_valid.minGroup k) 3 :=
    { ι := fun i => e6Rank1 k (![nd 2, nd 3, nd 4] i)
      θ := ![Ψ₀, Ψ₁, 1]
      left := fun i hi => by
        fin_cases i
        · exact h00
        · exact h10
        · exact absurd hi (by decide)
      right := fun i hi => by
        fin_cases i
        · exact h01
        · exact h11
        · exact absurd hi (by decide)
      comm := fun i j hij a b => by
        fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | skip
        exact (commute_e6Rank1 (a := nd 2) (b := nd 4) (by decide) (by decide) a b).eq }
  obtain ⟨Φ, hΦ, -⟩ := exists_hom_of_ctFamily F
  exact ⟨Φ, hΦ 0, hΦ 1, hΦ 2⟩

end Phi

section Levi12

variable {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

theorem sigma_comp_phi4 {Φ : SL(4, k) →* e6Data_valid.minGroup k}
    (h0 : Φ.comp (blockSL2 k 3 0) = e6Rank1 k (nd 2))
    (h1 : Φ.comp (blockSL2 k 3 1) = e6Rank1 k (nd 3))
    (h2 : Φ.comp (blockSL2 k 3 2) = e6Rank1 k (nd 4)) :
    (sigma k θ).comp Φ = Φ.comp (sigmaA (involEquiv θ hθ)).toMonoidHom := by
  refine hom_ext_blockSL2 fun i => ?_
  fin_cases i
  · refine MonoidHom.ext fun A => ?_
    show sigma k θ (Φ (blockSL2 k 3 0 A)) = Φ (sigmaA (involEquiv θ hθ) (blockSL2 k 3 0 A))
    rw [sigmaA_blockSL2_zero,
      show Φ (blockSL2 k 3 0 A) = e6Rank1 k (nd 2) A from DFunLike.congr_fun h0 A,
      show Φ (blockSL2 k 3 2 (fieldAutSL (involEquiv θ hθ) 2 A)) =
        e6Rank1 k (nd 4) (fieldAutSL (involEquiv θ hθ) 2 A) from DFunLike.congr_fun h2 _,
      sigma_e6Rank1]
    rfl
  · refine MonoidHom.ext fun A => ?_
    show sigma k θ (Φ (blockSL2 k 3 1 A)) = Φ (sigmaA (involEquiv θ hθ) (blockSL2 k 3 1 A))
    rw [sigmaA_blockSL2_one,
      show Φ (blockSL2 k 3 1 A) = e6Rank1 k (nd 3) A from DFunLike.congr_fun h1 A,
      show Φ (blockSL2 k 3 1 (fieldAutSL (involEquiv θ hθ) 2 A)) =
        e6Rank1 k (nd 3) (fieldAutSL (involEquiv θ hθ) 2 A) from DFunLike.congr_fun h1 _,
      sigma_e6Rank1]
    rfl
  · refine MonoidHom.ext fun A => ?_
    show sigma k θ (Φ (blockSL2 k 3 2 A)) = Φ (sigmaA (involEquiv θ hθ) (blockSL2 k 3 2 A))
    rw [sigmaA_blockSL2_two,
      show Φ (blockSL2 k 3 2 A) = e6Rank1 k (nd 4) A from DFunLike.congr_fun h2 A,
      show Φ (blockSL2 k 3 0 (fieldAutSL (involEquiv θ hθ) 2 A)) =
        e6Rank1 k (nd 2) (fieldAutSL (involEquiv θ hθ) 2 A) from DFunLike.congr_fun h0 _,
      sigma_e6Rank1]
    rfl

theorem eq_blockSL2_torus_of_scalar4 (ω η₂ η₃ : kˣ) (h2 : (η₂ : k) = (ω : k) ^ 2)
    (h3 : (η₃ : k) = (ω : k) ^ 3) (h4 : (ω : k) ^ 4 = 1) (g : SL(4, k))
    (hg : Matrix.scalar (Fin 4) (ω : k) = (g : Matrix (Fin 4) (Fin 4) k)) :
    g = blockSL2 k 3 0 (torusHom k ω) * blockSL2 k 3 1 (torusHom k η₂) *
      blockSL2 k 3 2 (torusHom k η₃) := by
  have hω : (ω : k) ≠ 0 := ω.ne_zero
  refine Subtype.ext ?_
  rw [← hg, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change _ = ((blockSL k 4 2 0 (by omega) (torusHom k ω) : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) *
    ((blockSL k 4 2 1 (by omega) (torusHom k η₂) : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) *
    ((blockSL k 4 2 2 (by omega) (torusHom k η₃) : SL(4, k)) : Matrix (Fin 4) (Fin 4) k)
  rw [coe_blockSL_four_zero, coe_blockSL_four_one, coe_blockSL_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, coe_torusHom, Matrix.scalar_apply,
      Units.val_inv_eq_inv_val, h2, h3]
  all_goals field_simp
  all_goals first | ring1 | linear_combination h4

theorem phi4_injective [Finite k] {Φ : SL(4, k) →* e6Data_valid.minGroup k}
    (h0 : Φ.comp (blockSL2 k 3 0) = e6Rank1 k (nd 2))
    (h1 : Φ.comp (blockSL2 k 3 1) = e6Rank1 k (nd 3))
    (h2 : Φ.comp (blockSL2 k 3 2) = e6Rank1 k (nd 4)) : Function.Injective Φ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hne : Φ (blockSL2 k 3 0 (tv 0 1 1)) ≠ 1 := by
    rw [show Φ (blockSL2 k 3 0 (tv 0 1 1)) = e6Rank1 k (nd 2) (tv 0 1 1) from
      DFunLike.congr_fun h0 _]
    intro h
    exact tv_zero_one_one_ne_one (e6Rank1_injective (nd 2) (h.trans (map_one _).symm))
  have hker : g ∈ Subgroup.center SL(4, k) :=
    ker_le_center_of_isQuasisimple (SpecialLinear.isQuasisimple 3 k (by norm_num))
      ⟨_, hne⟩ hg
  obtain ⟨ω, hω4, hωg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hker
  rw [Fintype.card_fin] at hω4
  have hω0 : ω ≠ 0 := fun h => by simp [h] at hω4
  let ωu : kˣ := Units.mk0 ω hω0
  have hg' : g = blockSL2 k 3 0 (torusHom k ωu) * blockSL2 k 3 1 (torusHom k (ωu ^ 2)) *
      blockSL2 k 3 2 (torusHom k (ωu ^ 3)) :=
    eq_blockSL2_torus_of_scalar4 ωu (ωu ^ 2) (ωu ^ 3) (by simp [ωu]) (by simp [ωu]) hω4 g hωg
  have hΦg : Φ g = e6Data_valid.hm k (nd 2) ωu * e6Data_valid.hm k (nd 3) (ωu ^ 2) *
      e6Data_valid.hm k (nd 4) (ωu ^ 3) := by
    rw [hg', map_mul, map_mul,
      show Φ (blockSL2 k 3 0 (torusHom k ωu)) = e6Rank1 k (nd 2) (torusHom k ωu) from
        DFunLike.congr_fun h0 _,
      show Φ (blockSL2 k 3 1 (torusHom k (ωu ^ 2))) = e6Rank1 k (nd 3) (torusHom k (ωu ^ 2)) from
        DFunLike.congr_fun h1 _,
      show Φ (blockSL2 k 3 2 (torusHom k (ωu ^ 3))) = e6Rank1 k (nd 4) (torusHom k (ωu ^ 3)) from
        DFunLike.congr_fun h2 _, e6Rank1_hm, e6Rank1_hm, e6Rank1_hm]
  have hu : TwistedE6.torusHom k
      ((Pi.mulSingle (nd 2) ωu * Pi.mulSingle (nd 3) (ωu ^ 2) * Pi.mulSingle (nd 4) (ωu ^ 3) :
        Fin (Tag.rank .E6) → kˣ)) = 1 := by
    rw [map_mul, map_mul, torusHom_mulSingle, torusHom_mulSingle, torusHom_mulSingle, ← hΦg]
    exact hg
  have h2' := eq_one_of_torusHom_eq_one hu (nd 2)
  have e1 : (nd 2 : Fin (Tag.rank .E6)) ≠ nd 3 := by decide
  have e2 : (nd 2 : Fin (Tag.rank .E6)) ≠ nd 4 := by decide
  simp [Pi.mul_apply, e1, e2] at h2'
  have hω1 : ω = 1 := by
    have := congrArg Units.val h2'
    simpa [ωu] using this
  refine Subtype.ext ?_
  rw [← hωg, hω1]
  simp

variable [Finite k]

theorem exists_levi12 : ∃ emb : unitaryGroup θ hθ →* fixedGroup k θ, Function.Injective emb ∧
    emb.comp (ulb θ hθ) = nodeHom1 θ ∧ emb.comp (usb θ hθ) = nodeHom2 θ hθ := by
  obtain ⟨Φ, h0, h1, h2⟩ := exists_phi4 (k := k)
  have hσ := sigma_comp_phi4 θ hθ h0 h1 h2
  have hfix : ∀ g : unitaryGroup θ hθ, Φ (g : SL(4, k)) ∈ fixedGroup k θ := fun g => by
    rw [mem_fixedGroup]
    have := DFunLike.congr_fun hσ (g : SL(4, k))
    simp only [MonoidHom.comp_apply] at this
    rw [this]
    exact congrArg Φ g.2
  refine ⟨(Φ.comp (unitaryGroup θ hθ).subtype).codRestrict (fixedGroup k θ) hfix, ?_, ?_, ?_⟩
  · intro g g' h
    have h' : Φ (g : SL(4, k)) = Φ (g' : SL(4, k)) := congrArg Subtype.val h
    exact Subtype.ext (phi4_injective h0 h1 h2 h')
  · refine MonoidHom.ext fun A => Subtype.ext ?_
    change Φ (blockSL2 k 3 1 (liftSL θ 2 A)) = e6Rank1 k (nd 3) (liftSL θ 2 A)
    exact DFunLike.congr_fun h1 _
  · refine MonoidHom.ext fun B => Subtype.ext ?_
    change Φ (blockSL2 k 3 0 B * blockSL2 k 3 2 (fieldAutSL (involEquiv θ hθ) 2 B)) = _
    rw [map_mul, show Φ (blockSL2 k 3 0 B) = e6Rank1 k (nd 2) B from DFunLike.congr_fun h0 B,
      show Φ (blockSL2 k 3 2 (fieldAutSL (involEquiv θ hθ) 2 B)) =
        e6Rank1 k (nd 4) (fieldAutSL (involEquiv θ hθ) 2 B) from DFunLike.congr_fun h2 _,
      slOrbitHom_apply]
    rfl

end Levi12

end CFSG.ClassicalInvolution.WeakCT
