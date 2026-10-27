module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.SylowCentral
public import CFSG.RankThree.PartOne.SEITZ11.G2SevenConsumer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.Quasithin.G2U CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.SEITZ3 CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.Classical

section Torus

variable {L : Type} [Field L]

abbrev tup (u w : Lˣ) : Fin Tag.G2.rank → Lˣ := ![u, w]

theorem rootChar_tuple (u w : Lˣ) (m n : ℤ) :
    rootChar (tup u w) (vec m n) = u ^ m * w ^ n := by
  rw [rootChar]
  refine (Fin.prod_univ_two _).trans ?_
  rfl

theorem rootTorusSL2_g2a_tuple (x : Lˣ) :
    rootTorusSL2 .G2 L g2a x =
      rootDiagUnit .G2 (tup (x ^ (2 : ℤ)) (x ^ (-1 : ℤ))) := by
  obtain ⟨t, ht, hA⟩ := rootTorusSL2_tuple (L := L) isRoot_g2a x
  rw [ht]
  congr 1
  have h0 : t ⟨0, by decide⟩ = x ^ (2 : ℤ) := by rw [hA]; congr 1
  have h1 : t ⟨1, by decide⟩ = x ^ (-1 : ℤ) := by rw [hA]; congr 1
  funext k
  fin_cases k
  · exact h0
  · exact h1

end Torus

section Model

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂] [Finite K₂]
  {σ : K₂ ≃+* K₂}

theorem QPlusModel.exists_beta_element_X (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) :
    ∃ x : adjointGroup .G2 K, ∃ h : twistEmb (K := K) M.g x ∈ monomialSubgroup .G2 K₂,
      weylQuotientHom .G2 K₂ ⟨_, h⟩ = rootReflection (vec 1 3) ∧
        twistEmb (K := K) M.g x ∈ M.X := by
  have h30 : IsRoot .G2 (vec 1 3) := isRoot_of_mem_rootList (by decide)
  obtain ⟨cβ, hcβΓ, hcβm, hcβw⟩ := M.exists_fixed_weyl hdeg hσ h30
  obtain ⟨x₀, hx₀⟩ := M.exists_twistEmb_eq hcβΓ
  have hmono : twistEmb (K := K) M.g x₀ ∈ monomialSubgroup .G2 K₂ := by
    rw [hx₀]; exact hcβm
  refine ⟨x₀, hmono, ?_, ?_⟩
  · have : (⟨twistEmb (K := K) M.g x₀, hmono⟩ : monomialSubgroup .G2 K₂) = ⟨_, hcβm⟩ :=
      Subtype.ext hx₀
    rw [this]
    exact hcβw
  · rw [hx₀]
    exact M.R_le_X h30 ⟨⟨nSL cβ, rfl⟩, hcβΓ⟩

theorem exists_unit_ne_one (h : 3 ≤ Nat.card K₂) : ∃ c : K₂ˣ, c ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsub : Subsingleton K₂ˣ := ⟨fun x y => by rw [hcon x, hcon y]⟩
  have : Nat.card K₂ˣ = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, inferInstance⟩
  rw [Nat.card_units] at this
  omega

theorem QPlusModel.X_eq_gamma_of_charTwo' [CharP K 2] (hmax : MaxSL2SL2G2) (M : QPlusModel K σ)
    (hdeg : Module.finrank K K₂ = 2) (hσ : ∀ c, σ c = c ^ Nat.card K)
    (hq4 : 4 ≤ Nat.card K) : M.X = M.gamma := by
  classical
  refine le_antisymm M.X_le_gamma fun y hy => ?_
  set φ' := M.phi.comp (adjointGroup .G2 K).subtype with hφ'
  set N : Subgroup (adjointGroup .G2 K) := M.X.comap φ' with hN
  have hstd : stdA1A1 K ≤ N := M.stdA1A1_le_comap
  rcases hmax K hq4 N hstd with hNeq | hNtop
  · exfalso
    have hq2 : Nat.card K₂ = Nat.card K ^ 2 := natCard_eq_sq_of_finrank_eq_two hdeg
    obtain ⟨c, hc⟩ := exists_unit_ne_one (K₂ := K₂) (by rw [hq2]; nlinarith)
    obtain ⟨n, hnm, hnw, hnX⟩ := M.exists_beta_element_X hdeg hσ
    have hnN : n ∈ N := hnX
    rw [hNeq] at hnN
    obtain ⟨⟨A, B⟩, rfl⟩ := hnN
    have hφn : twistEmb (K := K) M.g (a1a1Hom K (A, B)) =
        M.phi (rootSL2 .G2 K g2a A) * M.phi (rootSL2 .G2 K g2v B) := by
      show M.phi ((a1a1Hom K (A, B) : adjointGroup .G2 K) : ModGL .G2 K) = _
      rw [a1a1Hom_apply, map_mul]
    obtain ⟨Ca, hCa⟩ := M.phi_rootSL2_a A
    obtain ⟨Cv, hCv⟩ := M.phi_rootSL2_v B
    have hnm' := hnm
    set da := rootTorusSL2 .G2 K₂ g2a c with hda
    have hdaQ : da ∈ rootRankOneGroup .G2 K₂ g2a := ⟨HSL c, rfl⟩
    obtain ⟨Ea, hEa⟩ := hdaQ
    obtain ⟨a', ha', hchar⟩ := exists_conj_rootDiagUnit hnm
      (tup (c ^ (2 : ℤ)) (c ^ (-1 : ℤ)))
    rw [← rootTorusSL2_g2a_tuple] at ha'
    have hcomm : rootSL2 .G2 K₂ g2v Cv * da = da * rootSL2 .G2 K₂ g2v Cv := by
      rw [← hEa]; exact rootSL2_g2v_mul_rootSL2_g2a Cv Ea
    rw [hφn, ← hCa, ← hCv] at ha'
    have ht : rootDiagUnit .G2 (a' * (tup (c ^ (2 : ℤ)) (c ^ (-1 : ℤ)))⁻¹) =
        rootSL2 .G2 K₂ g2a (Ca * Ea * Ca⁻¹ * Ea⁻¹) := by
      have e1 : rootDiagUnit .G2 (a' * (tup (c ^ (2 : ℤ)) (c ^ (-1 : ℤ)))⁻¹) =
          rootDiagUnit .G2 a' * da⁻¹ := by
        rw [rootDiagUnit_mul, ← rootDiagUnit_inv, hda, rootTorusSL2_g2a_tuple]
      rw [e1, ← ha']
      have : rootSL2 .G2 K₂ g2a Ca * rootSL2 .G2 K₂ g2v Cv * da *
          (rootSL2 .G2 K₂ g2a Ca * rootSL2 .G2 K₂ g2v Cv)⁻¹ =
          rootSL2 .G2 K₂ g2a Ca * (rootSL2 .G2 K₂ g2v Cv * da * (rootSL2 .G2 K₂ g2v Cv)⁻¹) *
            (rootSL2 .G2 K₂ g2a Ca)⁻¹ := by
        simp only [mul_inv_rev, mul_assoc]
      rw [this, hcomm, mul_inv_cancel_right, ← hEa]
      simp only [map_mul, map_inv, mul_assoc]
    set t : Fin Tag.G2.rank → K₂ˣ := a' * (tup (c ^ (2 : ℤ)) (c ^ (-1 : ℤ)))⁻¹ with htdef
    have hv : IsRoot .G2 g2v := isRoot_g2v
    have hβ : IsRoot .G2 (vec 1 3) := isRoot_of_mem_rootList (by decide)
    have hr : IsRoot .G2 (vec 0 (-1)) := isRoot_of_mem_rootList (by decide)
    have hchar1 := hchar _ hr
    rw [hnw, QPlusModel.rootReflection_smul_eq_refl K₂ hβ] at hchar1
    have hrefl : refl (vec 1 3) (vec 0 (-1)) = g2v := by decide
    rw [hrefl, rootChar_tuple] at hchar1
    have hg2v : (g2v : Fin Tag.G2.rank → ℤ) = vec 1 2 := rfl
    have hcv : rootChar t g2v = c := by
      have h1 : rootChar t g2v = rootChar a' g2v *
          (rootChar (tup (c ^ (2 : ℤ)) (c ^ (-1 : ℤ))) g2v)⁻¹ := by
        have := map_mul (CFSG.RankThree.PartOne.SEITZ11.G2Seven.chiHom (L := K₂) g2v) a'
          (tup (c ^ (2 : ℤ)) (c ^ (-1 : ℤ)))⁻¹
        rw [map_inv] at this
        exact this
      have h2 : rootChar (tup (c ^ (2 : ℤ)) (c ^ (-1 : ℤ))) g2v = 1 := by
        rw [hg2v, rootChar_tuple, ← zpow_mul, ← zpow_mul, ← zpow_add]
        norm_num
      have h3 : rootChar a' g2v = c := by
        rw [hchar1]
        simp
      rw [h1, h2, h3, inv_one, mul_one]
    let U : SL2 K₂ := ⟨!![1, 1; 0, 1], by simp⟩
    have hcU : rootSL2 .G2 K₂ g2v U * rootDiagUnit .G2 t = rootDiagUnit .G2 t * rootSL2 .G2 K₂ g2v U := by
      rw [ht]; exact rootSL2_g2v_mul_rootSL2_g2a U _
    have hconj := rootDiagUnit_conj_rootSL2 t hv U
    rw [hcv] at hconj
    have hconj' : rootDiagUnit .G2 t * rootSL2 .G2 K₂ g2v U * (rootDiagUnit .G2 t)⁻¹ =
        rootSL2 .G2 K₂ g2v U := by
      rw [← hcU, mul_inv_cancel_right]
    rw [hconj'] at hconj
    have hU := rootSL2_injective_of_field g2v hconj.symm
    have hmat := congrArg (fun C : SL2 K₂ => (C : Matrix (Fin 2) (Fin 2) K₂) 0 1) hU
    have hmat' : ((diagUnitOne c : Matrix (Fin 2) (Fin 2) K₂) * (U : Matrix (Fin 2) (Fin 2) K₂) *
        (↑(diagUnitOne c)⁻¹ : Matrix (Fin 2) (Fin 2) K₂)) 0 1 = (U : Matrix (Fin 2) (Fin 2) K₂) 0 1 :=
      hmat
    simp only [CFSG.RankThree.Classical.coe_diagUnitOne,
      CFSG.RankThree.Classical.coe_diagUnitOne_inv, U, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hmat'
    apply hc
    apply Units.ext
    simpa using hmat'
  · obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    have hmem : (⟨y', hy'⟩ : adjointGroup .G2 K) ∈ N := by rw [hNtop]; trivial
    exact hmem

end Model

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
