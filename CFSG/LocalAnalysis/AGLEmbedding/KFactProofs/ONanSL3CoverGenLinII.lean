module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenLinI
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen

open Matrix CFSG CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField

variable {k : Type} [Field k] [Finite k]

theorem closure_fixSet_eq_top_of_field (h3 : 3 ∣ Nat.card k - 1) (T : FrobData k)
    (hτ : orderOf T.τ = 3) (E : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) k)))
    (hEab : Open.IsElemAbelian 3 E) (hEcard : Nat.card E = 9) (hFix : FixCube E)
    (hτE : slFieldAut (Fin 3) k T.τ ∈ E) : Subgroup.closure (fixSet E) = ⊤ := by
  classical
  have hτ1 : T.τ ≠ 1 := by
    rintro h1
    rw [h1, orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  have hf₂1 : slFieldAut (Fin 3) k T.τ ≠ 1 := slFieldAut_ne_one hτ1
  obtain ⟨a, haE, ha⟩ := exists_mem_not_mem_zpowers hEab hEcard hτE
  have hβ3 : a ^ 3 = 1 := hEab.2 a haE
  obtain ⟨m, g, hg⟩ := exists_isConjBy_mul_pow hτ a hβ3
  set e₁ : MulAut (Matrix.SpecialLinearGroup (Fin 3) k) := a * slFieldAut (Fin 3) k T.τ ^ m
    with he₁
  have he₁E : e₁ ∈ E := E.mul_mem haE (E.pow_mem hτE m)
  have he₁3 : e₁ ^ 3 = 1 := hEab.2 e₁ he₁E
  have he₁not : e₁ ∉ Subgroup.zpowers (slFieldAut (Fin 3) k T.τ) := by
    intro hmem
    apply ha
    have h1 : a = e₁ * (slFieldAut (Fin 3) k T.τ ^ m)⁻¹ := by rw [he₁]; group
    rw [h1]
    exact mul_mem hmem (inv_mem (pow_mem (Subgroup.mem_zpowers _) m))
  have he₁1 : e₁ ≠ 1 := fun h => he₁not (h ▸ one_mem _)
  have hcomm : e₁ * slFieldAut (Fin 3) k T.τ = slFieldAut (Fin 3) k T.τ * e₁ :=
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨e₁, he₁E⟩ ⟨_, hτE⟩)
  obtain ⟨y, hy, hyfix⟩ := exists_fixed_conj T hg hcomm
  obtain ⟨c, s, hcdet, hs, hsact⟩ := exists_det_one_conj T h3 hy hyfix
  obtain ⟨c', hc'⟩ := exists_pow_three_scalar hy he₁3
  have hs' : e₁ = MulAut.conj s := MulEquiv.ext fun t => by
    rw [MulAut.conj_apply]
    exact hsact t
  have hlift : (y : Matrix (Fin 3) (Fin 3) k) ^ 3 = (c : k) ^ 3 • (1 : Matrix (Fin 3) (Fin 3) k) →
      T.τ (c : k) = c := by
    intro hy3
    have hs3 : s ^ 3 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, hs, smul_pow, hy3, smul_smul, ← mul_pow,
        inv_mul_cancel₀ c.ne_zero, one_pow, one_smul]
      rfl
    have hfix := hFix _ hτE s hs3 (hs' ▸ he₁E)
    obtain ⟨i, j, hij⟩ : ∃ i j, (y : Matrix (Fin 3) (Fin 3) k) i j ≠ 0 := by
      by_contra hcon
      exact GL_ne_zero y (by ext i j; by_contra hij; exact hcon ⟨i, j, hij⟩)
    have h1 : T.τ ((s : Matrix (Fin 3) (Fin 3) k) i j) = (s : Matrix (Fin 3) (Fin 3) k) i j :=
      congrFun (congrFun (congrArg Subtype.val hfix) i) j
    rw [hs] at h1
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hyfix i j] at h1
    have h2 : T.τ ((c : k)⁻¹) = (c : k)⁻¹ := mul_right_cancel₀ hij h1
    rw [map_inv₀] at h2
    exact inv_injective h2
  obtain ⟨P, u, hP, hPu⟩ := T.exists_fixed_frame h3 y hyfix hcdet hc' hlift
  have hPGL : Matrix.GeneralLinearGroup.map (T.τ : k →+* k) P = P :=
    Units.ext (by ext i j; exact hP i j)
  have hgen := closure_fixed_eq_top_semi T hy hPGL hPu
  rw [eq_top_iff, ← hgen]
  refine Subgroup.closure_mono ?_
  rintro x (hx | hx)
  · exact ⟨_, hτE, hf₂1, hx⟩
  · exact ⟨e₁, he₁E, he₁1, hx⟩

theorem congr_eq_mul_mul_inv {S : Type*} [Group S] (α f : MulAut S) :
    MulAut.congr α f = α * f * α⁻¹ := by
  ext x
  rfl

theorem closure_fixSet_eq_top_linear (h3 : 3 ∣ Nat.card k - 1)
    (E : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) k))) (hEab : Open.IsElemAbelian 3 E)
    (hEcard : Nat.card E = 9) (hFix : FixCube E) : Subgroup.closure (fixSet E) = ⊤ := by
  classical
  by_cases hall : ∀ e ∈ E, ∃ g : GL (Fin 3) k, IsConjBy e g
  · exact closure_fixSet_eq_top_of_conj h3 E hEab hEcard hFix hall
  · push Not at hall
    obtain ⟨e₀, he₀E, he₀⟩ := hall
    have he₀3 : e₀ ^ 3 = 1 := hEab.2 e₀ he₀E
    rcases exists_isConjBy_or_conj_fieldAut e₀ he₀3 with ⟨g, hg⟩ | ⟨σ, H, hσ, hβ⟩
    · exact absurd hg (he₀ g)
    · obtain ⟨T, i, hi, hTσ⟩ := FrobData.exists_of_orderOf_eq_three hσ
      have hτ : orderOf T.τ = 3 := by
        rcases hi with rfl | rfl
        · rw [hTσ, pow_one]
          exact hσ
        · rw [hTσ, orderOf_pow' σ (by norm_num), hσ]
          norm_num
      set α : MulAut (Matrix.SpecialLinearGroup (Fin 3) k) := slConjugation 3 k H with hα
      have hmem : slFieldAut (Fin 3) k T.τ ∈ mapAut α.symm E := by
        rw [mem_mapAut, MulEquiv.symm_symm, congr_eq_mul_mul_inv]
        have : α * slFieldAut (Fin 3) k T.τ * α⁻¹ = e₀ ^ i := by
          rw [hβ, conj_pow, ← map_pow, ← hTσ]
        rw [this]
        exact E.pow_mem he₀E i
      have hFix' : FixCube (mapAut α.symm E) := hFix.mapAut α.symm
      have := closure_fixSet_eq_top_of_field h3 T hτ (mapAut α.symm E)
        (isElemAbelian_mapAut hEab α.symm) (by rw [card_mapAut]; exact hEcard) hFix' hmem
      exact (closure_fixSet_mapAut_eq_top_iff α.symm E).1 this

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
