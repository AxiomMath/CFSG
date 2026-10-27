module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3G
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3H
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3B
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3F

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.CatFactsL4U4.OutInv InvClassL

theorem transfer_conj {P : Type*} [Group P]
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P)) {J : Subgroup P} {κ : P}
    (hcenter : center ↥(J.map MulAut.conj ⊔ zpowers (MulAut.conj κ)) = ⊥)
    (hnot : MulAut.conj κ ∉ J.map MulAut.conj)
    (hE8 : ∃ A : Subgroup (MulAut P), A ≤ J.map MulAut.conj ⊔ zpowers (MulAut.conj κ) ∧
      GrSLit.IsElemTwo A ∧ Nat.card A = 8) :
    center ↥(J ⊔ zpowers κ) = ⊥ ∧ κ ∉ J ∧
      ∃ A : Subgroup P, A ≤ J ⊔ zpowers κ ∧ GrSLit.IsElemTwo A ∧ Nat.card A = 8 := by
  have hmap : (J ⊔ zpowers κ).map MulAut.conj = J.map MulAut.conj ⊔ zpowers (MulAut.conj κ) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  let eJ : ↥(J ⊔ zpowers κ) ≃* ↥(J.map MulAut.conj ⊔ zpowers (MulAut.conj κ)) :=
    ((J ⊔ zpowers κ).equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr hmap)
  refine ⟨Sporadic.HeldB.center_eq_bot_of_mulEquiv eJ hcenter,
    fun h => hnot (mem_map_of_mem _ h), ?_⟩
  obtain ⟨A, hA, hAe, hAc⟩ := hE8
  refine ⟨A.comap MulAut.conj, ?_, isElemTwo_comap_of_injective hinj hAe, ?_⟩
  · intro a ha
    have h1 : MulAut.conj a ∈ (J ⊔ zpowers κ).map MulAut.conj := hmap ▸ hA ha
    obtain ⟨b, hb, hba⟩ := h1
    rwa [← hinj hba]
  · have hAr : A ≤ (MulAut.conj : P →* MulAut P).range := by
      intro a ha
      obtain ⟨b, -, hb⟩ := (hmap ▸ hA ha : a ∈ (J ⊔ zpowers κ).map MulAut.conj)
      exact ⟨b, hb⟩
    rw [← hAc, ← Subgroup.card_map_of_injective hinj, map_comap_eq_self hAr]

variable {K : Type} [Field K]

theorem toGL_negOne4 : SpecialLinearGroup.toGL (negOne4 : SpecialLinearGroup (Fin 4) K) =
    GeneralLinearGroup.scalar (Fin 4) (-1) := by
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar]
  change (-1 : Matrix (Fin 4) (Fin 4) K) = scalar (Fin 4) ((-1 : Kˣ) : K)
  rw [Units.val_neg, Units.val_one, map_neg, map_one]

theorem conj_kappa {C U κ : GL (Fin 4) K}
    (hκU : κ * U = GeneralLinearGroup.scalar (Fin 4) (-1) * U * κ) (hκκ : κ * κ = 1) :
    C * U * C⁻¹ * (C * κ * C⁻¹) * (C * U * C⁻¹)⁻¹ =
      GeneralLinearGroup.scalar (Fin 4) (-1) * (C * κ * C⁻¹) := by
  set s := GeneralLinearGroup.scalar (Fin 4) (-1 : Kˣ) with hs
  have hsc : ∀ g : GL (Fin 4) K, s * g = g * s := fun g => GeneralLinearGroup.scalar_commute _ g
  have h1 : U * κ = s * κ * U := by
    calc U * κ = κ * (κ * U) * κ := by rw [← mul_assoc, hκκ, one_mul]
      _ = κ * (s * U * κ) * κ := by rw [hκU]
      _ = κ * s * U * (κ * κ) := by group
      _ = s * κ * U := by rw [hκκ, mul_one, ← hsc κ]
  calc C * U * C⁻¹ * (C * κ * C⁻¹) * (C * U * C⁻¹)⁻¹ = C * (U * κ) * U⁻¹ * C⁻¹ := by group
    _ = C * (s * κ * U) * U⁻¹ * C⁻¹ := by rw [h1]
    _ = C * s * κ * C⁻¹ := by group
    _ = s * (C * κ * C⁻¹) := by rw [← hsc C]; group

variable {G : Type} [Group G] [Finite G]

theorem l4_case (Q : Subgroup G) (x : G) (p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (hQ : IsQuasisimple ↥Q) (hL4 : Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSL 4 p k)
    (hZ : Nat.card ↥(center ↥Q) = 1 ∨ (Nat.card ↥(center ↥Q) = 2 ∧ 4 ∣ p ^ k - 1))
    (hxN : x ∈ normalizer (Q : Set G)) (hx2 : x * x = 1) (hxC : x ∉ centralizer (Q : Set G))
    (hLm : Blueprint.LieModel ↥(GSThmB.layerIn (Q ⊓ centralizer {x})) .PSL 2 p m) :
    m = 2 * k ∧
      ((∃ B : Subgroup G, B ≤ Q ⊓ centralizer {x} ∧ center ↥B = ⊥ ∧
          ∃ A : Subgroup G, A ≤ B ∧ GrSLit.IsElemTwo A ∧ Nat.card A = 8) ∨
        ∀ w ∈ GSThmB.layerIn (Q ⊓ centralizer {x}), orderOf w = 2 →
          ∃ X₁ X₂ : Subgroup G, X₁ ≠ X₂ ∧ X₁ ≤ Q ⊓ centralizer {w} ∧
            X₂ ≤ Q ⊓ centralizer {w} ∧ (X₁.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal ∧
            (X₂.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal ∧
            X₁ ≤ centralizer (X₂ : Set G) ∧ X₁ ⊓ X₂ = zpowers w ∧
            IsSLTwoOver (p ^ k) ↥X₁ ∧ IsSLTwoOver (p ^ k) ↥X₂) := by
  classical
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL4
  have hF2 : ringChar F ≠ 2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
  have hφ2 := phi_sq hxN e₀ hx2
  have hφ1 := phi_ne_one hxN e₀ hQ.1 hxC
  obtain ⟨hLs, hLna⟩ := GSThmB.Catalog7Std.Om8.simple_of_lieModel_psl_two hLm
  have hLZ : center ↥(Lay Q x) = ⊥ := FooteLit.center_eq_bot_of_isSimpleGroup hLna
  have hJφ := Jp_le_fixSub hxN e₀
  have hJ := isComponent_Jp hxN e₀ hLna
  have huniq : ∀ R : Subgroup (projectiveSL 4 F), R ≤ fixSub (phi hxN e₀) →
      IsComponent (R.subgroupOf (fixSub (phi hxN e₀))) → R ≤ Jp e₀ x :=
    fun R hR hRc => le_Jp_of_isComponent hxN e₀ hR hRc
  have hJm : Blueprint.LieModel ↥(Jp e₀ x) .PSL 2 p m :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (equivJp e₀ hLZ) hLm
  obtain ⟨hm, hrow⟩ := rowS_or_rowO hp hp2 hk hF hφ2 hφ1 hJφ hJ huniq hJm
  refine ⟨hm, ?_⟩
  have hZ' : Nat.card ↥(center ↥Q) = 1 ∨ (Nat.card ↥(center ↥Q) = 2 ∧ 4 ∣ Nat.card F - 1) := by
    rw [hF]
    exact hZ
  obtain ⟨θ, hθs, hθ, hθk, hθ1⟩ := exists_theta e₀ hQ hF2 hZ'
  rcases hrow with hS | hO
  ·
    left
    obtain ⟨C, ν, Ψ, hφM, hκU, hcen, hnot, hE8⟩ := rowS_aut hF2 hS
    set sκ := CatalogueBHigherLinearAction.slConjugation 4 F C (kappaSL ν Ψ) with hsκ
    have hκGL : SpecialLinearGroup.toGL sκ = C * rowSKappa ν Ψ * C⁻¹ := by
      rw [hsκ, CatalogueBHigherLinearAction.toGL_slConjugation, toGL_kappaSL]
    have hconjκ : MulAut.conj (proj 4 F sκ) = conjAut 4 F (C * rowSKappa ν Ψ * C⁻¹) := by
      rw [← conjAut_toGL, hκGL]
    rw [← hconjκ] at hcen hnot hE8
    obtain ⟨hcenP, hnotP, hE8P⟩ := transfer_conj CSL.conj_injective hcen hnot hE8
    have hxκ : xAut hxN (θ sκ) = θ sκ := by
      rw [xAut_theta e₀ hxN hθ hφM sκ]
      have h1 : CatalogueBHigherLinearAction.slConjugation 4 F (C * rowSU ν Ψ * C⁻¹) sκ =
          negOne4 * sκ := by
        apply SpecialLinearGroup.toGL_injective
        rw [CatalogueBHigherLinearAction.toGL_slConjugation, hκGL, map_mul, toGL_negOne4, hκGL]
        exact conj_kappa hκU (rowSKappa_mul_self ν Ψ)
      rw [h1, map_mul, hθ1, one_mul]
    have hκ2 : θ sκ * θ sκ = 1 := by
      rw [← map_mul]
      have h1 : sκ * sκ = 1 := by
        apply SpecialLinearGroup.toGL_injective
        rw [map_mul, hκGL, map_one,
          show C * rowSKappa ν Ψ * C⁻¹ * (C * rowSKappa ν Ψ * C⁻¹) =
            C * (rowSKappa ν Ψ * rowSKappa ν Ψ) * C⁻¹ by group, rowSKappa_mul_self, mul_one,
          mul_inv_cancel]
      rw [h1, map_one]
    rw [← hθ sκ] at hcenP hnotP hE8P
    exact b_alternative e₀ hLZ ((xAut_eq_iff hxN _).mp hxκ) hκ2 hnotP hcenP hE8P
  ·
    right
    intro w hw hw2
    have h := rowO_x_alternative hF2 hxN e₀ hθs hθ hθk hθ1 hLZ hO w hw hw2
    rw [hF] at h
    exact h

end CFSG.ComponentClassification.HarrisLit.C3
