module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3A
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CL4Tools

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4 InvClassL
open scoped commutatorElement

theorem commutatorElement_mul_center {Y : Type*} [Group Y] (a b : Y) {z₁ z₂ : Y}
    (hz₁ : z₁ ∈ center Y) (hz₂ : z₂ ∈ center Y) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  have c1 : z₁ * b = b * z₁ := (mem_center_iff.mp hz₁ b).symm
  have c2 : z₂ * a⁻¹ = a⁻¹ * z₂ := (mem_center_iff.mp hz₂ a⁻¹).symm
  have c12 : z₁ * z₂ = z₂ * z₁ := (mem_center_iff.mp hz₁ z₂).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z₁ * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹
      = a * (z₁ * b) * z₂ * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * (z₁ * z₂) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by rw [c1]; group
    _ = a * b * (z₂ * a⁻¹) * z₂⁻¹ * b⁻¹ := by rw [c12]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [c2]; group

theorem eq_of_perfect_of_center {H Y : Type*} [Group H] [Group Y] [hH : Group.IsPerfect H]
    {α β : H →* Y} (h : ∀ g, (α g)⁻¹ * β g ∈ center Y) : α = β := by
  have key : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ MonoidHom.eqLocus α β := by
    rw [commutator_le]
    intro a _ b _
    change α ⁅a, b⁆ = β ⁅a, b⁆
    have e1 : β a = α a * ((α a)⁻¹ * β a) := by group
    have e2 : β b = α b * ((α b)⁻¹ * β b) := by group
    rw [map_commutatorElement, map_commutatorElement, e1, e2,
      commutatorElement_mul_center _ _ (h a) (h b)]
  have htop : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = (⊤ : Subgroup H) := by
    rw [← _root_.commutator_def]
    exact hH.commutator_eq_top
  ext g
  exact key (by rw [htop]; exact mem_top g)

variable {G : Type} [Group G] {Q : Subgroup G} {K : Type} [Field K]
  (e : ↥Q ⧸ center ↥Q ≃* projectiveSL 4 K)

theorem exists_theta [Finite K] [Finite G] (hQ : IsQuasisimple ↥Q) (hK2 : ringChar K ≠ 2)
    (hZ : Nat.card (center ↥Q) = 1 ∨ (Nat.card (center ↥Q) = 2 ∧ 4 ∣ Nat.card K - 1)) :
    ∃ θ : SpecialLinearGroup (Fin 4) K →* ↥Q, Function.Surjective θ ∧
      (∀ s, piQ e (θ s) = proj 4 K s) ∧ θ.ker ≤ scalars 4 K ∧ θ negOne4 = 1 := by
  rcases hZ with hZ | ⟨hZ, h4⟩
  ·
    have hbot : center ↥Q = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
    have hinj : Function.Injective (piQ e) := by
      rw [← MonoidHom.ker_eq_bot_iff, ker_piQ, hbot]
    let eQ : ↥Q ≃* projectiveSL 4 K := MulEquiv.ofBijective (piQ e) ⟨hinj, piQ_surjective e⟩
    refine ⟨eQ.symm.toMonoidHom.comp (proj 4 K), eQ.symm.surjective.comp (proj_surjective 4 K),
      fun s => ?_, ?_, ?_⟩
    · change eQ (eQ.symm (proj 4 K s)) = proj 4 K s
      rw [MulEquiv.apply_symm_apply]
    · intro s hs
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff] at hs
      exact proj_eq_one_iff.mp hs
    · rw [MonoidHom.comp_apply, proj_negOne4, map_one]
  ·
    have : Group.IsPerfect ↥Q := hQ.1
    obtain ⟨σ, hσ, hσZ⟩ := GSThmB.Cent516.exists_cover_L4 hZ hK2 e
    have hσπ : ∀ s, piQ e (σ s) = proj 4 K s := fun s => by
      rw [piQ_apply]
      change e (GSThmB.Cent516.piZ (σ s)) = _
      rw [hσ, MulEquiv.apply_symm_apply]
    have hker : σ.ker ≤ scalars 4 K := by
      intro s hs
      rw [MonoidHom.mem_ker] at hs
      have h := hσπ s
      rw [hs, map_one] at h
      exact proj_eq_one_iff.mp h.symm
    refine ⟨σ, ?_, hσπ, hker, ?_⟩
    · intro y
      obtain ⟨s, hs⟩ := proj_surjective 4 K (piQ e y)
      have h1 : (σ s)⁻¹ * y ∈ center ↥Q := (piQ_eq_iff e _ _).mp (by rw [hσπ, hs])
      rw [← hσZ] at h1
      obtain ⟨c, -, hc⟩ := h1
      refine ⟨s * c, ?_⟩
      rw [map_mul, hc, mul_inv_cancel_left]
    ·
      have := Fintype.ofFinite K
      have hsq : IsSquare (-1 : K) := by
        rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
        have h1 : 1 ≤ Nat.card K := Nat.card_pos
        omega
      obtain ⟨i, hi⟩ := hsq
      have hi0 : i ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hi
        exact one_ne_zero (neg_eq_zero.mp hi)
      have hi4 : (Units.mk0 i hi0) ^ 4 = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
          show i ^ 4 = (i * i) * (i * i) by ring, ← hi]
        norm_num
      set c := scalarElement (Units.mk0 i hi0) hi4 with hc
      have hcZ : σ c ∈ center ↥Q := hσZ ▸ mem_map_of_mem σ (scalarElement_mem_scalars _ hi4)
      have hcc : c * c = negOne4 := by
        apply Subtype.ext
        change scalar (Fin 4) i * scalar (Fin 4) i = -1
        rw [← map_mul, ← hi, map_neg, map_one]
      rw [← hcc, map_mul]
      exact GSThmB.Cent516.sq_eq_one_of_mem_center hZ hcZ

theorem xAut_theta {x : G} (hx : x ∈ normalizer (Q : Set G))
    {θ : SpecialLinearGroup (Fin 4) K →* ↥Q} (hθ : ∀ s, piQ e (θ s) = proj 4 K s)
    {M : GL (Fin 4) K} (hM : phi hx e = conjAut 4 K M) (s : SpecialLinearGroup (Fin 4) K) :
    xAut hx (θ s) = θ (CatalogueBHigherLinearAction.slConjugation 4 K M s) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 4) K) :=
    LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  have h := eq_of_perfect_of_center (α := (xAut hx).toMonoidHom.comp θ)
    (β := θ.comp (CatalogueBHigherLinearAction.slConjugation 4 K M).toMonoidHom) fun g => by
      rw [← piQ_eq_iff e]
      change piQ e (xAut hx (θ g)) = piQ e (θ (CatalogueBHigherLinearAction.slConjugation 4 K M g))
      rw [← phi_piQ, hθ, hθ, hM, conjAut_proj]
  exact DFunLike.congr_fun h s

end CFSG.ComponentClassification.HarrisLit.C3
