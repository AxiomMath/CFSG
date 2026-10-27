module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpBase

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped MatrixGroups

theorem PerfectBig3.of_injective {G G' : Type} [Group G] [Group G'] (ψ : G →* G')
    (hψ : Function.Injective ψ) (h : PerfectBig3 G) : PerfectBig3 G' := by
  obtain ⟨Q, _, _, ι, hι, hQ, h27⟩ := h
  exact ⟨Q, inferInstance, inferInstance, ψ.comp ι, hψ.comp hι, hQ, h27⟩

theorem Perfect360.of_injective {G G' : Type} [Group G] [Group G'] (ψ : G →* G')
    (hψ : Function.Injective ψ) (h : Perfect360 G) : Perfect360 G' := by
  obtain ⟨Q, _, _, ι, hι, hQ, h360⟩ := h
  exact ⟨Q, inferInstance, inferInstance, ψ.comp ι, hψ.comp hι, hQ, h360⟩

theorem commutator_prod_eq_top {G₁ G₂ : Type} [Group G₁] [Group G₂] (h₁ : commutator G₁ = ⊤)
    (h₂ : commutator G₂ = ⊤) : commutator (G₁ × G₂) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨g₁, g₂⟩ -
  have h1 : (MonoidHom.inl G₁ G₂).range ≤ commutator (G₁ × G₂) :=
    a6sq_range_le_derived _ h₁
  have h2 : (MonoidHom.inr G₁ G₂).range ≤ commutator (G₁ × G₂) :=
    a6sq_range_le_derived _ h₂
  have e : ((g₁, g₂) : G₁ × G₂) = (g₁, 1) * (1, g₂) := by simp
  rw [e]
  exact Subgroup.mul_mem _ (h1 ⟨g₁, rfl⟩) (h2 ⟨g₂, rfl⟩)

theorem PerfectBig3.prod_left {G₁ G₂ : Type} [Group G₁] [Group G₂] (h : PerfectBig3 G₁) :
    PerfectBig3 (G₁ × G₂) :=
  h.of_injective (MonoidHom.inl G₁ G₂) (fun _ _ h => (Prod.mk.inj h).1)

theorem PerfectBig3.prod_right {G₁ G₂ : Type} [Group G₁] [Group G₂] (h : PerfectBig3 G₂) :
    PerfectBig3 (G₁ × G₂) :=
  h.of_injective (MonoidHom.inr G₁ G₂) (fun _ _ h => (Prod.mk.inj h).2)

theorem three_dvd_card_of_lieModel (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {τ : StatedLieTag} {n j : ℕ} (hadm : StatedLieAdmissible τ n 3 j)
    (hm : LieModel X τ n 3 j) (h3 : 3 ≤ lieSylowExponent τ n * j) : 27 ∣ Nat.card X := by
  obtain ⟨-, -, hfac⟩ := hO X τ n 3 j hadm hm
  have h1 : 3 ^ (Nat.card X).factorization 3 ∣ Nat.card X := Nat.ordProj_dvd _ 3
  rw [hfac] at h1
  exact (pow_dvd_pow 3 h3).trans h1

section Sp

variable {k : Type} [Field k] [Finite k]

theorem commutator_statedSp_eq_top {m : ℕ} (hm : 1 ≤ m)
    (h : 4 ≤ Nat.card k ∨ (Nat.card k = 3 ∧ 2 ≤ m)) : commutator (StatedSp m k) = ⊤ := by
  have hq := LieType.Universal.Symplectic.isQuasisimple m k hm (by
    rcases h with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h))
  exact Group.isPerfect_def.mp hq.1

theorem three_pow_dvd_card_statedSp {m j : ℕ} (hk : Nat.card k = 3 ^ j) :
    3 ^ (j * m ^ 2) ∣ Nat.card (StatedSp m k) := by
  rw [card_statedSp m, hk, ← pow_mul]
  exact Dvd.intro _ rfl

theorem perfectBig3_statedSp {m j : ℕ} (hm : 1 ≤ m) (hk : Nat.card k = 3 ^ j)
    (hq : 4 ≤ 3 ^ j ∨ 2 ≤ m) (h3 : 3 ≤ j * m ^ 2) : PerfectBig3 (StatedSp m k) := by
  refine ⟨StatedSp m k, inferInstance, inferInstance, MonoidHom.id _, Function.injective_id,
    commutator_statedSp_eq_top hm ?_, ?_⟩
  · rcases hq with hq | hq
    · exact Or.inl (hk ▸ hq)
    · by_cases h4 : 4 ≤ Nat.card k
      · exact Or.inl h4
      · refine Or.inr ⟨?_, hq⟩
        have hk3 : 3 ≤ Nat.card k := by
          rw [hk]
          rcases Nat.eq_zero_or_pos j with hj | hj
          · subst hj
            simp at h3
          · exact (Nat.le_self_pow (by omega) 3).trans' (by norm_num)
        omega
  · exact (pow_dvd_pow 3 h3).trans (three_pow_dvd_card_statedSp hk)

theorem perfect360_statedSp_one (hk : Nat.card k = 9) : Perfect360 (StatedSp 1 k) := by
  refine ⟨StatedSp 1 k, inferInstance, inferInstance, MonoidHom.id _, Function.injective_id,
    commutator_statedSp_eq_top le_rfl (Or.inl (by omega)), ?_⟩
  have h1 : Nat.card (StatedSp 1 k) = 720 := by
    rw [card_statedSp 1, hk]
    simp
  have h2 : Nat.card (spScalars 1 k) = 2 := by
    rw [card_spScalars_eq_gcd k le_rfl, hk]
    norm_num
  have h3 : Nat.card (StatedSp 1 k) =
      Nat.card (StatedSp 1 k ⧸ spScalars 1 k) * Nat.card (spScalars 1 k) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h4 : Nat.card (StatedSp 1 k ⧸ center (StatedSp 1 k)) =
      Nat.card (StatedSp 1 k ⧸ spScalars 1 k) :=
    Nat.card_congr (LieType.Universal.Symplectic.centerQuotientEquiv 1 k).toEquiv
  rw [h4]
  rw [h1, h2] at h3
  omega

end Sp

section Lin

variable {k : Type} [Field k] [Finite k]

theorem three_le_tri {m : ℕ} (hm : 2 ≤ m) : 3 ≤ (m + 1) * (m + 1 - 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num), Nat.add_sub_cancel]
  nlinarith

theorem perfectBig3_GL (hO : LieOrderFormulasInput) {r j : ℕ} (hr : 3 ≤ r) (hj : 1 ≤ j)
    (hk : Nat.card k = 3 ^ j) : PerfectBig3 (GL (Fin r) k) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hadm : StatedLieAdmissible .PSL (m + 1) 3 j :=
    ⟨Nat.prime_three, hj, by omega, fun h => by have := (Prod.mk.inj h).1; omega,
      fun h => by have := (Prod.mk.inj h).1; omega⟩
  refine ⟨SL(m + 1, k), inferInstance, inferInstance, Matrix.SpecialLinearGroup.toGL,
    Matrix.SpecialLinearGroup.toGL_injective, ?_, ?_⟩
  · exact Group.isPerfect_def.mp (CatalogueBGeneralLinear.specialLinear_quasisimple (m + 1) k
      (by omega) (Or.inl (by omega)) (Or.inl (by omega))).1
  · have hm : LieModel (SL(m + 1, k) ⧸ center SL(m + 1, k)) .PSL (m + 1) 3 j :=
      Or.inl ⟨by decide,
        LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient m k hadm hk⟩
    have h3 : 3 ≤ lieSylowExponent .PSL (m + 1) * j :=
      (three_le_tri (by omega)).trans (Nat.le_mul_of_pos_right _ hj)
    exact (three_dvd_card_of_lieModel hO hadm hm h3).trans (Subgroup.card_quotient_dvd_card _)

end Lin

end CFSG.ComponentClassification.CatFC
