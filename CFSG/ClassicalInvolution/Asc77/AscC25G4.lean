module

public import CFSG.ClassicalInvolution.Asc77.AscC25G3
import CFSG.ClassicalInvolution.ModelFacts.L6CMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25G

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]


variable (p f) in
@[expose] def TwinCent6 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (D : LieSystemData p f Y Φ)
    (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    D.card = 1 → (∃ i : Fin D.card, IsOrthTag 6 (!piSign p f) (D.tag i) (D.rank i)) →
    TwinSect0 Φ A A' z' a₀ b₀ →
    ∃ τ y : Y, τ ≠ z' ∧ τ * z' = z' * τ ∧ τ * τ = 1 ∧ y * z' * y⁻¹ = τ ∧
      conjSub τ A = A ∧ conjSub τ A' = A'

theorem twinCent6_of_hom (hp2 : p ≠ 2) {Y : Type} [Group Y] (t : StatedLieTag) (k e : ℕ)
    (hadm : StatedLieAdmissible t k p e) (ψ : (Generic.modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t k p e Fact.out).K)
    (hcase : (t = .PSL ∧ k = 4 ∧ ¬ p ^ e % 4 = 1) ∨ (t = .PSU ∧ k = 4 ∧ p ^ e % 4 = 1))
    {R R' : Subgroup (Generic.modelUniv t k p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k p e Fact.out).D)
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') :
    ∃ τ y : Y, τ ≠ z' ∧ τ * z' = z' * τ ∧ τ * τ = 1 ∧ y * z' * y⁻¹ = τ ∧
      conjSub τ (R.map ψ) = R.map ψ ∧ conjSub τ (R'.map ψ) = R'.map ψ := by
  have he : 1 ≤ e := hadm.2.1
  rcases hcase with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
  · have h2 : (2 : GaloisField p e) ≠ 0 := C25W.two_ne_zero_gf (p := p) e hp2
    exact L4.twinCent6_psl4 h2 ψ hker
      (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR)
      (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num)
        hR') hne hz hz'
  · have : NeZero (2 * e) := ⟨by omega⟩
    have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
      CFSG.LieType.Universal.card_galoisField_two_mul p e he
    obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
    obtain ⟨θ, hθ⟩ : ∃ θ : Phan.Su (GaloisField p (2 * e)) p e 4 →* Y,
        θ = ψ.comp φ.symm.toMonoidHom := ⟨_, rfl⟩
    have hθφ : ∀ r, θ (φ r) = ψ r := fun r => by
      rw [hθ]
      show ψ (φ.symm (φ r)) = ψ r
      rw [MulEquiv.symm_apply_apply]
    have hθker : θ.ker ≤ Subgroup.center (Phan.Su (GaloisField p (2 * e)) p e 4) := by
      intro y hy
      have h1 : φ.symm y ∈ Subgroup.center (Generic.modelUniv .PSU 4 p e Fact.out).K := by
        apply hker
        rw [MonoidHom.mem_ker, ← hθφ, MulEquiv.apply_symm_apply]
        exact MonoidHom.mem_ker.mp hy
      rw [Subgroup.mem_center_iff] at h1 ⊢
      intro w
      apply φ.symm.injective
      rw [map_mul, map_mul]
      exact h1 (φ.symm w)
    have hmap : ∀ S : Subgroup (Generic.modelUniv .PSU 4 p e Fact.out).K,
        S.map ψ = (S.map φ.toMonoidHom).map θ := fun S => by
      rw [Subgroup.map_map]
      congr 1
      ext r
      exact (hθφ r).symm
    rw [hmap R] at hz
    rw [hmap R'] at hz'
    rw [hmap R, hmap R'] at hne ⊢
    exact U4.twinCent6_psu4 hK hp2 θ hθker ((hφ R).mp hR) ((hφ R').mp hR') hne hz hz'

theorem twinCent6_proved : TwinCent6 p f := by
  intro Y _ _ Φ D A A' z' a₀ b₀ hD1 hi htw
  obtain ⟨i, hi⟩ := hi
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hcase : ∀ j : Fin D.card, (D.tag j = .PSL ∧ D.rank j = 4 ∧ ¬ p ^ f % 4 = 1) ∨
      (D.tag j = .PSU ∧ D.rank j = 4 ∧ p ^ f % 4 = 1) := by
    intro j
    rw [Subsingleton.elim j i]
    simp only [IsOrthTag] at hi
    rcases hi with ⟨h5, -⟩ | ⟨-, hε, ht, hn⟩ | ⟨-, hε, ht, hn⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · omega
    · left
      refine ⟨ht, hn, ?_⟩
      simp only [piSign, Bool.not_eq_true', decide_eq_false_iff_not] at hε
      exact hε
    · right
      refine ⟨ht, hn, ?_⟩
      simp only [piSign, Bool.not_eq_false', decide_eq_true_eq] at hε
      exact hε
    · omega
    · omega
    · omega
  have hexp : ∀ j : Fin D.card, D.exp j = f := by
    intro j
    rcases D.exp_eq j with h | ⟨hT, -⟩
    · exact h
    · rcases hcase j with ⟨ht, -⟩ | ⟨ht, -⟩ <;> rw [ht] at hT <;> exact absurd hT (by decide)
  have hf : 1 ≤ f := by
    rw [← hexp i]
    exact (D.admissible i).2.1
  by_cases hp2 : p = 2
  · exfalso
    rcases hcase i with ⟨ht, hn, -⟩ | ⟨-, -, h1⟩
    · exact ModelFacts.L6C.false_of_twin_char2 hp2 D hD1 i ht hn htw.hA htw.hzA
    · rw [hp2] at h1
      obtain ⟨c, hc⟩ := dvd_pow_self 2 (show f ≠ 0 by omega)
      rw [hc] at h1
      omega
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₂₁ : i₂ = i₁ := Subsingleton.elim _ _
  subst h₂₁
  have hz : IsUniqueInvolution (R.map (D.hom i₂)) z' := by
    rw [← hAR]
    exact htw.hzA
  have hz' : IsUniqueInvolution (R'.map (D.hom i₂)) z' := by
    rw [← hAR']
    exact htw.hzA'
  have hne : R.map (D.hom i₂) ≠ R'.map (D.hom i₂) := by
    rw [← hAR, ← hAR']
    exact htw.ne
  have hcase' : (D.tag i₂ = .PSL ∧ D.rank i₂ = 4 ∧ ¬ p ^ D.exp i₂ % 4 = 1) ∨
      (D.tag i₂ = .PSU ∧ D.rank i₂ = 4 ∧ p ^ D.exp i₂ % 4 = 1) := by
    rw [hexp i₂]
    exact hcase i₂
  rw [hAR, hAR']
  exact twinCent6_of_hom hp2 (D.tag i₂) (D.rank i₂) (D.exp i₂) (D.admissible i₂) (D.hom i₂)
    (D.ker_le_center i₂) hcase' hR hR' hne hz hz'

end CFSG.ClassicalInvolution.Asc77.C25G
