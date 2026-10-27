module

public import CFSG.ClassicalInvolution.Asc77.AscCX4L4
public import CFSG.ClassicalInvolution.Asc77.AscCX4U5
import CFSG.ClassicalInvolution.ModelFacts.L6CMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]


theorem layer6_facts_of_hom (hp2 : p ≠ 2) {Y : Type} [Group Y] (t : StatedLieTag) (k e : ℕ)
    (hadm : StatedLieAdmissible t k p e) (ψ : (Generic.modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ)
    (hcase : (t = .PSL ∧ k = 4 ∧ ¬ p ^ e % 4 = 1) ∨ (t = .PSU ∧ k = 4 ∧ p ^ e % 4 = 1))
    {R R' : Subgroup (Generic.modelUniv t k p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t k p e Fact.out).D)
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') : LayerTwinFacts (R.map ψ) (R'.map ψ) z' := by
  have he : 1 ≤ e := hadm.2.1
  have hodd : p ^ e % 2 = 1 :=
    Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  rcases hcase with ⟨rfl, rfl, h4⟩ | ⟨rfl, rfl, h4⟩
  · have h2 : (2 : GaloisField p e) ≠ 0 := C25W.two_ne_zero_gf (p := p) e hp2
    have hsq : ¬ IsSquare (-1 : GaloisField p e) := by
      have : Fintype (GaloisField p e) := Fintype.ofFinite _
      rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card,
        GaloisField.card p e (by omega)]
      omega
    exact CX4.L4.layerTwinFacts_psl4 h2 hsq ψ hker hsurj
      (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR)
      (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num)
        hR') hne hz hz'
  · have h1 : 1 < p ^ e := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
    have hq : 5 ≤ p ^ e := by omega
    have : NeZero (2 * e) := ⟨by omega⟩
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
    have hθsurj : Function.Surjective θ := fun y => by
      obtain ⟨r, rfl⟩ := hsurj y
      exact ⟨φ r, hθφ r⟩
    have hmap : ∀ S : Subgroup (Generic.modelUniv .PSU 4 p e Fact.out).K,
        S.map ψ = (S.map φ.toMonoidHom).map θ := fun S => by
      rw [Subgroup.map_map]
      congr 1
      ext r
      exact (hθφ r).symm
    rw [hmap R] at hz
    rw [hmap R'] at hz'
    rw [hmap R, hmap R'] at hne ⊢
    exact CX4.U4.layerTwinFacts_psu4 hK hp2 hq h4 θ hθker hθsurj ((hφ R).mp hR)
      ((hφ R').mp hR') hne hz hz'

variable (p f) in
theorem layer6Twin_proved : Layer6Twin p f := by
  intro Y _ _ Φ D A A' z' a₀ b₀ hD1 hi htw
  obtain ⟨i, hi⟩ := hi
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : ∀ j : Fin D.card, Function.Surjective (D.hom j) := by
    intro j
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom j).range := by
      intro l
      rw [Subsingleton.elim l j]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
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
  exact layer6_facts_of_hom hp2 (D.tag i₂) (D.rank i₂) (D.exp i₂) (D.admissible i₂) (D.hom i₂)
    (D.ker_le_center i₂) (hsurj i₂) hcase' hR hR' hne hz hz'

end CFSG.ClassicalInvolution.Asc77.CX
