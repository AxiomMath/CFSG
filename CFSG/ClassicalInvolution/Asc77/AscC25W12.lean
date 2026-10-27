module

public import CFSG.ClassicalInvolution.Asc77.AscC25W3
public import CFSG.ClassicalInvolution.Asc77.AscC25W11

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25W

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs

variable {p f : ℕ} [Fact p.Prime]


theorem two_ne_zero_gf (e : ℕ) (h : p ≠ 2) : (2 : GaloisField p e) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p e) p 2).1 (by exact_mod_cast h0)
  exact h ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd)

theorem layer5Sq_of_hom (hp2 : p ≠ 2) {Y : Type} [Group Y] (t : StatedLieTag) (k e : ℕ)
    (hadm : StatedLieAdmissible t k p e) (ψ : (modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (ht : t = .PSp) (hk : k = 2) (hq : 5 ≤ p ^ e)
    {R R' : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') (β : MulAut Y)
    (hβ : ∀ x : Y, β (β (β (β x))) = x) :
    ∃ R₀ ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D, ∃ s ∈ R₀,
      orderOf (ψ s) = 4 ∧ β (β (ψ s)) = ψ s := by
  subst ht hk
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have h2 := two_ne_zero_gf (p := p) e hp2
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  obtain ⟨P, hP, hRP⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
  obtain ⟨P', hP', hRP'⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'
  obtain ⟨i, hi⟩ := (exists_isLongRootSp2_iff h2 R).mpr ⟨P, hP, hRP⟩
  obtain ⟨i', hi'⟩ := (exists_isLongRootSp2_iff h2 R').mpr ⟨P', hP', hRP'⟩
  obtain ⟨u, w, s, huw, hs, hord, hfix⟩ :=
    Sp.psp4_model_sq h2 h4 ψ hker hsurj hi hi' hne hz hz' β hβ
  refine ⟨planeGroup (Submodule.span (GaloisField p e) {u, w}), ?_, s, hs, hord, hfix⟩
  exact (mem_fundamentalSubgroups_PSp_iff hadm _).mpr ⟨_, ⟨u, w, huw, rfl⟩, rfl⟩

theorem layer5Sq_proved : Layer5Sq p f := by
  intro hp2 hq Y _ _ Φ D A A' z' a₀ b₀ hD1 hi htw hconj β hββ
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
  have hcase : ∀ j : Fin D.card, D.tag j = .PSp ∧ D.rank j = 2 := by
    intro j
    rw [Subsingleton.elim j i]
    simp only [IsOrthTag] at hi
    rcases hi with ⟨-, ht, hn⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · exact ⟨ht, hn⟩
    all_goals omega
  have hexp : ∀ j : Fin D.card, D.exp j = f := by
    intro j
    rcases D.exp_eq j with h | ⟨hT, -⟩
    · exact h
    · rw [(hcase j).1] at hT
      exact absurd hT (by decide)
  have hβ : ∀ x : Y, β (β (β (β x))) = x := hββ
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₂₁ : i₂ = i₁ := Subsingleton.elim _ _
  subst h₂₁
  have hq' : 5 ≤ p ^ D.exp i₂ := by rw [hexp i₂]; exact hq
  have hz : IsUniqueInvolution (R.map (D.hom i₂)) z' := by
    rw [← hAR]
    exact htw.hzA
  have hz' : IsUniqueInvolution (R'.map (D.hom i₂)) z' := by
    rw [← hAR']
    exact htw.hzA'
  have hne : R.map (D.hom i₂) ≠ R'.map (D.hom i₂) := by
    rw [← hAR, ← hAR']
    exact htw.ne
  obtain ⟨R₀, hR₀, s, hs, hord, hfix⟩ :=
    layer5Sq_of_hom hp2 (D.tag i₂) (D.rank i₂) (D.exp i₂) (D.admissible i₂) (D.hom i₂)
      (D.ker_le_center i₂) (hsurj i₂) (hcase i₂).1 (hcase i₂).2 hq' hR hR' hne hz hz' β hβ
  have hfund : D.tag i₂ ≠ .G2 ∧ D.tag i₂ ≠ .trialityD4 := by
    rw [(hcase i₂).1]
    exact ⟨by decide, by decide⟩
  have hsingle := CFSG.ClassicalInvolution.RouteD.Gaps.fundamentalSingleClass_of_ne D i₂
    hfund.1 hfund.2
  have hJ : R₀.map (D.hom i₂) ∈ Φ :=
    D.map_mem_of_single_class (fun g L hL => hconj L hL g) i₂ hsingle hR₀
  refine ⟨R₀.map (D.hom i₂), hJ, D.hom i₂ s, Subgroup.mem_map_of_mem _ hs, ?_, ?_, hfix⟩
  · have h4 : D.hom i₂ s ^ 4 = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    simpa [pow_succ, mul_assoc] using h4
  · intro h
    have h2 : orderOf (D.hom i₂ s) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hord] at h2
    omega

end CFSG.ClassicalInvolution.Asc77.C25W
