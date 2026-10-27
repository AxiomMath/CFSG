module

public import CFSG.ClassicalInvolution.Asc77.AscC5OStmt
public import CFSG.ClassicalInvolution.Asc77.AscC5OM2

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {p f : ℕ} [Fact p.Prime]

theorem two_ne_zero_gf (e : ℕ) (hp : p ≠ 2) : (2 : GaloisField p e) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p e) p 2).1 (by exact_mod_cast h0)
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd)

theorem five_le_card_gf (hq : 5 ≤ p ^ f) : 5 ≤ Nat.card (GaloisField p f) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p f hf]
  exact hq


theorem frame_of_hom (hp2 : p ≠ 2) {Y : Type} [Group Y] {Φ : Set (Subgroup Y)}
    {A A' : Subgroup Y} {z' : Y} (t : StatedLieTag) (k e : ℕ)
    (hadm : StatedLieAdmissible t k p e) (ψ : (modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (ht : t = .PSp) (hk : k = 2) (he : e = f)
    {R R' : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hAR : A = R.map ψ) (hAR' : A' = R'.map ψ) (hne : A ≠ A')
    (hzA : IsUniqueInvolution A z') (hzA' : IsUniqueInvolution A' z')
    (hΦ1 : ∀ J ∈ Φ, ∃ R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D, J = R.map ψ)
    (hΦ2 : ∀ R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D, R.map ψ ∈ Φ) :
    Nonempty (Frame (GaloisField p f) Y Φ A A' z') := by
  subst ht hk he
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_gf e hp2
  obtain ⟨P, hP, hRP⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
  obtain ⟨P', hP', hRP'⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'
  obtain ⟨i, hi⟩ := (exists_isLongRootSp2_iff h2 R).mpr ⟨P, hP, hRP⟩
  obtain ⟨i', hi'⟩ := (exists_isLongRootSp2_iff h2 R').mpr ⟨P', hP', hRP'⟩
  subst hAR hAR'
  refine exists_frame_model h2 ψ hker hsurj hi hi' hne hzA hzA' ?_ ?_
  · intro J hJ
    obtain ⟨R₂, hR₂, rfl⟩ := hΦ1 J hJ
    obtain ⟨P₂, hP₂, rfl⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R₂).mp hR₂
    exact ⟨P₂, hP₂, rfl⟩
  · intro P₃ hP₃
    exact hΦ2 _ ((mem_fundamentalSubgroups_PSp_iff hadm _).mpr ⟨P₃, hP₃, rfl⟩)

theorem exists_frame {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y}
    {z' a₀ b₀ : Y} (hD : Om5Data p f Y Φ A A' z' a₀ b₀) :
    Nonempty (Frame (GaloisField p f) Y Φ A A' z') := by
  obtain ⟨D, hD1, i, hi⟩ := hD.lie
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : Function.Surjective (D.hom i) := by
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom i).range := by
      intro l
      rw [Subsingleton.elim l i]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hcase : D.tag i = .PSp ∧ D.rank i = 2 := by
    simp only [IsOrthTag] at hi
    rcases hi with ⟨-, ht, hn⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · exact ⟨ht, hn⟩
    all_goals omega
  have hexp : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨hT, -⟩
    · exact h
    · rw [hcase.1] at hT
      exact absurd hT (by decide)
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A hD.twin.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' hD.twin.hA'
  obtain rfl : i₁ = i := Subsingleton.elim _ _
  obtain rfl : i₂ = i₁ := Subsingleton.elim _ _
  have hfund : D.tag i₂ ≠ .G2 ∧ D.tag i₂ ≠ .trialityD4 := by
    rw [hcase.1]
    exact ⟨by decide, by decide⟩
  have hsingle := CFSG.ClassicalInvolution.RouteD.Gaps.fundamentalSingleClass_of_ne D i₂
    hfund.1 hfund.2
  refine frame_of_hom hD.odd (D.tag i₂) (D.rank i₂) (D.exp i₂) (D.admissible i₂) (D.hom i₂)
    (D.ker_le_center i₂) hsurj hcase.1 hcase.2 hexp hR hR' hAR hAR' hD.twin.ne hD.twin.hzA
    hD.twin.hzA' ?_ ?_
  · intro J hJ
    obtain ⟨i₃, R₃, hR₃, hJR⟩ := D.fundamental J hJ
    obtain rfl : i₃ = i₂ := Subsingleton.elim _ _
    exact ⟨R₃, hR₃, hJR⟩
  · intro R₃ hR₃
    exact D.map_mem_of_single_class (fun g L hL => hD.conj L hL g) i₂ hsingle hR₃

end CFSG.ClassicalInvolution.Asc77.C5O.M
