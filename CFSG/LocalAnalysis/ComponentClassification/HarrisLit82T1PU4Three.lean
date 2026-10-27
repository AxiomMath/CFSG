module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Props

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open CFSG.GH74.GLS.Bg.Thompson (IsSylowIn)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Universal.Spin (quadOdd)
open CFSG.RankThree.Classical.SteinbergBY
  (OrthogonalGates orthogonal_large_prime_semilinear_field_and_diagonal_gates)

theorem harris82Lemma411U4Three_holds : Harris82Lemma411U4Three := by
  intro X _ _ p f hp _ hX C P hIC hP
  obtain ⟨hq, -, hL⟩ := hX
  have : Group.IsPerfect X := hq.1
  rcases hL with ⟨-, hcm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hcm' := hcm
    obtain ⟨⟨-, hf, -, hp2⟩, K, _, _, hK, ⟨e⟩⟩ := hcm'
    have h2 : ringChar K ≠ 2 := by
      rw [CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hK]
      exact hp2
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates
      (X ⧸ center X) .POmegaOdd (Or.inl rfl) 3 p f hcm K hK e
    obtain ⟨φ, hOut⟩ := outData_coordinateQuadOdd K 3 hp hf hK h2 le_rfl hgates
    set e' := coordinateOddWitnessEquiv K e with he'
    let Φ : MulAut X →* MulAut (matrixProjectiveDerived (coordinateQuadOdd 3 K)) :=
      (MulAut.congr e').toMonoidHom.comp (PerfectAutomorphisms.centerQuotientHom X)
    have hΦ : Function.Injective Φ :=
      (MulAut.congr e').injective.comp (PerfectAutomorphisms.centerQuotientHom_injective X)
    have hΦconj : ∀ x : X, Φ (MulAut.conj x) = MulAut.conj (e' (QuotientGroup.mk' (center X) x)) :=
      fun x => by
        change MulAut.congr e' (PerfectAutomorphisms.onCenterQuotient (MulAut.conj x)) = _
        rw [onCenterQuotient_conj, OuterAutomorphisms.congr_conj]
    have hconjΦ : ∀ y, ∃ x : X, MulAut.conj y = Φ (MulAut.conj x) := fun y => by
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center X) (e'.symm y)
      exact ⟨x, by rw [hΦconj, hx, MulEquiv.apply_symm_apply]⟩
    have hI : (inner (matrixProjectiveDerived (coordinateQuadOdd 3 K))).comap Φ =
        (MulAut.conj : X →* MulAut X).range := by
      ext α
      rw [mem_comap]
      constructor
      · rintro ⟨y, hy⟩
        obtain ⟨x, hx⟩ := hconjΦ y
        exact ⟨x, hΦ (hx.symm.trans hy)⟩
      · rintro ⟨x, rfl⟩
        exact ⟨_, (hΦconj x).symm⟩
    have hIC' : inner (matrixProjectiveDerived (coordinateQuadOdd 3 K)) ≤ C.map Φ := by
      rintro _ ⟨y, rfl⟩
      obtain ⟨x, hx⟩ := hconjΦ y
      exact ⟨MulAut.conj x, hIC ⟨x, rfl⟩, hx.symm⟩
    obtain ⟨V', hV'⟩ := exists_isU4Complement hOut hIC' (isSylowIn_map hΦ hP)
    exact ⟨_, isU4Complement_comap hΦ hI hV'⟩
  all_goals omega

end CFSG.ComponentClassification.HarrisLit.T1
