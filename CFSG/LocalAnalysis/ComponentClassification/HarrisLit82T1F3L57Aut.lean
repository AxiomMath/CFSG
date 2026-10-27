module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1Three
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Universal.Spin (quadOdd)
open CFSG.RankThree.Classical.SteinbergBY
  (OrthogonalGates orthogonal_large_prime_semilinear_field_and_diagonal_gates)

theorem mem_of_pow_mem_of_index_eq_two_pow {A : Type*} [Group A] {I : Subgroup A} [I.Normal]
    {m : ℕ} (hI : I.index = 2 ^ m) {a : A} {k : ℕ} (hk : Odd k) (ha : a ^ k ∈ I) : a ∈ I := by
  have hc : Nat.card (A ⧸ I) = 2 ^ m := hI
  have : Finite (A ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  set b : A ⧸ I := (a : A ⧸ I)
  have hb : b ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  have h1 : orderOf b ∣ k := orderOf_dvd_of_pow_eq_one hb
  have h2 : orderOf b ∣ 2 ^ m := hc ▸ orderOf_dvd_natCard b
  have hcop : Nat.Coprime k (2 ^ m) := Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hk)
  have h3 : orderOf b = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff a).mp h3

theorem mem_range_conj_of_pow_mem_three {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hp : p.Prime) (h3 : p ^ f = 3) (hX : IsCoverOf .POmegaOdd 3 p f 2 X) {α : MulAut X} {k : ℕ}
    (hk : Odd k) (hα : α ^ k ∈ (MulAut.conj : X →* MulAut X).range) :
    α ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨hq, -, hL⟩ := hX
  have : Group.IsPerfect X := hq.1
  rcases hL with ⟨-, hcm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hcm' := hcm
    obtain ⟨⟨-, hf, -, hp2⟩, K, _, _, hK, ⟨e⟩⟩ := hcm'
    have h2 : ringChar K ≠ 2 := by
      rw [CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hK]
      exact hp2
    have hK3 : Nat.card K = 3 := hK.trans h3
    obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨-, m, hm⟩, -⟩ :=
      orthogonal_large_prime_semilinear_field_and_diagonal_gates
        (X ⧸ center X) .POmegaOdd (Or.inl rfl) 3 p f hcm K hK e
    have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K 3
      le_rfl h2
    have hD : (linearConjugationHom (coordinateQuadOdd 3 K)).range = ⊤ := by
      rw [eq_top_iff]
      intro a _
      have ha : a ∈ matrixProjectiveImage (coordinateQuadOdd 3 K) := htop ▸ mem_top a
      have hker : (⟨a, ha⟩ : matrixProjectiveImage (coordinateQuadOdd 3 K)) ∈ ψ.ker :=
        MonoidHom.mem_ker.mpr (ringEquiv_eq_one_of_card_eq_three hK3 _)
      rw [hψker] at hker
      exact hker
    rw [hD, relIndex_top_right] at hm
    set e' := coordinateOddWitnessEquiv K e with he'
    let Φ : MulAut X →* MulAut (matrixProjectiveDerived (coordinateQuadOdd 3 K)) :=
      (MulAut.congr e').toMonoidHom.comp (PerfectAutomorphisms.centerQuotientHom X)
    have hΦconj : ∀ x : X, Φ (MulAut.conj x) = MulAut.conj (e' (QuotientGroup.mk' (center X) x)) :=
      fun x => by
        change MulAut.congr e' (PerfectAutomorphisms.onCenterQuotient (MulAut.conj x)) = _
        rw [onCenterQuotient_conj, OuterAutomorphisms.congr_conj]
    have hconjΦ : ∀ y, ∃ x : X, MulAut.conj y = Φ (MulAut.conj x) := fun y => by
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center X) (e'.symm y)
      exact ⟨x, by rw [hΦconj, hx, MulEquiv.apply_symm_apply]⟩
    have hΦ : Function.Injective Φ :=
      (MulAut.congr e').injective.comp (PerfectAutomorphisms.centerQuotientHom_injective X)
    have hI : (inner (matrixProjectiveDerived (coordinateQuadOdd 3 K))).comap Φ =
        (MulAut.conj : X →* MulAut X).range := by
      ext β
      rw [mem_comap]
      constructor
      · rintro ⟨y, hy⟩
        obtain ⟨x, hx⟩ := hconjΦ y
        exact ⟨x, hΦ (hx.symm.trans hy)⟩
      · rintro ⟨x, rfl⟩
        exact ⟨_, (hΦconj x).symm⟩
    rw [← hI] at hα ⊢
    rw [mem_comap, map_pow] at hα
    exact mem_of_pow_mem_of_index_eq_two_pow hm hk hα
  all_goals omega

end CFSG.ComponentClassification.HarrisLit.T1
