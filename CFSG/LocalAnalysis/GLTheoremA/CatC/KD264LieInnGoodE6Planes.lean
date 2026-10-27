module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangAlg
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FiveAux.Plane
public import CFSG.Monster.B.E6.StdF4RadicalRoots

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

section Five


theorem perfectCentralizerPlanes_adjointGroup_E6_five (K : Type) [Field K] [Finite K]
    (h5K : ¬ 5 ∣ Nat.card K) (hq : Nat.card K % 5 = 1 ∨ Nat.card K % 5 = 4) :
    PerfectCentralizerPlanes 5 (adjointGroup Tag.E6 K) := by
  refine perfectCentralizerPlanes_adjointGroup_of_langTorus (W := fun _ => True)
    (Or.inr (Or.inl rfl)) K Nat.prime_five h5K (Or.inl le_rfl) ?_ ?_
  · intro A hAp hAc
    obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ := langToralPlane_E6_five K h5K A hAp hAc
    exact ⟨w, trivial, Fr, hFr, g0, hg0C, hg0, c, hc⟩
  · intro w _ Fr hFr g0 hg0C hg0 S hS D₁ hD₁ hc
    have hqS : S.D.q = Nat.card K := by rw [hS]; rfl
    exact bigComponentSet_nonempty_of_bigAnyPBig S
      (bigAnyPBig_five S (by rw [hqS]; exact hq)) hD₁ hc

end Five

section One


theorem perfectCentralizerPlanes_adjointGroup_E6_one (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hd : p ∣ Nat.card K - 1) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E6 K) :=
  perfectCentralizerPlanes_of_conj_into_torus hp (by omega) hd
    (fun A hA hAp => exists_conj_into_torus_E6 hp hp7 hd hA hAp)

end One

section Two


theorem perfectCentralizerPlanes_adjointGroup_E6_two (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hpd : p ∣ Nat.card K + 1)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E6 K) := by
  classical
  obtain ⟨Fr, hFr, g0, hg0C, hg0, S, hSD, hsyl, ⟨ε⟩⟩ :=
    springer_exists_langSetup_E6_two frobeniusOnRoots_proved K hp hp7 hpK h2
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hK4 : 4 ≤ Nat.card K := by
    have := Nat.le_of_dvd (by omega) hpd
    omega
  have hK8 : Nat.card K ≠ 8 := by
    intro h
    rw [h] at hpd
    have := Nat.le_of_dvd (by norm_num) hpd
    have h9 : p ∣ 3 ^ 2 := by simpa using hpd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h9)
    omega
  obtain ⟨Z, hZΓ, hZp, hZspan, hZord, -⟩ := exists_rigid_frame_E6_two hFr hg0C hg0 hK4 hK8
  have hfrob : FrobRootMap (LangDatum.ofFrobenius Fr (Nat.card K) hFr e6PhiTwoWeyl hg0C hg0)
      S.ρ := hSD ▸ S.frob
  have hρ := frobRootMap_ofFrobenius_apply Nat.card_pos hFr hg0C hg0 hfrob
    (isRoot_single Tag.E6 (1 : Fin Tag.E6.rank))
  have hspan : Z 1 ≤ rootSpan Tag.E6 (AlgebraicClosure K) {γ | ∃ j : ℕ,
      γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[j] (Pi.single 1 1) ∨
        γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[j] (-Pi.single 1 1)} := by
    refine (hZspan 1).trans (biSup_mono ?_)
    rintro γ (rfl | rfl | rfl | rfl)
    · exact ⟨0, Or.inl rfl⟩
    · exact ⟨0, Or.inr rfl⟩
    · exact ⟨1, Or.inl hρ.symm⟩
    · refine ⟨1, Or.inr ?_⟩
      change -(e6PhiTwoWeyl • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ)) = S.ρ (-Pi.single 1 1)
      rw [S.frob.neg_eq, hρ]
  have hbig : ∀ D₁ : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)), D₁ ≤ S.E →
      Nat.card D₁ = p ^ 2 → (bigComponentSet S D₁).Nonempty := by
    intro D₁ hD₁ hc
    obtain ⟨x, hxZ, hxp⟩ := hZord p hp (by omega) hpd 1
    have hΓ : Z 1 ≤ S.Γ := by
      change Z 1 ≤ S.D.Γ
      rw [hSD]
      exact hZΓ 1
    exact ⟨x, subset_bigComponentSet_of_perfect S hD₁ hc (isRoot_single Tag.E6 1) hΓ (hZp 1)
      hspan hxZ hxp hxZ⟩
  exact PerfectCentralizerPlanes.of_mulEquiv ε.symm
    (perfectCentralizerPlanes_of_sylow_le_torus S hsyl hbig)

end Two

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
