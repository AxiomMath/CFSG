module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenQuasi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenE6ThreeUntw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenE6ThreeTw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenE6ThreeField
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem isComponentOf_congr {S G : Type*} [Group S] [Group G] (φ : S ≃* G)
    {P : Subgroup (MulAut S)} {J : Subgroup S}
    (hJ : ∀ x ∈ P, x ≠ 1 → IsComponentOf J (fixSubgroup x)) :
    ∀ x ∈ P.map (MulAut.congr φ).toMonoidHom, x ≠ 1 →
      IsComponentOf (J.map φ.toMonoidHom) (fixSubgroup x) := by
  rintro _ ⟨x, hx, rfl⟩ hx1
  have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have h := isComponentOf_map_of_injective φ.toMonoidHom φ.injective (hJ x hx hx1')
  change IsComponentOf (J.map φ.toMonoidHom) (fixSubgroup (MulAut.congr φ x))
  rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr]
  exact h


theorem genPlaneE6Three_holds : GenPlaneE6Three := by
  intro T _ _ d h hd P hP hcard J hall
  have hcomp : ∀ x ∈ P, x ≠ 1 → IsComponentOf J (fixSubgroup x) := fun x hx hx1 =>
    genCompQuasiOn_holds 3 T d h trivial x (hP.2 x hx) hx1 J (hall x hx hx1)
  obtain ⟨e⟩ := h.iso
  obtain ⟨idx, hv⟩ := d
  obtain ⟨Q, hQ⟩ := hd
  have hpQ : (3 : ℕ) ≠ Q.p := by
    have h3 := h.ne
    rcases hQ with rfl | rfl <;> simpa using h3
  have h2Q : Q.p ≠ 2 := by
    have h2 := h.charOdd
    rcases hQ with rfl | rfl <;> simpa using h2
  have hQ2 : Q.card ≠ 2 := by
    intro hQc
    apply h2Q
    have hdvd : Q.p ∣ 2 := by
      rw [← hQc, TauCeti.PrimePower.card_def]
      exact dvd_pow_self _ Q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq Q.prime_p Nat.prime_two).1 hdvd
  have hP3 : ¬ 3 ∣ Q.card := not_dvd_card_of_ne Nat.prime_three hpQ
  rcases hQ with rfl | rfl
  ·
    obtain ⟨K, hF, hFin, hK, hKchar, ⟨ε⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 Q hv
    letI : Field K := hF
    letI : Finite K := hFin
    let φ : T ≃* adjointGroup Tag.E6 K := e.trans ε
    have hK3 : ringChar K ≠ 3 := by
      rw [ringChar.eq K Q.p]
      exact hpQ.symm
    have h3K : ¬ 3 ∣ Nat.card K := by
      rw [hK]
      exact hP3
    have hK4 : 4 ≤ Nat.card K :=
      four_le_of_not_three_dvd Finite.one_lt_card h3K (by rw [hK]; exact hQ2)
    have hP' : IsElemAbelian 3 (P.map (MulAut.congr φ).toMonoidHom) := hP.map _
    have hcard' : Nat.card (P.map (MulAut.congr φ).toMonoidHom) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective, hcard]
    have hcomp' := isComponentOf_congr φ hcomp
    by_cases hdiag : P.map (MulAut.congr φ).toMonoidHom ≤ e6Inndiag K
    · exact e6Three_not_common_component_of_le_inndiag hK3 hK4 hP' hcard' hdiag _ hcomp'
    · exact e6Three_not_common_component_of_not_le_inndiag hP' hcard' hdiag _ hcomp'
  ·
    obtain ⟨K, hF, σ, hK, hσ, ⟨ε⟩⟩ := exists_catEquiv_twistedE6 Q hv
    letI : Field K := hF
    have hℓ := Q.prime_p
    have hf := Q.exponent_pos
    have hqc : Q.card = Q.p ^ Q.exponent := TauCeti.PrimePower.card_def Q
    haveI : Finite K := Nat.finite_of_card_ne_zero (by
      rw [hK]
      exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
    let φ : T ≃* twistedE6RootGroup K σ := e.trans ε
    have hP' : IsElemAbelian 3 (P.map (MulAut.congr φ).toMonoidHom) := hP.map _
    have hcard' : Nat.card (P.map (MulAut.congr φ).toMonoidHom) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective, hcard]
    have hcomp' := isComponentOf_congr φ hcomp
    by_cases hdiag : P.map (MulAut.congr φ).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ
    · exact twE6Three_not_common_component_of_le_inndiag hℓ (Ne.symm hpQ) hf
        (by rw [← hqc]; exact hQ2) hK σ hσ hP' hcard' hdiag _ hcomp'
    · exact twE6Three_not_common_component_of_not_le_inndiag hℓ hf hK σ hσ hP' hcard' hdiag _
        hcomp'

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
