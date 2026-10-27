module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddLie
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {S : Type} [Group S] [Finite S]

theorem not_of_properFixedComponent_alternating {R : ∀ (X : Type) [Group X], Prop}
    (hR : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → R X → R Y)
    (hRalt : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], 5 ≤ Fintype.card Ω →
      ¬ R (alternatingGroup Ω))
    (hR360 : ∀ (X : Type) [Group X] [Finite X], R X → ¬ Nat.card X ∣ 360)
    {n : ℕ} (hn : 5 ≤ n) (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} {P : Subgroup S}
    (h : CatLeaf.ProperFixedComponent σ P) : ¬ R (P ⧸ Open.fusionZStar P) := by
  intro hP
  by_cases hn6 : n = 6
  · subst hn6
    apply hR360 _ hP
    have h1 := CatLeaf.card_dvd_of_fusionZStar_equiv (Equiv.refl (P ⧸ Open.fusionZStar P))
    rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h1
    norm_num [Nat.factorial] at h1
    exact h1
  obtain ⟨h', ⟨e⟩⟩ := h.map θ
  obtain ⟨Ω, _, _, hΩ, ⟨eA⟩⟩ := CatLeaf.isAltType_of_properFixedComponent_alternating hn hn6 h'
  exact hRalt Ω hΩ (hR _ _ (e.trans eA) hP)

theorem not_of_properFixedComponent_oddLie
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) (hO : CatLeaf.LieOrderFormulasInput)
    {R : ∀ (X : Type) [Group X], Prop}
    (hR : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → R X → R Y)
    (hRodd : ∀ (X : Type) [Group X] (t : StatedLieTag) (n p f : ℕ), p.Prime → p ≠ 2 →
      StatedLieAdmissible t n p f → LieModel X t n p f → ¬ R X)
    (hR504 : ∀ (X : Type) [Group X] [Finite X], R X → ¬ Nat.card X ∣ 504)
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (hodd : OddLieType S) {σ : MulAut S}
    {P : Subgroup S} (h : CatLeaf.ProperFixedComponent σ P) : ¬ R (P ⧸ Open.fusionZStar P) := by
  intro hP
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hq : IsQuasisimple L :=
    CatLeaf.fixedTwoComponentsQuasisimple_of_oddLieType hna hodd σ hσσ hσ1 L h.2.2.1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hq
  have hRL : R (L ⧸ center L) := hR _ _ eZ hP
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hm⟩ := hodd
  rcases hGLS S τ n p f hp hp2 hadm hm σ hσ2 L hcomp with ⟨τ', n', f', hadm', hm'⟩ |
      ⟨-, -, -, h8⟩
  · exact hRodd _ τ' n' p f' hp hp2 hadm' hm' hRL
  · apply hR504 _ hRL
    rw [← CatLeaf.card_of_lieModel_psl_two_eight hO h8]
    exact Subgroup.card_quotient_dvd_card _

theorem not_of_properFixedComponent_evenLie_inner
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) (hO : CatLeaf.LieOrderFormulasInput)
    {R : ∀ (X : Type) [Group X], Prop}
    (hR : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → R X → R Y)
    (hRalt : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], 5 ≤ Fintype.card Ω →
      ¬ R (alternatingGroup Ω))
    (hR360 : ∀ (X : Type) [Group X] [Finite X], R X → ¬ Nat.card X ∣ 360)
    (hRodd : ∀ (X : Type) [Group X] (t : StatedLieTag) (n p f : ℕ), p.Prime → p ≠ 2 →
      StatedLieAdmissible t n p f → LieModel X t n p f → ¬ R X)
    (hR504 : ∀ (X : Type) [Group X] [Finite X], R X → ¬ Nat.card X ∣ 504)
    (hR20160 : ∀ (X : Type) [Group X] [Finite X], R X → ¬ Nat.card X ∣ 20160)
    (hRHe : ∀ (X : Type) [Group X] [Finite X], R X → ¬ Nat.card X ∣ 4030387200)
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (heven : EvenLieType S) {σ : MulAut S}
    {P : Subgroup S} (h : CatLeaf.ProperFixedComponent σ P) {t : S} (ht : σ = MulAut.conj t) :
    ¬ R (P ⧸ Open.fusionZStar P) := by
  intro hP
  obtain ⟨ht2, -, hPc, -⟩ := h.inner hna ht
  rcases CatLeaf.oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU
  · have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
    exact CatLeaf.involutionCentralizersComponentFree_of_evenLieType heven t ht2 _
      ⟨hq, hPc.choose_spec.2.1⟩
  · rcases hU with ho | ⟨n, -, h7, hA⟩ | hL | hH
    · exact not_of_properFixedComponent_oddLie hGLS hO hR hRodd hR504 hna ho h hP
    · obtain ⟨θ⟩ := hA
      exact not_of_properFixedComponent_alternating hR hRalt hR360 (by omega) θ h hP
    · apply hR20160 _ hP
      have h1 := CatLeaf.card_dvd_of_fusionZStar_equiv (Equiv.refl (P ⧸ Open.fusionZStar P))
      rwa [CatLeaf.card_of_isL34Type hL] at h1
    · obtain ⟨eH⟩ := hH
      apply hRHe _ hP
      have h1 := CatLeaf.card_dvd_of_fusionZStar_equiv (Equiv.refl (P ⧸ Open.fusionZStar P))
      rwa [Nat.card_congr eH.toEquiv, Sporadic.He.card_He] at h1

end CFSG.ComponentClassification.GrSLit.L34Sec5S
