module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Moved
public import CFSG.HardMathSupport.Timmesfeld.Balance.Normalizes
public import CFSG.HardMathSupport.Timmesfeld.Balance.Faithful

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ClassicalInvolution.Balance.LocalBalance

universe u

variable {Y : Type u} [Group Y] [Finite Y] {p : ℕ}

theorem eq_bot_of_centralizes_pCore_of_centralizes_components_p (hp : p.Prime)
    (hO : GLAPPrimeCore p Y = ⊥) {D : Subgroup Y}
    (hDord : ∀ d ∈ D, (orderOf d).Coprime p)
    (hQ : D ≤ Subgroup.centralizer (CFSG.pCore p Y : Set Y))
    (hL : ∀ L : Subgroup Y, CFSG.IsComponent L → D ≤ Subgroup.centralizer (L : Set Y)) :
    D = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hO' : CFSG.pPrimeCore p Y = ⊥ := hO
  have hF : CFSG.fittingSubgroup Y = CFSG.pCore p Y := CFSG.Fitting_eq_pcore Y p hO'
  have hFc : CFSG.generalizedFitting Y ≤ Subgroup.centralizer (D : Set Y) := by
    refine sup_le ?_ (sSup_le fun L hL' => ?_)
    · rw [hF]
      exact Subgroup.le_centralizer_iff.mp hQ
    · exact Subgroup.le_centralizer_iff.mp (hL L hL')
  have hDF : D ≤ CFSG.fittingSubgroup Y := by
    have h1 : D ≤ Subgroup.centralizer (CFSG.generalizedFitting Y : Set Y) :=
      Subgroup.le_centralizer_iff.mp hFc
    have h2 := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting Y
    rw [← CFSG.generalizedFitting_eq_componentClassification] at h2
    exact h1.trans h2
  rw [hF] at hDF
  refine (Subgroup.eq_bot_iff_forall D).mpr fun d hd => ?_
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := p) (G := Y)) ⟨d, hDF hd⟩
  have hj' : d ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right j (hDord d hd)) (orderOf_dvd_of_pow_eq_one hj'))

theorem delta_eq_bot_of_locallyBalanced (hH1 : H1Stmt.{u}) (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k)
    (hO : GLAPPrimeCore p Y = ⊥) {F : Subgroup Y} (hFel : IsElemAbelian p F)
    (hFcard : Nat.card F = p ^ k)
    (hloc : ∀ L : Subgroup Y, IsComponent L → F ≤ Subgroup.normalizer (L : Set Y) →
      (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) → IsLocallyBalanced p k (fImage F L)) :
    (⨅ (f : Y) (_ : f ∈ F) (_ : f ≠ 1),
      GLAPPrimeCoreOf p (Subgroup.centralizer ({f} : Set Y))) = ⊥ := by
  have hpF : Fact p.Prime := ⟨hp⟩
  set D : Subgroup Y := ⨅ (f : Y) (_ : f ∈ F) (_ : f ≠ 1),
    GLAPPrimeCoreOf p (Subgroup.centralizer ({f} : Set Y)) with hDdef
  have hDF : ∀ f ∈ F, f ≠ 1 →
      D ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({f} : Set Y)) := fun f hf hf1 =>
    (iInf_le _ f).trans ((iInf_le _ hf).trans (iInf_le _ hf1))
  obtain ⟨f₀, hf₀F, hf₀1⟩ : ∃ f ∈ F, f ≠ 1 := by
    have : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hFcard]; exact Nat.one_lt_pow (by omega) hp.one_lt)
    obtain ⟨⟨f, hf⟩, hne⟩ := exists_ne (1 : F)
    exact ⟨f, hf, fun h => hne (Subtype.ext h)⟩
  have hFp : ∀ f ∈ F, f ^ p = 1 := hFel.2
  have hord : orderOf f₀ = p := orderOf_eq_prime (hFp f₀ hf₀F) hf₀1
  have hDord : ∀ d ∈ D, (orderOf d).Coprime p := fun d hd =>
    CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf hp
      (hDF f₀ hf₀F hf₀1 hd)
  have hQ : D ≤ Subgroup.centralizer (CFSG.pCore p Y : Set Y) := by
    have he : IsPGroup p (Subgroup.zpowers f₀) := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [Nat.card_zpowers, hord, pow_one]⟩
    have := CFSG.HardMathSupport.Timmesfeld.Proving.glaPPrimeCoreOf_centralizer_le_centralizer_pCore
      hp he
    exact (hDF f₀ hf₀F hf₀1).trans this
  have hLc : ∀ L : Subgroup Y, CFSG.IsComponent L → D ≤ Subgroup.centralizer (L : Set Y) := by
    intro L hL
    have hLp := p_dvd_card_center_quot hp hO hL
    have key : ∀ d ∈ D, ∀ x ∈ L, d * x = x * d := by
      by_cases hcen : ∃ f ∈ F, f ≠ 1 ∧ ∀ x ∈ L, f * x = x * f
      · obtain ⟨f, hfF, hf1, hfL⟩ := hcen
        have hLC : L ≤ Subgroup.centralizer ({f} : Set Y) := fun x hx =>
          Subgroup.mem_centralizer_singleton_iff.mpr (hfL x hx).symm
        have hnc : ¬ Nat.Coprime p (Nat.card L) := by
          intro hcop
          have h1 : Nat.card (↥L ⧸ Subgroup.center ↥L) ∣ Nat.card L :=
            Subgroup.card_quotient_dvd_card _
          have h2 : p ∣ Nat.card L := hLp.trans h1
          exact hp.one_lt.ne' (hcop.eq_one_of_dvd h2)
        intro d hd
        exact commute_of_mem_gLAPPrimeCoreOf_of_isComponent hp hLC
          (CFSG.LocalCores.component_overgroup hL hLC) hnc (hDF f hfF hf1 hd)
      · by_cases hmov : ∃ f ∈ F, conjSub f L ≠ L
        · obtain ⟨f, hfF, hfne⟩ := hmov
          have hf1 : f ≠ 1 := fun h => hfne (by rw [h, conjSub_one])
          intro d hd
          exact commute_of_moved_p hp hL hLp (hFp f hfF) hfne (hDF f hfF hf1 hd)
        · push Not at hcen hmov
          have hDn : ∀ d ∈ D, conjSub d L = L := fun d hd =>
            conjSub_eq_of_mem_gLAPPrimeCoreOf hH1 hp hL hLp (hFp f₀ hf₀F) (hmov f₀ hf₀F)
              (hDF f₀ hf₀F hf₀1 hd)
          have hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f := by
            intro f hf hf1 h
            obtain ⟨x, hx, hxne⟩ := hcen f hf hf1
            exact hxne (h x hx)
          have hFn : F ≤ Subgroup.normalizer (L : Set Y) := fun f hf =>
            mem_normalizer_of_conjSub_eq (hmov f hf)
          intro d hd
          exact commute_of_faithful_p hH1 hp hL hFel hFcard hmov hfaith
            (hloc L hL hFn hfaith) hDn hDF d hd
    intro d hd x hx
    exact (key d hd x hx).symm
  exact eq_bot_of_centralizes_pCore_of_centralizes_components_p hp hO hDord hQ hLc

end CFSG.HardMathSupport.Timmesfeld.Balance
