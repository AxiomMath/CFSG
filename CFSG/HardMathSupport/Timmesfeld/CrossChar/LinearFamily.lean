module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearOuter
public import CFSG.Adapters.LinearCatalog
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LieType.SeitzGeneration.Inner
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LieType.SeitzGeneration.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial Matrix
  CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem isElemAbelian_map {M N : Type*} [Group M] [Group N] (f : M →* N) {p : ℕ}
    {E : Subgroup M} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map hE _

theorem isElemAbelian_comap {M N : Type*} [Group M] [Group N] (f : M →* N)
    (hf : Function.Injective f) {p : ℕ} {E : Subgroup N} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap f) := CFSG.Open.IsElemAbelian.comap hE hf

theorem exists_inner_plane_of_mulEquiv {S G : Type*} [Group S] [Group G] (e : S ≃* G) {p : ℕ}
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 3)
    (h : ∀ D' : Subgroup (MulAut G), IsElemAbelian p D' → Nat.card D' = p ^ 3 →
      ∃ E' : Subgroup (MulAut G), E' ≤ D' ∧ E' ≤ innerAut G ∧ IsElemAbelian p E' ∧
        Nat.card E' = p ^ 2) :
    ∃ E : Subgroup (MulAut S), E ≤ D ∧ E ≤ innerAut S ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 2 := by
  set φ : MulAut S ≃* MulAut G := MulAut.congr e with hφ
  obtain ⟨E', hE'D, hE'in, hE', hE'c⟩ := h (D.map φ.toMonoidHom) (isElemAbelian_map _ hD)
    (by rw [Subgroup.card_map_of_injective φ.injective]; exact hcard)
  refine ⟨E'.map φ.symm.toMonoidHom, ?_, ?_, isElemAbelian_map _ hE', ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, hzy⟩ := hE'D hy
    have : φ.symm y = z := by rw [← hzy]; simp
    simpa [this] using hz
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨g, hg⟩ := hE'in hy
    refine ⟨e.symm g, ?_⟩
    rw [← hg]
    ext s
    simp [hφ, MulAut.congr_symm_apply, MulAut.conj_apply]
  · rw [Subgroup.card_map_of_injective φ.symm.injective, hE'c]

theorem isLocallyBalancedAbs_psl {n : ℕ} {F : Type} [Field F] [Finite F] (hn : 2 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : ¬ p ∣ Nat.card F)
    (hreg : ¬ (p ∣ Nat.card F - 1 ∧ p ∣ n)) (h32 : ¬ (p = 3 ∧ Nat.card F = 2))
    (hinj : Function.Injective
      (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) F →*
        MulAut (ProjectiveSpecialLinearGroup (Fin n) F))) :
    IsLocallyBalancedAbs p 3 (ProjectiveSpecialLinearGroup (Fin n) F) := by
  intro D hD hcard H hH hDH
  have hpg : ¬ p ∣ Nat.gcd n (Nat.card F - 1) := fun h =>
    hreg ⟨h.trans (Nat.gcd_dvd_right _ _), h.trans (Nat.gcd_dvd_left _ _)⟩
  obtain ⟨E, hED, hEin, hE, hEc⟩ : ∃ E : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin n) F)),
      E ≤ D ∧ E ≤ innerAut _ ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
    by_cases hn3 : 3 ≤ n
    · exact exists_inner_plane_of_mulEquiv
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL n F) D hD hcard
        fun D' hD' hc' => exists_inner_plane_projectiveSL hn3 hp hp2 hpg D' hD' hc'
    · have : n = 2 := by omega
      subst this
      exact exists_inner_plane_psl2 hp hp2 D hD hcard
  have hE₁ : (E.comap (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) F →* _)).map
      (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) F →* _) = E :=
    Subgroup.map_comap_eq_self hEin
  have hE₁el := isElemAbelian_comap _ hinj hE
  have hE₁c : Nat.card (E.comap (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) F →* _)) =
      p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hE₁, hEc]
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hbot : localDeltaIn p H E = ⊥ := by
    rw [← hE₁]
    by_cases hs : p ∣ Nat.card F - 1
    · exact localDeltaIn_eq_bot_psl_split hp hp3 hs (fun h => hreg ⟨hs, h⟩) (by omega) hinj _
        hE₁el hE₁c hH
    · have hp4 : 3 < p ∨ 4 ≤ Nat.card F := by
        rcases (by omega : p = 3 ∨ 3 < p) with h3 | h3
        · right
          subst h3
          have h2 : 1 < Nat.card F := Finite.one_lt_card
          have h3' : Nat.card F ≠ 3 := fun h => hpF (by rw [h])
          have h2' : Nat.card F ≠ 2 := fun h => h32 ⟨rfl, h⟩
          omega
        · exact Or.inl h3
      exact localDeltaIn_eq_bot_psl_nonsplit hp hp4 hpF hs (by omega) hinj _ hE₁el hE₁c hH
  exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans hbot.le)

@[expose] def regimeA (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (m : ℕ) (q : TauCeti.PrimePower), idx.1 = .A m q ∧ ¬ (p ∣ q.card - 1 ∧ p ∣ m + 1) ∧
    ¬ (p = 3 ∧ q.card = 2)

theorem crossCharFamAt_A : CrossCharFamAt .A regimeA := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨m, q, hd, h1, h2⟩
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm1 : 1 ≤ m := hrange.1
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hfour : 3 ≤ m + 1 ∨ ∃ s : Finset (GaloisField q.p q.exponent), s.card = 4 := by
    by_cases h3 : 3 ≤ m + 1
    · exact Or.inl h3
    · right
      have h4 : 4 ≤ q.card := hrange.2 (by omega)
      have : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
        Finset (GaloisField q.p q.exponent))) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardF]; exact h4)
      exact ⟨s, hs⟩
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) hfour).2.1
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) hfour).commutator_eq_top
  have hinjP := CFSG.LieType.SeitzGeneration.conj_injective_of_simple_perfect hperf
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hpF : ¬ p ∣ Nat.card (GaloisField q.p q.exponent) := by
    rw [hcardF, TauCeti.PrimePower.card_def]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).mp (hp.dvd_of_dvd_pow hdvd))
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_psl (n := m + 1) (by omega) hp hp2 hpF (by rwa [hcardF])
      (by rwa [hcardF]) hinjP)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
