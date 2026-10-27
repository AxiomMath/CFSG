module

public import CFSG.LieType.SeitzGeneration.HyperParabolic
public import CFSG.LieType.SeitzGeneration.HyperReducible
public import CFSG.LieType.SeitzGeneration.HyperQuotient
public import CFSG.LieType.SeitzGeneration.NonabLinear

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem hyperGen_top_of_mulEquiv (e : G ≃* G') {p : ℕ} {E : Subgroup G}
    (h : HyperGen p (⊤ : Subgroup G') (E.map e.toMonoidHom)) : HyperGen p (⊤ : Subgroup G) E := by
  set S : Set G := {k : G | k ∈ (⊤ : Subgroup G) ∧ ∃ F : Subgroup G, F ≤ E ∧ F.relIndex E = p ∧
    ∀ f ∈ F, f * k = k * f} with hS
  have hle : (⊤ : Subgroup G') ≤ (Subgroup.closure S).map e.toMonoidHom := by
    refine h.trans ((Subgroup.closure_le _).2 ?_)
    rintro k' ⟨-, F', hF'E, hF'r, hF'c⟩
    refine ⟨e.symm k', Subgroup.subset_closure ⟨Subgroup.mem_top _, F'.map e.symm.toMonoidHom, ?_,
      ?_, ?_⟩, by simp⟩
    · intro f hf
      obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.1 hf
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hF'E hf')
      simpa using hx
    · have := Subgroup.relIndex_map_map_of_injective (f := e.symm.toMonoidHom) F'
        (E.map e.toMonoidHom) e.symm.injective
      rw [Subgroup.map_map] at this
      have h2 : (e.symm.toMonoidHom.comp e.toMonoidHom) = MonoidHom.id G := by
        ext x; simp
      rw [h2, Subgroup.map_id] at this
      rw [this]
      exact hF'r
    · intro f hf
      obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.1 hf
      have := hF'c f' hf'
      apply e.injective
      simpa using this
  intro k _
  obtain ⟨s, hs, hsk⟩ := Subgroup.mem_map.1 (hle (Subgroup.mem_top (e k)))
  have : s = k := e.injective hsk
  exact this ▸ hs

end Transport

@[expose] def LinearReducible (d : TauCeti.ValidLieTypeIndex) (p : ℕ)
    (E₀ : Subgroup (Cat d)) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F)
    (e : Cat d ≃* ProjectiveSpecialLinearGroup (Fin n) F), (p : F) ≠ 0 ∧
    ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ x : SpecialLinearGroup (Fin n) F,
        QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) x ∈
          E₀.map e.toMonoidHom → ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W

@[expose] def LinearNonabIrr (d : TauCeti.ValidLieTypeIndex) (p : ℕ)
    (E₀ : Subgroup (Cat d)) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F)
    (e : Cat d ≃* ProjectiveSpecialLinearGroup (Fin n) F), (p : F) ≠ 0 ∧
    (∃ x y : SpecialLinearGroup (Fin n) F,
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) x ∈
        E₀.map e.toMonoidHom ∧
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) y ∈
        E₀.map e.toMonoidHom ∧ x * y ≠ y * x) ∧
    ∀ W : Submodule F (Fin n → F),
      (∀ x : SpecialLinearGroup (Fin n) F,
        QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) x ∈
          E₀.map e.toMonoidHom → ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) →
      W = ⊥ ∨ W = ⊤

theorem seitzHyperLie_linearReducible : SeitzHyperLie fun d p E₀ => LinearReducible d p E₀ := by
  intro d p hp hp2 hpd hlist E₀ hE hcard hred
  obtain ⟨n, F, _, _, e, hpF, W, hW0, hWt, hWE⟩ := hred
  have hn : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    exact hW0 (Submodule.eq_bot_of_subsingleton)
  have hE' : IsElemAbelian p (E₀.map e.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hcard' : Nat.card (E₀.map e.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  exact hyperGen_top_of_mulEquiv e
    (hyperGen_psl_of_reducible hp hpF (natCast_card_center_ne_zero hn) hE' hcard' hW0 hWt hWE)

theorem not_isCyclic_of_isElemAbelian_card {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) : ¬ IsCyclic E := by
  intro hcyc
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.1 hcyc
  have hgp : g ^ p = 1 := Subtype.ext (hE.2 g g.2)
  have hdvd : p ^ 3 ∣ p := hcard ▸ hg ▸ orderOf_dvd_of_pow_eq_one hgp
  have hle := Nat.le_of_dvd hp.pos hdvd
  have h2 := hp.two_le
  nlinarith [pow_pos hp.pos 2, Nat.pow_le_pow_left h2 2]

theorem linearReducible_or_nonabIrr {d : TauCeti.ValidLieTypeIndex} (hd : IsLinearIndex d.1)
    {p : ℕ} (hp : p.Prime) (hpd : p ≠ d.1.characteristic) {E₀ : Subgroup (Cat d)}
    (hE : IsElemAbelian p E₀) (hcard : Nat.card E₀ = p ^ 3) :
    LinearReducible d p E₀ ∨ LinearNonabIrr d p E₀ := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨m, q, hdq⟩ := hd
  simp only at hdq
  subst hdq
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpd' : p ≠ q.p := by simpa using hpd
  have hpF : (p : GaloisField q.p q.exponent) ≠ 0 := by
    intro h0
    have hq : CharP (GaloisField q.p q.exponent) q.p := inferInstance
    have hdvd : q.p ∣ p := (CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p p).1 h0
    exact hpd' ((Nat.prime_dvd_prime_iff_eq q.prime_p hp).1 hdvd).symm
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv
  have hn : NeZero (m + 1) := ⟨by omega⟩
  have hE' : IsElemAbelian p (E₀.map e.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hcard' : Nat.card (E₀.map e.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  have hnc : ¬ IsCyclic (E₀.map e.toMonoidHom) := not_isCyclic_of_isElemAbelian_card hp hE' hcard'
  let K := GaloisField q.p q.exponent
  by_cases hred : ∃ W : Submodule K (Fin (m + 1) → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ x : SpecialLinearGroup (Fin (m + 1)) K,
        QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (m + 1)) K)) x ∈
          E₀.map e.toMonoidHom → ∀ w ∈ W, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K).mulVec w ∈ W
  · obtain ⟨W, hW0, hWt, hWE⟩ := hred
    exact Or.inl ⟨m + 1, GaloisField q.p q.exponent, inferInstance, inferInstance, e, hpF, W, hW0,
      hWt, hWE⟩
  · refine Or.inr ⟨m + 1, GaloisField q.p q.exponent, inferInstance, inferInstance, e, hpF, ?_, ?_⟩
    · by_contra hcomm
      push Not at hcomm
      exact hred (exists_stable_of_commutative hnc hcomm)
    · intro W hW
      by_contra h
      push Not at h
      exact hred ⟨W, h.1, h.2, hW⟩

theorem SeitzHyperLie.of_cover_full {S S₁ S₂ : ∀ d : TauCeti.ValidLieTypeIndex, ℕ →
    Subgroup (Cat d) → Prop}
    (hcov : ∀ d p, p.Prime → p ≠ 2 → p ≠ d.1.characteristic → ∀ E : Subgroup (Cat d),
      IsElemAbelian p E → Nat.card E = p ^ 3 → S d p E → S₁ d p E ∨ S₂ d p E)
    (h₁ : SeitzHyperLie S₁) (h₂ : SeitzHyperLie S₂) : SeitzHyperLie S := by
  intro d p hp hp2 hpd hl E hE hc hs
  rcases hcov d p hp hp2 hpd E hE hc hs with h | h
  · exact h₁ d p hp hp2 hpd hl E hE hc h
  · exact h₂ d p hp hp2 hpd hl E hE hc h

@[expose] def SeitzHyperLieLinearIrr : Prop := SeitzHyperLie fun d p E₀ => LinearNonabIrr d p E₀

theorem seitzHyperLieLinear_of_irr (h : SeitzHyperLieLinearIrr) : SeitzHyperLieLinear :=
  SeitzHyperLie.of_cover_full (S₁ := fun d p E₀ => LinearReducible d p E₀)
    (S₂ := fun d p E₀ => LinearNonabIrr d p E₀)
    (fun _ _ hp _ hpd _ hE hc hs => linearReducible_or_nonabIrr hs hp hpd hE hc)
    seitzHyperLie_linearReducible h

end CFSG.LieType.SeitzGeneration
