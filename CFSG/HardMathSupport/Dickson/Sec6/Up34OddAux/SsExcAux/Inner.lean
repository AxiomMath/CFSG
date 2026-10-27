module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.InnerUnip
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

section Inner


theorem ssexc_char_ge_five {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup τ L 3)
    (h2 : (2 : L) ≠ 0) :
    ∃ r e : ℕ, r.Prime ∧ CharP L r ∧ 5 ≤ r ∧ 0 < e ∧ S.D.q = r ^ e := by
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  refine ⟨r, e, hr, hchar, ?_, he, hq⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact h2 (by simpa using CharP.cast_eq_zero L 2)
  have hr3 : r ≠ 3 := by
    rintro rfl
    exact S.hpq (hq ▸ dvd_pow_self 3 he.ne')
  have hr4 : r ≠ 4 := by
    rintro rfl
    exact absurd hr (by norm_num)
  have := hr.two_le
  omega

theorem ssexc_not_L34_inner {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup τ L 3)
    (h2 : (2 : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .inner) :
    ¬ IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  intro hL34
  obtain ⟨r, e, hr, hchar, hr5, he, hq⟩ := ssexc_char_ge_five S h2
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  have hinner := twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hk
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have h4q : 4 ≤ S.D.q := S.hq.resolve_left (by norm_num)
  have hQ' : 4 ≤ r ^ (e * s) := by
    rw [pow_mul, ← hq]
    exact h4q.trans (Nat.le_self_pow hs0.ne' _)
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ' (Nat.mul_pos he hs0) hQ'
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    refine ⟨Units.map (fixSubfield σ).subtype.toMonoidHom t, fun h => ht ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa using congrArg (fun x : Lˣ => (x : L)) h
  have hperfC := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ)
    (χ := rootCharHom a) ht i
  obtain ⟨f, hf1, hker, hf2⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  have hR : rationalComponent S.ρ S.Γ (rootCharHom a) i = f.range :=
    le_antisymm hf1 (hf2 (Subgroup.isPerfect_iff.1 hperfC))
  rw [hR] at hL34
  obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := L) r (e * s) (Nat.mul_pos he hs0)
  have hset : (fixSubfield σ : Set L) = {c : L | c ^ (r ^ (e * s)) = c} := by
    ext c
    show c ∈ fixSubfield σ ↔ _
    rw [mem_fixSubfield, hσ']
    rfl
  haveI hfinK : Finite (fixSubfield σ) := by
    have h1 : (fixSubfield σ : Set L).Finite := by rw [hset]; exact hfinset
    exact h1.to_subtype
  have hKcard : Nat.card (fixSubfield σ) = r ^ (e * s) := by
    have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set L).ncard :=
      Nat.card_coe_set_eq (fixSubfield σ : Set L)
    rw [h1, hset, hcardset]
  haveI : CharP (fixSubfield σ) r := inferInstance
  have hQ5 : 5 ≤ Nat.card (fixSubfield σ) := by
    rw [hKcard]
    exact hr5.trans (Nat.le_self_pow (Nat.mul_pos he hs0).ne' r)
  have hL34C : IsLThreeFour (↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) ⧸
      Subgroup.center ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i)) := by
    refine isLThreeFour_of_surjective_central hperfC f.rangeRestrict
      f.rangeRestrict_surjective ?_ hL34
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hbound : ∀ {V : Subgroup ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i)},
      IsPGroup r V → Nat.card V ≤ 7 := fun {V} hV =>
    up34_card_le_seven hperfC hL34C hr hr5 hV
  by_cases hA : ∃ γ ∈ componentRoots (rootCharHom a) i, ∃ δ ∈ componentRoots (rootCharHom a) i,
      δ ≠ γ ∧ δ ≠ -γ
  · obtain ⟨γ, hγ, δ, hδ, h1, h2'⟩ := hA
    obtain ⟨γ', hγ', δ', hδ', hγp, hδp, hne⟩ := ssexc_exists_two_pos i hγ hδ h1 h2'
    have hcard := ssexc_card_posPart_two (K := fixSubfield σ) hγ' hδ' hγp hδp hne
    have := hbound (ssexc_isPGroup_posPart (K := fixSubfield σ) (r := r) i)
    nlinarith
  · push Not at hA
    obtain ⟨γ, hγ, hγp⟩ := ssexc_exists_pos_root (χ := rootCharHom a) i
    by_cases hQ8 : 8 ≤ Nat.card (fixSubfield σ)
    · have hcard := ssexc_card_posPart_one (K := fixSubfield σ) hγ hγp
      have := hbound (ssexc_isPGroup_posPart (K := fixSubfield σ) (r := r) i)
      omega
    · push Not at hQ8
      have hrank : ∀ δ ∈ componentRoots (rootCharHom a) i, δ = γ ∨ δ = -γ := fun δ hδ => by
        by_cases hδγ : δ = γ
        · exact Or.inl hδγ
        · exact Or.inr (hA γ hγ δ hδ hδγ)
      have hC4 := ssexc_card_le_of_rank_one (K := fixSubfield σ) hγ hrank
      have h20160 : Nat.card (↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) ⧸
          Subgroup.center ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i)) = 20160 :=
        card_eq_of_isLThreeFour hL34C
      have hqle : Nat.card (↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) ⧸
          Subgroup.center ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i)) ≤
          Nat.card ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
      have hQ7 : Nat.card (fixSubfield σ) ≤ 7 := by omega
      have : Nat.card (fixSubfield σ) ^ 4 ≤ 7 ^ 4 := Nat.pow_le_pow_left hQ7 4
      omega

end Inner

end CFSG.HardMathSupport.Dickson.Sec6
