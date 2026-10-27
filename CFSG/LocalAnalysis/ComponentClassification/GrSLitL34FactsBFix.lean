module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsReal

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem lift_of_betaRep {β : E ≃* E} {t i : ℕ}
    (hβ : ∀ w, (nf l t 0 0)⁻¹ * β (l (cv w)) * nf l t 0 0 = l (cv (substWord (aut i) w))) :
    ∃ β' : E ≃* E, ∀ w, β' (l (cv w)) = l (cv (substWord (aut i) w)) :=
  ⟨β.trans (MulAut.conj (nf l t 0 0)⁻¹), fun w => by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv, hβ]⟩

theorem repPerm_mem_S {i : ℕ}
    (hi : i < 36) (hS : repInS.contains i = true) : repPerm i ∈ S := by
  have h := realBParts.repS
  simp only [repSOK, List.all_eq_true] at h
  exact mem_of_found_enum enumerates_S (tabRep_repTab hi) (h i (by simpa using hS))

theorem c6_spec {κ : ZMod 4 × ZMod 4} (hκ : κ ∈ kGens) {i : ℕ}
    (hi : i < 36) (hiS : repInS.contains i = false) (hl : liftsK κ i = true) {t : ℕ}
    (ht : t < 64) (hf : fixBM κ t i = true) {w : MElt} (hw : w ∈ allM)
    (hbw : eqKM κ (betaYM t i w) w = true)
    (hww : ∀ x ∈ allM, eqKM κ (betaYM t i (betaYM t i x)) (mulM (mulM w x) (invM w)) = true) :
    trichM κ (allM.filter (isAhM κ)) t i w = true := by
  have h := realBParts.c6
  simp only [c6OK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.mem_range] at h
  rcases h.2 κ (kGensC_eq ▸ hκ) i hi with (h1 | h1) | h1
  · rw [hiS] at h1
    exact Bool.noConfusion h1
  · rw [hl] at h1
    exact Bool.noConfusion h1
  · rcases h1 t ht with h2 | h2
    · rw [hf] at h2
      exact Bool.noConfusion h2
    · rcases h2 w hw with (h3 | h3) | h3
      · rw [hbw] at h3
        exact Bool.noConfusion h3
      · have : (allM.all fun x => eqKM κ (betaYM t i (betaYM t i x)) (mulM (mulM w x) (invM w))) =
            true := List.all_eq_true.2 hww
        rw [this] at h3
        exact Bool.noConfusion h3
      · exact h3


theorem bFixExponent : L34BFixExponentFact := by
  intro E _ q l h hcyc h4 y hyR hyN β hβ hB
  obtain ⟨κ, hκm, hκ⟩ := exists_kappa h hcyc h4
  obtain ⟨i, hi, t, ht, rfl, hβr⟩ := exists_betaRep h hyR hyN hβ
  obtain ⟨β', hβ'⟩ := lift_of_betaRep hβr
  exact pow4M_spec hi (c2_spec hκm hi (liftsK_of h hκ hi hβ') ht (fixBM_of h hκ ht hi hβr hB))

theorem u_nfM (h : IsQSetting q l) {β : E ≃* E} {t i : ℕ} (ht : t < 64)
    (hi : i < 36)
    (hβ : ∀ w, (nf l t 0 0)⁻¹ * β (l (cv w)) * nf l t 0 0 = l (cv (substWord (aut i) w)))
    {v w : MElt} (hv : v.1 < 64) (hw : w.1 < 64) :
    nfM l v * β (nfM l v) * nfM l w = nfM l (mulM (mulM v (betaYM t i v)) w) := by
  rw [betaY_nfM h ht hi hβ hv, nfM_mul h hv (betaYM_lt ht hi hv),
    nfM_mul h (mulM_lt hv (betaYM_lt ht hi hv)) hw]

theorem bFixOuterSquare : L34BFixOuterSquareFact := by
  intro E _ q l h hcyc h4 y hyR hyS hyN β hβ hB w hwT hβw hww
  obtain ⟨κ, hκm, hκ⟩ := exists_kappa h hcyc h4
  obtain ⟨i, hi, t, ht, rfl, hβr⟩ := exists_betaRep h hyR hyN hβ
  obtain ⟨β', hβ'⟩ := lift_of_betaRep hβr
  have hiS : repInS.contains i = false := by
    cases hc : repInS.contains i
    · rfl
    · exact absurd (S.mul_mem (wordPerm_mem _) (repPerm_mem_S hi hc)) hyS
  obtain ⟨kw, hkw, a, b, rfl⟩ := exists_nf h hwT
  have hw0 : (kw, a, b).1 < 64 := hkw
  have hbw : eqKM κ (betaYM t i (kw, a, b)) (kw, a, b) = true := by
    rw [eqKM_iff h hκ (betaYM_lt ht hi hw0) hw0, ← betaY_nfM h ht hi hβr hw0]
    exact hβw
  have hwwM : ∀ x ∈ allM, eqKM κ (betaYM t i (betaYM t i x))
      (mulM (mulM (kw, a, b) x) (invM (kw, a, b))) = true := by
    intro x hx
    have hx64 := lt_of_mem_allM hx
    rw [eqKM_iff h hκ (betaYM_lt ht hi (betaYM_lt ht hi hx64))
      (mulM_lt (mulM_lt hw0 hx64) (invM_lt hw0)), ← betaY_nfM h ht hi hβr (betaYM_lt ht hi hx64),
      ← betaY_nfM h ht hi hβr hx64, hww, ← nfM_mul h (mulM_lt hw0 hx64) (invM_lt hw0),
      ← nfM_mul h hw0 hx64, ← nfM_inv h hw0]
  have htr := c6_spec hκm hi hiS (liftsK_of h hκ hi hβ') ht (fixBM_of h hκ ht hi hβr hB)
    (mem_allM hw0) hbw hwwM
  simp only [trichM, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_filter,
    Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at htr
  rcases htr with (⟨v, ⟨hvM, hvA⟩, hv1⟩ | ⟨v, ⟨hvM, hvA⟩, hv2, hv3⟩) | hall
  · have hv := lt_of_mem_allM hvM
    refine Or.inl ⟨nfM l v, nfM_mem_aHat h hκ hv hvA, ?_⟩
    have hu := mulM_lt (mulM_lt hv (betaYM_lt ht hi hv)) hw0
    rw [show nf l kw a b = nfM l (kw, a, b) from rfl, u_nfM h ht hi hβr hv hw0, ← nfM_one]
    exact (eqKM_iff h hκ hu (by decide)).1 hv1
  · have hv := lt_of_mem_allM hvM
    refine Or.inr (Or.inl ⟨nfM l v, nfM_mem_aHat h hκ hv hvA, ?_, ?_⟩)
    · have hu := mulM_lt (mulM_lt hv (betaYM_lt ht hi hv)) hw0
      rw [show nf l kw a b = nfM l (kw, a, b) from rfl, u_nfM h ht hi hβr hv hw0, sq,
        nfM_mul h hu hu, MonoidHom.mem_ker, q_nfM h (mulM_lt hu hu), hv2, wordPerm_tg_zero']
    · have hu := mulM_lt (mulM_lt hv (betaYM_lt ht hi hv)) hw0
      rw [show nf l kw a b = nfM l (kw, a, b) from rfl, u_nfM h ht hi hβr hv hw0, sq,
        nfM_mul h hu hu, ← nfM_one]
      intro he
      rw [← eqKM_iff h hκ (mulM_lt hu hu) (by decide)] at he
      rw [he] at hv3
      exact Bool.noConfusion hv3
  · refine Or.inr (Or.inr fun v hv => ?_)
    obtain ⟨kv, hkv, av, bv, rfl⟩ := exists_nf h hv.1
    have hv0 : (kv, av, bv).1 < 64 := hkv
    obtain ⟨⟨hq0, hsq⟩, hne⟩ := hall (kv, av, bv) ⟨mem_allM hv0, isAhM_of_mem h hκ hv0 hv⟩
    have hu := mulM_lt (mulM_lt hv0 (betaYM_lt ht hi hv0)) hw0
    rw [show nf l kv av bv = nfM l (kv, av, bv) from rfl,
      show nf l kw a b = nfM l (kw, a, b) from rfl, u_nfM h ht hi hβr hv0 hw0]
    refine ⟨?_, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, q_nfM h hu, hq0, wordPerm_tg_zero']
    · rw [sq, nfM_mul h hu hu, ← nfM_one]
      exact (eqKM_iff h hκ (mulM_lt hu hu) (by decide)).1 hsq
    · intro he
      rw [← nfM_one, ← eqKM_iff h hκ hu (by decide)] at he
      rw [he] at hne
      exact Bool.noConfusion hne

end CFSG.ComponentClassification.GrSLit.L34Facts.Real

namespace CFSG.ComponentClassification.GrSLit

theorem l34BFixExponentFact :
    L34BFixExponentFact :=
  L34Facts.Real.bFixExponent

theorem l34BFixOuterSquareFact :
    L34BFixOuterSquareFact :=
  L34Facts.Real.bFixOuterSquare

end CFSG.ComponentClassification.GrSLit
