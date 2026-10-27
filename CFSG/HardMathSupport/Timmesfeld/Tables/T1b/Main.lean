module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Easy
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Chain
import CFSG.Models.Transport

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem center_centerQuotient_eq_bot {L : Type} [Group L] (hq : CFSG.Open.IsQuasisimple L) :
    Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := by
  obtain ⟨hperf, hsimple⟩ := hq
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (L ⧸ Subgroup.center L)) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ x y : L, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center L := by
      intro x y
      have hx : (QuotientGroup.mk x : L ⧸ Subgroup.center L) ∈
          Subgroup.center (L ⧸ Subgroup.center L) := h ▸ Subgroup.mem_top _
      have := Subgroup.mem_center_iff.1 hx (QuotientGroup.mk y)
      rw [← QuotientGroup.eq_one_iff]
      change (QuotientGroup.mk x : L ⧸ Subgroup.center L) * QuotientGroup.mk y *
        (QuotientGroup.mk x)⁻¹ * (QuotientGroup.mk y)⁻¹ = 1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact this.symm
    have hle : commutator L ≤ Subgroup.center L := by
      rw [commutator_eq_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, y, rfl⟩
      simpa [commutatorElement_def] using hcomm x y
    rw [hperf, top_le_iff] at hle
    have : Subsingleton (L ⧸ Subgroup.center L) := by
      rw [hle]
      exact QuotientGroup.subsingleton_quotient_top
    exact (hsimple.toNontrivial).exists_pair_ne.elim fun a hab => hab.elim fun b hne =>
      hne (Subsingleton.elim a b)

theorem models_lieModel_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {t : StatedLieTag} {n p f : ℕ} (h : CFSG.Models.LieModel G t n p f) :
    CFSG.Models.LieModel H t n p f :=
  CFSG.Models.LieModel.of_mulEquiv e h

theorem exists_blueprintLieModel
    {L : Type} [Group L] (hLC : LieCentralQuotient L) :
    ∃ (t : StatedLieTag) (n r f : ℕ),
      CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n r f := by
  obtain ⟨idx, ⟨e⟩⟩ := hLC
  obtain ⟨t, n, r, f, hm⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.exists_lieModel idx
  exact ⟨t, n, r, f, blueprintLieModel_of_models (models_lieModel_of_mulEquiv e.symm hm)⟩

@[expose] def T1bLieHard : Prop :=
  ∀ (L : Type) [Group L] [Finite L], LieCentralQuotient L → CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsKGroup L → ∀ p : ℕ, p.Prime → p ≠ 2 →
      (CFSG.Open.pRank p (⊤ : Subgroup L) < 7 ∨ p ∣ Nat.card (Subgroup.center L)) →
      (∃ (t : StatedLieTag) (n r f : ℕ),
        CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n r f ∧ ¬ OutEasy p t n r f) →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ CFSG.Open.pRank p (⊤ : Subgroup L) + 1

theorem t1bLie_of_hard
    (hCov : LieCoverRank) (hHard : T1bLieHard) : T1bLie := by
  intro L _ _ hLC hq hK p hp hp2 hcond
  obtain ⟨t, n, r, f, hm⟩ := exists_blueprintLieModel hLC
  by_cases hE : OutEasy p t n r f
  swap
  · exact hHard L hLC hq hK p hp hp2 hcond ⟨t, n, r, f, hm, hE⟩
  have hcen := center_centerQuotient_eq_bot hq
  have hchain := outPChain_of_lieModel hp hp2 hm hE
  have h1 := pRank_mulAut_le_of_outPChain hp hcen hchain
  have h2 := pRank_mulAut_le_mulAut_centerQuotient hq.1 hp
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup L) := by
    by_cases hZ : p ∣ Nat.card (Subgroup.center L)
    · exact hCov L hq hLC p hp hp2 hZ
    · exact pRank_centerQuotient_le_of_not_dvd hp hZ
  omega

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
