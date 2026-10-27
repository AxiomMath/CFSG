module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentRot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173SplitBorelTits
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173M

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.GroupTheory.WeirSylow CFSG.Open
  CFSG.RankThree.PartOne.K159 CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
  CFSG.LocalAnalysis.GLTheoremA.T173X

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem card_le_pow_pred_of_normalizes (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian p E)
    {T : Subgroup ↥(orthDerived Q)} (hT0 : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set ↥(orthDerived Q))) : Nat.card E ≤ p ^ (l - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  have hreg : RegOn Q ⊤ := fun u _ h =>
    hQ.1 u fun w => by simpa [QuadraticMap.polarBilin_apply_apply] using h w Submodule.mem_top
  obtain ⟨r, U, hU⟩ := exists_planeDecomp hQ hp hp2 hpq hE ⊤ hreg fun _ _ _ _ => Submodule.mem_top
  have hle : Nat.card E ≤ p ^ r := hU.card_le_pow hE hp
  have hrl : r ≤ l := by
    have h1 := hU.toIsPlaneSystem.finrank_biSup Finset.univ
    have h2 := Submodule.finrank_le (⨆ j ∈ (Finset.univ : Finset (Fin r)), U j)
    rw [h1, Finset.card_univ, Fintype.card_fin, hdim] at h2
    omega
  have hpg : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpg
  have hkl : l - 1 < k := (Nat.pow_lt_pow_iff_right hp.one_lt).1 (hk ▸ hlt)
  have hkr : k ≤ r := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hk ▸ hle)
  have hrl' : r = l := by omega
  subst hrl'
  have hcard : Nat.card E = p ^ r := by rw [hk]; congr 1; omega
  obtain ⟨e, he⟩ := hU.exists_planeFrame hE hp hcard
  have htop : (⨆ j, U j : Submodule F V) = ⊤ := by
    have e : (⨆ j ∈ (Finset.univ : Finset (Fin r)), U j : Submodule F V) = ⨆ j, U j := by simp
    rw [← e]
    apply Submodule.eq_top_of_finrank_eq
    rw [hU.toIsPlaneSystem.finrank_biSup, Finset.card_univ, Fintype.card_fin, hdim]
  obtain ⟨W, hW0, hWTS, hWinv⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T173S.exists_invariant_totallySingular_of_normalizes hQ hdim hl hT2 hT0 hET
  refine hW0 (eq_bot_of_separated he hp hp2 htop le_rfl ?_ hWTS hWinv)
  intro a b hab
  refine ⟨e b, he.mem b, ?_⟩
  have hbU : ∃ x ∈ U b, x ≠ 0 := by
    obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U b) (he.finrank_eq b)
    exact ⟨v, hv, hv0⟩
  constructor
  · intro _ hall
    obtain ⟨x, hx, hx0⟩ := hbU
    exact hx0 (he.eq_zero_of_apply_eq b x hx (hall x hx))
  · intro _ x hx
    exact he.apply_of_perp b x (mem_polarPerp_iff.2 fun y hy => he.perp b a (Ne.symm hab) y hy x hx)

theorem exists_twoLocal_witness (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (htype : IsPlusType Q ↔ Even l) :
    ∃ A : Subgroup ↥(orthDerived Q), IsElemAbelian p A ∧ Nat.card A = p ^ (l - 1) ∧
      ∃ T : Subgroup ↥(orthDerived Q), T ≠ ⊥ ∧ IsPGroup 2 T ∧
        A ≤ Subgroup.normalizer (T : Set ↥(orthDerived Q)) := by
  obtain ⟨U, ρ, i, j, A, hM, hT⟩ := exists_isMixedFrame hQ hdim hl hp hp2 hpq htype
  exact ⟨A, hM.isElemAbelian, hM.card_eq hp, hT⟩

theorem glaTwoLocalRank_eq (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (htype : IsPlusType Q ↔ Even l) :
    GLATwoLocalRank p ↥(orthDerived Q) = l - 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A₀, hA₀e, hA₀c, T, hT0, hT2, hA₀T⟩ := exists_twoLocal_witness hQ hdim hl hp hp2 hpq htype
  have hle : ∀ H : Subgroup ↥(orthDerived Q), IsTwoLocal H → CFSG.Open.pRank p H ≤ l - 1 := by
    rintro H ⟨P, hP0, hP2, rfl⟩
    refine csSup_le ⟨0, ⊥, bot_le, ⟨inferInstance, fun x hx => ?_⟩, by simp⟩ ?_
    · rw [Subgroup.mem_bot.1 hx]
      exact one_pow p
    · rintro k ⟨E, hEH, hE, hk⟩
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1
        (hk ▸ card_le_pow_pred_of_normalizes hQ hdim hl hp hp2 hpq hE hP0 hP2 hEH)
  have hloc : IsTwoLocal (Subgroup.normalizer (T : Set ↥(orthDerived Q))) := ⟨T, hT0, hT2, rfl⟩
  have hge : l - 1 ≤ CFSG.Open.pRank p (Subgroup.normalizer (T : Set ↥(orthDerived Q))) := by
    refine le_csSup ⟨l - 1, ?_⟩ ⟨A₀, hA₀T, hA₀e, hA₀c⟩
    rintro k ⟨E, hEH, hE, hk⟩
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1
      (hk ▸ card_le_pow_pred_of_normalizes hQ hdim hl hp hp2 hpq hE hT0 hT2 hEH)
  have hbdd : BddAbove {k | ∃ H : Subgroup ↥(orthDerived Q), IsTwoLocal H ∧ CFSG.Open.pRank p H = k} :=
    ⟨l - 1, fun k ⟨H, hH, hk⟩ => hk ▸ hle H hH⟩
  show twoLocalPrimeRank p ↥(orthDerived Q) = l - 1
  refine le_antisymm (csSup_le ⟨_, _, hloc, rfl⟩ fun k ⟨H, hH, hk⟩ => hk ▸ hle H hH) ?_
  exact le_csSup hbdd ⟨_, hloc, le_antisymm (hle _ hloc) hge⟩

theorem glaIsBmax_iff (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (htype : IsPlusType Q ↔ Even l) {A : Subgroup ↥(orthDerived Q)} :
    GLAIsBmax p A ↔ IsElemAbelian p A ∧ Nat.card A = p ^ (l - 1) ∧
      ∃ T : Subgroup ↥(orthDerived Q), T ≠ ⊥ ∧ IsPGroup 2 T ∧
        A ≤ Subgroup.normalizer (T : Set ↥(orthDerived Q)) := by
  have hrank := glaTwoLocalRank_eq hQ hdim hl hp hp2 hpq htype
  constructor
  · rintro ⟨hAe, hcard, hT⟩
    exact ⟨hAe, by rw [hcard, hrank], hT⟩
  · rintro ⟨hAe, hcard, hT⟩
    exact ⟨hAe, by rw [hcard, hrank], hT⟩

end CFSG.LocalAnalysis.GLTheoremA.T173M

end
