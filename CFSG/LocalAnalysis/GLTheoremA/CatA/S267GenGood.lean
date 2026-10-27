module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieExc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRest11
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE7
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodE8
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LiePL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem p_eq_two_of_card_eq_two_pow {q : TauCeti.PrimePower} {k : ℕ}
    (h : q.card = 2 ^ k) : q.p = 2 := by
  have hdvd : q.p ∣ 2 ^ k := by
    rw [← h, TauCeti.PrimePower.card_def]
    exact dvd_pow_self _ q.exponent_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hdvd)

private theorem characteristic_eq_two_of_ov2Idx {e : TauCeti.LieTypeIndex}
    (h : KD264Lie.ov2Idx e) : e.characteristic = 2 := by
  have key : ∀ q : TauCeti.PrimePower, q.card = 2 → q.p = 2 := fun q hq =>
    p_eq_two_of_card_eq_two_pow (k := 1) (by rw [hq, pow_one])
  rcases e with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q | q | q | q | q |
      m | m | m | _ <;>
    simp only [KD264Lie.ov2Idx, KD264Lie.fieldSize] at h
  all_goals first
    | simpa using key _ h
    | exact absurd (h ▸ dvd_pow_self 3 (by omega : 2 * m + 1 ≠ 0)) (by norm_num)
    | simp

theorem genGood_holds :
    GenGood := by
  intro p T _ _ d h hpT A hA hAcard
  obtain ⟨e⟩ := h.iso
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv T e.toEquiv
  by_cases hex : ∃ a ∈ A, a ≠ 1 ∧ GLAPLayer p (fixSubgroup a) ≠ ⊥
  · exact Or.inl hex
  refine Or.inr ?_
  push Not at hex
  have hDcard : Nat.card (A.map (MulAut.congr e).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hgood : ∀ b ∈ A.map (MulAut.congr e).toMonoidHom, b ≠ 1 →
      GLAPLayer p (fixSubgroup b) = ⊥ := by
    rintro _ ⟨a, ha, rfl⟩ hb
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hb (map_one _)
    change GLAPLayer p (fixSubgroup (MulAut.congr e a)) = ⊥
    rw [CFSG.glaPLayer_fixSubgroup_congr h.prime e a, hex a ha ha1, Subgroup.map_bot]
  have hpdvd : p ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
    rw [← Nat.card_congr e.toEquiv]
    exact hpT
  have hAcard' : p ^ 2 ≤ Nat.card (A.map (MulAut.congr e).toMonoidHom) := by
    rw [hDcard]
    exact hAcard
  have hExc : KD264Lie.KD264ExcNoGood p :=
    KD264Lie.kd264ExcNoGood_of_inputs KD264Lie.kd264OutCyc_holds (KD264Lie.kd264OuterIdx_of_families
        KD264Lie.lieOuterIdx_linear KD264Lie.lieOuterIdx_unitary KD264Lie.lieOuterIdx_classicalBCD
        KD264Lie.lieOuterIdx_triality KD264Lie.lieOuterIdx_excUntwisted
        KD264Lie.lieOuterIdx_excTwisted)
      (KD264Lie.kd264InnGood_of_exc KD264Lie.lieInnGood_E6 KD264Lie.lieInnGood_E7
        KD264Lie.lieInnGood_E8 KD264Lie.lieInnGood_twistedE6)
      KD264Lie.kd264TriInnGood_holds h.prime h.odd (KD264Lie.kd264PL_holds p h.prime h.odd)
  rcases hExc d h.ne hpdvd _ (hA.map _) hAcard' hgood with
    ⟨-, hov⟩ | ⟨-, ⟨q, hq, hq8⟩, -⟩ | ⟨-, hst⟩ | ⟨hlp, hcard⟩
  ·
    exact (h.charOdd (characteristic_eq_two_of_ov2Idx hov)).elim
  ·
    have hq2 : q.p = 2 := p_eq_two_of_card_eq_two_pow (k := 3) (by rw [hq8]; norm_num)
    exact (h.charOdd (by rcases hq with hq | hq <;> simp [hq, hq2])).elim
  ·
    exact (h.charOdd (by rcases hst with hst | hst <;> simp [hst])).elim
  ·
    exact ⟨hlp, hDcard.symm.trans hcard⟩

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
