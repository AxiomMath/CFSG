module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses.SpinPlus
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses.SpinMinus
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubPrime
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCent

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.ToralCensus CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

theorem exists_orderOf_map_rankOne {K Y : Type*} [Group K] [Group Y] {D : UniversalRootDatum K}
    {nW : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M q : ℕ}
    (h : BorelQuotient D nW H π M) (hrank : ∀ i, RankOneNode D i q) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ q ^ 2 - 1) (i : Fin D.rank) :
    ∃ x ∈ (rankOne D.rootGroup i).map π, orderOf x = p := by
  obtain ⟨x, hx, hxp, hxc⟩ := (hrank i).prime p hp hp5 hpq
  refine ⟨π x, ⟨x, hx, rfl⟩, ?_⟩
  have hπx : π x ≠ 1 := fun h' => hxc (h.ker_central x h')
  have hdvd : orderOf (π x) ∣ p :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, ← hxp, pow_orderOf_eq_one, map_one])
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · exact absurd (orderOf_eq_one_iff.1 h1) hπx
  · exact h1

theorem centralizerEscapes_of_hubWitnesses_of_rankOneNode {K Y : Type} [Group K] [Group Y]
    [Finite K] [Finite Y] {D : UniversalRootDatum K} {nW : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} {π : K →* Y} {M q : ℕ} (h : BorelQuotient D nW H π M)
    (hD : D.divisible = ∅) (hq4 : 4 ≤ q) (hrank : ∀ i, RankOneNode D i q)
    (hW : HubWitnesses D) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ q ^ 2 - 1) :
    CentralizerEscapes p Y :=
  centralizerEscapes_of_hubWitnesses h hD hq4 hrank hp (by omega)
    (exists_orderOf_map_rankOne h hrank hp hp5 hpq) hW

theorem centralizerEscapes_of_isLieOfTorus_d {X : Type} [Group X] [Finite X] {p : ℕ}
    (hX : IsLieOfTorus IdxD p X) (hp : p.Prime) (hp5 : 5 ≤ p) : CentralizerEscapes p X := by
  obtain ⟨⟨d, hv⟩, hd, ht, ⟨e⟩⟩ := hX
  cases d with
  | D r q =>
    change q.p = 2 at hd
    have hnt : q.card ≠ 2 ∧ p ∣ q.card - 1 := by simpa [IndexTorusFree] using ht
    have hq4 : 4 ≤ q.card := by
      rcases card_eq_two_or_four_le_of_p_eq_two hd with h2 | h4
      · exact absurd h2 hnt.1
      · exact h4
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e'⟩⟩ := h
    have hcardq : Nat.card F = q.card := by
      rw [hcard, TauCeti.PrimePower.card_def, hd]
    have := Fintype.ofFinite F
    have : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := q.exponent) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
    have hn3 : 3 ≤ r := Nat.le_of_succ_le hn
    have : NeZero r := ⟨by omega⟩
    have : Finite (spinGroup (quadPlus r F)) :=
      finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := r) (K := F))
    exact centralizerEscapes_of_hubWitnesses_of_rankOneNode (borelQuotient_spinPlus hn3 e') rfl
      (by rw [hcardq]; exact hq4) (rankOneNode_spinPlus hn3) (hubWitnesses_spinPlus hn) hp hp5
      (by rw [hcardq]; exact hnt.2.trans (sub_one_dvd_sq_sub_one _))
  | _ => exact hd.elim

theorem centralizerEscapes_of_isLieOfTorus_twistedD {X : Type} [Group X] [Finite X] {p : ℕ}
    (hX : IsLieOfTorus IdxTwistedD p X) (hp : p.Prime) (hp5 : 5 ≤ p) :
    CentralizerEscapes p X := by
  obtain ⟨⟨d, hv⟩, hd, ht, ⟨e⟩⟩ := hX
  cases d with
  | twistedD r q =>
    change q.p = 2 at hd
    have hnt : q.card ≠ 2 ∧ p ∣ q.card ^ 2 - 1 := by simpa [IndexTorusFree] using ht
    have hq4 : 4 ≤ q.card := by
      rcases card_eq_two_or_four_le_of_p_eq_two hd with h2 | h4
      · exact absurd h2 hnt.1
      · exact h4
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e'⟩⟩ := h
    have hcardq : Nat.card F = q.card := by
      rw [hcard, TauCeti.PrimePower.card_def, hd]
    have := Fintype.ofFinite F
    have : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := q.exponent) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
    have : Finite (spinGroup (quadMinus r F b c)) :=
      finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
    refine centralizerEscapes_of_hubWitnesses_of_rankOneNode (q := Nat.card F)
      (borelQuotient_spinMinus hirr hn e') rfl (by rw [hcardq]; exact hq4) (fun i => ?_) (hubWitnesses_spinMinus hirr hn) hp hp5
      (by rw [hcardq]; exact hnt.2)
    by_cases hk : i.val + 1 < r - 1
    · exact rankOneNode_spinMinus_long hirr hk
    · exact rankOneNode_spinMinus_short hirr hk
  | _ => exact hd.elim

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses
