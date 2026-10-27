module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineOne
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ChainNine
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFourOneConj
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFourOneAut
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_almostClauseTwoCore_of_threeOnePlusFour {N Q : Subgroup G} {p : ℕ}
    (P : Sylow p G) (hPN : (P : Subgroup G) ≤ N) (h : AlmostClauseTwoCore N P p)
    (hQN : Q ≤ N) (hcard : Nat.card ↥Q = 3 ^ 5) (hexp : ∀ x : ↥Q, x ^ 3 = 1)
    (hZ : Nat.card (Subgroup.center ↥Q) = 3) (hcomm : commutator ↥Q ≤ Subgroup.center ↥Q) :
    False := by
  classical
  obtain ⟨hp5, hsolv, P₀, hP₀P, hP₀card, hwc, ⟨hp, m, hm2, hL⟩, -, -, hF1, hF2⟩ := h
  haveI : Fact p.Prime := hp
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card hcard
  obtain ⟨g, -, hQ'norm⟩ :=
    exists_conj_le_normalizer_of_weaklyClosed (p := p) (N := N) (P₀ := P₀) (Q := Q)
      hp5 P hPN hsolv hP₀P hP₀card hwc (hF1 3 Nat.prime_three (by norm_num)) hQN hQ3
  let f : G →* G := (MulAut.conj g).toMonoidHom
  let e : ↥Q ≃* ↥(Q.map f) := Subgroup.equivMapOfInjective Q f (MulAut.conj g).injective
  have hcard' : Nat.card ↥(Q.map f) = 3 ^ 5 := by
    rw [← hcard]
    exact (Nat.card_congr e.toEquiv).symm
  have hexp' : ∀ x : ↥(Q.map f), x ^ 3 = 1 := by
    intro x
    calc x ^ 3 = (e (e.symm x)) ^ 3 := by rw [e.apply_symm_apply]
      _ = e ((e.symm x) ^ 3) := (map_pow e _ 3).symm
      _ = e 1 := by rw [hexp]
      _ = 1 := map_one e
  have hZ' : Nat.card (Subgroup.center ↥(Q.map f)) = 3 := by
    have hmap : (Subgroup.center ↥Q).map (e : ↥Q →* ↥(Q.map f)) =
        Subgroup.center ↥(Q.map f) := Subgroup.map_center_eq e
    rw [← hmap, Subgroup.card_map_of_injective e.injective, hZ]
  have hcomm' : commutator ↥(Q.map f) ≤ Subgroup.center ↥(Q.map f) := by
    have hmap : (commutator ↥Q).map (e : ↥Q →* ↥(Q.map f)) =
        commutator ↥(Q.map f) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
      rfl
    calc commutator ↥(Q.map f) = (commutator ↥Q).map (e : ↥Q →* ↥(Q.map f)) := hmap.symm
      _ ≤ (Subgroup.center ↥Q).map (e : ↥Q →* ↥(Q.map f)) := Subgroup.map_mono hcomm
      _ = Subgroup.center ↥(Q.map f) := Subgroup.map_center_eq e
  exact false_of_threeOnePlusFour_le_normalizer (p := p) (m := m) hp5 (by omega)
    hP₀card hL (hF2 3 Nat.prime_three (by norm_num)) hQ'norm hcard' hexp' hZ' hcomm'

theorem fourteenFourOneCaseOneAt_of {M : Subgroup G} (h142 : FourteenTwoCaseOneAt M)
    (hU : NineNineOneAt M) : FourteenFourOneCaseOneAt M := by
  intro H E Q J h hA r hr
  have hr3 : r ≠ 3 := fun h3 => h.hypCGen.not_mem_sigmaSet (h3 ▸ hr)
  have hrp : r.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime r hr.1
  haveI : Fact r.Prime := ⟨hrp⟩
  obtain ⟨P, hPM, -, hcase⟩ := h.cstar.almost M h.maxLocal r hr
  rcases hcase with hΓ | hclause2 | hclause3
  · haveI : IsSimpleGroup G := h.cstar.simple
    have hMtop : M ≠ ⊤ :=
      CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top h.cstar.nonab M h.maxLocal.1
    have hr2 : 2 ≤ CFSG.Open.pRank r M := hr.2
    have hdvd : r ∣ Nat.card G :=
      CFSG.RankThreeCoreUniqueness.Helpers.prime_dvd_card_of_pRank_pos r M (by omega)
    have hP : (P : Subgroup G) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P hdvd
    exact
      (CFSG.LocalAnalysis.RankThreeUC.gamma_one_le_iff_isStronglyPEmbedded hPM hMtop hP).mp hΓ
  · obtain ⟨hQcard, hQexp, hQcomm, hQZmap⟩ := (h142 H E Q J h hA).1
    have hQexp' : ∀ x : ↥Q, x ^ 3 = 1 := fun x => by
      apply Subtype.ext
      change (x : G) ^ 3 = 1
      exact hQexp (x : G) x.2
    have hQZ' : Nat.card (Subgroup.center ↥Q) = 3 :=
      (Subgroup.card_map_of_injective (f := Q.subtype) Q.subtype_injective).symm.trans hQZmap
    have hQcomm' : commutator ↥Q ≤ Subgroup.center ↥Q := by
      have heq : (commutator ↥Q).map Q.subtype = (Subgroup.center ↥Q).map Q.subtype := by
        rw [Subgroup.map_subtype_commutator, hQcomm]
      exact le_of_eq (Subgroup.map_injective Q.subtype_injective heq)
    exact (false_of_almostClauseTwoCore_of_threeOnePlusFour (N := M) (Q := Q) (p := r)
      P hPM hclause2 (h.Q_le_M hU) hQcard hQexp' hQZ' hQcomm').elim
  · exact absurd hclause3.1 hr3

theorem fourteenFourOneCaseOneGen_of (h142 : FourteenTwoCaseOneGen)
    (h1211 : TwelveElevenGen) (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen) :
    FourteenFourOneCaseOneGen := by
  intro G _ _ M
  exact fourteenFourOneCaseOneAt_of (h142 G M)
    (nineNineOneAt_of_twelveEleven (G := G) h991 h1211)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
