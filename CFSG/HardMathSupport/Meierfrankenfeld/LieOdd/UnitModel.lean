module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Steinberg.CentralExt.SUThreeField
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Assembly.LowTwoRank TauCeti

theorem card_center_dvd_gcd_of_psu {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    {F : Type} [Field F] [Finite F] {p f n : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hF : Nat.card F = (p ^ f) ^ 2) (hn : 3 ≤ n) (h43 : ¬ (n = 4 ∧ p ^ f = 3))
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSU n (p ^ f) F)) :
    Nat.card (Subgroup.center L) ∣ Nat.gcd n (p ^ f + 1) := by
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e
  have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2).pow
  have hp3 : 3 ≤ p ^ f := by
    have := (Fact.out : p.Prime).two_le
    have h3 : 3 ≤ p := by omega
    exact h3.trans (Nat.le_self_pow (by omega) p)
  have hcard : ∀ {m : ℕ}, Nonempty (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedSU n (p ^ f) F)) ≃* Multiplicative (ZMod m)) → Nat.card
      (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSU n (p ^ f) F))) = m := by
    rintro m ⟨φ⟩
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  by_cases hev : Even n
  · have hn4 : 4 ≤ n := by obtain ⟨k, hk⟩ := hev; omega
    by_cases h3 : p ^ f = 3
    · have hp : p = 3 := by
        have h1 : p ∣ 3 := h3 ▸ dvd_pow_self p (by omega)
        exact (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).1 h1
      subst hp
      have hf1 : f = 1 := by
        have : 3 ^ f = 3 ^ 1 := by rw [h3]; rfl
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
      subst hf1
      have hn6 : 6 ≤ n := by obtain ⟨k, hk⟩ := hev; omega
      have hM := (CFSG.LieType.Steinberg.CentralExt.SUClosed.psu_three_hopfMultiplier
        (F := F) hF hev hn6).2
      rw [hcard hM] at hdvd
      exact hdvd
    · have hq4 : 4 ≤ p ^ f := by
        by_contra hlt
        have : p ^ f = 3 := by
          obtain ⟨k, hk⟩ := hodd
          omega
        exact h3 this
      have hM := (CFSG.LieType.Steinberg.CentralExt.SUClosed.psu_hopfMultiplier
        (F := F) hF hev hn4 hq4).2
      rw [hcard hM] at hdvd
      exact hdvd
  · have hq : (n, p ^ f) ≠ (3, 2) := by
      intro h
      have h2 : p ^ f = 2 := (Prod.mk.inj h).2
      rw [h2] at hodd
      exact absurd hodd (by decide)
    have hM := (CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier
      (F := F) hF hf hn hev hq).2
    rw [hcard hM] at hdvd
    exact hdvd

theorem exists_psu_model_of_lie_twistedA {L : Type} [Group L] [Finite L]
    (hperf : Group.IsPerfect L) (_hodd : Odd (Nat.card (Subgroup.center L))) {r : ℕ}
    {q : PrimePower} (hv : (LieTypeIndex.twistedA r q).Valid) (hp2 : q.p ≠ 2)
    (h43 : ¬ (r = 3 ∧ q.card = 3))
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) :
    Nat.card (Subgroup.center L) ∣ Nat.gcd (r + 1) (q.p ^ q.exponent + 1) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (q.p ^ q.exponent) ^ 2 ∧
        Nonempty (L ⧸ Subgroup.center L ≃*
          StatedProj (StatedSU (r + 1) (q.p ^ q.exponent) K)) := by
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hr : 2 ≤ r := hrange.1
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, hKf, hKfin, hK, ⟨e'⟩⟩ :
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (q.p ^ q.exponent) ^ 2 ∧
        Nonempty (L ⧸ Subgroup.center L ≃*
          StatedProj (StatedSU (r + 1) (q.p ^ q.exponent) K)) :=
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e).2
  have : CharP K q.p := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := q.exponent * 2) (by
      rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  refine ⟨?_, K, hKf, hKfin, hK, ⟨e'⟩⟩
  exact card_center_dvd_gcd_of_psu hperf hp2 q.exponent_pos hK (by omega)
    (fun h => h43 ⟨by omega, by simpa [PrimePower.card_def] using h.2⟩) e'

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
