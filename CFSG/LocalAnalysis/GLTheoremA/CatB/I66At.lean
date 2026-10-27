module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I66Cube
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I66Real
public import CFSG.LocalAnalysis.GLTheoremA.S8.Inputs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S8

@[expose] def I66RealS : Prop :=
  (∀ t : (TauCeti.CFSGIndex.sporadic .Suz).Group, orderOf t = 3 → IsConj t t⁻¹) ∧
  (∀ t : (TauCeti.CFSGIndex.sporadic .Fi22).Group, orderOf t = 3 → IsConj t t⁻¹) ∧
  (∀ t : (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group, orderOf t = 3 → IsConj t t⁻¹) ∧
  (∃ g ∈ CFSG.Sporadic.Schreier.j3P,
    g * CFSG.RankThree.PartTwo.KFacts.K426.j3tXB * g⁻¹ =
      (CFSG.RankThree.PartTwo.KFacts.K426.j3tXB)⁻¹)

theorem i66_mult_pos (s : TauCeti.SporadicName) :
    0 < CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s := by
  cases s <;> decide

theorem i66_mult_le (s : TauCeti.SporadicName) :
    CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s ≤ 12 := by
  cases s <;> decide

theorem i66_nine_not_dvd (s : TauCeti.SporadicName) :
    ¬ 9 ∣ CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s := by
  cases s <;> decide

theorem i66_prime_big (s : TauCeti.SporadicName) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ p ∣ CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s := by
  intro hd
  have hle := (Nat.le_of_dvd (i66_mult_pos s) hd).trans (i66_mult_le s)
  interval_cases p
  all_goals first
    | (norm_num at hp; done)
    | (revert hd; cases s <;> decide)

theorem i66_card_center_dvd (hT : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    {K : Type} [Group K] [Finite K] (hK : Group.IsPerfect K) (s : TauCeti.SporadicName)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    Nat.card (Subgroup.center K) ∣
      CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s := by
  have h1 := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hK e
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    hT.1 s] at h1
  exact h1

theorem i66_clause1 (hT : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hreal : ∀ s : TauCeti.SporadicName,
      3 ∣ CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s →
        ∀ t : (TauCeti.CFSGIndex.sporadic s).Group, orderOf t = 3 → IsConj t t⁻¹) :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      CFSG.Open.GLAPPrimeCore 3 K = ⊥ →
      catalogIs (K ⧸ Subgroup.center K) isSporIndex →
      ∀ z ∈ Subgroup.center K, orderOf z = 3 → ∀ g : K, g ^ 3 ≠ z := by
  intro K _ _ hK hO hcat z hz hzo g
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p hp => simp [isSporIndex] at hi
  | alternating n hn => simp [isSporIndex] at hi
  | lie d => simp [isSporIndex] at hi
  | sporadic s =>
    have hperf : Group.IsPerfect K := ⟨hK.1⟩
    have hdvd := i66_card_center_dvd hT hperf s e
    have hn : Nat.card (Subgroup.center K) = 3 :=
      CFSG.LocalAnalysis.GLTheoremA.CatB.i66_card_center_eq_three hO hz hzo hdvd
        (i66_nine_not_dvd s)
    have h3 : 3 ∣ CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s := by
      rw [← hn]
      exact hn ▸ hdvd
    intro hg
    exact CFSG.LocalAnalysis.GLTheoremA.CatB.i66_cube_false hz hzo hn e (hreal s h3) g hg

theorem i66_clause2 (hT : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      catalogIs (K ⧸ Subgroup.center K) isSporIndex →
      ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.Open.GLAPPrimeCore p K = ⊥ →
      Subgroup.center K = ⊥ := by
  intro K _ _ hK hcat p hp hp5 hO
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic q hq => simp [isSporIndex] at hi
  | alternating n hn => simp [isSporIndex] at hi
  | lie d => simp [isSporIndex] at hi
  | sporadic s =>
    have hperf : Group.IsPerfect K := ⟨hK.1⟩
    have hdvd := i66_card_center_dvd hT hperf s e
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center K)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr
        (fun hd => i66_prime_big s p hp hp5 (hd.trans hdvd))
    exact CFSG.LocalAnalysis.GLTheoremA.CatB.i66_center_eq_bot p hO hcop

theorem i66_real_of
    (h : I66RealS) (s : TauCeti.SporadicName)
    (h3 : 3 ∣ CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s) :
    ∀ t : (TauCeti.CFSGIndex.sporadic s).Group, orderOf t = 3 → IsConj t t⁻¹ := by
  obtain ⟨hSuz, hFi22, hFi24, hB⟩ := h
  cases s <;> first
    | exact absurd h3 (by decide)
    | exact CFSG.LocalAnalysis.GLTheoremA.CatB.i66_real_M22
    | exact CFSG.LocalAnalysis.GLTheoremA.CatB.i66_real_J3 hB
    | exact CFSG.LocalAnalysis.GLTheoremA.CatB.i66_real_McL
    | exact CFSG.LocalAnalysis.GLTheoremA.CatB.i66_real_ON
    | exact hSuz
    | exact hFi22
    | exact hFi24

theorem i66At_of_real
 (h : I66RealS) : I66At := by
  unfold I66At
  have hT : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
  exact ⟨i66_clause1 hT (fun s h3 => i66_real_of h s h3), i66_clause2 hT⟩

end CFSG.LocalAnalysis.GLTheoremA

end
