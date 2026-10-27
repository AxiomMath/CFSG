module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSizeFactArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSetup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Mark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Size
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusU6Field
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CtxHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.CatDistinct

section BridgeOrder


theorem card_of_catalogIs_isTE6n {S : Type} [Group S] [Finite S] {n : ℕ}
    (h : catalogIs S (S10.isTE6n n)) :
    1 ≤ n ∧ Nat.card S = orderTwistedE6 (2 ^ n) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S10.isTE6n, onLie] at hi
  | alternating k hk => simp [S10.isTE6n, onLie] at hi
  | sporadic s => simp [S10.isTE6n, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedE6 q =>
      simp only [S10.isTE6n, onLie] at hi
      obtain ⟨hp, hn⟩ := hi
      refine ⟨by have := q.exponent_pos; omega, ?_⟩
      rw [lieOrderBridge_holds ⟨.twistedE6 q, hv⟩ S ⟨e⟩]
      show orderTwistedE6 q.card = _
      rw [TauCeti.PrimePower.card_def, hp, hn]
    | _ => simp [S10.isTE6n, onLie] at hi

end BridgeOrder

section Witnesses


private theorem odd_of_u6_of_witness {Ω : Type} [Group Ω] [Finite Ω] {L : Subgroup Ω}
    {n n₀ : ℕ}
    (hn₀ : Odd n₀)
    (hcase : catalogIs (PSimple 3 L) (S10.isU6n n₀) ∨
      catalogIs (PSimple 3 L) (S10.isTE6n n₀))
    (hcat : catalogIs (PSimple 3 L) (S10.isU6n n)) : Odd n := by
  obtain ⟨hn1, hcard, -⟩ := data_isU6n ctx_holds hcat
  rcases hcase with hU6 | hTE6
  · obtain ⟨hn01, hcard0, -⟩ := data_isU6n ctx_holds hU6
    have h : n = n₀ :=
      orderTwistedA_five_two_pow_injective hn1 hn01 (hcard.symm.trans hcard0)
    rw [h]
    exact hn₀
  · obtain ⟨hn01, hcard0⟩ := card_of_catalogIs_isTE6n hTE6
    exact absurd (hcard.symm.trans hcard0)
      (orderTwistedA_five_ne_orderTwistedE6 hn1 hn01)

private theorem odd_of_te6_of_witness {Ω : Type} [Group Ω] [Finite Ω] {L : Subgroup Ω}
    {n n₀ : ℕ}
    (hn₀ : Odd n₀)
    (hcase : catalogIs (PSimple 3 L) (S10.isU6n n₀) ∨
      catalogIs (PSimple 3 L) (S10.isTE6n n₀))
    (hcat : catalogIs (PSimple 3 L) (S10.isTE6n n)) : Odd n := by
  obtain ⟨hn1, hcard⟩ := card_of_catalogIs_isTE6n hcat
  rcases hcase with hU6 | hTE6
  · obtain ⟨hn01, hcard0, -⟩ := data_isU6n ctx_holds hU6
    exact absurd (hcard0.symm.trans hcard)
      (orderTwistedA_five_ne_orderTwistedE6 hn01 hn1)
  · obtain ⟨hn01, hcard0⟩ := card_of_catalogIs_isTE6n hTE6
    have h : n = n₀ :=
      orderTwistedE6_two_pow_injective hn1 hn01 (hcard.symm.trans hcard0)
    rw [h]
    exact hn₀

end Witnesses

theorem t171SizeFact_of
    (h9 : U6Type9) (h3 : E6Bound true) : T171.T171SizeFact := by
  intro p Ω _ _ B x L D K β _ hcfg _ hpre hpc hch hβ hβD hni hExt
  obtain ⟨rfl, n₀, hn₀, hcase⟩ := hExt
  obtain ⟨A, d, -, -, hSetup, hcardB⟩ :=
    setup_of_cfg hcfg hpre hpc hch hβ hβD hni
  constructor
  · intro n hcatU6
    have hn : Odd n := odd_of_u6_of_witness hn₀ hcase hcatU6
    have h3dvd : 3 ∣ 2 ^ n + 1 := by
      simpa using Odd.nat_add_dvd_pow_add_pow (x := 2) (y := 1) (n := n) hn
    have hA := card_le_u6_of_marking u6Marking_holds h9 u6SizeModel_holds hSetup hcatU6 hn h3dvd
    calc Nat.card B = 3 * Nat.card A := hcardB
      _ ≤ 3 * 3 ^ (1 + 6 / 3) := Nat.mul_le_mul_left 3 hA
      _ = 3 ^ 4 := by norm_num
  · intro n hcatTE6
    have hn : Odd n := odd_of_te6_of_witness hn₀ hcase hcatTE6
    have hE6cat : catalogIs (PSimple 3 L) (onLie fun i =>
        ∃ q, I171.I171LieShape 3 i ∧ i = .twistedE6 q) := by
      refine catalogIs_imp (fun i hi => ?_) hcatTE6
      cases i with
      | cyclic p hp => simp [S10.isTE6n, onLie] at hi
      | alternating k hk => simp [S10.isTE6n, onLie] at hi
      | sporadic s => simp [S10.isTE6n, onLie] at hi
      | lie idx =>
        obtain ⟨d, hv⟩ := idx
        cases d with
        | twistedE6 q =>
          simp only [S10.isTE6n, onLie] at hi
          obtain ⟨hp, hnq⟩ := hi
          refine ⟨q, ⟨rfl, hp, ?_⟩, rfl⟩
          rw [TauCeti.PrimePower.card_def, hp, hnq]
          simpa using Odd.nat_add_dvd_pow_add_pow (x := 2) (y := 1) (n := n) hn
        | _ => simp [S10.isTE6n, onLie] at hi
    have hA := h3 Ω L K A d β hSetup hE6cat
    calc Nat.card B = 3 * Nat.card A := hcardB
      _ ≤ 3 * 3 ^ 4 := Nat.mul_le_mul_left 3 hA
      _ = 3 ^ 5 := by norm_num

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
