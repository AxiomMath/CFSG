module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcRankMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.YS04G

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank


theorem kd26g_e6 {K : Type} [Group K] [Finite K] (hZ : IsPGroup 3 (Subgroup.center K))
    {q : ℕ} {lin : Bool} (hS : IsE6Eps (K ⧸ Subgroup.center K) q lin) (h3 : 3 ∣ qEps lin q) :
    4 ≤ GLATwoLocalRank 3 K := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  cases i with
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    obtain ⟨π, hπ, hker⟩ := exists_cover e
    have hodd : Odd (Nat.card π.ker) := by
      rw [hker]
      obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 3)).mp hZ
      rw [ha]
      exact Odd.pow (by decide)
    have hmain : ∀ {S : Type} [Group S] (π : K →* S), Function.Surjective π →
        π.ker ≤ Subgroup.center K → Odd (Nat.card π.ker) → LiftDatum S 3 →
        4 ≤ GLATwoLocalRank 3 K := fun π hπ hker hodd hL => by
      have := hL.cover_localRank hπ hker hodd (A := ⊥) (by simp) (by simp) (k := 0) (by simp)
      exact le_trans (by norm_num) this
    cases lin with
    | true =>
      cases d <;> simp only [onLie, isE6Eps] at hi
      rename_i qq
      have hp3 : qq.p ≠ 3 := by
        intro h
        have hq : q = qq.p ^ qq.exponent := by rw [← hi, TauCeti.PrimePower.card_def]
        have hqpos : 0 < q := by rw [hq]; exact pow_pos qq.prime_p.pos _
        have h1 : 3 ∣ q := by rw [hq, h]; exact dvd_pow_self 3 qq.exponent_pos.ne'
        have h2 : 3 ∣ q - 1 := by simpa [qEps] using h3
        have : 3 ∣ 1 := by omega
        omega
      exact hmain π hπ hker.le hodd (e6_liftDatum qq hv hp3)
    | false =>
      cases d <;> simp only [onLie, isE6Eps] at hi
      rename_i qq
      have hp3 : qq.p ≠ 3 := by
        intro h
        have hq : q = qq.p ^ qq.exponent := by rw [← hi, TauCeti.PrimePower.card_def]
        have hqpos : 0 < q := by rw [hq]; exact pow_pos qq.prime_p.pos _
        have h1 : 3 ∣ q := by rw [hq, h]; exact dvd_pow_self 3 qq.exponent_pos.ne'
        have h2 : 3 ∣ q + 1 := by simpa [qEps] using h3
        have : 3 ∣ 1 := by omega
        omega
      exact hmain π hπ hker.le hodd (twistedE6_liftDatum qq hv hp3)

end CFSG.LocalAnalysis.GLTheoremA.YS04G
