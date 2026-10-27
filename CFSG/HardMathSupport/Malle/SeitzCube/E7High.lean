module

public import CFSG.HardMathSupport.Malle.SeitzCube.LandingE7
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

@[expose] def ExcCubeHighAt (c : TauCeti.PrimePower → TauCeti.LieTypeIndex) (e : ℕ) : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (c q).Valid) (p : ℕ), p.Prime → p ≠ 2 → p ≠ q.p →
    ¬ P1ThreeLieList p ⟨c q, hv⟩ → ¬ p ∣ q.card ^ 2 - 1 →
    orderOf ((q.card : ℕ) : ZMod p) = e →
    (∃ E₀ : Subgroup (Cat ⟨c q, hv⟩), IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 3) →
    ∃ E : Subgroup (Cat ⟨c q, hv⟩), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      (NormalizesRSub ⟨c q, hv⟩ E ∨ HyperGen p ⊤ E)

theorem orderOf_eq_E7 {e : ℕ} (h : 3 ≤ degCount .E7 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 6 := by
  have h30 : e ≤ 30 := le_thirty_of_degCount_pos (Or.inr (Or.inr (Or.inl rfl))) (by omega)
  interval_cases e <;> first | decide | (exfalso; revert h; decide)

theorem orderOf_E7_high {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (hpq2 : ¬ p ∣ q ^ 2 - 1)
    (hdeg : 3 ≤ degCount .E7 (orderOf ((q : ℕ) : ZMod p))) :
    orderOf ((q : ℕ) : ZMod p) = 3 ∨ orderOf ((q : ℕ) : ZMod p) = 6 := by
  have : Fact p.Prime := ⟨hp⟩
  have hsq : ((q : ℕ) : ZMod p) ^ 2 ≠ 1 := fun h => hpq2 (by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow,
      Nat.cast_one, h, sub_self])
  rcases orderOf_eq_E7 hdeg with h | h | h | h
  · exact absurd (by rw [orderOf_eq_one_iff.1 h, one_pow]) hsq
  · exact absurd (h ▸ pow_orderOf_eq_one _) hsq
  · exact Or.inl h
  · exact Or.inr h

theorem excCubeHigh_E7_of_at (h3 : ExcCubeHighAt TauCeti.LieTypeIndex.E7 3)
    (h6 : ExcCubeHighAt TauCeti.LieTypeIndex.E7 6) :
    ExcCubeHigh .E7 TauCeti.LieTypeIndex.E7 := by
  intro q hv p hp hp2 hpq hl hpq2 hdeg hE₀
  have hq1 : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  rcases orderOf_E7_high hp hq1 hpq2 hdeg with h | h
  · exact h3 q hv p hp hp2 hpq hl hpq2 h hE₀
  · exact h6 q hv p hp hp2 hpq hl hpq2 h hE₀

section Twisted


@[expose] def TwistedCubeE7 (P : ℕ → ℕ → Prop) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L), (∀ c, Fr c = c ^ Nat.card K) → ∀ p : ℕ, p.Prime → p ≠ 2 → P (Nat.card K) p →
      TwistedCube .E7 L Fr p (ringChar K)

theorem excCubeHighAt_E7_three_of_twisted
    (h : TwistedCubeE7 fun q p => orderOf ((q : ℕ) : ZMod p) = 3) :
    ExcCubeHighAt TauCeti.LieTypeIndex.E7 3 := by
  intro q hv p hp hp2 _ _ _ he _
  obtain ⟨E, hE, hc, hR⟩ := exists_cube_cat_E7_of_twisted q hv hp hp2
    fun K _ _ hK hKc L _ _ _ Fr hFr => by
      have hT := h K L Fr (fun c => by rw [hFr, hK]) p hp hp2 (by rwa [hK])
      rwa [ringChar.eq K q.p] at hT
  exact ⟨E, hE, hc, Or.inl hR⟩

end Twisted

end CFSG.HardMathSupport.Malle.SeitzCube
