module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticB
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthFamily

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.HardMathSupport.Timmesfeld.DefChar

@[expose] def regimeBAll (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  regimeBOrth idx p ∨ regimeBSp idx p

theorem crossCharFamAt_B_all : CrossCharFamAt .B regimeBAll := by
  intro idx hk p hp hp2 hc hR
  rcases hR with hR | hR
  · exact crossCharFamAt_B_orth idx hk p hp hp2 hc hR
  · exact crossCharFamAt_B_symplectic idx hk p hp hp2 hc hR

theorem orth_eq_three_of_not_lt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : ¬ 3 < p) : p = 3 := by
  have := hp.two_le
  omega

theorem not_regimeBAll_iff {idx : TauCeti.ValidLieTypeIndex} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : LieFamily.B.Matches idx.1) :
    ¬ regimeBAll idx p ↔ p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .B r q ∧
      ((q.p ≠ 2 ∧ 3 ≤ r) ∨ q.card = 2) := by
  obtain ⟨r, q, hrq⟩ := hk
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 (hrq ▸ idx.2)).1
  have hr2 : 2 ≤ r := hrange.1
  constructor
  · intro h
    have hO : ¬ regimeBOrth idx p := fun h' => h (Or.inl h')
    have hS : ¬ regimeBSp idx p := fun h' => h (Or.inr h')
    by_cases hq : q.p = 2
    · have : p = 3 ∧ q.card = 2 := by
        by_contra hpc
        exact hS ⟨r, q, hrq, Or.inr hq, hpc⟩
      exact ⟨this.1, r, q, hrq, Or.inr this.2⟩
    · by_cases hr : r = 2
      · have : p = 3 ∧ q.card = 2 := by
          by_contra hpc
          exact hS ⟨r, q, hrq, Or.inl hr, hpc⟩
        exact ⟨this.1, r, q, hrq, Or.inr this.2⟩
      · have h3 : p = 3 :=
          orth_eq_three_of_not_lt hp hp2 fun hp3 => hO ⟨r, q, hrq, hq, by omega, hp3⟩
        exact ⟨h3, r, q, hrq, Or.inl ⟨hq, by omega⟩⟩
  · rintro ⟨h3, r', q', hrq', hc⟩ (⟨r'', q'', hrq'', -, -, hp3⟩ | ⟨r'', q'', hrq'', hsp, h32⟩)
    · omega
    · rw [hrq'] at hrq''
      obtain ⟨rfl, rfl⟩ : r' = r'' ∧ q' = q'' := by
        injection hrq'' with h1 h2
        exact ⟨h1, h2⟩
      rcases hc with ⟨hq, hr⟩ | hc
      · rcases hsp with hsp | hsp
        · omega
        · exact hq hsp
      · exact h32 ⟨h3, hc⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
