module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitInputs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem l2_cases (hL : L2NoPauliPSL) (hU : L2NoPauliPSU) (hO : L2NoPauliPOmega)
    {S : Type} [Group S] [Finite S] {H : Type} [Group H] [Finite H] (ρ : H →* S)
    (A : Subgroup S) (hρ : Function.Surjective ρ) (hq : CFSG.IsQuasisimple H)
    (hker : ρ.ker = center H) (h2 : IsPGroup 2 ↥(center H)) (hE : IsE 4 ↥A) (hP : L2Pauli ρ A)
    (hS : IsSylowIn 2 (centIn ⊤ A) A) (hZ : L2Z4Type S) :
    CFSG.Blueprint.NativeSporadic.IsSporadic S .M22 ∨ CFSG.Blueprint.LieModel S .PSL 3 2 2 ∨
      LitPSLU4All S := by
  rcases hZ with hM22 | hL34 | hPSL | hPSU | hPO | hPM
  · exact Or.inl hM22
  · exact Or.inr (Or.inl hL34)
  · obtain ⟨n, p, f, h4n, h4q, hX⟩ := hPSL
    obtain ⟨hp, hf, hn, -⟩ := hX.admissible
    have h1 : 1 ≤ p ^ f := Nat.one_le_pow f p hp.pos
    by_cases hn4 : n = 4
    · subst n
      refine Or.inr (Or.inr (Or.inl ⟨p, f, hp, by omega, ?_, hX⟩))
      obtain ⟨k, hk⟩ := h4q
      omega
    · have h8 : 8 ≤ n := by
        obtain ⟨k, hk⟩ := h4n
        omega
      exact (hL S H ρ A hρ hq hker h2 hE hP hS n p f h8 h4n h4q hX).elim
  · obtain ⟨n, p, f, h4n, h4q, hX⟩ := hPSU
    obtain ⟨hp, hf, hn, -⟩ := hX.admissible
    have h1 : 1 ≤ p ^ f := Nat.one_le_pow f p hp.pos
    by_cases hn4 : n = 4
    · subst n
      refine Or.inr (Or.inr (Or.inr ⟨p, f, hp, by omega, ?_, hX⟩))
      obtain ⟨k, hk⟩ := h4q
      omega
    · have h8 : 8 ≤ n := by
        obtain ⟨k, hk⟩ := h4n
        omega
      exact (hU S H ρ A hρ hq hker h2 hE hP hS n p f h8 h4n h4q hX).elim
  · obtain ⟨n, p, f, hodd, h4q, hX⟩ := hPO
    obtain ⟨hp, hf, hn⟩ := hX.admissible
    have h5 : 5 ≤ n := by
      obtain ⟨k, hk⟩ := hodd
      omega
    exact (hO S H ρ A hρ hq hker h2 hE hP hS n p f h5 hodd (Or.inl ⟨h4q, hX⟩)).elim
  · obtain ⟨n, p, f, hodd, h4q, hX⟩ := hPM
    obtain ⟨hp, hf, hn⟩ := hX.admissible
    have h5 : 5 ≤ n := by
      obtain ⟨k, hk⟩ := hodd
      omega
    exact (hO S H ρ A hρ hq hker h2 hE hP hS n p f h5 hodd (Or.inr ⟨h4q, hX⟩)).elim

end CFSG.OddStandard.HigherRank.YamadaG23
