module

public import CFSG.ClassicalInvolution.Phan.Phan3TRec
public import CFSG.ClassicalInvolution.Phan.Phan3TNorm
public import CFSG.ClassicalInvolution.Phan.Phan3TDefs

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem weakPhan3_recognition_of_tripleBlocks (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f = 3) {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X] {U : Fin n → Subgroup X}
    {W : Fin n → Fin n → Subgroup X} (hW : WeakPhanA K p f n U W)
    (hT : AdjacentTripleBlocks K p f U W) :
    ∃ ψ : Su K p f (n + 1) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (Su K p f (n + 1)) ∧
      ∀ i : Fin n, (blockEmb2 K p f n i).range.map ψ = U i := by
  refine weakPhan3_recognition_of_extension hK hq hn hW fun F hFι hFinj hFθ a ha => ?_
  have h1 : ((⟨a + 1, by omega⟩ : Fin n) : ℕ) = ((⟨a, by omega⟩ : Fin n) : ℕ) + 1 := rfl
  have h2 : ((⟨a + 2, ha⟩ : Fin n) : ℕ) = ((⟨a + 1, by omega⟩ : Fin n) : ℕ) + 1 := rfl
  obtain ⟨θ, -, hker, e₀, e₁, e₂⟩ := hT ⟨a, by omega⟩ ⟨a + 1, by omega⟩ ⟨a + 2, ha⟩ h1 h2
  have T : BlockTriple F θ ⟨a, by omega⟩ ⟨a + 1, by omega⟩ ⟨a + 2, ha⟩ :=
    ⟨h1, h2, hker, e₀.trans (hFι _).symm, e₁.trans (hFι _).symm, e₂.trans (hFι _).symm, hFinj,
      fun i h => (hFθ i h).2⟩
  obtain ⟨Θ, h₀, h₁, h₂⟩ := T.exists_extension hK
  refine ⟨Θ, fun k => ?_⟩
  fin_cases k
  · exact h₀
  · exact h₁
  · exact h₂

theorem phan3Rec_of_tripleBlocks {n : ℕ} (hn : 4 ≤ n) {X : Type} [Group X] {U : Fin n → Subgroup X}
    {W : Fin n → Fin n → Subgroup X} (hW : WeakPhanA (GaloisField 3 2) 3 1 n U W)
    (hT : AdjacentTripleBlocks (GaloisField 3 2) 3 1 U W) :
    ∃ ψ : Su (GaloisField 3 2) 3 1 (n + 1) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 (n + 1)) ∧
      ∀ i : Fin n, (blockEmb2 (GaloisField 3 2) 3 1 n i).range.map ψ = U i :=
  weakPhan3_recognition_of_tripleBlocks
    (by rw [GaloisField.card 3 2 (by norm_num)]; norm_num) (by norm_num) (by omega) hW hT

end CFSG.ClassicalInvolution.Phan.Q3G
