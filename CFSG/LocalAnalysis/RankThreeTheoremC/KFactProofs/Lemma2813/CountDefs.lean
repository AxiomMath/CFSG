module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
variable {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction GL32 M]

structure CTHyp (M : Type) [AddCommGroup M] [Finite M] [DistribMulAction GL32 M] (p₀ : V3)
    (d : GL32) : Prop where
  two : ∀ m : M, m + m = 0
  fixed : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0
  ne : ∃ m : M, m ≠ 0
  hp₀ : p₀ ≠ 0
  off : Nat.card M ≤ 4 * Nat.card (fixSub M (Spt p₀))
  hd : orderOf d = 3
  hdp : act d p₀ = p₀

@[expose] def CTConcl (M : Type) [AddCommGroup M] [DistribMulAction GL32 M] (p₀ : V3)
    (d : GL32) : Prop :=
  Nat.card (commSub M (zpowers d)) ≤ 16 ∧ Nat.card (fixSub M (Spt p₀ ⊔ zpowers d)) ≤ 2 ∧
    ((∃ m ∈ fixSub M (Spt p₀), d • m ≠ m) → fixSub M (Spt p₀ ⊔ zpowers d) = ⊥)

open Classical in
@[expose] noncomputable def Pset (M : Type) [AddCommGroup M] [DistribMulAction GL32 M]
    (w : M) : Finset V3 :=
  Finset.univ.filter (fun x : V3 => x ≠ 0 ∧ w ∈ fixSub M (Spt x))

@[expose] noncomputable def Ncnt (M : Type) [AddCommGroup M] [DistribMulAction GL32 M]
    (k : ℕ) : ℕ :=
  Nat.card {w : M // w ≠ 0 ∧ (Pset M w).card = k}

theorem mem_Pset {w : M} {x : V3} : x ∈ Pset M w ↔ x ≠ 0 ∧ w ∈ fixSub M (Spt x) := by
  classical
  simp [Pset]
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
