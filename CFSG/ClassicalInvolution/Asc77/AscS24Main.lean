module

public import CFSG.ClassicalInvolution.Asc77.AscS24Gen
public import CFSG.ClassicalInvolution.Asc77.AscT7C2RFive

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
open CFSG.Open (classicalInvolutionOddCore)

set_option linter.unusedSectionVars false


variable (p f : ℕ) [Fact p.Prime]

@[expose] def LayerE0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u g : G)
    (C : Ctx p f Ω K K' W S R R' z u g),
      if piSign p f then LayerLieType p f Ω C.e0 .PSL 3 else LayerLieType p f Ω C.e0 .PSU 3

variable {p f}

section Assembly

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}

theorem pairCore [IsSimpleGroup G] (hB2 : LayerE0 p f) (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (h8 : 8 < Nat.card ↥R) {g : G}
    (hg : g⁻¹ * z * g = u) :
    Commutes K K' ∧ K ⊔ conjSub g⁻¹ K ⊔ K' = ⊤ ∧
      (piSign p f = true →
        LinearBlockStandardPair (GaloisField p f) (K ⊔ conjSub g⁻¹ K) K (conjSub g⁻¹ K)) ∧
      (piSign p f = false →
        UnitaryBlockStandardPair (GaloisField p (2 * f)) p f (K ⊔ conjSub g⁻¹ K) K
          (conjSub g⁻¹ K)) := by
  obtain ⟨C⟩ := Ctx.exists_of_gt hs hd hg h8
  have hZ := hd.hZ
  have hL := hB2 G Ω K K' W S R R' z u g C
  obtain ⟨hlin, huni⟩ := C.standardPair hZ hL
  exact ⟨C.commutes_twin hZ hL, C.sup3_eq_top, hlin, huni⟩

theorem chain_of_pair_data [IsSimpleGroup G] (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) {g : G} (hg : g⁻¹ * z * g = u)
    (hcomm : Commutes K K') (hgenU : K ⊔ conjSub g⁻¹ K ⊔ K' = ⊤)
    (hlin : piSign p f = true →
      LinearBlockStandardPair (GaloisField p f) (K ⊔ conjSub g⁻¹ K) K (conjSub g⁻¹ K))
    (hphan : piSign p f = false →
      UnitaryBlockStandardPair (GaloisField p (2 * f)) p f (K ⊔ conjSub g⁻¹ K) K
        (conjSub g⁻¹ K)) :
    (piSign p f = true → ∃ U : Fin 3 → Subgroup G, LinearChain3 p f U) ∧
      (piSign p f = false → ∃ U : Fin 3 → Subgroup G, PhanChain3 p f U) := by
  obtain ⟨h₀, h1, h2⟩ := T7C2.exists_chain_conj hs hd hg
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hf : 2 * f ≠ 0 := by
    intro h0
    have : f = 0 := by omega
    subst this
    simp at hq
  have hK2 : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) hf, ← pow_mul, mul_comm]
  have hgen' : ⨆ k : Fin 3, (![K, conjSub g⁻¹ K, K'] : Fin 3 → Subgroup G) k = ⊤ := by
    rw [eq_top_iff, ← hgenU]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_iSup (fun k : Fin 3 => (![K, conjSub g⁻¹ K, K'] : Fin 3 → Subgroup G) k) 0
    · exact le_iSup (fun k : Fin 3 => (![K, conjSub g⁻¹ K, K'] : Fin 3 → Subgroup G) k) 1
    · exact le_iSup (fun k : Fin 3 => (![K, conjSub g⁻¹ K, K'] : Fin 3 → Subgroup G) k) 2
  refine ⟨fun hπ => ?_, fun hπ => ?_⟩
  · have h₁ := hlin hπ
    have h₂ : LinearBlockStandardPair (GaloisField p f) (conjSub h₀ (K ⊔ conjSub g⁻¹ K))
      (conjSub h₀ K) (conjSub h₀ (conjSub g⁻¹ K)) :=
      ModelFacts.linearBlockStandardPair_map_conj h₁ h₀
    rw [T7C2.conjSub_sup, h1, h2] at h₂
    exact ⟨![K, conjSub g⁻¹ K, K'], hcomm, ⟨_, h₁⟩, ⟨_, h₂⟩, hgen'⟩
  · have h₁ := hphan hπ
    have h₂ := T7C2.unitary_conjSub h₁ h₀
    rw [T7C2.conjSub_sup, h1, h2] at h₂
    refine ⟨![K, conjSub g⁻¹ K, K'], fun i j => (![K, conjSub g⁻¹ K, K'] : Fin 3 → Subgroup G) i ⊔
      (![K, conjSub g⁻¹ K, K'] : Fin 3 → Subgroup G) j, ?_, ?_, ?_, ?_, hgen'⟩
    · intro i
      fin_cases i
      · exact (nonempty_mulEquiv_of_standardPair hK2 h₁).1
      · exact (nonempty_mulEquiv_of_standardPair hK2 h₁).2
      · exact (nonempty_mulEquiv_of_standardPair hK2 h₂).2
    · intro i j _
      rfl
    · have key : ∀ i j : Fin 3, (i : ℕ) + 1 < j → i = 0 ∧ j = 2 := by decide
      intro i j hij
      obtain ⟨rfl, rfl⟩ := key i j hij
      exact hcomm
    · have key : ∀ i j : Fin 3, (j : ℕ) = i + 1 → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) := by decide
      intro i j hij
      rcases key i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h₁
      · exact h₂

theorem concOrTF4_of_layer [IsSimpleGroup G] (hB2 : LayerE0 p f)
    (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp24Data Ω K K' W S R R' z u)
    (h8 : 8 < Nat.card ↥R) {g : G} (hg : g⁻¹ * z * g = u) : ConcOrTF4 G := by
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  obtain ⟨hcomm, hgenU, hlin, hphan⟩ := pairCore hB2 hs hd h8 hg
  obtain ⟨hl, hu⟩ := chain_of_pair_data hs hd hg hcomm hgenU hlin hphan
  have hnab : ∃ a b : G, a * b ≠ b * a := T7C.exists_not_commute_of_stand hst
  refine Or.inl (Or.inl ?_)
  cases hπ : piSign p f
  · obtain ⟨U, hU⟩ := hu hπ
    exact oddLieType_of_phanChain3 hp hq hnab hU
  · obtain ⟨U, hU⟩ := hl hπ
    exact oddLieType_of_linearChain3 hp hq hnab hU

end Assembly

theorem c24_pair_of_layer (hB2 : LayerE0 p f) : C24_pair p f := by
  intro G _ _ _ Ω K K' W S R R' z u hs hd h8 g hg _ _ _ _ _ _ _ _
  exact pairCore hB2 hs hd h8 hg

theorem c24_8_big_of_layer (hB2 : LayerE0 p f) : C24_8_big p f := by
  intro G _ _ _ Ω K K' W S R R' z u hyp h8 g hg _ _ _ _ _ _
  exact (hyp.std.1.cex (concOrTF4_of_layer hB2 hyp.std.setting hyp.data h8 hg)).elim

end CFSG.ClassicalInvolution.Asc77.S24
