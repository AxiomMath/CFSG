module

public import CFSG.ClassicalInvolution.Asc77.AscT7C2RConj
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit24

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Phan

namespace T7C2

variable {X : Type} [Group X]

theorem conjSub_sup (x : X) (A B : Subgroup X) :
    conjSub x (A ⊔ B) = conjSub x A ⊔ conjSub x B :=
  Subgroup.map_sup _ _ _

theorem unitary_conjSub {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    {W U V : Subgroup X} (h : UnitaryBlockStandardPair K p f W U V) (x : X) :
    UnitaryBlockStandardPair K p f (conjSub x W) (conjSub x U) (conjSub x V) := by
  obtain ⟨θ, c, hW, hker, hUV⟩ := h
  refine ⟨(MulAut.conj x).toMonoidHom.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hW]
    rfl
  · rw [MonoidHom.ker_comp_of_injective θ (g := (MulAut.conj x).toMonoidHom)
      (MulAut.conj x).injective]
    exact hker
  · rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

end T7C2

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C24_pair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp23Setting p f Ω K K' z → Hyp24Data Ω K K' W S R R' z u → 8 < Nat.card ↥R →
      ∀ g : G, g⁻¹ * z * g = u →
      ∀ d x : G, d ∈ dGrp24 K S R R' g → orderOf d = 4 → x ∈ R' ⊓ W → orderOf x = 4 →
        (if piSign p f then SectionLieType p f Ω (rLayer Ω (d * x)) .PSL 3
          else SectionLieType p f Ω (rLayer Ω (d * x)) .PSU 3) →
        rLayer Ω (d * x) ⊔ K' = ⊤ →
          Commutes K K' ∧ K ⊔ conjSub g⁻¹ K ⊔ K' = ⊤ ∧
          (piSign p f = true →
            LinearBlockStandardPair (GaloisField p f) (K ⊔ conjSub g⁻¹ K) K (conjSub g⁻¹ K)) ∧
          (piSign p f = false →
            UnitaryBlockStandardPair (GaloisField p (2 * f)) p f (K ⊔ conjSub g⁻¹ K) K
              (conjSub g⁻¹ K))

variable {p f}

theorem c24_chain_of_pair (h : C24_pair p f) : C24_chain p f := by
  intro G _ _ _ Ω K K' W S R R' z u hs hd h8 g hg d x hdD od hx ox hsec hgen
  obtain ⟨hcomm, hgenU, hlin, hphan⟩ :=
    h G Ω K K' W S R R' z u hs hd h8 g hg d x hdD od hx ox hsec hgen
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

end CFSG.ClassicalInvolution.Asc77
