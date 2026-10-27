module

public import CFSG.GH74.GLS.C3.Layer2.Pattern67
public import CFSG.GH74.GLS.C3.Layer2.Terminal
public import CFSG.GH74.GLS.C3.Layer2.LocalRank

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.GH74.GLS.C3.Layer2

@[expose] def B_L2_Cv : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (n : ℕ) (x : G) (K T Q S : Subgroup G) (a : G),
    (n = 6 ∨ n = 7) → IsAConfig n x K T Q S a →
      ∃ v' : alternatingGroup (Fin (n + 4)), orderOf v' = 2 ∧
        numMoved (v' : Equiv.Perm (Fin (n + 4))) = 8 ∧
        Nonempty (↥(centralizer ({x * (a * x * a⁻¹)} : Set G)) ≃*
          ↥(centralizer ({v'} : Set (alternatingGroup (Fin (n + 4))))))

@[expose] def B_L2_five : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → AConfig G 5 → IsApproxTo G (alternatingGroup (Fin 9))

theorem b_L2_W2 :
    ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (n : ℕ) (x : G) (K T Q S : Subgroup G) (a : G),
      (n = 6 ∨ n = 7) → IsAConfig n x K T Q S a →
        ∀ q ∈ Q, q ≠ 1 → (Nat.card ↥(centralizer ({q} : Set G))).factorization 2 ≤
          (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 := by
  intro G _ _ hG n x K T Q S a hn h q hq hq1
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four ▸ le_rfl
  have hnt := h.exists_noncomm hn hG4
  exact h.factorization_centralizer_le (by rcases hn with rfl | rfl <;> norm_num) hG4 hnt q hq hq1

theorem s_layerII_of
    (hCv : B_L2_Cv) (h5 : B_L2_five) : S_layerII := by
  intro G _ _ hG n hn hconf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | hn67
  · exact h5 G hG hconf
  · have hn' : n = 6 ∨ n = 7 := by omega
    obtain ⟨x, K, T, Q, S, a, h⟩ := hconf
    obtain ⟨hs, hnab, -⟩ := isKProperSimple_iff.1 hG.kproper
    have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four ▸ le_rfl
    have hnt := h.exists_noncomm hn' hG4
    exact approxTo_of_config_67 h hn' hs hnab hnt
      (b_L2_W2 G hG n x K T Q S a hn' h) (hCv G hG n x K T Q S a hn' h)

end CFSG.GH74.GLS
