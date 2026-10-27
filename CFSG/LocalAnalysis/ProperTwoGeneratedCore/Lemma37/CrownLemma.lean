module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CrownLemmaFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairIndexTwo

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

variable {G : Type*} [Group G]

theorem crown_lemma_of_card_sq [Finite G] (hindexTwo : ∀ K : Subgroup G, K.index ≠ 2)
    (S : Sylow 2 G) {W : Subgroup G} (hWS : W ≤ S) (hWidx : W.relIndex S = 2)
    (hWexp : ∀ w ∈ W, w ^ 2 = 1) {y : G} (hyS : y ∈ S) (hyW : y ∉ W) (hy : y ^ 2 = 1)
    (hW : Nat.card W = Nat.card (W ⊓ Subgroup.centralizer {y} : Subgroup G) ^ 2)
    (hΔ : 2 < Nat.card (W ⊓ Subgroup.centralizer {y} : Subgroup G)) : False := by
  have h : CrownSetting (S : Subgroup G) W y := ⟨hWS, hWidx, hWexp, hyS, hyW, hy⟩
  obtain ⟨g, hg⟩ := RankOnePair.exists_conj_mem_of_sylow_relIndex_two hindexTwo S W hWS hWidx y
    (orderOf_eq_prime hy fun h1 => hyW (h1 ▸ W.one_mem))
  obtain ⟨n, hnN, hy₁⟩ := h.exists_conj_mem_axis (by rw [hW, sq]; nlinarith) hg
  exact h.false_of_conj_mem_axis hW hΔ hnN hy₁

theorem crown_lemma [Finite G] (hindexTwo : ∀ K : Subgroup G, K.index ≠ 2) (S : Sylow 2 G)
    {W : Subgroup G} (hWS : W ≤ S) (hWidx : W.relIndex S = 2) (hWexp : ∀ w ∈ W, w ^ 2 = 1)
    (hW : Nat.card W = 16) {y : G} (hyS : y ∈ S) (hyW : y ∉ W) (hy : y ^ 2 = 1)
    (hΔ : Nat.card (W ⊓ Subgroup.centralizer {y} : Subgroup G) = 4) : False :=
  crown_lemma_of_card_sq hindexTwo S hWS hWidx hWexp hyS hyW hy (by rw [hW, hΔ]; norm_num)
    (by omega)

theorem crown_lemma_of_perfect [Finite G] (hperf : commutator G = ⊤) (S : Sylow 2 G)
    {W : Subgroup G} (hWS : W ≤ S) (hWidx : W.relIndex S = 2) (hWexp : ∀ w ∈ W, w ^ 2 = 1)
    (hW : Nat.card W = 16) {y : G} (hyS : y ∈ S) (hyW : y ∉ W) (hy : y ^ 2 = 1)
    (hΔ : Nat.card (W ⊓ Subgroup.centralizer {y} : Subgroup G) = 4) : False := by
  refine crown_lemma (fun K hK => ?_) S hWS hWidx hWexp hW hyS hyW hy hΔ
  have hle : commutator G ≤ K := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    exact fun a _ b _ => commutatorElement_mem_of_sq_mem (Subgroup.sq_mem_of_index_two hK) a b
  rw [hperf, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hK
  omega

end CFSG.ProperTwoGeneratedCore.Lemma37
