module

public import CFSG.LocalAnalysis.AGLEmbedding.G28InSitu

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Perfect

variable {H₁ W₁ : Type*} [Group H₁] [Group W₁]

@[expose] def iterComm' (Q : Subgroup H₁) : ℕ → Subgroup H₁
  | 0 => Q
  | k + 1 => ⁅iterComm' Q k, iterComm' Q k⁆

theorem iterComm'_succ_le (Q : Subgroup H₁) (k : ℕ) : iterComm' Q (k + 1) ≤ iterComm' Q k := by
  change ⁅iterComm' Q k, iterComm' Q k⁆ ≤ iterComm' Q k
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact (iterComm' Q k).mul_mem ((iterComm' Q k).mul_mem ((iterComm' Q k).mul_mem ha hb)
    ((iterComm' Q k).inv_mem ha)) ((iterComm' Q k).inv_mem hb)

theorem iterComm'_le (Q : Subgroup H₁) (k : ℕ) : iterComm' Q k ≤ Q := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (iterComm'_succ_le Q k).trans ih

theorem exists_perfect_le_map_eq' [Finite H₁] (f : H₁ →* W₁) {Q : Subgroup H₁}
    {P : Subgroup W₁} (hQ : Q.map f = P) (hP : ⁅P, P⁆ = P) :
    ∃ P' : Subgroup H₁, P' ≤ Q ∧ ⁅P', P'⁆ = P' ∧ P'.map f = P := by
  have hmap : ∀ k, (iterComm' Q k).map f = P := by
    intro k
    induction k with
    | zero => exact hQ
    | succ k ih =>
      change (⁅iterComm' Q k, iterComm' Q k⁆).map f = P
      rw [Subgroup.map_commutator, ih, hP]
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (iterComm' Q)
  have hanti : Antitone (iterComm' Q) := antitone_nat_of_succ_le (iterComm'_succ_le Q)
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨iterComm' Q i, iterComm'_le Q i, le_antisymm (iterComm'_succ_le Q i) ?_, hmap i⟩
    calc iterComm' Q i = iterComm' Q j := heq
      _ ≤ iterComm' Q (i + 1) := hanti (Nat.succ_le_of_lt h)
  · refine ⟨iterComm' Q j, iterComm'_le Q j, le_antisymm (iterComm'_succ_le Q j) ?_, hmap j⟩
    calc iterComm' Q j = iterComm' Q i := heq.symm
      _ ≤ iterComm' Q (j + 1) := hanti (Nat.succ_le_of_lt h)

end Perfect

section G28Lift

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}

theorem G28InSitu.primeCore {Y : Type} [Group Y] [Finite Y] {T Y₀ V₀ : Subgroup Y} {zb : Y}
    (hS : G28InSitu T Y₀ zb V₀) (W : Subgroup Y) (hW : W ≤ Y₀)
    (hWn : (W.subgroupOf Y₀).Normal) (hWc : Nat.Coprime 3 (Nat.card W)) : W = ⊥ := by
  have hWn' : Y₀ ≤ Subgroup.normalizer (W : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hW).mp hWn
  have h3z : ¬ zb ∈ W := by
    intro hz
    have h1 := Subgroup.orderOf_dvd_natCard W hz
    rw [hS.z_order] at h1
    exact absurd (Nat.Coprime.eq_one_of_dvd hWc h1) (by norm_num)
  rcases hS.trichotomy W hW hWn' with h | h | h
  · exact h
  · rw [eq_bot_iff]
    intro w hw
    obtain ⟨n, rfl⟩ := h hw
    have hcz : Nat.card (Subgroup.zpowers zb) = 3 := by rw [Nat.card_zpowers, hS.z_order]
    by_contra hne
    apply h3z
    have hle : Subgroup.zpowers (zb ^ n) ≤ Subgroup.zpowers zb := Subgroup.zpowers_le.mpr
      (Subgroup.zpow_mem_zpowers zb n)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcz] at hdvd
    have hc3 : Nat.card (Subgroup.zpowers (zb ^ n)) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · exfalso
        rw [Nat.card_zpowers, orderOf_eq_one_iff] at h1
        exact hne (Subgroup.mem_bot.mpr h1)
      · exact h1
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, hc3])
    exact (Subgroup.zpowers_le.mpr hw) (heq ▸ Subgroup.mem_zpowers zb)
  · exact absurd (h hS.z_mem_V) h3z


end G28Lift

end CFSG.AGLEmbedding
