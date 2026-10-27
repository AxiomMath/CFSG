module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.GH74.Generic.BProg.B2.T4ElimE8Core

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem y7c_card_invariant_mod_seven {M : Type} [Group M] [Finite M] {σ : MulAut M}
    (hσ : σ ^ 7 = 1) (hfpf : ∀ m : M, σ m = m → m = 1) {V : Subgroup M}
    (hV : ∀ v ∈ V, σ v ∈ V) : Nat.card ↥V % 7 = 1 := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  let S : Finset M := (V : Set M).toFinset
  have hS : ∀ s ∈ S, σ s ∈ S := by
    intro s hs
    simp only [S, Set.mem_toFinset] at hs ⊢
    exact hV s hs
  have h := CFSG.GH74.Generic.BProg.B2.T4.T4ElimE8.card_modEq_fix (R := M) hσ S hS
  have hfix : S.filter (fun s => σ s = s) = {1} := by
    ext s
    simp only [S, Finset.mem_filter, Set.mem_toFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hs⟩; exact hfpf s hs
    · rintro rfl; exact ⟨V.one_mem, map_one σ⟩
  rw [hfix, Finset.card_singleton] at h
  have hcardS : S.card = Nat.card ↥V := by
    rw [Nat.card_eq_fintype_card]
    simp [S, Set.toFinset_card]
  rw [hcardS] at h
  simpa [Nat.ModEq] using h

theorem y7c_card_invariant_cases {M : Type} [Group M] [Finite M] (hM : IsE 6 M) {σ : MulAut M}
    (hσ : σ ^ 7 = 1) (hfpf : ∀ m : M, σ m = m → m = 1) {V : Subgroup M}
    (hV : ∀ v ∈ V, σ v ∈ V) : Nat.card ↥V = 1 ∨ Nat.card ↥V = 8 ∨ Nat.card ↥V = 64 := by
  have hmod := y7c_card_invariant_mod_seven hσ hfpf hV
  have hcardM : Nat.card M = 2 ^ 6 := by
    unfold IsE at hM
    exact hM.2
  have hdvd : Nat.card ↥V ∣ 2 ^ 6 := by
    rw [← hcardM]
    exact Subgroup.card_subgroup_dvd_card V
  obtain ⟨k, hk, hVk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hkmod : 2 ^ k % 7 = 1 := by
    rw [← hVk]
    exact hmod
  interval_cases k
  · left; simpa using hVk
  · exfalso; norm_num at hkmod
  · exfalso; norm_num at hkmod
  · right; left; simpa using hVk
  · exfalso; norm_num at hkmod
  · exfalso; norm_num at hkmod
  · right; right; simpa using hVk

end CFSG.OddStandard.HigherRank.YamadaG23
