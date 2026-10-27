module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MAutM

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem card_sylow_two {M : Type*} [Group M] [Finite M] {P K : Subgroup M}
    (h : IsSylowOf 2 P K) {k : ℕ} (hk : 2 ^ k ∣ Nat.card K) (hk1 : ¬ 2 ^ (k + 1) ∣ Nat.card K) :
    Nat.card P = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := h
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  have h1 := Q.pow_dvd_card_of_pow_dvd_card hk
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 Q.isPGroup'
  have h2 : Nat.card (Q : Subgroup K) ∣ Nat.card K := Subgroup.card_subgroup_dvd_card _
  rw [hm] at h1 h2 ⊢
  have hkm : k ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  have hmk : m ≤ k := by
    by_contra hc
    exact hk1 ((pow_dvd_pow 2 (by omega)).trans h2)
  rw [le_antisymm hmk hkm]

theorem not_pCfg_of_noP {M : Type*} [Group M] [Finite M] {R S₀ : Subgroup M} (hS₀R : S₀ ≤ R)
    {p k : ℕ} (hk : 2 ^ k ∣ Nat.card S₀) (hk1 : ¬ 2 ^ (k + 1) ∣ Nat.card S₀)
    (hstmt : ∀ P W : Subgroup M, P ≤ S₀ → W ≤ R → Nat.card P = 2 ^ k → IsPGroup p W →
      P ≤ normalizer (W : Set M) → W = ⊥) :
    ¬ N1PCfg p (S₀.subgroupOf R) := by
  rintro ⟨P, W, hP, hWp, hWne, hPW⟩
  have hPI : P ≤ S₀.subgroupOf R := by
    obtain ⟨Q, rfl⟩ := hP
    exact map_subtype_le _
  have hIc : Nat.card (S₀.subgroupOf R) = Nat.card S₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀R).toEquiv
  have hPc : Nat.card P = 2 ^ k := card_sylow_two hP (hIc ▸ hk) (hIc ▸ hk1)
  have h := hstmt (P.map R.subtype) (W.map R.subtype) ?_ ?_ ?_ ?_ ?_
  · exact hWne ((Subgroup.map_eq_bot_iff_of_injective W R.subtype_injective).1 h)
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hPI hx)
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective R.subtype_injective]
    exact hPc
  · exact hWp.map _
  · exact (Subgroup.map_mono hPW).trans (Subgroup.le_normalizer_map _)

theorem noN1_of_noP {M : Type} [Group M] [Finite M] {A : Subgroup M} {Y : Type} [Group Y]
    (e : Y ≃* ↥A) (hc : center ↥A = ⊥) (hcard : Nat.card (MulAut ↥A) ≤ 2 * Nat.card ↥A)
    {k : ℕ} (hk : 2 ^ k ∣ Nat.card A) (hk1 : ¬ 2 ^ (k + 1) ∣ Nat.card A)
    (hstmt : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P W : Subgroup M, P ≤ A → W ≤ A →
      Nat.card P = 2 ^ k → IsPGroup p W → P ≤ normalizer (W : Set M) → W = ⊥)
    {p : ℕ} {b : MulAut Y} {R₀ : Subgroup Y} : ¬ N1Config Y p b R₀ := by
  intro hN1
  have hpc := pCfg_top_of_n1_equiv e hc hcard hN1
  obtain ⟨hp, hp2, -⟩ := hN1
  rw [← Subgroup.subgroupOf_self] at hpc
  exact not_pCfg_of_noP le_rfl hk hk1 (hstmt p hp hp2) hpc

theorem noN1_of_noP_autModel {G : Type*} [Group G] [Finite G] {Y : Type} [Group Y] [Finite Y]
    (M : CFSG.GH74.KGroups.AutModel Y G) (hPA : M.P ≤ M.A) (hc : center Y = ⊥) {k : ℕ}
    (hk : 2 ^ k ∣ Nat.card M.P) (hk1 : ¬ 2 ^ (k + 1) ∣ Nat.card M.P)
    (hstmt : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P W : Subgroup G, P ≤ M.P → W ≤ M.A →
      Nat.card P = 2 ^ k → IsPGroup p W → P ≤ normalizer (W : Set G) → W = ⊥)
    {p : ℕ} {b : MulAut Y} {R₀ : Subgroup Y} : ¬ N1Config Y p b R₀ := by
  intro hN1
  have hpc := pCfg_of_n1_aut M.Φ.symm (map_P_eq_innSub M hPA) hc hN1
  obtain ⟨hp, hp2, -⟩ := hN1
  exact not_pCfg_of_noP hPA hk hk1 (hstmt p hp hp2) hpc

theorem noN1_of_noP_aut {G : Type*} [Group G] [Finite G] {R S₀ : Subgroup G} (hS₀R : S₀ ≤ R)
    {Y : Type} [Group Y] [Finite Y] (Θ : ↥R ≃* MulAut Y)
    (hI : (S₀.subgroupOf R).map Θ.toMonoidHom = innSub Y) (hc : center Y = ⊥) {k : ℕ}
    (hk : 2 ^ k ∣ Nat.card S₀) (hk1 : ¬ 2 ^ (k + 1) ∣ Nat.card S₀)
    (hstmt : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P W : Subgroup G, P ≤ S₀ → W ≤ R →
      Nat.card P = 2 ^ k → IsPGroup p W → P ≤ normalizer (W : Set G) → W = ⊥)
    {p : ℕ} {b : MulAut Y} {R₀ : Subgroup Y} : ¬ N1Config Y p b R₀ := by
  intro hN1
  have hpc := pCfg_of_n1_aut Θ hI hc hN1
  obtain ⟨hp, hp2, -⟩ := hN1
  exact not_pCfg_of_noP hS₀R hk hk1 (hstmt p hp hp2) hpc

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

end
