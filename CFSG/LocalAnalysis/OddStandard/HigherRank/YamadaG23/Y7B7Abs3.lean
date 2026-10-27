module

public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {G : Type} [Group G]

theorem y7b_relIndex_eq_six {X K : Subgroup G} (ρ : ↥X →* Equiv.Perm (Fin 3))
    (hs : Function.Surjective ρ) (hker : ∀ x : ↥X, ρ x = 1 ↔ (x : G) ∈ K) :
    K.relIndex X = 6 := by
  have hsub : K.subgroupOf X = ρ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact (hker x).symm
  have hcard : K.relIndex X = Nat.card ρ.range := by
    rw [Subgroup.relIndex, hsub, Subgroup.index_ker]
  rw [hcard, MonoidHom.range_eq_top.mpr hs, Subgroup.card_top, Nat.card_perm,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem y7b_perm3_surj_of_relIndex {X N K : Subgroup G} (hNX : N ≤ X) (hKN : K ≤ N)
    (ρ : ↥X →* Equiv.Perm (Fin 3))
    (hker : ∀ n : ↥X, (n : G) ∈ N → (ρ n = 1 ↔ (n : G) ∈ K)) (h6 : K.relIndex N = 6) :
    ∀ σ : Equiv.Perm (Fin 3), ∃ n : ↥X, (n : G) ∈ N ∧ ρ n = σ := by
  let ρ' : ↥N →* Equiv.Perm (Fin 3) := ρ.comp (Subgroup.inclusion hNX)
  have hker' : K.subgroupOf N = ρ'.ker := by
    ext n
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact (hker ⟨n, hNX n.2⟩ n.2).symm
  have hcard : Nat.card ρ'.range = 6 := by
    rw [← Subgroup.index_ker ρ', ← hker']
    simpa only [Subgroup.relIndex] using h6
  have htop : ρ'.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  intro σ
  have hmem : σ ∈ ρ'.range := by rw [htop]; exact Subgroup.mem_top σ
  rw [MonoidHom.mem_range] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact ⟨⟨n, hNX n.2⟩, n.2, hn⟩

private lemma y7b_perm3_sq_conj (σ : Equiv.Perm (Fin 3)) (hσ : σ * σ = 1)
    (h : (σ * (finRotate 3 * σ * (finRotate 3)⁻¹)) *
        (σ * (finRotate 3 * σ * (finRotate 3)⁻¹)) = 1) : σ = 1 := by
  revert σ
  decide

theorem y7b_perm3_normal_triv {P : Type*} [Group P] (ρ : P →* Equiv.Perm (Fin 3))
    (hρ : Function.Surjective ρ) (Y : Subgroup P) [Y.Normal] (hY : ∀ y ∈ Y, ρ y ^ 2 = 1) :
    ∀ y ∈ Y, ρ y = 1 := by
  intro y hy
  by_contra hne
  obtain ⟨n, hn⟩ := hρ (finRotate 3)
  have hconj : n * y * n⁻¹ ∈ Y := (inferInstance : Y.Normal).conj_mem y hy n
  have hprod : y * (n * y * n⁻¹) ∈ Y := Y.mul_mem hy hconj
  have h2 : (ρ y * (finRotate 3 * ρ y * (finRotate 3)⁻¹)) ^ 2 = 1 := by
    have h3 := hY (y * (n * y * n⁻¹)) hprod
    simpa only [map_mul, map_inv, hn] using h3
  have hσ : ρ y * ρ y = 1 := by
    have h := hY y hy
    rwa [pow_two] at h
  have hτ : (ρ y * (finRotate 3 * ρ y * (finRotate 3)⁻¹)) *
      (ρ y * (finRotate 3 * ρ y * (finRotate 3)⁻¹)) = 1 := by
    rwa [pow_two] at h2
  exact hne (y7b_perm3_sq_conj (ρ y) hσ hτ)

end CFSG.OddStandard.HigherRank.YamadaG23
