module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

theorem exists_normal_pComplement_centralizer {p : ℕ} (hp : p.Prime) {X : Type} [Group X]
    [Finite X] {D : Subgroup X} (_hD : IsMulCommutative D)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set X))) :
    ∃ Q : Subgroup X, Q ≤ centralizer (D : Set X) ∧ p.Coprime (Nat.card Q) ∧
      centralizer (D : Set X) ≤ normalizer (Q : Set X) ∧
      ∀ g ∈ centralizer (D : Set X), p.Coprime (orderOf g) → g ∈ Q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set C : Subgroup X := centralizer (D : Set X) with hC
  obtain ⟨S, hS⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hcentral : ∀ s ∈ (S : Subgroup C), ∀ x : C, x * s = s * x := by
    intro s hs x
    rw [hS] at hs
    have hsD : (s : X) ∈ D := hs
    have hx : (x : X) ∈ centralizer (D : Set X) := x.2
    exact Subtype.ext (by simpa [mul_assoc] using (mem_centralizer_iff.mp hx (s : X) hsD).symm)
  have hP : normalizer (S : Set C) ≤ centralizer (S : Set C) := by
    intro x _
    rw [mem_centralizer_iff]
    intro s hs
    exact (hcentral s hs x).symm
  obtain ⟨K, hKn, hnd, hKmem⟩ : ∃ K : Subgroup C, K.Normal ∧ ¬ p ∣ Nat.card K ∧
      ∀ c : C, p.Coprime (orderOf c) → c ∈ K := by
    refine ⟨(MonoidHom.transferSylow S hP).ker, MonoidHom.normal_ker _,
      MonoidHom.not_dvd_card_ker_transferSylow S hP, fun c hc => ?_⟩
    rw [MonoidHom.mem_ker]
    set τ : S := MonoidHom.transferSylow S hP c with hτ
    have hτpow : τ ^ orderOf c = 1 := by
      rw [hτ, ← map_pow, pow_orderOf_eq_one, map_one]
    obtain ⟨k, hk⟩ := S.isPGroup' τ
    have h1 : orderOf τ ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf τ ∣ orderOf c := orderOf_dvd_of_pow_eq_one hτpow
    have h3 : Nat.Coprime (orderOf τ) (orderOf c) :=
      Nat.Coprime.coprime_dvd_left h1 (hc.pow_left k)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h3 h2)
  have key : ∀ (g' : X), g' ∈ C → ∀ q' : X, q' ∈ K.map C.subtype →
      g' * q' * g'⁻¹ ∈ K.map C.subtype := by
    intro g' hg' q' hq'
    rw [Subgroup.mem_map] at hq' ⊢
    obtain ⟨k, hk, rfl⟩ := hq'
    exact ⟨⟨g', hg'⟩ * k * ⟨g', hg'⟩⁻¹, hKn.conj_mem k hk _, rfl⟩
  refine ⟨K.map C.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
  · intro g hg
    rw [mem_normalizer_iff]
    intro q
    refine ⟨key g hg q, fun hq => ?_⟩
    have := key g⁻¹ (inv_mem hg) _ hq
    simpa [mul_assoc] using this
  · intro g hg hgo
    refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩, hKmem _ ?_, rfl⟩
    rw [Subgroup.orderOf_mk]
    exact hgo

end CFSG.LocalAnalysis.RankThreeTheoremC
