module

import CFSG.LocalAnalysis.GH72.Sec4M0
public import CFSG.LocalAnalysis.GH72.DDStructure
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH72

open Subgroup

namespace G3cF

variable {G : Type*} [Group G] [Finite G]

theorem sup_twoResidualOf_eq {K T : Subgroup G} (hT : ABGLocalTools.IsSylowOf 2 T K) :
    T ⊔ O2 K = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK : T ≤ K := hT.le
  have hle : T ⊔ O2 K ≤ K := sup_le hTK (twoResidualOf_le_self K)
  obtain ⟨n, hn⟩ := exists_relIndex_twoResidualOf K
  have h1 := relIndex_mul_relIndex T (T ⊔ O2 K) K le_sup_left hle
  have h2 := relIndex_mul_relIndex (O2 K) (T ⊔ O2 K) K le_sup_right hle
  have hodd : ¬ 2 ∣ T.relIndex K := (ABGLocalTools.isSylowOf_iff.1 hT).2.2
  have hdvd₁ : (T ⊔ O2 K).relIndex K ∣ T.relIndex K := ⟨_, by rw [← h1, mul_comm]⟩
  have hdvd₂ : (T ⊔ O2 K).relIndex K ∣ 2 ^ n := ⟨_, by rw [← hn, ← h2, mul_comm]⟩
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd₂
  have hm0 : m = 0 := by
    by_contra h
    apply hodd
    exact (dvd_pow_self 2 h).trans (hm ▸ hdvd₁)
  rw [hm0, pow_zero] at hm
  exact le_antisymm hle (relIndex_eq_one.1 hm)

omit [Finite G] in
theorem sup_inf_eq_inf_sup {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂) {N : Subgroup G}
    (hS₂N : S₂ ≤ N) : S ⊓ N = (S₁ ⊓ N) ⊔ S₂ := by
  refine le_antisymm (fun g hg => ?_)
    (sup_le (inf_le_inf_right N hd.le_left) (le_inf hd.le_right hS₂N))
  obtain ⟨hgS, hgN⟩ := mem_inf.1 hg
  obtain ⟨x, hx, y, hy, rfl⟩ := hd.mem_iff.1 hgS
  have hxN : x ∈ N := by
    have h := N.mul_mem hgN (N.inv_mem (hS₂N hy))
    rwa [mul_inv_cancel_right] at h
  exact mul_mem (mem_sup_left (mem_inf.2 ⟨hx, hxN⟩)) (mem_sup_right hy)

omit [Finite G] in
theorem bar_self' (H : Subgroup G) : bar H H = ⊤ := by
  rw [bar, subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem bar_inf_bar_twoResidualOf_eq_bot {M P : Subgroup G} (hPO : P ⊓ O2 M = ⊥) :
    bar M P ⊓ bar M (O2 M) = ⊥ := by
  refine eq_bot_iff.2 fun y hy => ?_
  obtain ⟨⟨p, hpM⟩, hp, rfl⟩ := (mem_inf.1 hy).1
  obtain ⟨⟨h, hhM⟩, hh, hph⟩ := (mem_inf.1 hy).2
  have hp' : p ∈ P := hp
  have hh' : h ∈ O2 M := hh
  have hO : h⁻¹ * p ∈ O M := G4b.inv_mul_mem_O_of_mk_eq hph
  have hpO : p ∈ O2 M := by
    have h1 : h * (h⁻¹ * p) ∈ O2 M := mul_mem hh' (G4b.O_le_O2 M hO)
    rwa [mul_inv_cancel_left] at h1
  have hp1 : p = 1 := by
    have h1 : p ∈ P ⊓ O2 M := mem_inf.2 ⟨hp', hpO⟩
    rw [hPO] at h1
    exact (mem_bot).1 h1
  rw [mem_bot]
  have hpe : (⟨p, hpM⟩ : M) = 1 := Subtype.ext hp1
  rw [hpe, map_one]

end G3cF

end CFSG.GH72
