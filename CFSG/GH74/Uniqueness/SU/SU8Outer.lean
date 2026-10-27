module

public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.GH74.Uniqueness.SU.SU4Defs

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms

namespace Outer

variable {Hb : Type} [Group Hb] [Finite Hb]

theorem forall_inner_of_sylow_centralizes (K : Subgroup Hb) [K.Normal]
    (hK : BenderType ↥K 2 1 1) {S : Subgroup Hb} (hS : IsSylowIn ⊤ S) (P : Sylow 2 ↥K)
    (hP : ∀ s ∈ S, ∀ x : ↥K, x ∈ (P : Subgroup ↥K) → s * (x : Hb) * s⁻¹ = x) (h : Hb) :
    ∃ k : ↥K, ∀ x : ↥K, h * (x : Hb) * h⁻¹ = (k : Hb) * x * (k : Hb)⁻¹ := by
  let φ : Hb →* MulAut ↥K := MulAut.conjNormal
  let ψ : Hb →* Outer ↥K := (QuotientGroup.mk' (inner ↥K)).comp φ
  have hSker : S ≤ ψ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker]
    obtain ⟨r, -, hr⟩ := hK.lemma_3_6_a P (φ s) (fun x hx => by
      apply Subtype.ext
      have := hP s hs x hx
      simpa [φ, MulAut.conjNormal_apply] using this)
    have hin : φ s ∈ inner ↥K := ⟨r, by
      apply MulEquiv.ext
      intro k
      rw [hr k]
      simp [MulAut.conj_apply]⟩
    exact (QuotientGroup.eq_one_iff (φ s)).mpr hin
  have hcard : Nat.card (Outer ↥K) = 2 := hK.outer_linear.2
  have h1 : ψ.ker.index = Nat.card ψ.range := Subgroup.index_ker ψ
  have h2 : Nat.card ψ.range ∣ 2 := hcard ▸ Subgroup.card_subgroup_dvd_card ψ.range
  have h3 : ψ.ker.index ∣ S.index := Subgroup.index_dvd_of_le hSker
  have hodd : Odd S.index := by
    have := hS.2.2
    rwa [Subgroup.relIndex_top_right] at this
  have h4 : ψ.ker.index ∣ 2 := h1 ▸ h2
  have h5 : ψ.ker.index = 1 := by
    have hc : Nat.Coprime ψ.ker.index S.index := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h | h
      · rw [h]; exact Nat.coprime_one_left _
      · rw [h]; exact (Nat.coprime_two_left.mpr hodd)
    exact Nat.Coprime.eq_one_of_dvd hc h3
  have hker : ψ.ker = ⊤ := Subgroup.index_eq_one.mp h5
  have hmem : h ∈ ψ.ker := by rw [hker]; trivial
  rw [MonoidHom.mem_ker] at hmem
  obtain ⟨k, hk⟩ := (QuotientGroup.eq_one_iff (φ h)).mp hmem
  refine ⟨k, fun x => ?_⟩
  have := congrArg (fun σ : MulAut ↥K => ((σ x : ↥K) : Hb)) hk
  simpa [φ, MulAut.conjNormal_apply, MulAut.conj_apply] using this.symm

end Outer

end CFSG.GH74.Uniqueness.SU.SU8
