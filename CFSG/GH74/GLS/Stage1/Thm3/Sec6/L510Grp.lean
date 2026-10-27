module

public import CFSG.GH74.GLS.IVK.Lifted.Std6Glue
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Lifted CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

theorem cyc2_square_or_generator {Q : Type} [Group Q] [Finite Q] [IsCyclic Q] (hQ : IsPGroup 2 Q)
    (c : Q) : (∃ y : Q, y * y = c) ∨ ∀ x : Q, x ∈ zpowers c := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  have hc : c ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.2 (hg c)
  obtain ⟨m, rfl⟩ := hc
  rcases Nat.even_or_odd m with ⟨m', hm'⟩ | hodd
  · left
    exact ⟨g ^ m', by rw [← pow_add, hm']⟩
  · right
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    have hcop : (Nat.card Q).Coprime m := by
      rw [hn]
      exact Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hodd)
    obtain ⟨y, hy⟩ := (powCoprime hcop).surjective g
    have hym : y ^ m = g := by simpa [powCoprime_apply] using hy
    obtain ⟨j, rfl⟩ : y ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.2 (hg y)
    have hg_eq : g = (g ^ m) ^ j := by
      calc g = (g ^ j) ^ m := hym.symm
        _ = (g ^ m) ^ j := by rw [← pow_mul, ← pow_mul, mul_comm]
    have hgz : g ∈ zpowers (g ^ m) := by
      have := (zpowers (g ^ m)).pow_mem (Subgroup.mem_zpowers (g ^ m)) j
      rwa [← hg_eq] at this
    intro x
    exact (zpowers_le.2 hgz) (hg x)

theorem comm_Pof_Qof_r1 {G : Type} [Group G] [Finite G] {z : G} {S K : Subgroup G}
    (h : Std6r1 G z S K) {p q : G} (hp : p ∈ Pof S K) (hq : q ∈ Qof S K) : p * q = q * p := by
  have hOK : ⁅p, q⁆ ∈ pPrimeCoreOf 2 K := hq.2.2.2 p hp.2
  have hS : ⁅p, q⁆ ∈ S := by
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem hp.1 hq.1) (S.inv_mem hp.1)) (S.inv_mem hq.1)
  have hbot : S ⊓ pPrimeCoreOf 2 K = ⊥ :=
    M.inf_eq_bot_of_pgroup_odd (std6r1_S_pgroup h) (TwoThin.card_pPrimeCoreOf_odd K)
  have h1 : ⁅p, q⁆ ∈ S ⊓ pPrimeCoreOf 2 K := ⟨hS, hOK⟩
  rw [hbot, Subgroup.mem_bot] at h1
  simp only [commutatorElement_def] at h1
  calc p * q = (p * q * p⁻¹ * q⁻¹) * (q * p) := by group
    _ = q * p := by rw [h1]; group

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510
