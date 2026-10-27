module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkE

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

theorem Pk.no_pocket_tB
    {K : Subgroup P45} (hK : Sl23PocketIn Pk.P0 Pk.tB K) : False := by
  have hKC : K ≤ Pk.CBs := hK.2.1
  have hodd := oddCore_eq_bot_of_subnormal hKC Pk.noOdd_CBs hK.2.2.1
  obtain ⟨hK24, hgen⟩ := sl23_facts hK.2.2.2 hodd
  obtain ⟨U, hU12, hU1, hUmul, hUinv, hUall⟩ := Pk.facts.u
  have hle : K ≤ listSub U := hgen _ fun x hx hx3 =>
    (mem_listSub_iff hU1 hUmul hUinv).2 (hUall x (hKC hx) hx3)
  have h1 := Subgroup.card_le_of_le hle
  have h2 := card_listSub_le hU1 hUmul hUinv
  omega

theorem isI4PlusIn_of_conj_tA
    {y c : P45} (hc : c ∈ QP45.originalSubgroup)
    (h : c * Certificates.P43Twin.tA () * c⁻¹ = y) : IsI4PlusIn QP45.originalSubgroup y := by
  subst h
  refine ⟨?_, ?_⟩
  · have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective Pk.tA
    simpa [MulAut.conj_apply, Pk.orderOf_tA] using this
  · have hp := Pk.sl23Pocket_KA.conjugate c⁻¹
    rw [Pk.conjugate_self_of_mem (QP45.originalSubgroup.inv_mem hc), inv_inv] at hp
    exact ⟨_, hp⟩

theorem not_isI4PlusIn_of_conj_tB
    {y c : P45} (hc : c ∈ QP45.originalSubgroup)
    (h : c * Certificates.P43Twin.tB () * c⁻¹ = y) : ¬ IsI4PlusIn QP45.originalSubgroup y := by
  subst h
  rintro ⟨-, K, hK⟩
  have hp := hK.conjugate c
  rw [Pk.conjugate_self_of_mem hc, show c⁻¹ * (c * Pk.tB * c⁻¹) * c = Pk.tB by group] at hp
  exact Pk.no_pocket_tB hp

end CFSG.OddStandard.SmallF3.Omega
