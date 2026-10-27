module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.KCommT

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa : Subgroup G}
  {z b : G}

set_option linter.unusedSectionVars false

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include H W W2

theorem ThCyc.kCommutator_complement {k : G} (hkL : k ∈ L) (hkA : ∀ x ∈ A, k * x * k⁻¹ ∈ A)
    (hodd : Odd (orderOf k)) (hfix : ∀ x ∈ A, k * x * k⁻¹ = x → x = 1) :
    kCommutator (Csub A Aa t) k ⊔ zpowers t = Csub A Aa t ∧
      Disjoint (kCommutator (Csub A Aa t) k) (zpowers t) ∧
      Nat.card (kCommutator (Csub A Aa t) k) = 2 ^ 12 := by
  obtain ⟨hDC, -, -, -, hfac⟩ := H.kCommutator_factorization W W2 (C := Csub A Aa t) rfl hkL hkA
    hodd hfix
  have ht : t ∉ kCommutator (Csub A Aa t) k := H.t_not_mem_kCommutator W W2 hkL hkA hodd
  have hdisj : Disjoint (kCommutator (Csub A Aa t) k) (zpowers t) := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hxD, hxt⟩ := hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxt
    rcases zpow_eq_one_or_self H.sq_t j with h | h
    · rw [h]
      exact one_mem _
    · rw [h] at hxD
      exact absurd hxD ht
  have hsup : kCommutator (Csub A Aa t) k ⊔ zpowers t = Csub A Aa t := by
    refine le_antisymm (sup_le hDC ?_) fun c hc => ?_
    · exact zpowers_le.2 (H.t_mem_inf_centralizer_Aa W W2)
    · obtain ⟨d, hd, e, he, rfl⟩ := hfac c hc
      exact mul_mem (mem_sup_left hd) (mem_sup_right he)
  refine ⟨hsup, hdisj, ?_⟩
  have hcard := H.natCard_Bp_inf_centralizer_Aa W W2
  have ht2 : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers, H.order_two]
  have htC : zpowers t ≤ Csub A Aa t := zpowers_le.2 (H.t_mem_inf_centralizer_Aa W W2)
  let f : kCommutator (Csub A Aa t) k × zpowers t → ↥(Csub A Aa t) := fun p =>
    ⟨(p.1 : G) * p.2, (Csub A Aa t).mul_mem (hDC p.1.2) (htC p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨d, hd⟩, ⟨e, he⟩⟩ ⟨⟨d', hd'⟩, ⟨e', he'⟩⟩ hEq
      simp only [f, Subtype.mk.injEq] at hEq
      have h1 : d'⁻¹ * d = e' * e⁻¹ := by
        calc d'⁻¹ * d = d'⁻¹ * (d * e) * e⁻¹ := by group
          _ = d'⁻¹ * (d' * e') * e⁻¹ := by rw [hEq]
          _ = e' * e⁻¹ := by group
      have hmem : d'⁻¹ * d ∈ kCommutator (Csub A Aa t) k ⊓ zpowers t :=
        ⟨(kCommutator (Csub A Aa t) k).mul_mem ((kCommutator (Csub A Aa t) k).inv_mem hd') hd,
          by rw [h1]; exact (zpowers t).mul_mem he' ((zpowers t).inv_mem he)⟩
      rw [disjoint_iff.1 hdisj, mem_bot] at hmem
      have hdd : d = d' := (inv_mul_eq_one.1 hmem).symm
      subst hdd
      have hee : e = e' := mul_left_cancel hEq
      subst hee
      rfl
    · rintro ⟨c, hc⟩
      obtain ⟨d, hd, e, he, rfl⟩ := hfac c hc
      exact ⟨(⟨d, hd⟩, ⟨e, he⟩), rfl⟩
  have h2 := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod, hcard, ht2] at h2
  omega

end

end CFSG.EvenSporadicStandard.ThStd
