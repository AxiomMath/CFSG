module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.ThreeLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseCore

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Close

open Subgroup
open scoped commutatorElement

section Setup

variable {X : Type} [Group X] [Finite X]

abbrev proj (X : Type) [Group X] : X →* X ⧸ CFSG.oddCore X := QuotientGroup.mk' (CFSG.oddCore X)

theorem proj_surjective (X : Type) [Group X] : Function.Surjective (proj X) :=
  QuotientGroup.mk'_surjective _

structure KernelData (d : ThreeLocalData X) where
  K : Subgroup X
  normal : K.Normal
  odd_le : CFSG.oddCore X ≤ K
  comm_mem : ∀ c : X, ⁅c, d.t⁆ ∈ K
  comm_le : ⁅K, K⁆ ≤ centralizer (CFSG.oddCore X : Set X)

namespace KernelData

variable {d : ThreeLocalData X} (kd : KernelData d)

@[expose] def Kt : Subgroup (X ⧸ CFSG.oddCore X) := kd.K.map (proj X)

theorem Kt_normal : kd.Kt.Normal := by
  have := kd.normal
  exact Subgroup.Normal.map this (proj X) (proj_surjective X)

theorem comap_le {A : Subgroup (X ⧸ CFSG.oddCore X)} (hA : A ≤ kd.Kt) :
    A.comap (proj X) ≤ kd.K := by
  intro x hx
  obtain ⟨k, hk, hkx⟩ := hA hx
  have h1 : k⁻¹ * x ∈ CFSG.oddCore X := by
    have : (QuotientGroup.mk k : X ⧸ CFSG.oddCore X) = QuotientGroup.mk x := hkx
    exact (QuotientGroup.eq).1 this
  have h2 : k⁻¹ * x ∈ kd.K := kd.odd_le h1
  have := kd.K.mul_mem hk h2
  simpa using this

theorem commutator_mem (c : X ⧸ CFSG.oddCore X) :
    ⁅c, (QuotientGroup.mk d.t : X ⧸ CFSG.oddCore X)⁆ ∈ kd.Kt := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
  exact ⟨⁅c, d.t⁆, kd.comm_mem c, by simp [commutatorElement_def]⟩

theorem inf_ne_bot {N : Subgroup (X ⧸ CFSG.oddCore X)} (hN : N.Normal)
    (hC : ∀ x : X ⧸ CFSG.oddCore X, (∀ n ∈ N, x * n = n * x) → x = 1) : kd.Kt ⊓ N ≠ ⊥ := by
  intro h
  have ht1 : (QuotientGroup.mk d.t : X ⧸ CFSG.oddCore X) = 1 := by
    apply hC
    intro n hn
    have hmem : ⁅n, (QuotientGroup.mk d.t : X ⧸ CFSG.oddCore X)⁆ ∈ kd.Kt ⊓ N := by
      refine ⟨kd.commutator_mem n, ?_⟩
      have h1 := hN.conj_mem n⁻¹ (N.inv_mem hn) (QuotientGroup.mk d.t)
      have h2 := N.mul_mem hn h1
      convert h2 using 1
      simp [commutatorElement_def, mul_assoc]
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem.symm
  have := orderOf_mk_oddCore_eq_two d.t_ord
  rw [ht1, orderOf_one] at this
  omega

end KernelData

theorem card_centralizer_mk_t (d : ThreeLocalData X) (hM10 : Nat.card M10 = 720) :
    Nat.card ↥(centralizer ({(QuotientGroup.mk d.t : X ⧸ CFSG.oddCore X)} :
      Set (X ⧸ CFSG.oddCore X))) = 1440 := by
  obtain ⟨e⟩ := d.cen_iso
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, hM10]
  have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [this]

omit [Finite X] in
theorem card_map_proj_mul (F : Subgroup X) :
    Nat.card (F.map (proj X)) * Nat.card (CFSG.oddCore X ⊓ F : Subgroup X) = Nat.card F := by
  have h1 := Subgroup.relIndex_ker (K := F) (proj X)
  have h2 := Subgroup.relIndex_mul_card (H := (proj X).ker) (K := F)
  rw [QuotientGroup.ker_mk'] at h1 h2
  rw [← h1]
  exact h2

theorem exists_sylow_five_ge (d : ThreeLocalData X) {P : Subgroup X} (hP : IsPGroup 5 P)
    (hPC : P ≤ centralizer ({d.f} : Set X)) :
    ∃ F : Subgroup X, P ≤ F ∧ F ≤ centralizer ({d.f} : Set X) ∧ Nat.card F = 25 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set C := centralizer ({d.f} : Set X) with hC
  have hP' : IsPGroup 5 (P.subgroupOf C) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  obtain ⟨S, hS⟩ := hP'.exists_le_sylow
  refine ⟨(S : Subgroup C).map C.subtype, ?_, Subgroup.map_subtype_le _, ?_⟩
  · intro x hx
    exact ⟨⟨x, hPC hx⟩, hS hx, rfl⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity]
    have hpos : Nat.card C ≠ 0 := Nat.card_pos.ne'
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization (p := 5) (k := 2) (by norm_num) hpos).1
      (show 5 ^ 2 ∣ Nat.card C by norm_num; exact d.f_five.1)
    have h3 : ¬ 3 ≤ (Nat.card C).factorization 5 := fun h =>
      d.f_five.2 (by
        have := (Nat.Prime.pow_dvd_iff_le_factorization (p := 5) (k := 3)
          (by norm_num) hpos).2 h
        norm_num at this
        exact this)
    have : (Nat.card C).factorization 5 = 2 := by omega
    rw [this]
    norm_num

end Setup

end CFSG.EvenSporadicStandard.RuStd.S2.Close
