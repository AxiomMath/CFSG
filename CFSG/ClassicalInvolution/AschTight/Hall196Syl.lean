module

public import CFSG.ClassicalInvolution.AschTight.WreathedData

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

theorem isSylow2In_inf_of_le_normalizer (S : Sylow 2 G) {H : Subgroup G}
    (hSH : (S : Subgroup G) ≤ Subgroup.normalizer (H : Set G)) :
    IsSylow2In ((S : Subgroup G) ⊓ H) H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨inf_le_right, S.isPGroup'.to_inf_left, fun T hTH hT2 hle => ?_⟩
  obtain ⟨c, hc, hcT⟩ := exists_conj_le_of_sylow_le S
    (le_sup_right : (S : Subgroup G) ≤ H ⊔ (S : Subgroup G)) (hTH.trans le_sup_left) hT2
  have hcinv : c⁻¹ ∈ ((H ⊔ (S : Subgroup G) : Subgroup G) : Set G) := Subgroup.inv_mem _ hc
  rw [Subgroup.coe_mul_of_right_le_normalizer_left H (S : Subgroup G) hSH] at hcinv
  obtain ⟨h, hh, s, hs, hhs⟩ := Set.mem_mul.mp hcinv
  have h1 : T ≤ conjSub c⁻¹ (S : Subgroup G) := by
    have := conjSub_mono (n := c⁻¹) hcT
    rwa [conjSub_inv_conjSub] at this
  have h2 : conjSub c⁻¹ (S : Subgroup G) = conjSub h (S : Subgroup G) := by
    rw [← hhs, conjSub_mul, conjSub_eq_self_of_mem hs]
  have h3 : T ≤ conjSub h ((S : Subgroup G) ⊓ H) := by
    intro x hx
    have hx1 : x ∈ conjSub h (S : Subgroup G) := h2 ▸ h1 hx
    rw [mem_conjSub_iff] at hx1 ⊢
    exact ⟨hx1, H.mul_mem (H.mul_mem (H.inv_mem hh) (hTH hx)) hh⟩
  have hcard : Nat.card T ≤ Nat.card ↥((S : Subgroup G) ⊓ H) := by
    calc Nat.card T ≤ Nat.card ↥(conjSub h ((S : Subgroup G) ⊓ H)) := Subgroup.card_le_of_le h3
      _ = _ := Subgroup.card_map_of_injective (MulAut.conj h).injective
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

@[expose] def sylowOfIsSylow2In {V Y : Subgroup G} (h : IsSylow2In V Y) : Sylow 2 ↥Y where
  toSubgroup := V.subgroupOf Y
  isPGroup' := h.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hVQ : V ≤ Q.map Y.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hle
    have := h.2.2 (Q.map Y.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
    rw [← Subgroup.comap_map_eq_self_of_injective Y.subtype_injective Q, this]
    rfl

theorem le_classicalInvolutionOddCore {H : Type*} [Group H] {N : Subgroup H} [hN : N.Normal]
    (hodd : Odd (Nat.card N)) : N ≤ classicalInvolutionOddCore H :=
  le_sSup ⟨hN, hodd⟩

theorem sup_eq_oddCoreOf_sup_of_isCyclic {Y P W : Subgroup G} (hP : IsSylow2In P Y)
    (hPc : IsCyclic P) (hPW : P ≤ W) : W ⊔ Y = oddCoreOf Y ⊔ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOY : oddCoreOf Y ≤ Y := Subgroup.map_subtype_le _
  refine le_antisymm (sup_le le_sup_right ?_) (sup_le (hOY.trans le_sup_right) le_sup_left)
  set P' : Sylow 2 ↥Y := sylowOfIsSylow2In hP with hP'
  have hP'P : (P' : Subgroup ↥Y) = P.subgroupOf Y := rfl
  have hP'c : IsCyclic (P' : Subgroup ↥Y) := by
    rw [hP'P]
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hP.1).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hP.1).symm.surjective
  have hkey : ∀ N : Subgroup ↥Y, N.Normal → N.IsComplement' (P' : Subgroup ↥Y) →
      Y ≤ oddCoreOf Y ⊔ W := by
    intro N hNn hcomp
    have hNodd : Odd (Nat.card N) := by
      have hc := hcomp.card_mul_card
      rw [Sylow.card_eq_multiplicity] at hc
      set e := (Nat.card ↥Y).factorization 2 with he
      rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      intro h2
      have h3 : 2 ^ (e + 1) ∣ Nat.card ↥Y := by
        rw [← hc, pow_succ, mul_comm (2 ^ e) 2]
        exact Nat.mul_dvd_mul_right h2 _
      exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Nat.prime_two h3
    have hNO : N ≤ classicalInvolutionOddCore ↥Y := le_classicalInvolutionOddCore hNodd
    have htop := hcomp.sup_eq_top
    intro y hy
    have hy' : (⟨y, hy⟩ : ↥Y) ∈ N ⊔ (P' : Subgroup ↥Y) := htop ▸ Subgroup.mem_top _
    have hmap : (N ⊔ (P' : Subgroup ↥Y)).map Y.subtype ≤ oddCoreOf Y ⊔ W := by
      rw [Subgroup.map_sup]
      refine sup_le_sup (Subgroup.map_mono hNO) ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hPW (Subgroup.mem_subgroupOf.mp (hP'P ▸ hx))
    exact hmap ⟨⟨y, hy⟩, hy', rfl⟩
  by_cases h2 : 2 ∣ Nat.card ↥Y
  · have hmin : (Nat.card ↥Y).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
    exact hkey _ inferInstance (IsCyclic.isComplement' hmin hP'c)
  ·
    have hodd : Odd (Nat.card (⊤ : Subgroup ↥Y)) := by
      rw [Subgroup.card_top, Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      exact h2
    have hle := le_classicalInvolutionOddCore (N := (⊤ : Subgroup ↥Y)) hodd
    intro y hy
    exact Subgroup.mem_sup_left ⟨⟨y, hy⟩, hle (Subgroup.mem_top _), rfl⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
