module

public import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
public import CFSG.FeitThompson.Local.ComplementFixedFreeSpecialization
public import CFSG.FeitThompson.OddOrder.FrobeniusKernelContainsCentralizers

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] {H E U B : Subgroup L}

theorem le_of_isMulCommutative_of_coprime_natCard [Finite L] [Group.IsSolvable L] [H.Normal]
    [IsMulCommutative U] (hHE : H.IsComplement' E) (hHall : (Nat.card H).Coprime H.index)
    (hCH : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set L) = ⊥)
    (hH : H ≠ ⊥) (hU : U ≠ ⊥) (hB : B ≠ ⊥)
    (hBU : B ≤ normalizer (U : Set L)) (hUB : Disjoint U B)
    (hCU : ∀ b ∈ B, b ≠ 1 → U ⊓ centralizer ({b} : Set L) = ⊥)
    (hcop : (Nat.card H).Coprime (Nat.card B)) :
    U ≤ H := by
  by_cases hUH : U ⊓ H = ⊥
  ·
    exfalso
    set A : Subgroup L := U ⊔ B with hA
    have hUA : U ≤ A := le_sup_left
    have hBA : B ≤ A := le_sup_right
    have hdisjUH : Disjoint U H := disjoint_iff.2 hUH
    have hdisjHB : Disjoint H B := Subgroup.disjoint_of_coprime_natCard hcop
    have hUdvd : Nat.card U ∣ H.index := by
      have h1 : H.relIndex U = Nat.card U := by
        rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.2 hdisjUH.symm, Subgroup.index_bot]
      rw [← h1]
      exact Subgroup.relIndex_dvd_index_of_normal H U
    have hcopU : (Nat.card H).Coprime (Nat.card U) := hHall.coprime_dvd_right hUdvd
    have hcardA : Nat.card ↥A = Nat.card U * Nat.card B := by
      have hcoe : ((A : Subgroup L) : Set L) = (U : Set L) * (B : Set L) :=
        Subgroup.coe_mul_of_right_le_normalizer_left U B hBU
      have h1 := natCard_mul_mul_natCard_inf U B
      rw [disjoint_iff.1 hUB, Subgroup.card_bot, mul_one] at h1
      rw [← h1, ← hcoe, SetLike.coe_sort_coe]
    have hAnorm : A ≤ normalizer (U : Set L) := sup_le U.le_normalizer hBU
    have hUnormal : (U.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hAnorm
    have hcardU : Nat.card ↥(U.subgroupOf A) = Nat.card U :=
      Nat.card_congr (subgroupOfEquivOfLe hUA).toEquiv
    have hcardB : Nat.card ↥(B.subgroupOf A) = Nat.card B :=
      Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv
    have hcompl : (U.subgroupOf A).IsComplement' (B.subgroupOf A) := by
      refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
      · rw [hcardU, hcardB, hcardA]
      · rw [Subgroup.disjoint_def]
        intro x hx hx'
        rw [Subgroup.mem_subgroupOf] at hx hx'
        exact Subtype.ext (Subgroup.disjoint_def.1 hUB hx hx')
    set ρ : ↥A →* MulAut ↥H := MulAut.conjNormal.comp A.subtype with hρ
    have hρapply : ∀ (a : ↥A) (v : ↥H), ((ρ a v : ↥H) : L) = (a : L) * (v : L) * (a : L)⁻¹ :=
      fun a v => MulAut.conjNormal_apply (a : L) v
    have hcopA : (Nat.card ↥A).Coprime (Nat.card ↥H) := by
      rw [hcardA]
      exact (hcopU.mul_right hcop).symm
    have hCfix : ∀ w ∈ B.subgroupOf A, w ≠ 1 →
        U.subgroupOf A ⊓ centralizer ({w} : Set ↥A) = ⊥ := by
      intro w hw hw1
      rw [Subgroup.mem_subgroupOf] at hw
      have hw1' : (w : L) ≠ 1 := fun hc => hw1 (Subtype.ext hc)
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxU, hxc⟩ := Subgroup.mem_inf.1 hx
      rw [Subgroup.mem_subgroupOf] at hxU
      have hmem : (x : L) ∈ U ⊓ centralizer ({(w : L)} : Set L) := by
        refine Subgroup.mem_inf.2 ⟨hxU, mem_centralizer_singleton_iff.2 ?_⟩
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hxc)
      rw [hCU _ hw hw1', Subgroup.mem_bot] at hmem
      exact Subgroup.mem_bot.2 (Subtype.ext hmem)
    obtain ⟨b, hbB, hb1⟩ : ∃ b : L, b ∈ B ∧ b ≠ 1 := by
      obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB
      exact ⟨b, b.2, fun hc => hb (Subtype.ext hc)⟩
    have hbH : b ∉ H := fun hc => hb1 (Subgroup.disjoint_def.1 hdisjHB hc hbB)
    have hCK : ∀ v : ↥H, (∀ w ∈ B.subgroupOf A, ρ w v = v) → v = 1 := by
      intro v hv
      have hbA : b ∈ A := hBA hbB
      have hvb := hv ⟨b, hbA⟩ (Subgroup.mem_subgroupOf.2 hbB)
      have hcomm : (v : L) ∈ H ⊓ centralizer ({b} : Set L) := by
        refine Subgroup.mem_inf.2 ⟨v.2, mem_centralizer_singleton_iff.2 ?_⟩
        have h2 := congrArg (Subtype.val (p := fun x => x ∈ H)) hvb
        rw [hρapply ⟨b, hbA⟩ v] at h2
        simp only [mul_inv_eq_iff_eq_mul] at h2
        exact h2.symm
      rw [inf_centralizer_singleton_eq_bot_of_notMem hHE hCH hbH, Subgroup.mem_bot] at hcomm
      exact Subtype.ext hcomm
    have hker := le_ker_of_forall_fixedPoints_eq_one (U := U.subgroupOf A)
      (W := B.subgroupOf A) ρ hcopA hUnormal hcompl hCfix hCK
    obtain ⟨u, huU, hu1⟩ : ∃ u : L, u ∈ U ∧ u ≠ 1 := by
      obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU
      exact ⟨u, u.2, fun hc => hu (Subtype.ext hc)⟩
    obtain ⟨h, hhH, hh1⟩ : ∃ h : L, h ∈ H ∧ h ≠ 1 := by
      obtain ⟨h, hh⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hH
      exact ⟨h, h.2, fun hc => hh (Subtype.ext hc)⟩
    have huH : u ∉ H := fun hc => hu1 (Subgroup.disjoint_def.1 hdisjUH huU hc)
    have huA : u ∈ A := hUA huU
    have hact : ρ ⟨u, huA⟩ = 1 := hker (Subgroup.mem_subgroupOf.2 huU)
    have hfix : u * h * u⁻¹ = h := by
      have h3 := congrArg (fun f : MulAut ↥H => ((f ⟨h, hhH⟩ : ↥H) : L)) hact
      simpa [hρapply] using h3
    have hmem : h ∈ H ⊓ centralizer ({u} : Set L) := by
      refine Subgroup.mem_inf.2 ⟨hhH, mem_centralizer_singleton_iff.2 ?_⟩
      rw [mul_inv_eq_iff_eq_mul] at hfix
      exact hfix.symm
    rw [inf_centralizer_singleton_eq_bot_of_notMem hHE hCH huH, Subgroup.mem_bot] at hmem
    exact hh1 hmem
  ·
    obtain ⟨⟨h, hmem⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hUH
    have h1 : h ≠ 1 := fun hc => hne (Subtype.ext hc)
    exact le_trans (le_trans (Subgroup.le_centralizer U)
        (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hmem.1)))
      (centralizer_singleton_le_of_mem_of_ne_one hHE hCH hmem.2 h1)

theorem le_of_isMulCommutative_of_isHallSubgroup [Finite L] [Group.IsSolvable L] [H.Normal]
    [IsMulCommutative U] {π : Set ℕ} (hHE : H.IsComplement' E) (hHall : IsHallSubgroup π H)
    (hCH : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set L) = ⊥)
    (hH : H ≠ ⊥) (hU : U ≠ ⊥) (hB : B ≠ ⊥)
    (hBU : B ≤ normalizer (U : Set L)) (hUB : Disjoint U B)
    (hCU : ∀ b ∈ B, b ≠ 1 → U ⊓ centralizer ({b} : Set L) = ⊥)
    (hcop : (Nat.card H).Coprime (Nat.card B)) :
    U ≤ H :=
  le_of_isMulCommutative_of_coprime_natCard hHE hHall.coprime_natCard_index hCH hH hU hB hBU hUB
    hCU hcop

end CFSG.FeitThompson
