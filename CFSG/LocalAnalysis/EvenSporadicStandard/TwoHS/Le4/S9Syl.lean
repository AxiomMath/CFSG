module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Lists
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9HCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Hyp
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

section S1

variable {G : Type} [Group G] [Finite G]

@[expose] def S1sub (C : ECoord G) (t : G) (hLF : ListFacts) : Subgroup G where
  carrier := {x | x * t = t * x ∧ x ∈ normalizer (C.E : Set G) ∧ C.mat x ∈ shatList}
  mul_mem' := by
    rintro a b ⟨hat, haN, ham⟩ ⟨hbt, hbN, hbm⟩
    refine ⟨?_, Subgroup.mul_mem _ haN hbN, ?_⟩
    · calc a * b * t = a * (b * t) := by rw [mul_assoc]
        _ = a * (t * b) := by rw [hbt]
        _ = (a * t) * b := by rw [mul_assoc]
        _ = t * (a * b) := by rw [hat, mul_assoc]
    · rw [C.mat_mul haN hbN]
      exact hLF.shat_mul _ ham _ hbm
  one_mem' := ⟨by simp, Subgroup.one_mem _, by rw [C.mat_one]; exact hLF.shat_one⟩
  inv_mem' := by
    rintro a ⟨hat, haN, ham⟩
    refine ⟨?_, Subgroup.inv_mem _ haN, ?_⟩
    · calc a⁻¹ * t = a⁻¹ * (t * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * t) * a⁻¹ := by rw [hat]
        _ = t * a⁻¹ := by group
    · obtain ⟨B, hB, hAB, hBA⟩ := hLF.shat_inv _ ham
      have : C.mat a⁻¹ = B := by
        calc C.mat a⁻¹ = (B * C.mat a) * C.mat a⁻¹ := by rw [hBA, one_mul]
          _ = B * (C.mat a * C.mat a⁻¹) := by rw [mul_assoc]
          _ = B := by rw [C.mat_mul_inv haN, mul_one]
      rw [this]
      exact hB

theorem card_S1sub (C : ECoord G) {t : G} (hLF : ListFacts)
    (hshat : ∀ A ∈ shatList, A ∈ q0List)
    (hcent : ∀ x : G, x * t = t * x → (∀ e ∈ C.E, x * e = e * x) → x ∈ C.E)
    (hreal : ∀ A ∈ q0List, ∃ x : G, x * t = t * x ∧ x ∈ normalizer (C.E : Set G) ∧
      C.mat x = A)
    (htE : t ∈ C.E) :
    Nat.card (S1sub C t hLF) = 4096 := by
  set S := S1sub C t hLF with hS
  have hf := C.card_inf_centralizer_mul_ncard_image S fun x hx => hx.2.1
  have hK : S ⊓ centralizer (C.E : Set G) = C.E := by
    ext x
    constructor
    · rintro ⟨hxS, hxc⟩
      exact hcent x hxS.1 fun e he => (mem_centralizer_iff.1 hxc e he).symm
    · intro hxE
      refine ⟨⟨C.comm hxE htE, Subgroup.le_normalizer hxE, ?_⟩, ?_⟩
      · have h1 : C.mat x = 1 := (C.mat_eq_one_iff (Subgroup.le_normalizer hxE)).2
          fun e he => C.comm hxE he
        rw [h1]
        exact hLF.shat_one
      · exact mem_centralizer_iff.2 fun h hh => C.comm hh hxE
  have himg : C.mat '' (S : Set G) = ((shatList.toFinset : Finset M4) : Set M4) := by
    ext A
    constructor
    · rintro ⟨x, hxS, rfl⟩
      simpa using hxS.2.2
    · intro hA
      have hA' : A ∈ shatList := by simpa using hA
      obtain ⟨x, hxt, hxN, hxA⟩ := hreal A (hshat A hA')
      exact ⟨x, ⟨hxt, hxN, hxA ▸ hA'⟩, hxA⟩
  rw [hK, C.natCard_E, himg, Set.ncard_coe_finset, List.toFinset_card_of_nodup hLF.shat_nd,
    hLF.shat_len] at hf
  omega

theorem card_two_subgroup_le {L N S : Subgroup G} (hSN : S ≤ N) (hp : IsPGroup 2 S)
    (hLN : L.relIndex N ≤ 4) (hL : Nat.card L = 88704000) : Nat.card S ≤ 4096 := by
  have hne : L.relIndex N ≠ 0 := by
    have h := Subgroup.relIndex_mul_card (H := L) (K := N)
    intro h0
    rw [h0, zero_mul] at h
    have : 0 < Nat.card N := Nat.card_pos
    omega
  have h1 : L.relIndex S ≤ 4 := (Subgroup.relIndex_le_of_le_right hSN hne).trans hLN
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := S)
  have hq : IsPGroup 2 ↥(L ⊓ S) := hp.to_inf_right
  obtain ⟨n, hn⟩ := hq.exists_card_eq
  have hdvd : Nat.card ↥(L ⊓ S) ∣ Nat.card L := Subgroup.card_dvd_of_le inf_le_left
  rw [hn, hL] at hdvd
  have hn10 : n ≤ 10 := by
    by_contra hlt
    have h11 : 2 ^ 11 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := h11.trans hdvd
    norm_num at this
  have h1024 : Nat.card ↥(L ⊓ S) ≤ 1024 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hn10
      _ = 1024 := by norm_num
  calc Nat.card S = L.relIndex S * Nat.card ↥(L ⊓ S) := h2.symm
    _ ≤ 4 * 1024 := Nat.mul_le_mul h1 h1024
    _ = 4096 := by norm_num

end S1

end CFSG.EvenSporadicStandard.TwoHS
