module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenPerm
import CFSG.Quasithin.Background.B6Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.AGLEmbeddingD2.GN

open Equiv Equiv.Perm CFSG.QuasithinUnique CFSG.Quasithin

variable {N : ℕ}

theorem swap_commute_swap {a b u v : Fin N} (h : [a, b, u, v].Nodup) :
    swap a b * swap u v = swap u v * swap a b := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨hab, hau, hav⟩, ⟨hbu, hbv⟩, huv, -⟩ := h
  have hd : (swap a b).Disjoint (swap u v) := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support, Equiv.Perm.support_swap hab,
      Equiv.Perm.support_swap huv, Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl <;> simp_all
  exact hd.commute

theorem exists_orderOf_four (hN : 4 ≤ N) : ∃ c : Perm (Fin N), orderOf c = 4 := by
  let l : List (Fin N) := [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩]
  have hl : l.Nodup := by simp [l, List.nodup_cons, Fin.ext_iff]
  refine ⟨l.formPerm, ?_⟩
  have hcyc : l.formPerm.IsCycle := List.isCycle_formPerm hl (by simp [l])
  rw [hcyc.orderOf, List.support_formPerm_of_nodup l hl (by simp [l])]
  rw [List.toFinset_card_of_nodup hl]
  simp [l]

theorem not_isSylowTwoOf_swaps {A : Type*} [Group A] [Finite A] (hN : 4 ≤ N)
    {L Jc Tst : Subgroup A} (θ : ↥L ≃* Perm (Fin N)) (hTst : IsPGroup 2 Tst)
    (hcl : L ⊓ Jc = Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ Tst ∧ (θ ⟨x, hx⟩).IsSwap}) :
    ¬ IsSylowTwoOf Jc L := by
  intro hsyl
  set G₀ : Set A := {x | ∃ hx : x ∈ L, x ∈ Tst ∧ (θ ⟨x, hx⟩).IsSwap} with hG₀
  have hcl' : Jc = Subgroup.closure G₀ := by rw [← hcl, inf_eq_right.2 hsyl.1]
  set D : Subgroup (Perm (Fin N)) := ((Tst ⊓ L).subgroupOf L).map θ.toMonoidHom with hD
  have hDp : IsPGroup 2 ↥D := by
    have h1 : IsPGroup 2 ↥(Tst ⊓ L) := hTst.to_le inf_le_left
    have h2 : IsPGroup 2 ↥((Tst ⊓ L).subgroupOf L) :=
      h1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : Tst ⊓ L ≤ L)).symm
    exact h2.of_equiv (Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective)
  have hdata : ∀ x ∈ G₀, ∃ hx : x ∈ L, θ ⟨x, hx⟩ ∈ D ∧ ∃ u v : Fin N, u ≠ v ∧
      θ ⟨x, hx⟩ = swap u v := by
    rintro x ⟨hx, hxT, u, v, huv, hxuv⟩
    exact ⟨hx, ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.2 ⟨hxT, hx⟩, rfl⟩, u, v, huv, hxuv⟩
  have hsq0 : ∀ x ∈ G₀, x * x = 1 := by
    intro x hx
    obtain ⟨hxL, -, u, v, -, hxuv⟩ := hdata x hx
    have h1 : θ (⟨x, hxL⟩ * ⟨x, hxL⟩) = θ 1 := by
      rw [map_mul, map_one, hxuv, swap_mul_self]
    exact congrArg Subtype.val (θ.injective h1)
  have hcomm0 : ∀ x ∈ G₀, ∀ y ∈ G₀, x * y = y * x := by
    intro x hx y hy
    obtain ⟨hxL, hxD, u, v, huv, hxuv⟩ := hdata x hx
    obtain ⟨hyL, hyD, u', v', huv', hyuv⟩ := hdata y hy
    rw [hxuv] at hxD
    rw [hyuv] at hyD
    rcases eq_or_nodup_of_swaps hDp huv huv' hxD hyD with heq | hnodup
    · have : θ ⟨x, hxL⟩ = θ ⟨y, hyL⟩ := by rw [hxuv, hyuv, heq]
      have h2 := congrArg Subtype.val (θ.injective this)
      simp only at h2
      rw [h2]
    · have h1 : θ (⟨x, hxL⟩ * ⟨y, hyL⟩) = θ (⟨y, hyL⟩ * ⟨x, hxL⟩) := by
        rw [map_mul, map_mul, hxuv, hyuv]
        exact swap_commute_swap hnodup
      exact congrArg Subtype.val (θ.injective h1)
  have hc1 : ∀ y ∈ Subgroup.closure G₀, ∀ z ∈ G₀, y * z = z * y := by
    intro y hy z hz
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact hcomm0 x hx z hz
    | one => simp
    | mul a b _ _ iha ihb => rw [mul_assoc, ihb, ← mul_assoc, iha, mul_assoc]
    | inv a _ iha =>
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, iha, mul_assoc, mul_inv_cancel, mul_one]
  have hc2 : ∀ y ∈ Subgroup.closure G₀, ∀ z ∈ Subgroup.closure G₀, y * z = z * y := by
    intro y hy z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx => exact hc1 y hy x hx
    | one => simp
    | mul a b _ _ iha ihb => rw [← mul_assoc, iha, mul_assoc, ihb, ← mul_assoc]
    | inv a _ iha =>
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, iha, ← mul_assoc, inv_mul_cancel, one_mul]
  have hsq : ∀ y ∈ Subgroup.closure G₀, y * y = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact hsq0 x hx
    | one => simp
    | mul a b ha hb iha ihb =>
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hc2 b hb a ha]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [iha, ihb, one_mul]
    | inv a ha iha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [iha, inv_one]
  obtain ⟨c, hc4⟩ := exists_orderOf_four hN
  set g : A := ((θ.symm c : ↥L) : A) with hg
  have hgL : g ∈ L := (θ.symm c).2
  have hg4 : orderOf g = 4 := by
    rw [hg, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hc4]
  have hX : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg4]; norm_num)
  obtain ⟨S, hS, hXS⟩ := B6.exists_isSylowTwoOf_ge hX (Subgroup.zpowers_le.2 hgL)
  obtain ⟨h, -, hSeq⟩ := B6.isSylowTwoOf_exists_conj hsyl hS
  have hgS : g ∈ S := hXS (Subgroup.mem_zpowers g)
  rw [hSeq, B6.mem_conjSub, hcl'] at hgS
  have h2 := hsq _ hgS
  have hgg : g * g = 1 := by
    calc g * g = h * ((h⁻¹ * g * h) * (h⁻¹ * g * h)) * h⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have h3 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  rw [hg4] at h3
  omega

end CFSG.AGLEmbeddingD2.GN
