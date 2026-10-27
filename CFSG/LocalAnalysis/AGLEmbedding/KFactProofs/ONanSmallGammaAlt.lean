module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallGammaCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreAltSixSylow

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallGamma

open Equiv

def a6T0list : List (Perm (Fin 6)) :=
  [1, swap 0 2 * swap 0 1, swap 0 1 * swap 0 2, swap 3 5 * swap 3 4, swap 3 4 * swap 3 5,
    swap 0 2 * swap 0 1 * (swap 3 5 * swap 3 4), swap 0 2 * swap 0 1 * (swap 3 4 * swap 3 5),
    swap 0 1 * swap 0 2 * (swap 3 5 * swap 3 4), swap 0 1 * swap 0 2 * (swap 3 4 * swap 3 5)]

def a6Perms : List (Perm (Fin 6)) := permsOfList (List.finRange 6)

theorem mem_a6Perms (y : Perm (Fin 6)) : y ∈ a6Perms :=
  mem_permsOfList_of_mem fun x _ => List.mem_finRange x

theorem a6T0list_nodup : a6T0list.Nodup := by decide +kernel

theorem a6T0list_mul_check :
    a6T0list.all (fun a => a6T0list.all (fun b => decide (a * b ∈ a6T0list))) = true := by
  decide +kernel

theorem a6T0list_inv_check : a6T0list.all (fun a => decide (a⁻¹ ∈ a6T0list)) = true := by
  decide +kernel

theorem a6T0list_sign_check : a6T0list.all (fun a => decide (Perm.sign a = 1)) = true := by
  decide +kernel

theorem a6T0list_comm_check :
    a6T0list.all (fun a => a6T0list.all (fun b => decide (a * b = b * a))) = true := by
  decide +kernel

theorem a6_centralizer_check :
    a6Perms.all (fun y => a6T0list.all (fun t => decide (t ≠ 1 → y * t = t * y →
      Perm.sign y = 1 → y ∈ a6T0list))) = true := by
  decide +kernel

def a6Nlist : List (Perm (Fin 6)) :=
  a6Perms.filter (fun y => decide (Perm.sign y = 1) &&
    a6T0list.all (fun t => decide (y * t * y⁻¹ ∈ a6T0list)))

theorem a6Nlist_length : a6Nlist.length = 36 := by decide +kernel

theorem mem_a6Nlist {y : Perm (Fin 6)} (hs : Perm.sign y = 1)
    (hn : ∀ t ∈ a6T0list, y * t * y⁻¹ ∈ a6T0list) : y ∈ a6Nlist := by
  unfold a6Nlist
  rw [List.mem_filter]
  refine ⟨mem_a6Perms y, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨hs, hn⟩

theorem sign_of_mem_a6T0list {σ : Perm (Fin 6)} (h : σ ∈ a6T0list) : Perm.sign σ = 1 :=
  of_decide_eq_true (List.all_eq_true.1 a6T0list_sign_check σ h)

def altT0 : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {x | (x : Perm (Fin 6)) ∈ a6T0list}
  mul_mem' := fun {a b} ha hb =>
    of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 a6T0list_mul_check _ ha) _ hb)
  one_mem' := by
    show (1 : Perm (Fin 6)) ∈ a6T0list
    decide +kernel
  inv_mem' := fun {a} ha => of_decide_eq_true (List.all_eq_true.1 a6T0list_inv_check _ ha)

theorem altT0_card : Nat.card altT0 = 9 := by
  have e : altT0 ≃ ↥(a6T0list.toFinset : Set (Perm (Fin 6))) :=
    { toFun := fun x => ⟨((x : alternatingGroup (Fin 6)) : Perm (Fin 6)),
        Finset.mem_coe.2 (List.mem_toFinset.2 x.2)⟩
      invFun := fun σ => ⟨⟨σ, Perm.mem_alternatingGroup.mpr
          (sign_of_mem_a6T0list (List.mem_toFinset.1 σ.2))⟩, List.mem_toFinset.1 σ.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup a6T0list_nodup]
  rfl

theorem altT0_comm : ∀ x ∈ altT0, ∀ y ∈ altT0, x * y = y * x := by
  intro x hx y hy
  have h := List.all_eq_true.1 (List.all_eq_true.1 a6T0list_comm_check x.1 hx) y.1 hy
  exact Subtype.ext (of_decide_eq_true h)

theorem altT0_centralizer_le : ∀ t ∈ altT0, t ≠ 1 →
    ∀ g : alternatingGroup (Fin 6), g * t = t * g → g ∈ altT0 := by
  intro t ht ht1 g hg
  have h := List.all_eq_true.1 (List.all_eq_true.1 a6_centralizer_check g.1 (mem_a6Perms g.1))
    t.1 ht
  exact of_decide_eq_true h (fun h1 => ht1 (Subtype.ext h1)) (congrArg Subtype.val hg)
    (Perm.mem_alternatingGroup.1 g.2)

theorem card_normalizer_altT0_le :
    Nat.card (Subgroup.normalizer (altT0 : Set (alternatingGroup (Fin 6)))) ≤ 36 := by
  have hmem : ∀ n : Subgroup.normalizer (altT0 : Set (alternatingGroup (Fin 6))),
      (n : alternatingGroup (Fin 6)).1 ∈ a6Nlist.toFinset := by
    intro n
    rw [List.mem_toFinset]
    refine mem_a6Nlist (Perm.mem_alternatingGroup.1 n.1.2) fun t ht => ?_
    have hts : (⟨t, Perm.mem_alternatingGroup.2 (sign_of_mem_a6T0list ht)⟩ :
        alternatingGroup (Fin 6)) ∈ altT0 := ht
    exact (Subgroup.mem_normalizer_iff.1 n.2 _).1 hts
  have hinj : Function.Injective
      (fun n : Subgroup.normalizer (altT0 : Set (alternatingGroup (Fin 6))) =>
        (⟨(n : alternatingGroup (Fin 6)).1, hmem n⟩ : ↥a6Nlist.toFinset)) := by
    intro n m h
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  calc Nat.card (Subgroup.normalizer (altT0 : Set (alternatingGroup (Fin 6))))
      ≤ Nat.card ↥a6Nlist.toFinset := Nat.card_le_card_of_injective _ hinj
    _ = a6Nlist.toFinset.card := Nat.card_eq_fintype_card.trans (Fintype.card_coe _)
    _ ≤ a6Nlist.length := List.toFinset_card_le _
    _ = 36 := a6Nlist_length

theorem card_normalizer_altT0 :
    ∃ b : ℕ, Nat.card (Subgroup.normalizer (altT0 : Set (alternatingGroup (Fin 6)))) =
      3 ^ 2 * 2 ^ b := by
  set N := Subgroup.normalizer (altT0 : Set (alternatingGroup (Fin 6)))
  have h9 : 9 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer : altT0 ≤ N)
    rwa [altT0_card] at this
  have h360 : Nat.card N ∣ 360 := card_altSix ▸ Subgroup.card_subgroup_dvd_card N
  have hle : Nat.card N ≤ 36 := card_normalizer_altT0_le
  have hpos : 0 < Nat.card N := Nat.card_pos
  obtain ⟨m, hm⟩ := h9
  rw [hm] at h360 hle hpos ⊢
  have hm40 : m ∣ 40 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 9) (by simpa using h360)
  have hm1 : 1 ≤ m := by omega
  have hm4 : m ≤ 4 := by omega
  interval_cases m
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact absurd hm40 (by norm_num)
  · exact ⟨2, by norm_num⟩

theorem smallGammaData_altT0 : SmallGammaData (alternatingGroup (Fin 6)) altT0 := by
  obtain ⟨b, hb⟩ := card_normalizer_altT0
  exact SmallGammaData.of_centralizer (a := 2) (b := b) altT0_comm altT0_centralizer_le
    (by rw [altT0_card]; norm_num) hb

theorem smallGammaData_altSix {K : Type*} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 6)) (T : Sylow 3 K) : SmallGammaData K (T : Subgroup K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : Nat.card altT0 = 3 ^ 2 := by rw [altT0_card]; norm_num
  obtain ⟨S, hS⟩ := (IsPGroup.of_card h9).exists_le_sylow
  have hST : (S : Subgroup (alternatingGroup (Fin 6))) = altT0 :=
    (Subgroup.eq_of_le_of_card_ge hS (by rw [altT0_card]; exact card_sylow_altSix_le S)).symm
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e T S
  exact SmallGammaData.of_equiv_map e' (he'.trans hST) smallGammaData_altT0

end CFSG.AGLEmbedding.KFactProofs.SmallGamma
