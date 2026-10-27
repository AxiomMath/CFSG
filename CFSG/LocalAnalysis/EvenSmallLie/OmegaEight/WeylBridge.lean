module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylModel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylBridgeCheck

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def wordPerm (l : List ℕ) : Equiv.Perm (Fin 240) := (l.map refl).prod

theorem rep_wordArr : ∀ l : List ℕ, (∀ r ∈ l, r < 240) → Rep 240 (wordArr l) (wordPerm l)
  | [], _ => by
    rw [wordArr, wordPerm, List.map_nil, List.prod_nil]
    exact rep_idA
  | r :: l, h => by
    rw [wordArr, wordPerm, List.map_cons, List.prod_cons]
    exact rep_compA (rep_refl (h r List.mem_cons_self))
      (rep_wordArr l fun s hs => h s (List.mem_cons_of_mem _ hs))

theorem wordPerm_mem : ∀ l : List ℕ, (∀ r ∈ l, r < 240) → wordPerm l ∈ wE8
  | [], _ => by
    rw [wordPerm, List.map_nil, List.prod_nil]
    exact one_mem _
  | r :: l, h => by
    rw [wordPerm, List.map_cons, List.prod_cons]
    exact mul_mem (refl_mem (h r List.mem_cons_self))
      (wordPerm_mem l fun s hs => h s (List.mem_cons_of_mem _ hs))

theorem sign_wordPerm : ∀ l : List ℕ, (∀ r ∈ l, r < 240) →
    Equiv.Perm.sign (wordPerm l) = (-1) ^ l.length
  | [], _ => by rw [wordPerm, List.map_nil, List.prod_nil, map_one, List.length_nil, pow_zero]
  | r :: l, h => by
    rw [wordPerm, List.map_cons, List.prod_cons, map_mul, ← wordPerm,
      sign_refl (h r List.mem_cons_self), sign_wordPerm l fun s hs => h s (List.mem_cons_of_mem _ hs),
      List.length_cons, pow_succ, mul_comm]

theorem mem_wPlus_iff {g : Equiv.Perm (Fin 240)} :
    g ∈ wPlus ↔ g ∈ wE8 ∧ Equiv.Perm.sign g = 1 := by
  rw [wPlus, mem_inf, Equiv.Perm.mem_alternatingGroup]

theorem wPlus_le : wPlus ≤ wE8 := inf_le_left

theorem wordPerm_mem_wPlus {l : List ℕ} (h : ∀ r ∈ l, r < 240) (he : Even l.length) :
    wordPerm l ∈ wPlus :=
  mem_wPlus_iff.2 ⟨wordPerm_mem l h, by rw [sign_wordPerm l h, he.neg_one_pow]⟩

theorem refl_not_mem_wPlus {r : ℕ} (hr : r < 240) : refl r ∉ wPlus := fun h => by
  have := (mem_wPlus_iff.1 h).2
  rw [sign_refl hr] at this
  exact absurd this (by decide)

theorem rep_negArr : Rep 240 negArr zPerm := (isInvA_spec' refl_facts.zinv).1

theorem zPerm_mul_self : zPerm * zPerm = 1 := (isInvA_spec' refl_facts.zinv).2

theorem frameRootList_lt : ∀ r ∈ frameRootList, r < 240 := by
  intro r hr
  simp only [frameRootList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem zPerm_eq_wordPerm : zPerm = wordPerm frameRootList :=
  (eq_of_eqA (rep_wordArr _ frameRootList_lt) rep_negArr zWord_check).symm

theorem zPerm_mem_wE8 : zPerm ∈ wE8 := by
  rw [zPerm_eq_wordPerm]
  exact wordPerm_mem _ frameRootList_lt

theorem zPerm_mem_wPlus : zPerm ∈ wPlus := by
  rw [zPerm_eq_wordPerm]
  exact wordPerm_mem_wPlus frameRootList_lt (by decide)

theorem zPerm_ne_one : zPerm ≠ 1 := fun h => by
  have h1 := card_fixedPoints_of_rep rep_negArr
  rw [refl_facts.zfix, h] at h1
  exact (Fintype.card_eq_zero_iff.1 h1).false ⟨⟨0, by norm_num⟩, rfl⟩

theorem zPerm_inv : zPerm⁻¹ = zPerm := inv_eq_of_mul_eq_one_right zPerm_mul_self

theorem refl_mul_zPerm {r : ℕ} (hr : r < 240) : refl r * zPerm = zPerm * refl r :=
  (eq_of_eqA (rep_compA rep_negArr (rep_refl hr)) (rep_compA (rep_refl hr) rep_negArr)
    (refl_facts.zcomm r hr)).symm

theorem zPerm_comm : ∀ w ∈ wE8, w * zPerm = zPerm * w :=
  wE8_induction (by rw [one_mul, mul_one]) fun r hr g hg => by
    rw [mul_assoc, hg, ← mul_assoc, refl_mul_zPerm hr, mul_assoc]

theorem card_wPlus : Nat.card wPlus = 348364800 := by
  set f : wE8 →* ℤˣ := Equiv.Perm.sign.comp wE8.subtype with hf
  have hker : f.ker = wPlus.subgroupOf wE8 := by
    ext ⟨g, hg⟩
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_wPlus_iff]
    simp [hf, hg]
  have hrange : Nat.card f.range = 2 := by
    have htop : f.range = ⊤ := by
      rw [eq_top_iff]
      rintro u -
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact one_mem _
      · exact ⟨⟨refl 1, refl_mem (by norm_num)⟩, sign_refl (by norm_num)⟩
    rw [htop, card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange, hker, card_wE8] at h1
  have h2 : Nat.card (wPlus.subgroupOf wE8) = Nat.card wPlus :=
    Nat.card_congr (subgroupOfEquivOfLe wPlus_le).toEquiv
  omega
