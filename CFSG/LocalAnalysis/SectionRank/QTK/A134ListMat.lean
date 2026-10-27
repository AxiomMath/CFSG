module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
public import CFSG.Blueprint.NativeSporadic
import CFSG.LocalAnalysis.SectionRank.QTK.Witness3
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (localRank)

@[expose] def abWord {G : Type*} [Group G] (a b : G) : List ℕ → G
  | [] => 1
  | i :: w => (if i = 0 then a else if i = 1 then b else b⁻¹) * abWord a b w

theorem abWord_mem {G : Type*} [Group G] {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    ∀ w, abWord a b w ∈ H
  | [] => H.one_mem
  | i :: w => by
    refine H.mul_mem ?_ (abWord_mem ha hb w)
    split_ifs
    · exact ha
    · exact hb
    · exact H.inv_mem hb

theorem two_le_pRank_three_of_pair {S : Type} [Group S] [Finite S] {x y : S} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (hxy : Commute x y) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x)
    (hyx2 : y ≠ x ^ 2) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_of_gens hx hy hxy hx1
    fun n hn => ?_
  rw [pow_eq_pow_mod n hx] at hn
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h <;> rw [h] at hn
  · exact hy1 (by rw [← hn, pow_zero])
  · exact hyx (by rw [← hn, pow_one])
  · exact hyx2 hn.symm

theorem one_le_localRank_three_of_pow_six {S : Type} [Group S] [Finite S] {g : S}
    (h6 : g ^ 6 = 1) (h2 : g ^ 2 ≠ 1) (h3 : g ^ 3 ≠ 1) : 1 ≤ localRank 3 S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht : (g ^ 3) ^ 2 = 1 := by rw [← pow_mul]; exact h6
  have hx : (g ^ 2) ^ 3 = 1 := by rw [← pow_mul]; exact h6
  have hne : Subgroup.zpowers (g ^ 3) ≠ ⊥ := fun h =>
    h3 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers (g ^ 3)))
  exact one_le_localRank_of_mem_normalizer (by norm_num) hne (isPGroup_zpowers_of_sq ht)
    (mem_normalizer_zpowers ((Commute.refl g).pow_pow 2 3)) (orderOf_eq_prime hx h2)

theorem oddLocalWitness_of_six {G : Type} [Group G] {H : Subgroup G} [Finite H] {g y : G}
    (hg : g ∈ H) (hy : y ∈ H)
    (h : g ^ 6 = 1 ∧ g ^ 2 ≠ 1 ∧ g ^ 3 ≠ 1 ∧ y ^ 3 = 1 ∧ y * g ^ 2 = g ^ 2 * y ∧ y ≠ 1 ∧
      y ≠ g ^ 2 ∧ y ≠ g ^ 4) : OddLocalWitness H := by
  obtain ⟨h6, h2, h3, hy3, hc, hy1, hyx, hyx2⟩ := h
  let g' : H := ⟨g, hg⟩
  let y' : H := ⟨y, hy⟩
  have hv : ∀ (a : H) (n : ℕ), ((a ^ n : H) : G) = (a : G) ^ n := fun a n => by
    rw [SubgroupClass.coe_pow]
  have hne : ∀ (a : H) (b : G), (a : G) ≠ b → ∀ c : H, (c : G) = b → a ≠ c :=
    fun a b hab c hc h => hab (by rw [h, hc])
  have h6' : g' ^ 6 = 1 := Subtype.ext (by rw [hv]; exact h6)
  have hx3 : (g' ^ 2) ^ 3 = 1 := by rw [← pow_mul]; exact h6'
  have hx1 : g' ^ 2 ≠ 1 := fun h => h2 (by simpa [g'] using congrArg Subtype.val h)
  have h3' : g' ^ 3 ≠ 1 := fun h => h3 (by simpa [g'] using congrArg Subtype.val h)
  have hy3' : y' ^ 3 = 1 := Subtype.ext (by rw [hv]; exact hy3)
  have hc' : Commute (g' ^ 2) y' := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hv]
    exact hc.symm)
  have hy1' : y' ≠ 1 := fun h => hy1 (by simpa [y'] using congrArg Subtype.val h)
  have hyx' : y' ≠ g' ^ 2 := hne y' _ hyx _ (hv g' 2)
  have hyx2' : y' ≠ (g' ^ 2) ^ 2 := hne y' _ hyx2 _ (by rw [← pow_mul, hv])
  exact ⟨3, Nat.prime_three, by norm_num,
    two_le_pRank_three_of_pair hx3 hy3' hc' hx1 hy1' hyx' hyx2',
    one_le_localRank_three_of_pow_six h6' hx1 h3'⟩

abbrev m11a : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]

abbrev m11b : Equiv.Perm (Fin 11) := List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]

theorem oddLocalWitness_M11 : OddLocalWitness NativeSporadic.M11 := by
  have ha : m11a ∈ NativeSporadic.M11 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m11b ∈ NativeSporadic.M11 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact oddLocalWitness_of_six (abWord_mem ha hb [0, 1, 1])
    (abWord_mem ha hb [0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2]) (by decide +kernel)

abbrev m12a : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

abbrev m12b : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

theorem oddLocalWitness_M12 : OddLocalWitness NativeSporadic.M12 := by
  have ha : m12a ∈ NativeSporadic.M12 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m12b ∈ NativeSporadic.M12 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact oddLocalWitness_of_six (abWord_mem ha hb [0, 1, 0, 1, 1])
    (abWord_mem ha hb [2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1]) (by decide +kernel)

abbrev m22a : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

abbrev m22b : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

theorem oddLocalWitness_M22 : OddLocalWitness NativeSporadic.M22 := by
  have ha : m22a ∈ NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m22b ∈ NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact oddLocalWitness_of_six (abWord_mem ha hb [0, 1, 0, 1, 1, 1])
    (abWord_mem ha hb [0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1])
    (by decide +kernel)

abbrev m23a : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

abbrev m23b : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem oddLocalWitness_M23 : OddLocalWitness NativeSporadic.M23 := by
  have ha : m23a ∈ NativeSporadic.M23 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m23b ∈ NativeSporadic.M23 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact oddLocalWitness_of_six (abWord_mem ha hb [0, 1, 1])
    (abWord_mem ha hb [1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1])
    (by decide +kernel)

abbrev m24a : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] *
    List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] *
    List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] *
    List.formPerm [19, 23] * List.formPerm [21, 22]

abbrev m24b : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
    List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]

theorem oddLocalWitness_M24 : OddLocalWitness NativeSporadic.M24 := by
  have ha : m24a ∈ NativeSporadic.M24 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m24b ∈ NativeSporadic.M24 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact oddLocalWitness_of_six (abWord_mem ha hb [0, 1, 0, 1, 1, 0, 1, 0, 1, 1])
    (abWord_mem ha hb [1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1,
      0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1])
    (by decide +kernel)

theorem oddLocalWitness_mathieu {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24)
    [Finite (NativeSporadic.Carrier s)] : OddLocalWitness (NativeSporadic.Carrier s) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact oddLocalWitness_M11
  · exact oddLocalWitness_M12
  · exact oddLocalWitness_M22
  · exact oddLocalWitness_M23
  · exact oddLocalWitness_M24

end CFSG.SectionRank.QTK
