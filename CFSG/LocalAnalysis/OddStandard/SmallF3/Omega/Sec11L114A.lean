module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem mem_zpowers_invol {a x : G} (ha : a * a = 1) (hx : x ∈ zpowers a) :
    x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, ha, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, ha, one_zpow, one_mul, zpow_one]

theorem sec11L114_pair_mem {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    {x : G} : x ∈ zpowers a ⊔ zpowers b ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  constructor
  · intro hx
    have hcomm : ∀ u ∈ zpowers a, ∀ v ∈ zpowers b, u * v = v * u := by
      rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      exact (Commute.zpow_zpow (show Commute a b from hab) m n).eq
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hx
    rcases mem_zpowers_invol ha hu with h1 | h1 <;> rcases mem_zpowers_invol hb hv with h2 | h2
    · left
      rw [h1, h2, mul_one]
    · right; right; left
      rw [h1, h2, one_mul]
    · right; left
      rw [h1, h2, mul_one]
    · right; right; right
      rw [h1, h2]
  · rintro (h | h | h | h)
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_sup_left (mem_zpowers _)
    · rw [h]
      exact mem_sup_right (mem_zpowers _)
    · rw [h]
      exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem sec11L114_pair_sq {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    {x : G} (hx : x ∈ zpowers a ⊔ zpowers b) : x * x = 1 := by
  rcases (sec11L114_pair_mem ha hb hab).1 hx with h | h | h | h
  · rw [h, mul_one]
  · rw [h]
    exact ha
  · rw [h]
    exact hb
  · rw [h]
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [ha, hb, mul_one]

theorem sec11L114_pair_card_le {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : Nat.card ↥(zpowers a ⊔ zpowers b) ≤ 4 := by
  have hsub : ((zpowers a ⊔ zpowers b : Subgroup G) : Set G) ⊆ {1, a, b, a * b} := by
    intro x hx
    simpa using (sec11L114_pair_mem ha hb hab).1 hx
  calc Nat.card ↥(zpowers a ⊔ zpowers b) = ((zpowers a ⊔ zpowers b : Subgroup G) : Set G).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ({1, a, b, a * b} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 4 := by
      have h1 := Set.ncard_insert_le (1 : G) ({a, b, a * b} : Set G)
      have h2 := Set.ncard_insert_le a ({b, a * b} : Set G)
      have h3 := Set.ncard_insert_le b ({a * b} : Set G)
      have h4 : ({a * b} : Set G).ncard = 1 := Set.ncard_singleton _
      omega

theorem sec11L114_pair_card {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : Nat.card ↥(zpowers a ⊔ zpowers b) = 4 := by
  have hset : ((zpowers a ⊔ zpowers b : Subgroup G) : Set G) = {1, a, b, a * b} := by
    ext x
    simpa using sec11L114_pair_mem ha hb hab (x := x)
  have h1 : Nat.card ↥(zpowers a ⊔ zpowers b) = ({1, a, b, a * b} : Set G).ncard := by
    rw [← hset]
    exact Nat.card_coe_set_eq _
  have n1 : (1 : G) ∉ ({a, b, a * b} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨ha1.symm, hb1.symm, fun h => hne ?_⟩
    have h' : a * b = 1 := h.symm
    rw [eq_inv_of_mul_eq_one_left h', inv_eq_of_mul_eq_one_right hb]
  have n2 : a ∉ ({b, a * b} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨hne, fun h => hb1 ?_⟩
    exact mul_left_cancel (a := a) (show a * b = a * 1 by rw [mul_one]; exact h.symm)
  have n3 : b ≠ a * b := by
    intro h
    exact ha1 (mul_right_cancel (b := b) (show a * b = 1 * b by rw [one_mul]; exact h.symm))
  rw [h1, Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2, Set.ncard_pair n3]

theorem sec11L114_pair_isDih2 {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : IsDih2 (zpowers a ⊔ zpowers b) := by
  refine ⟨1, le_rfl, ?_⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥(zpowers a ⊔ zpowers b) :=
    ⟨⟨⟨a, mem_sup_left (mem_zpowers a)⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
  have hsq : ∀ g : ↥(zpowers a ⊔ zpowers b), g ^ 2 = 1 := fun g =>
    Subtype.ext (by rw [pow_two]; exact sec11L114_pair_sq ha hb hab g.2)
  haveI : IsKleinFour ↥(zpowers a ⊔ zpowers b) :=
    ⟨sec11L114_pair_card ha hb hab ha1 hb1 hne, by
      rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
      exact fun g hg => orderOf_eq_prime (hsq g) hg⟩
  obtain ⟨e⟩ := (IsKleinFour.nonempty_mulEquiv :
    Nonempty (↥(zpowers a ⊔ zpowers b) ≃* DihedralGroup 2))
  exact ⟨e⟩

theorem sec11L114_cent_dihedral [Finite G] {C : Subgroup G} {t z r : G} (ht : t * t = 1)
    (hz : z * z = 1) (hr : r * r = 1) (htz : t * z = z * t) (ht1 : t ≠ 1) (hz1 : z ≠ 1)
    (hne : t ≠ z) (htC : t ∈ C) (hzC : z ∈ C) (hCr : C = zpowers t ⊔ zpowers r) (hD8 : IsD8 C)
    {c : G} (hc : c ∈ C) (hct : c * t = t * c) : c ∈ zpowers t ⊔ zpowers z := by
  have hWC : zpowers t ⊔ zpowers z ≤ C :=
    sup_le (zpowers_le.2 htC) (zpowers_le.2 hzC)
  have hW4 : Nat.card ↥(zpowers t ⊔ zpowers z) = 4 := sec11L114_pair_card ht hz htz ht1 hz1 hne
  have hC8 : Nat.card ↥C = 8 := by
    obtain ⟨e⟩ := hD8
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hrC : r ∈ C := by
    rw [hCr]
    exact mem_sup_right (mem_zpowers r)
  by_cases hcomm : t * r = r * t
  · exfalso
    have hle : Nat.card ↥C ≤ 4 := by
      rw [hCr]
      exact sec11L114_pair_card_le ht hr hcomm
    omega
  · set Ct : Subgroup G := C ⊓ centralizer ({t} : Set G) with hCt
    have hWcent : zpowers t ⊔ zpowers z ≤ centralizer ({t} : Set G) :=
      sup_le (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl))
        (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 htz.symm))
    have hWCt : zpowers t ⊔ zpowers z ≤ Ct := le_inf hWC hWcent
    have hCtC : Ct ≤ C := inf_le_left
    have hrCt : r ∉ Ct := fun h =>
      hcomm (Subgroup.mem_centralizer_singleton_iff.1 h.2).symm
    have hne' : Ct ≠ C := fun h => hrCt (h ▸ hrC)
    have hdvd : Nat.card ↥Ct ∣ 8 := hC8 ▸ Subgroup.card_dvd_of_le hCtC
    have hne8 : Nat.card ↥Ct ≠ 8 := fun h =>
      hne' (Subgroup.eq_of_le_of_card_ge hCtC (by rw [h, hC8]))
    have h4le : 4 ≤ Nat.card ↥Ct := hW4 ▸ Subgroup.card_le_of_le hWCt
    have hle8 : Nat.card ↥Ct ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    have hCt4 : Nat.card ↥Ct = 4 := by
      have h5 : Nat.card ↥Ct ≠ 5 := fun h => by rw [h] at hdvd; omega
      have h6 : Nat.card ↥Ct ≠ 6 := fun h => by rw [h] at hdvd; omega
      have h7 : Nat.card ↥Ct ≠ 7 := fun h => by rw [h] at hdvd; omega
      omega
    have hCtW : zpowers t ⊔ zpowers z = Ct :=
      Subgroup.eq_of_le_of_card_ge hWCt (by rw [hCt4, hW4])
    have hcCt : c ∈ Ct := ⟨hc, Subgroup.mem_centralizer_singleton_iff.2 hct⟩
    rw [hCtW]
    exact hcCt

end CFSG.OddStandard.SmallF3.Omega
