module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace GL83.I243.Inner

open CFSG.Open

theorem card_center_le_of_not_isMulCommutative {T : Type*} [Group T] [Finite T] {p : ℕ}
    [Fact p.Prime] (hT : IsPGroup p T) (hnc : ¬ IsMulCommutative T)
    (hcard : Nat.card T ≤ p ^ 3) : Nat.card (Subgroup.center T) ≤ p := by
  have hQ : IsPGroup p (T ⧸ Subgroup.center T) := hT.to_quotient _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have hk2 : 2 ≤ k := by
    by_contra hlt
    apply hnc
    haveI : IsCyclic (T ⧸ Subgroup.center T) := by
      interval_cases k
      · haveI : Subsingleton (T ⧸ Subgroup.center T) :=
          (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
        exact isCyclic_of_subsingleton
      · exact isCyclic_of_prime_card (by simpa using hk)
    exact isMulCommutative_of_isCyclic_quotient_center_self T
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center T)
  rw [hk] at h
  have hp := (Fact.out : p.Prime)
  have hp2 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
  by_contra hgt
  push Not at hgt
  have hlt : p ^ 3 < Nat.card T := by
    rw [h]
    calc p ^ 3 = p ^ 2 * p := by ring
      _ < p ^ k * Nat.card (Subgroup.center T) :=
        Nat.mul_lt_mul_of_le_of_lt hp2 hgt (Nat.pow_pos hp.pos)
  omega

theorem exists_isElemAbelian_card_sq_of_not_isCyclic {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {A : Subgroup X} (hA : IsPGroup p A) (hncyc : ¬ IsCyclic A) :
    ∃ D ≤ A, IsElemAbelian p D ∧ Nat.card D = p ^ 2 := by
  haveI : Fact (IsPGroup p A) := ⟨hA⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hncyc
  haveI := hSel
  refine ⟨S.map A.subtype, Subgroup.map_subtype_le S, ?_, ?_⟩
  · haveI : CFSG.IsElementaryAbelian p (S.map A.subtype) := CFSG.IsElementaryAbelian.map_subtype
    exact isElemAbelian_of_isElementaryAbelian
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hScard]

theorem exists_pow_eq_one_not_central {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {T : Subgroup X} (hT : IsPGroup p T)
    (hnc : ∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x) (hcard : Nat.card T ≤ p ^ 3) :
    ∃ x ∈ T, x ^ p = 1 ∧ ∃ y ∈ T, x * y ≠ y * x := by
  have hncT : ¬ IsMulCommutative T := by
    intro hc
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact hxy (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : T) ⟨y, hy⟩))
  have hncyc : ¬ IsCyclic T := fun hcyc => hncT inferInstance
  obtain ⟨D, hDT, hD, hDcard⟩ := exists_isElemAbelian_card_sq_of_not_isCyclic hp2 hT hncyc
  by_contra hcon
  push Not at hcon
  have hDc : D.subgroupOf T ≤ Subgroup.center T := by
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro y
    have hsD : (s : X) ∈ D := hs
    exact Subtype.ext (hcon (s : X) s.2 (hD.2 _ hsD) y y.2).symm
  have h1 : Nat.card (D.subgroupOf T) ≤ Nat.card (Subgroup.center T) :=
    Subgroup.card_le_of_le hDc
  have h2 : Nat.card (D.subgroupOf T) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDT).toEquiv
  have h3 := card_center_le_of_not_isMulCommutative hT hncT hcard
  rw [h2, hDcard] at h1
  have hp := (Fact.out : p.Prime)
  have h4 : p * p ≤ p * 1 := by nlinarith [hp.pos, h1.trans h3]
  have := Nat.le_of_mul_le_mul_left h4 hp.pos
  have := hp.two_le
  omega

end GL83.I243.Inner
