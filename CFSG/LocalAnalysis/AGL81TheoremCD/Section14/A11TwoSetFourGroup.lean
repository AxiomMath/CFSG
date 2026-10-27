module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A11TwoSetThree
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

private abbrev A11 := alternatingGroup (Fin 11)

private def a0 : A11 :=
  ⟨c[0, 1, 2], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def b0 : A11 :=
  ⟨c[3, 4, 5], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def c0 : A11 :=
  ⟨c[6, 7, 8], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def s0 : A11 := a0 * b0

private def vv1 : A11 :=
  ⟨c[6, 7] * c[9, 10], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def vv2 : A11 :=
  ⟨c[0, 3] * c[1, 4] * c[2, 5] * c[9, 10], by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private theorem a0_ord : orderOf a0 = 3 := by
  apply orderOf_eq_prime (by decide) (by decide)

private theorem b0_ord : orderOf b0 = 3 := by
  apply orderOf_eq_prime (by decide) (by decide)

private theorem c0_ord : orderOf c0 = 3 := by
  apply orderOf_eq_prime (by decide) (by decide)

private theorem s0_ord : orderOf s0 = 3 := by
  apply orderOf_eq_prime (by decide) (by decide)

private theorem a0_comm_b0 : Commute a0 b0 := show a0 * b0 = b0 * a0 by decide

private theorem a0_comm_c0 : Commute a0 c0 := show a0 * c0 = c0 * a0 by decide

private theorem b0_comm_c0 : Commute b0 c0 := show b0 * c0 = c0 * b0 by decide

private theorem a0_disj_b0 : (a0 : Perm (Fin 11)).Disjoint b0 := by
  rw [Equiv.Perm.disjoint_iff_disjoint_support]; decide

private theorem zpowers_disjoint_a0_b0 :
    Subgroup.zpowers a0 ⊓ Subgroup.zpowers b0 = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hx, hy⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [Subgroup.mem_bot]
  have hd := a0_disj_b0.zpow_disjoint_zpow m n
  have hd'' : ((a0 ^ m : A11) : Perm (Fin 11)).Disjoint ((b0 ^ n : A11) : Perm (Fin 11)) := hd
  rw [hn] at hd''
  exact Subtype.ext (Equiv.Perm.disjoint_refl_iff.mp hd'')

private theorem card_zp_a0 : Nat.card ↥(Subgroup.zpowers a0) = 3 := by
  rw [Nat.card_zpowers, a0_ord]

private theorem card_zp_b0 : Nat.card ↥(Subgroup.zpowers b0) = 3 := by
  rw [Nat.card_zpowers, b0_ord]

private theorem card_zp_c0 : Nat.card ↥(Subgroup.zpowers c0) = 3 := by
  rw [Nat.card_zpowers, c0_ord]

private theorem commute_zp_a0_b0 :
    ∀ x ∈ Subgroup.zpowers a0, ∀ y ∈ Subgroup.zpowers b0, Commute x y := by
  intro x hx y hy
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact a0_comm_b0.zpow_zpow m n

private theorem card_sup_ab : Nat.card ↥(Subgroup.zpowers a0 ⊔ Subgroup.zpowers b0) = 9 := by
  rw [CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers a0) (Subgroup.zpowers b0)
    commute_zp_a0_b0 zpowers_disjoint_a0_b0, card_zp_a0, card_zp_b0]

private theorem mem_sup_ab_support {x : A11}
    (hx : x ∈ Subgroup.zpowers a0 ⊔ Subgroup.zpowers b0) :
    (x : Perm (Fin 11)).support ≤ ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := (CFSG.mem_sup_of_commute commute_zp_a0_b0).mp hx
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  calc
    (((a0 ^ m * b0 ^ n : A11) : Perm (Fin 11))).support
        ≤ ((a0 ^ m : A11) : Perm (Fin 11)).support ⊔
          ((b0 ^ n : A11) : Perm (Fin 11)).support :=
      Equiv.Perm.support_mul_le _ _
    _ ≤ ({0, 1, 2} : Finset (Fin 11)) ⊔ ({3, 4, 5} : Finset (Fin 11)) := by
      apply sup_le_sup
      · calc ((a0 ^ m : A11) : Perm (Fin 11)).support ≤ (a0 : Perm (Fin 11)).support := by
              simpa using Equiv.Perm.support_zpow_le (a0 : Perm (Fin 11)) m
          _ = ({0, 1, 2} : Finset (Fin 11)) := by decide
      · calc ((b0 ^ n : A11) : Perm (Fin 11)).support ≤ (b0 : Perm (Fin 11)).support := by
              simpa using Equiv.Perm.support_zpow_le (b0 : Perm (Fin 11)) n
          _ = ({3, 4, 5} : Finset (Fin 11)) := by decide
    _ = ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)) := by decide

private theorem mem_zp_c0_support {x : A11} (hx : x ∈ Subgroup.zpowers c0) :
    (x : Perm (Fin 11)).support ≤ ({6, 7, 8} : Finset (Fin 11)) := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  calc ((c0 ^ m : A11) : Perm (Fin 11)).support ≤ (c0 : Perm (Fin 11)).support := by
        simpa using Equiv.Perm.support_zpow_le (c0 : Perm (Fin 11)) m
    _ = ({6, 7, 8} : Finset (Fin 11)) := by decide

private theorem disjoint_sup_ab_c0 :
    (Subgroup.zpowers a0 ⊔ Subgroup.zpowers b0) ⊓ Subgroup.zpowers c0 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxab, hxc⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  by_contra hxne
  have hsuppab := mem_sup_ab_support hxab
  have hsuppc := mem_zp_c0_support hxc
  have hnecard : ((x : Perm (Fin 11)).support.card ≠ 0) := by
    intro h0
    apply hxne
    exact Subtype.ext (Equiv.Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp h0))
  obtain ⟨y, hy⟩ := Finset.card_ne_zero.mp hnecard
  exact (by decide : ∀ a : Fin 11,
    a ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 11)) →
    a ∈ ({6, 7, 8} : Finset (Fin 11)) → False) y (hsuppab hy) (hsuppc hy)

private theorem commute_sup_ab_c0 :
    ∀ x ∈ Subgroup.zpowers a0 ⊔ Subgroup.zpowers b0,
      ∀ y ∈ Subgroup.zpowers c0, Commute x y := by
  intro x hx y hy
  obtain ⟨u, hu, v, hv, rfl⟩ := (CFSG.mem_sup_of_commute commute_zp_a0_b0).mp hx
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  obtain ⟨p, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h1 : Commute (a0 ^ m) (c0 ^ p) := a0_comm_c0.zpow_zpow m p
  have h2 : Commute (b0 ^ n) (c0 ^ p) := b0_comm_c0.zpow_zpow n p
  exact h1.mul_left h2

private theorem card_sup_abc :
    Nat.card ↥((Subgroup.zpowers a0 ⊔ Subgroup.zpowers b0) ⊔ Subgroup.zpowers c0) = 27 := by
  rw [CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers a0 ⊔ Subgroup.zpowers b0)
    (Subgroup.zpowers c0) commute_sup_ab_c0 disjoint_sup_ab_c0, card_sup_ab, card_zp_c0]

private theorem b0_mem_closure : b0 ∈ Subgroup.closure ({s0, a0, c0} : Set A11) := by
  have hs : s0 ∈ Subgroup.closure ({s0, a0, c0} : Set A11) := Subgroup.subset_closure (by simp)
  have ha : a0 ∈ Subgroup.closure ({s0, a0, c0} : Set A11) := Subgroup.subset_closure (by simp)
  have h : a0⁻¹ ∈ Subgroup.closure ({s0, a0, c0} : Set A11) :=
    (Subgroup.closure ({s0, a0, c0} : Set A11)).inv_mem ha
  have hm := (Subgroup.closure ({s0, a0, c0} : Set A11)).mul_mem hs h
  have heq : a0 * b0 * a0⁻¹ = b0 := by
    calc a0 * b0 * a0⁻¹ = (b0 * a0) * a0⁻¹ := by rw [a0_comm_b0.eq]
      _ = b0 := by group
  simpa [s0, mul_assoc, heq] using hm

private theorem closure_eq_sup :
    Subgroup.closure ({s0, a0, c0} : Set A11) =
      (Subgroup.zpowers a0 ⊔ Subgroup.zpowers b0) ⊔ Subgroup.zpowers c0 := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left
        (show s0 ∈ Subgroup.zpowers a0 ⊔ Subgroup.zpowers b0 from by
          simpa [s0] using
            Subgroup.mul_mem_sup (Subgroup.mem_zpowers a0) (Subgroup.mem_zpowers b0))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers a0))
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c0)
  · apply sup_le
    · apply sup_le
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      · exact Subgroup.zpowers_le.mpr b0_mem_closure
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))

private theorem card_closure_abc :
    Nat.card ↥(Subgroup.closure ({s0, a0, c0} : Set A11)) = 27 := by
  rw [closure_eq_sup, card_sup_abc]

private theorem isElemAbelian_abc :
    CFSG.Open.IsElemAbelian 3 (Subgroup.closure ({s0, a0, c0} : Set A11)) := by
  have hA : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers a0) :=
    CFSG.Open.isElemAbelian_zpowers (by decide : a0 ^ 3 = 1)
  have hB : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers b0) :=
    CFSG.Open.isElemAbelian_zpowers (by decide : b0 ^ 3 = 1)
  have hC : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers c0) :=
    CFSG.Open.isElemAbelian_zpowers (by decide : c0 ^ 3 = 1)
  have hAB : CFSG.Open.IsElemAbelian 3
      (Subgroup.zpowers a0 ⊔ Subgroup.zpowers b0) :=
    hA.sup_of_commute hB (fun x hx y hy => (commute_zp_a0_b0 x hx y hy).eq)
  have hABC : CFSG.Open.IsElemAbelian 3
      ((Subgroup.zpowers a0 ⊔ Subgroup.zpowers b0) ⊔ Subgroup.zpowers c0) :=
    hAB.sup_of_commute hC (fun x hx y hy => (commute_sup_ab_c0 x hx y hy).eq)
  rwa [closure_eq_sup]

private theorem mem_closure_iff_fin (x : A11) :
    x ∈ Subgroup.closure ({s0, a0, c0} : Set A11) ↔
      ∃ i j k : Fin 3, x = a0 ^ (i : ℕ) * b0 ^ (j : ℕ) * c0 ^ (k : ℕ) := by
  constructor
  · intro hx
    rw [closure_eq_sup] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := (CFSG.mem_sup_of_commute commute_sup_ab_c0).mp hx
    obtain ⟨p, hp, q, hq, rfl⟩ := (CFSG.mem_sup_of_commute commute_zp_a0_b0).mp hu
    rw [mem_zpowers_iff_mem_range_orderOf, a0_ord] at hp
    rw [mem_zpowers_iff_mem_range_orderOf, b0_ord] at hq
    rw [mem_zpowers_iff_mem_range_orderOf, c0_ord] at hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨⟨i, by simpa using hi⟩, ⟨j, by simpa using hj⟩,
      ⟨k, by simpa using hk⟩, rfl⟩
  · rintro ⟨i, j, k, rfl⟩
    let J := Subgroup.closure ({s0, a0, c0} : Set A11)
    have ha : a0 ∈ J := Subgroup.subset_closure (by simp)
    have hc : c0 ∈ J := Subgroup.subset_closure (by simp)
    exact J.mul_mem (J.mul_mem (J.pow_mem ha i) (J.pow_mem b0_mem_closure j)) (J.pow_mem hc k)

private abbrev f (i j k : Fin 3) : A11 :=
  a0 ^ (i : ℕ) * b0 ^ (j : ℕ) * c0 ^ (k : ℕ)

private theorem support_triple_check :
    ∀ i j k i' j' k' : Fin 3, ((f i j k : A11) : Perm (Fin 11)).support.card = 6 →
      ((f i' j' k' : Perm (Fin 11)).support.card ≠ 6 ∨
       ((f i j k * f i' j' k' : A11) : Perm (Fin 11)).support.card ≠ 6 ∨
       (((f i j k) ^ 2 * f i' j' k' : A11) : Perm (Fin 11)).support.card ≠ 6) := by
  decide

private theorem ne_one_and_mul_ne_one_of_not_mem_zpowers {y1 y2 : A11}
    (hy2 : y2 ∉ Subgroup.zpowers y1) :
    y2 ≠ 1 ∧ y1 * y2 ≠ 1 ∧ y1 ^ 2 * y2 ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hy2
    rw [h]
    exact Subgroup.one_mem _
  · intro hprod
    apply hy2
    have hy2eq : y2 = y1⁻¹ := by
      calc y2 = y1⁻¹ * (y1 * y2) := by group
        _ = y1⁻¹ * 1 := by rw [hprod]
        _ = y1⁻¹ := by simp
    rw [hy2eq]
    exact Subgroup.zpow_mem (Subgroup.zpowers y1) (Subgroup.mem_zpowers y1) (-1)
  · intro hprod
    apply hy2
    have hy2eq : y2 = (y1 ^ 2)⁻¹ := by
      calc y2 = (y1 ^ 2)⁻¹ * (y1 ^ 2 * y2) := by group
        _ = (y1 ^ 2)⁻¹ * 1 := by rw [hprod]
        _ = (y1 ^ 2)⁻¹ := by simp
    rw [hy2eq]
    exact Subgroup.inv_mem (Subgroup.zpowers y1)
      (Subgroup.pow_mem (Subgroup.zpowers y1) (Subgroup.mem_zpowers y1) 2)

private theorem standard_subgroup_bound :
    ∀ Y : Subgroup A11, Y ≤ Subgroup.closure ({s0, a0, c0} : Set A11) →
      (∀ y ∈ Y, y ≠ 1 → (y : Perm (Fin 11)).support.card = 6) → Nat.card ↥Y ≤ 3 := by
  intro Y hYle hYsupp
  by_contra hle
  have hdvd : Nat.card ↥Y ∣ 27 := by
    have h := Subgroup.card_dvd_of_le hYle
    rwa [card_closure_abc] at h
  have hdvd' : Nat.card ↥Y ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num]
    exact hdvd
  have hge : 9 ≤ Nat.card ↥Y := by
    obtain ⟨m, hm, hEq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd'
    have hpos : 0 < Nat.card ↥Y := Nat.card_pos
    interval_cases m <;> simp [hEq] at * <;> omega
  have hYne : Y ≠ ⊥ := by
    intro hbot
    rw [hbot] at hge
    simp at hge
  obtain ⟨y1Y, hy1neY⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
  let y1 : A11 := y1Y.1
  have hy1Y : y1 ∈ Y := y1Y.2
  have hy1ne : y1 ≠ 1 := fun h => hy1neY (Subtype.ext h)
  have hy1J : y1 ∈ Subgroup.closure ({s0, a0, c0} : Set A11) := hYle hy1Y
  have hy1pow : y1 ^ 3 = 1 := isElemAbelian_abc.2 y1 hy1J
  have hy1ord : orderOf y1 = 3 := orderOf_eq_prime hy1pow hy1ne
  have hcardzp : Nat.card ↥(Subgroup.zpowers y1) = 3 := by
    rw [Nat.card_zpowers, hy1ord]
  have hnotle : ¬ Y ≤ Subgroup.zpowers y1 := by
    intro hleY
    have hcardle : Nat.card ↥Y ≤ Nat.card ↥(Subgroup.zpowers y1) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hleY) (Subgroup.inclusion_injective hleY)
    omega
  obtain ⟨y2, hy2Y, hy2not⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hy1supp : ((y1 : A11) : Perm (Fin 11)).support.card = 6 := hYsupp y1 hy1Y hy1ne
  obtain ⟨i, j, k, hijk⟩ := (mem_closure_iff_fin y1).mp hy1J
  obtain ⟨i', j', k', hi'j'k'⟩ := (mem_closure_iff_fin y2).mp (hYle hy2Y)
  have hpre : ((f i j k : A11) : Perm (Fin 11)).support.card = 6 := by
    rw [show f i j k = y1 from hijk.symm]
    exact hy1supp
  have hcheck := support_triple_check i j k i' j' k' hpre
  obtain ⟨hy2ne, hy12ne, hy1sq2ne⟩ :=
    ne_one_and_mul_ne_one_of_not_mem_zpowers hy2not
  have h2supp : ((f i' j' k' : A11) : Perm (Fin 11)).support.card = 6 := by
    rw [show f i' j' k' = y2 from hi'j'k'.symm]
    exact hYsupp y2 hy2Y hy2ne
  have h12supp : ((f i j k * f i' j' k' : A11) : Perm (Fin 11)).support.card = 6 := by
    rw [show f i j k = y1 from hijk.symm, show f i' j' k' = y2 from hi'j'k'.symm]
    exact hYsupp (y1 * y2) (Y.mul_mem hy1Y hy2Y) hy12ne
  have h1sq2supp : (((f i j k) ^ 2 * f i' j' k' : A11) : Perm (Fin 11)).support.card = 6 := by
    rw [show f i j k = y1 from hijk.symm, show f i' j' k' = y2 from hi'j'k'.symm]
    exact hYsupp (y1 ^ 2 * y2) (Y.mul_mem (Y.pow_mem hy1Y 2) hy2Y) hy1sq2ne
  rcases hcheck with h | h | h
  · exact h h2supp
  · exact h h12supp
  · exact h h1sq2supp

private theorem a0_mem_stab : a0 ∈ a11TwoSetStab 9 10 := by
  change ((a0 : Perm (Fin 11)) 9 = 9 ∧ (a0 : Perm (Fin 11)) 10 = 10) ∨
    ((a0 : Perm (Fin 11)) 9 = 10 ∧ (a0 : Perm (Fin 11)) 10 = 9)
  left; constructor <;> decide

private theorem c0_mem_stab : c0 ∈ a11TwoSetStab 9 10 := by
  change ((c0 : Perm (Fin 11)) 9 = 9 ∧ (c0 : Perm (Fin 11)) 10 = 10) ∨
    ((c0 : Perm (Fin 11)) 9 = 10 ∧ (c0 : Perm (Fin 11)) 10 = 9)
  left; constructor <;> decide

private theorem s0_mem_stab : s0 ∈ a11TwoSetStab 9 10 := by
  change ((s0 : Perm (Fin 11)) 9 = 9 ∧ (s0 : Perm (Fin 11)) 10 = 10) ∨
    ((s0 : Perm (Fin 11)) 9 = 10 ∧ (s0 : Perm (Fin 11)) 10 = 9)
  left; constructor <;> decide

private theorem vv1_mem_stab : vv1 ∈ a11TwoSetStab 9 10 := by
  change ((vv1 : Perm (Fin 11)) 9 = 9 ∧ (vv1 : Perm (Fin 11)) 10 = 10) ∨
    ((vv1 : Perm (Fin 11)) 9 = 10 ∧ (vv1 : Perm (Fin 11)) 10 = 9)
  right; constructor <;> decide

private theorem vv2_mem_stab : vv2 ∈ a11TwoSetStab 9 10 := by
  change ((vv2 : Perm (Fin 11)) 9 = 9 ∧ (vv2 : Perm (Fin 11)) 10 = 10) ∨
    ((vv2 : Perm (Fin 11)) 9 = 10 ∧ (vv2 : Perm (Fin 11)) 10 = 9)
  right; constructor <;> decide

private theorem vv1_cent : vv1 ∈ Subgroup.centralizer ({s0} : Set A11) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  decide

private theorem vv2_cent : vv2 ∈ Subgroup.centralizer ({s0} : Set A11) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  decide

private theorem conj_mem_stab {g x : A11} (hg : g ∈ a11TwoSetStab 9 10)
    (hx : x ∈ a11TwoSetStab 9 10) :
    MulAut.conj g⁻¹ x ∈ a11TwoSetStab 9 10 := by
  let S : Subgroup A11 := a11TwoSetStab 9 10
  have hginv : g⁻¹ ∈ S := S.inv_mem hg
  have h : g⁻¹ * x * (g⁻¹)⁻¹ ∈ S := S.mul_mem (S.mul_mem hginv hx) hg
  simpa [MulAut.conj_apply, inv_inv] using h

private theorem card_support_conj_a11 (g x : A11) :
    ((MulAut.conj g x : A11) : Perm (Fin 11)).support.card =
      (x : Perm (Fin 11)).support.card := by
  have h := Equiv.Perm.card_support_conj (σ := (g : Perm (Fin 11)))
    (τ := (x : Perm (Fin 11)))
  simpa [MulAut.conj_apply] using h

private theorem conj_c1c3_data {g σ c1 c3 : A11}
    (hg : g ∈ a11TwoSetStab 9 10)
    (hσeq : σ = MulAut.conj g⁻¹ s0)
    (hc1 : c1 = MulAut.conj g⁻¹ a0)
    (hc3 : c3 = MulAut.conj g⁻¹ c0) :
    c1 ∈ a11TwoSetStab 9 10 ∧ c3 ∈ a11TwoSetStab 9 10 ∧
    orderOf c1 = 3 ∧ orderOf c3 = 3 ∧
    (c1 : Perm (Fin 11)).support.card = 3 ∧
    (c3 : Perm (Fin 11)).support.card = 3 ∧
    ((σ * c3 : A11) : Perm (Fin 11)).support.card = 9 ∧
    Commute σ c1 ∧ Commute σ c3 ∧ Commute c1 c3 := by
  subst c1
  subst c3
  have hc1S : MulAut.conj g⁻¹ a0 ∈ a11TwoSetStab 9 10 :=
    conj_mem_stab hg a0_mem_stab
  have hc3S : MulAut.conj g⁻¹ c0 ∈ a11TwoSetStab 9 10 :=
    conj_mem_stab hg c0_mem_stab
  have hc1ord : orderOf (MulAut.conj g⁻¹ a0) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact a0_ord
  have hc3ord : orderOf (MulAut.conj g⁻¹ c0) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact c0_ord
  have hc1supp : ((MulAut.conj g⁻¹ a0 : A11) : Perm (Fin 11)).support.card = 3 := by
    rw [card_support_conj_a11]
    decide
  have hc3supp : ((MulAut.conj g⁻¹ c0 : A11) : Perm (Fin 11)).support.card = 3 := by
    rw [card_support_conj_a11]
    decide
  have hσc3 : σ * MulAut.conj g⁻¹ c0 = MulAut.conj g⁻¹ (s0 * c0) := by
    rw [hσeq, ← map_mul]
  have hσc3supp :
      ((σ * MulAut.conj g⁻¹ c0 : A11) : Perm (Fin 11)).support.card = 9 := by
    rw [hσc3, card_support_conj_a11]
    decide
  have hcommσc1 : Commute σ (MulAut.conj g⁻¹ a0) := by
    have h := (show Commute s0 a0 from show s0 * a0 = a0 * s0 by decide).conj g⁻¹
    rw [hσeq]
    simpa [MulAut.conj_apply] using h
  have hcommσc3 : Commute σ (MulAut.conj g⁻¹ c0) := by
    have h := (show Commute s0 c0 from show s0 * c0 = c0 * s0 by decide).conj g⁻¹
    rw [hσeq]
    simpa [MulAut.conj_apply] using h
  have hcommc1c3 : Commute (MulAut.conj g⁻¹ a0) (MulAut.conj g⁻¹ c0) := by
    have h := a0_comm_c0.conj g⁻¹
    simpa [MulAut.conj_apply] using h
  exact ⟨hc1S, hc3S, hc1ord, hc3ord, hc1supp, hc3supp, hσc3supp,
    hcommσc1, hcommσc3, hcommc1c3⟩

private theorem conj_closure_card {g σ : A11}
    (hσeq : σ = MulAut.conj g⁻¹ s0) :
    Subgroup.closure ({σ, MulAut.conj g⁻¹ a0, MulAut.conj g⁻¹ c0} : Set A11) =
      (Subgroup.closure ({s0, a0, c0} : Set A11)).map
        (MulAut.conj g⁻¹).toMonoidHom ∧
    Nat.card ↥(Subgroup.closure
      ({σ, MulAut.conj g⁻¹ a0, MulAut.conj g⁻¹ c0} : Set A11)) = 27 := by
  have hJmap : Subgroup.closure
      ({σ, MulAut.conj g⁻¹ a0, MulAut.conj g⁻¹ c0} : Set A11) =
      (Subgroup.closure ({s0, a0, c0} : Set A11)).map
        (MulAut.conj g⁻¹).toMonoidHom := by
    calc Subgroup.closure ({σ, MulAut.conj g⁻¹ a0, MulAut.conj g⁻¹ c0} : Set A11) =
          Subgroup.closure ((MulAut.conj g⁻¹).toMonoidHom ''
            ({s0, a0, c0} : Set A11)) := by
            congr 1
            ext x
            constructor
            · rintro (rfl | rfl | rfl)
              · exact ⟨s0, by simp, hσeq.symm⟩
              · exact ⟨a0, by simp, rfl⟩
              · exact ⟨c0, by simp, rfl⟩
            · rintro ⟨y, hy, rfl⟩
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
              rcases hy with rfl | rfl | rfl
              · exact Or.inl hσeq.symm
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
      _ = (Subgroup.closure ({s0, a0, c0} : Set A11)).map
            (MulAut.conj g⁻¹).toMonoidHom :=
          (MonoidHom.map_closure (MulAut.conj g⁻¹).toMonoidHom _).symm
  refine ⟨hJmap, ?_⟩
  rw [hJmap, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  exact card_closure_abc

private theorem conj_subgroup_bound {g σ : A11}
    (hJ : Subgroup.closure ({σ, MulAut.conj g⁻¹ a0, MulAut.conj g⁻¹ c0} : Set A11) =
      (Subgroup.closure ({s0, a0, c0} : Set A11)).map
        (MulAut.conj g⁻¹).toMonoidHom) :
    ∀ Y : Subgroup A11,
      Y ≤ Subgroup.closure ({σ, MulAut.conj g⁻¹ a0, MulAut.conj g⁻¹ c0} : Set A11) →
      (∀ y ∈ Y, y ≠ 1 → (y : Perm (Fin 11)).support.card = 6) →
        Nat.card ↥Y ≤ 3 := by
  intro Y hY hYsupp
  let Y0 : Subgroup A11 := Y.comap (MulAut.conj g⁻¹).toMonoidHom
  have hY0le : Y0 ≤ Subgroup.closure ({s0, a0, c0} : Set A11) := by
    intro x hx
    have hφxY : MulAut.conj g⁻¹ x ∈ Y := hx
    have hφxJ : MulAut.conj g⁻¹ x ∈
        Subgroup.closure ({σ, MulAut.conj g⁻¹ a0, MulAut.conj g⁻¹ c0} : Set A11) :=
      hY hφxY
    rw [hJ] at hφxJ
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hφxJ
    have hyx : y = x := (MulAut.conj g⁻¹).injective hyeq
    rwa [hyx] at hy
  have hY0supp : ∀ y ∈ Y0, y ≠ 1 → (y : Perm (Fin 11)).support.card = 6 := by
    intro y hy hyne
    have hφyY : MulAut.conj g⁻¹ y ∈ Y := hy
    have hφy_ne : MulAut.conj g⁻¹ y ≠ 1 := by
      intro h1
      apply hyne
      exact (MulAut.conj g⁻¹).injective (by simpa using h1)
    have h := hYsupp (MulAut.conj g⁻¹ y) hφyY hφy_ne
    rwa [card_support_conj_a11] at h
  have hY0card : Nat.card ↥Y0 ≤ 3 := standard_subgroup_bound Y0 hY0le hY0supp
  have hcardcomap : Nat.card ↥Y0 = Nat.card ↥Y := by
    change Nat.card ↥(Y.comap (MulAut.conj g⁻¹).toMonoidHom) = Nat.card ↥Y
    rw [Subgroup.comap_equiv_eq_map_symm' (MulAut.conj g⁻¹) Y,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).symm.injective]
  omega

private theorem conj_v_data {g σ v1 v2 c1 c3 : A11}
    (hg : g ∈ a11TwoSetStab 9 10)
    (hσeq : σ = MulAut.conj g⁻¹ s0)
    (hv1 : v1 = MulAut.conj g⁻¹ vv1)
    (hv2 : v2 = MulAut.conj g⁻¹ vv2)
    (hc1 : c1 = MulAut.conj g⁻¹ a0)
    (hc3 : c3 = MulAut.conj g⁻¹ c0) :
    v1 ∈ a11TwoSetStab 9 10 ⊓ Subgroup.centralizer ({σ} : Set A11) ∧
    v2 ∈ a11TwoSetStab 9 10 ⊓ Subgroup.centralizer ({σ} : Set A11) ∧
    v1 * c1 * v1⁻¹ = c1 ∧ v1 * c3 * v1⁻¹ = c3⁻¹ ∧
    v2 * c1 * v2⁻¹ = σ * c1⁻¹ ∧ v2 * c3 * v2⁻¹ = c3 := by
  subst v1
  subst v2
  subst c1
  subst c3
  have hv1S : MulAut.conj g⁻¹ vv1 ∈ a11TwoSetStab 9 10 :=
    conj_mem_stab hg vv1_mem_stab
  have hv2S : MulAut.conj g⁻¹ vv2 ∈ a11TwoSetStab 9 10 :=
    conj_mem_stab hg vv2_mem_stab
  have hv1cent : MulAut.conj g⁻¹ vv1 ∈ Subgroup.centralizer ({σ} : Set A11) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := (show Commute vv1 s0 from
      Subgroup.mem_centralizer_singleton_iff.mp vv1_cent).conj g⁻¹
    rw [hσeq]
    simpa [MulAut.conj_apply] using h.eq
  have hv2cent : MulAut.conj g⁻¹ vv2 ∈ Subgroup.centralizer ({σ} : Set A11) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := (show Commute vv2 s0 from
      Subgroup.mem_centralizer_singleton_iff.mp vv2_cent).conj g⁻¹
    rw [hσeq]
    simpa [MulAut.conj_apply] using h.eq
  have hv1c1 : MulAut.conj g⁻¹ vv1 * MulAut.conj g⁻¹ a0 *
      (MulAut.conj g⁻¹ vv1)⁻¹ = MulAut.conj g⁻¹ a0 := by
    have h := congrArg (MulAut.conj g⁻¹) (show vv1 * a0 * vv1⁻¹ = a0 by decide)
    simpa [map_mul, map_inv] using h
  have hv1c3 : MulAut.conj g⁻¹ vv1 * MulAut.conj g⁻¹ c0 *
      (MulAut.conj g⁻¹ vv1)⁻¹ = (MulAut.conj g⁻¹ c0)⁻¹ := by
    have h := congrArg (MulAut.conj g⁻¹) (show vv1 * c0 * vv1⁻¹ = c0⁻¹ by decide)
    simpa [map_mul, map_inv] using h
  have hv2c1 : MulAut.conj g⁻¹ vv2 * MulAut.conj g⁻¹ a0 *
      (MulAut.conj g⁻¹ vv2)⁻¹ = σ * (MulAut.conj g⁻¹ a0)⁻¹ := by
    have h := congrArg (MulAut.conj g⁻¹)
      (show vv2 * a0 * vv2⁻¹ = s0 * a0⁻¹ by decide)
    rw [hσeq]
    simpa [map_mul, map_inv] using h
  have hv2c3 : MulAut.conj g⁻¹ vv2 * MulAut.conj g⁻¹ c0 *
      (MulAut.conj g⁻¹ vv2)⁻¹ = MulAut.conj g⁻¹ c0 := by
    have h := congrArg (MulAut.conj g⁻¹) (show vv2 * c0 * vv2⁻¹ = c0 by decide)
    simpa [map_mul, map_inv] using h
  exact ⟨⟨hv1S, hv1cent⟩, ⟨hv2S, hv2cent⟩, hv1c1, hv1c3, hv2c1, hv2c3⟩

theorem exists_fourGroup_of_card_support_eq_six {σ : alternatingGroup (Fin 11)}
    (hσS : σ ∈ a11TwoSetStab 9 10) (hσ : orderOf σ = 3)
    (hs : (σ : Equiv.Perm (Fin 11)).support.card = 6) :
    ∃ c₁ c₃ v₁ v₂ : alternatingGroup (Fin 11),
      c₁ ∈ a11TwoSetStab 9 10 ∧ c₃ ∈ a11TwoSetStab 9 10 ∧
      orderOf c₁ = 3 ∧ orderOf c₃ = 3 ∧
      (c₁ : Equiv.Perm (Fin 11)).support.card = 3 ∧
      (c₃ : Equiv.Perm (Fin 11)).support.card = 3 ∧
      ((σ * c₃ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 9 ∧
      Commute σ c₁ ∧ Commute σ c₃ ∧ Commute c₁ c₃ ∧
      Nat.card ↥(Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) = 27 ∧
      (∀ Y : Subgroup (alternatingGroup (Fin 11)),
        Y ≤ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) →
        (∀ y ∈ Y, y ≠ 1 → (y : Equiv.Perm (Fin 11)).support.card = 6) → Nat.card ↥Y ≤ 3) ∧
      v₁ ∈ a11TwoSetStab 9 10 ⊓ Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) ∧
      v₂ ∈ a11TwoSetStab 9 10 ⊓ Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) ∧
      v₁ * c₁ * v₁⁻¹ = c₁ ∧ v₁ * c₃ * v₁⁻¹ = c₃⁻¹ ∧
      v₂ * c₁ * v₂⁻¹ = σ * c₁⁻¹ ∧ v₂ * c₃ * v₂⁻¹ = c₃ := by
  classical
  obtain ⟨g, hgS, hg⟩ := exists_conj_eq_of_card_support_eq (σ := σ) (τ := s0)
    hσS s0_mem_stab hσ s0_ord (by rw [hs]; decide)
  have hσeq : σ = MulAut.conj g⁻¹ s0 := by
    rw [MulAut.conj_apply]
    calc σ = g⁻¹ * (g * σ * g⁻¹) * g := by group
      _ = g⁻¹ * s0 * g := by rw [hg]
  let c1 : A11 := MulAut.conj g⁻¹ a0
  let c3 : A11 := MulAut.conj g⁻¹ c0
  let v1 : A11 := MulAut.conj g⁻¹ vv1
  let v2 : A11 := MulAut.conj g⁻¹ vv2
  obtain ⟨hc1S, hc3S, hc1ord, hc3ord, hc1supp, hc3supp, hσc3supp,
    hcommσc1, hcommσc3, hcommc1c3⟩ :=
    conj_c1c3_data (g := g) (σ := σ) (c1 := c1) (c3 := c3) hgS hσeq rfl rfl
  obtain ⟨hJmap, hcardJ⟩ := conj_closure_card (g := g) (σ := σ) hσeq
  have hbound := conj_subgroup_bound (g := g) (σ := σ) hJmap
  obtain ⟨hv1mem, hv2mem, hv1c1, hv1c3, hv2c1, hv2c3⟩ :=
    conj_v_data (g := g) (σ := σ) (v1 := v1) (v2 := v2)
      (c1 := c1) (c3 := c3) hgS hσeq rfl rfl rfl rfl
  exact ⟨c1, c3, v1, v2, hc1S, hc3S, hc1ord, hc3ord, hc1supp, hc3supp,
    hσc3supp, hcommσc1, hcommσc3, hcommc1c3, hcardJ, hbound,
    hv1mem, hv2mem, hv1c1, hv1c3, hv2c1, hv2c3⟩
end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
