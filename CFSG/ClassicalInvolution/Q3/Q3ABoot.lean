module

public import CFSG.ClassicalInvolution.Balance.Theorem5Untouched
public import CFSG.ClassicalInvolution.Q3.Q3PBranch

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance

variable {G : Type} [Group G]

theorem isElemAbelian_closure_triple {u v w : G} (hu : u * u = 1) (hv : v * v = 1)
    (hw : w * w = 1) (huv : u * v = v * u) (huw : u * w = w * u) (hvw : v * w = w * v) :
    IsElemAbelian 2 (Subgroup.closure ({u, v, w} : Set G)) := by
  refine Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl <;> assumption
  · intro s hs t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      first | rfl | assumption | exact (by assumption : _ = _).symm

theorem card_closure_triple_eq_eight [Finite G] {z a b : G} (hz : z * z = 1) (ha : a * a = 1)
    (hb : b * b = 1) (hza : z * a = a * z) (hzb : z * b = b * z) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b)
    (hnot : z ∉ Subgroup.closure ({a, b} : Set G)) :
    Nat.card (Subgroup.closure ({z, a, b} : Set G)) = 8 := by
  have hB : Nat.card (Subgroup.closure ({a, b} : Set G)) = 4 :=
    Bootstrap.card_closure_pair_eq_four ha hb ha1 hb1 hne hab
  have hcomm : ∀ s ∈ ({a, b} : Set G), z * s = s * z := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl <;> assumption
  have hle : Nat.card (Subgroup.closure ({z, a, b} : Set G)) ≤ 8 := by
    have := Theorem5.card_closure_insert_le hz hcomm
    rw [hB] at this
    simpa using this
  have hBA : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.closure ({z, a, b} : Set G) :=
    Subgroup.closure_mono (fun x hx => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)
  have hdvd : 4 ∣ Nat.card (Subgroup.closure ({z, a, b} : Set G)) :=
    hB ▸ Subgroup.card_dvd_of_le hBA
  have hpos : 0 < Nat.card (Subgroup.closure ({z, a, b} : Set G)) := Nat.card_pos
  by_contra h8
  have h4 : Nat.card (Subgroup.closure ({z, a, b} : Set G)) = 4 := by omega
  have hEq := Subgroup.eq_of_le_of_card_ge hBA (by omega)
  exact hnot (hEq ▸ Subgroup.subset_closure (by simp))

theorem IsClassicalMember3.mul_comm_of_mem {L : Subgroup G} {z : G} (h : IsClassicalMember3 L z)
    {l : G} (hl : l ∈ L) : z * l = l * z :=
  h.isCentralInvolution.central l hl

theorem bootData3_of_pair [Finite G] {Ω : Set (Subgroup G)} {L : Subgroup G} {z : G}
    (hLΩ : L ∈ Ω) (hz : IsClassicalMember3 L z) {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a)
    (hLa : L ≤ Subgroup.centralizer ({a} : Set G)) (hLb : L ≤ Subgroup.centralizer ({b} : Set G))
    (hnot : z ∉ Subgroup.closure ({a, b} : Set G)) : BootData3 Ω := by
  have hz2 : z * z = 1 := hz.isCentralInvolution.sq
  have hza : z * a = a * z := Subgroup.mem_centralizer_singleton_iff.mp (hLa hz.mem)
  have hzb : z * b = b * z := Subgroup.mem_centralizer_singleton_iff.mp (hLb hz.mem)
  refine ⟨L, z, Subgroup.closure ({z, a, b} : Set G), hLΩ, hz,
    isElemAbelian_closure_triple hz2 ha hb hza hzb hc,
    card_closure_triple_eq_eight hz2 ha hb hza hzb hc ha1 hb1 hab hnot,
    Subgroup.subset_closure (by simp), ?_⟩
  rw [Subgroup.le_centralizer_iff]
  rw [Subgroup.closure_le]
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro l hl
  rcases hs with rfl | rfl | rfl
  · exact (hz.mul_comm_of_mem hl).symm
  · exact (Subgroup.mem_centralizer_singleton_iff.mp (hLa hl))
  · exact (Subgroup.mem_centralizer_singleton_iff.mp (hLb hl))


theorem mem_closure_pair_cases {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {x : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hba : b * a = a * b := hab.symm
  have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hab' : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, hba, mul_assoc]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl <;> simp
  | one => simp
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [mul_assoc, ha, hb, ha', hab', hba]
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl <;> simp [mul_inv_rev, ia, ib, hba]

theorem exists_mem_not_mem_finset [Finite G] (A : Subgroup G) (S : Finset G)
    (h : S.card < Nat.card A) : ∃ x ∈ A, x ∉ S := by
  by_contra hcon
  push Not at hcon
  have hsub : (A : Set G) ⊆ (S : Set G) := fun x hx => by exact_mod_cast hcon x hx
  have : Nat.card A ≤ S.card := by
    calc Nat.card A = Nat.card (A : Set G) := rfl
      _ ≤ Nat.card (S : Set G) := Nat.card_mono (Set.toFinite _) hsub
      _ = S.card := Nat.card_eq_finsetCard S
  omega

theorem exists_pair_of_bootData3 [Finite G] {Ω : Set (Subgroup G)} (h : BootData3 Ω) :
    ∃ (L : Subgroup G) (z a b : G), L ∈ Ω ∧ IsClassicalMember3 L z ∧ a * a = 1 ∧ b * b = 1 ∧
      a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a ∧
      L ≤ Subgroup.centralizer ({a} : Set G) ∧ L ≤ Subgroup.centralizer ({b} : Set G) ∧
      z ∉ Subgroup.closure ({a, b} : Set G) := by
  classical
  obtain ⟨L, z, A, hLΩ, hz, hA, hcard, hzA, hLA⟩ := h
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by simpa [pow_two] using hA.2 x hx
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  obtain ⟨a, haA, haS⟩ := exists_mem_not_mem_finset A ({1, z} : Finset G) (by
    rw [hcard]; exact lt_of_le_of_lt (Finset.card_insert_le _ _) (by simp))
  obtain ⟨b, hbA, hbS⟩ := exists_mem_not_mem_finset A ({1, z, a, a * z} : Finset G) (by
    rw [hcard]
    refine lt_of_le_of_lt (Finset.card_insert_le _ _) (Nat.succ_lt_succ ?_)
    refine lt_of_le_of_lt (Finset.card_insert_le _ _) (Nat.succ_lt_succ ?_)
    refine lt_of_le_of_lt (Finset.card_insert_le _ _) (Nat.succ_lt_succ ?_)
    simp)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at haS hbS
  obtain ⟨ha1, haz⟩ := haS
  obtain ⟨hb1, hbz, hba, hbaz⟩ := hbS
  have haa := hsq a haA
  have hbb := hsq b hbA
  have hab := hcomm a haA b hbA
  have hzz : z * z = 1 := hz.isCentralInvolution.sq
  have hza := hcomm z hzA a haA
  have hLcent : ∀ x ∈ A, L ≤ Subgroup.centralizer ({x} : Set G) := fun x hx l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hLA hl) x hx).symm
  refine ⟨L, z, a, b, hLΩ, hz, haa, hbb, ha1, hb1, Ne.symm hba, hab, hLcent a haA,
    hLcent b hbA, fun hzc => ?_⟩
  rcases mem_closure_pair_cases haa hbb hab hzc with h1 | h1 | h1 | h1
  · exact hz.ne_one h1
  · exact haz h1.symm
  · exact hbz h1.symm
  · apply hbaz
    have : b = a * z := by
      calc b = a * (a * b) := by rw [← mul_assoc, haa, one_mul]
        _ = a * z := by rw [← h1]
    exact this

theorem bootData3_iff_exists_pair [Finite G] {Ω : Set (Subgroup G)} :
    BootData3 Ω ↔
      ∃ (L : Subgroup G) (z a b : G), L ∈ Ω ∧ IsClassicalMember3 L z ∧ a * a = 1 ∧ b * b = 1 ∧
        a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a ∧
        L ≤ Subgroup.centralizer ({a} : Set G) ∧ L ≤ Subgroup.centralizer ({b} : Set G) ∧
        z ∉ Subgroup.closure ({a, b} : Set G) := by
  refine ⟨exists_pair_of_bootData3, ?_⟩
  rintro ⟨L, z, a, b, hLΩ, hz, ha, hb, ha1, hb1, hab, hc, hLa, hLb, hnot⟩
  exact bootData3_of_pair hLΩ hz ha hb ha1 hb1 hab hc hLa hLb hnot

theorem eq_or_eq_or_eq_mul_of_not_bootData3 [Finite G] {Ω : Set (Subgroup G)}
    (hB : ¬ BootData3 Ω) {L : Subgroup G} {z : G} (hLΩ : L ∈ Ω) (hz : IsClassicalMember3 L z)
    {a b : G} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hc : a * b = b * a) (hLa : L ≤ Subgroup.centralizer ({a} : Set G))
    (hLb : L ≤ Subgroup.centralizer ({b} : Set G)) : z = a ∨ z = b ∨ z = a * b := by
  by_contra hcon
  push Not at hcon
  refine hB (bootData3_of_pair hLΩ hz ha hb ha1 hb1 hab hc hLa hLb fun hzc => ?_)
  rcases mem_closure_pair_cases ha hb hc hzc with h1 | h1 | h1 | h1
  · exact hz.ne_one h1
  · exact hcon.1 h1
  · exact hcon.2.1 h1
  · exact hcon.2.2 h1

theorem mem_fourGroup_of_not_bootData3 [Finite G] {Ω : Set (Subgroup G)} (hB : ¬ BootData3 Ω)
    {L : Subgroup G} {z : G} (hLΩ : L ∈ Ω) (hz : IsClassicalMember3 L z) {F : Subgroup G}
    (hsq : ∀ x ∈ F, x * x = 1) (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    (hcard : Nat.card F = 4) (hLF : L ≤ Subgroup.centralizer (F : Set G)) : z ∈ F := by
  classical
  obtain ⟨a, haF, haS⟩ := exists_mem_not_mem_finset F ({1} : Finset G) (by simp [hcard])
  obtain ⟨b, hbF, hbS⟩ := exists_mem_not_mem_finset F ({1, a} : Finset G) (by
    rw [hcard]
    exact lt_of_le_of_lt (Finset.card_insert_le _ _) (by simp))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at haS hbS
  obtain ⟨hb1, hba⟩ := hbS
  have hcent : ∀ x ∈ F, L ≤ Subgroup.centralizer ({x} : Set G) := fun x hx l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hLF hl) x hx).symm
  have hle : Subgroup.closure ({a, b} : Set G) ≤ F := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  have hc4 : Nat.card (Subgroup.closure ({a, b} : Set G)) = 4 :=
    Bootstrap.card_closure_pair_eq_four (hsq a haF) (hsq b hbF) haS hb1 (Ne.symm hba)
      (hcomm a haF b hbF)
  have heq : Subgroup.closure ({a, b} : Set G) = F :=
    Subgroup.eq_of_le_of_card_ge hle (by omega)
  rw [← heq]
  have hz3 := eq_or_eq_or_eq_mul_of_not_bootData3 hB hLΩ hz (hsq a haF) (hsq b hbF) haS hb1
    (Ne.symm hba) (hcomm a haF b hbF) (hcent a haF) (hcent b hbF)
  rcases hz3 with h | h | h <;> rw [h]
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

end CFSG.ClassicalInvolution.Q3
