module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

variable {G : Type*} [Group G]

section Klein

variable {a b : G}

theorem klein_e4 (ha : a * a = 1) : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]

theorem klein_e5 (hb : b * b = 1) (hab : a * b = b * a) : b * (a * b) = a := by
  rw [hab, ← mul_assoc, hb, one_mul]

theorem klein_e6 (ha : a * a = 1) (hab : a * b = b * a) : a * b * a = b := by
  rw [hab, mul_assoc, ha, mul_one]

theorem klein_e7 (hb : b * b = 1) : a * b * b = a := by rw [mul_assoc, hb, mul_one]

theorem klein_e8 (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    a * b * (a * b) = 1 := by
  rw [mul_assoc, klein_e5 hb hab, ha]

@[expose] def klein (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Subgroup G where
  carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have e3 : b * a = a * b := hab.symm
    have e4 := klein_e4 (b := b) ha
    have e5 := klein_e5 hb hab
    have e6 := klein_e6 ha hab
    have e7 := klein_e7 (a := a) hb
    have e8 := klein_e8 ha hb hab
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp [ha, hb, e3, e4, e5, e6, e7, e8]
  inv_mem' := by
    have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rcases hx with hx | hx | hx | hx <;> rw [hx] <;> simp [ia, ib, mul_inv_rev, hab]

theorem mem_klein {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a} {x : G} :
    x ∈ klein a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

theorem klein_le {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a} {A : Subgroup G}
    (haA : a ∈ A) (hbA : b ∈ A) : klein a b ha hb hab ≤ A := by
  intro x hx
  rcases mem_klein.1 hx with h | h | h | h <;> rw [h]
  · exact A.one_mem
  · exact haA
  · exact hbA
  · exact A.mul_mem haA hbA

theorem left_mem_klein {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a} :
    a ∈ klein a b ha hb hab := mem_klein.2 (Or.inr (Or.inl rfl))

theorem klein_card {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a} (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hne : a ≠ b) : Nat.card (klein a b ha hb hab) = 4 := by
  have hset : ((klein a b ha hb hab : Subgroup G) : Set G) = {1, a, b, a * b} := by
    ext x
    exact mem_klein
  have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h1 : (1 : G) ∉ ({a, b, a * b} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨fun h => ha1 h.symm, fun h => hb1 h.symm, fun h => ?_⟩
    have := inv_eq_of_mul_eq_one_right h.symm
    exact hne (ia.symm.trans this)
  have h2 : a ∉ ({b, a * b} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨hne, fun h => ?_⟩
    have h' : a * b = a * 1 := by rw [mul_one]; exact h.symm
    exact hb1 (mul_left_cancel h')
  have h3 : b ≠ a * b := fun h => by
    have h' : 1 * b = a * b := by rw [one_mul]; exact h
    exact ha1 (mul_right_cancel h').symm
  show Nat.card ((klein a b ha hb hab : Subgroup G) : Set G) = 4
  rw [Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
    Set.ncard_pair h3]

theorem klein_isElemAbelian {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a} :
    CFSG.Open.IsElemAbelian 2 (klein a b ha hb hab) := by
  have e3 : b * a = a * b := hab.symm
  have e4 := klein_e4 (b := b) ha
  have e5 := klein_e5 hb hab
  have e6 := klein_e6 ha hab
  have e7 := klein_e7 (a := a) hb
  have e8 := klein_e8 ha hb hab
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    show x * y = y * x
    rcases mem_klein.1 hx with hx | hx | hx | hx <;> rcases mem_klein.1 hy with hy | hy | hy | hy
      <;> rw [hx, hy] <;> simp [e3, e4, e5, e6, e7]
  · rw [pow_two]
    rcases mem_klein.1 hx with h | h | h | h <;> rw [h] <;> simp [ha, hb, e8]

end Klein

variable [Finite G]

theorem exists_fourGroup_of_card {A : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hsq : ∀ x ∈ A, x * x = 1) (h4 : 4 ≤ Nat.card A) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) :
    ∃ W : Subgroup G, W ≤ A ∧ a ∈ W ∧ CFSG.Open.IsElemAbelian 2 W ∧ Nat.card W = 4 := by
  obtain ⟨b, hbA, hb1, hba⟩ : ∃ b ∈ A, b ≠ 1 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have hsub : (A : Set G) ⊆ {1, a} := fun x hx => by
      by_cases hx1 : x = 1
      · simp [hx1]
      · simp [hcon x hx hx1]
    have h2 : Nat.card A ≤ 2 := by
      calc Nat.card A = ((A : Set G)).ncard := Nat.card_coe_set_eq _
        _ ≤ ({1, a} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ({a} : Set G).ncard + 1 := Set.ncard_insert_le 1 {a}
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  have ha2 := hsq a haA
  have hb2 := hsq b hbA
  have hab := hcomm a haA b hbA
  exact ⟨klein a b ha2 hb2 hab, klein_le haA hbA, left_mem_klein, klein_isElemAbelian,
    klein_card ha1 hb1 (Ne.symm hba)⟩

theorem card_le_sq_centralizer {V : Subgroup G} (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hsq : ∀ x ∈ V, x * x = 1) {w : G} (hw : w * w = 1) (hwV : ∀ x ∈ V, w * x * w⁻¹ ∈ V) :
    Nat.card V ≤ Nat.card ↥(V ⊓ Subgroup.centralizer ({w} : Set G)) ^ 2 := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  let δ : ↥V →* ↥V := MonoidHom.mk' (fun x => ⟨x * (w * x * w⁻¹), V.mul_mem x.2 (hwV x x.2)⟩)
    (by
      intro x y
      apply Subtype.ext
      show (x : G) * y * (w * ((x : G) * y) * w⁻¹) =
        ((x : G) * (w * x * w⁻¹)) * ((y : G) * (w * y * w⁻¹))
      have hc := hcomm y y.2 _ (hwV x x.2)
      calc (x : G) * y * (w * ((x : G) * y) * w⁻¹)
          = x * y * ((w * x * w⁻¹) * (w * y * w⁻¹)) := by group
        _ = x * (y * (w * x * w⁻¹)) * (w * y * w⁻¹) := by group
        _ = x * ((w * x * w⁻¹) * y) * (w * y * w⁻¹) := by rw [hc]
        _ = ((x : G) * (w * x * w⁻¹)) * ((y : G) * (w * y * w⁻¹)) := by group)
  set C : Subgroup ↥V := (V ⊓ Subgroup.centralizer ({w} : Set G)).subgroupOf V with hC
  have hker : δ.ker ≤ C := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (x : G) * (w * x * w⁻¹) = 1 := congrArg Subtype.val hx
    have hconj : w * (x : G) * w⁻¹ = x := by
      have h1 : w * (x : G) * w⁻¹ = (x : G)⁻¹ := eq_inv_of_mul_eq_one_right hx'
      have h2 : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x x.2)
      rw [h1, h2]
    rw [hC, Subgroup.mem_subgroupOf]
    refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc (x : G) * w = (w * x * w⁻¹) * w := by rw [hconj]
      _ = w * x := by group
  have hrange : δ.range ≤ C := by
    rintro _ ⟨x, rfl⟩
    rw [hC, Subgroup.mem_subgroupOf]
    refine ⟨(δ x).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    show ((x : G) * (w * x * w⁻¹)) * w = w * ((x : G) * (w * x * w⁻¹))
    have hc := hcomm x x.2 _ (hwV x x.2)
    calc ((x : G) * (w * x * w⁻¹)) * w = w * x * w⁻¹ * x * w := by rw [← hc]
      _ = w * x * w⁻¹ * (w * (w * x * w⁻¹) * w⁻¹) * w := by
          have : w * (w * (x : G) * w⁻¹) * w⁻¹ = x := by
            rw [hwi]
            have : w * (w * (x : G) * w) * w = (w * w) * x * (w * w) := by group
            rw [this, hw]
            group
          rw [this]
      _ = w * ((x : G) * (w * x * w⁻¹)) := by group
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker
  have hq : Nat.card (↥V ⧸ δ.ker) = Nat.card δ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv
  have hC1 : Nat.card δ.ker ≤ Nat.card C := Subgroup.card_le_of_le hker
  have hC2 : Nat.card δ.range ≤ Nat.card C := Subgroup.card_le_of_le hrange
  have hC3 : Nat.card C = Nat.card ↥(V ⊓ Subgroup.centralizer ({w} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hcard, hq, pow_two, ← hC3]
  exact Nat.mul_le_mul hC2 hC1

theorem four_le_card_centralizer {V : Subgroup G} (hV2 : IsPGroup 2 V) (h8 : 8 ≤ Nat.card V)
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hsq : ∀ x ∈ V, x * x = 1) {w : G}
    (hw : w * w = 1) (hwV : ∀ x ∈ V, w * x * w⁻¹ ∈ V) :
    4 ≤ Nat.card ↥(V ⊓ Subgroup.centralizer ({w} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsqle := card_le_sq_centralizer hcomm hsq hw hwV
  have hA2 : IsPGroup 2 ↥(V ⊓ Subgroup.centralizer ({w} : Set G)) := hV2.to_le inf_le_left
  obtain ⟨n, hn⟩ := hA2.exists_card_eq
  by_contra hlt
  push Not at hlt
  have hn1 : n ≤ 1 := by
    by_contra hn2
    push Not at hn2
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
  have h4 : Nat.card ↥(V ⊓ Subgroup.centralizer ({w} : Set G)) ≤ 2 := by omega
  have h5 : Nat.card ↥(V ⊓ Subgroup.centralizer ({w} : Set G)) ^ 2 ≤ 2 ^ 2 :=
    Nat.pow_le_pow_left h4 2
  omega

end CFSG.CGT.PushingUpLit.LIT.Foote
