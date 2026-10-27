module

public import CFSG.GH74.Uniqueness.SU.SU13TA1Invol
public import CFSG.LocalAnalysis.LargeEvenClassification.CommutingElementaryProduct

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L97

open Subgroup Equiv Equiv.Perm CFSG CFSG.GH74.GLS CFSG.GH74.Uniqueness.SU.SU13.TA

def a8 : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

def b8 : Perm (Fin 8) := swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7

theorem a8_sq : a8 * a8 = 1 := by decide

theorem b8_sq : b8 * b8 = 1 := by decide

theorem a8_b8 : a8 * b8 = b8 * a8 := by decide

theorem a8_ne : a8 ≠ 1 := by decide

theorem b8_ne : b8 ≠ 1 := by decide

theorem ab8_ne : a8 * b8 ≠ 1 := by decide

theorem a8_supp : a8.support.card = 8 := by decide

theorem b8_supp : b8.support.card = 8 := by decide

theorem ab8_supp : (a8 * b8).support.card = 8 := by decide

theorem cycleType_of_sq {σ : Perm (Fin 8)} (h2 : σ * σ = 1) (h1 : σ ≠ 1)
    (hs : σ.support.card = 8) : σ.cycleType = {2, 2, 2, 2} := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hm, hord, hs] at hsum
  simp only [Multiset.sum_replicate, smul_eq_mul] at hsum
  have hm3 : m = 3 := by omega
  rw [hm, hord, hm3]
  rfl

theorem a8_ct : a8.cycleType = {2, 2, 2, 2} := cycleType_of_sq a8_sq a8_ne a8_supp

theorem b8_ct : b8.cycleType = {2, 2, 2, 2} := cycleType_of_sq b8_sq b8_ne b8_supp

theorem ab8_ct : (a8 * b8).cycleType = {2, 2, 2, 2} :=
  cycleType_of_sq (by decide) ab8_ne ab8_supp

def emb8 {n : ℕ} (hn : 8 ≤ n) : Fin 8 ≃ {x : Fin n // x.val < 8} where
  toFun i := ⟨⟨i.val, lt_of_lt_of_le i.isLt hn⟩, i.isLt⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def ι8 {n : ℕ} (hn : 8 ≤ n) : Perm (Fin 8) →* Perm (Fin n) :=
  Equiv.Perm.extendDomainHom (emb8 hn)

theorem cycleType_ι8 {n : ℕ} (hn : 8 ≤ n) (σ : Perm (Fin 8)) :
    (ι8 hn σ).cycleType = σ.cycleType :=
  Equiv.Perm.cycleType_extendDomain (emb8 hn)

theorem exists_klein_2222 {n : ℕ} (hn : 8 ≤ n) :
    ∃ a b : Perm (Fin n), a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧
      a.cycleType = {2, 2, 2, 2} ∧ b.cycleType = {2, 2, 2, 2} ∧
      (a * b).cycleType = {2, 2, 2, 2} := by
  refine ⟨ι8 hn a8, ι8 hn b8, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, a8_sq, map_one]
  · rw [← map_mul, b8_sq, map_one]
  · rw [← map_mul, ← map_mul, a8_b8]
  · rw [cycleType_ι8, a8_ct]
  · rw [cycleType_ι8, b8_ct]
  · rw [← map_mul, cycleType_ι8, ab8_ct]

section Klein

variable {G : Type*} [Group G]

def klein (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) : Subgroup G where
  carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    have hba : b * a = a * b := hab.symm
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
    · left; exact one_mul 1
    · right; left; exact one_mul _
    · right; right; left; exact one_mul _
    · right; right; right; exact one_mul _
    · right; left; exact mul_one _
    · left; exact ha
    · right; right; right; rfl
    · right; right; left; rw [← mul_assoc, ha, one_mul]
    · right; right; left; exact mul_one _
    · right; right; right; exact hba
    · left; exact hb
    · right; left; rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
    · right; right; right; exact mul_one _
    · right; right; left; rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
    · right; left; rw [mul_assoc, hb, mul_one]
    · left
      calc a * b * (a * b) = a * (b * a) * b := by simp [mul_assoc]
        _ = a * (a * b) * b := by rw [hba]
        _ = a * a * (b * b) := by simp [mul_assoc]
        _ = 1 := by rw [ha, hb, one_mul]
  inv_mem' := by
    intro x hx
    have hba : b * a = a * b := hab.symm
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl
    · left; exact inv_one
    · right; left; exact hai
    · right; right; left; exact hbi
    · right; right; right; rw [mul_inv_rev, hai, hbi, hba]

theorem mem_klein {a b : G} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a} {x : G} :
    x ∈ klein a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

theorem card_klein {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : Nat.card (klein a b ha hb hab) = 4 := by
  have hset : ((klein a b ha hb hab : Subgroup G) : Set G) = {1, a, b, a * b} := by
    ext x
    simp only [SetLike.mem_coe, mem_klein, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hne
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, hai]
  have h1 : a * b ≠ a := by
    intro h; apply hb1; exact mul_eq_left.mp h
  have h2 : a * b ≠ b := by
    intro h; apply ha1; exact mul_eq_right.mp h
  change Nat.card ((klein a b ha hb hab : Subgroup G) : Set G) = 4
  rw [hset, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_pair h2.symm]
  · simp [hb1, hne]
  · simp [ha1.symm, hb1.symm, hab1.symm]

theorem klein_sq {a b : G} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a}
    (hab2 : a * b * (a * b) = 1) {x : G} (hx : x ∈ klein a b ha hb hab) : x * x = 1 := by
  rcases mem_klein.mp hx with rfl | rfl | rfl | rfl
  · exact one_mul _
  · exact ha
  · exact hb
  · exact hab2

end Klein

theorem isElemAbelian_of_sq {G : Type*} [Group G] (E : Subgroup G) (h : ∀ x ∈ E, x * x = 1) :
    CFSG.Open.IsElemAbelian 2 E := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    have hxy : (x * y : E) * (x * y) = 1 := Subtype.ext (h _ (x * y).2)
    have h1 := inv_eq_of_mul_eq_one_right hxy
    have hx' : (x : E)⁻¹ = x := inv_eq_of_mul_eq_one_right (Subtype.ext (h _ x.2))
    have hy' : (y : E)⁻¹ = y := inv_eq_of_mul_eq_one_right (Subtype.ext (h _ y.2))
    have : x * y = y * x := by
      calc x * y = (x * y)⁻¹ := h1.symm
        _ = y * x := by rw [mul_inv_rev, hx', hy']
    exact congrArg Subtype.val this
  · rw [sq]; exact h x hx

theorem mem_alt_of_ct {n : ℕ} {σ : Perm (Fin n)} (hσ : σ.cycleType = {2, 2, 2, 2}) :
    σ ∈ alternatingGroup (Fin n) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_of_cycleType, hσ]
  decide

theorem exists_twoCover {Lh : Type} [Group Lh] {n : ℕ} (hL : IsDoubleCoverOfAlt Lh n) :
    ∃ π : Lh →* alternatingGroup (Fin n), TwoCover π ∧ π.ker = center Lh := by
  obtain ⟨hKq, hZ, ⟨e⟩⟩ := hL
  let π : Lh →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (center Lh))
  have hker : π.ker = center Lh := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : e ((QuotientGroup.mk' (center Lh)) x) = 1 := hx
      exact (QuotientGroup.eq_one_iff x).mp ((map_eq_one_iff e e.injective).mp h1)
    · intro hx
      have h1 : (QuotientGroup.mk' (center Lh)) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      show e ((QuotientGroup.mk' (center Lh)) x) = 1
      rw [h1, map_one]
  exact ⟨π, ⟨e.surjective.comp (QuotientGroup.mk'_surjective _), hker.le,
    by rw [hker]; exact hZ, hKq.1⟩, hker⟩

theorem exists_E_F {Lh : Type} [Group Lh] [Finite Lh] {n : ℕ} (hn : 8 ≤ n)
    (hL : IsDoubleCoverOfAlt Lh n) :
    ∃ E F : Subgroup Lh, F ≤ E ∧ center Lh ≤ E ∧ CFSG.Open.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ 3 ∧ CFSG.Open.IsElemAbelian 2 F ∧ Nat.card F = 2 ^ 2 ∧
      F ⊓ center Lh = ⊥ := by
  obtain ⟨π, hπ, hker⟩ := exists_twoCover hL
  obtain ⟨a, b, ha2, hb2, hab, hact, hbct, habct⟩ := exists_klein_2222 hn
  let aA : alternatingGroup (Fin n) := ⟨a, mem_alt_of_ct hact⟩
  let bA : alternatingGroup (Fin n) := ⟨b, mem_alt_of_ct hbct⟩
  obtain ⟨ah, hah⟩ := hπ.surj aA
  obtain ⟨bh, hbh⟩ := hπ.surj bA
  have hah2 : ah * ah = 1 := by
    have := hπ.sq_eq_one_of_cycleType_two_two_two_two hn (x := ah) (by rw [hah]; exact hact)
    rwa [sq] at this
  have hbh2 : bh * bh = 1 := by
    have := hπ.sq_eq_one_of_cycleType_two_two_two_two hn (x := bh) (by rw [hbh]; exact hbct)
    rwa [sq] at this
  have habh2 : ah * bh * (ah * bh) = 1 := by
    have := hπ.sq_eq_one_of_cycleType_two_two_two_two hn (x := ah * bh)
      (by rw [map_mul, hah, hbh]; exact habct)
    rwa [sq] at this
  have hcomm : ah * bh = bh * ah := by
    have h1 : ah * bh = (ah * bh)⁻¹ := (inv_eq_of_mul_eq_one_right habh2).symm
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hah2, inv_eq_of_mul_eq_one_right hbh2] at h1
    exact h1
  have ha1 : a ≠ 1 := by
    intro h; rw [h, Perm.cycleType_one] at hact; exact absurd hact (by decide)
  have hb1 : b ≠ 1 := by
    intro h; rw [h, Perm.cycleType_one] at hbct; exact absurd hbct (by decide)
  have hab1 : a * b ≠ 1 := by
    intro h; rw [h, Perm.cycleType_one] at habct; exact absurd habct (by decide)
  have hah1 : ah ≠ 1 := by
    intro h; apply ha1
    have := congrArg (fun x : Lh => ((π x : alternatingGroup (Fin n)) : Perm (Fin n))) h
    simpa [hah, aA] using this
  have hbh1 : bh ≠ 1 := by
    intro h; apply hb1
    have := congrArg (fun x : Lh => ((π x : alternatingGroup (Fin n)) : Perm (Fin n))) h
    simpa [hbh, bA] using this
  have hne : ah ≠ bh := by
    intro h
    apply hab1
    have := congrArg (fun x : Lh => ((π x : alternatingGroup (Fin n)) : Perm (Fin n))) h
    simp only [hah, hbh, aA, bA] at this
    rw [← this]
    exact ha2
  let F : Subgroup Lh := klein ah bh hah2 hbh2 hcomm
  have hFcard : Nat.card F = 2 ^ 2 := by
    have := card_klein hah2 hbh2 hcomm hah1 hbh1 hne
    rw [this]; norm_num
  have hFelem : CFSG.Open.IsElemAbelian 2 F :=
    isElemAbelian_of_sq F (fun x hx => klein_sq habh2 hx)
  have hFZ : F ⊓ center Lh = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxF, hxZ⟩
    have hx1 : π x = 1 := by
      have : x ∈ π.ker := by rw [hker]; exact hxZ
      exact this
    rw [Subgroup.mem_bot]
    rcases mem_klein.mp hxF with rfl | rfl | rfl | rfl
    · rfl
    · exfalso; apply ha1
      have := congrArg (fun y : alternatingGroup (Fin n) => (y : Perm (Fin n))) hx1
      simpa [hah, aA] using this
    · exfalso; apply hb1
      have := congrArg (fun y : alternatingGroup (Fin n) => (y : Perm (Fin n))) hx1
      simpa [hbh, bA] using this
    · exfalso; apply hab1
      have := congrArg (fun y : alternatingGroup (Fin n) => (y : Perm (Fin n))) hx1
      rw [map_mul, hah, hbh] at this
      simpa [aA, bA] using this
  have hZcard : Nat.card (center Lh) = 2 ^ 1 := by
    have := hL.2.1
    rw [this]; norm_num
  have hZelem : CFSG.Open.IsElemAbelian 2 (center Lh) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    have h1 : (⟨x, hx⟩ : center Lh) ^ Nat.card (center Lh) = 1 := pow_card_eq_one'
    rw [hZcard, pow_one] at h1
    have := congrArg Subtype.val h1
    simpa using this
  obtain ⟨E, hFE, hZE, hE, hEcard, -⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
      (prime := 2) (firstRank := 2) (secondRank := 1) F (center Lh) hFelem hZelem hFcard hZcard
      (fun x _ => Subgroup.mem_centralizer_iff.mpr fun c hc =>
        (Subgroup.mem_center_iff.mp hc x).symm)
      (disjoint_iff.mpr hFZ)
  exact ⟨E, F, hFE, hZE, hE, by rw [hEcard], hFelem, hFcard, hFZ⟩

end CFSG.GH74.GLS.Stage1.Thm4.L97
