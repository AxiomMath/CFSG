module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpCoreA
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpCoreB

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped commutatorElement

section Q8Basic

variable {A : Type} [Group A] {p : ℕ} {W X : Subgroup A} {z : A}

private lemma q8_mem_Z_iff {u : A} :
    u ∈ W ⊓ centralizer (W : Set A) ↔ u ∈ W ∧ ∀ w ∈ W, w * u = u * w := by
  simp [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]

private lemma q8_X_conj_Z (hC : Core412 W X z) {x u : A} (hx : x ∈ X)
    (hu : u ∈ W ⊓ centralizer (W : Set A)) : x * u * x⁻¹ = u := by
  have h1 : u * x = x * u := mem_centralizer_iff.mp (hC.X_cent_Z hx) u hu
  calc x * u * x⁻¹ = (u * x) * x⁻¹ := by rw [h1]
    _ = u := by group

private lemma q8_exists_sq_pow (h : Setup412 p W X z) {x : A} (hx : x ∈ X) :
    ∃ m : ℕ, x = (x * x) ^ m := by
  obtain ⟨k, hk⟩ := h.Xp ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, hj⟩ := (h.prime.odd_of_ne_two h.odd).pow (n := k)
  refine ⟨j + 1, ?_⟩
  have e : p ^ k + 1 = 2 * (j + 1) := by omega
  calc x = x ^ (p ^ k) * x := by rw [hk', one_mul]
    _ = x ^ (p ^ k + 1) := (pow_succ x _).symm
    _ = x ^ (2 * (j + 1)) := by rw [e]
    _ = (x * x) ^ (j + 1) := by rw [pow_mul, sq]

private lemma q8_first (h : Setup412 p W X z) (hC : Core412 W X z) {s : A}
    (hsZ : s ∈ W ⊓ centralizer (W : Set A))
    (hZ : ∀ g ∈ W ⊓ centralizer (W : Set A), g = 1 ∨ g = s) {w : A} (hw : w ∈ W)
    (hx : ∀ x ∈ X, ⁅x, w⁆ = 1 ∨ ⁅x, w⁆ = s) : w = 1 ∨ w = s := by
  apply hZ
  rw [hC.Z_eq_fix]
  refine Subgroup.mem_inf.2 ⟨hw, ?_⟩
  rw [mem_centralizer_iff]
  intro x hxX
  have hss : s * s = 1 := hC.Z_exp2 s hsZ
  have hgZ : ⁅x, w⁆ ∈ W ⊓ centralizer (W : Set A) := by
    rcases hx x hxX with e | e
    · rw [e]; exact one_mem _
    · rw [e]; exact hsZ
  have hgg : ⁅x, w⁆ * ⁅x, w⁆ = 1 := by
    rcases hx x hxX with e | e <;> rw [e] <;> simp [hss]
  have h1 : ⁅x * x, w⁆ = 1 := by
    have e : ⁅x * x, w⁆ = (x * ⁅x, w⁆ * x⁻¹) * ⁅x, w⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, q8_X_conj_Z hC hxX hgZ, hgg]
  obtain ⟨m, hm⟩ := q8_exists_sq_pow h hxX
  have hcomm : Commute (x * x) w := commutatorElement_eq_one_iff_mul_comm.mp h1
  have h2 : Commute ((x * x) ^ m) w := hcomm.pow_left m
  rw [← hm] at h2
  exact h2

private lemma q8_card_Z {s : A} (hs : s ≠ 1) (hsZ : s ∈ W ⊓ centralizer (W : Set A))
    (hZ : ∀ g ∈ W ⊓ centralizer (W : Set A), g = 1 ∨ g = s) :
    Nat.card ↥(W ⊓ centralizer (W : Set A)) = 2 := by
  have hset : ((W ⊓ centralizer (W : Set A) : Subgroup A) : Set A) = {1, s} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact hZ g
    · rintro (rfl | rfl)
      · exact one_mem _
      · exact hsZ
  have e : Nat.card ↥(W ⊓ centralizer (W : Set A)) =
      (((W ⊓ centralizer (W : Set A) : Subgroup A) : Set A)).ncard := Nat.card_coe_set_eq _
  rw [e, hset]
  exact Set.ncard_pair (Ne.symm hs)

private lemma q8_z_cent (h : Setup412 p W X z) {s : A} (hs : s ≠ 1)
    (hsZ : s ∈ W ⊓ centralizer (W : Set A))
    (hZ : ∀ g ∈ W ⊓ centralizer (W : Set A), g = 1 ∨ g = s) : z * s = s * z := by
  have h1 : z * s * z⁻¹ ∈ W ⊓ centralizer (W : Set A) :=
    (mem_normalizer_iff.mp (CoreA.mem_normalizer_center h.zW) s).mp hsZ
  rcases hZ _ h1 with e | e
  · exfalso
    apply hs
    calc s = z⁻¹ * (z * s * z⁻¹) * z := by group
      _ = 1 := by rw [e]; group
  · calc z * s = (z * s * z⁻¹) * z := by group
      _ = s * z := by rw [e]

private lemma q8_card_W (h : Setup412 p W X z) (hC : Core412 W X z) {s : A} (hs : s ≠ 1)
    (hsZ : s ∈ W ⊓ centralizer (W : Set A))
    (hZ : ∀ g ∈ W ⊓ centralizer (W : Set A), g = 1 ∨ g = s) : Nat.card ↥W = 8 := by
  apply hC.card8
  have hle : W ⊓ centralizer (W : Set A) ≤ centralizer ({z} : Set A) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hZ g hg with rfl | rfl
    · simp
    · exact (q8_z_cent h hs hsZ hZ).symm
  rw [inf_eq_left.2 hle]
  exact q8_card_Z hs hsZ hZ

private def nci (W : Subgroup A) : Set A :=
  {w | w ∈ W ∧ w ∉ W ⊓ centralizer (W : Set A) ∧ w * w = 1}

private lemma nci_conj (h : Setup412 p W X z) (hC : Core412 W X z) {x w : A} (hx : x ∈ X)
    (hw : w ∈ nci W) : x * w * x⁻¹ ∈ nci W := by
  obtain ⟨hwW, hwZ, hw2⟩ := hw
  refine ⟨(mem_normalizer_iff.mp (h.XW hx) w).mp hwW, fun hc => hwZ ?_, ?_⟩
  · have e : x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ = x * w * x⁻¹ := q8_X_conj_Z hC (X.inv_mem hx) hc
    have e2 : x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ = w := by group
    rw [e2] at e
    rw [e]; exact hc
  · calc (x * w * x⁻¹) * (x * w * x⁻¹) = x * (w * w) * x⁻¹ := by group
      _ = 1 := by rw [hw2]; group

end Q8Basic

section Q8Count

variable {A : Type} [Group A] [Finite A] {p : ℕ} {W X : Subgroup A} {z : A}

private lemma nci_p_dvd (h : Setup412 p W X z) (hC : Core412 W X z) :
    p ∣ Nat.card ↥(nci W) := by
  classical
  let _ : MulAction ↥X ↥(nci W) :=
    { smul := fun x w => ⟨x * w * x⁻¹, nci_conj h hC x.2 w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ((1 : ↥X) : A) * (w : A) * ((1 : ↥X) : A)⁻¹ = w
        simp)
      mul_smul := fun x y w => Subtype.ext (by
        show ((x * y : ↥X) : A) * (w : A) * ((x * y : ↥X) : A)⁻¹ =
          (x : A) * ((y : A) * (w : A) * (y : A)⁻¹) * (x : A)⁻¹
        simp [mul_assoc]) }
  have : Fact p.Prime := ⟨h.prime⟩
  have hmod := h.Xp.card_modEq_card_fixedPoints ↥(nci W)
  have hempty : MulAction.fixedPoints ↥X ↥(nci W) = ∅ := by
    ext w
    simp only [MulAction.mem_fixedPoints, Set.mem_empty_iff_false, iff_false]
    intro hfix
    obtain ⟨hwW, hwZ, hw2⟩ := w.2
    apply hwZ
    rw [hC.Z_eq_fix]
    refine Subgroup.mem_inf.2 ⟨hwW, ?_⟩
    rw [mem_centralizer_iff]
    intro x hx
    have h' : x * (w : A) * x⁻¹ = w := congrArg Subtype.val (hfix ⟨x, hx⟩)
    calc x * (w : A) = (x * w * x⁻¹) * x := by group
      _ = w * x := by rw [h']
  rw [hempty] at hmod
  have h0 : Nat.card (↥(∅ : Set ↥(nci W))) = 0 := by simp
  rw [h0] at hmod
  exact (Nat.modEq_zero_iff_dvd).1 hmod

private lemma nci_two_dvd (hC : Core412 W X z) {s : A} (hs : s ≠ 1)
    (hsZ : s ∈ W ⊓ centralizer (W : Set A)) : 2 ∣ Nat.card ↥(nci W) := by
  classical
  have hss : s * s = 1 := hC.Z_exp2 s hsZ
  have hsc : ∀ a ∈ W, a * s = s * a := fun a ha => (q8_mem_Z_iff.mp hsZ).2 a ha
  have hρ : ∀ w ∈ nci W, w * s ∈ nci W := by
    rintro w ⟨hwW, hwZ, hw2⟩
    refine ⟨W.mul_mem hwW hsZ.1, fun hc => hwZ ?_, ?_⟩
    · have : (w * s) * s⁻¹ ∈ W ⊓ centralizer (W : Set A) :=
        (W ⊓ centralizer (W : Set A)).mul_mem hc
          ((W ⊓ centralizer (W : Set A)).inv_mem hsZ)
      simpa using this
    · calc (w * s) * (w * s) = w * (s * w) * s := by group
        _ = w * (w * s) * s := by rw [← hsc w hwW]
        _ = (w * w) * (s * s) := by group
        _ = 1 := by rw [hw2, hss]; group
  let σ : Function.End ↥(nci W) := fun w => ⟨w * s, hρ w w.2⟩
  have hσ : σ ^ 2 ^ 1 = 1 := by
    funext w
    apply Subtype.ext
    show (w : A) * s * s = w
    calc (w : A) * s * s = w * (s * s) := by group
      _ = w := by rw [hss]; group
  have : Fintype ↥(nci W) := Fintype.ofFinite _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥(nci W)) (f := σ) (p := 2) (n := 1) hσ
  have h0 : Fintype.card ↑(Function.fixedPoints σ) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨w, hw⟩ => ?_⟩
    have h1 : (w : A) * s = w := congrArg Subtype.val hw
    exact hs (by simpa using h1)
  rw [h0, ← Nat.card_eq_fintype_card] at hmod
  exact (Nat.modEq_zero_iff_dvd).1 hmod

private lemma q8_sq_of_not_mem (h : Setup412 p W X z) (hC : Core412 W X z) {s : A} (hs : s ≠ 1)
    (hsZ : s ∈ W ⊓ centralizer (W : Set A))
    (hZ : ∀ g ∈ W ⊓ centralizer (W : Set A), g = 1 ∨ g = s) {w : A} (hw : w ∈ W)
    (hwZ : w ∉ W ⊓ centralizer (W : Set A)) : w * w = s := by
  have hp2 := nci_two_dvd hC hs hsZ
  have hpp := nci_p_dvd h hC
  have h8 := q8_card_W h hC hs hsZ hZ
  have hZ2 := q8_card_Z hs hsZ hZ
  have hsub : nci W ⊆ (W : Set A) \ ((W ⊓ centralizer (W : Set A) : Subgroup A) : Set A) :=
    fun w hw => ⟨hw.1, hw.2.1⟩
  have hW8 : (W : Set A).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]; exact h8
  have hZ2' : ((W ⊓ centralizer (W : Set A) : Subgroup A) : Set A).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]; exact hZ2
  have hZW : ((W ⊓ centralizer (W : Set A) : Subgroup A) : Set A) ⊆ (W : Set A) :=
    fun g hg => hg.1
  have hcardD :
      ((W : Set A) \ ((W ⊓ centralizer (W : Set A) : Subgroup A) : Set A)).ncard = 6 := by
    rw [Set.ncard_sdiff hZW, hW8, hZ2']
  have hle : (nci W).ncard ≤ 6 := hcardD ▸ Set.ncard_le_ncard hsub (Set.toFinite _)
  have hcard : Nat.card ↥(nci W) = (nci W).ncard := Nat.card_coe_set_eq _
  rw [hcard] at hp2 hpp
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two h.prime).2 (Ne.symm h.odd)
  have hp3 : 3 ≤ p := by
    have := h.prime.two_le
    have := h.odd
    omega
  have h2p : 2 * p ∣ (nci W).ncard := hcop.mul_dvd_of_dvd_of_dvd hp2 hpp
  have hcases : (nci W).ncard = 0 ∨ (nci W).ncard = 6 := by
    rcases Nat.eq_zero_or_pos (nci W).ncard with h0 | hpos
    · exact Or.inl h0
    · have := Nat.le_of_dvd hpos h2p
      omega
  rcases hcases with h0 | h6
  · have hN : nci W = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).1 h0
    by_contra hne
    have h1 : w * w ≠ 1 := fun e => by
      have : w ∈ nci W := ⟨hw, hwZ, e⟩
      rw [hN] at this
      exact this
    rcases hZ _ (hC.sq_central w hw) with e | e
    · exact h1 e
    · exact hne e
  · exfalso
    have hEq : nci W = (W : Set A) \ ((W ⊓ centralizer (W : Set A) : Subgroup A) : Set A) :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hcardD, h6]) (Set.toFinite _)
    have hsq : ∀ a ∈ W, a * a = 1 := by
      intro a ha
      by_cases haZ : a ∈ W ⊓ centralizer (W : Set A)
      · exact hC.Z_exp2 a haZ
      · have : a ∈ nci W := by rw [hEq]; exact ⟨ha, haZ⟩
        exact this.2.2
    apply hC.nonab
    intro a ha b hb
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hsq (a * b) (W.mul_mem ha hb))
    calc a * b = (a * b)⁻¹ := hab.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hai, hbi]

end Q8Count

section Q8Y

variable {A : Type} [Group A] {p : ℕ} {W X : Subgroup A} {z : A}

private lemma q8_exists_y (h : Setup412 p W X z) (hC : Core412 W X z) {s : A}
    (hsZ : s ∈ W ⊓ centralizer (W : Set A))
    (hZ : ∀ g ∈ W ⊓ centralizer (W : Set A), g = 1 ∨ g = s)
    (hsq : ∀ w ∈ W, w ∉ W ⊓ centralizer (W : Set A) → w * w = s) :
    ∃ y ∈ W, y * y = s ∧ z * y * z⁻¹ = y⁻¹ := by
  have hss : s * s = 1 := hC.Z_exp2 s hsZ
  have hsc : ∀ a ∈ W, a * s = s * a := fun a ha => (q8_mem_Z_iff.mp hsZ).2 a ha
  have hzz : z⁻¹ * z⁻¹ = 1 := by rw [← mul_inv_rev, h.z2, inv_one]
  have hτ2 : ∀ a : A, z * (z * a * z⁻¹) * z⁻¹ = a := fun a => by
    calc z * (z * a * z⁻¹) * z⁻¹ = (z * z) * a * (z⁻¹ * z⁻¹) := by group
      _ = a := by rw [h.z2, hzz]; group
  have hτW : ∀ a ∈ W, z * a * z⁻¹ ∈ W := fun a ha => (mem_normalizer_iff.mp h.zW a).mp ha
  have hτZ : ∀ a ∈ W ⊓ centralizer (W : Set A), z * a * z⁻¹ ∈ W ⊓ centralizer (W : Set A) :=
    fun a ha => (mem_normalizer_iff.mp (CoreA.mem_normalizer_center h.zW) a).mp ha
  have hCz : ∀ c ∈ W, z * c * z⁻¹ = c → c ∈ W ⊓ centralizer (W : Set A) := by
    intro c hc hcz
    have hcomm : c * z = z * c := by
      calc c * z = (z * c * z⁻¹) * z := by rw [hcz]
        _ = z * c := by group
    rw [hC.Z_eq_fix]
    exact Subgroup.mem_inf.2 ⟨hc, CoreA.mem_centralizer_of_commute h hc hcomm⟩
  have hinv : ∀ a : A, a * a = s → a * s = a⁻¹ := by
    intro a ha
    have : a * (a * s) = 1 := by rw [← mul_assoc, ha, hss]
    exact eq_inv_of_mul_eq_one_right this
  obtain ⟨w, hw, hwZ⟩ : ∃ w ∈ W, w ∉ W ⊓ centralizer (W : Set A) := by
    by_contra hcon
    apply hC.nonab
    intro a ha b hb
    have haZ : a ∈ W ⊓ centralizer (W : Set A) := by
      by_contra hna
      exact hcon ⟨a, ha, hna⟩
    exact ((q8_mem_Z_iff.mp haZ).2 b hb).symm
  have hws : w * w = s := hsq w hw hwZ
  by_cases hcase : z * w * z⁻¹ = w * s
  · exact ⟨w, hw, hws, by rw [hcase]; exact hinv w hws⟩
  · have hu : z * w * z⁻¹ ∈ W := hτW w hw
    have hu1 : z * w * z⁻¹ ≠ w := fun e => hwZ (hCz w hw e)
    have hτu : z * (z * w * z⁻¹) * z⁻¹ = w := hτ2 w
    have hyW : w * (z * w * z⁻¹) ∈ W := W.mul_mem hw hu
    have hyZ : w * (z * w * z⁻¹) ∉ W ⊓ centralizer (W : Set A) := by
      intro hc
      rcases hZ _ hc with e | e
      · apply hcase
        have : z * w * z⁻¹ = w⁻¹ := eq_inv_of_mul_eq_one_right e
        rw [← hinv w hws] at this
        exact this
      · apply hu1
        calc z * w * z⁻¹ = w⁻¹ * (w * (z * w * z⁻¹)) := by group
          _ = (w * s) * s := by rw [e, ← hinv w hws]
          _ = w := by rw [mul_assoc, hss]; group
    have hy2 : (w * (z * w * z⁻¹)) * (w * (z * w * z⁻¹)) = s := hsq _ hyW hyZ
    have hcZ : ⁅z * w * z⁻¹, w⁆ ∈ W ⊓ centralizer (W : Set A) := by
      rw [hC.Z_eq_derived]; exact Subgroup.commutator_mem_commutator hu hw
    have hτy : z * (w * (z * w * z⁻¹)) * z⁻¹ = ⁅z * w * z⁻¹, w⁆ * (w * (z * w * z⁻¹)) := by
      have e1 : z * (w * (z * w * z⁻¹)) * z⁻¹ =
          (z * w * z⁻¹) * (z * (z * w * z⁻¹) * z⁻¹) := by group
      have e2 : (z * w * z⁻¹) * w = ⁅z * w * z⁻¹, w⁆ * (w * (z * w * z⁻¹)) := by
        simp only [commutatorElement_def]; group
      rw [e1, hτu]; exact e2
    refine ⟨w * (z * w * z⁻¹), hyW, hy2, ?_⟩
    rcases hZ _ hcZ with e | e
    · exfalso
      apply hyZ
      apply hCz _ hyW
      rw [hτy, e, one_mul]
    · rw [hτy, e, ← hinv _ hy2]
      exact (hsc _ hyW).symm

end Q8Y

section Q8Main

variable {A : Type} [Group A] [Finite A]

theorem core412_of_setup {p : ℕ} {W X : Subgroup A} {z : A} (h : Setup412 p W X z)
    (hW : ⁅W, X⁆ = W) (hne : W ≠ ⊥) : Core412 W X z := core412_of_part1 (part1_of_setup h hW hne)

theorem q8_data {p : ℕ} {W X : Subgroup A} {z : A} (h : Setup412 p W X z) (hW : ⁅W, X⁆ = W)
    (hne : W ≠ ⊥) {s : A} (hs : s ≠ 1) (hsZ : s ∈ W ⊓ centralizer (W : Set A))
    (hZ : ∀ g ∈ W ⊓ centralizer (W : Set A), g = 1 ∨ g = s) :
    (∀ w ∈ W, (∀ x ∈ X, ⁅x, w⁆ = 1 ∨ ⁅x, w⁆ = s) → w = 1 ∨ w = s) ∧
      ∃ y ∈ W, y * y = s ∧ z * y * z⁻¹ = y⁻¹ := by
  have hC := core412_of_setup h hW hne
  exact ⟨fun w hw hx => q8_first h hC hsZ hZ hw hx,
    q8_exists_y h hC hsZ hZ (fun w hw hwZ => q8_sq_of_not_mem h hC hs hsZ hZ hw hwZ)⟩

end Q8Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
