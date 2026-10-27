module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open Subgroup

variable {Q : Type*} [Group Q]

@[expose] def GomiElemAb (W : Subgroup Q) : Prop :=
  (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧ ∀ x ∈ W, x * x = 1

@[expose] def gomiExt (M : Subgroup Q) (y : Q) (hc : ∀ m ∈ M, y * m = m * y) (h2 : y * y = 1) :
    Subgroup Q where
  carrier := {x | x ∈ M ∨ ∃ m ∈ M, x = y * m}
  one_mem' := Or.inl M.one_mem
  mul_mem' := by
    rintro a b (ha | ⟨m, hm, rfl⟩) (hb | ⟨m', hm', rfl⟩)
    · exact Or.inl (M.mul_mem ha hb)
    · refine Or.inr ⟨a * m', M.mul_mem ha hm', ?_⟩
      calc a * (y * m') = (a * y) * m' := by rw [mul_assoc]
        _ = (y * a) * m' := by rw [← hc a ha]
        _ = y * (a * m') := by rw [mul_assoc]
    · refine Or.inr ⟨m * b, M.mul_mem hm hb, ?_⟩
      rw [mul_assoc]
    · refine Or.inl ?_
      have : y * m * (y * m') = m * m' := by
        calc y * m * (y * m') = y * (m * y) * m' := by group
          _ = y * (y * m) * m' := by rw [← hc m hm]
          _ = (y * y) * (m * m') := by group
          _ = m * m' := by rw [h2, one_mul]
      rw [this]
      exact M.mul_mem hm hm'
  inv_mem' := by
    rintro a (ha | ⟨m, hm, rfl⟩)
    · exact Or.inl (M.inv_mem ha)
    · refine Or.inr ⟨m⁻¹, M.inv_mem hm, ?_⟩
      have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right h2
      rw [mul_inv_rev, hy]
      have := hc m⁻¹ (M.inv_mem hm)
      exact this.symm

theorem gomiExt_le (M : Subgroup Q) (y : Q) (hc : ∀ m ∈ M, y * m = m * y) (h2 : y * y = 1) :
    M ≤ gomiExt M y hc h2 := fun _ hm => Or.inl hm

theorem gomiExt_mem (M : Subgroup Q) (y : Q) (hc : ∀ m ∈ M, y * m = m * y) (h2 : y * y = 1) :
    y ∈ gomiExt M y hc h2 := Or.inr ⟨1, M.one_mem, (mul_one y).symm⟩

theorem gomiExt_elemAb (M : Subgroup Q) (y : Q) (hc : ∀ m ∈ M, y * m = m * y) (h2 : y * y = 1)
    (hM : GomiElemAb M) : GomiElemAb (gomiExt M y hc h2) := by
  obtain ⟨hcomm, hsq⟩ := hM
  have hmm : ∀ m ∈ M, ∀ m' ∈ M, y * m * (y * m') = m * m' := by
    intro m hm m' hm'
    calc y * m * (y * m') = y * (m * y) * m' := by group
      _ = y * (y * m) * m' := by rw [← hc m hm]
      _ = (y * y) * (m * m') := by group
      _ = m * m' := by rw [h2, one_mul]
  refine ⟨?_, ?_⟩
  · rintro a (ha | ⟨m, hm, rfl⟩) b (hb | ⟨m', hm', rfl⟩)
    · exact hcomm a ha b hb
    · calc a * (y * m') = (a * y) * m' := by rw [mul_assoc]
        _ = (y * a) * m' := by rw [← hc a ha]
        _ = y * (a * m') := by rw [mul_assoc]
        _ = y * (m' * a) := by rw [hcomm a ha m' hm']
        _ = (y * m') * a := by rw [mul_assoc]
    · calc y * m * b = y * (m * b) := by rw [mul_assoc]
        _ = y * (b * m) := by rw [hcomm m hm b hb]
        _ = (y * b) * m := by rw [mul_assoc]
        _ = (b * y) * m := by rw [hc b hb]
        _ = b * (y * m) := by rw [mul_assoc]
    · rw [hmm m hm m' hm', hmm m' hm' m hm, hcomm m hm m' hm']
  · rintro a (ha | ⟨m, hm, rfl⟩)
    · exact hsq a ha
    · rw [hmm m hm m hm]
      exact hsq m hm

theorem gomiOdd_card_le_two_mul [Finite Q] (S D : Subgroup Q) (y : Q)
    (h : ∀ x ∈ S, x ∈ D ∨ y⁻¹ * x ∈ D) : Nat.card S ≤ 2 * Nat.card D := by
  have hsub : (S : Set Q) ⊆ (D : Set Q) ∪ (fun d => y * d) '' (D : Set Q) := by
    intro x hx
    rcases h x hx with hd | hd
    · exact Or.inl hd
    · exact Or.inr ⟨y⁻¹ * x, hd, by simp⟩
  have h1 : Nat.card S = (S : Set Q).ncard := Nat.card_coe_set_eq _
  have h2 : Nat.card D = (D : Set Q).ncard := Nat.card_coe_set_eq _
  have h3 : ((S : Set Q)).ncard ≤ ((D : Set Q) ∪ (fun d => y * d) '' (D : Set Q)).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h4 := Set.ncard_union_le (D : Set Q) ((fun d => y * d) '' (D : Set Q))
  have h5 : ((fun d => y * d) '' (D : Set Q)).ncard ≤ (D : Set Q).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  omega

structure GomiQuad (Q : Type*) [Group Q] (z : Q) : Prop where
  central : ∀ x : Q, x * z = z * x
  sq_z : z * z = 1
  sq : ∀ x : Q, x * x = 1 ∨ x * x = z

theorem GomiQuad.comm_or {z : Q} (h : GomiQuad Q z) (x y : Q) :
    x * y = y * x ∨ x * y = z * (y * x) := by
  have hcen : ∀ c : Q, (c = 1 ∨ c = z) → ∀ g : Q, c * g = g * c := by
    rintro c (rfl | rfl) g
    · simp
    · exact (h.central g).symm
  have hself : ∀ c : Q, (c = 1 ∨ c = z) → c * c = 1 := by
    rintro c (rfl | rfl)
    · simp
    · exact h.sq_z
  have hmul : ∀ c d : Q, (c = 1 ∨ c = z) → (d = 1 ∨ d = z) → (c * d = 1 ∨ c * d = z) := by
    rintro c d (rfl | rfl) (rfl | rfl)
    · left; simp
    · right; simp
    · right; simp
    · left; exact h.sq_z
  have hinv : ∀ w c : Q, (c = 1 ∨ c = z) → w * w = c → w⁻¹ = w * c := by
    intro w c hc hw
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hw]
    exact hself c hc
  have ha := h.sq x
  have hb := h.sq y
  have ht := h.sq (x * y)
  have hu : x * y * x⁻¹ * y⁻¹ = (x * y * (x * y)) * (x * x) * (y * y) := by
    rw [hinv x (x * x) ha rfl, hinv y (y * y) hb rfl]
    calc x * y * (x * (x * x)) * (y * (y * y)) = x * y * x * ((x * x) * y) * (y * y) := by group
      _ = x * y * x * (y * (x * x)) * (y * y) := by rw [hcen (x * x) ha y]
      _ = (x * y * (x * y)) * (x * x) * (y * y) := by group
  have hxy : x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
  rcases hmul _ _ (hmul _ _ ht ha) hb with h1 | h1
  · left
    rw [hu, h1, one_mul] at hxy
    exact hxy
  · right
    rw [hu, h1] at hxy
    exact hxy

theorem GomiQuad.commute_inv_mul {z : Q} (h : GomiQuad Q z) {x y₁ y : Q}
    (hy₁ : x * y₁ = z * (y₁ * x)) (hy : x * y = z * (y * x)) :
    x * (y₁⁻¹ * y) = (y₁⁻¹ * y) * x := by
  have e1 : y₁⁻¹ * x = z * (x * y₁⁻¹) := by
    calc y₁⁻¹ * x = y₁⁻¹ * (x * y₁) * y₁⁻¹ := by group
      _ = y₁⁻¹ * (z * (y₁ * x)) * y₁⁻¹ := by rw [hy₁]
      _ = (y₁⁻¹ * z) * (y₁ * x) * y₁⁻¹ := by group
      _ = (z * y₁⁻¹) * (y₁ * x) * y₁⁻¹ := by rw [h.central y₁⁻¹]
      _ = z * (x * y₁⁻¹) := by group
  have e2 : y * x = z * (x * y) := by
    calc y * x = (z * z) * (y * x) := by rw [h.sq_z, one_mul]
      _ = z * (z * (y * x)) := by rw [mul_assoc]
      _ = z * (x * y) := by rw [← hy]
  calc x * (y₁⁻¹ * y) = (z * z) * (x * y₁⁻¹ * y) := by rw [h.sq_z, one_mul]; group
    _ = z * ((z * (x * y₁⁻¹)) * y) := by group
    _ = z * ((y₁⁻¹ * x) * y) := by rw [← e1]
    _ = (z * y₁⁻¹) * (x * y) := by group
    _ = (y₁⁻¹ * z) * (x * y) := by rw [h.central y₁⁻¹]
    _ = y₁⁻¹ * (z * (x * y)) := by group
    _ = y₁⁻¹ * (y * x) := by rw [← e2]
    _ = (y₁⁻¹ * y) * x := by group

variable [Finite Q]

theorem GomiQuad.exists_involution {z : Q} (h : GomiQuad Q z) (hz1 : z ≠ 1)
    (M : Subgroup Q) (hzM : z ∈ M)
    (hcard : 4 * Nat.card M < Nat.card (Subgroup.centralizer (M : Set Q))) :
    ∃ y ∈ Subgroup.centralizer (M : Set Q), y ∉ M ∧ y * y = 1 := by
  by_contra hcon
  push Not at hcon
  set C := Subgroup.centralizer (M : Set Q) with hC
  have hsqz : ∀ y ∈ C, y ∉ M → y * y = z := fun y hy hyM =>
    (h.sq y).resolve_left (hcon y hy hyM)
  have claim1 : ∀ x ∈ C, x ∉ M → ∀ y ∈ C, y ∉ M → x * y = y * x → ∃ m ∈ M, y = x * m := by
    intro x hx hxM y hy hyM hxy
    by_contra hno
    push Not at hno
    have hxyC : x * y ∈ C := C.mul_mem hx hy
    have hxyM : x * y ∉ M := by
      intro hm
      apply hno (z * (x * y)) (M.mul_mem hzM hm)
      calc y = z * z * y := by rw [h.sq_z, one_mul]
        _ = z * (z * y) := by rw [mul_assoc]
        _ = z * ((x * x) * y) := by rw [hsqz x hx hxM]
        _ = x * (z * (x * y)) := by
          calc z * ((x * x) * y) = z * x * (x * y) := by group
            _ = x * z * (x * y) := by rw [h.central x]
            _ = x * (z * (x * y)) := by group
    have h1 := hsqz _ hxyC hxyM
    have h2 : x * y * (x * y) = (x * x) * (y * y) := by
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = (x * x) * (y * y) := by group
    rw [h2, hsqz x hx hxM, hsqz y hy hyM, h.sq_z] at h1
    exact hz1 h1.symm
  obtain ⟨x₀, hx₀C, hx₀M⟩ : ∃ x ∈ C, x ∉ M := by
    by_contra hne
    push Not at hne
    have hle : C ≤ M := fun x hx => hne x hx
    have := Subgroup.card_le_of_le hle
    omega
  set D : Subgroup Q := C ⊓ Subgroup.centralizer ({x₀} : Set Q) with hD
  have hDmem : ∀ y, y ∈ D ↔ y ∈ C ∧ x₀ * y = y * x₀ := by
    intro y
    rw [hD, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
  have hDcard : Nat.card D ≤ 2 * Nat.card M := by
    refine gomiOdd_card_le_two_mul D M x₀ ?_
    intro y hy
    by_cases hyM : y ∈ M
    · exact Or.inl hyM
    · right
      obtain ⟨hyC, hcomm⟩ := (hDmem y).mp hy
      obtain ⟨m, hm, hym⟩ := claim1 x₀ hx₀C hx₀M y hyC hyM hcomm
      rw [hym, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hm
  have hCcard : Nat.card C ≤ 2 * Nat.card D := by
    by_cases hCD : C ≤ D
    · refine gomiOdd_card_le_two_mul C D 1 ?_
      intro y hy
      exact Or.inl (hCD hy)
    · obtain ⟨y₁, hy₁C, hy₁D⟩ := SetLike.not_le_iff_exists.mp hCD
      have hy₁comm : x₀ * y₁ = z * (y₁ * x₀) := by
        rcases h.comm_or x₀ y₁ with h1 | h1
        · exact absurd ((hDmem y₁).mpr ⟨hy₁C, h1⟩) hy₁D
        · exact h1
      refine gomiOdd_card_le_two_mul C D y₁ ?_
      intro y hy
      by_cases hyD : y ∈ D
      · exact Or.inl hyD
      · right
        have hycomm : x₀ * y = z * (y * x₀) := by
          rcases h.comm_or x₀ y with h1 | h1
          · exact absurd ((hDmem y).mpr ⟨hy, h1⟩) hyD
          · exact h1
        refine (hDmem _).mpr ⟨C.mul_mem (C.inv_mem hy₁C) hy, ?_⟩
        exact h.commute_inv_mul hy₁comm hycomm
  omega

theorem gomiExt_card_ge (M : Subgroup Q) (y : Q) (hc : ∀ m ∈ M, y * m = m * y) (h2 : y * y = 1)
    (hy : y ∉ M) : 2 * Nat.card M ≤ Nat.card (gomiExt M y hc h2) := by
  have hle := gomiExt_le M y hc h2
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have hEpos : 0 < Nat.card (gomiExt M y hc h2) := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    have heq : M = gomiExt M y hc h2 := Subgroup.eq_of_le_of_card_ge hle hk.le
    exact hy (heq ▸ gomiExt_mem M y hc h2)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hk2 : 2 ≤ k := by omega
  rw [hk]
  calc 2 * Nat.card M ≤ k * Nat.card M := Nat.mul_le_mul_right _ hk2
    _ = Nat.card M * k := Nat.mul_comm _ _

theorem GomiQuad.card_le_thirty_two {z : Q} (h : GomiQuad Q z)
    (hE : ∀ W : Subgroup Q, GomiElemAb W → Nat.card W ≤ 4) : Nat.card Q ≤ 32 := by
  by_cases hz1 : z = 1
  · subst hz1
    have hsq1 : ∀ x : Q, x * x = 1 := fun x => (h.sq x).elim id id
    have hcomm : ∀ x y : Q, x * y = y * x := by
      intro x y
      calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq1 (x * y))).symm
        _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
        _ = y * x := by
          rw [inv_eq_of_mul_eq_one_right (hsq1 x), inv_eq_of_mul_eq_one_right (hsq1 y)]
    have := hE ⊤ ⟨fun x _ y _ => hcomm x y, fun x _ => hsq1 x⟩
    rw [Subgroup.card_top] at this
    omega
  · by_contra hbig
    push Not at hbig
    have hc0 : ∀ m ∈ (⊥ : Subgroup Q), z * m = m * z := by
      intro m hm
      rw [Subgroup.mem_bot.mp hm]
      simp
    have hb0 : GomiElemAb (⊥ : Subgroup Q) :=
      ⟨fun x hx y hy => by rw [Subgroup.mem_bot.mp hx, Subgroup.mem_bot.mp hy],
        fun x hx => by rw [Subgroup.mem_bot.mp hx]; simp⟩
    set M₀ := gomiExt ⊥ z hc0 h.sq_z with hM₀
    have hM₀e : GomiElemAb M₀ := gomiExt_elemAb ⊥ z hc0 h.sq_z hb0
    have hzM₀ : z ∈ M₀ := gomiExt_mem ⊥ z hc0 h.sq_z
    have hM₀card : 2 ≤ Nat.card M₀ := by
      have := gomiExt_card_ge ⊥ z hc0 h.sq_z (by simpa [Subgroup.mem_bot] using hz1)
      simpa using this
    have hM₀central : ∀ m ∈ M₀, ∀ g : Q, m * g = g * m := by
      rintro m (hm | ⟨m', hm', rfl⟩) g
      · rw [Subgroup.mem_bot.mp hm]
        simp
      · rw [Subgroup.mem_bot.mp hm', mul_one]
        exact (h.central g).symm
    have hC₀ : Subgroup.centralizer (M₀ : Set Q) = ⊤ := by
      refine eq_top_iff.mpr (fun g _ => ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact hM₀central m hm g
    obtain ⟨x₁, -, hx₁M, hx₁sq⟩ := h.exists_involution hz1 M₀ hzM₀ (by
      rw [hC₀, Subgroup.card_top]
      have := hE M₀ hM₀e
      omega)
    have hx₁c : ∀ m ∈ M₀, x₁ * m = m * x₁ := fun m hm => (hM₀central m hm x₁).symm
    set M₁ := gomiExt M₀ x₁ hx₁c hx₁sq with hM₁
    have hM₁e : GomiElemAb M₁ := gomiExt_elemAb M₀ x₁ hx₁c hx₁sq hM₀e
    have hzM₁ : z ∈ M₁ := gomiExt_le M₀ x₁ hx₁c hx₁sq hzM₀
    have hM₁card : 2 * Nat.card M₀ ≤ Nat.card M₁ := gomiExt_card_ge M₀ x₁ hx₁c hx₁sq hx₁M
    have hD₁C₁ : Subgroup.centralizer ({x₁} : Set Q) ≤ Subgroup.centralizer (M₁ : Set Q) := by
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      rw [Subgroup.mem_centralizer_iff]
      rintro m (hm | ⟨m', hm', rfl⟩)
      · exact hM₀central m hm g
      · calc x₁ * m' * g = x₁ * (m' * g) := by rw [mul_assoc]
          _ = x₁ * (g * m') := by rw [hM₀central m' hm' g]
          _ = (x₁ * g) * m' := by rw [mul_assoc]
          _ = (g * x₁) * m' := by rw [← hg]
          _ = g * (x₁ * m') := by rw [mul_assoc]
    have hQD : Nat.card Q ≤ 2 * Nat.card (Subgroup.centralizer ({x₁} : Set Q)) := by
      have key : ∃ y₁ : Q, ∀ g : Q, g ∈ Subgroup.centralizer ({x₁} : Set Q) ∨
          y₁⁻¹ * g ∈ Subgroup.centralizer ({x₁} : Set Q) := by
        by_cases hall : ∀ g : Q, g ∈ Subgroup.centralizer ({x₁} : Set Q)
        · exact ⟨1, fun g => Or.inl (hall g)⟩
        · push Not at hall
          obtain ⟨y₁, hy₁⟩ := hall
          refine ⟨y₁, fun g => ?_⟩
          by_cases hg : g ∈ Subgroup.centralizer ({x₁} : Set Q)
          · exact Or.inl hg
          · right
            have hy₁c : x₁ * y₁ = z * (y₁ * x₁) := by
              rcases h.comm_or x₁ y₁ with h1 | h1
              · exact absurd (Subgroup.mem_centralizer_singleton_iff.mpr h1.symm) hy₁
              · exact h1
            have hgc : x₁ * g = z * (g * x₁) := by
              rcases h.comm_or x₁ g with h1 | h1
              · exact absurd (Subgroup.mem_centralizer_singleton_iff.mpr h1.symm) hg
              · exact h1
            exact Subgroup.mem_centralizer_singleton_iff.mpr (h.commute_inv_mul hy₁c hgc).symm
      obtain ⟨y₁, hy₁⟩ := key
      have := gomiOdd_card_le_two_mul (⊤ : Subgroup Q) _ y₁ (fun g _ => hy₁ g)
      rwa [Subgroup.card_top] at this
    have hC₁card := Subgroup.card_le_of_le hD₁C₁
    have hM₁le := hE M₁ hM₁e
    obtain ⟨x₂, hx₂C, hx₂M, hx₂sq⟩ := h.exists_involution hz1 M₁ hzM₁ (by omega)
    have hx₂c : ∀ m ∈ M₁, x₂ * m = m * x₂ := fun m hm =>
      (Subgroup.mem_centralizer_iff.mp hx₂C m hm).symm
    have hM₂e : GomiElemAb (gomiExt M₁ x₂ hx₂c hx₂sq) :=
      gomiExt_elemAb M₁ x₂ hx₂c hx₂sq hM₁e
    have hM₂card := gomiExt_card_ge M₁ x₂ hx₂c hx₂sq hx₂M
    have := hE _ hM₂e
    omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
