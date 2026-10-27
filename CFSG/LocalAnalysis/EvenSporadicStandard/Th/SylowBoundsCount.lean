module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5AaFacts

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L S A B Aa : Subgroup G} {z b : G}

omit [Finite G] in
theorem ThLocalIn.conj_mem_A_of_mem_S (W : ThLocalIn L S A B z) {s : G} (hs : s ∈ S) {x : G}
    (hx : x ∈ A) : s * x * s⁻¹ ∈ A := by
  rw [W.mem_A_iff] at hx ⊢
  obtain ⟨hxS, hx4⟩ := hx
  refine ⟨S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs), fun s₁ hs₁ s₂ hs₂ s₃ hs₃ s₄ hs₄ => ?_⟩
  have key : ∀ (u v : G), ⁅s * u * s⁻¹, s * v * s⁻¹⁆ = s * ⁅u, v⁆ * s⁻¹ := fun u v => by
    simp only [commutatorElement_def]
    group
  have hS' : ∀ t ∈ S, s⁻¹ * t * s ∈ S := fun t ht => S.mul_mem (S.mul_mem (S.inv_mem hs) ht) hs
  have h := hx4 (s⁻¹ * s₁ * s) (hS' _ hs₁) (s⁻¹ * s₂ * s) (hS' _ hs₂) (s⁻¹ * s₃ * s) (hS' _ hs₃)
    (s⁻¹ * s₄ * s) (hS' _ hs₄)
  have e : ∀ t : G, t = s * (s⁻¹ * t * s) * s⁻¹ := fun t => by group
  rw [e s₁, e s₂, e s₃, e s₄, key, key, key, key, h]
  group

omit [Finite G] in
theorem ThLocalIn2.inv_of_mem_B (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {y : G}
    (hy : y ∈ B) (hyAa : y ∉ Aa) {x : G} (hx : x ∈ Aa) : y * x * y⁻¹ = x⁻¹ := by
  have hyb : y * b ∈ Aa := (W2.mem_Aa_or_mul_b W hy).resolve_left hyAa
  have hy_eq : y = (y * b) * b := by rw [mul_assoc, ← pow_two, W2.b_sq, mul_one]
  obtain ⟨a, haAa, rfl⟩ : ∃ a ∈ Aa, y = a * b := ⟨y * b, hyb, hy_eq⟩
  calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    _ = a * x⁻¹ * a⁻¹ := by rw [W2.b_inv x hx]
    _ = x⁻¹ := by rw [W2.Aa_comm a haAa x⁻¹ (Aa.inv_mem hx)]; group

namespace SylowBounds

omit [Finite G] in
theorem sq_eq_one_of_inv_comm {y x : G} (hinv : y * x * y⁻¹ = x⁻¹) (hc : x * y = y * x) :
    x ^ 2 = 1 := by
  have h : y * x * y⁻¹ = x := by rw [← hc]; group
  rw [h] at hinv
  rw [pow_two]
  exact mul_eq_one_iff_eq_inv.2 hinv

theorem card_le_sq {K C : Subgroup G} (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hsq : ∀ x ∈ K, x ^ 2 ∈ C) (hker : ∀ x ∈ K, x ^ 2 = 1 → x ∈ C) :
    Nat.card K ≤ Nat.card C ^ 2 := by
  let f : ↥K →* ↥K := MonoidHom.mk' (fun x => x ^ 2) (fun x y => by
    apply Subtype.ext
    have hc : Commute (x : G) (y : G) := hK _ x.2 _ y.2
    simpa using hc.mul_pow 2)
  have h1 := Subgroup.card_ker_mul_card_range f
  have hker' : Nat.card f.ker ≤ Nat.card C := by
    have hmem : ∀ x : f.ker, ((x : ↥K) : G) ∈ C := fun x => hker _ x.1.2 (by
      have h1 : f x.1 = 1 := x.2
      have h2 : ((f x.1 : ↥K) : G) = ((1 : ↥K) : G) := congrArg Subtype.val h1
      exact h2)
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : ↥K) : G), hmem x⟩) ?_
    intro x y hxy
    have h3 : ((x : ↥K) : G) = ((y : ↥K) : G) := congrArg (fun w : ↥C => (w : G)) hxy
    exact Subtype.ext (Subtype.ext h3)
  have hrange' : Nat.card f.range ≤ Nat.card C := by
    have hmem : ∀ y : f.range, ((y : ↥K) : G) ∈ C := fun y => by
      obtain ⟨x, hx⟩ := y.2
      rw [← hx]
      exact hsq _ x.2
    refine Nat.card_le_card_of_injective (fun y => ⟨((y : ↥K) : G), hmem y⟩) ?_
    intro x y hxy
    have h3 : ((x : ↥K) : G) = ((y : ↥K) : G) := congrArg (fun w : ↥C => (w : G)) hxy
    exact Subtype.ext (Subtype.ext h3)
  rw [← h1, sq]
  exact Nat.mul_le_mul hker' hrange'

end SylowBounds

theorem ThLocalIn2.card_Aa_inf_centralizer_le (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (g : G) {m : ℕ}
    (h : Nat.card ↥(A ⊓ centralizer ({g} : Set G)) ≤ m) :
    Nat.card ↥(Aa ⊓ centralizer ({g} : Set G)) ≤ m ^ 2 := by
  refine (SylowBounds.card_le_sq (K := Aa ⊓ centralizer ({g} : Set G))
    (C := A ⊓ centralizer ({g} : Set G)) ?_ ?_ ?_).trans (Nat.pow_le_pow_left h 2)
  · intro x hx y hy
    exact W2.Aa_comm x hx.1 y hy.1
  · intro x hx
    exact ⟨W2.sq_mem_A hx.1, pow_mem hx.2 2⟩
  · intro x hx hx2
    exact ⟨W2.mem_A_of_sq_eq_one W hx.1 hx2, hx.2⟩

theorem ThLocalIn.card_le_eight_of_not_le (W : ThLocalIn L S A B z) {K : Subgroup G}
    (hKA : K ≤ A) (hne : ¬ A ≤ K) : Nat.card K ≤ 8 := by
  have hdvd : Nat.card K ∣ 16 := by
    rw [← W.A_card]
    exact Subgroup.card_dvd_of_le hKA
  have hne16 : Nat.card K ≠ 16 := by
    intro h16
    have heq : K = A := Subgroup.eq_of_le_of_card_ge hKA (by rw [W.A_card, h16])
    exact hne heq.symm.le
  generalize Nat.card K = d at hdvd hne16 ⊢
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hd16 : d ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases d <;> omega

omit [Finite G] in
theorem ThLocalIn2.relIndex_Aa (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) :
    Aa.relIndex B = 2 := by
  have h := Subgroup.relIndex_mul_card (H := Aa) (K := B)
  rw [inf_of_le_left W2.Aa_le, W2.Aa_card, W.B_card] at h
  omega

omit [Finite G] in
theorem ThLocalIn2.card_inf_B_le (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (Y : Subgroup G) : Nat.card ↥(Y ⊓ B) ≤ 2 * Nat.card ↥(Y ⊓ Aa) := by
  have h1 := Subgroup.relIndex_mul_card (H := Aa) (K := Y ⊓ B)
  have hrel := W2.relIndex_Aa W
  have h2 : Aa.relIndex (Y ⊓ B) ≤ Aa.relIndex B :=
    Subgroup.relIndex_le_of_le_right inf_le_right (by rw [hrel]; norm_num)
  have h3 : Aa ⊓ (Y ⊓ B) = Y ⊓ Aa := by
    ext x
    simp only [mem_inf]
    constructor
    · rintro ⟨hx1, hx2, -⟩
      exact ⟨hx2, hx1⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx2, hx1, W2.Aa_le hx2⟩
  rw [h3] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ (hrel ▸ h2)

omit [Finite G] in
theorem ThLocalIn2.inf_Aa_le_A (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    {Y : Subgroup G} (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) {y : G} (hyY : y ∈ Y)
    (hyB : y ∈ B) (hyAa : y ∉ Aa) : Y ⊓ Aa ≤ A := by
  intro x hx
  have hinv := W2.inv_of_mem_B W hyB hyAa hx.2
  exact W2.mem_A_of_sq_eq_one W hx.2
    (SylowBounds.sq_eq_one_of_inv_comm hinv (hcomm x hx.1 y hyY))

omit [Finite G] in
theorem ThLocalIn2.inf_Aa_le_A_of_sq (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    {Y : Subgroup G} (hsq : ∀ y ∈ Y, y ^ 2 = 1) : Y ⊓ Aa ≤ A := fun x hx =>
  W2.mem_A_of_sq_eq_one W hx.2 (hsq x hx.1)

namespace SylowBounds

omit [Finite G] in
theorem inf_le_inf_centralizer {Y P : Subgroup G} (hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x)
    {g : G} (hg : g ∈ Y) : Y ⊓ P ≤ P ⊓ centralizer ({g} : Set G) := fun x hx =>
  ⟨hx.2, mem_centralizer_singleton_iff.2 (hcomm x hx.1 g hg)⟩

end SylowBounds

@[expose] def TransvCent {G : Type*} [Group G] (L A B Aa : Subgroup G) : Prop :=
  ∀ g ∈ L, (∀ x ∈ A, g * x * g⁻¹ ∈ A) → g ∉ B →
    (∃ A₃ : Subgroup G, A₃ ≤ A ∧ Nat.card A₃ = 8 ∧ ∀ a ∈ A₃, g * a * g⁻¹ = a) →
    ∀ K : Subgroup G, K ≤ Aa → (∀ x ∈ K, g * x * g⁻¹ = x) → Nat.card K ≤ 16

theorem ThLocalIn.card_inf_centralizer_le_eight (W : ThLocalIn L S A B z) {g : G} (hgL : g ∈ L)
    (hgB : g ∉ B) : Nat.card ↥(A ⊓ centralizer ({g} : Set G)) ≤ 8 := by
  refine W.card_le_eight_of_not_le inf_le_left fun hA => hgB ?_
  refine (W.mem_B_iff g hgL).2 fun a ha => ?_
  exact (mem_centralizer_singleton_iff.1 (hA ha).2).symm

theorem ThLocalIn2.card_Aa_inf_centralizer_le_sixteen (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hT : TransvCent L A B Aa) {g : G} (hgL : g ∈ L)
    (hgA : ∀ x ∈ A, g * x * g⁻¹ ∈ A) (hgB : g ∉ B) :
    Nat.card ↥(Aa ⊓ centralizer ({g} : Set G)) ≤ 16 := by
  have h8 := W.card_inf_centralizer_le_eight hgL hgB
  by_cases h4 : Nat.card ↥(A ⊓ centralizer ({g} : Set G)) ≤ 4
  · exact (W2.card_Aa_inf_centralizer_le W g h4).trans (by norm_num)
  · push Not at h4
    have hdvd : Nat.card ↥(A ⊓ centralizer ({g} : Set G)) ∣ 16 := by
      rw [← W.A_card]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h8' : Nat.card ↥(A ⊓ centralizer ({g} : Set G)) = 8 := by
      generalize Nat.card ↥(A ⊓ centralizer ({g} : Set G)) = d at hdvd h4 h8
      interval_cases d <;> omega
    refine hT g hgL hgA hgB ⟨A ⊓ centralizer ({g} : Set G), inf_le_left, h8', fun a ha => ?_⟩
      (Aa ⊓ centralizer ({g} : Set G)) inf_le_left fun x hx => ?_
    · have := mem_centralizer_singleton_iff.1 ha.2
      calc g * a * g⁻¹ = (g * a) * g⁻¹ := rfl
        _ = (a * g) * g⁻¹ := by rw [this]
        _ = a := by group
    · have := mem_centralizer_singleton_iff.1 hx.2
      calc g * x * g⁻¹ = (g * x) * g⁻¹ := rfl
        _ = (x * g) * g⁻¹ := by rw [this]
        _ = x := by group

end CFSG.EvenSporadicStandard.ThStd
