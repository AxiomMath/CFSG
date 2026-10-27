module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResHSplit

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH

open Subgroup

variable {V : Type*} [CommGroup V]

@[expose] def resSet (S : Subgroup (MulAut V)) (U : Subgroup V) : Set (U → V) :=
  Set.range fun t : S => fun u : U => (t : MulAut V) (u : V)

theorem ncard_range_le_of_factors {α X Y : Type*} [Finite Y] {f : α → X} {g : α → Y}
    (hfg : ∀ a b, g a = g b → f a = f b) : (Set.range f).ncard ≤ (Set.range g).ncard := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [Set.range_eq_empty]
  · classical
    let F : Y → X := Function.extend g f fun _ => f (Classical.arbitrary α)
    have hF : ∀ a, F (g a) = f a := fun a =>
      Function.FactorsThrough.extend_apply (fun a b hab => hfg a b hab) _ a
    have hrange : Set.range f = F '' Set.range g := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨g a, ⟨a, rfl⟩, hF a⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, (hF a).symm⟩
    rw [hrange]
    exact Set.ncard_image_le (Set.toFinite _)

theorem eq_of_mul_eq_of_le {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) (hc : 0 < c) (hd : 0 < d)
    (h : a * b = c * d) : a = c ∧ b = d := by
  have hcd : 0 < c * d := Nat.mul_pos hc hd
  have ha : 0 < a := Nat.pos_of_ne_zero fun h0 => by simp [h0] at h; omega
  have hb : 0 < b := Nat.pos_of_ne_zero fun h0 => by simp [h0] at h; omega
  have h1 : a = c := by
    by_contra hne
    have hlt : a < c := lt_of_le_of_ne hac hne
    have := Nat.mul_lt_mul_of_pos_right hlt hb
    have := Nat.mul_le_mul_left c hbd
    omega
  subst h1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left ha h⟩

@[expose] def RankBound (p : ℕ) (S : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∀ d : ℕ, Nat.card U = p ^ d → (resSet S U).ncard ≤ 2 ^ d ∧
    ((resSet S U).ncard = 2 ^ d → ∃ t ∈ S, ∀ u ∈ U, t u = u⁻¹)

theorem rankBound_base {p : ℕ} {S : Subgroup (MulAut V)} [Finite V] {U : Subgroup V}
    (hpm : ∀ t ∈ S, (∀ u ∈ U, t u = u) ∨ ∀ u ∈ U, t u = u⁻¹) : RankBound p S U := by
  intro d hd
  have hsub : resSet S U ⊆ {fun u : U => (u : V), fun u : U => (u : V)⁻¹} := by
    rintro _ ⟨⟨t, ht⟩, rfl⟩
    rcases hpm t ht with h1 | h1
    · left; funext u; exact h1 u u.2
    · right; funext u; exact h1 u u.2
  have h2 : (resSet S U).ncard ≤ 2 := by
    calc (resSet S U).ncard
        ≤ ({fun u : U => (u : V), fun u : U => (u : V)⁻¹} : Set (U → V)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 1 + 1 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · have hbot : U = ⊥ := (Subgroup.eq_bot_iff_card U).2 (by rw [hd, pow_zero])
    have hu1 : ∀ u ∈ U, u = 1 := fun u hu => by simpa [hbot] using hu
    have hsub1 : resSet S U ⊆ {fun _ : U => (1 : V)} := by
      rintro _ ⟨⟨t, ht⟩, rfl⟩
      funext u
      show t (u : V) = 1
      rw [hu1 u u.2, map_one]
    have hle : (resSet S U).ncard ≤ 1 := by
      calc (resSet S U).ncard ≤ ({fun _ : U => (1 : V)} : Set (U → V)).ncard :=
            Set.ncard_le_ncard hsub1 (Set.toFinite _)
        _ = 1 := Set.ncard_singleton _
    refine ⟨by simpa using hle, fun _ => ⟨1, S.one_mem, fun u hu => ?_⟩⟩
    rw [hu1 u hu]
    simp
  · have h2d : 2 ≤ 2 ^ d := Nat.le_self_pow (by omega) 2
    refine ⟨h2.trans h2d, fun hcard => ?_⟩
    have h1 : 1 < (resSet S U).ncard := by
      rw [hcard]
      exact Nat.one_lt_two_pow (by omega)
    obtain ⟨f, g, ⟨⟨t₁, ht₁⟩, rfl⟩, ⟨⟨t₂, ht₂⟩, rfl⟩, hne⟩ :=
      (Set.one_lt_ncard_iff (Set.toFinite _)).1 h1
    rcases hpm t₁ ht₁ with h₁ | h₁
    · rcases hpm t₂ ht₂ with h₂ | h₂
      · exact absurd (funext fun u : U => (h₁ (u : V) u.2).trans (h₂ (u : V) u.2).symm) hne
      · exact ⟨t₂, ht₂, h₂⟩
    · exact ⟨t₁, ht₁, h₁⟩

namespace Setup

variable {p : ℕ} {S : Subgroup (MulAut V)} (h : Setup p S)
include h

theorem rankBound_step [Finite V] {U : Subgroup V} (hU : IsInvariant S U) {s : MulAut V}
    (hs : s ∈ S) (hA : RankBound p S (plusPart s U)) (hB : RankBound p S (minusPart s U)) :
    RankBound p S U := by
  intro d hd
  have hsU : ∀ u ∈ U, s u ∈ U := hU s hs
  have hcard := h.card_eq_mul hs hsU
  obtain ⟨i, hid, hi⟩ := (Nat.dvd_prime_pow h.prime).1
    (show Nat.card (plusPart s U) ∣ p ^ d by rw [← hd, hcard]; exact dvd_mul_right _ _)
  obtain ⟨j, hjd, hj⟩ := (Nat.dvd_prime_pow h.prime).1
    (show Nat.card (minusPart s U) ∣ p ^ d by rw [← hd, hcard]; exact dvd_mul_left _ _)
  have hdij : d = i + j :=
    Nat.pow_right_injective h.prime.two_le
      (show p ^ d = p ^ (i + j) by rw [← hd, hcard, hi, hj, pow_add])
  obtain ⟨hA1, hA2⟩ := hA i hi
  obtain ⟨hB1, hB2⟩ := hB j hj
  let Φ : S → (plusPart s U → V) × (minusPart s U → V) := fun t =>
    (fun a => (t : MulAut V) (a : V), fun b => (t : MulAut V) (b : V))
  have hΦsub : Set.range Φ ⊆ resSet S (plusPart s U) ×ˢ resSet S (minusPart s U) := by
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨t, rfl⟩, ⟨t, rfl⟩⟩
  have hfac : (resSet S U).ncard ≤ (Set.range Φ).ncard := by
    refine ncard_range_le_of_factors (fun a b hab => ?_)
    funext u
    obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_mul_eq hs hsU u.2
    have hx' := congrFun (congrArg Prod.fst hab) ⟨x, hx⟩
    have hy' := congrFun (congrArg Prod.snd hab) ⟨y, hy⟩
    show (a : MulAut V) (u : V) = (b : MulAut V) (u : V)
    rw [← hxy, map_mul, map_mul]
    exact congrArg₂ _ hx' hy'
  have hprod : (resSet S (plusPart s U) ×ˢ resSet S (minusPart s U)).ncard =
      (resSet S (plusPart s U)).ncard * (resSet S (minusPart s U)).ncard := Set.ncard_prod
  have hle : (Set.range Φ).ncard ≤
      (resSet S (plusPart s U)).ncard * (resSet S (minusPart s U)).ncard :=
    hprod ▸ Set.ncard_le_ncard hΦsub (Set.toFinite _)
  have hmul : 2 ^ d = 2 ^ i * 2 ^ j := by rw [hdij, pow_add]
  refine ⟨?_, fun heq => ?_⟩
  · calc (resSet S U).ncard ≤ (Set.range Φ).ncard := hfac
      _ ≤ _ := hle
      _ ≤ 2 ^ i * 2 ^ j := Nat.mul_le_mul hA1 hB1
      _ = 2 ^ d := hmul.symm
  · have hchain : (resSet S (plusPart s U)).ncard * (resSet S (minusPart s U)).ncard =
        2 ^ i * 2 ^ j := by
      refine le_antisymm (Nat.mul_le_mul hA1 hB1) ?_
      calc 2 ^ i * 2 ^ j = (resSet S U).ncard := by rw [← hmul, heq]
        _ ≤ (Set.range Φ).ncard := hfac
        _ ≤ _ := hle
    obtain ⟨hAeq, hBeq⟩ := eq_of_mul_eq_of_le hA1 hB1 (pow_pos two_pos i) (pow_pos two_pos j) hchain
    obtain ⟨tA, htA, htAinv⟩ := hA2 hAeq
    obtain ⟨tB, htB, htBinv⟩ := hB2 hBeq
    have hrange : Set.range Φ = resSet S (plusPart s U) ×ˢ resSet S (minusPart s U) := by
      refine Set.eq_of_subset_of_ncard_le hΦsub ?_ (Set.toFinite _)
      rw [hprod, hchain, ← hmul, ← heq]
      exact hfac
    have hmem : ((fun a : plusPart s U => (tA : MulAut V) (a : V)),
        (fun b : minusPart s U => (tB : MulAut V) (b : V))) ∈ Set.range Φ := by
      rw [hrange]
      exact ⟨⟨⟨tA, htA⟩, rfl⟩, ⟨⟨tB, htB⟩, rfl⟩⟩
    obtain ⟨⟨t, ht⟩, hΦt⟩ := hmem
    refine ⟨t, ht, fun u hu => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := h.exists_mul_eq hs hsU hu
    have hx' : t x = tA x := congrFun (congrArg Prod.fst hΦt) ⟨x, hx⟩
    have hy' : t y = tB y := congrFun (congrArg Prod.snd hΦt) ⟨y, hy⟩
    rw [map_mul, hx', hy', htAinv x hx, htBinv y hy, mul_inv]

theorem rankBound_all [Finite V] : ∀ U, IsInvariant S U → RankBound p S U :=
  h.induction (P := RankBound p S) (fun _ _ hpm => rankBound_base hpm)
    fun _ hU _ hs _ _ hA hB => h.rankBound_step hU hs hA hB

end Setup

theorem elemAb_card_le_and_inv_mem {p r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ p = 1) (hcard : Nat.card V = p ^ r)
    (S : Subgroup (MulAut V)) (hS : ∀ s ∈ S, s * s = 1)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) :
    Nat.card S ≤ 2 ^ r ∧ (Nat.card S = 2 ^ r → MulEquiv.inv V ∈ S) := by
  have h : Setup p S := ⟨Fact.out, hp2, hV, hS, hcomm⟩
  have htop : Nat.card (⊤ : Subgroup V) = p ^ r := by rw [Subgroup.card_top, hcard]
  obtain ⟨h1, h2⟩ := h.rankBound_all ⊤ (fun _ _ _ _ => mem_top _) r htop
  have hinj : Function.Injective
      fun t : S => fun u : (⊤ : Subgroup V) => (t : MulAut V) (u : V) := by
    intro t t' htt'
    refine Subtype.ext (MulEquiv.ext fun v => ?_)
    exact congrFun htt' ⟨v, mem_top v⟩
  have hres : (resSet S ⊤).ncard = Nat.card S := Set.ncard_range_of_injective hinj
  rw [hres] at h1 h2
  refine ⟨h1, fun hc => ?_⟩
  obtain ⟨t, ht, htinv⟩ := h2 hc
  have : t = MulEquiv.inv V := MulEquiv.ext fun v => htinv v (mem_top v)
  exact this ▸ ht

end CFSG.EvenSporadicStandard.M24Std.CResH
