module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineCountSum
public import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.SeitzReduction.RankOne

namespace SixNineCount

open Finset

variable {V : Type*} [AddCommGroup V]

theorem triv_or_free {B : Subgroup (AddMonoid.End V)ˣ}
    (hBcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g) {W₁ W₂ : AddSubgroup V} (hW : W₁ ≤ W₂)
    (hW₁ : ∀ g ∈ B, ∀ w ∈ W₁, (g : AddMonoid.End V) w ∈ W₁)
    (hW₂ : ∀ g ∈ B, ∀ w ∈ W₂, (g : AddMonoid.End V) w ∈ W₂)
    (hirr : ∀ W : AddSubgroup V, (∀ g ∈ B, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
      W₁ ≤ W → W ≤ W₂ → W = W₁ ∨ W = W₂)
    {g : (AddMonoid.End V)ˣ} (hg : g ∈ B) :
    (∀ w ∈ W₂, (g : AddMonoid.End V) w - w ∈ W₁) ∨
      (∀ w ∈ W₂, (g : AddMonoid.End V) w - w ∈ W₁ → w ∈ W₁) := by
  let C : AddSubgroup V :=
    { carrier := {w | w ∈ W₂ ∧ (g : AddMonoid.End V) w - w ∈ W₁}
      zero_mem' := ⟨W₂.zero_mem, by simp⟩
      add_mem' := by
        rintro a b ⟨ha₂, ha₁⟩ ⟨hb₂, hb₁⟩
        refine ⟨W₂.add_mem ha₂ hb₂, ?_⟩
        have e : (g : AddMonoid.End V) (a + b) - (a + b) =
            ((g : AddMonoid.End V) a - a) + ((g : AddMonoid.End V) b - b) := by
          rw [map_add]; abel
        rw [e]
        exact W₁.add_mem ha₁ hb₁
      neg_mem' := by
        rintro a ⟨ha₂, ha₁⟩
        refine ⟨W₂.neg_mem ha₂, ?_⟩
        have e : (g : AddMonoid.End V) (-a) - -a = -((g : AddMonoid.End V) a - a) := by
          rw [map_neg]; abel
        rw [e]
        exact W₁.neg_mem ha₁ }
  have hCinv : ∀ h ∈ B, ∀ w ∈ C, (h : AddMonoid.End V) w ∈ C := by
    rintro h hh w ⟨hw₂, hw₁⟩
    refine ⟨hW₂ h hh w hw₂, ?_⟩
    have hgh : (g : AddMonoid.End V) ((h : AddMonoid.End V) w) =
        (h : AddMonoid.End V) ((g : AddMonoid.End V) w) := by
      change ((g * h : (AddMonoid.End V)ˣ) : AddMonoid.End V) w =
        ((h * g : (AddMonoid.End V)ˣ) : AddMonoid.End V) w
      rw [hBcomm g hg h hh]
    rw [hgh, ← map_sub]
    exact hW₁ h hh _ hw₁
  have hW₁C : W₁ ≤ C := fun w hw => ⟨hW hw, W₁.sub_mem (hW₁ g hg w hw) hw⟩
  have hCW₂ : C ≤ W₂ := fun w hw => hw.1
  rcases hirr C hCinv hW₁C hCW₂ with h | h
  · right
    intro w hw₂ hw₁
    have hwC : w ∈ C := ⟨hw₂, hw₁⟩
    rwa [h] at hwC
  · left
    intro w hw₂
    have hwC : w ∈ C := by rw [h]; exact hw₂
    exact hwC.2

theorem triv_or_exists_triv (hV : ∀ v : V, v + v = 0) {B : Subgroup (AddMonoid.End V)ˣ}
    (hBcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g) {W₁ W₂ : AddSubgroup V} (hW : W₁ ≤ W₂)
    (hW₁ : ∀ g ∈ B, ∀ w ∈ W₁, (g : AddMonoid.End V) w ∈ W₁)
    (hW₂ : ∀ g ∈ B, ∀ w ∈ W₂, (g : AddMonoid.End V) w ∈ W₂)
    (hirr : ∀ W : AddSubgroup V, (∀ g ∈ B, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
      W₁ ≤ W → W ≤ W₂ → W = W₁ ∨ W = W₂)
    {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) {a b : (AddMonoid.End V)ˣ} (ha : a ∈ B) (hb : b ∈ B)
    (hal : a ^ l = 1) (hbl : b ^ l = 1) :
    (∀ w ∈ W₂, (a : AddMonoid.End V) w - w ∈ W₁) ∨
      ∃ j < l, ∀ w ∈ W₂, ((b * a ^ j : (AddMonoid.End V)ˣ) : AddMonoid.End V) w - w ∈ W₁ := by
  rcases Classical.em (∀ w ∈ W₂, (a : AddMonoid.End V) w - w ∈ W₁) with h | h
  · exact Or.inl h
  right
  by_contra hne
  push Not at hne
  apply h
  have hfree : ∀ j < l, ∀ w ∈ W₂, ((b : AddMonoid.End V) * (a : AddMonoid.End V) ^ j) w - w ∈ W₁ →
      w ∈ W₁ := by
    intro j hj
    have hmem : b * a ^ j ∈ B := B.mul_mem hb (B.pow_mem ha j)
    rcases triv_or_free hBcomm hW hW₁ hW₂ hirr hmem with h' | h'
    · obtain ⟨w, hw, hnw⟩ := hne j hj
      exact absurd (h' w hw) hnw
    · simpa using h'
  have hcomm : Commute (a : AddMonoid.End V) (b : AddMonoid.End V) := by
    show (a : AddMonoid.End V) * b = b * a
    rw [← Units.val_mul, ← Units.val_mul, hBcomm a ha b hb]
  have hal' : (a : AddMonoid.End V) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, hal]; rfl
  have hbl' : (b : AddMonoid.End V) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, hbl]; rfl
  exact sub_mem_of_free hV hcomm hl hl2 hal' hbl' (hW₁ a ha) (hW₂ a ha) (hW₂ b hb) hfree

theorem triv_mul {W₁ W₂ : AddSubgroup V} {g h : (AddMonoid.End V)ˣ}
    (hg₁ : ∀ w ∈ W₁, (g : AddMonoid.End V) w ∈ W₁)
    (hg : ∀ w ∈ W₂, (g : AddMonoid.End V) w - w ∈ W₁)
    (hh : ∀ w ∈ W₂, (h : AddMonoid.End V) w - w ∈ W₁) :
    ∀ w ∈ W₂, ((g * h : (AddMonoid.End V)ˣ) : AddMonoid.End V) w - w ∈ W₁ := by
  intro w hw
  have e : ((g * h : (AddMonoid.End V)ˣ) : AddMonoid.End V) w - w =
      (g : AddMonoid.End V) ((h : AddMonoid.End V) w - w) + ((g : AddMonoid.End V) w - w) := by
    rw [Units.val_mul, map_sub]
    change (g : AddMonoid.End V) ((h : AddMonoid.End V) w) - w = _
    abel
  rw [e]
  exact W₁.add_mem (hg₁ _ (hh w hw)) (hg w hw)

theorem eq_one_of_triv_triv (hV : ∀ v : V, v + v = 0) {l : ℕ} (hl : Odd l)
    {g : (AddMonoid.End V)ˣ} (hgl : g ^ l = 1) {V₁ : AddSubgroup V}
    (h₁ : ∀ w ∈ V₁, (g : AddMonoid.End V) w - w ∈ (⊥ : AddSubgroup V))
    (h₂ : ∀ w ∈ (⊤ : AddSubgroup V), (g : AddMonoid.End V) w - w ∈ V₁) : g = 1 := by
  have hsq : (g : AddMonoid.End V) ^ 2 = 1 := by
    ext v
    have hu := h₂ v (AddSubgroup.mem_top v)
    have hgu := h₁ _ hu
    rw [AddSubgroup.mem_bot, sub_eq_zero, map_sub] at hgu
    change (g : AddMonoid.End V) ((g : AddMonoid.End V) v) = v
    have e : (g : AddMonoid.End V) ((g : AddMonoid.End V) v) =
        ((g : AddMonoid.End V) ((g : AddMonoid.End V) v) - (g : AddMonoid.End V) v) +
          (g : AddMonoid.End V) v := by abel
    rw [hgu] at e
    rw [e]
    have e2 : (g : AddMonoid.End V) v - v + (g : AddMonoid.End V) v =
        v + (((g : AddMonoid.End V) v - v) + ((g : AddMonoid.End V) v - v)) := by abel
    rw [e2, hV, add_zero]
  obtain ⟨k, rfl⟩ := hl
  have hgl' : (g : AddMonoid.End V) ^ (2 * k + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hgl]; rfl
  rw [pow_succ, pow_mul, hsq, one_pow, one_mul] at hgl'
  exact Units.val_eq_one.mp hgl'

theorem card_le_mul_card_of_cover {G : Type*} [Group G] [DecidableEq G] {S K : Finset G} {a : G}
    {l : ℕ} (h : ∀ b ∈ S, ∃ j < l, b * a ^ j ∈ K) : S.card ≤ l * K.card := by
  have hsub : S ⊆ (K ×ˢ range l).image (fun x => x.1 * (a ^ x.2)⁻¹) := by
    intro b hb
    obtain ⟨j, hj, hk⟩ := h b hb
    exact mem_image.mpr ⟨(b * a ^ j, j), mem_product.mpr ⟨hk, mem_range.mpr hj⟩, by group⟩
  calc S.card ≤ ((K ×ˢ range l).image (fun x => x.1 * (a ^ x.2)⁻¹)).card := card_le_card hsub
    _ ≤ (K ×ˢ range l).card := card_image_le
    _ = l * K.card := by rw [card_product, card_range, mul_comm]

theorem eq_of_dvd_add_sub {l α α' : ℕ} (hα : α < l) (hα' : α' < l) (h : l ∣ α + (l - α')) :
    α = α' := by
  obtain ⟨k, hk⟩ := h
  have hk0 : k ≠ 0 := by rintro rfl; omega
  have hk2 : k < 2 := by
    by_contra hk2
    have := Nat.mul_le_mul_left l (not_lt.mp hk2)
    omega
  have hk1 : k = 1 := by omega
  subst hk1
  omega

theorem pow_mul_pow_mul_pow_injOn {M : Type*} [CommMonoid M] {x₁ x₂ x₃ : M} {l : ℕ}
    (hx₁ : x₁ ^ l = 1) (hx₂ : x₂ ^ l = 1) (hx₃ : x₃ ^ l = 1)
    (hind : ∀ α β γ : ℕ, x₁ ^ α * x₂ ^ β * x₃ ^ γ = 1 → l ∣ α ∧ l ∣ β ∧ l ∣ γ) :
    Set.InjOn (fun t : ℕ × ℕ × ℕ => x₁ ^ t.1 * x₂ ^ t.2.1 * x₃ ^ t.2.2)
      ((range l ×ˢ range l ×ˢ range l : Finset (ℕ × ℕ × ℕ)) : Set (ℕ × ℕ × ℕ)) := by
  rintro ⟨α, β, γ⟩ ht ⟨α', β', γ'⟩ ht' h
  simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at ht ht'
  simp only at h
  have e1 : x₁ ^ (α + (l - α')) * x₂ ^ (β + (l - β')) * x₃ ^ (γ + (l - γ')) =
      (x₁ ^ α * x₂ ^ β * x₃ ^ γ) * (x₁ ^ (l - α') * x₂ ^ (l - β') * x₃ ^ (l - γ')) := by
    simp only [pow_add]
    ac_rfl
  have e2 : (x₁ ^ α' * x₂ ^ β' * x₃ ^ γ') * (x₁ ^ (l - α') * x₂ ^ (l - β') * x₃ ^ (l - γ')) =
      1 := by
    have e3 : (x₁ ^ α' * x₂ ^ β' * x₃ ^ γ') *
        (x₁ ^ (l - α') * x₂ ^ (l - β') * x₃ ^ (l - γ')) =
        x₁ ^ (α' + (l - α')) * x₂ ^ (β' + (l - β')) * x₃ ^ (γ' + (l - γ')) := by
      simp only [pow_add]
      ac_rfl
    rw [e3, Nat.add_sub_cancel' ht'.1.le, Nat.add_sub_cancel' ht'.2.1.le,
      Nat.add_sub_cancel' ht'.2.2.le, hx₁, hx₂, hx₃, one_mul, one_mul]
  have key : x₁ ^ (α + (l - α')) * x₂ ^ (β + (l - β')) * x₃ ^ (γ + (l - γ')) = 1 := by
    rw [e1, h, e2]
  obtain ⟨d₁, d₂, d₃⟩ := hind _ _ _ key
  rw [eq_of_dvd_add_sub ht.1 ht'.1 d₁, eq_of_dvd_add_sub ht.2.1 ht'.2.1 d₂,
    eq_of_dvd_add_sub ht.2.2 ht'.2.2 d₃]

theorem triv_pow {W₁ W₂ : AddSubgroup V} {a : (AddMonoid.End V)ˣ}
    (ha₁ : ∀ w ∈ W₁, (a : AddMonoid.End V) w ∈ W₁)
    (ha : ∀ w ∈ W₂, (a : AddMonoid.End V) w - w ∈ W₁) (j : ℕ) :
    ∀ w ∈ W₂, ((a ^ j : (AddMonoid.End V)ˣ) : AddMonoid.End V) w - w ∈ W₁ := by
  induction j with
  | zero => intro w _; simp
  | succ j ih =>
    rw [pow_succ]
    have hpow₁ : ∀ w ∈ W₁, ((a ^ j : (AddMonoid.End V)ˣ) : AddMonoid.End V) w ∈ W₁ := by
      rw [Units.val_pow_eq_pow_val]
      exact pow_apply_mem ha₁ j
    exact triv_mul hpow₁ ih ha

theorem false_of_three_indep (hV : ∀ v : V, v + v = 0) [Finite V]
    {B : Subgroup (AddMonoid.End V)ˣ} (hBcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g)
    {V₁ : AddSubgroup V} (hV₁ : ∀ g ∈ B, ∀ w ∈ V₁, (g : AddMonoid.End V) w ∈ V₁)
    (hirr₁ : ∀ W : AddSubgroup V, (∀ g ∈ B, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
      W ≤ V₁ → W = ⊥ ∨ W = V₁)
    (hirr₂ : ∀ W : AddSubgroup V, (∀ g ∈ B, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
      V₁ ≤ W → W = V₁ ∨ W = ⊤)
    {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) {x₁ x₂ x₃ : (AddMonoid.End V)ˣ}
    (h₁ : x₁ ∈ B) (h₂ : x₂ ∈ B) (h₃ : x₃ ∈ B)
    (hx₁ : x₁ ^ l = 1) (hx₂ : x₂ ^ l = 1) (hx₃ : x₃ ^ l = 1)
    (hind : ∀ α β γ : ℕ, x₁ ^ α * x₂ ^ β * x₃ ^ γ = 1 → l ∣ α ∧ l ∣ β ∧ l ∣ γ) : False := by
  classical
  have : Finite (AddMonoid.End V) :=
    Finite.of_injective (fun f : AddMonoid.End V => (f : V → V))
      (fun f g h => AddMonoidHom.ext (congrFun h))
  have : Finite (AddMonoid.End V)ˣ := Finite.of_injective Units.val Units.val_injective
  let _ : Fintype (AddMonoid.End V)ˣ := Fintype.ofFinite _
  have hbot : ∀ g ∈ B, ∀ w ∈ (⊥ : AddSubgroup V),
      (g : AddMonoid.End V) w ∈ (⊥ : AddSubgroup V) := by
    intro g _ w hw
    rw [AddSubgroup.mem_bot] at hw ⊢
    rw [hw, map_zero]
  have htop : ∀ g ∈ B, ∀ w ∈ (⊤ : AddSubgroup V),
      (g : AddMonoid.End V) w ∈ (⊤ : AddSubgroup V) := fun _ _ w _ => AddSubgroup.mem_top _
  have hirr₁' : ∀ W : AddSubgroup V, (∀ g ∈ B, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
      ⊥ ≤ W → W ≤ V₁ → W = ⊥ ∨ W = V₁ := fun W hW _ hle => hirr₁ W hW hle
  have hirr₂' : ∀ W : AddSubgroup V, (∀ g ∈ B, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
      V₁ ≤ W → W ≤ ⊤ → W = V₁ ∨ W = ⊤ := fun W hW hle _ => hirr₂ W hW hle
  let S : Finset (AddMonoid.End V)ˣ := univ.filter (fun g => g ∈ B ∧ g ^ l = 1)
  let K₁ : Finset (AddMonoid.End V)ˣ :=
    S.filter (fun g => ∀ w ∈ V₁, (g : AddMonoid.End V) w - w ∈ (⊥ : AddSubgroup V))
  let K₁₂ : Finset (AddMonoid.End V)ˣ :=
    K₁.filter (fun g => ∀ w ∈ (⊤ : AddSubgroup V), (g : AddMonoid.End V) w - w ∈ V₁)
  have hmemS : ∀ g, g ∈ S ↔ g ∈ B ∧ g ^ l = 1 := fun g => by simp [S]
  have hmulS : ∀ a ∈ S, ∀ b ∈ S, ∀ j : ℕ, b * a ^ j ∈ S := by
    intro a ha b hb j
    rw [hmemS] at ha hb ⊢
    refine ⟨B.mul_mem hb.1 (B.pow_mem ha.1 j), ?_⟩
    have hc : Commute b (a ^ j) := (hBcomm b hb.1 _ (B.pow_mem ha.1 j))
    rw [hc.mul_pow, hb.2, ← pow_mul, mul_comm, pow_mul, ha.2, one_pow, one_mul]
  have hK₁₂ : K₁₂.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [K₁₂, K₁, mem_filter] at ha hb
    rw [eq_one_of_triv_triv hV (hl.odd_of_ne_two hl2) ((hmemS a).mp ha.1.1).2 ha.1.2 ha.2,
      eq_one_of_triv_triv hV (hl.odd_of_ne_two hl2) ((hmemS b).mp hb.1.1).2 hb.1.2 hb.2]
  have hA : S.card ≤ l * K₁.card := by
    by_cases hex : ∃ a ∈ S, ¬ ∀ w ∈ V₁, (a : AddMonoid.End V) w - w ∈ (⊥ : AddSubgroup V)
    · obtain ⟨a, haS, hna⟩ := hex
      apply card_le_mul_card_of_cover (a := a)
      intro b hbS
      have ha' := (hmemS a).mp haS
      have hb' := (hmemS b).mp hbS
      rcases triv_or_exists_triv hV hBcomm bot_le hbot hV₁ hirr₁' hl hl2 ha'.1 hb'.1 ha'.2
          hb'.2 with h | ⟨j, hj, hjt⟩
      · exact absurd h hna
      · exact ⟨j, hj, mem_filter.mpr ⟨hmulS a haS b hbS j, hjt⟩⟩
    · have hK : K₁ = S := Finset.filter_true_of_mem fun a ha => by
        by_contra hna
        exact hex ⟨a, ha, hna⟩
      rw [hK]
      exact Nat.le_mul_of_pos_left _ hl.pos
  have hB : K₁.card ≤ l * K₁₂.card := by
    by_cases hex : ∃ a ∈ K₁, ¬ ∀ w ∈ (⊤ : AddSubgroup V), (a : AddMonoid.End V) w - w ∈ V₁
    · obtain ⟨a, haK, hna⟩ := hex
      apply card_le_mul_card_of_cover (a := a)
      intro b hbK
      obtain ⟨haS, haT⟩ := mem_filter.mp haK
      obtain ⟨hbS, hbT⟩ := mem_filter.mp hbK
      have ha' := (hmemS a).mp haS
      have hb' := (hmemS b).mp hbS
      rcases triv_or_exists_triv hV hBcomm le_top hV₁ htop hirr₂' hl hl2 ha'.1 hb'.1 ha'.2
          hb'.2 with h | ⟨j, hj, hjt⟩
      · exact absurd h hna
      · refine ⟨j, hj, mem_filter.mpr ⟨mem_filter.mpr ⟨hmulS a haS b hbS j, ?_⟩, hjt⟩⟩
        exact triv_mul (hbot b hb'.1) hbT (triv_pow (hbot a ha'.1) haT j)
    · have hK : K₁₂ = K₁ := Finset.filter_true_of_mem fun a ha => by
        by_contra hna
        exact hex ⟨a, ha, hna⟩
      rw [hK]
      exact Nat.le_mul_of_pos_left _ hl.pos
  let _ : CommGroup B :=
    { (inferInstance : Group B) with mul_comm := fun a b => Subtype.ext (hBcomm _ a.2 _ b.2) }
  let y₁ : B := ⟨x₁, h₁⟩
  let y₂ : B := ⟨x₂, h₂⟩
  let y₃ : B := ⟨x₃, h₃⟩
  have hy : ∀ t : ℕ × ℕ × ℕ, ((y₁ ^ t.1 * y₂ ^ t.2.1 * y₃ ^ t.2.2 : B) : (AddMonoid.End V)ˣ) =
      x₁ ^ t.1 * x₂ ^ t.2.1 * x₃ ^ t.2.2 := fun t => rfl
  have hinj := pow_mul_pow_mul_pow_injOn (x₁ := y₁) (x₂ := y₂) (x₃ := y₃) (l := l)
    (Subtype.ext hx₁) (Subtype.ext hx₂) (Subtype.ext hx₃) (fun α β γ h =>
      hind α β γ (by have := congrArg Subtype.val h; exact this))
  have hy₁ : y₁ ^ l = 1 := Subtype.ext hx₁
  have hy₂ : y₂ ^ l = 1 := Subtype.ext hx₂
  have hy₃ : y₃ ^ l = 1 := Subtype.ext hx₃
  have hC : (range l ×ˢ range l ×ˢ range l).card ≤ S.card := by
    have hinj' : Set.InjOn (fun t : ℕ × ℕ × ℕ => x₁ ^ t.1 * x₂ ^ t.2.1 * x₃ ^ t.2.2)
        ((range l ×ˢ range l ×ˢ range l : Finset (ℕ × ℕ × ℕ)) : Set (ℕ × ℕ × ℕ)) :=
      fun t ht t' ht' h => hinj ht ht' (Subtype.ext h)
    rw [← card_image_of_injOn hinj']
    apply card_le_card
    intro g hg
    obtain ⟨t, -, rfl⟩ := mem_image.mp hg
    rw [hmemS]
    refine ⟨B.mul_mem (B.mul_mem (B.pow_mem h₁ _) (B.pow_mem h₂ _)) (B.pow_mem h₃ _), ?_⟩
    have hyl : (y₁ ^ t.1 * y₂ ^ t.2.1 * y₃ ^ t.2.2) ^ l = 1 := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm t.1 l, mul_comm t.2.1 l,
        mul_comm t.2.2 l, pow_mul, pow_mul, pow_mul, hy₁, hy₂, hy₃, one_pow, one_pow, one_pow,
        one_mul, one_mul]
    exact congrArg Subtype.val hyl
  have hcard : (range l ×ˢ range l ×ˢ range l).card = l * (l * l) := by
    simp [card_product]
  have hl2' : 2 ≤ l := hl.two_le
  have : l * (l * l) ≤ l * (l * 1) := by
    calc l * (l * l) ≤ S.card := hcard ▸ hC
      _ ≤ l * K₁.card := hA
      _ ≤ l * (l * K₁₂.card) := Nat.mul_le_mul_left l hB
      _ ≤ l * (l * 1) := Nat.mul_le_mul_left l (Nat.mul_le_mul_left l hK₁₂)
  have := Nat.le_of_mul_le_mul_left this hl.pos
  have := Nat.le_of_mul_le_mul_left this hl.pos
  omega

theorem no_chain_four {S : Set (AddMonoid.End V)ˣ} {X : AddSubgroup V}
    (hX : ∀ g ∈ S, ∀ w ∈ X, (g : AddMonoid.End V) w ∈ X)
    (hX₁ : ∀ W : AddSubgroup V, (∀ g ∈ S, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
      W ≤ X → W = ⊥ ∨ W = X)
    (hX₂ : ∀ W : AddSubgroup V, (∀ g ∈ S, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
      X ≤ W → W = X ∨ W = ⊤)
    {Y₀ Y₁ Y₂ Y₃ : AddSubgroup V}
    (h₀ : ∀ g ∈ S, ∀ w ∈ Y₀, (g : AddMonoid.End V) w ∈ Y₀)
    (h₁ : ∀ g ∈ S, ∀ w ∈ Y₁, (g : AddMonoid.End V) w ∈ Y₁)
    (h₂ : ∀ g ∈ S, ∀ w ∈ Y₂, (g : AddMonoid.End V) w ∈ Y₂)
    (h₃ : ∀ g ∈ S, ∀ w ∈ Y₃, (g : AddMonoid.End V) w ∈ Y₃)
    (h₀₁ : Y₀ < Y₁) (h₁₂ : Y₁ < Y₂) (h₂₃ : Y₂ < Y₃) : False := by
  classical
  have hinf : ∀ Y : AddSubgroup V, (∀ g ∈ S, ∀ w ∈ Y, (g : AddMonoid.End V) w ∈ Y) →
      ∀ g ∈ S, ∀ w ∈ Y ⊓ X, (g : AddMonoid.End V) w ∈ Y ⊓ X :=
    fun Y hY g hg w hw => ⟨hY g hg w hw.1, hX g hg w hw.2⟩
  have hsup : ∀ Y : AddSubgroup V, (∀ g ∈ S, ∀ w ∈ Y, (g : AddMonoid.End V) w ∈ Y) →
      ∀ g ∈ S, ∀ w ∈ Y ⊔ X, (g : AddMonoid.End V) w ∈ Y ⊔ X := by
    intro Y hY g hg w hw
    obtain ⟨y, hy, x, hx, rfl⟩ := AddSubgroup.mem_sup.mp hw
    rw [map_add]
    exact AddSubgroup.add_mem_sup (hY g hg y hy) (hX g hg x hx)
  have hlt : ∀ Y Y' : AddSubgroup V, (∀ g ∈ S, ∀ w ∈ Y, (g : AddMonoid.End V) w ∈ Y) →
      (∀ g ∈ S, ∀ w ∈ Y', (g : AddMonoid.End V) w ∈ Y') → Y < Y' →
      (if Y ⊓ X = X then 1 else 0) + (if Y ⊔ X = ⊤ then 1 else 0) <
        (if Y' ⊓ X = X then 1 else 0) + (if Y' ⊔ X = ⊤ then 1 else 0) := by
    intro Y Y' hY hY' hYY'
    have hle := hYY'.le
    have hm1 : Y ⊓ X = X → Y' ⊓ X = X := fun h =>
      le_antisymm inf_le_right (calc X = Y ⊓ X := h.symm
        _ ≤ Y' ⊓ X := inf_le_inf_right X hle)
    have hm2 : Y ⊔ X = ⊤ → Y' ⊔ X = ⊤ := fun h => top_unique (h ▸ sup_le_sup_right hle X)
    have hstrict : ¬ ((Y' ⊓ X = X → Y ⊓ X = X) ∧ (Y' ⊔ X = ⊤ → Y ⊔ X = ⊤)) := by
      rintro ⟨hc1, hc2⟩
      apply hYY'.not_ge
      intro w hw
      have hsup' : Y' ⊔ X ≤ Y ⊔ X := by
        rcases hX₂ _ (hsup Y' hY') le_sup_right with h | h
        · rw [h]; exact le_sup_right
        · rw [hc2 h]; exact le_top
      have hinf' : Y' ⊓ X ≤ Y ⊓ X := by
        rcases hX₁ _ (hinf Y' hY') inf_le_right with h | h
        · rw [h]; exact bot_le
        · rw [h, hc1 h]
      obtain ⟨y, hy, x, hx, hyx⟩ := AddSubgroup.mem_sup.mp (hsup' (AddSubgroup.mem_sup_left hw))
      have hxY' : x ∈ Y' := by
        have e : x = w - y := by rw [← hyx]; abel
        rw [e]
        exact Y'.sub_mem hw (hle hy)
      have hxY : x ∈ Y := (hinf' ⟨hxY', hx⟩).1
      rw [← hyx]
      exact Y.add_mem hy hxY
    split_ifs <;> first | omega | (exfalso; tauto)
  have a := hlt _ _ h₀ h₁ h₀₁
  have b := hlt _ _ h₁ h₂ h₁₂
  have c := hlt _ _ h₂ h₃ h₂₃
  have d : (if Y₃ ⊓ X = X then 1 else 0) + (if Y₃ ⊔ X = ⊤ then 1 else 0) ≤ 2 := by
    split_ifs <;> omega
  omega

theorem exists_layers {S : Set (AddMonoid.End V)ˣ} {X : AddSubgroup V}
    (hX : ∀ g ∈ S, ∀ w ∈ X, (g : AddMonoid.End V) w ∈ X)
    (hX₁ : ∀ W : AddSubgroup V, (∀ g ∈ S, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
      W ≤ X → W = ⊥ ∨ W = X)
    (hX₂ : ∀ W : AddSubgroup V, (∀ g ∈ S, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
      X ≤ W → W = X ∨ W = ⊤)
    (B : Subgroup (AddMonoid.End V)ˣ) (hSB : S ⊆ B) :
    ∃ V₁ : AddSubgroup V, (∀ g ∈ B, ∀ w ∈ V₁, (g : AddMonoid.End V) w ∈ V₁) ∧
      (∀ W : AddSubgroup V, (∀ g ∈ B, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
        W ≤ V₁ → W = ⊥ ∨ W = V₁) ∧
      (∀ W : AddSubgroup V, (∀ g ∈ B, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
        V₁ ≤ W → W = V₁ ∨ W = ⊤) := by
  classical
  have hBS : ∀ W : AddSubgroup V, (∀ g ∈ B, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
      ∀ g ∈ S, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W := fun W hW g hg => hW g (hSB hg)
  have hbot : ∀ g ∈ B, ∀ w ∈ (⊥ : AddSubgroup V),
      (g : AddMonoid.End V) w ∈ (⊥ : AddSubgroup V) := by
    intro g _ w hw
    rw [AddSubgroup.mem_bot] at hw ⊢
    rw [hw, map_zero]
  have htop : ∀ g ∈ B, ∀ w ∈ (⊤ : AddSubgroup V),
      (g : AddMonoid.End V) w ∈ (⊤ : AddSubgroup V) := fun _ _ w _ => AddSubgroup.mem_top _
  by_cases hex : ∃ W : AddSubgroup V, (∀ g ∈ B, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) ∧
      ⊥ < W ∧ W < ⊤
  · obtain ⟨W, hW, hbW, hWt⟩ := hex
    refine ⟨W, hW, ?_, ?_⟩
    · intro W' hW' hle
      by_contra hne
      have h1 : ⊥ < W' := bot_lt_iff_ne_bot.mpr fun h => hne (Or.inl h)
      have h2 : W' < W := lt_of_le_of_ne hle fun h => hne (Or.inr h)
      exact no_chain_four hX hX₁ hX₂ (hBS _ hbot) (hBS _ hW') (hBS _ hW) (hBS _ htop) h1 h2 hWt
    · intro W' hW' hle
      by_contra hne
      have h1 : W < W' := lt_of_le_of_ne hle fun h => hne (Or.inl h.symm)
      have h2 : W' < ⊤ := lt_top_iff_ne_top.mpr fun h => hne (Or.inr h)
      exact no_chain_four hX hX₁ hX₂ (hBS _ hbot) (hBS _ hW) (hBS _ hW') (hBS _ htop) hbW h1 h2
  · refine ⟨⊥, hbot, fun W _ hle => Or.inl (le_bot_iff.mp hle), fun W hW _ => ?_⟩
    by_cases hb : W = ⊥
    · exact Or.inl hb
    · right
      by_contra ht
      exact hex ⟨W, hW, bot_lt_iff_ne_bot.mpr hb, lt_top_iff_ne_top.mpr ht⟩

theorem false_of_layers_indep (hV : ∀ v : V, v + v = 0) [Finite V]
    {B : Subgroup (AddMonoid.End V)ˣ} (hBcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g)
    {S : Set (AddMonoid.End V)ˣ} (hSB : S ⊆ B) {X : AddSubgroup V}
    (hX : ∀ g ∈ S, ∀ w ∈ X, (g : AddMonoid.End V) w ∈ X)
    (hX₁ : ∀ W : AddSubgroup V, (∀ g ∈ S, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
      W ≤ X → W = ⊥ ∨ W = X)
    (hX₂ : ∀ W : AddSubgroup V, (∀ g ∈ S, ∀ w ∈ W, (g : AddMonoid.End V) w ∈ W) →
      X ≤ W → W = X ∨ W = ⊤)
    {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) {x₁ x₂ x₃ : (AddMonoid.End V)ˣ}
    (h₁ : x₁ ∈ B) (h₂ : x₂ ∈ B) (h₃ : x₃ ∈ B)
    (hx₁ : x₁ ^ l = 1) (hx₂ : x₂ ^ l = 1) (hx₃ : x₃ ^ l = 1)
    (hind : ∀ α β γ : ℕ, x₁ ^ α * x₂ ^ β * x₃ ^ γ = 1 → l ∣ α ∧ l ∣ β ∧ l ∣ γ) : False := by
  obtain ⟨V₁, hV₁, hirr₁, hirr₂⟩ := exists_layers hX hX₁ hX₂ B hSB
  exact false_of_three_indep hV hBcomm hV₁ hirr₁ hirr₂ hl hl2 h₁ h₂ h₃ hx₁ hx₂ hx₃ hind

end SixNineCount

end CFSG.SeitzReduction.RankOne
