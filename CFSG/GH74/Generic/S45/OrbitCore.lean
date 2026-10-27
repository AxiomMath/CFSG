module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.Generic.S45

open Subgroup

section

variable {T : Type} [Group T]

theorem mem_or_mem_coset (hcomm : ∀ a b : T, a * b = b * a) (hcard : Nat.card T = 16)
    (R : Subgroup T) (hR : Nat.card R = 8) {x : T} (hxR : x ∉ R) (t : T) :
    t ∈ R ∨ x⁻¹ * t ∈ R := by
  have hidx : R.index = 2 := by
    have := Subgroup.card_mul_index R
    rw [hR, hcard] at this
    omega
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hidx
  by_cases ht : t ∈ R
  · exact Or.inl ht
  · right
    have h1 : t * a ∈ R := by
      rcases (ha t) with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h ht
    have h2 : x * a ∈ R := by
      rcases (ha x) with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hxR
    have h3 : (t * a) * (x * a)⁻¹ ∈ R := mul_mem h1 (inv_mem h2)
    have h4 : (t * a) * (x * a)⁻¹ = t * x⁻¹ := by group
    rw [h4, hcomm t x⁻¹] at h3
    exact (hcomm x⁻¹ t) ▸ h3

theorem orbit_card (A B : Subgroup (MulAut T)) (x : T)
    (hBx : ∀ f ∈ B, f x = x) (hAB : ∀ f ∈ A, f x = x → f ∈ B) (hBA : B ≤ A) :
    Nat.card (MulAction.orbit A x) * Nat.card B = Nat.card A := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (↥A) x)
  have h2 := MulAction.index_stabilizer (↥A) x
  have hst : Nat.card (MulAction.stabilizer (↥A) x) = Nat.card B := by
    apply Nat.card_congr
    refine ⟨fun f => ⟨(f.1 : MulAut T), ?_⟩, fun f => ⟨⟨f.1, hBA f.2⟩, ?_⟩, ?_, ?_⟩
    · exact hAB _ f.1.2 f.2
    · exact hBx _ f.2
    · intro f; rfl
    · intro f; rfl
  rw [hst, h2] at h1
  rw [mul_comm]
  exact h1

theorem mem_orbit_iff (A : Subgroup (MulAut T)) (x y : T) :
    y ∈ MulAction.orbit A x ↔ ∃ f ∈ A, f x = y := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.1, f.2, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩

variable [Finite T]

theorem card_ne_one : Nat.card {y : T // y ≠ 1} + 1 = Nat.card T := by
  have : Fintype T := Fintype.ofFinite T
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have h1 : Fintype.card {y : T // y = 1} = 1 := Fintype.card_subtype_eq 1
  have h2 : 0 < Fintype.card T := Fintype.card_pos
  rw [h1]
  omega

theorem exists_ne_one_ne (R : Subgroup T) (hR : Nat.card R = 8) (r : T) (hr : r ∈ R) :
    ∃ r₂ ∈ R, r₂ ≠ 1 ∧ r₂ ≠ r := by
  classical
  have : Fintype R := Fintype.ofFinite R
  have hc : Fintype.card R = 8 := by rw [← Nat.card_eq_fintype_card]; exact hR
  have h2 : ({1, (⟨r, hr⟩ : R)} : Finset R).card < (Finset.univ : Finset R).card := by
    rw [Finset.card_univ, hc]
    calc ({1, (⟨r, hr⟩ : R)} : Finset R).card ≤ 2 := Finset.card_le_two
      _ < 8 := by norm_num
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card h2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  refine ⟨y, y.2, ?_, ?_⟩
  · intro h
    apply hy.1
    exact Subtype.ext h
  · intro h
    apply hy.2
    exact Subtype.ext h

theorem exists_ne_one (R : Subgroup T) (hR : Nat.card R = 8) : ∃ r₀ ∈ R, r₀ ≠ 1 := by
  have : Nontrivial R := (Finite.one_lt_card_iff_nontrivial (α := R)).1 (by omega)
  obtain ⟨⟨r₀, hr₀R⟩, hne⟩ := exists_ne (1 : R)
  exact ⟨r₀, hr₀R, fun h => hne (Subtype.ext h)⟩

theorem orbit_analysis
    (hcomm : ∀ a b : T, a * b = b * a) (hsq : ∀ a : T, a * a = 1) (hcard : Nat.card T = 16)
    (R : Subgroup T) (hR : Nat.card R = 8) {x : T} (hxR : x ∉ R)
    (A B : Subgroup (MulAut T)) (hBA : B ≤ A) (hBx : ∀ f ∈ B, f x = x)
    (hAB : ∀ f ∈ A, f x = x → f ∈ B)
    (htrans : ∀ r ∈ R, r ≠ 1 → ∀ s ∈ R, s ≠ 1 → ∃ f ∈ B, f r = s)
    (hB21 : Nat.card B = 21)
    (hnon : ∃ f ∈ A, f x ≠ x) (h315 : ∀ A' : Subgroup (MulAut T), Nat.card A' ≠ 315) :
    (∀ f ∈ A, x⁻¹ * f x ∈ R) ∧ (∀ r ∈ R, ∃ f ∈ A, f x = x * r) := by
  classical
  have hx1 : x ≠ 1 := fun h => hxR (h ▸ one_mem R)
  have hcos := mem_or_mem_coset hcomm hcard R hR hxR
  have hΩ : ∀ y, y ∈ MulAction.orbit A x ↔ ∃ f ∈ A, f x = y := mem_orbit_iff A x
  have hxΩ : x ∈ MulAction.orbit A x := (hΩ x).2 ⟨1, one_mem _, rfl⟩
  have hΩne : ∀ y ∈ MulAction.orbit A x, y ≠ 1 := by
    intro y hy
    obtain ⟨f, _, rfl⟩ := (hΩ y).1 hy
    intro h
    apply hx1
    apply f.injective
    rw [h, map_one]
  have hΩmul : ∀ g ∈ A, ∀ y ∈ MulAction.orbit A x, g y ∈ MulAction.orbit A x := by
    intro g hg y hy
    obtain ⟨f, hf, rfl⟩ := (hΩ y).1 hy
    exact (hΩ _).2 ⟨g * f, mul_mem hg hf, rfl⟩
  have step1R : ∀ v ∈ MulAction.orbit A x, v ∈ R → ∀ s ∈ R, s ≠ 1 → s ∈ MulAction.orbit A x := by
    intro v hv hvR s hs hs1
    obtain ⟨f, hfA, rfl⟩ := (hΩ _).1 hv
    obtain ⟨b, hbB, hb⟩ := htrans _ hvR (hΩne _ hv) s hs hs1
    exact (hΩ s).2 ⟨b * f, mul_mem (hBA hbB) hfA, hb⟩
  have step1X : ∀ v ∈ MulAction.orbit A x, x⁻¹ * v ∈ R → v ≠ x → ∀ s ∈ R, s ≠ 1 →
      x * s ∈ MulAction.orbit A x := by
    intro v hv hvR hvx s hs hs1
    obtain ⟨f, hfA, rfl⟩ := (hΩ _).1 hv
    have hr1 : x⁻¹ * f x ≠ 1 := by
      intro h
      apply hvx
      have : f x = x := by
        have := congrArg (fun u => x * u) h
        simpa using this
      exact this
    obtain ⟨b, hbB, hb⟩ := htrans _ hvR hr1 s hs hs1
    refine (hΩ _).2 ⟨b * f, mul_mem (hBA hbB) hfA, ?_⟩
    have h1 : f x = x * (x⁻¹ * f x) := by group
    show b (f x) = x * s
    rw [h1, map_mul, hBx b hbB, hb]
  obtain ⟨f₀, hf₀A, hf₀⟩ := hnon
  have hv₀ : f₀ x ∈ MulAction.orbit A x := (hΩ _).2 ⟨f₀, hf₀A, rfl⟩
  have hP : (∀ s ∈ R, s ≠ 1 → s ∈ MulAction.orbit A x) ∨
      (∀ s ∈ R, s ≠ 1 → x * s ∈ MulAction.orbit A x) := by
    rcases hcos (f₀ x) with h | h
    · exact Or.inl (step1R _ hv₀ h)
    · exact Or.inr (step1X _ hv₀ h hf₀)
  by_cases hP₁ : ∀ s ∈ R, s ≠ 1 → s ∈ MulAction.orbit A x
  · by_cases hP₂ : ∀ s ∈ R, s ≠ 1 → x * s ∈ MulAction.orbit A x
    · exfalso
      have hΩeq : MulAction.orbit A x = {y | y ≠ 1} := by
        ext y
        constructor
        · exact fun hy => hΩne y hy
        · intro hy
          have hy1 : y ≠ 1 := hy
          rcases hcos y with h | h
          · exact hP₁ y h hy1
          · by_cases hs : x⁻¹ * y = 1
            · have : y = x := by
                have := congrArg (fun u => x * u) hs
                simpa using this
              rw [this]; exact hxΩ
            · have := hP₂ _ h hs
              simpa using this
      have hc15 : Nat.card (MulAction.orbit A x) = 15 := by
        rw [hΩeq]
        have := card_ne_one (T := T)
        rw [hcard] at this
        have h2 : Nat.card ↥({y : T | y ≠ 1}) = Nat.card {y : T // y ≠ 1} := rfl
        omega
      have := orbit_card A B x hBx hAB hBA
      rw [hc15, hB21] at this
      exact h315 A (by omega)
    · exfalso
      have hno : ∀ v ∈ MulAction.orbit A x, v ≠ x → x⁻¹ * v ∈ R → False := by
        intro v hv hvx hvR
        exact hP₂ (fun s hs hs1 => step1X v hv hvR hvx s hs hs1)
      have hΩsub : ∀ v ∈ MulAction.orbit A x, v = x ∨ v ∈ R := by
        intro v hv
        by_cases hvx : v = x
        · exact Or.inl hvx
        · rcases hcos v with h | h
          · exact Or.inr h
          · exact (hno v hv hvx h).elim
      obtain ⟨r₀, hr₀R, hr₀1⟩ := exists_ne_one R hR
      obtain ⟨f, hfA, hf⟩ := (hΩ r₀).1 (hP₁ r₀ hr₀R hr₀1)
      have hfR : ∀ r ∈ R, f r ∈ R := by
        intro r hr
        by_cases hr1 : r = 1
        · rw [hr1, map_one]; exact one_mem R
        · have hrΩ : r ∈ MulAction.orbit A x := hP₁ r hr hr1
          have hfrΩ : f r ∈ MulAction.orbit A x := hΩmul f hfA r hrΩ
          rcases hΩsub _ hfrΩ with h | h
          · exfalso
            obtain ⟨r₂, hr₂R, hr₂1, hr₂r⟩ := exists_ne_one_ne R hR r hr
            have h2Ω : f r₂ ∈ MulAction.orbit A x := hΩmul f hfA r₂ (hP₁ r₂ hr₂R hr₂1)
            have h2x : f r₂ ≠ x := by
              intro h2
              apply hr₂r
              apply f.injective
              rw [h2, h]
            have h2R : f r₂ ∈ R := (hΩsub _ h2Ω).resolve_left h2x
            have hrr₂R : r * r₂ ∈ R := mul_mem hr hr₂R
            have hrr₂1 : r * r₂ ≠ 1 := by
              intro h3
              apply hr₂r
              have h4 : r₂ = r⁻¹ := eq_inv_of_mul_eq_one_right h3
              have h5 : r⁻¹ = r := inv_eq_of_mul_eq_one_right (hsq r)
              rw [h4, h5]
            have h3Ω : f (r * r₂) ∈ MulAction.orbit A x :=
              hΩmul f hfA _ (hP₁ _ hrr₂R hrr₂1)
            have h4 : f (r * r₂) = x * f r₂ := by rw [map_mul, h]
            have h5 : x * f r₂ ≠ x := by
              intro h6
              apply hr₂1
              apply f.injective
              rw [map_one]
              exact mul_left_cancel (h6.trans (mul_one x).symm)
            exact hno (f (r * r₂)) h3Ω (by rw [h4]; exact h5) (by rw [h4]; simpa using h2R)
          · exact h
      have hinj : Function.Injective (fun r : R => (⟨f r, hfR r r.2⟩ : R)) := by
        intro a b hab
        have := congrArg Subtype.val hab
        exact Subtype.ext (f.injective this)
      obtain ⟨r', hr'⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨r₀, hr₀R⟩
      have hr'val : f r' = r₀ := congrArg Subtype.val hr'
      have : (r' : T) = x := f.injective (by rw [hr'val, hf])
      exact hxR (this ▸ r'.2)
  · have hP₂ : ∀ s ∈ R, s ≠ 1 → x * s ∈ MulAction.orbit A x := hP.resolve_left hP₁
    refine ⟨?_, ?_⟩
    · intro f hf
      have hv : f x ∈ MulAction.orbit A x := (hΩ _).2 ⟨f, hf, rfl⟩
      rcases hcos (f x) with h | h
      · exact absurd (step1R _ hv h) hP₁
      · exact h
    · intro r hr
      by_cases hr1 : r = 1
      · exact ⟨1, one_mem _, by simp [hr1]⟩
      · exact (hΩ _).1 (hP₂ r hr hr1)

omit [Finite T] in
theorem card_A_eq (R : Subgroup T) (hR : Nat.card R = 8) {x : T}
    (A B : Subgroup (MulAut T)) (hBA : B ≤ A) (hBx : ∀ f ∈ B, f x = x)
    (hAB : ∀ f ∈ A, f x = x → f ∈ B) (hB21 : Nat.card B = 21)
    (h1 : ∀ f ∈ A, x⁻¹ * f x ∈ R) (h2 : ∀ r ∈ R, ∃ f ∈ A, f x = x * r) :
    Nat.card A = 168 := by
  have hcard : Nat.card (MulAction.orbit A x) = Nat.card R := by
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun r : R => (⟨x * (r : T), (mem_orbit_iff A x _).2 (h2 r r.2)⟩ : MulAction.orbit A x))
      ⟨?_, ?_⟩)
    · intro a b hab
      exact Subtype.ext (mul_left_cancel (congrArg Subtype.val hab))
    · rintro ⟨y, hy⟩
      obtain ⟨f, hf, rfl⟩ := (mem_orbit_iff A x y).1 hy
      refine ⟨⟨x⁻¹ * f x, h1 f hf⟩, Subtype.ext ?_⟩
      exact mul_inv_cancel_left x (f x)
  have := orbit_card A B x hBx hAB hBA
  rw [hcard, hR, hB21] at this
  omega

end

end CFSG.GH74.Generic.S45
