module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterKGA8TAlt

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup Equiv Equiv.Perm Nat

theorem alt_data {K : Type} [Group K] (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : K ≃* alternatingGroup (Fin n)) (τ : MulAut K) (h2 : τ * τ = 1) (h1 : τ ≠ 1) :
    ∃ π : Perm (Fin n), π * π = 1 ∧
      (∀ x : K, ((e (τ x) : alternatingGroup (Fin n)) : Perm (Fin n)) =
        π * ((e x : alternatingGroup (Fin n)) : Perm (Fin n)) * π⁻¹) ∧
      ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ n ∧ π.cycleType = Multiset.replicate a 2 ∧
        2 * Nat.card (autCentralizer τ) = (n - 2 * a)! * 2 ^ a * a ! := by
  classical
  have hτsq : ∀ x : K, τ (τ x) = x := fun x => by
    have := congrArg (fun f : MulAut K => f x) h2
    simpa using this
  let τ' : MulAut (alternatingGroup (Fin n)) := e.symm.trans ((τ : K ≃* K).trans e)
  have hτ' : ∀ a, τ' a = e (τ (e.symm a)) := fun _ => rfl
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn
    hn6).2 τ'
  have hinj := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).1
  have hsq : π * π = 1 := by
    apply hinj
    rw [map_mul, hπ, map_one]
    ext a
    simp [hτ', hτsq]
  have hne : π ≠ 1 := by
    rintro rfl
    apply h1
    ext x
    have h3 : τ' (e x) = e x := by rw [← hπ]; simp
    rw [hτ'] at h3
    simpa using h3
  have key : ∀ x : K, τ x = x ↔
      π * ((e x : alternatingGroup (Fin n)) : Perm (Fin n)) =
        ((e x : alternatingGroup (Fin n)) : Perm (Fin n)) * π := by
    intro x
    have h1' : τ' (e x) = e (τ x) := by simp [hτ']
    constructor
    · intro hx
      have h3 : MulAut.conjNormal π (e x) = e x := by rw [hπ, h1', hx]
      have h4 := congrArg Subtype.val h3
      rw [MulAut.conjNormal_apply] at h4
      exact mul_inv_eq_iff_eq_mul.1 h4
    · intro h
      apply e.injective
      rw [← h1', ← hπ]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, h, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : ∀ x : K, ((e (τ x) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      π * ((e x : alternatingGroup (Fin n)) : Perm (Fin n)) * π⁻¹ := by
    intro x
    have h1' : τ' (e x) = e (τ x) := by simp [hτ']
    rw [← h1', ← hπ, MulAut.conjNormal_apply]
  let sg : centralizer ({π} : Set (Perm (Fin n))) →* ℤˣ :=
    (sign : Perm (Fin n) →* ℤˣ).comp (centralizer ({π} : Set (Perm (Fin n)))).subtype
  have hbij : Nat.card (autCentralizer τ) = Nat.card sg.ker := by
    let f : autCentralizer τ → sg.ker := fun x =>
      ⟨⟨((e x : alternatingGroup (Fin n)) : Perm (Fin n)),
        Subgroup.mem_centralizer_singleton_iff.2 ((key x).1 x.2).symm⟩,
        mem_alternatingGroup.1 (e x).2⟩
    refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
    · intro x y hxy
      have := congrArg (fun z : sg.ker => ((z : centralizer ({π} : Set (Perm (Fin n)))) :
        Perm (Fin n))) hxy
      exact Subtype.ext (e.injective (Subtype.ext this))
    · rintro ⟨⟨g, hg⟩, hs⟩
      have hs' : sign g = 1 := hs
      refine ⟨⟨e.symm ⟨g, mem_alternatingGroup.2 hs'⟩, ?_⟩, ?_⟩
      · rw [show (e.symm ⟨g, mem_alternatingGroup.2 hs'⟩ ∈ autCentralizer τ) ↔
            τ (e.symm ⟨g, mem_alternatingGroup.2 hs'⟩) = e.symm ⟨g, mem_alternatingGroup.2 hs'⟩
            from Iff.rfl]
        rw [key]
        simpa using (Subgroup.mem_centralizer_singleton_iff.1 hg).symm
      · apply Subtype.ext
        apply Subtype.ext
        simp [f]
  have hrange : sg.range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact one_mem _
    · obtain ⟨t, ht, hs⟩ := Zassenhaus.Outer.exists_odd_mem_centralizer_perm π hsq hne
      exact ⟨⟨t, ht⟩, hs⟩
  have hunits : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_units_int
  have hker : Nat.card (centralizer ({π} : Set (Perm (Fin n)))) = Nat.card sg.ker * 2 := by
    rw [← Subgroup.card_mul_index sg.ker, Subgroup.index_ker, hrange, Subgroup.card_top, hunits]
  obtain ⟨a, ha1, ha2, hc⟩ := Zassenhaus.Outer.cycleType_eq_replicate_two π hsq hne
  refine ⟨π, hsq, hconj, a, ha1, ha2, hc, ?_⟩
  rw [← Zassenhaus.Outer.nat_card_centralizer_perm_two π ha1 hc, hker, hbij]
  ring

theorem alt_numeric_one {m r d : ℕ} (hm : Odd m) (hm7 : 7 ≤ m) (hr : 1 ≤ r) (hrm : 2 * r ≤ m)
    (hd : d = 2 ^ (r - 1) * r ! * (m - 2 * r)!) (h : d = 60 ∨ d = 120 ∨ d = 240) :
    m = 7 ∧ r = 1 ∧ d = 120 := by
  obtain ⟨k, hk⟩ := hm
  obtain ⟨f, hf⟩ : ∃ f, m = f + 2 * r := ⟨m - 2 * r, by omega⟩
  have hf' : m - 2 * r = f := by omega
  rw [hf'] at hd
  have hpos1 : 1 ≤ 2 ^ (r - 1) * r ! := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hpos2 : 1 ≤ f ! := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hdle : d ≤ 240 := by omega
  have hf5 : f ≤ 5 := by
    by_contra hh
    push Not at hh
    have h1 : 6 ! ≤ f ! := Nat.factorial_le hh
    have h2 : f ! * 1 ≤ f ! * (2 ^ (r - 1) * r !) := Nat.mul_le_mul_left _ hpos1
    have h6 : 6 ! = 720 := by decide
    rw [mul_comm (2 ^ (r - 1) * r !) (f !)] at hd
    rw [mul_one] at h2
    nlinarith
  have hr4 : r ≤ 4 := by
    by_contra hh
    push Not at hh
    have h1 : 5 ! ≤ r ! := Nat.factorial_le hh
    have h2 : 2 ^ 4 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 1 * 2 ^ 4 * 5 ! ≤ f ! * 2 ^ (r - 1) * r ! :=
      Nat.mul_le_mul (Nat.mul_le_mul hpos2 h2) h1
    have h5 : 5 ! = 120 := by decide
    rw [hd] at hdle
    have h4 : f ! * 2 ^ (r - 1) * r ! = 2 ^ (r - 1) * r ! * f ! := by ring
    omega
  interval_cases r <;> interval_cases f <;> simp only [Nat.factorial] at hd <;> omega

theorem alt_numeric_two {m r d : ℕ} (hm : Odd m) (hm7 : 7 ≤ m) (hr : 1 ≤ r) (hrm : 2 * r ≤ m)
    (hd : d = 2 ^ (r - 1) * r ! * (m - 2 * r)!) (h : d = 60 ∨ d = 120 ∨ d = 240 ∨ d = 480) :
    (m = 7 ∧ r = 1 ∧ d = 120) ∨ (m = 9 ∧ r = 2 ∧ d = 480) := by
  obtain ⟨k, hk⟩ := hm
  obtain ⟨f, hf⟩ : ∃ f, m = f + 2 * r := ⟨m - 2 * r, by omega⟩
  have hf' : m - 2 * r = f := by omega
  rw [hf'] at hd
  have hpos1 : 1 ≤ 2 ^ (r - 1) * r ! := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hpos2 : 1 ≤ f ! := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hdle : d ≤ 480 := by omega
  have hf5 : f ≤ 5 := by
    by_contra hh
    push Not at hh
    have h1 : 6 ! ≤ f ! := Nat.factorial_le hh
    have h2 : f ! * 1 ≤ f ! * (2 ^ (r - 1) * r !) := Nat.mul_le_mul_left _ hpos1
    have h6 : 6 ! = 720 := by decide
    rw [mul_comm (2 ^ (r - 1) * r !) (f !)] at hd
    rw [mul_one] at h2
    nlinarith
  have hr4 : r ≤ 4 := by
    by_contra hh
    push Not at hh
    have h1 : 5 ! ≤ r ! := Nat.factorial_le hh
    have h2 : 2 ^ 4 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 1 * 2 ^ 4 * 5 ! ≤ f ! * 2 ^ (r - 1) * r ! :=
      Nat.mul_le_mul (Nat.mul_le_mul hpos2 h2) h1
    have h5 : 5 ! = 120 := by decide
    rw [hd] at hdle
    have h4 : f ! * 2 ^ (r - 1) * r ! = 2 ^ (r - 1) * r ! * f ! := by ring
    omega
  interval_cases r <;> interval_cases f <;> simp only [Nat.factorial] at hd <;> omega

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
