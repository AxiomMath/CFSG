module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Equiv Equiv.Perm Nat

theorem cycleType_eq_replicate_two {n : ℕ} (π : Perm (Fin n)) (h : π * π = 1) (h1 : π ≠ 1) :
    ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ n ∧ π.cycleType = Multiset.replicate a 2 := by
  have ho : orderOf π = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact h) h1
  have hmem : ∀ b ∈ π.cycleType, b = 2 := fun b hb =>
    Nat.le_antisymm (Nat.le_of_dvd (by norm_num) (ho ▸ Equiv.Perm.dvd_of_mem_cycleType hb))
      (Equiv.Perm.two_le_of_mem_cycleType hb)
  have hrep := Multiset.eq_replicate_of_mem hmem
  have hs := Equiv.Perm.sum_cycleType_le π
  generalize Multiset.card π.cycleType = a at hrep
  rw [hrep, Multiset.sum_replicate, Fintype.card_fin] at hs
  refine ⟨a, ?_, by simpa [mul_comm] using hs, hrep⟩
  rw [Nat.one_le_iff_ne_zero]
  rintro rfl
  exact h1 (Equiv.Perm.cycleType_eq_zero.1 hrep)

theorem nat_card_centralizer_perm_two {n a : ℕ} (π : Perm (Fin n)) (ha : 1 ≤ a)
    (hc : π.cycleType = Multiset.replicate a 2) :
    Nat.card (centralizer ({π} : Set (Perm (Fin n)))) = (n - 2 * a)! * 2 ^ a * a ! := by
  rw [Equiv.Perm.nat_card_centralizer, hc, Fintype.card_fin, Multiset.sum_replicate,
    Multiset.prod_replicate, Multiset.toFinset_replicate]
  have ha0 : a ≠ 0 := by omega
  simp [ha0, mul_comm]

theorem exists_odd_mem_centralizer_perm {n : ℕ} (π : Perm (Fin n)) (h : π * π = 1)
    (h1 : π ≠ 1) :
    ∃ t ∈ centralizer ({π} : Set (Perm (Fin n))), sign t = -1 := by
  obtain ⟨x, hx⟩ : ∃ x, π x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact h1 (Equiv.ext hcon)
  refine ⟨swap x (π x), ?_, Equiv.Perm.sign_swap hx.symm⟩
  rw [Subgroup.mem_centralizer_singleton_iff, mul_swap_eq_swap_mul]
  have hpp : π (π x) = x := by
    have := congrArg (fun f : Perm (Fin n) => f x) h
    simpa using this
  rw [hpp, swap_comm]

theorem card_autCentralizer_alt {K : Type} [Group K] (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : K ≃* alternatingGroup (Fin n)) (τ : MulAut K) (h2 : τ * τ = 1) (h1 : τ ≠ 1) :
    ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ n ∧
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
    · obtain ⟨t, ht, hs⟩ := exists_odd_mem_centralizer_perm π hsq hne
      exact ⟨⟨t, ht⟩, hs⟩
  have hunits : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_units_int
  have hker : Nat.card (centralizer ({π} : Set (Perm (Fin n)))) = Nat.card sg.ker * 2 := by
    rw [← Subgroup.card_mul_index sg.ker, Subgroup.index_ker, hrange, Subgroup.card_top, hunits]
  obtain ⟨a, ha1, ha2, hc⟩ := cycleType_eq_replicate_two π hsq hne
  refine ⟨a, ha1, ha2, ?_⟩
  rw [← nat_card_centralizer_perm_two π ha1 hc, hker, hbij]
  ring

theorem alt_numeric {m a c : ℕ} (ha : 1 ≤ a) (han : 2 * a ≤ 2 * m)
    (h2c : 2 * c = (2 * m - 2 * a)! * 2 ^ a * a !) (hdvd : 20160 ∣ c) (hle : c ≤ 161280) :
    (m = 5 ∨ m = 6) ∧ (c ≤ 80640 → m = 5) := by
  obtain ⟨f, hf⟩ : ∃ f, 2 * m = f + 2 * a := ⟨2 * m - 2 * a, by omega⟩
  have hf' : 2 * m - 2 * a = f := by omega
  rw [hf'] at h2c
  have hpos : 1 ≤ 2 ^ a * a ! := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hf9 : f ≤ 9 := by
    by_contra hh
    push Not at hh
    have h1 : 10 ! ≤ f ! := Nat.factorial_le hh
    have h2 : f ! * 1 ≤ f ! * (2 ^ a * a !) := Nat.mul_le_mul_left _ hpos
    rw [← mul_assoc] at h2
    have h10 : 10 ! = 3628800 := by decide
    omega
  have ha6 : a ≤ 6 := by
    by_contra hh
    push Not at hh
    have h1 : 7 ! ≤ a ! := Nat.factorial_le hh
    have h2 : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hh
    have h3 : 1 ≤ f ! := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h4 : 1 * 2 ^ 7 * 7 ! ≤ f ! * 2 ^ a * a ! :=
      Nat.mul_le_mul (Nat.mul_le_mul h3 h2) h1
    have h7 : 7 ! = 5040 := by decide
    omega
  interval_cases a <;> interval_cases f <;> simp only [Nat.factorial] at h2c <;> omega

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
