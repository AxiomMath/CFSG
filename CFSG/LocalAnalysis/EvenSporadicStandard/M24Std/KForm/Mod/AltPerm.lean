module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup Equiv Equiv.Perm
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem cycleType_eq_replicate_two' {n : ℕ} (π : Perm (Fin n)) (h : π * π = 1)
    (h1 : π ≠ 1) :
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

private theorem nat_card_centralizer_perm_two' {n a : ℕ} (π : Perm (Fin n)) (ha : 1 ≤ a)
    (hc : π.cycleType = Multiset.replicate a 2) :
    Nat.card (centralizer ({π} : Set (Perm (Fin n)))) =
      (n - 2 * a).factorial * 2 ^ a * a.factorial := by
  rw [Equiv.Perm.nat_card_centralizer, hc, Fintype.card_fin, Multiset.sum_replicate,
    Multiset.prod_replicate, Multiset.toFinset_replicate]
  have ha0 : a ≠ 0 := by omega
  simp [ha0, mul_comm]

private theorem exists_odd_mem_centralizer_perm' {n : ℕ} (π : Perm (Fin n)) (h : π * π = 1)
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

theorem exists_perm_fixedSubgroup_alt {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 7 ≤ n)
    (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} (hσ : orderOf σ = 2) :
    ∃ (r : ℕ) (π : Perm (Fin n)), 1 ≤ r ∧ 2 * r ≤ n ∧ π.cycleType = Multiset.replicate r 2 ∧
      (∀ x : S, σ x = x ↔
        π * ((θ x : alternatingGroup (Fin n)) : Perm (Fin n)) =
          ((θ x : alternatingGroup (Fin n)) : Perm (Fin n)) * π) ∧
      Nat.card (fixedSubgroup σ) = 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial := by
  classical
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by decide)
  have hτsq : ∀ x : S, σ (σ x) = x := fun x => by
    have := congrArg (fun f : MulAut S => f x) hσ2
    simpa using this
  let τ' : MulAut (alternatingGroup (Fin n)) := θ.symm.trans ((σ : S ≃* S).trans θ)
  have hτ' : ∀ a, τ' a = θ (σ (θ.symm a)) := fun _ => rfl
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
    (by omega) (by omega)
  obtain ⟨π, hπ⟩ := hbij.2 τ'
  have hinj := hbij.1
  have hsq : π * π = 1 := by
    apply hinj
    rw [map_mul, hπ, map_one]
    ext a
    simp [hτ', hτsq]
  have hne : π ≠ 1 := by
    rintro rfl
    apply hσ1
    ext x
    have h3 : τ' (θ x) = θ x := by rw [← hπ]; simp
    rw [hτ'] at h3
    simpa using h3
  have key : ∀ x : S, σ x = x ↔
      π * ((θ x : alternatingGroup (Fin n)) : Perm (Fin n)) =
        ((θ x : alternatingGroup (Fin n)) : Perm (Fin n)) * π := by
    intro x
    have h1' : τ' (θ x) = θ (σ x) := by simp [hτ']
    constructor
    · intro hx
      have h3 : MulAut.conjNormal π (θ x) = θ x := by rw [hπ, h1', hx]
      have h4 := congrArg Subtype.val h3
      rw [MulAut.conjNormal_apply] at h4
      exact mul_inv_eq_iff_eq_mul.1 h4
    · intro h
      apply θ.injective
      rw [← h1', ← hπ]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, h, mul_assoc, mul_inv_cancel, mul_one]
  let sg : centralizer ({π} : Set (Perm (Fin n))) →* ℤˣ :=
    (sign : Perm (Fin n) →* ℤˣ).comp (centralizer ({π} : Set (Perm (Fin n)))).subtype
  have hbijcard : Nat.card (fixedSubgroup σ) = Nat.card sg.ker := by
    let f : fixedSubgroup σ → sg.ker := fun x =>
      ⟨⟨((θ x : alternatingGroup (Fin n)) : Perm (Fin n)),
        Subgroup.mem_centralizer_singleton_iff.2 ((key x).1 (show σ x = x from x.2)).symm⟩,
        mem_alternatingGroup.1 (θ x).2⟩
    refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
    · intro x y hxy
      have := congrArg (fun z : sg.ker => ((z : centralizer ({π} : Set (Perm (Fin n)))) :
        Perm (Fin n))) hxy
      exact Subtype.ext (θ.injective (Subtype.ext this))
    · rintro ⟨⟨g, hg⟩, hs⟩
      have hs' : sign g = 1 := hs
      refine ⟨⟨θ.symm ⟨g, mem_alternatingGroup.2 hs'⟩, ?_⟩, ?_⟩
      · refine (key (θ.symm ⟨g, mem_alternatingGroup.2 hs'⟩)).2 ?_
        simpa using (Subgroup.mem_centralizer_singleton_iff.1 hg).symm
      · apply Subtype.ext
        apply Subtype.ext
        simp [f]
  have hrange : sg.range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact one_mem _
    · obtain ⟨t, ht, hs⟩ := exists_odd_mem_centralizer_perm' π hsq hne
      exact ⟨⟨t, ht⟩, hs⟩
  have hunits : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_units_int
  have hker : Nat.card (centralizer ({π} : Set (Perm (Fin n)))) = Nat.card sg.ker * 2 := by
    rw [← Subgroup.card_mul_index sg.ker, Subgroup.index_ker, hrange, Subgroup.card_top, hunits]
  obtain ⟨a, ha1, ha2, hc⟩ := cycleType_eq_replicate_two' π hsq hne
  have hcard : 2 * Nat.card (fixedSubgroup σ) =
      (n - 2 * a).factorial * 2 ^ a * a.factorial := by
    rw [← nat_card_centralizer_perm_two' π ha1 hc, hker, hbijcard]
    ring
  refine ⟨a, π, ha1, ha2, hc, key, ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have h2 : 2 * Nat.card (fixedSubgroup σ) =
      2 * (2 ^ b * (b + 1).factorial * (n - 2 * (b + 1)).factorial) := by
    rw [hcard]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

private def alt9x0 : Perm (Fin 9) := List.formPerm [0, 1, 2, 3, 4, 5, 6]

private def alt9y0 : Perm (Fin 9) := alt9x0⁻¹ * (Equiv.swap 0 2 * Equiv.swap 1 3)

private lemma alt9x0_mul_alt9y0 :
    alt9x0 * alt9y0 = Equiv.swap 0 2 * Equiv.swap 1 3 := by
  rw [alt9y0]; group

private lemma alt9x0_order : orderOf alt9x0 = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime (p := 7) (by decide +kernel) (by decide +kernel)

private lemma alt9y0_order : orderOf alt9y0 = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime (p := 7) (by decide +kernel) (by decide +kernel)

private lemma alt9xy_order : orderOf (alt9x0 * alt9y0) = 2 := by
  rw [alt9x0_mul_alt9y0]
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact orderOf_eq_prime (p := 2) (by decide +kernel) (by decide +kernel)

private lemma alt9x0_sign : sign alt9x0 = 1 := by decide +kernel

private lemma alt9y0_sign : sign alt9y0 = 1 := by decide +kernel

private lemma alt9x0_comm : alt9x0 * Equiv.swap (7 : Fin 9) 8 =
    Equiv.swap (7 : Fin 9) 8 * alt9x0 := by decide +kernel

private lemma alt9y0_comm : alt9y0 * Equiv.swap (7 : Fin 9) 8 =
    Equiv.swap (7 : Fin 9) 8 * alt9y0 := by decide +kernel

theorem alt9_seven_pair {S : Type} [Group S] [Finite S] (θ : S ≃* alternatingGroup (Fin 9))
    {σ : MulAut S} {π : Perm (Fin 9)} (hπ : π.cycleType = Multiset.replicate 1 2)
    (hkey : ∀ x : S, σ x = x ↔
      π * ((θ x : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
        ((θ x : alternatingGroup (Fin 9)) : Perm (Fin 9)) * π) :
    ∃ x y : ↥(fixedSubgroup σ), orderOf x = 7 ∧ orderOf y = 7 ∧ orderOf (x * y) = 2 := by
  classical
  have hswap : (Equiv.swap (7 : Fin 9) 8).cycleType = Multiset.replicate 1 2 := by
    rw [Multiset.replicate_one]
    exact isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide))
  have hconj : IsConj (Equiv.swap (7 : Fin 9) 8) π :=
    isConj_iff_cycleType_eq.mpr (by rw [hswap, hπ])
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let x₁ : Perm (Fin 9) := MulAut.conj g alt9x0
  let y₁ : Perm (Fin 9) := MulAut.conj g alt9y0
  have hπg : π = MulAut.conj g (Equiv.swap (7 : Fin 9) 8) := by
    rw [MulAut.conj_apply, ← hg]
  have hx1_comm : π * x₁ = x₁ * π := by
    rw [hπg]
    change MulAut.conj g (Equiv.swap (7 : Fin 9) 8) * MulAut.conj g alt9x0 =
      MulAut.conj g alt9x0 * MulAut.conj g (Equiv.swap (7 : Fin 9) 8)
    rw [← map_mul, ← map_mul, alt9x0_comm]
  have hy1_comm : π * y₁ = y₁ * π := by
    rw [hπg]
    change MulAut.conj g (Equiv.swap (7 : Fin 9) 8) * MulAut.conj g alt9y0 =
      MulAut.conj g alt9y0 * MulAut.conj g (Equiv.swap (7 : Fin 9) 8)
    rw [← map_mul, ← map_mul, alt9y0_comm]
  have hx1_even : sign x₁ = 1 := by
    change sign (MulAut.conj g alt9x0) = 1
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, alt9x0_sign]
    group
  have hy1_even : sign y₁ = 1 := by
    change sign (MulAut.conj g alt9y0) = 1
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, alt9y0_sign]
    group
  have hx1_order : orderOf x₁ = 7 := by
    change orderOf (MulAut.conj g alt9x0) = 7
    rw [MulEquiv.orderOf_eq, alt9x0_order]
  have hy1_order : orderOf y₁ = 7 := by
    change orderOf (MulAut.conj g alt9y0) = 7
    rw [MulEquiv.orderOf_eq, alt9y0_order]
  have hxy1 : x₁ * y₁ = MulAut.conj g (alt9x0 * alt9y0) := by
    change MulAut.conj g alt9x0 * MulAut.conj g alt9y0 =
      MulAut.conj g (alt9x0 * alt9y0)
    rw [← map_mul]
  have hxy_order : orderOf (x₁ * y₁) = 2 := by
    rw [hxy1, MulEquiv.orderOf_eq, alt9xy_order]
  let xS : S := θ.symm ⟨x₁, mem_alternatingGroup.mpr hx1_even⟩
  have hxS : xS ∈ fixedSubgroup σ := (hkey xS).2 (by simpa [xS] using hx1_comm)
  let yS : S := θ.symm ⟨y₁, mem_alternatingGroup.mpr hy1_even⟩
  have hyS : yS ∈ fixedSubgroup σ := (hkey yS).2 (by simpa [yS] using hy1_comm)
  have hxS_order : orderOf (⟨xS, hxS⟩ : fixedSubgroup σ) = 7 := by
    rw [Subgroup.orderOf_mk]
    change orderOf (θ.symm ⟨x₁, mem_alternatingGroup.mpr hx1_even⟩) = 7
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx1_order]
  have hyS_order : orderOf (⟨yS, hyS⟩ : fixedSubgroup σ) = 7 := by
    rw [Subgroup.orderOf_mk]
    change orderOf (θ.symm ⟨y₁, mem_alternatingGroup.mpr hy1_even⟩) = 7
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy1_order]
  have hxyS_order : orderOf ((⟨xS, hxS⟩ : fixedSubgroup σ) * ⟨yS, hyS⟩) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨xS, hxS⟩ * ⟨yS, hyS⟩), Subgroup.coe_mul]
    change orderOf (θ.symm ⟨x₁, mem_alternatingGroup.mpr hx1_even⟩ *
      θ.symm ⟨y₁, mem_alternatingGroup.mpr hy1_even⟩) = 2
    rw [← map_mul, MulEquiv.orderOf_eq]
    rw [← Subgroup.orderOf_coe (⟨x₁, mem_alternatingGroup.mpr hx1_even⟩ *
      ⟨y₁, mem_alternatingGroup.mpr hy1_even⟩), Subgroup.coe_mul]
    exact hxy_order
  exact ⟨⟨xS, hxS⟩, ⟨yS, hyS⟩, hxS_order, hyS_order, hxyS_order⟩

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
