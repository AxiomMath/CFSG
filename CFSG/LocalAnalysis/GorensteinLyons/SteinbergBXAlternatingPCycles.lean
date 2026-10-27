module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCentralLift
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXPermCycles
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Equiv Equiv.Perm Subgroup

variable {n : ℕ}

theorem exists_alternating_conj_pow_four {c : Perm (Fin n)} (hc : c.IsCycle)
    (hodd : Odd (orderOf c)) :
    ∃ g : alternatingGroup (Fin n), (g : Perm (Fin n)) * c * (g : Perm (Fin n))⁻¹ = c ^ 4 ∧
      ∀ x ∉ c.support, (g : Perm (Fin n)) x = x := by
  obtain ⟨h, hh, hfix⟩ := exists_conj_pow_support hc (m := 2) (Nat.coprime_two_left.mpr hodd)
  have hmem : h ^ 2 ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, map_pow, Int.units_sq]
  refine ⟨⟨h ^ 2, hmem⟩, ?_, fun x hx => ?_⟩
  · calc h ^ 2 * c * (h ^ 2)⁻¹ = h * (h * c * h⁻¹) * h⁻¹ := by
          rw [pow_two, mul_inv_rev]; group
      _ = h * c ^ 2 * h⁻¹ := by rw [hh]
      _ = (h * c * h⁻¹) ^ 2 := by rw [conj_pow]
      _ = c ^ 4 := by rw [hh, ← pow_mul]
  · change (h ^ 2) x = x
    rw [pow_two, Perm.mul_apply, hfix x hx, hfix x hx]

theorem commute_of_coe_commute {G : Subgroup (Perm (Fin n))} {a b : G}
    (h : Commute (a : Perm (Fin n)) (b : Perm (Fin n))) : Commute a b :=
  Subtype.ext h.eq

theorem alternating_central_cover_injective_disjoint_p_cycles {p k : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (_hk : 1 ≤ k) (_hn : k * p ≤ n) {K : Type*} [Group K] [Finite K]
    (π : K →* alternatingGroup (Fin n)) (hπ : Function.Surjective π) (hZ : π.ker ≤ center K)
    (Ω : Fin k → Finset (Fin n)) (hΩ : ∀ i, (Ω i).card = p)
    (hdisj : Pairwise fun i j => Disjoint (Ω i) (Ω j)) (c : Fin k → alternatingGroup (Fin n))
    (hc : ∀ i, (c i : Perm (Fin n)).IsCycle ∧ (c i : Perm (Fin n)).support = Ω i) :
    ∃ v : Fin k → K, (∀ i j, Commute (v i) (v j)) ∧ (∀ i, orderOf (v i) = p) ∧
      (∀ i, π (v i) = c i) ∧ CFSG.IsElementaryAbelian p (closure (Set.range v)) ∧
      Nat.card (closure (Set.range v)) = p ^ k ∧ Set.InjOn π (closure (Set.range v)) ∧
      (closure (Set.range v)).map π = closure (Set.range c) ∧
      closure (Set.range v) ⊓ π.ker = ⊥ ∧
      (k * p + 4 ≤ n → ∃ u : K, orderOf u = 2 ∧ ∀ i, Commute u (v i)) := by
  have hp2 : p ≠ 2 := by omega
  have hordp : ∀ i, orderOf (c i : Perm (Fin n)) = p := fun i => by
    rw [(hc i).1.orderOf, (hc i).2, hΩ i]
  have hord : ∀ i, orderOf (c i) = p := fun i => by rw [← orderOf_coe, hordp]
  have hcp : ∀ i, c i ^ p = 1 := fun i => hord i ▸ pow_orderOf_eq_one (c i)
  have hc1 : ∀ i, c i ≠ 1 := fun i h => by
    have := hord i
    rw [h, orderOf_one] at this
    omega
  have hsupp : ∀ i, ∀ x ∉ Ω i, (c i : Perm (Fin n)) x = x := fun i x hx =>
    notMem_support.mp ((hc i).2 ▸ hx)
  have hcomm : ∀ i j, Commute (c i) (c j) := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · exact commute_of_coe_commute (commute_of_apply_eq_self (hdisj hij) (hsupp i) (hsupp j))
  have hind : iSupIndep fun i => zpowers (c i) :=
    iSupIndep_zpowers_of_apply_eq_self (alternatingGroup (Fin n)).subtype Subtype.val_injective
      c Ω hdisj hsupp
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hg : ∀ i, ∃ g : alternatingGroup (Fin n), g * c i * g⁻¹ = c i ^ (4 : ℤ) ∧
      ∀ x ∉ Ω i, (g : Perm (Fin n)) x = x := by
    intro i
    obtain ⟨g, hg, hgfix⟩ := exists_alternating_conj_pow_four (hc i).1 (hordp i ▸ hodd)
    refine ⟨g, Subtype.ext ?_, fun x hx => hgfix x ((hc i).2 ▸ hx)⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, zpow_ofNat, Subgroup.coe_pow] using hg
  have hp3 : ∀ m : ℤ, (m = 3 ∨ m = -3) → ¬ (p : ℤ) ∣ m := by
    rintro m (rfl | rfl) h
    · have : p ∣ 3 := by exact_mod_cast h
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · have : p ∣ 3 := by exact_mod_cast (dvd_neg.mp h)
      have := Nat.le_of_dvd (by norm_num) this
      omega
  have hinv : ∀ i, ∃ g : alternatingGroup (Fin n), ∃ a : ℤ, ¬ (p : ℤ) ∣ 1 - a ∧
      g * c i * g⁻¹ = c i ^ a := by
    intro i
    obtain ⟨g, hgc, -⟩ := hg i
    exact ⟨g, 4, hp3 _ (Or.inr (by norm_num)), hgc⟩
  have hpair : ∀ i j, i ≠ j → ∃ g : alternatingGroup (Fin n),
      (∃ a b : ℤ, ¬ (p : ℤ) ∣ a * b - 1 ∧ g * c i * g⁻¹ = c i ^ a ∧ g * c j * g⁻¹ = c j ^ b) ∨
        (g * c i * g⁻¹ = c j ∧ g * c j * g⁻¹ = c i) := by
    intro i j hij
    obtain ⟨g, hgc, hgfix⟩ := hg i
    have hgj : Commute g (c j) :=
      commute_of_coe_commute (commute_of_apply_eq_self (hdisj hij) hgfix (hsupp j))
    refine ⟨g, Or.inl ⟨4, 1, hp3 _ (Or.inl (by norm_num)), hgc, ?_⟩⟩
    rw [hgj.eq, mul_inv_cancel_right, zpow_one]
  obtain ⟨v, hvc, hvo, hvcomm, hEA, hcard, hinj, hmap, -⟩ :=
    exists_lift_of_weyl hp2 π hπ hZ c hcp hc1 hcomm hind hinv hpair
  rw [Fintype.card_fin] at hcard
  refine ⟨v, hvcomm, hvo, hvc, hEA, hcard, hinj, hmap, ?_, fun hn4 => ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    exact hinj (mem_inf.mp hx).1 (one_mem _) (by rw [MonoidHom.mem_ker.mp (mem_inf.mp hx).2,
      map_one])
  set B := Finset.univ.biUnion Ω with hB
  have hBcard : B.card = k * p := by
    rw [hB, Finset.card_biUnion (fun i _ j _ hij => hdisj hij)]
    simp [hΩ]
  have hRcard : 4 ≤ (Finset.univ \ B).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      hBcard]
    omega
  obtain ⟨T, hTR, hT4⟩ := Finset.exists_subset_card_eq hRcard
  let e := T.equivFinOfCardEq hT4
  set a : Fin n := (e.symm 0 : Fin n)
  set b : Fin n := (e.symm 1 : Fin n)
  set c' : Fin n := (e.symm 2 : Fin n)
  set d : Fin n := (e.symm 3 : Fin n)
  have hne : ∀ x y : Fin 4, x ≠ y → (e.symm x : Fin n) ≠ e.symm y := fun x y hxy h =>
    hxy (e.symm.injective (Subtype.ext h))
  have hab : a ≠ b := hne 0 1 (by decide)
  have hac : a ≠ c' := hne 0 2 (by decide)
  have had : a ≠ d := hne 0 3 (by decide)
  have hbc : b ≠ c' := hne 1 2 (by decide)
  have hbd : b ≠ d := hne 1 3 (by decide)
  have hcd : c' ≠ d := hne 2 3 (by decide)
  have hout : ∀ x : Fin 4, ∀ i, (e.symm x : Fin n) ∉ Ω i := by
    intro x i hx
    have := hTR (e.symm x).2
    rw [Finset.mem_sdiff, hB, Finset.mem_biUnion] at this
    exact this.2 ⟨i, Finset.mem_univ _, hx⟩
  set s : Perm (Fin n) := swap a b * swap c' d with hs
  have hss : Commute (swap a b) (swap c' d) := by
    refine commute_of_apply_eq_self (s := {a, b}) (t := {c', d}) ?_ ?_ ?_
    · simp [Finset.disjoint_left, hac, had, hbc, hbd]
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      exact swap_apply_of_ne_of_ne hx.1 hx.2
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      exact swap_apply_of_ne_of_ne hx.1 hx.2
  have hsmem : s ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, hs, map_mul, sign_swap hab, sign_swap hcd]
    decide
  have hsfix : ∀ x, x ≠ a → x ≠ b → x ≠ c' → x ≠ d → s x = x := by
    intro x h1 h2 h3 h4
    rw [hs, Perm.mul_apply, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]
  have hs1 : (⟨s, hsmem⟩ : alternatingGroup (Fin n)) ≠ 1 := by
    intro h
    have h' : s a = a := by
      have := congrArg (fun g : alternatingGroup (Fin n) => (g : Perm (Fin n)) a) h
      simpa using this
    rw [hs, Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left] at h'
    exact hab h'.symm
  have hs2 : (⟨s, hsmem⟩ : alternatingGroup (Fin n)) ^ 2 = 1 := by
    apply Subtype.ext
    change s ^ 2 = 1
    rw [hs, hss.mul_pow, pow_two, pow_two, swap_mul_self, swap_mul_self, one_mul]
  have hsc : ∀ i, Commute (⟨s, hsmem⟩ : alternatingGroup (Fin n)) (π (v i)) := by
    intro i
    rw [hvc i]
    refine commute_of_coe_commute (commute_of_apply_eq_self (s := T) (t := Ω i) ?_ ?_ (hsupp i))
    · rw [Finset.disjoint_left]
      intro x hxT hxΩ
      exact hout (e ⟨x, hxT⟩) i (by simpa using hxΩ)
    · intro x hx
      have hxT : ∀ y : Fin 4, (e.symm y : Fin n) ≠ x := fun y h => hx (h ▸ (e.symm y).2)
      exact hsfix x (hxT 0).symm (hxT 1).symm (hxT 2).symm (hxT 3).symm
  exact exists_involution_commute hp2 π hπ hZ v (fun i => hvo i ▸ pow_orderOf_eq_one (v i))
    hs1 hs2 hsc

end CFSG.LocalAnalysis.GorensteinLyons
