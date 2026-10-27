module

public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.Timmesfeld.Orders.ExceptionalWeyl

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TD4Le

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld.ExceptionalOrders

variable {K : Type} [Field K]

abbrev nd (i : ℕ) (h : i < 4 := by decide) : Fin TwistTag.D4.tag.rank := ⟨i, h⟩

theorem perm_zero : TwistTag.D4.perm (nd 0) = nd 1 := by decide

theorem perm_one : TwistTag.D4.perm (nd 1) = nd 3 := by decide

theorem fin_cases_D4 (i : Fin TwistTag.D4.tag.rank) :
    i = nd 0 ∨ i = nd 1 ∨ i = nd 2 ∨ i = nd 3 := by
  revert i
  decide

theorem rootChar_D4 (a : Fin TwistTag.D4.tag.rank → Kˣ)
    (hρ : ∀ i, a (TwistTag.D4.perm i) = a i)
    (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar a v = a (nd 0) ^ (v (nd 0) + v (nd 1) + v (nd 3)) * a (nd 2) ^ v (nd 2) := by
  have h1 : a (nd 1) = a (nd 0) := by
    have := hρ (nd 0)
    rwa [perm_zero] at this
  have h3 : a (nd 3) = a (nd 0) := by
    have := hρ (nd 1)
    rwa [perm_one, h1] at this
  have : rootChar a v = a (nd 0) ^ v (nd 0) * a (nd 1) ^ v (nd 1) * a (nd 2) ^ v (nd 2) *
      a (nd 3) ^ v (nd 3) := by
    unfold rootChar
    exact Fin.prod_univ_four (fun i => a i ^ v i)
  rw [this, h1, h3, zpow_add, zpow_add]
  ac_rfl

theorem exists_primitive (l m : Kˣ) (hl : l ^ 3 = 1) (hm : m ^ 3 = 1) (h : ¬ (l = 1 ∧ m = 1)) :
    ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ∃ x y : ℕ, x < 3 ∧ y < 3 ∧ (x ≠ 0 ∨ y ≠ 0) ∧
      l = ω ^ x ∧ m = ω ^ y := by
  by_cases hl1 : l = 1
  · have hm1 : m ≠ 1 := fun hm1 => h ⟨hl1, hm1⟩
    exact ⟨m, hm, hm1, 0, 1, by norm_num, by norm_num, Or.inr (by norm_num), by simp [hl1],
      by simp⟩
  · refine ⟨l, hl, hl1, 1, ?_⟩
    have hlK : (l : K) ^ 3 = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) hl
      simpa using this
    have hl1K : (l : K) ≠ 1 := fun h1 => hl1 (Units.ext h1)
    have hmK : (m : K) ^ 3 = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) hm
      simpa using this
    have hs : (l : K) ^ 2 + (l : K) + 1 = 0 := by
      have h0 : ((l : K) - 1) * ((l : K) ^ 2 + (l : K) + 1) = 0 := by linear_combination hlK
      rcases mul_eq_zero.1 h0 with h1 | h1
      · exact absurd (sub_eq_zero.1 h1) hl1K
      · exact h1
    have hprod : ((m : K) - 1) * ((m : K) - l) * ((m : K) - (l : K) ^ 2) = 0 := by
      linear_combination hmK + (-(m : K) ^ 2 + (m : K)) * hs + ((m : K) - 1) * hlK
    have hcases : m = 1 ∨ m = l ∨ m = l ^ 2 := by
      rcases mul_eq_zero.1 hprod with h1 | h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact Or.inl (Units.ext (sub_eq_zero.1 h2))
        · exact Or.inr (Or.inl (Units.ext (sub_eq_zero.1 h2)))
      · exact Or.inr (Or.inr (Units.ext (by simpa using sub_eq_zero.1 h1)))
    rcases hcases with h1 | h1 | h1
    · exact ⟨0, by norm_num, by norm_num, Or.inl (by norm_num), by simp, by simp [h1]⟩
    · exact ⟨1, by norm_num, by norm_num, Or.inl (by norm_num), by simp, by simp [h1]⟩
    · exact ⟨2, by norm_num, by norm_num, Or.inl (by norm_num), by simp, h1⟩

theorem eq_of_perm_invariant (a : Fin TwistTag.D4.tag.rank → Kˣ)
    (hρ : ∀ i, a (TwistTag.D4.perm i) = a i) :
    a (nd 1) = a (nd 0) ∧ a (nd 3) = a (nd 0) := by
  have h1 : a (nd 1) = a (nd 0) := by
    have := hρ (nd 0)
    rwa [perm_zero] at this
  refine ⟨h1, ?_⟩
  have := hρ (nd 1)
  rwa [perm_one, h1] at this

theorem rootChar_D4_eq_one_iff {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (a : Fin TwistTag.D4.tag.rank → Kˣ) (hρ : ∀ i, a (TwistTag.D4.perm i) = a i) {x y : ℕ}
    (hl : a (nd 0) = ω ^ x) (hm : a (nd 2) = ω ^ y) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar a v = 1 ↔
      ((x : ℤ) * (v (nd 0) + v (nd 1) + v (nd 3)) + (y : ℤ) * v (nd 2)) % 3 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [rootChar_D4 a hρ v, hl, hm]
  have e : (ω ^ x) ^ (v (nd 0) + v (nd 1) + v (nd 3)) * (ω ^ y) ^ v (nd 2) =
      ω ^ ((x : ℤ) * (v (nd 0) + v (nd 1) + v (nd 3)) + (y : ℤ) * v (nd 2)) := by
    rw [← zpow_natCast ω x, ← zpow_natCast ω y, ← zpow_mul, ← zpow_mul, ← zpow_add]
  rw [e, ← orderOf_dvd_iff_zpow_eq_one, orderOf_eq_prime hω3 hω1]
  push_cast
  exact Int.dvd_iff_emod_eq_zero

theorem count_roots : ∀ x y : Fin 3, (x ≠ 0 ∨ y ≠ 0) →
    (rootList TwistTag.D4.tag).countP (fun v => decide
      ((((x : ℕ) : ℤ) * (v (nd 0) + v (nd 1) + v (nd 3)) + ((y : ℕ) : ℤ) * v (nd 2)) % 3 = 0 ∧
        0 < height v)) = 3 := by
  decide +kernel

theorem ncard_posKernel (a : Fin TwistTag.D4.tag.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1)
    (hρ : ∀ i, a (TwistTag.D4.perm i) = a i) (h1 : a ≠ 1) :
    (rootCharKernel a ∩ {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α}).ncard = 3 := by
  classical
  obtain ⟨hb1, hb3⟩ := eq_of_perm_invariant a hρ
  have hnot : ¬ (a (nd 0) = 1 ∧ a (nd 2) = 1) := by
    rintro ⟨h0, h2⟩
    apply h1
    funext i
    rcases fin_cases_D4 i with rfl | rfl | rfl | rfl
    · exact h0
    · rw [hb1, h0]; rfl
    · exact h2
    · rw [hb3, h0]; rfl
  obtain ⟨ω, hω3, hω1, x, y, hx, hy, hxy, hl, hm⟩ :=
    exists_primitive (a (nd 0)) (a (nd 2)) (h3 _) (h3 _) hnot
  have hset : (rootCharKernel a ∩ {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α}) =
      {v | IsRoot TwistTag.D4.tag v ∧
        ((((x : ℤ) * (v (nd 0) + v (nd 1) + v (nd 3)) + (y : ℤ) * v (nd 2)) % 3 = 0 ∧
          0 < height v))} := by
    ext v
    simp only [rootCharKernel, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [rootChar_D4_eq_one_iff hω3 hω1 a hρ hl hm v]
    tauto
  rw [hset, ncard_setOf_isRoot_and]
  have hne : (⟨x, hx⟩ : Fin 3) ≠ 0 ∨ (⟨y, hy⟩ : Fin 3) ≠ 0 := by
    rcases hxy with h | h
    · exact Or.inl fun hh => h (by simpa [Fin.ext_iff] using hh)
    · exact Or.inr fun hh => h (by simpa [Fin.ext_iff] using hh)
  exact count_roots ⟨x, hx⟩ ⟨y, hy⟩ hne

theorem height_permLattice' (π : Equiv.Perm (Fin TwistTag.D4.tag.rank))
    (v : Fin TwistTag.D4.tag.rank → ℤ) : height (permLattice π v) = height v := by
  simp only [height, permLattice, Function.comp_apply]
  exact Equiv.sum_comp π.symm v

theorem posKernel_perm (a : Fin TwistTag.D4.tag.rank → Kˣ)
    (hρ : ∀ i, a (TwistTag.D4.perm i) = a i) :
    ∀ α ∈ rootCharKernel a ∩ {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α},
      permLattice TwistTag.D4.perm α ∈
        rootCharKernel a ∩ {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α} := by
  rintro α ⟨⟨hroot, hchar⟩, -, hpos⟩
  have hroot' : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm α) :=
    hroot.permLattice TwistTag.D4.cartan_perm
  have hrc : rootChar a (permLattice TwistTag.D4.perm α) = rootChar a α := by
    unfold rootChar permLattice
    rw [← Equiv.prod_comp TwistTag.D4.perm (fun i => a i ^ (α ∘ TwistTag.D4.perm.symm) i)]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [hρ j]
  exact ⟨⟨hroot', by rw [hrc]; exact hchar⟩, hroot', by rw [height_permLattice']; exact hpos⟩

theorem rootChar_nsmul (a : Fin TwistTag.D4.tag.rank → Kˣ) (m : ℕ)
    (v : Fin TwistTag.D4.tag.rank → ℤ) : rootChar a (m • v) = rootChar a v ^ m := by
  rw [← natCast_zsmul, rootChar_zsmul, zpow_natCast]

theorem height_add_nsmul (m n : ℕ) (α β : Fin TwistTag.D4.tag.rank → ℤ) :
    height (m • α + n • β) = m * height α + n * height β := by
  simp [height, Finset.sum_add_distrib, Finset.mul_sum]

theorem posKernel_closed (a : Fin TwistTag.D4.tag.rank → Kˣ) :
    ∀ α ∈ rootCharKernel a ∩ {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α},
      ∀ β ∈ rootCharKernel a ∩ {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α},
        ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot TwistTag.D4.tag (m • α + n • β) →
          m • α + n • β ∈
            rootCharKernel a ∩ {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α} := by
  rintro α ⟨⟨-, hα⟩, -, hαpos⟩ β ⟨⟨-, hβ⟩, -, hβpos⟩ m n hm hn hroot
  refine ⟨⟨hroot, ?_⟩, hroot, ?_⟩
  · rw [rootChar_add, rootChar_nsmul, rootChar_nsmul, hα, hβ]
    simp
  · rw [height_add_nsmul]
    have h1 : (0 : ℤ) < m := by exact_mod_cast hm
    have h2 : (0 : ℤ) < n := by exact_mod_cast hn
    positivity

end CFSG.LocalAnalysis.GLTheoremA.TD4Le

end
