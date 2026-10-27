module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeKernelData
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3Torus
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Chevalley.ExceptionalCover (cartanCoord)

section Exponent

variable {L : Type} [Field L]

@[expose] def e6Dg (ζ : Lˣ) (q m : ℕ) : Fin 3 → Lˣ := ![ζ ^ m, ζ ^ (m * q), ζ ^ (m * q ^ 2)]

@[expose] def e6KerChar (ζ : Lˣ) (q x y : ℕ) : Fin Tag.E6.rank → Lˣ :=
  e6A2TorusChar 0 (e6Dg ζ q x) * e6A2TorusChar 1 (e6Dg ζ q y)

@[expose] def e6KerExp (q x y : ℤ) (v : Fin Tag.E6.rank → ℤ) : ℤ :=
  x * (e6KerP 0 v + q * e6KerQ 0 v) + y * (e6KerP 1 v + q * e6KerQ 1 v)

theorem e6A2TorusChar_Dg (ζ : Lˣ) (q m : ℕ) (i : Fin 3) (k : Fin Tag.E6.rank) :
    e6A2TorusChar i (e6Dg ζ q m) k = ζ ^ ((m : ℤ) * (cartanCoord (τ := Tag.E6) (e6A2Simple₀ i) k +
      cartanCoord (τ := Tag.E6) (e6A2Simple₁ i) k) +
        (m : ℤ) * q * cartanCoord (τ := Tag.E6) (e6A2Simple₁ i) k) := by
  simp only [e6A2TorusChar, e6Dg, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← zpow_natCast ζ m, ← zpow_natCast ζ (m * q), ← zpow_mul, ← zpow_mul, ← zpow_add]
  push_cast
  rfl

theorem rootChar_e6KerChar (ζ : Lˣ) (q x y : ℕ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (e6KerChar ζ q x y) v = ζ ^ e6KerExp q x y v := by
  have hprod : ∀ (s : Finset (Fin Tag.E6.rank)) (f : Fin Tag.E6.rank → ℤ),
      ∏ i ∈ s, ζ ^ f i = ζ ^ ∑ i ∈ s, f i := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  have hpair : ∀ u : Fin Tag.E6.rank → ℤ, e6Pair u v =
      ∑ k, cartanCoord (τ := Tag.E6) u k * v k := fun u => by
    simp only [e6Pair, cartanCoord, mul_comm]
  simp only [rootChar, e6KerChar, Pi.mul_apply, e6A2TorusChar_Dg, ← zpow_add, ← zpow_mul]
  rw [hprod]
  congr 1
  simp only [e6KerExp, e6KerP, e6KerQ, hpair, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Exponent

section Cube

theorem omega_sq {p q : ℕ} (hq : p ∣ q ^ 2 + q + 1) :
    ((q : ZMod p)) ^ 2 + (q : ZMod p) + 1 = 0 := by
  have := (ZMod.natCast_eq_zero_iff (q ^ 2 + q + 1) p).2 hq
  push_cast at this
  exact this

theorem omega_cube {p q : ℕ} (hq : p ∣ q ^ 2 + q + 1) : ((q : ZMod p)) ^ 3 = 1 := by
  linear_combination ((q : ZMod p) - 1) * omega_sq hq

theorem omega_ne_zero {p q : ℕ} (hp : p.Prime) (hq : p ∣ q ^ 2 + q + 1) : (q : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  intro h
  have := omega_sq hq
  rw [h] at this
  simp at this

theorem three_ne_zero {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h')

theorem blockVal_ne_zero {p q : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hq : p ∣ q ^ 2 + q + 1)
    {z : ℤ × ℤ} (hz : e6BlockVal z) : (z.1 : ZMod p) + (q : ZMod p) * (z.2 : ZMod p) ≠ 0 := by
  have h3 := three_ne_zero hp hp3
  have hω := omega_sq hq
  rcases z with ⟨a, b⟩
  simp only [e6BlockVal, Prod.mk.injEq] at hz
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    intro h <;> push_cast at h
  · exact h3 (by linear_combination hω - ((q : ZMod p) - 1) * h)
  · exact h3 (by linear_combination 4 * hω - (2 * (q : ZMod p) + 1) * h)
  · exact h3 (by linear_combination hω + ((q : ZMod p) + 2) * h)
  · exact h3 (by linear_combination hω + ((q : ZMod p) - 1) * h)
  · exact h3 (by linear_combination 4 * hω + (2 * (q : ZMod p) + 1) * h)
  · exact h3 (by linear_combination hω - ((q : ZMod p) + 2) * h)

theorem eig_cast {p q : ℕ} (hq : p ∣ q ^ 2 + q + 1) {z : ℤ × ℤ} {σ : Bool} {j : Fin 3}
    (h : e6Eig z = some (σ, j)) :
    (z.1 : ZMod p) + (q : ZMod p) * (z.2 : ZMod p) =
      (if σ then 1 else -1) * (q : ZMod p) ^ (j : ℕ) := by
  have hω := omega_sq hq
  rcases z with ⟨a, b⟩
  unfold e6Eig at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    push_cast
    simp
    linear_combination (-1 : ZMod p) * hω
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Prod.mk.injEq] at h4
    obtain ⟨rfl, rfl⟩ := h4
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Prod.mk.injEq] at h6
    obtain ⟨rfl, rfl⟩ := h6
    push_cast
    simp
    linear_combination hω

theorem omega_ne_one {p q : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hq : p ∣ q ^ 2 + q + 1) :
    (q : ZMod p) ≠ 1 := by
  intro h
  have := omega_sq hq
  rw [h] at this
  exact three_ne_zero hp hp3 (by linear_combination this)

theorem omega_pow_inj {p q : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hq : p ∣ q ^ 2 + q + 1)
    {s t : Fin 3} (h : (q : ZMod p) ^ (s : ℕ) = (q : ZMod p) ^ (t : ℕ)) : s = t := by
  have h3 := three_ne_zero hp hp3
  have hω := omega_sq hq
  have h0 := omega_ne_zero hp hq
  have h1 := omega_ne_one hp hp3 hq
  have hne01 : (1 : ZMod p) ≠ (q : ZMod p) := fun h' => h1 h'.symm
  have hne02 : (1 : ZMod p) ≠ (q : ZMod p) ^ 2 := fun h' =>
    h3 (by linear_combination (1 - (q : ZMod p)) * h' - ((q : ZMod p) - 2) * hω)
  have hne12 : (q : ZMod p) ≠ (q : ZMod p) ^ 2 := fun h' => by
    have hm : (q : ZMod p) * ((q : ZMod p) - 1) = 0 := by linear_combination (-1 : ZMod p) * h'
    have : Fact p.Prime := ⟨hp⟩
    rcases mul_eq_zero.1 hm with h'' | h''
    · exact h0 h''
    · exact h1 (sub_eq_zero.1 h'')
  obtain ⟨s, hs⟩ := s
  obtain ⟨t, ht⟩ := t
  interval_cases s <;> interval_cases t <;>
    first
    | rfl
    | (simp only [pow_zero, pow_one] at h
       first
       | exact absurd h hne01 | exact absurd h.symm hne01
       | exact absurd h hne02 | exact absurd h.symm hne02
       | exact absurd h hne12 | exact absurd h.symm hne12)

theorem omega_pow_sub {p q : ℕ} (hq : p ∣ q ^ 2 + q + 1) (j k : Fin 3) :
    (q : ZMod p) ^ (j : ℕ) = (q : ZMod p) ^ (k : ℕ) * (q : ZMod p) ^ ((j - k : Fin 3) : ℕ) := by
  have h3 := omega_cube hq
  fin_cases j <;> fin_cases k <;> simp only [Fin.val_sub] <;> norm_num <;>
    first
    | ring1
    | linear_combination (-1 : ZMod p) * h3
    | linear_combination h3
    | linear_combination (q : ZMod p) * h3
    | linear_combination (-(q : ZMod p)) * h3

@[expose] def kerVal {p : ℕ} (q x y : ZMod p) (z w : ℤ × ℤ) : ZMod p :=
  x * ((z.1 : ZMod p) + q * (z.2 : ZMod p)) + y * ((w.1 : ZMod p) + q * (w.2 : ZMod p))

theorem kerVal_zero {p : ℕ} (q x y : ZMod p) : kerVal q x y (0, 0) (0, 0) = 0 := by
  simp [kerVal]

theorem kerVal_block0 {p q : ℕ} {z : ℤ × ℤ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hq : p ∣ q ^ 2 + q + 1) (x y : ZMod p) (hz : e6BlockVal z) :
    kerVal (q : ZMod p) x y z (0, 0) = 0 ↔ x = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hA := blockVal_ne_zero hp hp3 hq hz
  simp only [kerVal, Int.cast_zero, mul_zero, add_zero]
  rw [mul_eq_zero]
  exact ⟨fun h => h.resolve_right hA, Or.inl⟩

theorem kerVal_block1 {p q : ℕ} {w : ℤ × ℤ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hq : p ∣ q ^ 2 + q + 1) (x y : ZMod p) (hw : e6BlockVal w) :
    kerVal (q : ZMod p) x y (0, 0) w = 0 ↔ y = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hB := blockVal_ne_zero hp hp3 hq hw
  simp only [kerVal, Int.cast_zero, mul_zero, add_zero, zero_add]
  rw [mul_eq_zero]
  exact ⟨fun h => h.resolve_right hB, Or.inl⟩

theorem kerVal_eig {p q : ℕ} {z w : ℤ × ℤ} {σ : Bool} {j k : Fin 3} (hp : p.Prime)
    (hq : p ∣ q ^ 2 + q + 1) (x y : ZMod p) (hz : e6Eig z = some (σ, j))
    (hw : e6Eig w = some (!σ, k)) :
    kerVal (q : ZMod p) x y z w = 0 ↔ y = x * (q : ZMod p) ^ ((j - k : Fin 3) : ℕ) := by
  have hj := omega_pow_sub hq j k
  have hA := eig_cast hq hz
  have hB := eig_cast hq hw
  have key : kerVal (q : ZMod p) x y z w =
      (if σ then 1 else -1) * (q : ZMod p) ^ (k : ℕ) *
        (x * (q : ZMod p) ^ ((j - k : Fin 3) : ℕ) - y) := by
    unfold kerVal
    rw [hA, hB, hj]
    cases σ <;> simp <;> ring
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hne : (if σ then (1 : ZMod p) else -1) * (q : ZMod p) ^ (k : ℕ) ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero _ (omega_ne_zero hp hq))
    have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
    cases σ
    · exact neg_ne_zero.2 h1
    · exact h1
  rw [key, mul_eq_zero, sub_eq_zero]
  constructor
  · intro h
    exact (h.resolve_left hne).symm
  · intro h
    exact Or.inr h.symm

end Cube

section Kernel

variable {L : Type} [Field L]

theorem mem_rootCharKernel_e6KerChar_iff {ζ : Lˣ} {p q x y : ℕ} (hζ : orderOf ζ = p)
    (v : Fin Tag.E6.rank → ℤ) :
    v ∈ rootCharKernel (e6KerChar ζ q x y) ↔ IsRoot .E6 v ∧
      (x : ZMod p) * ((e6KerP 0 v : ZMod p) + (q : ZMod p) * (e6KerQ 0 v : ZMod p)) +
        (y : ZMod p) * ((e6KerP 1 v : ZMod p) + (q : ZMod p) * (e6KerQ 1 v : ZMod p)) = 0 := by
  refine and_congr_right fun _ => ?_
  rw [rootChar_e6KerChar, ← orderOf_dvd_iff_zpow_eq_one, hζ, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [e6KerExp]
  push_cast
  rfl

end Kernel

section Main

variable {L : Type} [Field L] {ζ : Lˣ} {p q x y : ℕ}

theorem mem_kernel_kerVal (hζ : orderOf ζ = p) (v : Fin Tag.E6.rank → ℤ) :
    v ∈ rootCharKernel (e6KerChar ζ q x y) ↔ IsRoot .E6 v ∧
      kerVal (q : ZMod p) (x : ZMod p) (y : ZMod p) (e6KerP 0 v, e6KerQ 0 v)
        (e6KerP 1 v, e6KerQ 1 v) = 0 :=
  mem_rootCharKernel_e6KerChar_iff hζ v

theorem mem_e6BlockRoots (i : Fin 3) (v : Fin Tag.E6.rank → ℤ) :
    v ∈ e6BlockRoots i ↔ IsRoot .E6 v ∧ ∃ a b : Fin 3, a ≠ b ∧ v = e6A2Root i a b := by
  simp [e6BlockRoots, e6BlockRootsF, mem_rootFinset]

theorem mem_e6MixedRoots (s : Fin 3) (v : Fin Tag.E6.rank → ℤ) :
    v ∈ e6MixedRoots s ↔ IsRoot .E6 v ∧ ∃ σ : Bool, ∃ j k : Fin 3,
      e6Eig (e6KerP 0 v, e6KerQ 0 v) = some (σ, j) ∧
        e6Eig (e6KerP 1 v, e6KerQ 1 v) = some (!σ, k) ∧ j - k = s := by
  simp [e6MixedRoots, e6MixedRootsF, mem_rootFinset]

theorem rootCharKernel_e6KerChar_block12 (hp : p.Prime) (hp3 : p ≠ 3) (hζ : orderOf ζ = p)
    (hq : p ∣ q ^ 2 + q + 1) (hx : ¬ p ∣ x) (hy : p ∣ y) :
    rootCharKernel (e6KerChar ζ q x y) = e6BlockRoots 1 ∪ e6BlockRoots 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx0 : (x : ZMod p) ≠ 0 := fun h => hx ((ZMod.natCast_eq_zero_iff x p).1 h)
  have hy0 : (y : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff y p).2 hy
  ext v
  rw [mem_kernel_kerVal hζ, Set.mem_union, mem_e6BlockRoots, mem_e6BlockRoots]
  constructor
  · rintro ⟨hv, hk⟩
    have hv' := mem_rootFinset.2 hv
    rcases e6_root_kinds v hv' with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩ | ⟨σ, j, k, h4a, h4b⟩
    · exact Or.inr ⟨hv, (e6_block2_iff v hv').2 h1⟩
    · rw [h2b] at hk
      exact (hx0 ((kerVal_block0 hp hp3 hq _ _ h2a).1 hk)).elim
    · exact Or.inl ⟨hv, (e6_block1_iff v hv').2 ⟨h3a, h3b⟩⟩
    · have := (kerVal_eig hp hq _ _ h4a h4b).1 hk
      rw [hy0] at this
      exact (hx0 ((mul_eq_zero.1 this.symm).resolve_right (pow_ne_zero _ (omega_ne_zero hp hq)))).elim
  · rintro (⟨hv, hb⟩ | ⟨hv, hb⟩)
    · obtain ⟨h3a, h3b⟩ := (e6_block1_iff v (mem_rootFinset.2 hv)).1 hb
      refine ⟨hv, ?_⟩
      rw [h3a]
      exact (kerVal_block1 hp hp3 hq _ _ h3b).2 hy0
    · obtain ⟨h1a, h1b⟩ := (e6_block2_iff v (mem_rootFinset.2 hv)).1 hb
      refine ⟨hv, ?_⟩
      rw [h1a, h1b]
      exact kerVal_zero _ _ _

theorem rootCharKernel_e6KerChar_block02 (hp : p.Prime) (hp3 : p ≠ 3) (hζ : orderOf ζ = p)
    (hq : p ∣ q ^ 2 + q + 1) (hx : p ∣ x) (hy : ¬ p ∣ y) :
    rootCharKernel (e6KerChar ζ q x y) = e6BlockRoots 0 ∪ e6BlockRoots 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx0 : (x : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff x p).2 hx
  have hy0 : (y : ZMod p) ≠ 0 := fun h => hy ((ZMod.natCast_eq_zero_iff y p).1 h)
  ext v
  rw [mem_kernel_kerVal hζ, Set.mem_union, mem_e6BlockRoots, mem_e6BlockRoots]
  constructor
  · rintro ⟨hv, hk⟩
    have hv' := mem_rootFinset.2 hv
    rcases e6_root_kinds v hv' with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩ | ⟨σ, j, k, h4a, h4b⟩
    · exact Or.inr ⟨hv, (e6_block2_iff v hv').2 h1⟩
    · exact Or.inl ⟨hv, (e6_block0_iff v hv').2 ⟨h2a, h2b⟩⟩
    · rw [h3a] at hk
      exact (hy0 ((kerVal_block1 hp hp3 hq _ _ h3b).1 hk)).elim
    · have := (kerVal_eig hp hq _ _ h4a h4b).1 hk
      rw [hx0, zero_mul] at this
      exact (hy0 this).elim
  · rintro (⟨hv, hb⟩ | ⟨hv, hb⟩)
    · obtain ⟨h2a, h2b⟩ := (e6_block0_iff v (mem_rootFinset.2 hv)).1 hb
      refine ⟨hv, ?_⟩
      rw [h2b]
      exact (kerVal_block0 hp hp3 hq _ _ h2a).2 hx0
    · obtain ⟨h1a, h1b⟩ := (e6_block2_iff v (mem_rootFinset.2 hv)).1 hb
      refine ⟨hv, ?_⟩
      rw [h1a, h1b]
      exact kerVal_zero _ _ _

theorem rootCharKernel_e6KerChar_mixed (hp : p.Prime) (hp3 : p ≠ 3) (hζ : orderOf ζ = p)
    (hq : p ∣ q ^ 2 + q + 1) (hx : ¬ p ∣ x) {s : Fin 3}
    (hs : (y : ZMod p) = (x : ZMod p) * (q : ZMod p) ^ (s : ℕ)) :
    rootCharKernel (e6KerChar ζ q x y) = e6BlockRoots 2 ∪ e6MixedRoots s := by
  have : Fact p.Prime := ⟨hp⟩
  have hx0 : (x : ZMod p) ≠ 0 := fun h => hx ((ZMod.natCast_eq_zero_iff x p).1 h)
  have hω := omega_ne_zero hp hq
  ext v
  rw [mem_kernel_kerVal hζ, Set.mem_union, mem_e6BlockRoots, mem_e6MixedRoots]
  constructor
  · rintro ⟨hv, hk⟩
    have hv' := mem_rootFinset.2 hv
    rcases e6_root_kinds v hv' with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩ | ⟨σ, j, k, h4a, h4b⟩
    · exact Or.inl ⟨hv, (e6_block2_iff v hv').2 h1⟩
    · rw [h2b] at hk
      exact (hx0 ((kerVal_block0 hp hp3 hq _ _ h2a).1 hk)).elim
    · rw [h3a] at hk
      have := (kerVal_block1 hp hp3 hq _ _ h3b).1 hk
      rw [this] at hs
      exact (hx0 ((mul_eq_zero.1 hs.symm).resolve_right (pow_ne_zero _ hω))).elim
    · have h := (kerVal_eig hp hq _ _ h4a h4b).1 hk
      rw [hs] at h
      have h' := mul_left_cancel₀ hx0 h
      have hjk : j - k = s := omega_pow_inj hp hp3 hq h'.symm
      exact Or.inr ⟨hv, σ, j, k, h4a, h4b, hjk⟩
  · rintro (⟨hv, hb⟩ | ⟨hv, σ, j, k, h4a, h4b, hjk⟩)
    · obtain ⟨h1a, h1b⟩ := (e6_block2_iff v (mem_rootFinset.2 hv)).1 hb
      refine ⟨hv, ?_⟩
      rw [h1a, h1b]
      exact kerVal_zero _ _ _
    · refine ⟨hv, (kerVal_eig hp hq _ _ h4a h4b).2 ?_⟩
      rw [hjk]
      exact hs

theorem rootCharKernel_e6KerChar_block2 (hp : p.Prime) (hp3 : p ≠ 3) (hζ : orderOf ζ = p)
    (hq : p ∣ q ^ 2 + q + 1) (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (hs : ∀ s : Fin 3, (y : ZMod p) ≠ (x : ZMod p) * (q : ZMod p) ^ (s : ℕ)) :
    rootCharKernel (e6KerChar ζ q x y) = e6BlockRoots 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx0 : (x : ZMod p) ≠ 0 := fun h => hx ((ZMod.natCast_eq_zero_iff x p).1 h)
  have hy0 : (y : ZMod p) ≠ 0 := fun h => hy ((ZMod.natCast_eq_zero_iff y p).1 h)
  ext v
  rw [mem_kernel_kerVal hζ, mem_e6BlockRoots]
  constructor
  · rintro ⟨hv, hk⟩
    have hv' := mem_rootFinset.2 hv
    rcases e6_root_kinds v hv' with h1 | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩ | ⟨σ, j, k, h4a, h4b⟩
    · exact ⟨hv, (e6_block2_iff v hv').2 h1⟩
    · rw [h2b] at hk
      exact (hx0 ((kerVal_block0 hp hp3 hq _ _ h2a).1 hk)).elim
    · rw [h3a] at hk
      exact (hy0 ((kerVal_block1 hp hp3 hq _ _ h3b).1 hk)).elim
    · exact ((hs (j - k)) ((kerVal_eig hp hq _ _ h4a h4b).1 hk)).elim
  · rintro ⟨hv, hb⟩
    obtain ⟨h1a, h1b⟩ := (e6_block2_iff v (mem_rootFinset.2 hv)).1 hb
    refine ⟨hv, ?_⟩
    rw [h1a, h1b]
    exact kerVal_zero _ _ _

end Main

end CFSG.HardMathSupport.Malle.SeitzCube
