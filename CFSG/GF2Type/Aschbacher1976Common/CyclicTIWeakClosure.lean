module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCConjugate

public section

namespace CFSG.GF2Type.Aschbacher1976Common

open Subgroup CFSG CFSG.LocalAnalysis.GorensteinLyons

variable {G : Type*} [Group G] [Finite G]

private theorem ti_conjugate_inf (X Y : Subgroup G) (g : G) :
    conjugate (X ⊓ Y) g = conjugate X g ⊓ conjugate Y g := by
  ext x
  simp only [Subgroup.mem_inf, mem_conjugate_iff_conj_mem]

private theorem ti_conjugate_bot (g : G) : conjugate (⊥ : Subgroup G) g = ⊥ := by
  ext x
  simp only [mem_conjugate_iff_conj_mem, Subgroup.mem_bot]
  constructor
  · intro h
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, h]
    group
  · intro h
    rw [h]
    group

private theorem ti_conjugate_pair {A : Subgroup G}
    (hTI : ∀ g : G, conjugate A g = A ∨ A ⊓ conjugate A g = ⊥) (x y : G) :
    conjugate A x = conjugate A y ∨ conjugate A x ⊓ conjugate A y = ⊥ := by
  rcases hTI (x * y⁻¹) with h | h
  · left
    calc conjugate A x = conjugate (conjugate A (x * y⁻¹)) y := by
          rw [conjugate_conjugate, inv_mul_cancel_right]
      _ = conjugate A y := by rw [h]
  · right
    have h2 : conjugate (A ⊓ conjugate A (x * y⁻¹)) y = conjugate ⊥ y := by rw [h]
    rw [ti_conjugate_inf, conjugate_conjugate, inv_mul_cancel_right, ti_conjugate_bot] at h2
    rw [inf_comm]
    exact h2

theorem commute_of_mem_conjugate_of_mem_normalizer {A : Subgroup G} (hA : IsCyclic A)
    (hA2 : IsPGroup 2 A) (hTI : ∀ g : G, conjugate A g = A ∨ A ⊓ conjugate A g = ⊥) {g k : G}
    (hne : conjugate A g ≠ A) (hk : k ∈ conjugate A g) (hkN : k ∈ normalizer (A : Set G))
    (hk2 : k ^ 2 ≠ 1) :
    ∀ a ∈ A, a * k = k * a := by
  intro a ha
  have hcomm : ∀ x y : A, x * y = y * x := by
    intro x y
    letI := IsCyclic.commGroup (α := ↥A)
    exact mul_comm x y
  have hN : ∀ x : G, x ∈ A ↔ k * x * k⁻¹ ∈ A := fun x => mem_normalizer_iff.mp hkN x
  have hinv : ∀ x : G, k⁻¹ * x * k ∈ A ↔ x ∈ A := by
    intro x
    rw [hN (k⁻¹ * x * k), show k * (k⁻¹ * x * k) * k⁻¹ = x by group]
  have hαA : ∀ x ∈ A, k⁻¹ * x * k ∈ A := fun x hx => (hinv x).mpr hx
  let α : A →* A :=
    { toFun := fun x => ⟨k⁻¹ * (x : G) * k, hαA _ x.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; simp only [Subgroup.coe_mul]; group }
  have hαval : ∀ x : A, ((α x : A) : G) = k⁻¹ * (x : G) * k := fun x => rfl
  by_contra hne'
  have hfix : ∃ x : A, α x ≠ x := by
    refine ⟨⟨a, ha⟩, fun h => hne' ?_⟩
    have h1 : k⁻¹ * a * k = a := by
      have := congrArg Subtype.val h
      rw [hαval] at this
      exact this
    calc a * k = k * (k⁻¹ * a * k) := by group
      _ = k * a := by rw [h1]
  obtain ⟨x, hx⟩ := hfix
  have hy1 : x⁻¹ * α x ≠ 1 := fun h => hx (inv_mul_eq_one.mp h).symm
  have hdvd : 2 ∣ orderOf (x⁻¹ * α x) := hA2.dvd_orderOf hy1
  have hord_ne : orderOf (x⁻¹ * α x) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨m, hm⟩ : ∃ m, m = orderOf (x⁻¹ * α x) / 2 := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : A, z = (x⁻¹ * α x) ^ m := ⟨_, rfl⟩
  have hzord : orderOf z = 2 := by
    rw [hzdef, hm]
    exact orderOf_pow_orderOf_div hord_ne hdvd
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzord] at this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    norm_num at hzord
  have hcx : Commute x⁻¹ (α x) := hcomm _ _
  have hzeq : z = (x ^ m)⁻¹ * α (x ^ m) := by
    rw [hzdef, hcx.mul_pow, inv_pow, ← map_pow]
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : G, a₀ = ((x ^ m : A) : G) := ⟨_, rfl⟩
  have ha₀A : a₀ ∈ A := by
    rw [ha₀]
    exact (x ^ m).2
  have hzG : (z : G) = a₀⁻¹ * (k⁻¹ * a₀ * k) := by
    have h := congrArg Subtype.val hzeq
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hαval, ← ha₀] at h
    exact h
  have hαa0 : k⁻¹ * a₀ * k = a₀ * (z : G) := by
    rw [hzG]
    group
  have hzG2 : (z : G) ^ 2 = 1 := by
    have := congrArg Subtype.val hz2
    simpa using this
  have hzG1 : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hαz : α z = z := by
    apply eq_of_orderOf_eq_two_of_isCyclic _ hzord
    apply orderOf_eq_prime
    · rw [← map_pow, hz2, map_one]
    · intro h
      apply hzG1
      have h' := congrArg Subtype.val h
      rw [hαval] at h'
      calc (z : G) = k * (k⁻¹ * (z : G) * k) * k⁻¹ := by group
        _ = 1 := by rw [h']; simp
  have hαzG : k⁻¹ * (z : G) * k = (z : G) := by
    have h := congrArg Subtype.val hαz
    rw [hαval] at h
    exact h
  have hα2 : k⁻¹ * (k⁻¹ * a₀ * k) * k = a₀ := by
    calc k⁻¹ * (k⁻¹ * a₀ * k) * k = k⁻¹ * (a₀ * (z : G)) * k := by rw [hαa0]
      _ = (k⁻¹ * a₀ * k) * (k⁻¹ * (z : G) * k) := by group
      _ = (a₀ * (z : G)) * (z : G) := by rw [hαa0, hαzG]
      _ = a₀ * ((z : G) * (z : G)) := by rw [mul_assoc]
      _ = a₀ := by rw [← sq, hzG2, mul_one]
  have hcomm2 : a₀ * (k * k) = (k * k) * a₀ := by
    have h1 : (k * k) * (k⁻¹ * (k⁻¹ * a₀ * k) * k) = a₀ * (k * k) := by group
    rw [hα2] at h1
    exact h1.symm
  have hαne : k⁻¹ * a₀ * k ≠ a₀ := by
    intro h
    apply hzG1
    have h' : a₀ * (z : G) = a₀ := by rw [← hαa0, h]
    calc (z : G) = a₀⁻¹ * (a₀ * (z : G)) := by group
      _ = 1 := by rw [h']; group
  have hkk : k * k ∈ conjugate A g := mul_mem hk hk
  have hkk1 : k * k ≠ 1 := fun h => hk2 (by rw [sq]; exact h)
  have hcon : a₀ * (k * k) * a₀⁻¹ = k * k := by
    rw [hcomm2, mul_inv_cancel_right]
  have hmemk : k * k ∈ conjugate (conjugate A g) a₀ := by
    rw [mem_conjugate_iff_conj_mem, hcon]
    exact hkk
  have hconjB : conjugate (conjugate A g) a₀ = conjugate A g := by
    rcases ti_conjugate_pair hTI g (g * a₀) with h | h
    · rw [conjugate_conjugate]
      exact h.symm
    · exfalso
      have hm1 : k * k ∈ conjugate A g ⊓ conjugate A (g * a₀) := by
        refine Subgroup.mem_inf.mpr ⟨hkk, ?_⟩
        rw [← conjugate_conjugate]
        exact hmemk
      rw [h] at hm1
      exact hkk1 (Subgroup.mem_bot.mp hm1)
  have hbot : A ⊓ conjugate A g = ⊥ := (hTI g).resolve_left hne
  have hw : ∀ w : G, w ∈ conjugate A g ↔ a₀ * w * a₀⁻¹ ∈ conjugate A g := by
    intro w
    rw [← mem_conjugate_iff_conj_mem, hconjB]
  have hwB : a₀⁻¹ * k⁻¹ * a₀ ∈ conjugate A g := by
    rw [hw, show a₀ * (a₀⁻¹ * k⁻¹ * a₀) * a₀⁻¹ = k⁻¹ by group]
    exact inv_mem hk
  have hcA : a₀⁻¹ * k⁻¹ * a₀ * k ∈ A := by
    rw [show a₀⁻¹ * k⁻¹ * a₀ * k = a₀⁻¹ * (k⁻¹ * a₀ * k) by group]
    exact mul_mem (inv_mem ha₀A) (hαA _ ha₀A)
  have hcB : a₀⁻¹ * k⁻¹ * a₀ * k ∈ conjugate A g := mul_mem hwB hk
  have hc1 : a₀⁻¹ * k⁻¹ * a₀ * k = 1 := by
    have hmem : a₀⁻¹ * k⁻¹ * a₀ * k ∈ A ⊓ conjugate A g := Subgroup.mem_inf.mpr ⟨hcA, hcB⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hfin : k⁻¹ * a₀ * k = a₀ := by
    calc k⁻¹ * a₀ * k = a₀ * (a₀⁻¹ * k⁻¹ * a₀ * k) := by group
      _ = a₀ := by rw [hc1, mul_one]
  exact hαne hfin

theorem conjugate_inv_le_normalizer {A : Subgroup G} (hA : IsCyclic A) (hA2 : IsPGroup 2 A)
    (hTI : ∀ g : G, conjugate A g = A ∨ A ⊓ conjugate A g = ⊥) {g k : G}
    (hne : conjugate A g ≠ A) (hk : k ∈ conjugate A g) (hkN : k ∈ normalizer (A : Set G))
    (hk2 : k ^ 2 ≠ 1) :
    conjugate A g⁻¹ ≤ normalizer (A : Set G) := by
  have hcomm_k : ∀ b ∈ A, b * k = k * b :=
    commute_of_mem_conjugate_of_mem_normalizer hA hA2 hTI hne hk hkN hk2
  have hkk : k * k ∈ conjugate A g := mul_mem hk hk
  have hkk1 : k * k ≠ 1 := fun h => hk2 (by rw [sq]; exact h)
  have hB : ∀ b ∈ A, conjugate (conjugate A g) b = conjugate A g := by
    intro b hb
    have hcb : Commute b k := hcomm_k b hb
    have h2 : b * (k * k) = k * k * b := (hcb.mul_right hcb).eq
    have hmemk : k * k ∈ conjugate (conjugate A g) b := by
      rw [mem_conjugate_iff_conj_mem, show b * (k * k) * b⁻¹ = k * k by
        rw [h2, mul_inv_cancel_right]]
      exact hkk
    rcases ti_conjugate_pair hTI g (g * b) with h | h
    · rw [conjugate_conjugate]
      exact h.symm
    · exfalso
      have hm1 : k * k ∈ conjugate A g ⊓ conjugate A (g * b) := by
        refine Subgroup.mem_inf.mpr ⟨hkk, ?_⟩
        rw [← conjugate_conjugate]
        exact hmemk
      rw [h] at hm1
      exact hkk1 (Subgroup.mem_bot.mp hm1)
  intro x hx
  have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ A := mem_conjugate_iff_conj_mem.mp hx
  obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, x = g * a * g⁻¹ :=
    ⟨g⁻¹ * x * g⁻¹⁻¹, hx', by group⟩
  rw [mem_normalizer_iff_conjugate_eq]
  calc conjugate A (g * a * g⁻¹) = conjugate (conjugate A g) (a * g⁻¹) := by
        rw [conjugate_conjugate, mul_assoc]
    _ = conjugate (conjugate (conjugate A g) a) g⁻¹ := (conjugate_conjugate _ a g⁻¹).symm
    _ = conjugate (conjugate A g) g⁻¹ := by rw [hB a ha]
    _ = conjugate A (g * g⁻¹) := conjugate_conjugate A g g⁻¹
    _ = A := by
        rw [mul_inv_cancel]
        exact (mem_normalizer_iff_conjugate_eq (H := A) (g := 1)).mp (one_mem _)

end CFSG.GF2Type.Aschbacher1976Common
