module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

variable {Ĝ G : Type*} [Group Ĝ] [Group G]

@[expose] def IsPElt (p : ℕ) (x : Ĝ) : Prop := ∃ k : ℕ, x ^ (p ^ k) = 1

theorem IsPElt.one (p : ℕ) : IsPElt p (1 : Ĝ) := ⟨0, one_pow _⟩

theorem IsPElt.inv {p : ℕ} {x : Ĝ} (h : IsPElt p x) : IsPElt p x⁻¹ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [inv_pow, hk, inv_one]⟩

theorem IsPElt.conj {p : ℕ} {x : Ĝ} (h : IsPElt p x) (g : Ĝ) : IsPElt p (g * x * g⁻¹) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [conj_pow, hk]; simp⟩

theorem IsPElt.conj' {p : ℕ} {x : Ĝ} (hx : IsPElt p x) (g : Ĝ) : IsPElt p (g⁻¹ * x * g) := by
  have := hx.conj g⁻¹
  rwa [inv_inv] at this

theorem IsPElt.map {p : ℕ} {x : Ĝ} (h : IsPElt p x) (π : Ĝ →* G) : IsPElt p (π x) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

structure IsCentralCover (π : Ĝ →* G) (p : ℕ) : Prop where
  surj : Function.Surjective π
  ker_le : π.ker ≤ Subgroup.center Ĝ
  coprime : Nat.Coprime (Nat.card π.ker) p

variable {π : Ĝ →* G} {p : ℕ}

theorem IsCentralCover.eq_one_of_isPElt [Finite Ĝ] (h : IsCentralCover π p) {z : Ĝ}
    (hz : z ∈ π.ker) (hp : IsPElt p z) : z = 1 := by
  obtain ⟨k, hk⟩ := hp
  have h1 : orderOf z ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf z ∣ Nat.card π.ker := by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : π.ker)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : Nat.Coprime (Nat.card π.ker) (p ^ k) := h.coprime.pow_right k
  have h4 : orderOf z = 1 :=
    Nat.eq_one_of_dvd_coprimes h3 h2 h1
  exact orderOf_eq_one_iff.1 h4

section Closure

variable [Finite Ĝ] [hp : Fact p.Prime]

theorem IsCentralCover.isPElt_mul (h : IsCentralCover π p) {P : Subgroup G}
    (hP : IsPGroup p P) {x y : Ĝ} (hx : π x ∈ P) (hy : π y ∈ P) (hx' : IsPElt p x)
    (hy' : IsPElt p y) : IsPElt p (x * y) := by
  set M : Subgroup Ĝ := P.comap π with hM
  have hxM : x ∈ M := hx
  have hyM : y ∈ M := hy
  have : Finite G := Finite.of_surjective π h.surj
  let f : ↥M →* ↥P := (π.comp M.subtype).codRestrict P fun m => m.2
  have hnil : Group.IsNilpotent ↥M := by
    have : Group.IsNilpotent ↥P := hP.isNilpotent
    refine Subgroup.isNilpotent_of_ker_le_center f ?_
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro g
    have hm1 : π (m : Ĝ) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hm)
    have hc := Subgroup.mem_center_iff.1 (h.ker_le hm1) (g : Ĝ)
    exact Subtype.ext hc
  have := hnil
  have hsyl : ∀ z : ↥M, IsPElt p (z : Ĝ) → ∀ S : Sylow p ↥M, z ∈ (S : Subgroup ↥M) := by
    intro z hz S
    obtain ⟨k, hk⟩ := hz
    have hz' : IsPGroup p (Subgroup.zpowers z) := by
      rintro ⟨g, hg⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      refine ⟨k, Subtype.ext ?_⟩
      have hk' : z ^ (p ^ k) = 1 := Subtype.ext hk
      show (z ^ n) ^ (p ^ k) = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk', one_zpow]
    obtain ⟨Q, hQ⟩ := hz'.exists_le_sylow
    have hQS : Q = S := by
      have := Sylow.unique_of_normal Q inferInstance
      exact Subsingleton.elim _ _
    exact hQS ▸ hQ (Subgroup.mem_zpowers z)
  let S : Sylow p ↥M := default
  have hxS := hsyl ⟨x, hxM⟩ hx' S
  have hyS := hsyl ⟨y, hyM⟩ hy' S
  have hmul := mul_mem hxS hyS
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨_, hmul⟩
  exact ⟨k, by simpa using congrArg Subtype.val (congrArg Subtype.val hk)⟩

end Closure

section PLift

variable [Finite Ĝ] [Fact p.Prime]

@[expose] def pLift (h : IsCentralCover π p) (P : Subgroup G) (hP : IsPGroup p P) :
    Subgroup Ĝ where
  carrier := {x | π x ∈ P ∧ IsPElt p x}
  one_mem' := ⟨by rw [map_one]; exact one_mem _, IsPElt.one p⟩
  mul_mem' := fun {x y} hx hy => ⟨by rw [map_mul]; exact mul_mem hx.1 hy.1,
    h.isPElt_mul hP hx.1 hy.1 hx.2 hy.2⟩
  inv_mem' := fun {x} hx => ⟨by rw [map_inv]; exact inv_mem hx.1, hx.2.inv⟩

variable (h : IsCentralCover π p) {P : Subgroup G} (hP : IsPGroup p P)

theorem pLift_isPGroup : IsPGroup p (pLift h P hP) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, hk⟩ := hx.2
  exact ⟨k, Subtype.ext hk⟩

variable {h hP}

theorem pLift_inj {P : Subgroup G} {hP : IsPGroup p P} {x y : Ĝ} (hx : x ∈ pLift h P hP)
    (hy : y ∈ pLift h P hP) (hxy : π x = π y) : x = y := by
  have hz : x * y⁻¹ ∈ pLift h P hP := mul_mem hx (inv_mem hy)
  have hker : x * y⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  have := h.eq_one_of_isPElt hker hz.2
  exact mul_inv_eq_one.1 this

theorem exists_pLift {P : Subgroup G} {hP : IsPGroup p P} {g : G} (hg : g ∈ P) :
    ∃ x ∈ pLift h P hP, π x = g := by
  obtain ⟨x₀, rfl⟩ := h.surj g
  obtain ⟨k, hk⟩ := hP ⟨π x₀, hg⟩
  have hk' : (π x₀) ^ (p ^ k) = 1 := congrArg Subtype.val hk
  set m := Nat.card π.ker with hm
  have hcop : Nat.Coprime m (p ^ k) := h.coprime.pow_right k
  obtain ⟨j, hj1, hj0⟩ := Nat.chineseRemainder hcop.symm 1 0
  have hmj : m ∣ j := (Nat.modEq_zero_iff_dvd).1 hj0
  have hπj : (π x₀) ^ j = π x₀ := by
    rw [pow_eq_pow_mod j hk', hj1, ← pow_eq_pow_mod 1 hk', pow_one]
  refine ⟨x₀ ^ j, ⟨?_, ?_⟩, ?_⟩
  · rw [map_pow, hπj]
    exact hg
  · refine ⟨k, ?_⟩
    obtain ⟨t, ht⟩ := hmj
    have hz : (x₀ ^ (p ^ k)) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, hk']
    have hzm : (x₀ ^ (p ^ k)) ^ m = 1 := by
      have := pow_card_eq_one' (G := ↥π.ker) (x := ⟨_, hz⟩)
      exact congrArg Subtype.val this
    rw [← pow_mul, mul_comm, pow_mul, ht, pow_mul, hzm, one_pow]
  · rw [map_pow, hπj]

end PLift

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
