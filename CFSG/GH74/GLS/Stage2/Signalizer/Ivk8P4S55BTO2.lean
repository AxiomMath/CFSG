module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOut
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG
open scoped commutatorElement

section PC

variable {A : Type*} [Group A]

theorem exists_bezout_two_pow {m : ℕ} (hm : Odd m) (k : ℕ) :
    ∃ a b : ℤ, (m : ℤ) * a + 2 ^ k * b = 1 := by
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k hm.coprime_two_right
  refine ⟨Nat.gcdA m (2 ^ k), Nat.gcdB m (2 ^ k), ?_⟩
  have hg := Nat.gcd_eq_gcd_ab m (2 ^ k)
  rw [hcop] at hg
  push_cast at hg
  exact hg.symm

theorem exists_pc {J N : Subgroup A} (hJp : Group.IsPerfect ↥J) (hJN : J ≤ N)
    {O : Subgroup (MulAut (↥J ⧸ center ↥J))}
    (hOinn : ∀ w ∈ O, ∃ m : ℕ, Odd m ∧
      w ^ m ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    {y : A} (hy : y ∈ normalizer (J : Set A)) (hyO : actJ J ⟨y, hy⟩ ∈ O) {k : ℕ}
    (hyk : y ^ 2 ^ k ∈ N) :
    ∃ n ∈ N, n ∈ J ⊔ zpowers y ∧ n⁻¹ * y ∈ centralizer (J : Set A) := by
  obtain ⟨m, hm, ⟨yb, hyb⟩⟩ := hOinn _ hyO
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective yb
  obtain ⟨a, b, hab⟩ := exists_bezout_two_pow hm k
  set y' : ↥(normalizer (J : Set A)) := ⟨y, hy⟩ with hy'
  set j' : ↥(normalizer (J : Set A)) := ⟨(j : A), Subgroup.le_normalizer j.2⟩ with hj'
  set n' : ↥(normalizer (J : Set A)) := j' ^ a * (y' ^ 2 ^ k) ^ b with hn'
  have hj'act : actJ J j' = actJ J y' ^ m := by
    rw [hj', actJ_of_mem J j.2, ← hyb]
  have hn'act : actJ J n' = actJ J y' := by
    rw [hn', map_mul, map_zpow, map_zpow, map_pow, hj'act, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_add]
    push_cast
    rw [hab, zpow_one]
  have hc : actJ J (n'⁻¹ * y') = 1 := by rw [map_mul, map_inv, hn'act, inv_mul_cancel]
  have hcen := mem_centralizer_of_actJ_eq_one J hJp hc
  refine ⟨(n' : A), ?_, ?_, ?_⟩
  · show (j : A) ^ a * (y ^ 2 ^ k) ^ b ∈ N
    exact N.mul_mem (N.zpow_mem (hJN j.2) a) (N.zpow_mem hyk b)
  · show (j : A) ^ a * (y ^ 2 ^ k) ^ b ∈ J ⊔ zpowers y
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_sup_left j.2) a)
      (Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers y)) _) b)
  · simpa using hcen

end PC

section Comps

variable {M : Type*} [Group M] [Finite M]

omit [Finite M] in
theorem mem_normalizer_of_odd
    (h3 : ∀ J₁ J₂ J₃ : Subgroup M, IsComponent J₁ → IsComponent J₂ → IsComponent J₃ →
      J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False)
    {J : Subgroup M} (hJ : IsComponent J) {y : M} {m : ℕ} (hm : Odd m) (hym : y ^ m = 1) :
    y ∈ normalizer (J : Set M) := by
  have hnorm : ∀ b : M, J.map (MulAut.conj b).toMonoidHom = J → b ∈ normalizer (J : Set M) := by
    intro b h
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      have : z = x := by
        have h2 : b * z * b⁻¹ = b * x * b⁻¹ := hzx
        simpa using h2
      rw [← this]
      exact hz
  have hcomp : ∀ b : M, IsComponent (J.map (MulAut.conj b).toMonoidHom) := fun b =>
    LocalCores.isComponent_map_mulEquiv (MulAut.conj b) hJ
  have hmap : ∀ b c : M, (J.map (MulAut.conj c).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * c)).toMonoidHom := by
    intro b c
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  by_contra hn
  have h1 : J.map (MulAut.conj y).toMonoidHom ≠ J := fun h => hn (hnorm y h)
  by_cases h2 : J.map (MulAut.conj (y * y)).toMonoidHom = J
  · apply hn
    obtain ⟨r, hr⟩ := hm
    have hyy : y = (y * y) ^ (r + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (r + 1) = m + 1 by omega, pow_succ, hym, one_mul]
    rw [hyy]
    exact Subgroup.pow_mem _ (hnorm _ h2) _
  · by_cases h21 : J.map (MulAut.conj (y * y)).toMonoidHom = J.map (MulAut.conj y).toMonoidHom
    · apply h1
      have hone : J.map (MulAut.conj (1 : M)).toMonoidHom = J := by
        ext x
        simp
      have := congrArg (fun K => K.map (MulAut.conj y⁻¹).toMonoidHom) h21
      simp only [hmap] at this
      rw [show y⁻¹ * (y * y) = y by group, inv_mul_cancel, hone] at this
      exact this
    · exact h3 J _ _ hJ (hcomp y) (hcomp (y * y)) (Ne.symm h1) (Ne.symm h2) (Ne.symm h21)

theorem le_of_perfect_of_two {N X J : Subgroup M} [N.Normal] (hJX : J ≤ X)
    (hJ : Group.IsPerfect ↥J) (hX2 : ∀ x ∈ X, ∃ n : ℕ, x ^ 2 ^ n ∈ N) : J ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q : M →* M ⧸ N := QuotientGroup.mk' N with hq
  have h2 : IsPGroup 2 ↥(J.map q) := by
    rintro ⟨_, j, hj, rfl⟩
    obtain ⟨n, hn⟩ := hX2 j (hJX hj)
    refine ⟨n, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hn
  have hP : Group.IsPerfect ↥(J.map q) := Group.IsPerfect.map q
  have hnil : Group.IsNilpotent ↥(J.map q) := h2.isNilpotent
  have hbot : J.map q = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(J.map q) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isNilpotent (↥(J.map q)) hnil
  intro j hj
  have : q j ∈ J.map q := ⟨j, hj, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff _).mp this

theorem le_centralizer_of_not_le {N X J : Subgroup M} [N.Normal] [hX : X.Normal]
    (hX2 : ∀ x ∈ X, ∃ n : ℕ, x ^ 2 ^ n ∈ N) (hJ : IsComponent J) (hJN : ¬ J ≤ N) :
    X ≤ centralizer (J : Set M) := by
  rcases LocalCores.component_normal_subgroup hJ hX with h | h
  · exact absurd (le_of_perfect_of_two h hJ.1.1 hX2) hJN
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have : ⁅j, x⁆ ∈ (⊥ : Subgroup M) := h ▸ Subgroup.commutator_mem_commutator hj hx
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp this)

end Comps

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
