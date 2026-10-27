module

public import CFSG.GH74.GLS.Balance.Bender.ExtSylow
public import CFSG.GH74.GLS.Balance.Bender.L53Core
public import CFSG.GH74.GLS.Balance.PStarComp

public section

namespace CFSG.GH74.GLS.Balance.BenderExt

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Balance
open scoped commutatorElement

variable {G : Type} [Group G] {p : ℕ}

theorem pow_mul_mem_of_mem_normalizer {A : Subgroup G} {a c : G} (ha : a ∈ A)
    (hc : c ∈ normalizer (A : Set G)) (n : ℕ) : ∃ a' ∈ A, (a * c) ^ n = a' * c ^ n := by
  induction n with
  | zero => exact ⟨1, A.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨a', ha', h⟩ := ih
    have hcn : c ^ n ∈ normalizer (A : Set G) := Subgroup.pow_mem _ hc n
    have h1 : c ^ n * a * (c ^ n)⁻¹ ∈ A := (mem_normalizer_iff.mp hcn a).mp ha
    refine ⟨a' * (c ^ n * a * (c ^ n)⁻¹), A.mul_mem ha' h1, ?_⟩
    rw [pow_succ, h]
    group

theorem le_sup_oResOf [Finite G] (hp : p.Prime) {X A C : Subgroup G} (hX : oResOf p X = X)
    (hAX : A ≤ X) (hAn : (A.subgroupOf X).Normal) (hCX : C ≤ X) (h : X ≤ A ⊔ C) :
    X ≤ A ⊔ oResOf p C := by
  have hXA : X ≤ normalizer (A : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hAX
  have key : oResOf p X ≤ A ⊔ oResOf p C := by
    refine oResOf_le_of fun x hx hcop => ?_
    obtain ⟨a, ha, c, hc, hac⟩ := (mem_sup_of_le_normalizer (hCX.trans hXA)).mp (h hx)
    obtain ⟨e, he⟩ := exists_pow_mem_oResOf hp hc
    obtain ⟨a', ha', hpow⟩ := pow_mul_mem_of_mem_normalizer ha (hXA (hCX hc)) (p ^ e)
    have hmem : x ^ (p ^ e) ∈ A ⊔ oResOf p C := by
      rw [← hac, hpow]
      exact Subgroup.mul_mem_sup ha' he
    have hcop' : Nat.Coprime (p ^ e) (orderOf x) := (hcop.pow_right e).symm
    rcases Nat.lt_or_ge 1 (orderOf x) with h1 | h1
    · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop' h1
      have : x = (x ^ (p ^ e)) ^ m := by
        rw [← pow_mul, ← pow_mod_orderOf, hm, pow_one]
      rw [this]; exact Subgroup.pow_mem _ hmem m
    · have : orderOf x = 1 := le_antisymm h1 (orderOf_pos x)
      rw [orderOf_eq_one_iff.mp this]; exact one_mem _
  rw [hX] at key
  exact key

end CFSG.GH74.GLS.Balance.BenderExt

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Balance.BenderExt
open scoped commutatorElement

theorem bender_l54 {p : ℕ} [Fact p.Prime] (h53 : BenderL53 p) : BenderL54 p := by
  intro G _ _ X N P hX hNX hNn hP
  have hp : p.Prime := Fact.out
  set C := X ⊓ centralizer (P : Set G) with hC
  set X₀ := oResOf p C with hX₀
  have hX₀C : X₀ ≤ C := oResOf_le p C
  have hX₀X : X₀ ≤ X := hX₀C.trans inf_le_left
  have hX₀P : X₀ ≤ centralizer (P : Set G) := hX₀C.trans inf_le_right
  have hXN : X ≤ normalizer (N : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hNX
  have hXT : X ≤ N ⊔ C := isPStar_T_ambient hX hNX hNn hP.1 hP.2.1
  have hXX₀ : X ≤ N ⊔ X₀ := le_sup_oResOf hp hX.oResOf_eq hNX hNn inf_le_left hXT
  set N₀ := N ⊓ X₀ with hN₀
  have hN₀n : (N₀.subgroupOf X₀).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hx' : (x : G) ∈ N₀ := hx
    have h1 : (g : G) * (x : G) * (g : G)⁻¹ ∈ N :=
      (mem_normalizer_iff.mp (hXN (hX₀X g.2)) (x : G)).mp hx'.1
    exact ⟨h1, X₀.mul_mem (X₀.mul_mem g.2 hx'.2) (X₀.inv_mem g.2)⟩
  have hP₀ : IsSylowIn p (P ⊓ X₀) N₀ := isSylowIn_inf_of_le_centralizer hP hX₀P
  have hZ0 : IsPStar p (↥X ⧸ N.subgroupOf X) := by
    have := hNn
    exact bender_l52ii p ↥X (N.subgroupOf X) hX
  set φ : ↥X₀ →* ↥X ⧸ N.subgroupOf X :=
    (QuotientGroup.mk' (N.subgroupOf X)).comp (Subgroup.inclusion hX₀X) with hφ
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
    have hw : (w : G) ∈ N ⊔ X₀ := hXX₀ w.2
    obtain ⟨n, hn, x, hx, hnx⟩ := (mem_sup_of_le_normalizer (hX₀X.trans hXN)).mp hw
    refine ⟨⟨x, hx⟩, ?_⟩
    show (QuotientGroup.mk' (N.subgroupOf X)) ⟨x, hX₀X hx⟩ = (w : ↥X ⧸ N.subgroupOf X)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
    show (x⁻¹ * (w : G)) ∈ N
    rw [← hnx]
    have := (mem_normalizer_iff.mp (hXN (X.inv_mem (hX₀X hx))) n).mp hn
    simpa [mul_assoc] using this
  have hker : φ.ker = N₀.subgroupOf X₀ := by
    ext y
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨fun h => ⟨h, y.2⟩, fun h => h.1⟩
  have hZ : IsPStar p (↥X₀ ⧸ N₀.subgroupOf X₀) := by
    have e : (↥X₀ ⧸ N₀.subgroupOf X₀) ≃* (↥X ⧸ N.subgroupOf X) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
    exact IsPStar.of_mulEquiv e.symm hZ0
  have hL : IsPStar p ↥(oResOf p N₀) := by
    apply bender_l52i p
    apply coprime_card_oResOf_of_central_sylow hP₀
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hX₀P hn.2 |> fun h => Subgroup.mem_centralizer_iff.mp h u hu.1 |>.symm).symm
  have h3 : oResOf p X₀ ≤ oResOf p N₀ ⊔ (X₀ ⊓ centralizer ((P ⊓ X₀ : Subgroup G) : Set G)) := by
    have : X₀ ≤ centralizer ((P ⊓ X₀ : Subgroup G) : Set G) := fun x hx =>
      Subgroup.centralizer_le (by exact SetLike.coe_subset_coe.mpr inf_le_left) (hX₀P hx)
    exact (oResOf_le p X₀).trans ((le_inf le_rfl this).trans le_sup_right)
  have := h53 G X₀ N₀ (P ⊓ X₀) inf_le_right hP₀ hZ hL h3
  rwa [hX₀, oResOf_oResOf] at this

end CFSG.GH74.GLS.Balance
