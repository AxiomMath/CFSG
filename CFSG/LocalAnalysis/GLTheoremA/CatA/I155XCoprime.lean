module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I155XBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conj_cc_succ (x c : G) (i : ℕ) :
    x⁻¹ * ((x ^ i)⁻¹ * c * x ^ i) * x = (x ^ (i + 1))⁻¹ * c * x ^ (i + 1) := by
  rw [pow_succ, mul_inv_rev]
  group

theorem list_telescope (x c : G) : ∀ (n s : ℕ),
    x⁻¹ * (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' s n)).prod * x =
      (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' (s + 1) n)).prod
  | 0, s => by simp
  | n + 1, s => by
    have ih := list_telescope x c n (s + 1)
    have e1 : (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' s (n + 1))).prod =
        (x ^ s)⁻¹ * c * x ^ s *
          (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' (s + 1) n)).prod := by
      rw [List.range'_succ, List.map_cons, List.prod_cons]
    have e2 : (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' (s + 1) (n + 1))).prod =
        (x ^ (s + 1))⁻¹ * c * x ^ (s + 1) *
          (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' (s + 1 + 1) n)).prod := by
      rw [List.range'_succ, List.map_cons, List.prod_cons]
    rw [e1, e2]
    calc x⁻¹ * ((x ^ s)⁻¹ * c * x ^ s *
          (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' (s + 1) n)).prod) * x
        = (x⁻¹ * ((x ^ s)⁻¹ * c * x ^ s) * x) *
          (x⁻¹ * (List.map (fun i : ℕ => (x ^ i)⁻¹ * c * x ^ i) (List.range' (s + 1) n)).prod * x) := by
          group
      _ = _ := by
          rw [conj_cc_succ, ih]

theorem prod_range'_succ_right {M : Type*} [Monoid M] (f : ℕ → M) (n s : ℕ) :
    (List.map f (List.range' s (n + 1))).prod =
      (List.map f (List.range' s n)).prod * f (s + n) := by
  simp [List.range'_concat]

theorem coset_conj_pow {x z : G} {N : Subgroup G} (hxN : ∀ n ∈ N, x⁻¹ * n * x ∈ N)
    (hz : z⁻¹ * (x⁻¹ * z * x) ∈ N) : ∀ k : ℕ, z⁻¹ * ((x ^ k)⁻¹ * z * x ^ k) ∈ N
  | 0 => by simp
  | k + 1 => by
    have ih := coset_conj_pow hxN hz k
    have e : z⁻¹ * ((x ^ (k + 1))⁻¹ * z * x ^ (k + 1)) =
        (z⁻¹ * (x⁻¹ * z * x)) * (x⁻¹ * (z⁻¹ * ((x ^ k)⁻¹ * z * x ^ k)) * x) := by
      rw [pow_succ, mul_inv_rev]
      group
    rw [e]
    exact N.mul_mem hz (hxN _ ih)

theorem zpowers_mem_normalizer_of_mem {x : G} {N : Subgroup G} (hxN : x ∈ Subgroup.normalizer (N : Set G))
    {g : G} (hg : g ∈ Subgroup.zpowers x) (n : G) (hn : n ∈ N) : g * n * g⁻¹ ∈ N :=
  (Subgroup.mem_normalizer_iff.1 (Subgroup.zpowers_le.2 hxN hg) n).1 hn

theorem coset_conj_zpowers {x z : G} {p : ℕ} (hp : 0 < p) (hx : x ^ p = 1) {N : Subgroup G}
    (hxN : ∀ n ∈ N, x⁻¹ * n * x ∈ N) (hz : z⁻¹ * (x⁻¹ * z * x) ∈ N) :
    ∀ g ∈ Subgroup.zpowers x, z⁻¹ * (g * z * g⁻¹) ∈ N := by
  intro g hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
  obtain ⟨n, hnp, hkn⟩ := exists_nat_pow_eq hp hx k
  have hg' : g = x ^ n := by rw [← hk]; exact hkn
  have hinv : g⁻¹ = x ^ (p - n) := by
    rw [hg']
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, Nat.add_sub_cancel' hnp.le, hx]
  have hgeq : g = (x ^ (p - n))⁻¹ := inv_eq_iff_eq_inv.1 hinv
  have hg2 : g * z * g⁻¹ = (x ^ (p - n))⁻¹ * z * x ^ (p - n) := by
    rw [hinv, hgeq]
  rw [hg2]
  exact coset_conj_pow hxN hz (p - n)

theorem exists_fixed_coset {x z : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1) {N : Subgroup G}
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) (hcop : ¬ p ∣ Nat.card N)
    (hz : z⁻¹ * (x⁻¹ * z * x) ∈ N) :
    ∃ n ∈ N, x⁻¹ * (z * n) * x = z * n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hxN' : ∀ n ∈ N, x⁻¹ * n * x ∈ N := fun n hn => by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxN) n).1 hn
    simpa using this
  have hconj := coset_conj_zpowers hp.pos hx hxN' hz
  have hPp : IsPGroup p (Subgroup.zpowers x) := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hmem : ∀ (g : Subgroup.zpowers x) (n : N),
      z⁻¹ * ((g : G) * z * (n : G) * (g : G)⁻¹) ∈ N := by
    intro g n
    have e : z⁻¹ * ((g : G) * z * (n : G) * (g : G)⁻¹) =
        (z⁻¹ * ((g : G) * z * (g : G)⁻¹)) * ((g : G) * (n : G) * (g : G)⁻¹) := by group
    rw [e]
    exact N.mul_mem (hconj _ g.2) (zpowers_mem_normalizer_of_mem hxN g.2 _ n.2)
  letI act : MulAction (Subgroup.zpowers x) N :=
    { smul := fun g n => ⟨z⁻¹ * ((g : G) * z * (n : G) * (g : G)⁻¹), hmem g n⟩
      one_smul := fun n => Subtype.ext (by
        show z⁻¹ * (((1 : Subgroup.zpowers x) : G) * z * (n : G) *
          ((1 : Subgroup.zpowers x) : G)⁻¹) = (n : G)
        simp)
      mul_smul := fun g h n => Subtype.ext (by
        show z⁻¹ * (((g * h : Subgroup.zpowers x) : G) * z * (n : G) *
          ((g * h : Subgroup.zpowers x) : G)⁻¹) = z⁻¹ * ((g : G) * z *
          (z⁻¹ * ((h : G) * z * (n : G) * (h : G)⁻¹)) * (g : G)⁻¹)
        simp only [Subgroup.coe_mul]
        group) }
  obtain ⟨n₀, hn₀⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hPp N hcop
  have h1 : z⁻¹ * (x * z * (n₀ : G) * x⁻¹) = (n₀ : G) :=
    congrArg Subtype.val (hn₀ ⟨x, Subgroup.mem_zpowers x⟩)
  have h3 : x * (z * n₀) * x⁻¹ = z * n₀ := by
    calc x * (z * n₀) * x⁻¹ = z * (z⁻¹ * (x * z * (n₀ : G) * x⁻¹)) := by group
      _ = z * n₀ := by rw [h1]
  refine ⟨n₀, n₀.2, ?_⟩
  calc x⁻¹ * (z * n₀) * x = x⁻¹ * (x * (z * n₀) * x⁻¹) * x := by rw [h3]
    _ = z * n₀ := by group

end CFSG.LocalAnalysis.GLTheoremA.I155X
