module

public import CFSG.LocalAnalysis.OddStandard.Seitz77OddCoreCount
public import Mathlib.GroupTheory.Solvable

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup

theorem oddCore_exists_normal_pgroup_le {H : Type*} [Group H] [Finite H] (K₀ : Subgroup H)
    [K₀.Normal] [Group.IsSolvable K₀] (hK₀ : K₀ ≠ ⊥) :
    ∃ (M : Subgroup H) (p r : ℕ), M.Normal ∧ M ≤ K₀ ∧ p.Prime ∧ 0 < r ∧
      Nat.card M = p ^ r := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ M : Subgroup H, M.Normal ∧ M ≤ K₀ ∧ M ≠ ⊥ ∧ Nat.card M = n
  have hP : ∃ n, P n := ⟨Nat.card K₀, K₀, inferInstance, le_rfl, hK₀, rfl⟩
  obtain ⟨M, hMn, hMK, hMbot, hMcard⟩ := Nat.find_spec hP
  have hmin : ∀ K : Subgroup H, K.Normal → K ≤ M → K = ⊥ ∨ K = M := by
    intro K hK hKM
    by_cases hKbot : K = ⊥
    · exact Or.inl hKbot
    · right
      by_contra hne
      have hlt : Nat.card K < Nat.card M := Subgroup.card_lt_of_lt (lt_of_le_of_ne hKM hne)
      exact Nat.find_min hP (hMcard ▸ hlt) ⟨K, hK, hKM.trans hMK, hKbot, rfl⟩
  have : M.Normal := hMn
  have : CFSG.IsMinimalNormal M := ⟨fun K _ hKM => hmin K inferInstance hKM⟩
  have : Group.IsSolvable M :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hMK)
  obtain ⟨p, hp, hel⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian M
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := (CFSG.IsElementaryAbelian.isPGroup p M).exists_card_eq
  refine ⟨M, p, r, hMn, hMK, hp, ?_, hr⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · exfalso
    apply hMbot
    rw [pow_zero, Subgroup.card_eq_one] at hr
    exact hr
  · exact hr0

theorem oddCore_mem_centralizer_of_pow_eq_one {H : Type*} [Group H] [Finite H] (M : Subgroup H)
    [M.Normal] (x : H) (q : ℕ) [hq : Fact q.Prime] (hx : x ^ q = 1) (p r : ℕ)
    (hp : p.Prime) (hpq : p ≠ q) (hM : Nat.card M = p ^ r)
    (htab : ∀ j, 1 ≤ j → j ≤ r → p ^ j % q ≠ 1) :
    x ∈ Subgroup.centralizer (M : Set H) := by
  classical
  let f : M → M := fun m => ⟨x * m * x⁻¹, Normal.conj_mem inferInstance m.1 m.2 x⟩
  have hit : ∀ n : ℕ, ∀ m : M, ((f^[n] m : M) : H) = x ^ n * m * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ n ih =>
      intro m
      rw [Function.iterate_succ_apply', pow_succ']
      show x * ((f^[n] m : M) : H) * x⁻¹ = _
      rw [ih]
      group
  have hf : f^[q] = id := by
    funext m
    apply Subtype.ext
    rw [hit, hx]
    simp
  have h := oddCore_card_modEq_card_fixed f q hf
  let C : Subgroup H := M ⊓ Subgroup.centralizer ({x} : Set H)
  have e : {m : M // f m = m} ≃ C :=
    { toFun := fun m => ⟨m.1.1, m.1.2, by
        refine Subgroup.mem_centralizer_iff.mpr (fun h hh => ?_)
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        have := congrArg Subtype.val m.2
        simp only [f] at this
        calc x * (m.1 : H) = (x * m.1 * x⁻¹) * x := by group
          _ = (m.1 : H) * x := by rw [this]⟩
      invFun := fun c => ⟨⟨c.1, c.2.1⟩, by
        apply Subtype.ext
        have hc := (Subgroup.mem_centralizer_iff.mp c.2.2) x (Set.mem_singleton x)
        show x * c.1 * x⁻¹ = c.1
        rw [hc]
        group⟩
      left_inv := fun m => rfl
      right_inv := fun c => rfl }
  rw [Nat.card_congr e, hM] at h
  have hCdvd : Nat.card C ∣ p ^ r := hM ▸ Subgroup.card_dvd_of_le (inf_le_left : C ≤ M)
  obtain ⟨s, hs, hCs⟩ := (Nat.dvd_prime_pow hp).mp hCdvd
  rw [hCs] at h
  have hsr : s = r := by
    by_contra hne
    have hlt : s < r := lt_of_le_of_ne hs hne
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have hcop : Nat.gcd q (p ^ s) = 1 :=
      Nat.Coprime.pow_right s ((Nat.coprime_primes hq.out hp).mpr (Ne.symm hpq))
    have h2 : p ^ s * p ^ (j + 1) ≡ p ^ s * 1 [MOD q] := by
      rw [← pow_add, mul_one]
      exact h
    have h3 := Nat.ModEq.cancel_left_of_coprime hcop h2
    have h4 : p ^ (j + 1) % q = 1 := by
      have := h3
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt hq.out.one_lt] at this
    exact htab (j + 1) (by omega) (by omega) h4
  subst hsr
  have hCM : C = M := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hCs, hM])
  have hMle : M ≤ Subgroup.centralizer ({x} : Set H) := by
    rw [← hCM]
    exact inf_le_right
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  exact ((Subgroup.mem_centralizer_iff.mp (hMle hm)) x (Set.mem_singleton x)).symm

theorem oddCore_le_center_of_sup_eq_top {H : Type*} [Group H] (hperf : commutator H = ⊤)
    (K₀ : Subgroup H) [Group.IsSolvable K₀] (M : Subgroup H) [M.Normal]
    (hsup : Subgroup.centralizer (M : Set H) ⊔ K₀ = ⊤) : M ≤ Subgroup.center H := by
  set C := Subgroup.centralizer (M : Set H) with hC
  have hperf' : Group.IsPerfect H := Group.isPerfect_def.mpr hperf
  have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp K₀.subtype) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C y
    have hg : g ∈ C ⊔ K₀ := hsup ▸ Subgroup.mem_top g
    obtain ⟨c, hc, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    refine ⟨⟨k, hk⟩, ?_⟩
    simp [(QuotientGroup.eq_one_iff c).mpr hc]
  have hsolv : Group.IsSolvable (H ⧸ C) := Group.isSolvable_of_surjective hsurj
  have hsub : Subsingleton (H ⧸ C) := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (H ⧸ C) hsolv
  have hall : ∀ g : H, g ∈ C := fun g => (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  have htop : C = ⊤ := eq_top_iff.mpr (fun g _ => hall g)
  exact Subgroup.centralizer_eq_top_iff_subset.mp htop

theorem oddCore_le_center_of_card_prime {H : Type*} [Group H] (hperf : commutator H = ⊤)
    (M : Subgroup H) [M.Normal] (hM : (Nat.card M).Prime) : M ≤ Subgroup.center H := by
  have : Fact (Nat.card M).Prime := ⟨hM⟩
  have : IsCyclic M := isCyclic_of_prime_card (p := Nat.card M) rfl
  let φ : H →* (ZMod (Nat.card M))ˣ :=
    (IsCyclic.mulAutMulEquiv M).toMonoidHom.comp MulAut.conjNormal
  have h1 : commutator H ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hperf] at h1
  intro m hm
  rw [Subgroup.mem_center_iff]
  intro g
  have hφ : φ g = 1 := h1 (Subgroup.mem_top g)
  have h2 : (MulAut.conjNormal g : MulAut M) = 1 := by
    apply (IsCyclic.mulAutMulEquiv M).injective
    simpa [φ] using hφ
  have h3 := congrArg (fun a : MulAut M => ((a ⟨m, hm⟩ : M) : H)) h2
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
  calc g * m = (g * m * g⁻¹) * g := by group
    _ = m * g := by rw [h3]

theorem oddCore_sup_eq_top_of_isSimple {H : Type*} [Group H] (K₀ : Subgroup H) [K₀.Normal]
    [IsSimpleGroup (H ⧸ K₀)] (D : Subgroup H) [D.Normal] (hD : ¬ D ≤ K₀) : D ⊔ K₀ = ⊤ := by
  let π := QuotientGroup.mk' K₀
  have hN : (D.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective K₀)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.map π) with h | h
  · exfalso
    apply hD
    intro d hd
    have h1 : π d ∈ D.map π := Subgroup.mem_map_of_mem π hd
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff d).mp h1
  · have h2 : D ⊔ K₀ = (D.map π).comap π := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [h2, h, Subgroup.comap_top]

theorem oddCore_sup_eq_top_of_order_five {H : Type*} [Group H] [Finite H] (K₀ : Subgroup H)
    [K₀.Normal] (hcop : Nat.Coprime 5 (Nat.card K₀))
    (hgen : Subgroup.closure {x : H ⧸ K₀ | orderOf x = 5} = ⊤)
    (D : Subgroup H) [D.Normal] (hD : ∀ x : H, orderOf x = 5 → x ∈ D) : D ⊔ K₀ = ⊤ := by
  let π := QuotientGroup.mk' K₀
  have hsub : {x : H ⧸ K₀ | orderOf x = 5} ⊆ (D.map π : Set (H ⧸ K₀)) := by
    intro x hx
    have hx5 : orderOf x = 5 := hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K₀ x
    set n := Nat.card K₀ with hn
    have hy5 : y ^ 5 ∈ K₀ := by
      rw [← QuotientGroup.eq_one_iff]
      have : (QuotientGroup.mk (y ^ 5) : H ⧸ K₀) = (QuotientGroup.mk y) ^ 5 := rfl
      rw [this]
      have := pow_orderOf_eq_one (π y)
      rwa [hx5] at this
    have hz5 : (y ^ n) ^ 5 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      have := pow_card_eq_one' (G := K₀) (x := ⟨y ^ 5, hy5⟩)
      exact congrArg Subtype.val this
    have hπz : π (y ^ n) = (π y) ^ n := map_pow π y n
    have hord : orderOf (π (y ^ n)) = 5 := by
      rw [hπz, Nat.Coprime.orderOf_pow (by rw [hx5]; exact hcop), hx5]
    have hz1 : y ^ n ≠ 1 := by
      intro h
      rw [h, map_one] at hord
      simp at hord
    have hzord : orderOf (y ^ n) = 5 := by
      have hdvd : orderOf (y ^ n) ∣ 5 := orderOf_dvd_of_pow_eq_one hz5
      rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hz1
      · exact h
    have hzD := hD _ hzord
    obtain ⟨n', -, hn'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm (by norm_num : 1 < 5)
    refine ⟨(y ^ n) ^ n', Subgroup.pow_mem D hzD n', ?_⟩
    show π ((y ^ n) ^ n') = π y
    rw [map_pow, hπz, ← pow_mul]
    have h5 : (π y) ^ (n * n') = (π y) ^ (n * n' % 5) := by
      rw [← hx5, pow_mod_orderOf]
    rw [h5, hn', pow_one]
  have hT : D.map π = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le _).mpr hsub
  have h2 : D ⊔ K₀ = (D.map π).comap π := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  rw [h2, hT, Subgroup.comap_top]

end CFSG.OddStandard.Seitz77
