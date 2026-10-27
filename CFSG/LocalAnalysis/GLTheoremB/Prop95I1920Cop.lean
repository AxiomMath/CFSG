module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Asm

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18
open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem inv_mul_mem_normalizer_of_map_conj_eq {K : Subgroup X} {a b : X}
    (h : K.map (MulAut.conj a).toMonoidHom = K.map (MulAut.conj b).toMonoidHom) :
    a⁻¹ * b ∈ Subgroup.normalizer (K : Set X) := by
  have key : ∀ {a b : X}, K.map (MulAut.conj a).toMonoidHom = K.map (MulAut.conj b).toMonoidHom →
      ∀ x ∈ K, a⁻¹ * b * x * (a⁻¹ * b)⁻¹ ∈ K := by
    intro a b h x hx
    have h1 : b * x * b⁻¹ ∈ K.map (MulAut.conj b).toMonoidHom := ⟨x, hx, rfl⟩
    rw [← h] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have hyx' : a * y * a⁻¹ = b * x * b⁻¹ := hyx
    have : a⁻¹ * b * x * (a⁻¹ * b)⁻¹ = y := by
      calc a⁻¹ * b * x * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * x * b⁻¹) * a := by group
        _ = a⁻¹ * (a * y * a⁻¹) * a := by rw [hyx']
        _ = y := by group
    rw [this]
    exact hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key h x, fun hx => ?_⟩
  have h2 := key h.symm _ hx
  have e : (b⁻¹ * a) * (a⁻¹ * b * x * (a⁻¹ * b)⁻¹) * (b⁻¹ * a)⁻¹ = x := by group
  rwa [e] at h2

theorem pow_mul_not_mem_normalizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup X} {d t : X}
    (hd : d ^ p = 1) (hdK : d ∉ Subgroup.normalizer (K : Set X)) (hdt : t * d = d * t) {e : ℕ}
    (ht2 : t ^ (2 ^ e) = 1) (htK : t ∉ Subgroup.normalizer (K : Set X)) (m : ℕ) :
    d ^ m * t ∉ Subgroup.normalizer (K : Set X) := by
  intro hg
  have hcomm : Commute (d ^ m) t := Commute.pow_left (show Commute d t from hdt.symm) m
  have hg2 : (d ^ m * t) ^ (2 ^ e) = d ^ (m * 2 ^ e) := by
    rw [hcomm.mul_pow, ht2, mul_one, ← pow_mul]
  have hmem : d ^ (m * 2 ^ e) ∈ Subgroup.normalizer (K : Set X) := by
    rw [← hg2]
    exact Subgroup.pow_mem _ hg _
  by_cases hpm : p ∣ m
  · obtain ⟨c, rfl⟩ := hpm
    have h1 : d ^ (p * c) = 1 := by rw [pow_mul, hd, one_pow]
    rw [h1, one_mul] at hg
    exact htK hg
  · have hord : orderOf d = p := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hd) with h1 | h1
      · exact absurd (by rw [orderOf_eq_one_iff.1 h1]; exact Subgroup.one_mem _) hdK
      · exact h1
    have hcop : Nat.Coprime (m * 2 ^ e) (orderOf d) := by
      rw [hord]
      refine Nat.Coprime.mul_left ?_ ?_
      · exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpm |>.symm
      · exact Nat.Coprime.pow_left e ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime hcop
    apply hdK
    rw [← hs]
    exact Subgroup.pow_mem _ hmem s

theorem commute_of_diagProd_commute {p : ℕ} (hp : p.Prime) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) {d : X} (hd : d ^ p = 1) (hdK : d ∉ Subgroup.normalizer (K : Set X))
    {k : X} (hk : k ∈ K) {k' : X} (hk' : k' ∈ K)
    (h : diagProd d p k * k' = k' * diagProd d p k) : k * k' = k' * k := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  rw [diagProd_succ] at h
  set M := ((List.range q).map (fun i => cpow d (i + 1) k)).prod with hM
  have hMc : M * k' = k' * M := by
    have : Commute M k' := by
      apply Commute.list_prod_left
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      have := commute_cpow hp hK hd hdK (by have := List.mem_range.1 hi; omega : i + 1 < q + 1)
        (by omega : 0 < q + 1) (by omega : i + 1 ≠ 0) hk hk'
      rwa [cpow_zero] at this
    exact this.eq
  have h1 : k * k' * M = k' * k * M := by
    calc k * k' * M = k * (k' * M) := by group
      _ = k * (M * k') := by rw [hMc]
      _ = k * M * k' := by group
      _ = k' * (k * M) := h
      _ = k' * k * M := by group
  exact mul_right_cancel h1

theorem pCoreOf_le_normalizer_of_not_mem_normalizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) {d : X} (hd : d ^ p = 1)
    (hdK : d ∉ Subgroup.normalizer (K : Set X)) :
    pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) ≤ Subgroup.normalizer (K : Set X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₀ := pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) with hT₀
  intro t ht
  by_contra htK
  have htC : t ∈ Subgroup.centralizer ({d} : Set X) := CFSG.LieType.BorelTits.pCoreOf_le 2 _ ht
  have hdt : t * d = d * t := Subgroup.mem_centralizer_singleton_iff.1 htC
  obtain ⟨e, he⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
    (Subgroup.centralizer ({d} : Set X))) ⟨t, ht⟩
  have ht2 : t ^ (2 ^ e) = 1 := by simpa using congrArg Subtype.val he
  have hcomm : ∀ i j : ℕ, i < p → j < p → ∀ x ∈ K, ∀ y ∈ K,
      cpow d i x * cpow d j (t * y * t⁻¹) = cpow d j (t * y * t⁻¹) * cpow d i x := by
    intro i j hi hj x hx y hy
    have hne : K.map (MulAut.conj (d ^ i)).toMonoidHom ≠
        K.map (MulAut.conj (d ^ j * t)).toMonoidHom := by
      intro h
      have hN := inv_mul_mem_normalizer_of_map_conj_eq h
      have h1 : (d ^ i)⁻¹ = d ^ (p - i) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_cancel' hi.le, hd]
      have h2 : (d ^ i)⁻¹ * (d ^ j * t) = d ^ (p - i + j) * t := by
        rw [h1, ← mul_assoc, ← pow_add]
      rw [h2] at hN
      exact pow_mul_not_mem_normalizer hp hp2 hd hdK hdt ht2 htK (p - i + j) hN
    have hKi := isComponentOf_conj hK (d ^ i)
    have hKj := isComponentOf_conj hK (d ^ j * t)
    refine comp_comm hKi hKj hne ⟨x, hx, rfl⟩ ⟨y, hy, ?_⟩
    show (d ^ j * t) * y * (d ^ j * t)⁻¹ = cpow d j (t * y * t⁻¹)
    simp only [cpow]
    group
  have hcommσ : ∀ x ∈ K, ∀ y ∈ K,
      Commute (diagProd d p x) (diagProd d p (t * y * t⁻¹)) := by
    intro x hx y hy
    unfold diagProd
    apply Commute.list_prod_left
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    apply Commute.list_prod_right
    intro b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
    exact hcomm i j (List.mem_range.1 hi) (List.mem_range.1 hj) x hx y hy
  have key : ∀ x ∈ K, ∃ e' : ℕ, ∀ k ∈ K, x ^ (2 ^ e') * k = k * x ^ (2 ^ e') := by
    intro x hx
    have hδC : diagProd d p x ∈ Subgroup.centralizer ({d} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := diagProd_comm_d hp hK hd hdK hx
      calc diagProd d p x * d = (d * diagProd d p x * d⁻¹) * d := by rw [h1]
        _ = d * diagProd d p x := by group
    have hδT : diagProd d p x * t * (diagProd d p x)⁻¹ ∈ T₀ :=
      (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hδC) t).1 ht
    have hc : diagProd d p x * t * (diagProd d p x)⁻¹ * t⁻¹ ∈ T₀ := T₀.mul_mem hδT (T₀.inv_mem ht)
    obtain ⟨e', he'⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (Subgroup.centralizer ({d} : Set X))) ⟨_, hc⟩
    have hc1 : (diagProd d p x * t * (diagProd d p x)⁻¹ * t⁻¹) ^ (2 ^ e') = 1 := by
      simpa using congrArg Subtype.val he'
    refine ⟨e', fun k hk => ?_⟩
    set n := 2 ^ e' with hn
    set δ := diagProd d p x with hδ
    set σ := t * δ * t⁻¹ with hσ
    have hσeq : σ = diagProd d p (t * x * t⁻¹) := diagProd_conj hdt p x
    have hcδσ : Commute δ σ⁻¹ := by
      rw [hσeq]
      exact (hcommσ x hx x hx).inv_right
    have hceq : δ * t * δ⁻¹ * t⁻¹ = δ * σ⁻¹ := by simp only [hσ]; group
    rw [hceq, hcδσ.mul_pow, inv_pow] at hc1
    have hδσ : δ ^ n = σ ^ n := by
      have : δ ^ n * (σ ^ n)⁻¹ = 1 := hc1
      exact mul_inv_eq_one.1 this
    have hpow : diagProd d p (x ^ n) = δ ^ n := by
      have := map_pow (diagHom hp hK hd hdK) (⟨x, hx⟩ : ↥K) n
      exact this
    have hσn : σ ^ n = t * δ ^ n * t⁻¹ := by
      simp only [hσ]
      exact (map_pow (MulAut.conj t) δ n).symm.trans (by simp [MulAut.conj_apply])
    have hσ2 : σ ^ n = diagProd d p (t * x ^ n * t⁻¹) := by
      rw [hσn, ← hpow, diagProd_conj hdt]
    have hxn : x ^ n ∈ K := Subgroup.pow_mem _ hx n
    have hw : diagProd d p (x ^ n) * k = k * diagProd d p (x ^ n) := by
      rw [hpow, hδσ, hσ2]
      have hlist : Commute (diagProd d p (t * x ^ n * t⁻¹)) k := by
        unfold diagProd
        apply Commute.list_prod_left
        intro a ha
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
        have := hcomm 0 j hp.pos (List.mem_range.1 hj) k hk (x ^ n) hxn
        rw [cpow_zero] at this
        exact this.symm
      exact hlist.eq
    exact commute_of_diagProd_commute hp hK hd hdK hxn hk hw
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
  have hnab := (isQuasisimple_of_comp hK).2.2
  refine CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb.not_isPGroup_two hnab ?_
  intro g
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨e', he'⟩ := key (x : X) x.2
  refine ⟨e', ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  intro g'
  apply Subtype.ext
  have := he' (g' : X) g'.2
  simpa using this.symm

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1920
