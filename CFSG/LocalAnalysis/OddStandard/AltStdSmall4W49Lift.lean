module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoStageMLift

public section

namespace CFSG.OddStandard.AltStdSmall4.W49

open Subgroup AltStdSec

@[expose] def OddCoversTrivial (K : Type) [Group K] : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ], Group.IsPerfect Γ → ∀ π : Γ →* K, Function.Surjective π →
    π.ker ≤ center Γ → Odd (Nat.card π.ker) → π.ker = ⊥

section Conj

variable {N : Type} [Group N]

private theorem exists_conj_of_involutions {P : Subgroup N} (hP : ∀ x ∈ P, Odd (orderOf x))
    {u v : N} (hu : u * u = 1) (hv : v * v = 1) (huv : v * u ∈ P) :
    ∃ r ∈ P, r * u * r⁻¹ = v := by
  have hv1 : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvvu : v * (v * u) = u := by rw [← mul_assoc, hv, one_mul]
  have hinv : v * (v * u) * v⁻¹ = (v * u)⁻¹ := by
    rw [hvvu, mul_inv_rev, hu1, hv1]
  obtain ⟨r, hr, hrr, hvr⟩ := exists_sq_root_inverted (hP _ huv) hinv
  have hrP : r ∈ P := (zpowers_le.2 huv) hr
  have hvr' : v * r = r⁻¹ * v := mul_inv_eq_iff_eq_mul.1 hvr
  refine ⟨r, hrP, ?_⟩
  calc r * u * r⁻¹ = r * (v * (v * u)) * r⁻¹ := by rw [hvvu]
    _ = r * (v * (r * r)) * r⁻¹ := by rw [hrr]
    _ = r * ((v * r) * r) * r⁻¹ := by group
    _ = r * ((r⁻¹ * v) * r) * r⁻¹ := by rw [hvr']
    _ = v := by group

private theorem comm_mul_of_commute {w₁ w₂ a c : N} (h1c : Commute w₁ c) (h12 : Commute w₁ w₂)
    (h2a : Commute w₂ a) :
    (a * w₁) * (c * w₂) * (a * w₁)⁻¹ * (c * w₂)⁻¹ = a * c * a⁻¹ * c⁻¹ := by
  calc (a * w₁) * (c * w₂) * (a * w₁)⁻¹ * (c * w₂)⁻¹
      = a * (w₁ * c) * w₂ * w₁⁻¹ * a⁻¹ * w₂⁻¹ * c⁻¹ := by group
    _ = a * (c * w₁) * w₂ * w₁⁻¹ * a⁻¹ * w₂⁻¹ * c⁻¹ := by rw [h1c.eq]
    _ = a * c * (w₁ * w₂) * w₁⁻¹ * a⁻¹ * w₂⁻¹ * c⁻¹ := by group
    _ = a * c * (w₂ * w₁) * w₁⁻¹ * a⁻¹ * w₂⁻¹ * c⁻¹ := by rw [h12.eq]
    _ = a * c * (w₂ * a⁻¹) * w₂⁻¹ * c⁻¹ := by group
    _ = a * c * (a⁻¹ * w₂) * w₂⁻¹ * c⁻¹ := by rw [h2a.inv_right.eq]
    _ = a * c * a⁻¹ * c⁻¹ := by group

theorem sq_eq_one_and_exists_conj' {O : Subgroup N} [O.Normal]
    (hO : ∀ x ∈ O, Odd (orderOf x)) {z b : N} (hz : z * z = 1) (hb : b * b = 1)
    (hzb : z * b = b * z) {K : Subgroup (N ⧸ O)} (hKc : center K = ⊥)
    (hKK : ∀ a ∈ K, ∀ c ∈ K, a * ((z : N ⧸ O) * c * (z : N ⧸ O)⁻¹) =
      ((z : N ⧸ O) * c * (z : N ⧸ O)⁻¹) * a) {a : N ⧸ O} (ha : a ∈ K)
    (hab : (b : N ⧸ O) = a * ((z : N ⧸ O) * a * (z : N ⧸ O)⁻¹)) :
    a * a = 1 ∧ ∃ g : N, g * b = b * g ∧ g * z * g⁻¹ = z * b := by
  obtain ⟨zq, hzq⟩ : ∃ zq : N ⧸ O, (z : N ⧸ O) = zq := ⟨_, rfl⟩
  rw [hzq] at hKK hab
  have hbq2 : (b : N ⧸ O) * (b : N ⧸ O) = 1 := by
    rw [← QuotientGroup.mk_mul, hb, QuotientGroup.mk_one]
  have haa' : a * (zq * a * zq⁻¹) = (zq * a * zq⁻¹) * a := hKK a ha a ha
  have ha2 : a * a = 1 := by
    have h1 : (a * a) * (zq * (a * a) * zq⁻¹) = 1 := by
      calc (a * a) * (zq * (a * a) * zq⁻¹)
          = a * (a * (zq * a * zq⁻¹)) * (zq * a * zq⁻¹) := by group
        _ = a * ((zq * a * zq⁻¹) * a) * (zq * a * zq⁻¹) := by rw [haa']
        _ = (a * (zq * a * zq⁻¹)) * (a * (zq * a * zq⁻¹)) := by group
        _ = 1 := by rw [← hab]; exact hbq2
    have h2 : zq * (a * a) * zq⁻¹ = (a * a)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hcen : (⟨a * a, mul_mem ha ha⟩ : K) ∈ center K := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      have h3 := hKK c c.2 (a * a) (mul_mem ha ha)
      rw [h2] at h3
      show (c : N ⧸ O) * (a * a) = (a * a) * c
      calc (c : N ⧸ O) * (a * a) = (a * a) * ((a * a)⁻¹ * c) * (a * a) := by group
        _ = (a * a) * ((c : N ⧸ O) * (a * a)⁻¹) * (a * a) := by rw [← h3]
        _ = (a * a) * c := by group
    rw [hKc] at hcen
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hcen)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective a
  have hab' : a * (b : N ⧸ O) = (b : N ⧸ O) * a := by
    rw [hab]
    calc a * (a * (zq * a * zq⁻¹)) = a * ((zq * a * zq⁻¹) * a) := by rw [haa']
      _ = (a * (zq * a * zq⁻¹)) * a := by group
  have hmem : g₀ * b * g₀⁻¹ * b⁻¹ ∈ O := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hg₀, hab']
    group
  obtain ⟨g₁, hg₁b, hg₁q⟩ : ∃ g₁ : N, g₁ * b = b * g₁ ∧ (g₁ : N ⧸ O) = a := by
    obtain ⟨p, hpO, hpc⟩ := exists_mul_mem_centralizer hO hb hmem
    refine ⟨p * g₀, mem_centralizer_singleton_iff.1 hpc, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff p).2 hpO, one_mul, hg₀]
  have hu2 : (g₁ * z * g₁⁻¹) * (g₁ * z * g₁⁻¹) = 1 := by
    calc (g₁ * z * g₁⁻¹) * (g₁ * z * g₁⁻¹) = g₁ * (z * z) * g₁⁻¹ := by group
      _ = 1 := by rw [hz]; group
  have hv2 : (b * z) * (b * z) = 1 := by
    calc (b * z) * (b * z) = b * (z * b) * z := by group
      _ = b * (b * z) * z := by rw [hzb]
      _ = (b * b) * (z * z) := by group
      _ = 1 := by rw [hb, hz, one_mul]
  have huq : ((g₁ * z * g₁⁻¹ : N) : N ⧸ O) = ((b * z : N) : N ⧸ O) := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hg₁q, hab, hzq, hai]
    group
  have hg₁b' : g₁⁻¹ * b = b * g₁⁻¹ := by
    calc g₁⁻¹ * b = g₁⁻¹ * (b * g₁) * g₁⁻¹ := by group
      _ = g₁⁻¹ * (g₁ * b) * g₁⁻¹ := by rw [← hg₁b]
      _ = b * g₁⁻¹ := by group
  have hub : (g₁ * z * g₁⁻¹) * b = b * (g₁ * z * g₁⁻¹) := by
    calc (g₁ * z * g₁⁻¹) * b = g₁ * z * (g₁⁻¹ * b) := by group
      _ = g₁ * z * (b * g₁⁻¹) := by rw [hg₁b']
      _ = g₁ * (z * b) * g₁⁻¹ := by group
      _ = g₁ * (b * z) * g₁⁻¹ := by rw [hzb]
      _ = (g₁ * b) * z * g₁⁻¹ := by group
      _ = (b * g₁) * z * g₁⁻¹ := by rw [hg₁b]
      _ = b * (g₁ * z * g₁⁻¹) := by group
  have hvu : (b * z) * (g₁ * z * g₁⁻¹) ∈ O ⊓ centralizer ({b} : Set N) := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, huq, ← QuotientGroup.mk_mul, hv2,
        QuotientGroup.mk_one]
    · rw [mem_centralizer_singleton_iff]
      calc (b * z) * (g₁ * z * g₁⁻¹) * b = b * z * ((g₁ * z * g₁⁻¹) * b) := by group
        _ = b * z * (b * (g₁ * z * g₁⁻¹)) := by rw [hub]
        _ = b * (z * b) * (g₁ * z * g₁⁻¹) := by group
        _ = b * (b * z) * (g₁ * z * g₁⁻¹) := by rw [hzb]
        _ = b * ((b * z) * (g₁ * z * g₁⁻¹)) := by group
  obtain ⟨r, hrP, hr⟩ := exists_conj_of_involutions (P := O ⊓ centralizer ({b} : Set N))
    (fun x hx => hO x (Subgroup.mem_inf.1 hx).1) hu2 hv2 hvu
  have hrb : r * b = b * r := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hrP).2
  refine ⟨ha2, r * g₁, ?_, ?_⟩
  · calc r * g₁ * b = r * (g₁ * b) := by group
      _ = r * (b * g₁) := by rw [hg₁b]
      _ = (r * b) * g₁ := by group
      _ = (b * r) * g₁ := by rw [hrb]
      _ = b * (r * g₁) := by group
  · calc r * g₁ * z * (r * g₁)⁻¹ = r * (g₁ * z * g₁⁻¹) * r⁻¹ := by group
      _ = b * z := hr
      _ = z * b := hzb.symm

end Conj

section Lift

variable {N : Type} [Group N] [Finite N]

theorem diag_centralizes_oddCore' {O B : Subgroup N} [O.Normal] (hOodd : Odd (Nat.card O))
    {z : N} (hz : z * z = 1) (hCzB : ∀ u ∈ O, z * u * z⁻¹ = u → ∀ b ∈ B, u * b = b * u)
    {K : Subgroup (N ⧸ O)} (hKc : center K = ⊥)
    (hKK : ∀ a ∈ K, ∀ c ∈ K, a * ((z : N ⧸ O) * c * (z : N ⧸ O)⁻¹) =
      ((z : N ⧸ O) * c * (z : N ⧸ O)⁻¹) * a)
    (hBz : ∀ b ∈ B, z * b * z⁻¹ = b)
    (hB : ∀ g : N ⧸ O, g ∈ B.map (QuotientGroup.mk' O) ↔
      ∃ k ∈ K, g = k * ((z : N ⧸ O) * k * (z : N ⧸ O)⁻¹))
    {b₀ : N} (hb₀B : b₀ ∈ B) (hb₀2 : b₀ * b₀ = 1) (hb₀1 : b₀ ≠ 1)
    (hb₀N : ∀ M : Subgroup N, (∀ b ∈ B, ∀ m ∈ M, b * m * b⁻¹ ∈ M) → b₀ ∈ M → B ≤ M) :
    ∀ b ∈ B, ∀ u ∈ O, b * u = u * b := by
  have hOodd' : ∀ x ∈ O, Odd (orderOf x) := fun x hx =>
    hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)
  have hzb₀ : z * b₀ = b₀ * z := by
    calc z * b₀ = (z * b₀ * z⁻¹) * z := by group
      _ = b₀ * z := by rw [hBz b₀ hb₀B]
  have hb₀O : ∀ u ∈ O, u * b₀ = b₀ * u := by
    by_cases hz1 : z = 1
    · intro u hu
      exact hCzB u hu (by rw [hz1]; group) b₀ hb₀B
    obtain ⟨a, ha, hab⟩ := (hB (b₀ : N ⧸ O)).1 ⟨b₀, hb₀B, rfl⟩
    obtain ⟨ha2, g, hgb, hgz⟩ := sq_eq_one_and_exists_conj' hOodd' hz hb₀2 hzb₀ hKc hKK ha hab
    have hbz : b₀ ≠ z := by
      intro hbz
      rw [hbz] at hab
      have h3 : a * (z : N ⧸ O) * a = 1 := by
        calc a * (z : N ⧸ O) * a = (a * ((z : N ⧸ O) * a * (z : N ⧸ O)⁻¹)) * (z : N ⧸ O) := by
              group
          _ = (z : N ⧸ O) * (z : N ⧸ O) := by rw [← hab]
          _ = 1 := by rw [← QuotientGroup.mk_mul, hz, QuotientGroup.mk_one]
      have h2 : (z : N ⧸ O) = 1 := by
        calc (z : N ⧸ O) = a⁻¹ * (a * (z : N ⧸ O) * a) * a⁻¹ := by group
          _ = (a * a)⁻¹ := by rw [h3]; group
          _ = 1 := by rw [ha2, inv_one]
      have hzO : z ∈ O := (QuotientGroup.eq_one_iff z).1 h2
      have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
      have h4 := hOodd' z hzO
      rw [hzo] at h4
      exact (Nat.not_odd_iff_even.2 even_two) h4
    exact AltStdCycTwo.StageM.commute_of_conj_four hOodd hz hb₀2 hzb₀ hz1 hb₀1 hbz hgb hgz
      (fun u hu hzu => hCzB u hu hzu b₀ hb₀B)
  have hle : B ≤ centralizer (O : Set N) := by
    refine hb₀N _ (fun b _ m hm => ?_) (mem_centralizer_iff.2 fun u hu => hb₀O u hu)
    exact (inferInstance : (centralizer (O : Set N)).Normal).conj_mem m hm b
  intro b hb u hu
  exact (mem_centralizer_iff.1 (hle hb) u hu).symm

theorem exists_wreath_lift_weak' {O B : Subgroup N} [O.Normal] (hOodd : Odd (Nat.card O))
    {z : N} (hz : z * z = 1) (hCzB : ∀ u ∈ O, z * u * z⁻¹ = u → ∀ b ∈ B, u * b = b * u)
    {K : Subgroup (N ⧸ O)} (hKc : center K = ⊥) (hKperf : ⁅K, K⁆ = K)
    (hKcov : OddCoversTrivial K)
    (hKK : ∀ a ∈ K, ∀ c ∈ K, a * ((z : N ⧸ O) * c * (z : N ⧸ O)⁻¹) =
      ((z : N ⧸ O) * c * (z : N ⧸ O)⁻¹) * a)
    (hBperf : ⁅B, B⁆ = B) (hBz : ∀ b ∈ B, z * b * z⁻¹ = b)
    (hB : ∀ g : N ⧸ O, g ∈ B.map (QuotientGroup.mk' O) ↔
      ∃ k ∈ K, g = k * ((z : N ⧸ O) * k * (z : N ⧸ O)⁻¹))
    {b₀ : N} (hb₀B : b₀ ∈ B) (hb₀2 : b₀ * b₀ = 1) (hb₀1 : b₀ ≠ 1)
    (hb₀N : ∀ M : Subgroup N, (∀ b ∈ B, ∀ m ∈ M, b * m * b⁻¹ ∈ M) → b₀ ∈ M → B ≤ M) :
    ∃ (Q : Subgroup N) (ψ : B →* N), Q.map (QuotientGroup.mk' O) = K ∧ ⁅Q, Q⁆ = Q ∧
      Q ⊓ O = ⊥ ∧ (∀ q ∈ Q, ∀ u ∈ O, q * u = u * q) ∧
      (∀ a ∈ Q, ∀ x ∈ zConjSub z Q, a * x = x * a) ∧ Q ⊓ zConjSub z Q = ⊥ ∧ (∀ b, ψ b ∈ Q) ∧
      Function.Injective ψ ∧ (∀ b, ψ b * (z * ψ b * z⁻¹) = b) := by
  classical
  have hBO : ∀ b ∈ B, ∀ u ∈ O, b * u = u * b :=
    diag_centralizes_oddCore' hOodd hz hCzB hKc hKK hBz hB hb₀B hb₀2 hb₀1 hb₀N
  set π : N →* N ⧸ O := QuotientGroup.mk' O with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hDbar : ((centralizer (O : Set N)).map π).Normal :=
    (inferInstance : (centralizer (O : Set N)).Normal).map π hπsurj
  have hBD : B.map π ≤ (centralizer (O : Set N)).map π :=
    Subgroup.map_mono fun b hb => mem_centralizer_iff.2 fun u hu => (hBO b hb u hu).symm
  have hKD : K ≤ (centralizer (O : Set N)).map π := by
    refine le_of_comm_mem hKperf fun k₁ hk₁ k₂ hk₂ => ?_
    have hd : k₂ * ((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹) ∈ (centralizer (O : Set N)).map π :=
      hBD ((hB _).2 ⟨k₂, hk₂, rfl⟩)
    have hc := hKK k₁ hk₁ k₂ hk₂
    have h1 : k₁ * k₂ * k₁⁻¹ * k₂⁻¹ =
        (k₁ * (k₂ * ((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹)) * k₁⁻¹) *
          (k₂ * ((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹))⁻¹ := by
      calc k₁ * k₂ * k₁⁻¹ * k₂⁻¹
          = k₁ * k₂ * (k₁⁻¹ * (((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹) * k₁)) * k₁⁻¹ *
              ((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹)⁻¹ * k₂⁻¹ := by group
        _ = k₁ * k₂ * (k₁⁻¹ * (k₁ * ((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹))) * k₁⁻¹ *
              ((z : N ⧸ O) * k₂ * (z : N ⧸ O)⁻¹)⁻¹ * k₂⁻¹ := by rw [← hc]
        _ = _ := by group
    rw [h1]
    exact mul_mem (hDbar.conj_mem _ hd k₁) (inv_mem hd)
  obtain ⟨Q₀, hQ₀map, hQ₀perf⟩ := exists_perfect_lift
    (π.comp (centralizer (O : Set N)).subtype) K hKperf
    (by rw [MonoidHom.range_comp, Subgroup.range_subtype]; exact hKD)
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup N, Q = Q₀.map (centralizer (O : Set N)).subtype :=
    ⟨_, rfl⟩
  have hQmap : Q.map π = K := by rw [hQdef, Subgroup.map_map]; exact hQ₀map
  have hQperf : ⁅Q, Q⁆ = Q := by rw [hQdef, ← Subgroup.map_commutator, hQ₀perf]
  have hQO : ∀ q ∈ Q, ∀ u ∈ O, q * u = u * q := by
    intro q hq u hu
    rw [hQdef] at hq
    obtain ⟨q', -, rfl⟩ := hq
    exact (mem_centralizer_iff.1 q'.2 u hu).symm
  have hQz : ∀ a ∈ Q, ∀ b ∈ Q, a * (z * b * z⁻¹) * a⁻¹ * (z * b * z⁻¹)⁻¹ ∈ O := by
    intro a ha b hb
    have haK : π a ∈ K := hQmap ▸ ⟨a, ha, rfl⟩
    have hbK : π b ∈ K := hQmap ▸ ⟨b, hb, rfl⟩
    rw [← QuotientGroup.eq_one_iff]
    show π (a * (z * b * z⁻¹) * a⁻¹ * (z * b * z⁻¹)⁻¹) = 1
    have := hKK _ haK _ hbK
    simp only [map_mul, map_inv]
    rw [show π z = (z : N ⧸ O) from rfl]
    rw [this]; group
  have hQQz := perfect_commute_zConjSub hQperf hQO hQz
  have hQbot : Q ⊓ O = ⊥ := by
    let πQ : ↥Q →* ↥K := (π.comp Q.subtype).codRestrict K (fun q => by
      rw [← hQmap]; exact ⟨q, q.2, rfl⟩)
    have hπQ : Function.Surjective πQ := by
      intro k
      have h1 : (k : N ⧸ O) ∈ Q.map π := by rw [hQmap]; exact k.2
      obtain ⟨q, hq, hqk⟩ := h1
      exact ⟨⟨q, hq⟩, Subtype.ext hqk⟩
    have hker_le : ∀ q : ↥Q, q ∈ πQ.ker → (q : N) ∈ O := by
      intro q hq
      have h3 : π q = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hq)
      exact (QuotientGroup.eq_one_iff (q : N)).1 h3
    have hZc : πQ.ker ≤ Subgroup.center ↥Q := by
      intro q hq
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact hQO g g.2 q (hker_le q hq)
    have hodd' : Odd (Nat.card πQ.ker) := by
      let ι : πQ.ker →* O := MonoidHom.codRestrict ((Q.subtype).comp πQ.ker.subtype) O
        (fun q => hker_le q.1 q.2)
      have hι : Function.Injective ι := by
        intro a b hab
        have h1 : ((ι a : O) : N) = ((ι b : O) : N) := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h1)
      exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_injective ι hι)
    have hperfQ : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQperf
    have hbot := hKcov ↥Q hperfQ πQ hπQ hZc hodd'
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxO⟩ := hx
    have hxk : (⟨x, hxQ⟩ : ↥Q) ∈ πQ.ker :=
      MonoidHom.mem_ker.2 (Subtype.ext ((QuotientGroup.eq_one_iff x).2 hxO))
    rw [hbot] at hxk
    have := congrArg Subtype.val (Subgroup.mem_bot.1 hxk)
    exact Subgroup.mem_bot.2 this
  have hQQzbot : Q ⊓ zConjSub z Q = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgQ, hgz⟩ := hg
    have hπg : π g ∈ K := hQmap ▸ ⟨g, hgQ, rfl⟩
    have hcen : (⟨π g, hπg⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      obtain ⟨q, hq, hqk⟩ : (k : N ⧸ O) ∈ Q.map π := by rw [hQmap]; exact k.2
      apply Subtype.ext
      show (k : N ⧸ O) * π g = π g * k
      rw [← hqk, ← map_mul, ← map_mul, hQQz q hq g hgz]
    rw [hKc] at hcen
    have h1 : π g = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hcen)
    have hgO : g ∈ O := (QuotientGroup.eq_one_iff g).1 h1
    have : g ∈ Q ⊓ O := ⟨hgQ, hgO⟩
    rwa [hQbot] at this
  let πQ : ↥Q →* ↥K := (π.comp Q.subtype).codRestrict K (fun q => by
    rw [← hQmap]; exact ⟨q, q.2, rfl⟩)
  have hπQbij : Function.Bijective πQ := by
    constructor
    · intro a b hab
      have h1 : π (a : N) = π (b : N) := congrArg Subtype.val hab
      have h2 : ((a : N)⁻¹ * (b : N)) ∈ O := by
        rw [← QuotientGroup.eq_one_iff]
        show π ((a : N)⁻¹ * (b : N)) = 1
        rw [map_mul, map_inv, h1]; group
      have h3 : ((a : N)⁻¹ * (b : N)) ∈ Q ⊓ O := ⟨Q.mul_mem (Q.inv_mem a.2) b.2, h2⟩
      rw [hQbot] at h3
      have h4 : (a : N)⁻¹ * (b : N) = 1 := h3
      exact Subtype.ext (inv_mul_eq_one.1 h4)
    · intro k
      have h1 : (k : N ⧸ O) ∈ Q.map π := by rw [hQmap]; exact k.2
      obtain ⟨q, hq, hqk⟩ := h1
      exact ⟨⟨q, hq⟩, Subtype.ext hqk⟩
  let eQ : ↥Q ≃* ↥K := MulEquiv.ofBijective πQ hπQbij
  set zq : N ⧸ O := (z : N ⧸ O) with hzq
  let δ : ↥K →* N ⧸ O := MonoidHom.mk' (fun k => (k : N ⧸ O) * (zq * k * zq⁻¹)) (fun a b => by
    have hc : (b : N ⧸ O) * (zq * (a : N ⧸ O) * zq⁻¹) = (zq * (a : N ⧸ O) * zq⁻¹) * b :=
      hKK b b.2 a a.2
    show ((a * b : ↥K) : N ⧸ O) * (zq * ((a * b : ↥K) : N ⧸ O) * zq⁻¹) =
      ((a : N ⧸ O) * (zq * a * zq⁻¹)) * ((b : N ⧸ O) * (zq * b * zq⁻¹))
    rw [Subgroup.coe_mul]
    calc ((a : N ⧸ O) * b) * (zq * ((a : N ⧸ O) * b) * zq⁻¹)
        = (a : N ⧸ O) * ((b : N ⧸ O) * (zq * a * zq⁻¹)) * (zq * b * zq⁻¹) := by group
      _ = (a : N ⧸ O) * ((zq * a * zq⁻¹) * b) * (zq * b * zq⁻¹) := by rw [hc]
      _ = ((a : N ⧸ O) * (zq * a * zq⁻¹)) * ((b : N ⧸ O) * (zq * b * zq⁻¹)) := by group)
  have hδinj : Function.Injective δ := by
    intro a b hab
    have hker : ∀ k : ↥K, δ k = 1 → k = 1 := by
      intro k hk
      have h1 : (k : N ⧸ O) * (zq * k * zq⁻¹) = 1 := hk
      have h2 : zq * (k : N ⧸ O) * zq⁻¹ = (k : N ⧸ O)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have hcen : k ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        have := hKK g g.2 k k.2
        rw [h2] at this
        show (g : N ⧸ O) * k = k * g
        have h3 : (g : N ⧸ O) * (k : N ⧸ O)⁻¹ = (k : N ⧸ O)⁻¹ * g := this
        calc (g : N ⧸ O) * k = k * ((k : N ⧸ O)⁻¹ * g) * k := by group
          _ = k * ((g : N ⧸ O) * (k : N ⧸ O)⁻¹) * k := by rw [← h3]
          _ = k * g := by group
      rw [hKc] at hcen
      exact hcen
    have : δ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    exact inv_mul_eq_one.1 (hker _ this)
  have hδrange : δ.range = B.map π := by
    ext g
    rw [hB]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  let eδ : ↥K ≃* ↥δ.range := MonoidHom.ofInjective hδinj
  let πB : ↥B →* ↥δ.range := (π.comp B.subtype).codRestrict δ.range (fun b => by
    rw [hδrange]; exact ⟨b, b.2, rfl⟩)
  let κ : ↥B →* ↥K := eδ.symm.toMonoidHom.comp πB
  let ψ : ↥B →* N := Q.subtype.comp (eQ.symm.toMonoidHom.comp κ)
  have hπψ : ∀ b : ↥B, π (ψ b) = (κ b : N ⧸ O) := by
    intro b
    have h1 : πQ (eQ.symm (κ b)) = κ b := eQ.apply_symm_apply (κ b)
    exact congrArg Subtype.val h1
  have hδκ : ∀ b : ↥B, δ (κ b) = π b := by
    intro b
    have h1 : eδ (κ b) = πB b := eδ.apply_symm_apply (πB b)
    exact congrArg Subtype.val h1
  have hψQ : ∀ b : ↥B, ψ b ∈ Q := fun b => (eQ.symm (κ b)).2
  have hcomm : ∀ a b : ↥B, ψ a * (z * ψ b * z⁻¹) = (z * ψ b * z⁻¹) * ψ a := fun a b =>
    hQQz _ (hψQ a) _ (mem_zConjSub.2 ⟨ψ b, hψQ b, rfl⟩)
  let xh : ↥B →* N := MonoidHom.mk' (fun b => ψ b * (z * ψ b * z⁻¹)) (fun a b => by
    have hc := hcomm b a
    show ψ (a * b) * (z * ψ (a * b) * z⁻¹) =
      (ψ a * (z * ψ a * z⁻¹)) * (ψ b * (z * ψ b * z⁻¹))
    rw [map_mul]
    calc ψ a * ψ b * (z * (ψ a * ψ b) * z⁻¹)
        = ψ a * (ψ b * (z * ψ a * z⁻¹)) * (z * ψ b * z⁻¹) := by group
      _ = ψ a * ((z * ψ a * z⁻¹) * ψ b) * (z * ψ b * z⁻¹) := by rw [hc]
      _ = (ψ a * (z * ψ a * z⁻¹)) * (ψ b * (z * ψ b * z⁻¹)) := by group)
  have hxπ : ∀ b : ↥B, π (xh b) = π b := by
    intro b
    show π (ψ b * (z * ψ b * z⁻¹)) = π b
    rw [map_mul, map_mul, map_mul, map_inv, hπψ]
    exact hδκ b
  have hxO : ∀ b : ↥B, ∀ u ∈ O, Commute (xh b) u := by
    intro b u hu
    have h1 : Commute (ψ b) u := hQO (ψ b) (hψQ b) u hu
    have h2 : Commute (z * ψ b * z⁻¹) u :=
      zConjSub_centralizes (z := z) hQO _ (mem_zConjSub.2 ⟨ψ b, hψQ b, rfl⟩) u hu
    exact h1.mul_left h2
  have hdef : ∀ b : ↥B, ∃ w ∈ O, (∀ u ∈ O, Commute w u) ∧ xh b = (b : N) * w := by
    intro b
    refine ⟨(b : N)⁻¹ * xh b, ?_, fun u hu => ?_, by group⟩
    · rw [← QuotientGroup.eq_one_iff]
      show π ((b : N)⁻¹ * xh b) = 1
      rw [map_mul, map_inv, hxπ]; group
    · exact (Commute.inv_left (show Commute (b : N) u from hBO b b.2 u hu)).mul_left (hxO b u hu)
  have hT : B ≤ (MonoidHom.eqLocus xh B.subtype).map B.subtype := by
    refine le_of_comm_mem hBperf (fun a ha c hc => ?_)
    refine ⟨⟨a, ha⟩ * ⟨c, hc⟩ * ⟨a, ha⟩⁻¹ * ⟨c, hc⟩⁻¹, ?_, rfl⟩
    show xh (⟨a, ha⟩ * ⟨c, hc⟩ * ⟨a, ha⟩⁻¹ * ⟨c, hc⟩⁻¹) = a * c * a⁻¹ * c⁻¹
    obtain ⟨wa, hwaO, hwac, hwa⟩ : ∃ w ∈ O, (∀ u ∈ O, Commute w u) ∧ xh ⟨a, ha⟩ = a * w :=
      hdef ⟨a, ha⟩
    obtain ⟨wc, hwcO, -, hwc⟩ : ∃ w ∈ O, (∀ u ∈ O, Commute w u) ∧ xh ⟨c, hc⟩ = c * w :=
      hdef ⟨c, hc⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hwa, hwc]
    exact comm_mul_of_commute (hBO c hc wa hwaO).symm (hwac wc hwcO) (hBO a ha wc hwcO).symm
  have hxeq : ∀ b : ↥B, xh b = (b : N) := by
    intro b
    obtain ⟨b', hb', hbb⟩ := hT b.2
    have : b' = b := Subtype.ext hbb
    rw [← this]; exact hb'
  refine ⟨Q, ψ, hQmap, hQperf, hQbot, hQO, hQQz, hQQzbot, hψQ, ?_, ?_⟩
  · intro a b hab
    have h1 : xh a = xh b := by
      show ψ a * (z * ψ a * z⁻¹) = ψ b * (z * ψ b * z⁻¹)
      rw [hab]
    rw [hxeq a, hxeq b] at h1
    exact Subtype.ext h1
  · intro b
    exact hxeq b

end Lift

end CFSG.OddStandard.AltStdSmall4.W49
