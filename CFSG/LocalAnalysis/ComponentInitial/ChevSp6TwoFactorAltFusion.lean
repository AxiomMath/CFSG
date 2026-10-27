module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverLift
public import CFSG.CharacterTheory.Wreathed.OddNormalQuotientInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXSp6TensorModel

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor

open Subgroup CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (Mat3)
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModel

section Fusion

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H} [V.Normal]
  (hV2 : ∀ v ∈ V, v * v = 1) (ω : H →* Ehat) (hω : Function.Surjective ω) (hωker : ω.ker = V)
  (μ : V → Mat3) (hμinj : Function.Injective μ) (hμadd : ∀ v w : V, μ (v * w) = μ v + μ w)
  (hμeq : ∀ (h : H) (v : V), μ ⟨h * v * h⁻¹, (inferInstance : V.Normal).conj_mem _ v.2 h⟩ =
    repE (ω h) (μ v))

abbrev cosetInv (u : H) : Set H := {x | x * x = 1 ∧ ω x = ω u}

omit [Finite H] in
include hV2 hωker hμinj hμeq in
theorem card_cosetInv_le {u : H} (hu : u * u = 1) :
    Nat.card (cosetInv ω u) ≤ Nat.card (FixM {ω u}) := by
  have hmem : ∀ x ∈ cosetInv ω u, x * u⁻¹ ∈ V := fun x hx => by
    rw [← hωker, MonoidHom.mem_ker, map_mul, map_inv, hx.2, mul_inv_cancel]
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hfix : ∀ x (hx : x ∈ cosetInv ω u), repE (ω u) (μ ⟨_, hmem x hx⟩) = μ ⟨_, hmem x hx⟩ := by
    intro x hx
    rw [← hμeq]
    congr 2
    have hv2 : x * u⁻¹ * (x * u⁻¹) = 1 := hV2 _ (hmem x hx)
    have hx2 : x * x = 1 := hx.1
    change u * (x * u⁻¹) * u⁻¹ = x * u⁻¹
    rw [huinv] at hv2 ⊢
    have key : u * x * u = x := by
      calc u * x * u = x⁻¹ * (x * u * (x * u)) := by group
        _ = x := by rw [hv2, mul_one, inv_eq_of_mul_eq_one_right hx2]
    calc u * (x * u) * u = u * x * u * u := by group
      _ = x * u := by rw [key]
  refine Nat.card_le_card_of_injective (fun x => ⟨μ ⟨_, hmem x.1 x.2⟩, fun b hb => ?_⟩) ?_
  · rw [Set.mem_singleton_iff] at hb
    subst hb
    exact hfix x.1 x.2
  · intro x y h
    have h1 := hμinj (congrArg Subtype.val h)
    have h2 : (x : H) * u⁻¹ = y * u⁻¹ := congrArg Subtype.val h1
    exact Subtype.ext (mul_right_cancel h2)

end Fusion

section Orbit

variable {H : Type*} [Group H]

theorem card_conjOrbit_mul_card_centralizer {M : Subgroup H} {u : H}
    (hCM : centralizer ({u} : Set H) ≤ M) :
    Nat.card {x : H // ∃ g ∈ M, g * u * g⁻¹ = x} * Nat.card (centralizer ({u} : Set H)) =
      Nat.card M := by
  classical
  let _ : MulAction M H := MulAction.compHom H ((MulAut.conj : H →* MulAut H).comp M.subtype)
  have hsmul : ∀ (g : M) (x : H), g • x = (g : H) * x * (g : H)⁻¹ := fun g x => rfl
  have horb : MulAction.orbit M u = {x : H | ∃ g ∈ M, g * u * g⁻¹ = x} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, (hsmul g u).symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, hsmul _ u⟩
  have hstab : MulAction.stabilizer M u = (centralizer ({u} : Set H)).subgroupOf M := by
    ext g
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc (g : H) * u = (g : H) * u * (g : H)⁻¹ * g := by group
        _ = u * g := by rw [h]
    · intro h
      rw [h]
      group
  have hcard : Nat.card (MulAction.stabilizer M u) = Nat.card (centralizer ({u} : Set H)) := by
    rw [hstab]
    exact Nat.card_congr (subgroupOfEquivOfLe hCM).toEquiv
  have h1 : Nat.card {x : H // ∃ g ∈ M, g * u * g⁻¹ = x} = Nat.card (MulAction.orbit M u) := by
    rw [horb]
    rfl
  rw [h1, ← hcard, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer M u)]
  exact (MulAction.stabilizer M u).index_mul_card

end Orbit

section Main

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H} [V.Normal]
  (hV2 : ∀ v ∈ V, v * v = 1) (ω : H →* Ehat) (hω : Function.Surjective ω) (hωker : ω.ker = V)
  (hVcard : Nat.card V = 512)
  (μ : V → Mat3) (hμinj : Function.Injective μ) (hμadd : ∀ v w : V, μ (v * w) = μ v + μ w)
  (hμeq : ∀ (h : H) (v : V), μ ⟨h * v * h⁻¹, (inferInstance : V.Normal).conj_mem _ v.2 h⟩ =
    repE (ω h) (μ v))

omit [V.Normal] in
include hω hωker hVcard in
theorem card_comap_centralizer (u : H) :
    Nat.card ((centralizer ({ω u} : Set Ehat)).comap ω) =
      Nat.card (centralizer ({ω u} : Set Ehat)) * 512 := by
  rw [FieldFourCover.card_comap_of_surjective hω, hωker, hVcard]

omit [Finite H] in
theorem centralizer_le_comap (u : H) :
    centralizer ({u} : Set H) ≤ (centralizer ({ω u} : Set Ehat)).comap ω := fun x hx => by
  rw [mem_comap, mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    mem_centralizer_singleton_iff.1 hx]

omit [Finite H] in
theorem conjOrbit_subset (u : H) (hu : u * u = 1) :
    ∀ x, (∃ g ∈ (centralizer ({ω u} : Set Ehat)).comap ω, g * u * g⁻¹ = x) →
      x ∈ cosetInv ω u := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨by rw [show g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ by group, hu]; group, ?_⟩
  have hc : ω g * ω u = ω u * ω g := mem_centralizer_singleton_iff.1 hg
  rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]

include hV2 hω hωker hVcard hμinj hμeq in
theorem two_pow_eleven_dvd_of_tt {u : H} (hu : u * u = 1)
    (hωu : ω u = SemidirectProduct.inl ((tS, tS) : K)) :
    2 ^ 11 ∣ Nat.card (centralizer ({u} : Set H)) := by
  set M := (centralizer ({ω u} : Set Ehat)).comap ω with hM
  have hMcard : Nat.card M = 2 ^ 16 := by
    rw [hM, card_comap_centralizer ω hω hωker hVcard, hωu, card_centralizer_tt]
    norm_num
  have horb := card_conjOrbit_mul_card_centralizer (centralizer_le_comap ω u)
  rw [← hM, hMcard] at horb
  have hO : Nat.card {x : H // ∃ g ∈ M, g * u * g⁻¹ = x} ≤ 32 := by
    refine (Nat.card_le_card_of_injective (fun x => (⟨x.1, conjOrbit_subset ω u hu x.1 x.2⟩ :
      cosetInv ω u)) fun x y h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext h').trans ?_
    refine (card_cosetInv_le hV2 ω hωker μ hμinj hμeq hu).trans ?_
    rw [hωu]
    exact card_fixM_tt
  have hdvd : Nat.card (centralizer ({u} : Set H)) ∣ 2 ^ 16 := Dvd.intro_left _ horb
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hj] at horb ⊢
  apply pow_dvd_pow 2
  by_contra hlt
  push Not at hlt
  have h1 : 2 ^ j ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : Nat.card {x : H // ∃ g ∈ M, g * u * g⁻¹ = x} * 2 ^ j ≤ 32 * 2 ^ 10 :=
    Nat.mul_le_mul hO h1
  omega

include hV2 hω hωker hVcard hμinj hμadd hμeq in
theorem not_two_part_ten_of_t1 {u : H} (hu : u * u = 1)
    (hωu : ω u = SemidirectProduct.inl ((tS, 1) : K)) :
    ¬ (2 ^ 10 ∣ Nat.card (centralizer ({u} : Set H)) ∧
      ¬ 2 ^ 11 ∣ Nat.card (centralizer ({u} : Set H))) := by
  classical
  rintro ⟨h10, h11⟩
  set M := (centralizer ({ω u} : Set Ehat)).comap ω with hM
  have hMcard : Nat.card M = 688128 := by
    rw [hM, card_comap_centralizer ω hω hωker hVcard, hωu, card_centralizer_t1]
  have horb := card_conjOrbit_mul_card_centralizer (centralizer_le_comap ω u)
  rw [← hM, hMcard] at horb
  set O := {x : H // ∃ g ∈ M, g * u * g⁻¹ = x} with hO
  have hOle : Nat.card O ≤ 64 := by
    refine (Nat.card_le_card_of_injective (fun x => (⟨x.1, conjOrbit_subset ω u hu x.1 x.2⟩ :
      cosetInv ω u)) fun x y h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext h').trans ?_
    refine (card_cosetInv_le hV2 ω hωker μ hμinj hμeq hu).trans ?_
    rw [hωu]
    exact card_fixM_t1
  have hO32 : Nat.card O = 32 := by
    obtain ⟨k, hk⟩ := h10
    rw [hk] at horb h11
    have hpos : 0 < Nat.card O := Nat.card_pos_iff.2 ⟨⟨⟨u, 1, one_mem _, by group⟩⟩, inferInstance⟩
    interval_cases hOc : Nat.card O <;> omega
  obtain ⟨c, hc⟩ := hω (SemidirectProduct.inl ((1, c7S) : K))
  set c₁ := c ^ 8 with hc₁
  have hω7 : (SemidirectProduct.inl ((1, c7S) : K) : Ehat) ^ 7 = 1 := by
    rw [← map_pow, show ((1, c7S) : K) ^ 7 = 1 from Prod.ext (one_pow 7) c7S_pow_seven, map_one]
  have hωc₁ : ω c₁ = SemidirectProduct.inl ((1, c7S) : K) := by
    rw [hc₁, map_pow, hc, show (8 : ℕ) = 7 + 1 from rfl, pow_succ, hω7, one_mul]
  have hc7V : c ^ 7 ∈ V := by
    rw [← hωker, MonoidHom.mem_ker, map_pow, hc, hω7]
  have hc₁7 : c₁ ^ 7 = 1 := by
    have h1 : c ^ 7 * c ^ 7 = 1 := hV2 _ hc7V
    calc c₁ ^ 7 = (c ^ 7 * c ^ 7) ^ 4 := by rw [hc₁, ← pow_mul, ← pow_add, ← pow_mul]
      _ = 1 := by rw [h1, one_pow]
  have hc₁M : c₁ ∈ M := by
    rw [hM, mem_comap, mem_centralizer_singleton_iff, hωc₁, hωu, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (by simp) (by simp)
  let f : Function.End O := fun x => ⟨c₁ * x.1 * c₁⁻¹, by
    obtain ⟨g, hg, hgx⟩ := x.2
    exact ⟨c₁ * g, mul_mem hc₁M hg, by rw [← hgx]; group⟩⟩
  have hfpow : ∀ (n : ℕ) (x : O), ((f ^ n) x).1 = c₁ ^ n * x.1 * (c₁ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [pow_zero, one_mul, inv_one, mul_one]
      rfl
    | succ n ih =>
      intro x
      rw [pow_succ']
      change c₁ * ((f ^ n) x).1 * c₁⁻¹ = _
      rw [ih, pow_succ']
      group
  have hf7 : f ^ 7 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    rw [pow_one, hfpow, hc₁7, one_mul, inv_one, mul_one]
    rfl
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fintype O := Fintype.ofFinite O
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 7) (n := 1) hf7
  rw [← Nat.card_eq_fintype_card, hO32] at hmod
  have hfix2 : 2 ≤ Fintype.card (Function.fixedPoints f) := by
    have h1 : Fintype.card (Function.fixedPoints f) % 7 = 4 := by
      unfold Nat.ModEq at hmod
      omega
    omega
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card
    (Function.fixedPoints f))
  have hp := conjOrbit_subset ω u hu p.1.1 p.1.2
  have hq := conjOrbit_subset ω u hu q.1.1 q.1.2
  have hpc : c₁ * p.1.1 = p.1.1 * c₁ := by
    have h1 := congrArg Subtype.val p.2
    change c₁ * p.1.1 * c₁⁻¹ = p.1.1 at h1
    calc c₁ * p.1.1 = c₁ * p.1.1 * c₁⁻¹ * c₁ := by group
      _ = p.1.1 * c₁ := by rw [h1]
  have hqc : c₁ * q.1.1 = q.1.1 * c₁ := by
    have h1 := congrArg Subtype.val q.2
    change c₁ * q.1.1 * c₁⁻¹ = q.1.1 at h1
    calc c₁ * q.1.1 = c₁ * q.1.1 * c₁⁻¹ * c₁ := by group
      _ = q.1.1 * c₁ := by rw [h1]
  have hvV : q.1.1 * (p.1.1)⁻¹ ∈ V := by
    rw [← hωker, MonoidHom.mem_ker, map_mul, map_inv, hq.2, hp.2, mul_inv_cancel]
  set v : V := ⟨_, hvV⟩ with hv
  have hpinv : (p.1.1)⁻¹ = p.1.1 := inv_eq_of_mul_eq_one_right hp.1
  have hqinv : (q.1.1)⁻¹ = q.1.1 := inv_eq_of_mul_eq_one_right hq.1
  have hv2 : q.1.1 * (p.1.1)⁻¹ * (q.1.1 * (p.1.1)⁻¹) = 1 := hV2 _ hvV
  have hpv : p.1.1 * (q.1.1 * (p.1.1)⁻¹) * (p.1.1)⁻¹ = q.1.1 * (p.1.1)⁻¹ := by
    rw [hpinv] at hv2 ⊢
    have hcomm : p.1.1 * q.1.1 = q.1.1 * p.1.1 := by
      calc p.1.1 * q.1.1 = (q.1.1)⁻¹ * (q.1.1 * p.1.1 * (q.1.1 * p.1.1)) * (p.1.1)⁻¹ := by group
        _ = q.1.1 * p.1.1 := by rw [hv2, mul_one, hqinv, hpinv]
    calc p.1.1 * (q.1.1 * p.1.1) * p.1.1 = p.1.1 * q.1.1 * (p.1.1 * p.1.1) := by group
      _ = q.1.1 * p.1.1 := by rw [hcomm, hp.1, mul_one]
  have hcv : c₁ * (q.1.1 * (p.1.1)⁻¹) * c₁⁻¹ = q.1.1 * (p.1.1)⁻¹ := by
    calc c₁ * (q.1.1 * (p.1.1)⁻¹) * c₁⁻¹ = (c₁ * q.1.1) * (c₁ * p.1.1)⁻¹ := by group
      _ = q.1.1 * (p.1.1)⁻¹ := by rw [hqc, hpc]; group
  have h1 : repE (SemidirectProduct.inl ((tS, 1) : K)) (μ v) = μ v := by
    rw [← hωu, ← hp.2, ← hμeq]
    congr 2
  have h2 : repE (SemidirectProduct.inl ((1, c7S) : K)) (μ v) = μ v := by
    rw [← hωc₁, ← hμeq]
    congr 2
  have h0 := eq_zero_of_fix_t1_c7 (μ v) h1 h2
  have hμ1 : μ 1 = 0 := by
    have := hμadd 1 1
    rw [mul_one] at this
    have h3 : μ 1 + μ 1 = μ 1 + 0 := by rw [← this, add_zero]
    exact (add_left_cancel h3)
  have hv1 : v = 1 := hμinj (h0.trans hμ1.symm)
  apply hpq
  apply Subtype.ext
  apply Subtype.ext
  have h4 : q.1.1 * (p.1.1)⁻¹ = 1 := congrArg Subtype.val hv1
  exact (mul_inv_eq_one.1 h4).symm

omit [Finite H] in
theorem card_centralizer_conj_eq (w f : H) :
    Nat.card (centralizer ({w * f * w⁻¹} : Set H)) = Nat.card (centralizer ({f} : Set H)) := by
  have h : centralizer ({w * f * w⁻¹} : Set H) =
      (centralizer ({f} : Set H)).map (MulAut.conj w).toMonoidHom := by
    ext x
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hx
      refine ⟨w⁻¹ * x * w, mem_centralizer_singleton_iff.2 ?_, by
        change w * (w⁻¹ * x * w) * w⁻¹ = x
        group⟩
      calc w⁻¹ * x * w * f = w⁻¹ * (x * (w * f * w⁻¹)) * w := by group
        _ = w⁻¹ * (w * f * w⁻¹ * x) * w := by rw [hx]
        _ = f * (w⁻¹ * x * w) := by group
    · rintro ⟨y, hy, rfl⟩
      have hy' := mem_centralizer_singleton_iff.1 hy
      change w * y * w⁻¹ * (w * f * w⁻¹) = w * f * w⁻¹ * (w * y * w⁻¹)
      calc w * y * w⁻¹ * (w * f * w⁻¹) = w * (y * f) * w⁻¹ := by group
        _ = w * (f * y) * w⁻¹ := by rw [hy']
        _ = w * f * w⁻¹ * (w * y * w⁻¹) := by group
  rw [h, Subgroup.card_map_of_injective (MulAut.conj w).injective]

include hV2 hω hωker hVcard hμinj hμadd hμeq in
theorem exact_two_part_ne_ten {u : H} (hu : u * u = 1) (huV : u ∉ V)
    (hur : (ω u).right = 1) :
    ¬ (2 ^ 10 ∣ Nat.card (centralizer ({u} : Set H)) ∧
      ¬ 2 ^ 11 ∣ Nat.card (centralizer ({u} : Set H))) := by
  set k := (ω u).left with hk
  have hωu : ω u = SemidirectProduct.inl k := SemidirectProduct.ext rfl hur
  have hk2 : k * k = 1 := SemidirectProduct.inl_injective (by
    rw [map_mul, ← hωu, ← map_mul, hu, map_one, map_one])
  have hk1 : k ≠ 1 := by
    intro h
    apply huV
    rw [← hωker, MonoidHom.mem_ker, hωu, h, map_one]
  obtain ⟨e, he⟩ := exists_conj_std hk2 hk1
  obtain ⟨w, rfl⟩ := hω e
  set u' := w * u * w⁻¹ with hu'
  have hu'2 : u' * u' = 1 := by
    rw [hu', show w * u * w⁻¹ * (w * u * w⁻¹) = w * (u * u) * w⁻¹ by group, hu, mul_one,
      mul_inv_cancel]
  have hωu' : ω u' = ω w * SemidirectProduct.inl k * (ω w)⁻¹ := by
    rw [hu', map_mul, map_mul, map_inv, hωu]
  rw [← card_centralizer_conj_eq w u]
  rcases he with he | he
  · exact not_two_part_ten_of_t1 hV2 ω hω hωker hVcard μ hμinj hμadd hμeq hu'2
      (hωu'.trans he)
  · rintro ⟨-, h11⟩
    exact h11 (two_pow_eleven_dvd_of_tt hV2 ω hω hωker hVcard μ hμinj hμeq hu'2
      (hωu'.trans he))

end Main

section OddKernel

variable {X : Type*} [Group X] [Finite X] {C N : Subgroup X} [C.Normal] [N.Normal]
  (hC2 : ∀ c ∈ C, c * c = 1) (hCcard : Nat.card C = 512) (hN : Odd (Nat.card N))
  (hCN : C ⊓ N = ⊥) (Ω : X →* Ehat) (hΩ : Function.Surjective Ω) (hΩker : Ω.ker = C ⊔ N)
  (μ : C → Mat3) (hμinj : Function.Injective μ) (hμadd : ∀ v w : C, μ (v * w) = μ v + μ w)
  (hμeq : ∀ (x : X) (c : C), μ ⟨x * c * x⁻¹, (inferInstance : C.Normal).conj_mem _ c.2 x⟩ =
    repE (Ω x) (μ c))

include hC2 hCcard hN hCN hΩ hΩker hμinj hμadd hμeq in
theorem exact_two_part_ne_ten_of_odd_kernel {u : X} (hu : u * u = 1) (huC : u ∉ C)
    (hur : (Ω u).right = 1) :
    ¬ (2 ^ 10 ∣ Nat.card (centralizer ({u} : Set X)) ∧
      ¬ 2 ^ 11 ∣ Nat.card (centralizer ({u} : Set X))) := by
  classical
  set π := QuotientGroup.mk' N with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hNle : N ≤ Ω.ker := hΩker ▸ le_sup_right
  set ω : X ⧸ N →* Ehat := QuotientGroup.lift N Ω hNle with hω
  have hωπ : ∀ x, ω (π x) = Ω x := fun x => rfl
  have hωsurj : Function.Surjective ω := fun e => by
    obtain ⟨x, rfl⟩ := hΩ e
    exact ⟨π x, rfl⟩
  set V := C.map π with hV
  have hVn : V.Normal := Subgroup.Normal.map inferInstance π hπsurj
  have hπinj : ∀ c ∈ C, ∀ d ∈ C, π c = π d → c = d := by
    intro c hc d hd h
    have h1 : c⁻¹ * d ∈ N := (QuotientGroup.eq).1 h
    have h2 : c⁻¹ * d ∈ C ⊓ N := mem_inf.2 ⟨mul_mem (inv_mem hc) hd, h1⟩
    rw [hCN, mem_bot] at h2
    exact (inv_mul_eq_one.1 h2)
  have hVcard : Nat.card V = 512 := by
    rw [hV, ← hCcard, ← SetLike.coe_sort_coe, Subgroup.coe_map,
      Nat.card_image_of_injOn (fun c hc d hd h => hπinj c hc d hd h), SetLike.coe_sort_coe]
  have hCNcomm : ∀ c ∈ C, ∀ n ∈ N, c * n = n * c := by
    intro c hc n hn
    have hC' : c * n * c⁻¹ * n⁻¹ ∈ C := by
      rw [show c * n * c⁻¹ * n⁻¹ = c * (n * c⁻¹ * n⁻¹) by group]
      exact mul_mem hc ((inferInstance : C.Normal).conj_mem _ (inv_mem hc) n)
    have hN' : c * n * c⁻¹ * n⁻¹ ∈ N :=
      mul_mem ((inferInstance : N.Normal).conj_mem _ hn c) (inv_mem hn)
    have h1 : c * n * c⁻¹ * n⁻¹ ∈ C ⊓ N := mem_inf.2 ⟨hC', hN'⟩
    rw [hCN, mem_bot] at h1
    calc c * n = c * n * c⁻¹ * n⁻¹ * (n * c) := by group
      _ = n * c := by rw [h1, one_mul]
  have hmemCN : ∀ x : X, x ∈ C ⊔ N ↔ ∃ c ∈ C, π c = π x := by
    intro x
    constructor
    · intro hx
      rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx
      obtain ⟨c, hc, n, hn, rfl⟩ := hx
      refine ⟨c, hc, (QuotientGroup.eq).2 ?_⟩
      rw [inv_mul_cancel_left]
      exact hn
    · rintro ⟨c, hc, h⟩
      have h1 : c⁻¹ * x ∈ N := (QuotientGroup.eq).1 h
      rw [show x = c * (c⁻¹ * x) by group]
      exact mul_mem_sup hc h1
  have hωker : ω.ker = V := by
    ext y
    obtain ⟨x, rfl⟩ := hπsurj y
    rw [MonoidHom.mem_ker, hωπ, ← MonoidHom.mem_ker, hΩker, hmemCN]
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨c, hc, h⟩
    · rintro ⟨c, hc, h⟩
      exact ⟨c, hc, h⟩
  have hV2 : ∀ v ∈ V, v * v = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    rw [← map_mul, hC2 c hc, map_one]
  let f₀ : C →* V := (π.comp C.subtype).codRestrict V fun c => ⟨c, c.2, rfl⟩
  have hf₀bij : Function.Bijective f₀ := by
    constructor
    · intro c d h
      exact Subtype.ext (hπinj c c.2 d d.2 (congrArg Subtype.val h))
    · rintro ⟨_, c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  set eC := MulEquiv.ofBijective f₀ hf₀bij with heC
  have heCapply : ∀ c : C, ((eC c : V) : X ⧸ N) = π c := fun c => rfl
  set μ' : V → Mat3 := fun v => μ (eC.symm v) with hμ'
  have hμ'inj : Function.Injective μ' := fun v w h => eC.symm.injective (hμinj h)
  have hμ'add : ∀ v w : V, μ' (v * w) = μ' v + μ' w := fun v w => by
    simp only [hμ', map_mul, hμadd]
  have hμ'eq : ∀ (h : X ⧸ N) (v : V), μ' ⟨h * v * h⁻¹, hVn.conj_mem _ v.2 h⟩ =
      repE (ω h) (μ' v) := by
    intro h v
    obtain ⟨x, rfl⟩ := hπsurj h
    obtain ⟨c, rfl⟩ := eC.surjective v
    have hxc : (⟨π x * ((eC c : V) : X ⧸ N) * (π x)⁻¹, hVn.conj_mem _ (eC c).2 (π x)⟩ : V) =
        eC ⟨x * c * x⁻¹, (inferInstance : C.Normal).conj_mem _ c.2 x⟩ := by
      apply Subtype.ext
      change π x * ((eC c : V) : X ⧸ N) * (π x)⁻¹ =
        ((eC ⟨x * c * x⁻¹, (inferInstance : C.Normal).conj_mem _ c.2 x⟩ : V) : X ⧸ N)
      rw [heCapply, heCapply, map_mul, map_mul, map_inv]
    change μ (eC.symm _) = repE (ω (π x)) (μ (eC.symm (eC c)))
    rw [hxc, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, hμeq, hωπ]
  have hu1 : u ≠ 1 := fun h => huC (h ▸ one_mem C)
  have huord : orderOf u = 2 := orderOf_eq_prime (by rw [sq, hu]) hu1
  have huV : π u ∉ V := by
    rintro ⟨c, hc, hcu⟩
    have hn : c⁻¹ * u ∈ N := (QuotientGroup.eq).1 hcu
    have hn2 : (c⁻¹ * u) * (c⁻¹ * u) = 1 := by
      have hcn := hCNcomm c hc _ hn
      calc (c⁻¹ * u) * (c⁻¹ * u) = c⁻¹ * (c * (c⁻¹ * u)) * (c⁻¹ * u) * c * c⁻¹ := by group
        _ = c⁻¹ * ((c⁻¹ * u) * c) * (c⁻¹ * u) * c * c⁻¹ := by rw [hcn]
        _ = (c * c)⁻¹ * (u * u) := by group
        _ = 1 := by rw [hC2 c hc, hu, inv_one, one_mul]
    have hn1 : c⁻¹ * u = 1 := by
      have hodd : Odd (orderOf (c⁻¹ * u)) := by
        have h1 : orderOf (⟨c⁻¹ * u, hn⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk] at h1
        exact Odd.of_dvd_nat hN h1
      have h2 : orderOf (c⁻¹ * u) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hn2])
      have h3 : orderOf (c⁻¹ * u) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
        · exact h
        · rw [h] at hodd
          exact absurd hodd (by decide)
      exact orderOf_eq_one_iff.1 h3
    apply huC
    rw [show u = c * (c⁻¹ * u) by group, hn1, mul_one]
    exact hc
  have hAFL := exact_two_part_ne_ten hV2 ω hωsurj hωker hVcard μ' hμ'inj hμ'add hμ'eq
    (u := π u) (by rw [← map_mul, hu, map_one]) huV (by rw [hωπ]; exact hur)
  have hcard := CFSG.Wreathed.OddNormalQuotientInvolutions.centralizer_card N hN u huord
  set a := Nat.card (CFSG.Wreathed.OddNormalQuotientInvolutions.kernelCentralizer N u) with ha
  have haodd : Odd a := by
    have h1 : a ∣ Nat.card N := Subgroup.card_subgroup_dvd_card _
    exact Odd.of_dvd_nat hN h1
  rintro ⟨h10, h11⟩
  apply hAFL
  rw [hcard] at h10 h11
  refine ⟨?_, fun h => h11 (Dvd.dvd.mul_left h a)⟩
  have hcop : Nat.Coprime (2 ^ 10) a := Nat.Coprime.pow_left 10 (Nat.coprime_two_left.2 haodd)
  exact hcop.dvd_of_dvd_mul_left h10

end OddKernel

end CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor
