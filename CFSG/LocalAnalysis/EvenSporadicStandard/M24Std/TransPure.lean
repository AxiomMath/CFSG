module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Trans

theorem card_modEq_card_fix {W : Subgroup G} {x : G} {p : ℕ} [Fact p.Prime]
    (hx : x ^ p = 1) (hn : ∀ v ∈ W, x * v * x⁻¹ ∈ W) :
    Nat.card W ≡ Nat.card {v : W | x * (v : G) * x⁻¹ = v} [MOD p] := by
  classical
  have := Fintype.ofFinite W
  let f : Function.End W := fun v => ⟨x * v * x⁻¹, hn v v.2⟩
  have hfk : ∀ k : ℕ, ∀ v : W, ((f ^ k) v : G) = x ^ k * v * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero =>
      intro v
      show (v : G) = x ^ 0 * v * (x ^ 0)⁻¹
      simp
    | succ k ih =>
      intro v
      rw [pow_succ]
      show (((f ^ k) (f v) : W) : G) = _
      rw [ih, pow_succ]
      show x ^ k * (x * v * x⁻¹) * (x ^ k)⁻¹ = _
      group
  have hf : f ^ p ^ 1 = 1 := by
    funext v
    apply Subtype.ext
    show (((f ^ p ^ 1) v : W) : G) = (v : G)
    rw [pow_one, hfk, hx]
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card] at hmod
  have hset : Function.fixedPoints f = {v : W | x * (v : G) * x⁻¹ = v} := by
    ext v
    exact Subtype.ext_iff
  rw [hset] at hmod
  exact hmod

theorem card_eq_four_or_of_invariant {A W : Subgroup G} {r : G} (hA : Nat.card A = 64)
    (hr : r ^ 5 = 1) (hfix : {c : G | c ∈ A ∧ r * c * r⁻¹ = c}.ncard = 4) (hWA : W ≤ A)
    (hrW : ∀ w ∈ W, r * w * r⁻¹ ∈ W) (hCW : ∀ c ∈ A, r * c * r⁻¹ = c → c ∈ W) :
    Nat.card W = 4 ∨ Nat.card W = 64 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmod := card_modEq_card_fix hr hrW
  have h4 : Nat.card {v : W | r * (v : G) * r⁻¹ = v} = 4 := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_image_of_injective _ Subtype.val_injective, ← hfix]
    congr 1
    ext c
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hWA v.2, hv⟩
    · rintro ⟨hc, hrc⟩
      exact ⟨⟨c, hCW c hc hrc⟩, hrc, rfl⟩
  rw [h4] at hmod
  have hdvd : Nat.card W ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← hA]
    exact Subgroup.card_dvd_of_le hWA
  obtain ⟨i, hi, hWi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hWi] at hmod ⊢
  interval_cases i <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hmod; decide)

theorem eight_le_card_inf_centralizer {A : Subgroup G} (hAe : EgElemAb A) (hA : Nat.card A = 64)
    {q : G} (hqA : ∀ a ∈ A, q * a * q⁻¹ ∈ A) (hq2 : ∀ a ∈ A, q * q * a = a * (q * q)) :
    8 ≤ Nat.card (A ⊓ centralizer ({q} : Set G) : Subgroup G) := by
  let φ : A →* A :=
    { toFun := fun a => ⟨a * (q * a * q⁻¹), A.mul_mem a.2 (hqA a a.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show (a * b : G) * (q * (a * b) * q⁻¹) = a * (q * a * q⁻¹) * (b * (q * b * q⁻¹))
        have hc := hAe.1 b b.2 (q * a * q⁻¹) (hqA a a.2)
        calc (a * b : G) * (q * (a * b) * q⁻¹)
            = a * (b * (q * a * q⁻¹)) * (q * b * q⁻¹) := by group
          _ = a * ((q * a * q⁻¹) * b) * (q * b * q⁻¹) := by rw [hc]
          _ = a * (q * a * q⁻¹) * (b * (q * b * q⁻¹)) := by group) }
  have hker : ∀ a : A, a ∈ φ.ker ↔ q * (a : G) * q⁻¹ = a := by
    intro a
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h' : (a : G) * (q * a * q⁻¹) = 1 := congrArg Subtype.val h
      calc q * (a : G) * q⁻¹ = a * (a * (q * a * q⁻¹)) := by
            rw [← mul_assoc, hAe.2 a a.2, one_mul]
        _ = a := by rw [h', mul_one]
    · intro h
      apply Subtype.ext
      show (a : G) * (q * a * q⁻¹) = 1
      rw [h]
      exact hAe.2 a a.2
  have hle : φ.range ≤ φ.ker := by
    rintro _ ⟨a, rfl⟩
    rw [hker]
    show q * ((a : G) * (q * a * q⁻¹)) * q⁻¹ = (a : G) * (q * a * q⁻¹)
    have h1 : q * (q * (a : G) * q⁻¹) * q⁻¹ = a := by
      calc q * (q * (a : G) * q⁻¹) * q⁻¹ = (q * q * a) * (q * q)⁻¹ := by group
        _ = a := by rw [hq2 a a.2]; group
    have h2 := hAe.1 _ (hqA a a.2) a a.2
    calc q * ((a : G) * (q * a * q⁻¹)) * q⁻¹
        = (q * a * q⁻¹) * (q * (q * a * q⁻¹) * q⁻¹) := by group
      _ = (q * a * q⁻¹) * a := by rw [h1]
      _ = a * (q * a * q⁻¹) := h2
  have hmap : φ.ker.map A.subtype = A ⊓ centralizer ({q} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.coe_subtype, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, ?_⟩
      have := (hker a).1 ha
      calc (a : G) * q = q * a * q⁻¹ * q := by rw [this]
        _ = q * a := by group
    · rintro ⟨hx, hxq⟩
      refine ⟨⟨x, hx⟩, (hker _).2 ?_, rfl⟩
      show q * x * q⁻¹ = x
      rw [← hxq]
      group
  have hcard := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hA] at hcard
  have hr := Subgroup.card_le_of_le hle
  rw [← hmap, Subgroup.card_map_of_injective A.subtype_injective]
  by_contra hlt
  push Not at hlt
  have : Nat.card φ.ker * Nat.card φ.range ≤ 7 * 7 := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem mem_centralizer_of_pow {A : Subgroup G} {r : G} (hAe : EgElemAb A) (hA : Nat.card A = 64)
    (hr : r ^ 5 = 1) (hrA : ∀ a ∈ A, r * a * r⁻¹ ∈ A)
    (hfix : {c : G | c ∈ A ∧ r * c * r⁻¹ = c}.ncard = 4) :
    ∀ (k : ℕ) (q : G), q ^ 2 ^ k = 1 → (∀ a ∈ A, q * a * q⁻¹ ∈ A) → q * r = r * q →
      (∀ c ∈ A, r * c * r⁻¹ = c → q * c = c * q) → ∀ a ∈ A, q * a = a * q := by
  intro k
  induction k with
  | zero =>
    intro q hq _ _ _ a _
    rw [pow_zero, pow_one] at hq
    rw [hq, one_mul, mul_one]
  | succ k ih =>
    intro q hq hqA hqr hqC
    have hq2 : ∀ a ∈ A, q * q * a = a * (q * q) := by
      refine ih (q * q) ?_ ?_ ?_ ?_
      · rw [← pow_two, ← pow_mul, ← pow_succ']
        exact hq
      · intro a ha
        have := hqA _ (hqA a ha)
        rwa [show q * (q * a * q⁻¹) * q⁻¹ = q * q * a * (q * q)⁻¹ by group] at this
      · calc q * q * r = q * (q * r) := by group
          _ = q * (r * q) := by rw [hqr]
          _ = (q * r) * q := by group
          _ = r * q * q := by rw [hqr]
          _ = r * (q * q) := by group
      · intro c hc hrc
        calc q * q * c = q * (q * c) := by group
          _ = q * (c * q) := by rw [hqC c hc hrc]
          _ = (q * c) * q := by group
          _ = c * q * q := by rw [hqC c hc hrc]
          _ = c * (q * q) := by group
    have h8 := eight_le_card_inf_centralizer hAe hA hqA hq2
    have hqr' : r⁻¹ * q = q * r⁻¹ := by
      calc r⁻¹ * q = r⁻¹ * (q * r) * r⁻¹ := by group
        _ = r⁻¹ * (r * q) * r⁻¹ := by rw [hqr]
        _ = q * r⁻¹ := by group
    have hrW : ∀ w ∈ A ⊓ centralizer ({q} : Set G),
        r * w * r⁻¹ ∈ A ⊓ centralizer ({q} : Set G) := by
      intro w hw
      obtain ⟨hwA, hwq⟩ := mem_inf.1 hw
      rw [mem_centralizer_singleton_iff] at hwq
      refine mem_inf.2 ⟨hrA w hwA, mem_centralizer_singleton_iff.2 ?_⟩
      calc r * w * r⁻¹ * q = r * w * (r⁻¹ * q) := by group
        _ = r * w * (q * r⁻¹) := by rw [hqr']
        _ = r * (w * q) * r⁻¹ := by group
        _ = r * (q * w) * r⁻¹ := by rw [hwq]
        _ = (r * q) * w * r⁻¹ := by group
        _ = (q * r) * w * r⁻¹ := by rw [hqr]
        _ = q * (r * w * r⁻¹) := by group
    have hCW : ∀ c ∈ A, r * c * r⁻¹ = c → c ∈ A ⊓ centralizer ({q} : Set G) := fun c hc hrc =>
      mem_inf.2 ⟨hc, mem_centralizer_singleton_iff.2 (hqC c hc hrc).symm⟩
    have hW := card_eq_four_or_of_invariant hA hr hfix inf_le_left hrW hCW
    have h64 : Nat.card (A ⊓ centralizer ({q} : Set G) : Subgroup G) = 64 := by omega
    have heq : A ⊓ centralizer ({q} : Set G) = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h64, hA])
    intro a ha
    have : a ∈ A ⊓ centralizer ({q} : Set G) := by rw [heq]; exact ha
    exact (mem_centralizer_singleton_iff.1 (mem_inf.1 this).2).symm

end Trans

theorem card_le_eight_mul_of_normalizer {A S : Subgroup G} {r : G}
    (hAe : EgElemAb A) (hA : Nat.card A = 64) (hrA : r ∈ normalizer (A : Set G))
    (hr : orderOf r = 5) (hfix : Nat.card {a : A | r * (a : G) * r⁻¹ = a} = 4)
    (hS : IsPGroup 2 S) (hSA : S ≤ normalizer (A : Set G))
    (hSr : S ≤ normalizer (zpowers r : Set G)) :
    Nat.card S ≤ 8 * Nat.card (S ⊓ centralizer (A : Set G) : Subgroup G) := by
  have hr5 : r ^ 5 = 1 := by rw [← hr]; exact pow_orderOf_eq_one r
  have hrA' : ∀ a ∈ A, r * a * r⁻¹ ∈ A := fun a ha => (mem_normalizer_iff.1 hrA a).1 ha
  set CA : Set G := {c | c ∈ A ∧ r * c * r⁻¹ = c} with hCA
  have hCA4 : CA.ncard = 4 := by
    have : CA = Subtype.val '' {a : A | r * (a : G) * r⁻¹ = a} := by
      ext x
      constructor
      · rintro ⟨hx, hrx⟩
        exact ⟨⟨x, hx⟩, hrx, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.2, ha⟩
    rw [this, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq, hfix]
  set S0 : Subgroup G := S ⊓ centralizer ({r} : Set G) with hS0
  have h1 : Nat.card S ≤ 4 * Nat.card S0 := by
    have hc := J4Std.card_inf_centralizer_mul_ncard S r
    have hsub : {m | ∃ k ∈ S, m = k * r * k⁻¹} ⊆ (zpowers r : Set G) \ {1} := by
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨(mem_normalizer_iff.1 (hSr hk) r).1 (mem_zpowers r), fun h => ?_⟩
      have h' : k * r * k⁻¹ = 1 := h
      have : r = 1 := by
        calc r = k⁻¹ * (k * r * k⁻¹) * k := by group
          _ = 1 := by rw [h']; group
      rw [this, orderOf_one] at hr
      omega
    have hz : ((zpowers r : Set G) \ {1}).ncard = 4 := by
      rw [Set.ncard_sdiff_singleton_of_mem (one_mem (zpowers r)), ← Nat.card_coe_set_eq,
        show Nat.card (zpowers r : Set G) = Nat.card (zpowers r) from rfl, Nat.card_zpowers, hr]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hz] at hle
    rw [← hc]
    calc Nat.card S0 * {m | ∃ k ∈ S, m = k * r * k⁻¹}.ncard ≤ Nat.card S0 * 4 :=
          Nat.mul_le_mul_left _ hle
      _ = 4 * Nat.card S0 := mul_comm _ _
  have hS0p : IsPGroup 2 S0 := hS.to_le inf_le_left
  set X : Set G := {c | c ∈ A ∧ r * c * r⁻¹ = c ∧ c ≠ 1} with hX
  have hX3 : Nat.card X = 3 := by
    have : X = CA \ {1} := by
      ext c
      simp only [hX, hCA, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
    rw [Nat.card_coe_set_eq, this,
      Set.ncard_sdiff_singleton_of_mem (show (1 : G) ∈ CA from ⟨one_mem A, by group⟩), hCA4]
  have hXs : ∀ s ∈ S0, ∀ c ∈ X, s * c * s⁻¹ ∈ X := by
    intro s hs c hc
    obtain ⟨hcA, hrc, hc1⟩ := hc
    obtain ⟨hsS, hsr⟩ := mem_inf.1 hs
    rw [mem_centralizer_singleton_iff] at hsr
    refine ⟨(mem_normalizer_iff.1 (hSA hsS) c).1 hcA, ?_, fun h => hc1 ?_⟩
    · calc r * (s * c * s⁻¹) * r⁻¹ = (r * s) * c * (r * s)⁻¹ := by group
        _ = (s * r) * c * (s * r)⁻¹ := by rw [← hsr]
        _ = s * (r * c * r⁻¹) * s⁻¹ := by group
        _ = s * c * s⁻¹ := by rw [hrc]
    · calc c = s⁻¹ * (s * c * s⁻¹) * s := by group
        _ = 1 := by rw [h]; group
  let _ : MulAction S0 X :=
    { smul := fun s c => ⟨(s : G) * c * (s : G)⁻¹, hXs s s.2 c c.2⟩
      one_smul := fun c => Subtype.ext (show ((1 : S0) : G) * c * ((1 : S0) : G)⁻¹ = c by simp)
      mul_smul := fun s t c => Subtype.ext (show ((s * t : S0) : G) * c * ((s * t : S0) : G)⁻¹ =
          s * ((t : G) * c * (t : G)⁻¹) * (s : G)⁻¹ by rw [Subgroup.coe_mul]; group) }
  let φ := MulAction.toPermHom S0 X
  have hφr : Nat.card φ.range ≤ 2 := by
    have hp : IsPGroup 2 φ.range := hS0p.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hp
    have hdvd : Nat.card φ.range ∣ 6 := by
      have := Subgroup.card_subgroup_dvd_card φ.range
      rwa [Nat.card_perm, hX3, show Nat.factorial 3 = 6 from rfl] at this
    rw [hj] at hdvd ⊢
    have hj1 : j ≤ 1 := by
      by_contra hj1
      have h4 : 2 ^ 2 ∣ 6 := dvd_trans (pow_dvd_pow 2 (by omega)) hdvd
      exact absurd h4 (by decide)
    interval_cases j <;> norm_num
  have hS2c : Nat.card S0 ≤ 2 * Nat.card (φ.ker.map S0.subtype) := by
    have hcard := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at hcard
    rw [Subgroup.card_map_of_injective S0.subtype_injective, ← hcard]
    calc Nat.card φ.ker * Nat.card φ.range ≤ Nat.card φ.ker * 2 := Nat.mul_le_mul_left _ hφr
      _ = 2 * Nat.card φ.ker := mul_comm _ _
  have hS2A : φ.ker.map S0.subtype ≤ S ⊓ centralizer (A : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨hsS, hsr⟩ := mem_inf.1 s.2
    rw [mem_centralizer_singleton_iff] at hsr
    have hsX : ∀ c (hc : c ∈ X), (s : G) * c * (s : G)⁻¹ = c := fun c hc =>
      congrArg (fun π : Equiv.Perm X => ((π ⟨c, hc⟩ : X) : G)) (MonoidHom.mem_ker.1 hs)
    have hsC : ∀ c ∈ A, r * c * r⁻¹ = c → (s : G) * c = c * s := by
      intro c hc hrc
      by_cases hc1 : c = 1
      · rw [hc1, mul_one, one_mul]
      · have := hsX c ⟨hc, hrc, hc1⟩
        calc (s : G) * c = s * c * (s : G)⁻¹ * s := by group
          _ = c * s := by rw [this]
    obtain ⟨k, hk⟩ := hS ⟨s, hsS⟩
    have hk' : (s : G) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hsA : ∀ a ∈ A, (s : G) * a * (s : G)⁻¹ ∈ A := fun a ha =>
      (mem_normalizer_iff.1 (hSA hsS) a).1 ha
    refine mem_inf.2 ⟨hsS, mem_centralizer_iff.2 fun a ha => ?_⟩
    exact (Trans.mem_centralizer_of_pow hAe hA hr5 hrA' hCA4 k s hk' hsA hsr hsC a ha).symm
  have h3 := Subgroup.card_le_of_le hS2A
  omega

end CFSG.EvenSporadicStandard.M24Std
