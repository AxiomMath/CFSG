module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma314Perm
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRTwoBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section SecPerm

variable {G : Type*} [Group G] {K : Type*} {S S' X : Subgroup G} {f : G → K}

@[expose] noncomputable def secFun (hsurj : ∀ w, ∃ x ∈ S, f x = w) (g : G) (w : K) : K :=
  f (g * Classical.choose (hsurj w) * g⁻¹)

theorem secFun_apply (hsurj : ∀ w, ∃ x ∈ S, f x = w)
    (heq : ∀ x ∈ S, ∀ x' ∈ S, f x = f x' ↔ x⁻¹ * x' ∈ S') {g : G}
    (hgS : g ∈ normalizer (S : Set G)) (hgS' : g ∈ normalizer (S' : Set G)) {x : G} (hx : x ∈ S) :
    secFun hsurj g (f x) = f (g * x * g⁻¹) := by
  obtain ⟨hxS, hfx⟩ := Classical.choose_spec (hsurj (f x))
  set y := Classical.choose (hsurj (f x))
  have hyx : y⁻¹ * x ∈ S' := (heq y hxS x hx).mp hfx
  have hconj : g * (y⁻¹ * x) * g⁻¹ ∈ S' := (mem_normalizer_iff.mp hgS' _).mp hyx
  have hgy : g * y * g⁻¹ ∈ S := (mem_normalizer_iff.mp hgS _).mp hxS
  have hgx : g * x * g⁻¹ ∈ S := (mem_normalizer_iff.mp hgS _).mp hx
  refine (heq _ hgy _ hgx).mpr ?_
  have e : (g * y * g⁻¹)⁻¹ * (g * x * g⁻¹) = g * (y⁻¹ * x) * g⁻¹ := by group
  rw [e]
  exact hconj

@[expose] noncomputable def secEquiv (hsurj : ∀ w, ∃ x ∈ S, f x = w)
    (heq : ∀ x ∈ S, ∀ x' ∈ S, f x = f x' ↔ x⁻¹ * x' ∈ S') {g : G}
    (hgS : g ∈ normalizer (S : Set G)) (hgS' : g ∈ normalizer (S' : Set G)) : Equiv.Perm K where
  toFun := secFun hsurj g
  invFun := secFun hsurj g⁻¹
  left_inv w := by
    obtain ⟨hxS, hfx⟩ := Classical.choose_spec (hsurj w)
    have h1 : g * Classical.choose (hsurj w) * g⁻¹ ∈ S := (mem_normalizer_iff.mp hgS _).mp hxS
    have h2 : secFun hsurj g w = f (g * Classical.choose (hsurj w) * g⁻¹) := rfl
    show secFun hsurj g⁻¹ (secFun hsurj g w) = w
    rw [h2, secFun_apply hsurj heq (inv_mem hgS) (inv_mem hgS') h1,
      show g⁻¹ * (g * Classical.choose (hsurj w) * g⁻¹) * g⁻¹⁻¹ = Classical.choose (hsurj w) by
        group, hfx]
  right_inv w := by
    obtain ⟨hxS, hfx⟩ := Classical.choose_spec (hsurj w)
    have h1 : g⁻¹ * Classical.choose (hsurj w) * g⁻¹⁻¹ ∈ S :=
      (mem_normalizer_iff.mp (inv_mem hgS) _).mp hxS
    have h2 : secFun hsurj g⁻¹ w = f (g⁻¹ * Classical.choose (hsurj w) * g⁻¹⁻¹) := rfl
    show secFun hsurj g (secFun hsurj g⁻¹ w) = w
    rw [h2, secFun_apply hsurj heq hgS hgS' h1,
      show g * (g⁻¹ * Classical.choose (hsurj w) * g⁻¹⁻¹) * g⁻¹ = Classical.choose (hsurj w) by
        group, hfx]

@[expose] noncomputable def secPerm (hXS : X ≤ normalizer (S : Set G))
    (hXS' : X ≤ normalizer (S' : Set G)) (hsurj : ∀ w, ∃ x ∈ S, f x = w)
    (heq : ∀ x ∈ S, ∀ x' ∈ S, f x = f x' ↔ x⁻¹ * x' ∈ S') : X →* Equiv.Perm K where
  toFun n := secEquiv hsurj heq (hXS n.2) (hXS' n.2)
  map_one' := by
    refine Equiv.ext fun w => ?_
    show secFun hsurj ((1 : X) : G) w = w
    obtain ⟨-, hfx⟩ := Classical.choose_spec (hsurj w)
    rw [secFun, OneMemClass.coe_one, one_mul, inv_one, mul_one, hfx]
  map_mul' n m := by
    refine Equiv.ext fun w => ?_
    show secFun hsurj ((n * m : X) : G) w = secFun hsurj n (secFun hsurj m w)
    obtain ⟨hxS, -⟩ := Classical.choose_spec (hsurj w)
    have h1 : (m : G) * Classical.choose (hsurj w) * (m : G)⁻¹ ∈ S :=
      (mem_normalizer_iff.mp (hXS m.2) _).mp hxS
    have h2 : secFun hsurj m w = f ((m : G) * Classical.choose (hsurj w) * (m : G)⁻¹) := rfl
    rw [h2, secFun_apply hsurj heq (hXS n.2) (hXS' n.2) h1, secFun, Subgroup.coe_mul]
    congr 1
    group

theorem secPerm_apply (hXS : X ≤ normalizer (S : Set G)) (hXS' : X ≤ normalizer (S' : Set G))
    (hsurj : ∀ w, ∃ x ∈ S, f x = w) (heq : ∀ x ∈ S, ∀ x' ∈ S, f x = f x' ↔ x⁻¹ * x' ∈ S')
    (n : X) {x : G} (hx : x ∈ S) :
    secPerm hXS hXS' hsurj heq n (f x) = f ((n : G) * x * (n : G)⁻¹) := by
  show secFun hsurj n (f x) = _
  exact secFun_apply hsurj heq (hXS n.2) (hXS' n.2) hx

theorem secPerm_fixed_of_isPGroup [Finite K] {p : ℕ} [Fact p.Prime]
    (hXS : X ≤ normalizer (S : Set G)) (hXS' : X ≤ normalizer (S' : Set G))
    (hsurj : ∀ w, ∃ x ∈ S, f x = w) (heq : ∀ x ∈ S, ∀ x' ∈ S, f x = f x' ↔ x⁻¹ * x' ∈ S')
    {P : Subgroup G} (hP : IsPGroup p P) (hPX : P ≤ X) {d : G} (hdX : d ∈ X)
    (hdP : d ∈ normalizer (P : Set G))
    (htrans : ∀ x ∈ S, ∀ x' ∈ S, f x ≠ f 1 → f x' ≠ f 1 →
      ∃ m : ℕ, f ((d ^ m)⁻¹ * x * d ^ m) = f x')
    (hdvd : p ∣ Nat.card K) : ∀ n ∈ P, ∀ x ∈ S, f (n * x * n⁻¹) = f x := by
  set σ := secPerm hXS hXS' hsurj heq with hσ
  set P' : Subgroup (Equiv.Perm K) := (P.subgroupOf X).map σ with hP'
  have hPp : IsPGroup p P' := (hP.of_equiv (subgroupOfEquivOfLe hPX).symm).map σ
  set c : Equiv.Perm K := σ ⟨d, hdX⟩ with hc
  have hcP : c ∈ normalizer (P' : Set (Equiv.Perm K)) := by
    refine mem_normalizer_iff.mpr fun τ => ⟨fun hτ => ?_, fun hτ => ?_⟩
    · obtain ⟨n, hn, rfl⟩ := mem_map.mp hτ
      refine mem_map.mpr ⟨⟨d, hdX⟩ * n * ⟨d, hdX⟩⁻¹, mem_subgroupOf.mpr ?_, ?_⟩
      · exact (mem_normalizer_iff.mp hdP _).mp (mem_subgroupOf.mp hn)
      · rw [map_mul, map_mul, map_inv]
    · obtain ⟨n, hn, hnτ⟩ := mem_map.mp hτ
      refine mem_map.mpr ⟨⟨d, hdX⟩⁻¹ * n * ⟨d, hdX⟩, mem_subgroupOf.mpr ?_, ?_⟩
      · have h1 := (mem_normalizer_iff.mp (inv_mem hdP) _).mp (mem_subgroupOf.mp hn)
        simpa using h1
      · rw [map_mul, map_mul, map_inv, hnτ, ← hc]
        group
  have h1S : (1 : G) ∈ S := one_mem _
  have hfix1 : ∀ τ ∈ P', τ • f 1 = f 1 := by
    intro τ hτ
    obtain ⟨n, -, rfl⟩ := mem_map.mp hτ
    rw [Equiv.Perm.smul_def, hσ, secPerm_apply hXS hXS' hsurj heq n h1S, mul_one, mul_inv_cancel]
  have htr : ∀ β γ : K, β ≠ f 1 → γ ≠ f 1 → ∃ k : ℤ, c ^ k • β = γ := by
    intro β γ hβ hγ
    obtain ⟨x, hx, rfl⟩ := hsurj β
    obtain ⟨x', hx', rfl⟩ := hsurj γ
    obtain ⟨m, hm⟩ := htrans x hx x' hx' hβ hγ
    refine ⟨-(m : ℤ), ?_⟩
    have e : c ^ (-(m : ℤ)) = σ (⟨d, hdX⟩ ^ m)⁻¹ := by
      rw [zpow_neg, zpow_natCast, hc, map_inv, map_pow]
    rw [e, Equiv.Perm.smul_def, secPerm_apply hXS hXS' hsurj heq _ hx]
    simpa using hm
  have key := CFSG.ComponentClassification.GMS78.smul_eq_of_isPGroup hPp hcP hfix1 htr hdvd
  intro n hn x hx
  have h1 := key (σ ⟨n, hPX hn⟩) (mem_map.mpr ⟨_, mem_subgroupOf.mpr hn, rfl⟩) (f x)
  rwa [Equiv.Perm.smul_def, secPerm_apply hXS hXS' hsurj heq _ hx] at h1

end SecPerm

end CFSG.SeitzReduction.RankOne
