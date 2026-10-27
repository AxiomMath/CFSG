module

import CFSG.ClassicalInvolution.Asc77.WP3FramePSCCover
public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace T7L

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

section Coprime

theorem exists_conj_sylow {P P' M : Subgroup G} (h : IsSylow2In P M) (h' : IsSylow2In P' M) :
    ∃ c ∈ M, conjSub c P = P' := by
  obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow (G := ↥M) (sylowOfIsSylow2In h)
    (sylowOfIsSylow2In h')
  refine ⟨x, x.2, ?_⟩
  have hPx : conjSub (x : G) P ≤ M := by
    have := conjSub_mono (n := (x : G)) h.1
    rwa [conjSub_eq_self_of_mem x.2] at this
  have h1 : (conjSub (x : G) P).subgroupOf M = P'.subgroupOf M := by
    have e : (conjSub (x : G) P).subgroupOf M = conjSub x (P.subgroupOf M) := by
      ext y
      rw [Subgroup.mem_subgroupOf, mem_conjSub_iff, mem_conjSub_iff, Subgroup.mem_subgroupOf]
      simp
    rw [e]
    exact hx
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_eq_left.mpr hPx, inf_eq_left.mpr h'.1] at h2

omit [Finite G] in
theorem mem_sup_normalForm {N R : Subgroup G} (hRN : R ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ N ⊔ R) : ∃ n ∈ N, ∃ r ∈ R, x = n * r := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, R.one_mem, by simp⟩
    · exact ⟨1, N.one_mem, x, hx, by simp⟩
  | one => exact ⟨1, N.one_mem, 1, R.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, r, hr, rfl⟩ := hx
    obtain ⟨n', hn', r', hr', rfl⟩ := hy
    refine ⟨n * (r * n' * r⁻¹), N.mul_mem hn ?_, r * r', R.mul_mem hr hr', by group⟩
    exact (Subgroup.mem_normalizer_iff.mp (hRN hr) n').mp hn'
  | inv x _ hx =>
    obtain ⟨n, hn, r, hr, rfl⟩ := hx
    refine ⟨r⁻¹ * n⁻¹ * r, ?_, r⁻¹, R.inv_mem hr, by group⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hRN (R.inv_mem hr)) n⁻¹).mp (N.inv_mem hn)
    simpa [mul_assoc] using h1

theorem exists_conj_centralizes {N R : Subgroup G} {c : G} (hc2 : c * c = 1)
    (hNodd : Odd (Nat.card N)) (hR2 : IsPGroup 2 R) (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hcN : c ∈ Subgroup.normalizer (N : Set G)) (hcR : ∀ r ∈ R, ⁅c, r⁆ ∈ N) :
    ∃ n ∈ N, conjSub n R ≤ Subgroup.centralizer ({c} : Set G) := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  let H₀ : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (N : Set G) ∧ ⁅c, x⁆ ∈ N}
      one_mem' := ⟨Subgroup.one_mem _, by simp [commutatorElement_def]⟩
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
        have e : ⁅c, x * y⁆ = ⁅c, x⁆ * (x * ⁅c, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact N.mul_mem hx' ((Subgroup.mem_normalizer_iff.mp hx _).mp hy')
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨Subgroup.inv_mem _ hx, ?_⟩
        have e : ⁅c, x⁻¹⁆ = x⁻¹ * ⁅c, x⁆⁻¹ * x := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have h1 : ⁅c, x⁆⁻¹ ∈ N := N.inv_mem hx'
        have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) _).mp h1
        simpa using h2 }
  have hNle : N ≤ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer
  have hNH : N ≤ H₀ := fun n hn => ⟨hNle hn, by
    have e : ⁅c, n⁆ = (c * n * c⁻¹) * n⁻¹ := rfl
    rw [e]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp hcN n).mp hn) (N.inv_mem hn)⟩
  have hRH : R ≤ H₀ := fun r hr => ⟨hRN hr, hcR r hr⟩
  set T := N ⊔ R with hT
  have hTH : T ≤ H₀ := sup_le hNH hRH
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := fun x hx => (hTH hx).1
  have hNT : N ≤ T := le_sup_left
  have hRT : R ≤ T := le_sup_right
  have hcT : c ∈ trivialOnQuot T := by
    have hcomm : ∀ x ∈ T, ⁅c, x⁆ ∈ oddCoreIn T := fun x hx =>
      le_oddCoreIn_of_normalizes hNT hTN hNodd ((hTH hx).2)
    have hnorm : ∀ x ∈ T, c * x * c⁻¹ ∈ T := by
      intro x hx
      have e : c * x * c⁻¹ = ⁅c, x⁆ * x := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact T.mul_mem (hNT ((hTH hx).2)) hx
    refine ⟨?_, hcomm⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hnorm x hx, fun hx => ?_⟩
    have := hnorm _ hx
    have e : c * (c * x * c⁻¹) * c⁻¹ = x := by
      calc c * (c * x * c⁻¹) * c⁻¹ = (c * c) * x * (c⁻¹ * c⁻¹) := by group
        _ = x := by rw [hc2, hci, hc2]; group
    rwa [e] at this
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hc2
  obtain ⟨P, hP, hPc⟩ := AscE184Sect.exists_isSylow2In_centralizer hc2'
    (commutator_zpowers_le_iff.mpr hcT)
  have hRsyl : IsSylow2In R T := by
    refine ⟨hRT, hR2, fun V hVT hV2 hRV => ?_⟩
    refine le_antisymm (fun x hx => ?_) hRV
    obtain ⟨n, hn, r, hr, rfl⟩ := mem_sup_normalForm hRN (hVT hx)
    have hnV : n ∈ V := by
      have : n = (n * r) * r⁻¹ := by group
      rw [this]
      exact V.mul_mem hx (V.inv_mem (hRV hr))
    have hn1 : n = 1 :=
      eq_one_of_isPGroup_of_mem_odd hNodd hn (hV2.to_le (Subgroup.zpowers_le.mpr hnV))
    rw [hn1, one_mul]
    exact hr
  obtain ⟨y, hy, hyP⟩ := exists_conj_sylow hRsyl hP
  obtain ⟨n, hn, r, hr, rfl⟩ := mem_sup_normalForm hRN hy
  refine ⟨n, hn, ?_⟩
  have : conjSub (n * r) R = conjSub n R := by
    rw [conjSub_mul, conjSub_eq_self_of_mem hr]
  rw [this] at hyP
  rw [hyP]
  intro x hx
  have := hPc hx
  rwa [centralizer_zpowers_eq_singleton'] at this

end Coprime

section NoMember

omit [Finite G] in
theorem mem_normalizer_oddCoreOf {Y : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) : g ∈ Subgroup.normalizer (oddCoreOf Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => mem_normalizer_oddCoreOf_of_mem_normalizer hg hx, fun hx => ?_⟩
  have h1 := mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.inv_mem _ hg) hx
  simpa [mul_assoc] using h1

theorem no_member_commutes (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K K' : Subgroup G} {z u v' : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hperp : KPerp Ω K = {K, K'}) (hKt : K ∉ tqMembers Ω u) (hK't : K' ∉ tqMembers Ω u)
    (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hzv : ∀ y ∈ exactLayer Ω u, z * y * z⁻¹ = v' * y * v'⁻¹)
    {M : Subgroup G} (hM : M ∈ tqMembers Ω u) :
    ∃ m ∈ exactCore u M, ⁅v', m⁆ ∉ oddCoreOf (exactLayer Ω u) := by
  by_contra hcon
  push Not at hcon
  have hu2' : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one hu2
  obtain ⟨hMΩ, R₀, hR₀, hR₀c⟩ := (mem_tqMembers_iff_exists_sylow hp hq hΩ hu2').mp hM
  have hR₀core : IsSylow2In R₀ (exactCore u M) :=
    (isSylow2In_exactCore_iff hΩ hu2' hMΩ hM.2).mpr ⟨hR₀, hR₀c⟩
  have hR₀Y : R₀ ≤ exactLayer Ω u := hR₀core.1.trans (exactCore_le_exactLayer hM)
  have hzC : z ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzu
  have hzY : z ∈ Subgroup.normalizer ((exactLayer Ω u : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_exactLayer hΩ.conjInvariant hzC)
  have hNodd : Odd (Nat.card ↥(oddCoreOf (exactLayer Ω u))) := oddCoreOf_odd_natCard _
  have hRN : R₀ ≤ Subgroup.normalizer (oddCoreOf (exactLayer Ω u) : Set G) := fun r hr =>
    normalizer_oddCoreIn (exactLayer Ω u) (hR₀Y hr)
  obtain ⟨n, hn, hnR⟩ := exists_conj_centralizes hz.sq hNodd hR₀core.2.1 hRN
    (mem_normalizer_oddCoreOf hzY) (fun r hr => by
      have h1 := hzv r (hR₀Y hr)
      have h2 : ⁅z, r⁆ = ⁅v', r⁆ := by
        simp only [commutatorElement_def]
        rw [h1]
      rw [h2]
      exact hcon r (hR₀core.1 hr))
  have hnY : n ∈ exactLayer Ω u := oddCoreIn_le _ hn
  have hnC : n ∈ Subgroup.centralizer ({u} : Set G) := exactLayer_le_centralizer Ω u hnY
  have hM₁ : conjSub n M ∈ tqMembers Ω u := conjSub_mem_tqMembers hΩ.conjInvariant hnC hM
  have hS : IsSylow2In (conjSub n R₀) (conjSub n M) := hR₀.conj n
  have hRset : conjSub n R₀ ∈ RSet Ω := mem_RSet_of_isSylow2In hM₁.1 hS
  have hne : conjSub n M ≠ K := fun h => hKt (h ▸ hM₁)
  have hnbr : conjSub n M ∈ omegaNbr Ω K :=
    mem_omegaNbr_of_sylow_le_centralizer hp hq hΩ hK hM₁.1 hne hz hS hRset hnR
  have hperp' : conjSub n M ∈ KPerp Ω K := Or.inr hnbr
  rw [hperp] at hperp'
  rcases hperp' with h | h
  · exact hne h
  · exact hK't (h ▸ hM₁)

end NoMember

end T7L

end CFSG.ClassicalInvolution.Asc77
