module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2
public import CFSG.ClassicalInvolution.AschTight.E2StarTargets

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conjSub_le_centralizer {z c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G))
    {A : Subgroup G} (hA : A ≤ Subgroup.centralizer ({z} : Set G)) :
    conjSub c A ≤ Subgroup.centralizer ({z} : Set G) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h1 := hA hx
  have e : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc h1) (Subgroup.inv_mem _ hc)

theorem conjSub_gammaGen_le {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {z c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) : conjSub c (gammaGen Ω z) ≤ gammaGen Ω z := by
  unfold gammaGen
  change Subgroup.map (MulAut.conj c).toMonoidHom _ ≤ _
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun A hA => Subgroup.map_le_iff_le_comap.mp ?_
  have hmem : conjSub c A ∈ {A : Subgroup G | (A ∈ USet Ω ∨ A ∈ RSet Ω) ∧
      A ≤ Subgroup.centralizer ({z} : Set G)} := by
    refine ⟨?_, conjSub_le_centralizer hc hA.2⟩
    rcases hA.1 with h | h
    · exact Or.inl (USet.conj hΩ h c)
    · exact Or.inr (RSet.conj hΩ h c)
  exact le_iSup₂_of_le (f := fun (B : Subgroup G) (_ : B ∈ {A : Subgroup G |
    (A ∈ USet Ω ∨ A ∈ RSet Ω) ∧ A ≤ Subgroup.centralizer ({z} : Set G)}) => B)
    (conjSub c A) hmem le_rfl

theorem conjSub_gammaGen {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {z c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) : conjSub c (gammaGen Ω z) = gammaGen Ω z := by
  refine le_antisymm (conjSub_gammaGen_le hΩ hc) ?_
  have h := conjSub_gammaGen_le hΩ (Subgroup.inv_mem _ hc)
  have h2 := conjSub_mono (n := c) h
  rwa [conjSub_conjSub_inv] at h2

theorem gammaGen_le_centralizer (Ω : Set (Subgroup G)) (z : G) :
    gammaGen Ω z ≤ Subgroup.centralizer ({z} : Set G) :=
  iSup₂_le fun _ hA => hA.2

theorem conjSub_centralizerModOdd_le [Finite G] {H L : Subgroup G} {c : G}
    (hcL : c ∈ Subgroup.normalizer (L : Set G)) (hcH : conjSub c H = H) :
    conjSub c (centralizerModOdd H L) ≤ centralizerModOdd H L := by
  have hcO : c ∈ Subgroup.normalizer (oddCoreOf L : Set G) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hcL
  rintro _ ⟨x, ⟨hxH, hxL, hxO, hx⟩, rfl⟩
  change c * x * c⁻¹ ∈ centralizerModOdd H L
  refine ⟨?_, ?_, ?_, fun l hl => ?_⟩
  · rw [← hcH]
    exact conj_mem_conjSub hxH
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcL hxL) (Subgroup.inv_mem _ hcL)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcO hxO) (Subgroup.inv_mem _ hcO)
  · have hl' : c⁻¹ * l * c ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcL) l).mp hl
      simpa using this
    have h1 := hx _ hl'
    have h2 := (Subgroup.mem_normalizer_iff.mp hcO _).mp h1
    have e : ⁅c * x * c⁻¹, l⁆ = c * ⁅x, c⁻¹ * l * c⁆ * c⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h2

theorem conjSub_centralizerModOdd [Finite G] {H L : Subgroup G} {c : G}
    (hcL : c ∈ Subgroup.normalizer (L : Set G)) (hcH : conjSub c H = H) :
    conjSub c (centralizerModOdd H L) = centralizerModOdd H L := by
  refine le_antisymm (conjSub_centralizerModOdd_le hcL hcH) ?_
  have hcH' : conjSub c⁻¹ H = H := by
    conv_lhs => rw [← hcH]
    exact conjSub_inv_conjSub c H
  have h := conjSub_centralizerModOdd_le (H := H) (L := L)
    (Subgroup.inv_mem _ hcL) hcH'
  have h2 := conjSub_mono (n := c) h
  rwa [conjSub_conjSub_inv] at h2

theorem centralizer_le_normalizer_sec19X (K : Subgroup G) (z : G) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer ((sec19X K z : Subgroup G) : Set G) :=
  fun _ hc => mem_normalizer_iff_conjSub_eq.mpr (conjSub_gammaGen (conjInvariant_conjClass K) hc)

theorem sec19Y_le_sec19X (K : Subgroup G) (z : G) : sec19Y K z ≤ sec19X K z :=
  fun _ hx => hx.1

theorem sec19Y_le_centralizer (K : Subgroup G) (z : G) :
    sec19Y K z ≤ Subgroup.centralizer ({z} : Set G) :=
  (sec19Y_le_sec19X K z).trans (gammaGen_le_centralizer _ z)

variable {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}

theorem conjSub_sec19Y (ht : S19R.TightStd p f K z) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) : conjSub c (sec19Y K z) = sec19Y K z := by
  have hcK : c ∈ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight ht.toTightBranch]
    exact hc
  exact conjSub_centralizerModOdd hcK (conjSub_gammaGen (conjInvariant_conjClass K) hc)

theorem centralizer_le_normalizer_sec19Y (ht : S19R.TightStd p f K z) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G) :=
  fun _ hc => mem_normalizer_iff_conjSub_eq.mpr (conjSub_sec19Y ht hc)

theorem eq_one_of_mem_oddCoreOf {K : Subgroup G} {x : G} (hx : x ∈ oddCoreOf K)
    (h2 : IsPGroup 2 (Subgroup.zpowers x)) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨o, ho, rfl⟩ := hx
  have hodd : Odd (orderOf o) := by
    have h1 := Subgroup.orderOf_dvd_natCard (classicalInvolutionOddCore ↥K) ho
    exact Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card ↥K) h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2) ⟨_, Subgroup.mem_zpowers _⟩
  have hk' : orderOf (o : G) = 2 ^ k := (Subgroup.orderOf_mk _ _).symm.trans hk
  rw [Subgroup.orderOf_coe] at hk'
  rw [hk'] at hodd
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk'
    simp [hk']
  · exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero k⟩))

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
