module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf2
import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Hyp
public import CFSG.ClassicalInvolution.Asc77.AscT8T3

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section TwinProduct

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

private theorem conjSub_mem_twinSet_of_mem_centralizer (hΩ : HypOmegaGen Ω) {M : Subgroup G}
    {c : G} (hM : M ∈ Ω) (hc : IsUniqueInvolution M c) {x : G}
    (hx : x ∈ Subgroup.centralizer ({c} : Set G)) : conjSub x M ∈ twinSet Ω M := by
  have hxc : x * c * x⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hx]
    group
  refine ⟨hΩ.conjInvariant x M hM, c, hc, ?_⟩
  have := hc.conj x
  rwa [hxc] at this

variable [Finite G]

private theorem exists_mul_of_mem_sup_twin (hΩ : HypOmegaGen Ω) {M M' : Subgroup G} {c : G}
    (hM : M ∈ Ω) (hM' : M' ∈ Ω) (hne : M' ≠ M) (hc : IsUniqueInvolution M c)
    (hc' : IsUniqueInvolution M' c) {n : G} (hn : n ∈ M ⊔ M') :
    ∃ m ∈ M, ∃ m' ∈ M', n = m * m' := by
  have hN : M' ≤ Subgroup.normalizer (M : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hM' hM hne hc' hc
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left M M' hN] at hn
  obtain ⟨m, hm, m', hm', rfl⟩ := hn
  exact ⟨m, hm, m', hm', rfl⟩

private theorem conj_mem_sup_twin (hΩ : HypOmegaGen Ω) {M M' : Subgroup G} {c : G} (hM : M ∈ Ω)
    (hc : IsUniqueInvolution M c) (hne : M' ≠ M) (htw : twinSet Ω M = {M, M'}) {x : G}
    (hx : x ∈ Subgroup.centralizer ({c} : Set G)) {n : G} (hn : n ∈ M ⊔ M') :
    x * n * x⁻¹ ∈ M ⊔ M' := by
  have hM'T : M' ∈ twinSet Ω M := by rw [htw]; exact Or.inr rfl
  have hM' : M' ∈ Ω := hM'T.1
  have hc' : IsUniqueInvolution M' c := isUniqueInvolution_of_mem_twinSet hc hM'T
  obtain ⟨m, hm, m', hm', rfl⟩ := exists_mul_of_mem_sup_twin hΩ hM hM' hne hc hc' hn
  have h1 : x * m * x⁻¹ ∈ M ⊔ M' := by
    have h := conjSub_mem_twinSet_of_mem_centralizer hΩ hM hc hx
    rw [htw] at h
    have hmem : x * m * x⁻¹ ∈ conjSub x M := conj_mem_conjSub hm
    rcases h with h | h
    · rw [h] at hmem
      exact Subgroup.mem_sup_left hmem
    · rw [Set.mem_singleton_iff.mp h] at hmem
      exact Subgroup.mem_sup_right hmem
  have h2 : x * m' * x⁻¹ ∈ M ⊔ M' := by
    have h := conjSub_mem_twinSet_of_mem_centralizer hΩ hM' hc' hx
    rw [twinSet_eq_of_mem_twinSet hc hM'T, htw] at h
    have hmem : x * m' * x⁻¹ ∈ conjSub x M' := conj_mem_conjSub hm'
    rcases h with h | h
    · rw [h] at hmem
      exact Subgroup.mem_sup_left hmem
    · rw [Set.mem_singleton_iff.mp h] at hmem
      exact Subgroup.mem_sup_right hmem
  have e : x * (m * m') * x⁻¹ = (x * m * x⁻¹) * (x * m' * x⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ h1 h2

private theorem exists_pow_oddQuotMk_eq_one {c : G} {M : Subgroup G}
    (h2 : IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hO : Balance.oddCoreIn M ≤ Balance.oddCoreIn (Subgroup.centralizer ({c} : Set G))) {m : G}
    (hm : m ∈ M) (hmC : m ∈ Subgroup.centralizer ({c} : Set G)) :
    ∃ k : ℕ, (Balance.oddQuotMk c ⟨m, hmC⟩) ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := h2 (QuotientGroup.mk ⟨m, hm⟩)
  refine ⟨k, ?_⟩
  have hmem : (⟨m, hm⟩ : ↥M) ^ 2 ^ k ∈ classicalInvolutionOddCore ↥M :=
    (QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow]; exact hk)
  have h1 : m ^ 2 ^ k ∈ Balance.oddCoreIn M := ⟨_, hmem, rfl⟩
  have h3 : m ^ 2 ^ k ∈ Balance.oddCoreIn (Subgroup.centralizer ({c} : Set G)) := hO h1
  have h4 := oddQuotMk_eq_one_of_mem_oddCoreIn h3 (Subgroup.pow_mem _ hmC _)
  rw [← h4, ← map_pow]
  rfl

theorem tightInO2_of_twinSet_pair (hΩ : HypOmegaGen Ω) (hcls : Q3CL.ClassicalClause Ω)
    (h2 : ∀ N ∈ Ω, IsPGroup 2 (↥N ⧸ classicalInvolutionOddCore ↥N)) {M M' : Subgroup G}
    {c b : G} (hM : M ∈ Ω) (hc : IsUniqueInvolution M c) (hne : M' ≠ M)
    (htw : twinSet Ω M = {M, M'}) (hb : b ∈ M ⊔ M')
    (hbC : b ∈ Subgroup.centralizer ({c} : Set G)) :
    TightInO2 (Balance.oddQuotMk c ⟨b, hbC⟩) := by
  have hM'T : M' ∈ twinSet Ω M := by rw [htw]; exact Or.inr rfl
  have hM' : M' ∈ Ω := hM'T.1
  have hc' : IsUniqueInvolution M' c := isUniqueInvolution_of_mem_twinSet hc hM'T
  have hMC : M ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6Gen.le_centralizer_of_isUniqueInvolution hc
  have hM'C : M' ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6Gen.le_centralizer_of_isUniqueInvolution hc'
  have hOM : Balance.oddCoreIn M ≤ Balance.oddCoreIn (Subgroup.centralizer ({c} : Set G)) :=
    Balance.oddCoreIn_le_of_isSubnormal (hcls.isSubnormal_of_uniqueInvolution hM hc)
  have hOM' : Balance.oddCoreIn M' ≤ Balance.oddCoreIn (Subgroup.centralizer ({c} : Set G)) :=
    Balance.oddCoreIn_le_of_isSubnormal (hcls.isSubnormal_of_uniqueInvolution hM' hc')
  have hcomm : ⁅M, M'⁆ ≤ oddCoreOf M ⊓ oddCoreOf M' :=
    Sec6Gen.comm_le_oddCore_of_twin hΩ hM hM' hne.symm hc hc'
  refine ⟨Balance.modOdd c (M ⊔ M'), ⟨fun p hp q => ?_⟩, fun ⟨p, hp⟩ => ?_,
    Balance.oddQuotMk_mem_modOdd hb hbC⟩
  ·
    obtain ⟨k, hk, rfl⟩ := Balance.mem_modOdd_iff.mp hp
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have e : (QuotientGroup.mk y : Balance.OddQuot c) * Balance.oddQuotMk c k *
        (QuotientGroup.mk y : Balance.OddQuot c)⁻¹ = Balance.oddQuotMk c (y * k * y⁻¹) := by
      show Balance.oddQuotMk c y * _ * (Balance.oddQuotMk c y)⁻¹ = _
      simp
    rw [e]
    exact Balance.mem_modOdd_iff.mpr ⟨y * k * y⁻¹, conj_mem_sup_twin hΩ hM hc hne htw y.2 hk, rfl⟩
  ·
    obtain ⟨k, hk, rfl⟩ := Balance.mem_modOdd_iff.mp hp
    obtain ⟨m, hm, m', hm', hkmm⟩ := exists_mul_of_mem_sup_twin hΩ hM hM' hne hc hc' hk
    obtain ⟨k₁, hk₁⟩ := exists_pow_oddQuotMk_eq_one (h2 M hM) hOM hm (hMC hm)
    obtain ⟨k₂, hk₂⟩ := exists_pow_oddQuotMk_eq_one (h2 M' hM') hOM' hm' (hM'C hm')
    have hkk : k = ⟨m, hMC hm⟩ * ⟨m', hM'C hm'⟩ := Subtype.ext hkmm
    have hcC : ⁅m, m'⁆ ∈ Subgroup.centralizer ({c} : Set G) := by
      simp only [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hMC hm) (hM'C hm'))
        (Subgroup.inv_mem _ (hMC hm))) (Subgroup.inv_mem _ (hM'C hm'))
    have hcm : Commute (Balance.oddQuotMk c ⟨m, hMC hm⟩)
        (Balance.oddQuotMk c ⟨m', hM'C hm'⟩) := by
      have h1 : ⁅m, m'⁆ ∈ Balance.oddCoreIn (Subgroup.centralizer ({c} : Set G)) :=
        hOM (hcomm (Subgroup.commutator_mem_commutator hm hm')).1
      have h3 := oddQuotMk_eq_one_of_mem_oddCoreIn h1 hcC
      have h4 : Balance.oddQuotMk c ⟨⁅m, m'⁆, hcC⟩ =
          ⁅Balance.oddQuotMk c ⟨m, hMC hm⟩, Balance.oddQuotMk c ⟨m', hM'C hm'⟩⁆ := by
        rw [← map_commutatorElement]
        rfl
      rw [h4] at h3
      exact commutatorElement_eq_one_iff_mul_comm.mp h3
    refine ⟨k₁ + k₂, Subtype.ext ?_⟩
    show (Balance.oddQuotMk c k) ^ 2 ^ (k₁ + k₂) = 1
    rw [hkk, map_mul, hcm.mul_pow]
    have e1 : (Balance.oddQuotMk c ⟨m, hMC hm⟩) ^ 2 ^ (k₁ + k₂) = 1 := by
      rw [pow_add, pow_mul, hk₁, one_pow]
    have e2 : (Balance.oddQuotMk c ⟨m', hM'C hm'⟩) ^ 2 ^ (k₁ + k₂) = 1 := by
      rw [add_comm, pow_add, pow_mul, hk₂, one_pow]
    rw [e1, e2, one_mul]

theorem tightInO2_of_twinProduct {K J : Subgroup G} {z t a g : G}
    (h : FrameIIHyp K J z t a g) {M M' : Subgroup G} {c b : G}
    (hM : M ∈ CoreAssembly.conjClass K) (hc : IsUniqueInvolution M c) (hne : M' ≠ M)
    (htw : twinSet (CoreAssembly.conjClass K) M = {M, M'}) (hb : b ∈ M ⊔ M')
    (hbC : b ∈ Subgroup.centralizer ({c} : Set G)) :
    TightInO2 (Balance.oddQuotMk c ⟨b, hbC⟩) :=
  tightInO2_of_twinSet_pair h.hyp h.cls
    (TwinADescent3.isPGroup_two_quotient_conjClass h.twoGroup) hM hc hne htw hb hbC

end TwinProduct

section Hyp51

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem hyp51At_of_tightInO2_image {B : Subgroup G} {c b : G} (hB : IsElemAbelian 2 B)
    (hcB : c ∈ B) (hc1 : c ≠ 1) (hbB : b ∈ B) (hb1 : b ≠ 1) (hbc : b ≠ c)
    (hbC : b ∈ Subgroup.centralizer ({c} : Set G))
    (ht : TightInO2 (Balance.oddQuotMk c ⟨b, hbC⟩)) : Hyp51At B c :=
  CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24.hyp51At_of_commute hB hcB hc1 hbB hb1 hbc hbC
    fun _ hL y hy => CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24.commute_of_tightInO2 ht hL y hy

end Hyp51

section Pairs

variable {G : Type} [Group G]

theorem isElemAbelian2_closure_pair_of_commute {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) (hcomm : x * y = y * x) :
    IsElemAbelian2 (Subgroup.closure ({x, y} : Set G)) 2 :=
  T7A.isElemAbelian2_closure_pair hx hy hx1 hy1 hxy hcomm

theorem isElemAbelian2_closure_pair_of_mem {B : Subgroup G} (hB : IsElemAbelian 2 B) {x y : G}
    (hx : x ∈ B) (hy : y ∈ B) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) :
    IsElemAbelian2 (Subgroup.closure ({x, y} : Set G)) 2 :=
  isElemAbelian2_closure_pair_of_commute (Lemma52Proof.mul_self_eq_one_of_mem hB hx)
    (Lemma52Proof.mul_self_eq_one_of_mem hB hy) hx1 hy1 hxy
    (Subgroup.mem_centralizer_singleton_iff.mp (Lemma52Proof.le_centralizer_of_mem hB hy hx))

theorem closure_pair_le_of_mem {B : Subgroup G} {x y : G} (hx : x ∈ B) (hy : y ∈ B) :
    Subgroup.closure ({x, y} : Set G) ≤ B := by
  rw [Subgroup.closure_le]
  rintro w (rfl | rfl)
  · exact hx
  · exact hy

end Pairs

section Alpha

variable {G : Type} [Group G] [Finite G]

theorem alphaOf_eq_of_hyp51 {B A D : Subgroup G} (hB : Hyp51 B) (hAB : A ≤ B) (hDB : D ≤ B)
    (hA : IsElemAbelian2 A 2) (hD : IsElemAbelian2 D 2) : alphaOf A = alphaOf D :=
  (lemma54_odd_and_eq hB hDB hD).2 A hAB hA

theorem odd_alphaOf_of_hyp51 {B A : Subgroup G} (hB : Hyp51 B) (hAB : A ≤ B)
    (hA : IsElemAbelian2 A 2) : Odd (Nat.card (alphaOf A)) :=
  (lemma54_odd_and_eq hB hAB hA).1

theorem oddCore_le_normalizer_alphaOf {B A : Subgroup G} {z : G} (hB : Hyp51 B) (hzB : z ∈ B)
    (hAB : A ≤ B) (hA : IsElemAbelian2 A 2) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤ Subgroup.normalizer (alphaOf A : Set G) :=
  T8T.oddCoreOf_centralizer_le_normalizer hB.1 hB.2.1 hzB
    (fun _ hDB hD => alphaOf_eq_of_hyp51 hB hDB hAB hD hA)

theorem conjSub_alphaOf_eq_of_mem_oddCore {B A : Subgroup G} {z o : G} (hB : Hyp51 B)
    (hzB : z ∈ B) (hAB : A ≤ B) (hA : IsElemAbelian2 A 2)
    (ho : o ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G))) :
    conjSub o (alphaOf A) = alphaOf A :=
  mem_normalizer_iff_conjSub_eq.mp (oddCore_le_normalizer_alphaOf hB hzB hAB hA ho)

theorem alphaOf_pair_eq_of_hyp51 {B : Subgroup G} (hB : Hyp51 B) {z u₁ u₂ : G} (hz : z ∈ B)
    (hu₁ : u₁ ∈ B) (hu₂ : u₂ ∈ B)
    (h₁ : IsElemAbelian2 (Subgroup.closure ({z, u₁} : Set G)) 2)
    (h₂ : IsElemAbelian2 (Subgroup.closure ({z, u₂} : Set G)) 2) :
    alphaOf (Subgroup.closure ({z, u₁} : Set G)) = alphaOf (Subgroup.closure ({z, u₂} : Set G)) :=
  alphaOf_eq_of_hyp51 hB (closure_pair_le_of_mem hz hu₁) (closure_pair_le_of_mem hz hu₂) h₁ h₂

theorem alphaOf_pair_eq_of_hyp51_of_mem {B : Subgroup G} (hB : Hyp51 B) {z u₁ u₂ : G}
    (hz : z ∈ B) (hz1 : z ≠ 1) (hu₁ : u₁ ∈ B) (hu₁1 : u₁ ≠ 1) (hu₁z : u₁ ≠ z) (hu₂ : u₂ ∈ B)
    (hu₂1 : u₂ ≠ 1) (hu₂z : u₂ ≠ z) :
    alphaOf (Subgroup.closure ({z, u₁} : Set G)) = alphaOf (Subgroup.closure ({z, u₂} : Set G)) :=
  alphaOf_pair_eq_of_hyp51 hB hz hu₁ hu₂
    (isElemAbelian2_closure_pair_of_mem hB.1 hz hu₁ hz1 hu₁1 hu₁z.symm)
    (isElemAbelian2_closure_pair_of_mem hB.1 hz hu₂ hz1 hu₂1 hu₂z.symm)

end Alpha

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
