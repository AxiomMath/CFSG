module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefs
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Input19DeltaReduction

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving

theorem localDeltaIn_eq_bot_of_outer {M : Type*} [Group M] [Finite M] (J H D : Subgroup M)
    [J.Normal] (hJH : J ≤ H) {f : M} (hfD : f ∈ D) (hf1 : f ≠ 1)
    (hi : GLAPPrimeCoreOf 3 (J ⊓ Subgroup.centralizer ({f} : Set M)) = ⊥)
    (hii : ∀ y ∈ Subgroup.centralizer ((J ⊓ Subgroup.centralizer ({f} : Set M) : Subgroup M) : Set M),
      Nat.Coprime 3 (orderOf y) → y = 1) :
    localDeltaIn 3 H D = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  set X : Subgroup M := H ⊓ Subgroup.centralizer ({f} : Set M) with hX
  set Sf : Subgroup M := J ⊓ Subgroup.centralizer ({f} : Set M) with hSf
  have hyN : y ∈ GLAPPrimeCoreOf 3 X := by
    have := (Subgroup.mem_iInf.1 hy f)
    have := (Subgroup.mem_iInf.1 this) hfD
    exact (Subgroup.mem_iInf.1 this) hf1
  have hSfX : Sf ≤ X := inf_le_inf_right _ hJH
  set N : Subgroup M := GLAPPrimeCoreOf 3 X with hN
  have hcop : Nat.Coprime 3 (Nat.card N) := coprime_card_GLAPPrimeCoreOf Nat.prime_three X
  have hNX : N ≤ X := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hNnorm : ∀ g ∈ X, ∀ w ∈ N, g * w * g⁻¹ ∈ N := by
    intro g hg w hw
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw
    exact ⟨⟨g, hg⟩ * z * ⟨g, hg⟩⁻¹, (GLAPPrimeCore.normal 3 X).conj_mem z hz ⟨g, hg⟩, rfl⟩
  refine hii y ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsX : s ∈ X := hSfX hs
    have hcomN : y * s * y⁻¹ * s⁻¹ ∈ N := by
      have : y * s * y⁻¹ * s⁻¹ = y * (s * y⁻¹ * s⁻¹) := by group
      rw [this]
      exact N.mul_mem hyN (hNnorm s hsX _ (N.inv_mem hyN))
    have hcomJ : y * s * y⁻¹ * s⁻¹ ∈ J :=
      J.mul_mem (Subgroup.Normal.conj_mem inferInstance s hs.1 _) (J.inv_mem hs.1)
    have hcomC : y * s * y⁻¹ * s⁻¹ ∈ Subgroup.centralizer ({f} : Set M) := by
      have hyC : y ∈ Subgroup.centralizer ({f} : Set M) := (hNX hyN).2
      have hsC : s ∈ Subgroup.centralizer ({f} : Set M) := hs.2
      exact mul_mem (mul_mem (mul_mem hyC hsC) (inv_mem hyC)) (inv_mem hsC)
    have hcomS : y * s * y⁻¹ * s⁻¹ ∈ Sf := ⟨hcomJ, hcomC⟩
    set Q : Subgroup Sf := (N ⊓ J).subgroupOf Sf with hQ
    have hQn : Q.Normal := by
      refine ⟨fun w hw g => ?_⟩
      rw [hQ, Subgroup.mem_subgroupOf] at hw ⊢
      refine ⟨?_, ?_⟩
      · exact hNnorm g (hSfX g.2) w hw.1
      · exact Subgroup.Normal.conj_mem inferInstance _ hw.2 _
    have hQc : Nat.Coprime 3 (Nat.card Q) := by
      by_contra h3
      have h3' : 3 ∣ Nat.card Q := by
        by_contra hnd
        exact h3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd)
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 h3'
      have hq1 : orderOf ((q : Sf) : M) = 3 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hq]
      have hqN : ((q : Sf) : M) ∈ N := q.2.1
      have := Subgroup.orderOf_dvd_natCard N hqN
      rw [hq1] at this
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop this
    have hQle : Q ≤ GLAPPrimeCore 3 ↥Sf := le_sSup ⟨hQn, hQc⟩
    have hmem : (⟨y * s * y⁻¹ * s⁻¹, hcomS⟩ : Sf) ∈ Q := by
      rw [hQ, Subgroup.mem_subgroupOf]
      exact ⟨hcomN, hcomJ⟩
    have h1 : y * s * y⁻¹ * s⁻¹ ∈ GLAPPrimeCoreOf 3 Sf :=
      ⟨_, hQle hmem, rfl⟩
    rw [hi, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  · exact (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N hyN) hcop)

theorem innerAut_normal' (K : Type*) [Group K] : (innerAut K).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨a, rfl⟩ := hn
  refine ⟨g a, ?_⟩
  ext z
  simp [MulAut.conj_apply]

theorem isLocallyBalancedAbs_three_two_of_outer {K : Type*} [Group K] [Finite K]
    (h : ∀ D : Subgroup (MulAut K), IsElemAbelian 3 D → Nat.card D = 9 →
      ∃ f ∈ D, f ≠ 1 ∧
        GLAPPrimeCoreOf 3 (innerAut K ⊓ Subgroup.centralizer ({f} : Set (MulAut K))) = ⊥ ∧
        ∀ y ∈ Subgroup.centralizer
          ((innerAut K ⊓ Subgroup.centralizer ({f} : Set (MulAut K)) : Subgroup (MulAut K)) :
            Set (MulAut K)), Nat.Coprime 3 (orderOf y) → y = 1) :
    IsLocallyBalancedAbs 3 2 K := by
  intro D hD hcard H hH _
  haveI := innerAut_normal' K
  obtain ⟨f, hfD, hf1, hi, hii⟩ := h D hD (by rw [hcard]; norm_num)
  exact localDeltaIn_eq_bot_of_outer (innerAut K) H D hH hfD hf1 hi hii

end CFSG.HardMathSupport.Solomon.Coordinator
