module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut
open CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega (eq_one_of_mem_of_mem
  eq_one_of_mem_normalizer exists_smul_eq mem_smul_iff mem_conj_smul_iff smul_conj_smul
  smul_eq_of_mapsTo)
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem radRigid_of_stronglyEmbedded (hs : IsSimpleGroup X)
    (hX : ∀ T : Sylow 2 X,
      fusionStronglyEmbedded (Subgroup.normalizer ((T : Subgroup X) : Set X)) ∧
        Nat.card (Sylow 2 X) = Nat.card (T : Subgroup X) + 1)
    (hBT : HoldsTits X 2) : RadRigid 2 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro R hR α hfix hord
  obtain ⟨h0, hp, hc, hnt⟩ := hR
  obtain ⟨-, -, -, -, -, U, hUN⟩ := canonical_parabolic_tits hBT h0 hp
  rw [radInf_eq_of_pCoreOf hc] at hUN
  have hRU : R ≤ (U : Subgroup X) := by
    have hsup : IsPGroup 2 ↥(R ⊔ (U : Subgroup X)) := hp.to_sup_of_normal_left' U.isPGroup' hUN
    have h1 : R ⊔ (U : Subgroup X) = (U : Subgroup X) := U.is_maximal' hsup le_sup_right
    exact h1 ▸ le_sup_left
  obtain ⟨r0, hr0, hr01⟩ : ∃ r ∈ R, r ≠ 1 := (Subgroup.bot_or_exists_ne_one R).resolve_left h0
  have huniq : ∀ P : Sylow 2 X, R ≤ (P : Subgroup X) → P = U := by
    intro P hRP
    by_contra hPU
    exact hr01 (eq_one_of_mem_of_mem (hX U).1 hPU (hRU hr0) (hRP hr0))
  have hNR : Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer ((U : Subgroup X) : Set X) := by
    intro g hg
    refine Sylow.smul_eq_iff_mem_normalizer.mp (huniq _ fun q hq => ?_)
    rw [mem_conj_smul_iff]
    have hq' := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) q).mp hq
    rw [inv_inv] at hq'
    exact hRU hq'
  have hRUeq : R = (U : Subgroup X) := by
    refine le_antisymm hRU ?_
    have hUle : (U : Subgroup X) ≤ pCoreOf 2 (Subgroup.normalizer (R : Set X)) := by
      refine le_pCoreOf 2 hUN ?_ U.isPGroup'
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hUN]
      exact hNR
    rw [hc] at hUle
    exact hUle
  have hfixU : ∀ u ∈ (U : Subgroup X), α u = u := fun u hu => hfix u (hRUeq ▸ hu)
  have hαU : α • U = U := smul_eq_of_mapsTo fun s hs => by rw [hfixU s hs]; exact hs
  have hαinvU : α⁻¹ • U = U := by
    calc α⁻¹ • U = α⁻¹ • (α • U) := by rw [hαU]
      _ = U := inv_smul_smul α U
  have hα : α ^ orderOf α = 1 := pow_orderOf_eq_one α
  have hall : ∀ P : Sylow 2 X, α • P = P := by
    intro P
    by_cases hPU : P = U
    · rw [hPU]
      exact hαU
    · have hne : α • P ≠ U := by
        intro h
        apply hPU
        calc P = α⁻¹ • (α • P) := (inv_smul_smul α P).symm
          _ = α⁻¹ • U := by rw [h]
          _ = U := hαinvU
      obtain ⟨u₀, hu₀, hu₀P⟩ := exists_smul_eq (hX U).1 (hX U).2 hPU hne
      have hpow : ∀ n : ℕ, (α ^ n) • P = (u₀ ^ n) • P := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have hαu : α (u₀ ^ n) = u₀ ^ n := by rw [map_pow, hfixU u₀ hu₀]
          calc (α ^ (n + 1)) • P = α • ((α ^ n) • P) := by rw [pow_succ', mul_smul]
            _ = α • ((u₀ ^ n) • P) := by rw [ih]
            _ = α (u₀ ^ n) • (α • P) := smul_conj_smul α (u₀ ^ n) P
            _ = (u₀ ^ n) • (u₀ • P) := by rw [hαu, ← hu₀P]
            _ = (u₀ ^ (n + 1)) • P := by rw [← mul_smul, pow_succ]
      have hm : (u₀ ^ orderOf α) • P = P := by
        rw [← hpow, hα, one_smul]
      have hm1 : u₀ ^ orderOf α = 1 :=
        eq_one_of_mem_normalizer (hX U).1 hPU (U.1.pow_mem hu₀ _)
          (Sylow.smul_eq_iff_mem_normalizer.mp hm)
      have hu₀1 : u₀ = 1 := by
        refine eq_one_of_mem_pGroup_of_coprime U.isPGroup' hu₀ ?_
        exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hm1) hord
      rw [← hu₀P, hu₀1, one_smul]
  obtain ⟨K, hK⟩ : ∃ K : Subgroup X, K = (MulAction.toPermHom X (Sylow 2 X)).ker := ⟨_, rfl⟩
  have hKmem : ∀ g, g ∈ K ↔ ∀ P : Sylow 2 X, g • P = P := fun g => by
    rw [hK, MonoidHom.mem_ker, Equiv.ext_iff]
    simp [MulAction.toPermHom_apply, MulAction.toPerm_apply]
  haveI hKn : K.Normal := by rw [hK]; infer_instance
  have hKtop : K ≠ ⊤ := by
    intro htop
    apply (hX U).1.1
    rw [eq_top_iff]
    intro g _
    exact Sylow.smul_eq_iff_mem_normalizer.mp ((hKmem g).1 (htop ▸ Subgroup.mem_top g) U)
  have hK1 : K = ⊥ := (hs.eq_bot_or_eq_top_of_normal K).resolve_right hKtop
  refine MulEquiv.ext fun s => ?_
  have hg : s⁻¹ * α s ∈ K := by
    rw [hKmem]
    intro P
    have h1 : (α s) • P = s • P := by
      calc (α s) • P = (α s) • (α • P) := by rw [hall P]
        _ = α • (s • P) := (smul_conj_smul α s P).symm
        _ = s • P := hall _
    calc (s⁻¹ * α s) • P = s⁻¹ • ((α s) • P) := mul_smul _ _ _
      _ = s⁻¹ • (s • P) := by rw [h1]
      _ = P := inv_smul_smul s P
  rw [hK1, Subgroup.mem_bot] at hg
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp hg).symm

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
