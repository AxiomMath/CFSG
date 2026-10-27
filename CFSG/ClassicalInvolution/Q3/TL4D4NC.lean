module

public import CFSG.ClassicalInvolution.Q3.TL4D4NCTwoP
public import CFSG.ClassicalInvolution.Q3.Q3TJD4

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open scoped Pointwise

variable {K : Type} [Field K]

theorem smul_pointFamily_of_centralizes [Finite K] (hK : Nat.card K = 3) (β : MulAut (D4P K))
    (hodd : Odd (orderOf β)) (s : D4P K) (hs : orderOf s = 2)
    (hβ : ∀ c : D4P K, c * s = s * c → β c = c) :
    β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ s
  have hgg : g * g ∈
      (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf (StatedOmega (StatedQuadPlus 4 K)) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two]
    have := pow_orderOf_eq_one (QuotientGroup.mk' _ g : D4P K)
    rwa [hs] at this
  rw [Subgroup.mem_subgroupOf, mem_statedScalars_iff] at hgg
  obtain ⟨c, hc⟩ := mem_scalars.mp hgg
  set φ := toLinEquiv _ K g.val with hφ
  have hφ2 : ∀ v, φ (φ v) = c • v := fun v => by
    rw [← hc v, Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply]
  have hφO : φ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
    toLinEquiv_mem_orthogonalGroup g
  obtain ⟨-, a, -, ha⟩ := exists_hypPair_and_aniso hK (nondegenerate_polarBilin_quadPlus 4 K)
    (by rw [finrank_d4]; norm_num)
  have hc2 : c * c = 1 := by
    have h1 : quadPlus 4 K (φ (φ a)) = quadPlus 4 K a := by
      rw [map_of_mem hφO, map_of_mem hφO]
    rw [hφ2, map_smul_eq_sq] at h1
    have h2 : (c ^ 2 - 1) * quadPlus 4 K a = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    have h3 := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right ha)
    rw [← pow_two]
    exact h3
  rcases mul_self_eq_one_iff.mp hc2 with rfl | rfl
  · exact typeI_smul hK β g (fun x => by rw [hφ2, one_smul]) hβ
  · exact typeII_smul hK β hodd g (fun x => by rw [hφ2, neg_one_smul]) (hβ _ rfl)

theorem d4OddAutInner3_all : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
    Subgroup.center X = ⊥ →
      ∀ f : (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →* X,
        Function.Surjective f →
          f.ker ≤ Subgroup.center (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →
            ∀ s : X, orderOf s = 2 → ∀ α : MulAut X, Odd (orderOf α) →
              (∀ c ∈ Subgroup.centralizer ({s} : Set X),
                c⁻¹ * α c ∈ Balance.oddCoreIn (Subgroup.centralizer ({s} : Set X))) →
                ∃ g : X, α = MulAut.conj g := by
  intro X _ _ _ hZ f hf hker s hs α hodd hfix
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hOC : Balance.oddCoreIn (Subgroup.centralizer ({s} : Set X)) = ⊥ :=
    Q3.oddCentralizerFreeTag_POmegaPlus 4 Nat.prime_three trivial hadm X f hf hker s hs
  have hcent : ∀ c ∈ Subgroup.centralizer ({s} : Set X), α c = c := by
    intro c hc
    have h := hfix c hc
    rw [hOC, Subgroup.mem_bot] at h
    calc α c = c * (c⁻¹ * α c) := by group
      _ = c := by rw [h, mul_one]
  have hker' : f.ker = Subgroup.center (spinGroup (quadPlus 4 (GaloisField 3 1))) :=
    le_antisymm hker (ModelFacts.ChevAut.center_le_ker_of_surjective hf hZ)
  obtain ⟨e, he⟩ := Q3T.exists_mulEquiv_apply_eq f hf (Q3T.d4Proj (GaloisField 3 1))
    (spinToStatedProj_quadPlus (by norm_num : 3 ≤ 4)).1
    (hker'.trans (spinToStatedProj_quadPlus (by norm_num : 3 ≤ 4)).2.2.symm)
  set β := MulAut.congr e α with hβdef
  have hβ : ∀ c, c * e s = e s * c → β c = c := by
    intro c hc
    have hc' : e.symm c ∈ Subgroup.centralizer ({s} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hc
    change e (α (e.symm c)) = c
    rw [hcent _ hc', MulEquiv.apply_symm_apply]
  have hs' : orderOf (e s) = 2 := by rw [MulEquiv.orderOf_eq]; exact hs
  have hodd' : Odd (orderOf β) := by rw [hβdef, MulEquiv.orderOf_eq]; exact hodd
  have hF := smul_pointFamily_of_centralizes Q3T.natCard_galoisField_three β hodd' (e s) hs' hβ
  obtain ⟨y, hy⟩ := Q3T.exists_eq_conj_of_smul_statedPointFamily β hF hodd'
  refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
  exact hy

end CFSG.ClassicalInvolution.Q3.TL4
