module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowSummand
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverBasic

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ClassicalGroups.Orthogonal
open CFSG.OddStandard.SmallF3.HypA2 (TypU)
open scoped MatrixGroups

variable {K U V : Type} [Field K] [Finite K] [AddCommGroup U] [Module K U] [AddCommGroup V]
  [Module K V] [Finite V] {Q₀ : QuadraticForm K U} {Q : QuadraticForm K V}

theorem a2l_neg_mul_comm (B : U ≃ₗ[K] U) : LinearEquiv.neg K * B = B * LinearEquiv.neg K :=
  LinearEquiv.ext fun d => by simp

theorem a2l_neg_mul_self : LinearEquiv.neg K * LinearEquiv.neg K = (1 : U ≃ₗ[K] U) :=
  LinearEquiv.ext fun d => by simp

theorem a2lDatum_projElementary_of_summand [Nontrivial U] (h2 : (2 : K) ≠ 0)
    (S : A2lSummand Q₀ Q) {v : V} (hv0 : v ≠ 0) (hv : S.coords v = 0) {q₀ : ℕ} (hodd : Odd q₀)
    (h5 : 5 ≤ q₀) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = q₀)
    (φ : SL(2, F) →* (U ≃ₗ[K] U)) (hφ : Function.Injective φ)
    (hφE : ∀ g, φ g ∈ elementaryGroup Q₀) (hφt : φ (a2lNegOne F) = LinearEquiv.neg K)
    (hq : CFSG.IsQuasisimple ↥(elementaryGroup Q₀)) (hTU : TypU ↥(elementaryGroup Q₀)) :
    a2lDatum (ProjElementary Q) := by
  haveI : Finite (V ≃ₗ[K] V) := a2l_finite_linearEquiv
  have hnegE : LinearEquiv.neg K ∈ elementaryGroup Q₀ := hφt ▸ hφE _
  let ΦE : ↥(elementaryGroup Q₀) →* ↥(elementaryGroup Q) :=
    ((S.Phi).comp (elementaryGroup Q₀).subtype).codRestrict (elementaryGroup Q)
      fun B => S.Phi_mem_elementaryGroup h2 B.2
  have hΦE : Function.Injective ΦE := fun a b h =>
    Subtype.ext (S.Phi_injective (congrArg Subtype.val h))
  let Φφ : SL(2, F) →* ↥(elementaryGroup Q) :=
    ((S.Phi).comp φ).codRestrict (elementaryGroup Q)
      fun g => S.Phi_mem_elementaryGroup h2 (hφE g)
  have hΦφ : Function.Injective Φφ := fun a b h =>
    hφ (S.Phi_injective (congrArg Subtype.val h))
  let t : ↥(elementaryGroup Q) :=
    ⟨S.Phi (LinearEquiv.neg K), S.Phi_mem_elementaryGroup h2 hnegE⟩
  have hvfix : ∀ B : U ≃ₗ[K] U, S.Phi B v = v := fun B =>
    S.embHom_apply_of_coords_eq_zero _ B hv
  have hscal : ∀ {x : ↥(elementaryGroup Q)}, (x : V ≃ₗ[K] V) v = v →
      QuotientGroup.mk' ((scalars K V).subgroupOf (elementaryGroup Q)) x = 1 → x = 1 := by
    intro x hxv hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    obtain ⟨c, hc⟩ := mem_scalars.1 hx
    have hc1 : c = 1 := by
      have h := hc v
      rw [hxv] at h
      have h' : (1 - c) • v = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
      have := (smul_eq_zero.1 h').resolve_right hv0
      linear_combination -this
    refine Subtype.ext (LinearEquiv.ext fun w => ?_)
    rw [hc w, hc1, one_smul]
    rfl
  refine a2lDatum_of_block_normal (P := ↥(elementaryGroup Q))
    (QuotientGroup.mk' ((scalars K V).subgroupOf (elementaryGroup Q)))
    (QuotientGroup.mk'_surjective _) ?_ hodd h5 (t := t) ?_ ?_
    (J := ΦE.range) (N := Φφ.range) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [QuotientGroup.ker_mk'] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (commute_of_mem_scalars hx y.1).symm
  · refine Subtype.ext ?_
    change S.Phi (LinearEquiv.neg K) * S.Phi (LinearEquiv.neg K) = 1
    rw [← map_mul, a2l_neg_mul_self, map_one]
  · intro hπ
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hπ
    obtain ⟨c, hc⟩ := mem_scalars.1 hπ
    have hc1 : c = 1 := by
      have h := hc v
      change S.Phi (LinearEquiv.neg K) v = c • v at h
      rw [hvfix] at h
      have h' : (1 - c) • v = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
      have := (smul_eq_zero.1 h').resolve_right hv0
      linear_combination -this
    obtain ⟨d, hd⟩ := exists_ne (0 : U)
    have h := hc (S.incl d)
    change S.Phi (LinearEquiv.neg K) (S.incl d) = c • S.incl d at h
    rw [S.Phi_apply_incl, hc1, one_smul] at h
    have h' : (2 : K) • S.incl d = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h]
      simp
    exact hd (S.incl_injective (by
      rw [(smul_eq_zero.1 h').resolve_left h2, map_zero]))
  · rintro _ ⟨g, rfl⟩
    exact ⟨⟨φ g, hφE g⟩, rfl⟩
  · exact ⟨a2lNegOne F, Subtype.ext (by
      change S.Phi (φ (a2lNegOne F)) = S.Phi (LinearEquiv.neg K)
      rw [hφt])⟩
  · rintro _ ⟨B, rfl⟩
    rw [mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    change S.Phi B * S.Phi (LinearEquiv.neg K) = S.Phi (LinearEquiv.neg K) * S.Phi B
    rw [← map_mul, ← map_mul, a2l_neg_mul_comm]
  · rintro g hg _ ⟨B, rfl⟩
    have hgt : (g : V ≃ₗ[K] V) * S.Phi (LinearEquiv.neg K) = S.Phi (LinearEquiv.neg K) * g :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.1 hg)
    have hKey := S.hasKey_of_commute h2 hgt
    have hAO := S.actEquiv_mem_orthogonalGroup h2 hKey
      (elementaryGroup_le_orthogonalGroup Q g.2)
    have hE := conj_mem_elementaryGroup hAO B.2
    refine ⟨⟨_, hE⟩, Subtype.ext ?_⟩
    exact (S.conj_Phi hKey B).symm
  · exact CFSG.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hΦE).symm hq
  · rintro _ ⟨B, rfl⟩ hx
    exact hscal (hvfix B) hx
  · exact ⟨F, inferInstance, inferInstance, hF, ⟨(MonoidHom.ofInjective hΦφ).symm⟩⟩
  · exact a2l_typU_of_mulEquiv (MonoidHom.ofInjective hΦE) hTU

end CFSG.OddStandard.SmallF3.HypA2Leaves
