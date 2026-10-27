module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsOrthBlock
public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsCentral

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open (IsSubnormal)
open QuadraticMap TauCeti.QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section Orthogonal

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {K : Type} [Group K]

theorem commute_map_of_isSubnormal_centralizer_orthogonal (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hQ : (polarBilin Q).Nondegenerate) (θ : K →* (V ≃ₗ[F] V))
    (hθO : θ.range ≤ orthogonalGroup Q) (hθE : elementaryGroup Q ≤ θ.range)
    (hker : θ.ker ≤ Subgroup.center K) {w : K} (hw : w * w = 1) {N : Subgroup K}
    (hNs : IsSubnormal N (Subgroup.centralizer ({w} : Set K))) (hsolv : Group.IsSolvable N)
    (hodd' : IsOddGenerated N) : ∀ x ∈ N, ∀ y ∈ N, θ x * θ y = θ y * θ x := by
  have hii : θ w * θ w = 1 := by rw [← map_mul, hw, map_one]
  have hiO : θ w ∈ orthogonalGroup Q := hθO ⟨w, rfl⟩
  have hCw : Subgroup.centralizer ({w} : Set K) ≤
      (Subgroup.centralizer ({θ w} : Set (V ≃ₗ[F] V))).comap θ := by
    intro c hc
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hc]
  have hnorm : ((Subgroup.centralizer ({w} : Set K)).subgroupOf
      ((Subgroup.centralizer ({θ w} : Set (V ≃ₗ[F] V))).comap θ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCw]
    intro c g hc hg
    refine conj_mem_centralizer_of_commutator_mem_center ?_ hc
    apply hker
    rw [MonoidHom.mem_ker]
    have hgi : θ g * θ w = θ w * θ g :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hg)
    simp only [map_mul, map_inv]
    rw [hgi]
    group
  have hNsC := CFSG.ClassicalInvolution.isSubnormal_trans hNs
    (CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hCw hnorm)
  have hmap := CFSG.ClassicalInvolution.ModelFacts.isSubnormal_map θ hNsC
  rw [Subgroup.map_comap_eq] at hmap
  have hsolv' : Group.IsSolvable ↥(N.map θ) :=
    Group.isSolvable_of_surjective (f := θ.subgroupMap N) (MonoidHom.subgroupMap_surjective θ N)
  have hc := commute_of_isSubnormal_centralizer_involution hodd h5 hQ hθO hθE hiO hii hmap hsolv'
    (isOddGenerated_map θ hodd')
  intro x hx y hy
  exact hc _ (Subgroup.mem_map_of_mem θ hx) _ (Subgroup.mem_map_of_mem θ hy)

theorem derivedSeries_two_eq_bot_of_orthogonal (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (θ : K →* (V ≃ₗ[F] V))
    (hθO : θ.range ≤ orthogonalGroup Q) (hθE : elementaryGroup Q ≤ θ.range)
    (hker : θ.ker ≤ Subgroup.center K) {w : K} (hw : w * w = 1) {N : Subgroup K}
    (hNs : IsSubnormal N (Subgroup.centralizer ({w} : Set K))) (hsolv : Group.IsSolvable N)
    (hodd' : IsOddGenerated N) : derivedSeries ↥N 2 = ⊥ := by
  have hc := commute_map_of_isSubnormal_centralizer_orthogonal hodd h5 hQ θ hθO hθE hker hw hNs
    hsolv hodd'
  refine derivedSeries_two_eq_bot_of_commutator_mem (B := θ.ker) (fun a _ b hb => ?_)
    fun x hx y hy => ?_
  · exact Subgroup.mem_center_iff.mp (hker hb) a
  · rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hc x hx y hy)

variable [Finite K]

theorem false_of_isClassicalMember3_of_orthogonal {X : Type} [Group X] [Finite X]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (hQ : (polarBilin Q).Nondegenerate)
    (θ : K →* (V ≃ₗ[F] V)) (hθO : θ.range ≤ orthogonalGroup Q) (hθE : elementaryGroup Q ≤ θ.range)
    (hθker : θ.ker ≤ Subgroup.center K) (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z) :
    False := by
  refine false_of_isClassicalMember3_of_oddGenerated ψ hψ hker ?_ h
  intro w hw N _ hNs hsolv hodd'
  exact derivedSeries_two_eq_bot_of_orthogonal hodd h5 hQ θ hθO hθE hθker hw hNs hsolv hodd'

end Orthogonal

end CFSG.ClassicalInvolution.Q3
