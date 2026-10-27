module

public import CFSG.LieType.SeitzGeneration.OrthHyperRad
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {F : Type} [Group F]

@[expose] def qFix (φ : F →* (V ≃ₗ[K] V)) : Submodule K V where
  carrier := {v | ∀ f, φ f v = v}
  add_mem' := fun {a b} ha hb f => by rw [map_add, ha f, hb f]
  zero_mem' := fun f => map_zero _
  smul_mem' := fun c v hv f => by rw [map_smul, hv f]

theorem mem_qFix {φ : F →* (V ≃ₗ[K] V)} {v : V} : v ∈ qFix φ ↔ ∀ f, φ f v = v := Iff.rfl

variable [Fintype F]

@[expose] noncomputable def qAvg (φ : F →* (V ≃ₗ[K] V)) (v : V) : V :=
  ((Fintype.card F : ℕ) : K)⁻¹ • ∑ f : F, φ f v

theorem qAvg_mem (φ : F →* (V ≃ₗ[K] V)) (v : V) : qAvg φ v ∈ qFix φ := by
  intro g
  unfold qAvg
  rw [map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun f => ?_)
  rw [Equiv.coe_mulLeft, map_mul, LinearEquiv.mul_apply]

theorem polar_qAvg {φ : F →* (V ≃ₗ[K] V)}
    (hφ : ∀ f, φ f ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hF : ((Fintype.card F : ℕ) : K) ≠ 0) {c : V} (hc : c ∈ qFix φ) (v : V) :
    polar Q c (qAvg φ v) = polar Q c v := by
  unfold qAvg
  rw [polar_smul_right_eq]
  have h1 : polar Q c (∑ f : F, φ f v) = ∑ f : F, polar Q c (φ f v) :=
    map_sum (polarBilin Q c) (fun f => φ f v) Finset.univ
  have h2 : ∀ f : F, polar Q c (φ f v) = polar Q c v := fun f => by
    have := polar_map_of_mem (hφ f) c v
    rwa [hc f] at this
  rw [h1]
  simp only [h2, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K, smul_eq_mul]
  field_simp

theorem sub_qAvg_mem_qPerp {φ : F →* (V ≃ₗ[K] V)}
    (hφ : ∀ f, φ f ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hF : ((Fintype.card F : ℕ) : K) ≠ 0) (v : V) : v - qAvg φ v ∈ qPerp Q (qFix φ) := by
  intro c hc
  rw [polar_sub_right, polar_qAvg hφ hF hc, sub_self]

theorem polarNondegOn_qFix {φ : F →* (V ≃ₗ[K] V)} (hQ : (polarBilin Q).Nondegenerate)
    (hφ : ∀ f, φ f ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hF : ((Fintype.card F : ℕ) : K) ≠ 0) : PolarNondegOn Q (qFix φ) := by
  intro c hc hcc
  refine eq_zero_of_polar_eq_zero hQ fun v => ?_
  have h1 : v = qAvg φ v + (v - qAvg φ v) := by abel
  have h2 : polar Q c (v - qAvg φ v) = 0 := sub_qAvg_mem_qPerp hφ hF v c hc
  rw [h1, polar_add_right, hcc _ (qAvg_mem φ v), zero_add]
  exact h2

theorem commute_eichler_of_fix {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {u w : V} (hu : g u = u) (hw : g w = w) :
    g * eichler Q u w = eichler Q u w * g := by
  have h := eichler_conj hg u w
  rw [hu, hw] at h
  exact mul_inv_eq_iff_eq_mul.1 h

end CFSG.LieType.SeitzGeneration
