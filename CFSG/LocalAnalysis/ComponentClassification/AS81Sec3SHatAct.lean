module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatTheta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup QuadraticMap CFSG.Open CFSG.Fischer Sec3Theta
open scoped Pointwise

namespace Sec3Theta

variable {G : Type} [Group G]

abbrev nSHat (Q₀ Q Zs : Subgroup G) : Subgroup G :=
  centralizer (Zs : Set G) ⊓ normalizer (sec3SHat (Q₀ ⊔ Q) Zs : Set G)

end Sec3Theta

namespace Sec38Hyp

namespace ThetaHyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  {H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀}
  {e : G} {b : Fin 6 → H.xsub.Qt} {t : Fin 6 → G}

@[expose] noncomputable def pre (hT : H.ThetaHyp e b t) (v : Census.V₀) : G :=
  Classical.choose (hT.theta_surjective v)

@[expose] noncomputable def actFun (hT : H.ThetaHyp e b t) (n : G) (v : Census.V₀) : Census.V₀ :=
  theta z e t (n * hT.pre v * n⁻¹)

variable (hT : H.ThetaHyp e b t)
include hT

theorem pre_mem (v : Census.V₀) : hT.pre v ∈ sec3SHat (Q₀ ⊔ Q) Zs :=
  (Classical.choose_spec (hT.theta_surjective v)).1

theorem theta_pre (v : Census.V₀) : theta z e t (hT.pre v) = v :=
  (Classical.choose_spec (hT.theta_surjective v)).2

omit [Finite G] hT in
theorem conj_mem {n : G} (hnS : n ∈ normalizer (sec3SHat (Q₀ ⊔ Q) Zs : Set G)) {s : G}
    (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) : n * s * n⁻¹ ∈ sec3SHat (Q₀ ⊔ Q) Zs :=
  (mem_normalizer_iff.mp hnS s).mp hs

variable {n : G} (hnZ : n ∈ centralizer (Zs : Set G))
  (hnS : n ∈ normalizer (sec3SHat (Q₀ ⊔ Q) Zs : Set G))
include hnZ hnS

theorem actFun_theta {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    hT.actFun n (theta z e t s) = theta z e t (n * s * n⁻¹) := by
  have hs' := hT.pre_mem (theta z e t s)
  have h := (hT.theta_eq_iff hs hs').mp (hT.theta_pre _).symm
  rw [actFun, eq_comm, hT.theta_eq_iff (conj_mem hnS hs) (conj_mem hnS hs')]
  have e1 : (n * hT.pre (theta z e t s) * n⁻¹)⁻¹ * (n * s * n⁻¹) =
      n * ((hT.pre (theta z e t s))⁻¹ * s) * n⁻¹ := by group
  rw [e1, ← mem_centralizer_iff.mp hnZ _ h, mul_inv_cancel_right]
  exact h

theorem actFun_add (v w : Census.V₀) :
    hT.actFun n (v + w) = hT.actFun n v + hT.actFun n w := by
  have hv := hT.pre_mem v
  have hw := hT.pre_mem w
  conv_lhs => rw [← hT.theta_pre v, ← hT.theta_pre w, ← hT.theta_mul hv hw]
  rw [hT.actFun_theta hnZ hnS (mul_mem hv hw),
    show n * (hT.pre v * hT.pre w) * n⁻¹ = (n * hT.pre v * n⁻¹) * (n * hT.pre w * n⁻¹) by group,
    hT.theta_mul (conj_mem hnS hv) (conj_mem hnS hw)]
  rfl

theorem Q₀_actFun (v : Census.V₀) : Census.Q₀ (hT.actFun n v) = Census.Q₀ v := by
  have hv := hT.pre_mem v
  have hsq := hT.mul_self_mem hv
  rw [actFun, hT.Q₀_theta (conj_mem hnS hv),
    show n * hT.pre v * n⁻¹ * (n * hT.pre v * n⁻¹) = n * (hT.pre v * hT.pre v) * n⁻¹ by group,
    ← mem_centralizer_iff.mp hnZ _ hsq, mul_inv_cancel_right, ← hT.Q₀_theta hv, hT.theta_pre]

theorem polar_actFun (v w : Census.V₀) :
    polar Census.Q₀ (hT.actFun n v) (hT.actFun n w) = polar Census.Q₀ v w := by
  rw [polar, ← hT.actFun_add hnZ hnS, hT.Q₀_actFun hnZ hnS, hT.Q₀_actFun hnZ hnS,
    hT.Q₀_actFun hnZ hnS, polar]

omit hnZ hnS in
theorem actFun_mul {n n' : G} (hn : n ∈ nSHat Q₀ Q Zs) (hn' : n' ∈ nSHat Q₀ Q Zs)
    (v : Census.V₀) : hT.actFun n (hT.actFun n' v) = hT.actFun (n * n') v := by
  have hv := hT.pre_mem v
  conv_lhs => rw [← hT.theta_pre v]
  rw [hT.actFun_theta hn'.1 hn'.2 hv, hT.actFun_theta hn.1 hn.2 (conj_mem hn'.2 hv),
    show n * (n' * hT.pre v * n'⁻¹) * n⁻¹ = (n * n') * hT.pre v * (n * n')⁻¹ by group]
  rfl

omit hnZ hnS in
theorem actFun_one (v : Census.V₀) : hT.actFun 1 v = v := by
  rw [actFun, one_mul, inv_one, mul_one, hT.theta_pre]

omit hnZ hnS in
theorem actFun_smul {n : G} (hn : n ∈ nSHat Q₀ Q Zs) (c : F4) (v : Census.V₀) :
    hT.actFun n (c • v) = c • hT.actFun n v := by
  have hn' : n⁻¹ ∈ nSHat Q₀ Q Zs := inv_mem hn
  have hsurj : ∀ w, hT.actFun n (hT.actFun n⁻¹ w) = w := fun w => by
    rw [hT.actFun_mul hn hn', mul_inv_cancel, hT.actFun_one]
  apply sub_eq_zero.mp
  refine Census.Q₀_nondegenerate.1 _ fun w => ?_
  rw [polarBilin_apply_apply, ← hsurj w, polar_sub_left, polar_smul_left,
    hT.polar_actFun hn.1 hn.2, hT.polar_actFun hn.1 hn.2, polar_smul_left, smul_eq_mul,
    sub_self]

omit hnZ hnS in
@[expose] noncomputable def actEquiv {n : G} (hn : n ∈ nSHat Q₀ Q Zs) :
    Census.V₀ ≃ₗ[F4] Census.V₀ where
  toFun := hT.actFun n
  invFun := hT.actFun n⁻¹
  map_add' := hT.actFun_add hn.1 hn.2
  map_smul' c v := by rw [RingHom.id_apply]; exact hT.actFun_smul hn c v
  left_inv v := by rw [hT.actFun_mul (inv_mem hn) hn, inv_mul_cancel, hT.actFun_one]
  right_inv v := by rw [hT.actFun_mul hn (inv_mem hn), mul_inv_cancel, hT.actFun_one]

omit hnZ hnS in
@[expose] noncomputable def hN : ↥(nSHat Q₀ Q Zs) →* TauCeti.QuadraticMap.orthogonalGroup Census.Q₀ where
  toFun n := ⟨hT.actEquiv n.2, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
    (hT.Q₀_actFun n.2.1 n.2.2)⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun v => hT.actFun_one v)
  map_mul' n n' := Subtype.ext (LinearEquiv.ext fun v => (hT.actFun_mul n.2 n'.2 v).symm)

omit hnZ hnS in
theorem hN_theta (n : ↥(nSHat Q₀ Q Zs)) {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    ((hT.hN n : TauCeti.QuadraticMap.orthogonalGroup Census.Q₀) : Census.V₀ ≃ₗ[F4] Census.V₀)
      (theta z e t s) = theta z e t ((n : G) * s * (n : G)⁻¹) :=
  hT.actFun_theta n.2.1 n.2.2 hs

omit hnZ hnS in
theorem conj_mem_U_of_smul (n : ↥(nSHat Q₀ Q Zs))
    (h : hT.hN n • Census.N0 = Census.N0) {u : G}
    (hu : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) :
    (n : G) * u * (n : G)⁻¹ ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := by
  have huS := H.U_le_SHat hT.hQF hu
  refine hT.mem_U_of_theta_mem (conj_mem n.2.2 huS) ?_
  rw [← hT.hN_theta n huS, ← h, Census.smul_N0_eq]
  exact ⟨_, hT.theta_image_U ▸ ⟨u, hu, rfl⟩, rfl⟩

omit hnZ hnS in
theorem smul_N0_of_conj (n : ↥(nSHat Q₀ Q Zs))
    (h : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G),
      (n : G) * u * (n : G)⁻¹ ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) :
    hT.hN n • Census.N0 = Census.N0 := by
  have hsub : hT.hN n • Census.N0 ⊆ Census.N0 := by
    rw [Census.smul_N0_eq]
    rintro _ ⟨v, hv, rfl⟩
    rw [← hT.theta_image_U] at hv ⊢
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨_, h u hu, (hT.hN_theta n (H.U_le_SHat hT.hQF hu)).symm⟩
  refine Set.eq_of_subset_of_ncard_le hsub ?_ Census.N0_finite
  rw [Census.smul_N0_eq, Set.ncard_image_of_injective _
    ((hT.hN n : TauCeti.QuadraticMap.orthogonalGroup Census.Q₀) :
      Census.V₀ ≃ₗ[F4] Census.V₀).injective]

omit [Finite G] hT hnZ hnS in
theorem mem_nSHat_of_mem_SHat {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    s ∈ nSHat Q₀ Q Zs :=
  ⟨SHat_le_C hs, le_normalizer hs⟩

omit hnZ hnS in
theorem hN_eq_one_of_mem_SHat {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    hT.hN ⟨s, mem_nSHat_of_mem_SHat hs⟩ = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  have hv := hT.pre_mem v
  conv_lhs => rw [← hT.theta_pre v]
  rw [hT.hN_theta _ hv]
  change theta z e t (s * hT.pre v * s⁻¹) = v
  have hc := hT.comm_mem_SHat hs hv
  rw [show s * hT.pre v * s⁻¹ = (s * hT.pre v * s⁻¹ * (hT.pre v)⁻¹) * hT.pre v by group,
    hT.theta_mul (H.Zs_le_U hT.hZQ hc |> H.U_le_SHat hT.hQF) hv,
    (hT.theta_eq_zero_iff (H.Zs_le_U hT.hZQ hc |> H.U_le_SHat hT.hQF)).mpr hc, zero_add,
    hT.theta_pre]

omit hnZ hnS in
theorem comm_mem_of_hN_eq_one (k : ↥(nSHat Q₀ Q Zs)) (h : hT.hN k = 1) {s : G}
    (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    (k : G) * s * (k : G)⁻¹ * s⁻¹ ∈ Zs := by
  have h1 := hT.hN_theta k hs
  rw [h] at h1
  change theta z e t s = theta z e t ((k : G) * s * (k : G)⁻¹) at h1
  have h2 := (hT.theta_eq_iff (conj_mem k.2.2 hs) hs).mp h1.symm
  have h3 : (k : G) * s * (k : G)⁻¹ * s⁻¹ = s * (s⁻¹ * ((k : G) * s * (k : G)⁻¹)) * s⁻¹ := by
    group
  rw [h3, ← mem_centralizer_iff.mp (SHat_le_C hs) _ h2, mul_inv_cancel_right]
  exact h2

end ThetaHyp

end Sec38Hyp

end CFSG.ComponentClassification.AS81
