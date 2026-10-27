module

public import CFSG.GF2Type.Smith1979.CaseIIA1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

structure IsK (t k : S.O) : Prop where
  comm : k * t = t * k
  fix : ∀ u ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), (k : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u

namespace IsK

theorem mul {k k' : S.O} (hk : IsK t k) (hk' : IsK t k') : IsK t (k * k') :=
  ⟨by rw [mul_assoc, hk'.comm, ← mul_assoc, hk.comm, mul_assoc], fun u hu => by
    rw [coe_mul_apply, hk'.fix u hu, hk.fix u hu]⟩

theorem inv {k : S.O} (hk : IsK t k) : IsK t k⁻¹ :=
  ⟨by
    calc k⁻¹ * t = k⁻¹ * (t * k) * k⁻¹ := by group
      _ = k⁻¹ * (k * t) * k⁻¹ := by rw [hk.comm]
      _ = t * k⁻¹ := by group, fun u hu => by
    have := hk.fix u hu
    calc ((k⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u =
        ((k⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := by rw [this]
      _ = u := inv_apply_apply_O k u⟩

theorem conj {k : S.O} (hk : IsK t k) (c : ↥(centralizer ({t} : Set S.O))) :
    IsK t ((c : S.O) * k * (c : S.O)⁻¹) := by
  have hc : (c : S.O) * t = t * (c : S.O) := mem_centralizer_singleton_iff.mp c.2
  have hc' : (c : S.O)⁻¹ * t = t * (c : S.O)⁻¹ :=
    calc (c : S.O)⁻¹ * t = (c : S.O)⁻¹ * (t * c) * (c : S.O)⁻¹ := by group
      _ = (c : S.O)⁻¹ * (c * t) * (c : S.O)⁻¹ := by rw [hc]
      _ = t * (c : S.O)⁻¹ := by group
  refine ⟨?_, fun u hu => ?_⟩
  · calc (c : S.O) * k * (c : S.O)⁻¹ * t = (c : S.O) * k * (t * (c : S.O)⁻¹) := by
          rw [mul_assoc _ _ t, hc', ← mul_assoc]
      _ = (c : S.O) * (k * t) * (c : S.O)⁻¹ := by group
      _ = (c : S.O) * (t * k) * (c : S.O)⁻¹ := by rw [hk.comm]
      _ = t * ((c : S.O) * k * (c : S.O)⁻¹) := by
          rw [← mul_assoc (c : S.O) t k, hc]
          group
  · have hu' : (((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈
        commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := apply_mem_commSpace_of_commute hc' hu
    rw [coe_mul_apply, coe_mul_apply, hk.fix _ hu']
    exact apply_inv_apply_O c u

end IsK

@[expose] noncomputable def alphaK (t k : S.O) :
    LinearMap.BilinForm (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
  S.q.polarBilin.compl₁₂ (secU t)
    ((((k : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1).comp (secU t))

theorem alphaK_apply (t k : S.O) (u u' : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    alphaK t k u u' = polar S.q (secU t u)
      ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) (secU t u') - secU t u') := rfl

namespace Data

variable (D : Data S g t)
include D

theorem secU_epsU_sub_mem (x : S.Qt) :
    secU t (epsU t x) - x ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have h1 : secU t (epsU t x) - x ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [mem_fixSpace, map_sub]
    have h := congrArg (fun w : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) => (w : S.Qt))
      (epsU_secU t (epsU t x))
    simp only [coe_epsU] at h
    exact sub_eq_sub_iff_sub_eq_sub.mp h
  rwa [← D.commSpace_eq_fixSpace] at h1

end Data

namespace IsK

variable (D : Data S g t)
include D

theorem sub_mem {k : S.O} (hk : IsK t k) (y : S.Qt) :
    (k : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have h1 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) y) =
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) y) := by
    rw [← coe_mul_apply, ← coe_mul_apply, hk.comm]
  have h2 := hk.fix _ (sub_mem_commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) y)
  rw [map_sub] at h2
  rw [D.commSpace_eq_fixSpace, mem_fixSpace, map_sub, h1]
  exact sub_eq_sub_iff_sub_eq_sub.mp h2

end IsK

namespace Data

variable (D : Data S g t)
include D

theorem resCt_epsU (c : ↥(centralizer ({t} : Set S.O))) (x : S.Qt) :
    resCt t c (epsU t x) = epsU t (((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) := by
  have hc : (c : S.O) * t = t * (c : S.O) := mem_centralizer_singleton_iff.mp c.2
  apply Subtype.ext
  rw [coe_resCt, coe_epsU, coe_epsU, map_sub, ← coe_mul_apply, ← coe_mul_apply, hc]

theorem alphaK_epsU {k : S.O} (hk : IsK t k) (x y : S.Qt) :
    alphaK t k (epsU t x) (epsU t y) =
      polar S.q x ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) := by
  have hy : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) (secU t (epsU t y)) - secU t (epsU t y) =
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y := by
    have h2 := hk.fix _ (D.secU_epsU_sub_mem y)
    rw [map_sub] at h2
    exact sub_eq_sub_iff_sub_eq_sub.mp h2
  rw [alphaK_apply, hy]
  have := D.omegaU_epsU x ⟨(k : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y, IsK.sub_mem D hk y⟩
  rw [omegaU_apply] at this
  exact this

theorem alphaK_alt {k : S.O} (hk : IsK t k) (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    alphaK t k u u = 0 := by
  obtain ⟨x, rfl⟩ := epsU_surjective t u
  rw [D.alphaK_epsU hk, polar_sub_right, polar_self_eq_zero, sub_zero, polar_comm,
    ← map_sub_eq_polar k.2 x]
  exact D.q_eq_zero (IsK.sub_mem D hk x)

theorem alphaK_conj {k : S.O} (hk : IsK t k) (c : ↥(centralizer ({t} : Set S.O)))
    (u u' : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    alphaK t ((c : S.O) * k * (c : S.O)⁻¹) u u' =
      alphaK t k (resCt t c⁻¹ u) (resCt t c⁻¹ u') := by
  obtain ⟨x, rfl⟩ := epsU_surjective t u
  obtain ⟨y, rfl⟩ := epsU_surjective t u'
  have h1 := D.alphaK_epsU (hk.conj c) x y
  have e1 : resCt t c⁻¹ (epsU t x) =
      epsU t ((((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) := D.resCt_epsU c⁻¹ x
  have e2 : resCt t c⁻¹ (epsU t y) =
      epsU t ((((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) := D.resCt_epsU c⁻¹ y
  have h2 := D.alphaK_epsU hk ((((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x)
    ((((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y)
  have e : (((c : S.O) * k * (c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y =
      ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) -
          (((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) := by
    rw [map_sub, apply_inv_apply_O]
    rfl
  have h3 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (c : S.O).2
    ((((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x)
    ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) -
      (((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y)
  rw [apply_inv_apply_O] at h3
  calc alphaK t ((c : S.O) * k * (c : S.O)⁻¹) (epsU t x) (epsU t y)
      = polar S.q x ((((c : S.O) * k * (c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) := h1
    _ = polar S.q x (((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) -
          (((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y)) := congrArg (polar S.q x) e
    _ = polar S.q ((((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x)
        ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) -
          (((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) := h3
    _ = alphaK t k (epsU t ((((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x))
        (epsU t ((((c : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y)) := h2.symm
    _ = alphaK t k (resCt t c⁻¹ (epsU t x)) (resCt t c⁻¹ (epsU t y)) := by rw [e1, e2]

theorem alphaK_mul {k k' : S.O} (hk : IsK t k) (hk' : IsK t k') :
    alphaK t (k * k') = alphaK t k + alphaK t k' := by
  refine LinearMap.ext fun u => LinearMap.ext fun u' => ?_
  obtain ⟨x, rfl⟩ := epsU_surjective t u
  obtain ⟨y, rfl⟩ := epsU_surjective t u'
  rw [LinearMap.add_apply, LinearMap.add_apply, D.alphaK_epsU (hk.mul hk'), D.alphaK_epsU hk,
    D.alphaK_epsU hk', ← polar_add_right]
  congr 1
  have h := hk.fix _ (IsK.sub_mem D hk' y)
  rw [map_sub] at h
  have h' := sub_eq_iff_eq_add.mp h
  show (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k' : S.Qt ≃ₗ[ZMod 2] S.Qt) y) - y = _
  rw [h']
  abel

theorem isK_t : IsK t t := ⟨rfl, fun u hu => by
  rw [D.commSpace_eq_fixSpace] at hu
  exact mem_fixSpace.mp hu⟩

theorem alphaK_t : alphaK t t = omegaU t := by
  refine LinearMap.ext fun u => LinearMap.ext fun u' => ?_
  obtain ⟨x, rfl⟩ := epsU_surjective t u
  obtain ⟨y, rfl⟩ := epsU_surjective t u'
  rw [D.alphaK_epsU D.isK_t, D.omegaU_epsU, coe_epsU]

theorem eq_one_of_alphaK_eq_zero {k : S.O} (hk : IsK t k) (h : alphaK t k = 0) : k = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun y => ?_)
  have hz : ∀ x : S.Qt, polar S.q x ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) = 0 := fun x => by
    rw [← D.alphaK_epsU hk, h]
    rfl
  have := S.q_nondegenerate.1 _ fun x => by
    rw [polarBilin_apply_apply, polar_comm]
    exact hz x
  exact sub_eq_zero.mp this

theorem K1 {k : S.O} (hk : IsK t k)
    (hcomm : ∀ r ∈ Rbar S g t, r * k * r⁻¹ = k ∨ r * k * r⁻¹ = k * t) : k = 1 ∨ k = t := by
  have hinv : ∀ γ ∈ D.Gam, ∃ c : ZMod 2, ∀ u v, alphaK t k (γ u) (γ v) =
      alphaK t k u v + c * omegaU t u v := by
    rintro _ ⟨r, rfl⟩
    have hmem : ((r⁻¹ : Rbar S g t) : S.O) ∈ centralizer ({t} : Set S.O) :=
      Rbar_le_centralizer D.H.conj_mem (r⁻¹).2
    have key : ∀ u v, alphaK t k (D.resR r u) (D.resR r v) =
        alphaK t (((r⁻¹ : Rbar S g t) : S.O) * k * ((r⁻¹ : Rbar S g t) : S.O)⁻¹) u v := by
      intro u v
      rw [D.alphaK_conj hk ⟨_, hmem⟩ u v]
      rfl
    rcases hcomm _ (r⁻¹).2 with h | h
    · refine ⟨0, fun u v => ?_⟩
      rw [key, h, zero_mul, add_zero]
    · refine ⟨1, fun u v => ?_⟩
      rw [key, h, D.alphaK_mul hk D.isK_t, D.alphaK_t, one_mul]
      rfl
  obtain ⟨c, hc⟩ := Sp.IsGamma.invariant_form D.isGamma D.spData (alphaK t k) (D.alphaK_alt hk) hinv
  rcases Sp.zmod2_cases c with rfl | rfl
  · left
    refine D.eq_one_of_alphaK_eq_zero hk (LinearMap.ext fun u => LinearMap.ext fun v => ?_)
    rw [hc u v, zero_mul]
    rfl
  · right
    have hkt : IsK t (k * t) := hk.mul D.isK_t
    have h0 : alphaK t (k * t) = 0 := by
      rw [D.alphaK_mul hk D.isK_t, D.alphaK_t]
      refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
      rw [LinearMap.add_apply, LinearMap.add_apply, hc u v, one_mul]
      exact Sp.zmod2_add_self _
    have h1 := D.eq_one_of_alphaK_eq_zero hkt h0
    have htt : t * t = 1 := mul_self_of_mem_Lbar S D.H.conj_mem D.ht
    calc k = k * (t * t) := by rw [htt, mul_one]
      _ = (k * t) * t := by rw [mul_assoc]
      _ = t := by rw [h1, one_mul]

end Data

end CFSG.GF2Type.Smith1979.Case2
