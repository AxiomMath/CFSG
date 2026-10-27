module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTable3
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieDatum
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieComponent
import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5T1
import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5T2
import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (STSetting sylowImg)
open CFSG.ClassicalInvolution.Q3.TA3.Q3L5
open scoped MatrixGroups

theorem normal_subgroupOf_centralizer_of_perfect {G : Type*} [Group G] {u : G} {H : Subgroup G}
    (hHC : H ≤ Subgroup.centralizer ({u} : Set G)) (hHp : ⁅H, H⁆ = H)
    (hmax : ∀ M : Subgroup G, M ≤ Subgroup.centralizer ({u} : Set G) → ⁅M, M⁆ = M → M ≤ H) :
    (H.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal := by
  refine ⟨fun x hx y => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have hy : (y : G) ∈ Subgroup.centralizer ({u} : Set G) := y.2
  have hM : H.map (MulAut.conj (y : G)).toMonoidHom ≤ Subgroup.centralizer ({u} : Set G) := by
    rintro _ ⟨h, hh, rfl⟩
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hy (hHC hh)) (Subgroup.inv_mem _ hy)
    simpa [MulAut.conj_apply] using this
  have hMp : ⁅H.map (MulAut.conj (y : G)).toMonoidHom, H.map (MulAut.conj (y : G)).toMonoidHom⁆ =
      H.map (MulAut.conj (y : G)).toMonoidHom := by
    rw [← Subgroup.map_commutator, hHp]
  have := hmax _ hM hMp ⟨x, hx, rfl⟩
  simpa [MulAut.conj_apply] using this

theorem component_map {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {u : G} {E : Subgroup G}
    (hEC : E ≤ Subgroup.centralizer ({u} : Set G))
    (hEn : (E.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal)
    (hq : CFSG.IsQuasisimple ↥E) :
    E.map φ.toMonoidHom ≤ Subgroup.centralizer ({φ u} : Set H) ∧
      ((E.map φ.toMonoidHom).subgroupOf (Subgroup.centralizer ({φ u} : Set H))).Normal ∧
      CFSG.IsQuasisimple ↥(E.map φ.toMonoidHom) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨q, hq', rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hEC hq')
    rw [Subgroup.mem_centralizer_singleton_iff]
    show φ q * φ u = φ u * φ q
    rw [← map_mul, ← map_mul, h1]
  · refine ⟨fun x hx y => ?_⟩
    obtain ⟨q, hq', hqx⟩ := Subgroup.mem_subgroupOf.mp hx
    have hy := y.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    have hyC : φ.symm y ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg φ.symm hy
      rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at this
    have hmem := hEn.conj_mem ⟨q, hEC hq'⟩ (Subgroup.mem_subgroupOf.mpr hq') ⟨φ.symm y, hyC⟩
    have hmem' := Subgroup.mem_subgroupOf.mp hmem
    refine Subgroup.mem_subgroupOf.mpr ⟨_, hmem', ?_⟩
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, map_mul, map_inv]
    rw [← hqx]
    simp
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (E.equivMapOfInjective φ.toMonoidHom φ.injective) hq

theorem negModel_PSL5 : NegModel .PSL 5 := by
  intro X _ _ hX K hK R hq
  obtain ⟨e⟩ := exists_mulEquiv_sl5 hX
  obtain ⟨t, P, SP, hD, hPK, hKt, hCN⟩ := pieceTightDatum X K hK R hq
  have ht2 : t * t = 1 := by rw [← sq, ← hD.order]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h
    have := hD.order
    rw [h, orderOf_one] at this
    omega
  have hz : e t * e t = 1 := by rw [← map_mul, ht2, map_one]
  have hz1 : e t ≠ 1 := fun h => ht1 (e.injective (by rw [h, map_one]))
  obtain ⟨c, hc⟩ := exists_conj_u hz hz1
  let ψ : SL(5, ZMod 3) ≃* X := (MulAut.conj c).trans e.symm
  have hψ : ∀ u : SL(5, ZMod 3), c⁻¹ * e t * c = u → ψ u = t := by
    intro u hu
    have : c * u * c⁻¹ = e t := by rw [← hu]; group
    show e.symm (c * u * c⁻¹) = t
    rw [this, MulEquiv.symm_apply_apply]
  obtain ⟨E, hEC, hEn, hEq⟩ : ∃ E : Subgroup X, E ≤ Subgroup.centralizer ({t} : Set X) ∧
      (E.subgroupOf (Subgroup.centralizer ({t} : Set X))).Normal ∧ CFSG.IsQuasisimple ↥E := by
    rcases hc with hc | hc
    · have hq1 : CFSG.IsQuasisimple ↥H₁ :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective blk₃_injective)
          (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (K := ZMod 3)
            (n := 3) (by norm_num))
      have hn1 := normal_subgroupOf_centralizer_of_perfect H₁_le
        (Subgroup.isPerfect_iff.mp isPerfect_H₁) perfect_le_H₁
      obtain ⟨h1, h2, h3⟩ := component_map ψ H₁_le hn1 hq1
      rw [hψ u₁ hc] at h1 h2
      exact ⟨_, h1, h2, h3⟩
    · have hq2 : CFSG.IsQuasisimple ↥H₂ :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective blk₄_injective)
          (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (K := ZMod 3)
            (n := 4) (by norm_num))
      have hn2 := normal_subgroupOf_centralizer_of_perfect H₂_le
        (Subgroup.isPerfect_iff.mp isPerfect_H₂) perfect_le_H₂
      obtain ⟨h1, h2, h3⟩ := component_map ψ H₂_le hn2 hq2
      rw [hψ u₂ hc] at h1 h2
      exact ⟨_, h1, h2, h3⟩
  rw [hCN] at hEC hEn
  exact false_of_normal_quasisimple_in_normalizer hK hEC hEn hEq

end CFSG.CGT.PushingUpLit.SolKNA
