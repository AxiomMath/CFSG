module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusCore
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightResidualMain

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.EvenSmallLie
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Trans

variable {G P : Type*} [Group G] [Group P] {L : Subgroup G}

theorem modelToG_trans_symm_mulAut (e : L ≃* P) (δ : MulAut P) (H : Subgroup P) :
    modelToG (e.trans δ.symm) H = modelToG e (H.map δ.toMonoidHom) := by
  ext g
  simp only [UnitaryPilot.mem_modelToG, mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨δ x, ⟨x, hx, rfl⟩, by rw [MulEquiv.symm_trans_apply, MulEquiv.symm_symm]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by rw [MulEquiv.symm_trans_apply, MulEquiv.symm_symm]⟩

end Trans

section Elt

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conj_eq_mul_forall_le_centralizer_plus_four_of_mem (hset : SeitzSetting G L)
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hR5 : ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot (coordinateQuadPlus 4 K) (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot (coordinateQuadPlus 4 K) (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)))
    {y₀ : matrixProjectiveDerived (coordinateQuadPlus 4 K)} (hy₀A : y₀ ∈ plusA K) (hy₀1 : y₀ ≠ 1)
    (hy₀o : Odd (orderOf y₀)) :
    ∃ g : G, g⁻¹ * t * g = t * (e.symm (plusZ K) : G) ∧
      ∀ S : Subgroup G, ⁅S, S⁆ = S → (∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤) →
        S ≤ centralizer ({g⁻¹ * t * g} : Set G) →
        S ≤ centralizer ({(e.symm y₀ : G)} : Set G) →
        (e.symm (plusZ K) : G) ∈ S →
        S ≤ centralizer (modelToG e (stabTwoBar K 0 1) : Set G) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hK; omega
    · exact h
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv_plus (le_refl 4) hf hK e
  have htC := mem_centralizer_of_inf_eq hKt
  have h₁₂ : (plusPair K 0).Orth (flipPair (plusPair K 1)) := plusPair_orth_flip (by decide)
  have h₁₃ : (plusPair K 0).Orth (plusPair K 2) := plusPair_orth (by decide)
  have h₂₃ : (flipPair (plusPair K 1)).Orth (plusPair K 2) :=
    orth_flipPair_left (plusPair_orth (by decide))
  obtain ⟨x, z, -, hxz, ⟨hzL, hzl⟩, ⟨hzx, hzl'⟩⟩ := hR5
  have hc : ∃ c, c * e ⟨z, hzL⟩ * c⁻¹ = plusZ K := isConj_iff.mp (isConj_of_isLongRoot hQ h₁₂
    h₁₃ h₂₃ hzl (isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃))
  obtain ⟨c', hc'⟩ := hc
  set c : L := e.symm c'⁻¹ with hcdef
  have htc : ∀ m ∈ L, t * m = m * t := fun m hm => (mem_centralizer_iff.mp htC m hm).symm
  have hcz : (c : G)⁻¹ * z * c = (e.symm (plusZ K) : G) := by
    have h1 : (c⁻¹ * ⟨z, hzL⟩ * c : L) = e.symm (plusZ K) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, hcdef,
        MulEquiv.apply_symm_apply, inv_inv, ← hc']
    rw [← h1]
    rfl
  have hxzx : x * z * x⁻¹ ∈ L := by
    obtain ⟨m, hm, hmz⟩ := hzx
    rw [← hmz]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show x * (x⁻¹ * m * x) * x⁻¹ = m by group]
    exact hm
  have hsymm : (((conjugateMulEquiv L x).symm ⟨z, hzx⟩ : L) : G) = x * z * x⁻¹ := by
    set w : G := (((conjugateMulEquiv L x).symm ⟨z, hzx⟩ : L) : G) with hw
    have h1 := coe_conjugateMulEquiv L x ((conjugateMulEquiv L x).symm ⟨z, hzx⟩)
    rw [MulEquiv.apply_symm_apply] at h1
    have h1' : z = x⁻¹ * w * x := h1
    calc w = x * (x⁻¹ * w * x) * x⁻¹ := by group
      _ = x * z * x⁻¹ := by rw [← h1']
  have hg : (x * (c : G))⁻¹ * t * (x * c) = t * (e.symm (plusZ K) : G) := by
    rw [← hcz, show (x * (c : G))⁻¹ * t * (x * c) = (c : G)⁻¹ * (x⁻¹ * t * x) * c by group, hxz,
      show (c : G)⁻¹ * (t * z) * c = (c : G)⁻¹ * t * (z * c) by group, ← htc _ (inv_mem c.2)]
    group
  refine ⟨x * c, hg, fun S hSperf hSsimple hSt hSy hzS => ?_⟩
  refine le_centralizer_stabTwoBar_of_conj_eq_mul_plus hset.standardSetting hOut hq e ht htC hg ?_
    hy₀A hy₀1 hy₀o hSperf hSsimple hSt hSy hzS
  have he : x * (c : G) * (e.symm (plusZ K) : G) * (x * c)⁻¹ = x * z * x⁻¹ := by
    rw [← hcz]; group
  refine ⟨he ▸ hxzx, ?_⟩
  have hzz : (⟨x * (c : G) * (e.symm (plusZ K) : G) * (x * c)⁻¹, he ▸ hxzx⟩ : L) =
      (conjugateMulEquiv L x).symm ⟨z, hzx⟩ := Subtype.ext (he.trans hsymm.symm)
  rw [hzz]
  exact hzl'

theorem exists_conj_eq_mul_forall_le_centralizer_plus_four_aut (hset : SeitzSetting G L)
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hR5 : ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot (coordinateQuadPlus 4 K) (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot (coordinateQuadPlus 4 K) (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)))
    (δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    {y₀ : matrixProjectiveDerived (coordinateQuadPlus 4 K)} (hy₀A : y₀ ∈ plusA K) (hy₀1 : y₀ ≠ 1)
    (hy₀o : Odd (orderOf y₀)) :
    ∃ g : G, g⁻¹ * t * g = t * (e.symm (δ (plusZ K)) : G) ∧
      ∀ S : Subgroup G, ⁅S, S⁆ = S → (∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤) →
        S ≤ centralizer ({g⁻¹ * t * g} : Set G) →
        S ≤ centralizer ({(e.symm (δ y₀) : G)} : Set G) →
        (e.symm (δ (plusZ K)) : G) ∈ S →
        S ≤ centralizer (modelToG e ((stabTwoBar K 0 1).map δ.toMonoidHom) : Set G) := by
  have hs : ∀ y, (e.trans δ.symm).symm y = e.symm (δ y) := fun y => by
    rw [MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  obtain ⟨x, z, hz, hxz, ⟨hzL, hzl⟩, ⟨hzx, hzl'⟩⟩ := hR5
  obtain ⟨g, hg, hS⟩ := exists_conj_eq_mul_forall_le_centralizer_plus_four_of_mem hset hK hq
    (e.trans δ.symm) ht hKt ⟨x, z, hz, hxz, ⟨hzL, isLongRoot_map_plus (by norm_num) δ.symm _ hzl⟩,
      ⟨hzx, isLongRoot_map_plus (by norm_num) δ.symm _ hzl'⟩⟩ hy₀A hy₀1 hy₀o
  refine ⟨g, by rw [hg, hs], fun S hSperf hSsimple hSt hSy hzS => ?_⟩
  rw [← modelToG_trans_symm_mulAut]
  exact hS S hSperf hSsimple hSt (by rwa [hs]) (by rwa [hs])

end Elt

end CFSG.SeitzReduction.OmegaPilot
