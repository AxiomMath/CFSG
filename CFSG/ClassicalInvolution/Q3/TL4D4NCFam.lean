module

public import CFSG.ClassicalInvolution.Q3.Q3TJD4Fam
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
open CFSG.ComponentClassification.CatalogueBStabilizerFamily
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type} [Field K]

abbrev D4P (K : Type) [Field K] : Type := StatedProj (StatedOmega (StatedQuadPlus 4 K))

theorem act_ts (u : D4P K) {W : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hdim : Module.finrank K W = 4)
    (hts : ∀ v ∈ W, StatedQuadPlus 4 K v = 0) :
    Module.finrank K (statedProjectiveSubspaceAction (StatedQuadPlus 4 K) u W) = 4 ∧
      ∀ v ∈ statedProjectiveSubspaceAction (StatedQuadPlus 4 K) u W,
        StatedQuadPlus 4 K v = 0 := by
  obtain ⟨U, rfl⟩ := QuotientGroup.mk'_surjective _ u
  rw [statedProjectiveSubspaceAction_mk_apply]
  refine ⟨?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq]
    exact hdim
  · rintro _ ⟨v, hv, rfl⟩
    have h := Q3T.quadPlus_mulVec_of_mem_statedOmega U.2 v
    rw [coe_quadPlus] at h
    rw [LinearEquiv.coe_coe, toLinEquiv_apply, h]
    exact hts v hv

theorem smul_pointFamily_of_fixPoint [Finite K] (β : MulAut (D4P K)) (Y : Set (D4P K))
    (hβ : ∀ y ∈ Y, β y = y) (L : Points (quadPlus 4 K))
    (hL : ∀ y ∈ Y, statedPointAction (coe_quadPlus 4 K) y L = L)
    (hno : ∀ W : Submodule K (Fin 4 ⊕ Fin 4 → K), Module.finrank K W = 4 →
      (∀ v ∈ W, StatedQuadPlus 4 K v = 0) →
        ¬ ∀ y ∈ Y, statedProjectiveSubspaceAction (StatedQuadPlus 4 K) y W = W) :
    β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  set P₀ := statedPointStabilizer (coe_quadPlus 4 K) L with hP₀
  have hP₀F : P₀ ∈ statedPointFamily (coe_quadPlus 4 K) := ⟨L, rfl⟩
  have hmem : ∀ y ∈ Y, y ∈ P₀.map β.toMonoidHom := fun y hy => ⟨y, hL y hy, hβ y hy⟩
  have hexcl : ∀ W : Submodule K (Fin 4 ⊕ Fin 4 → K), Module.finrank K W = 4 →
      (∀ v ∈ W, StatedQuadPlus 4 K v = 0) → P₀.map β.toMonoidHom ∉
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) W) := by
    rintro W hdim hts ⟨u, hu⟩
    obtain ⟨hdim', hts'⟩ := act_ts u hdim hts
    refine hno _ hdim' hts' fun y hy => ?_
    have hy' := hmem y hy
    rw [← hu] at hy'
    obtain ⟨t, ht, hty⟩ := hy'
    have ht' : statedProjectiveSubspaceAction (StatedQuadPlus 4 K) t W = W := ht
    have hty' : u * t * u⁻¹ = y := hty
    rw [← hty', ← Equiv.Perm.mul_apply, ← map_mul, show u * t * u⁻¹ * u = u * t by group,
      map_mul, Equiv.Perm.mul_apply, ht']
  have hO := stated_pointFamily_orbit_subset (K := K) (n := 4) rfl (MulAction.mem_orbit _ β)
  have hP₀β : P₀.map β.toMonoidHom ∈ β • statedPointFamily (coe_quadPlus 4 K) :=
    Set.mem_smul_set.mpr ⟨P₀, hP₀F, rfl⟩
  rcases hO with h | h | h
  · exact h
  · rw [h] at hP₀β
    exact absurd hP₀β (hexcl _ (flag_data le_rfl).1 (flag_data le_rfl).2)
  · rw [h] at hP₀β
    exact absurd hP₀β (hexcl _ (Xstar_data (by norm_num)).1 (Xstar_data (by norm_num)).2)

theorem smul_pointFamily_ne (γ : MulAut (D4P K)) (y u : D4P K) (Z : Submodule K (Fin 4 ⊕ Fin 4 → K))
    (hγ : γ y = y)
    (hZ : statedProjectiveSubspaceAction (StatedQuadPlus 4 K) y
      (statedProjectiveSubspaceAction (StatedQuadPlus 4 K) u Z) =
        statedProjectiveSubspaceAction (StatedQuadPlus 4 K) u Z)
    (hno : ∀ L : Points (quadPlus 4 K), statedPointAction (coe_quadPlus 4 K) y L ≠ L) :
    γ • statedPointFamily (coe_quadPlus 4 K) ≠
      conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) Z) := by
  intro h
  set M := (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) Z).map
    (MulAut.conj u).toMonoidHom with hM
  have hMC : M ∈ conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) Z) :=
    ⟨u, rfl⟩
  rw [← h] at hMC
  obtain ⟨N, hN, hNM⟩ := Set.mem_smul_set.mp hMC
  obtain ⟨L, hL⟩ := hN
  have hNM' : N.map γ.toMonoidHom = M := hNM
  have hyM : y ∈ M := by
    refine ⟨u⁻¹ * y * u, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    change statedProjectiveSubspaceAction (StatedQuadPlus 4 K) (u⁻¹ * y * u) Z = Z
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hZ, ← Equiv.Perm.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply]
  have hyN : y ∈ N := by
    rw [← hNM'] at hyM
    obtain ⟨x, hx, hxy⟩ := hyM
    have hxy' : γ x = y := hxy
    have : x = y := by
      apply γ.injective
      rw [hxy', hγ]
    rw [← this]
    exact hx
  rw [← hL] at hyN
  exact hno L hyN

theorem smul_eq_of_orbit_three {G α : Type*} [Group G] [MulAction G α] (β : G)
    (hodd : Odd (orderOf β)) (F A B : α) (hO : ∀ γ : G, γ • F = F ∨ γ • F = A ∨ γ • F = B)
    (h1 : β • F ≠ A) (h2 : (β * β) • F ≠ A) : β • F = F := by
  rcases hO β with h | h | h
  · exact h
  · exact absurd h h1
  rcases hO (β * β) with h' | h' | h'
  · obtain ⟨k, hk⟩ := hodd
    have hpow : β = (β * β) ^ (k + 1) := by
      rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf β + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    have hmem : β * β ∈ MulAction.stabilizer G F := h'
    have hmem' := Subgroup.pow_mem _ hmem (k + 1)
    rw [← hpow] at hmem'
    exact hmem'
  · exact absurd h' h2
  · rw [mul_smul, h] at h'
    rw [← h] at h'
    exact smul_left_cancel β h'

theorem smul_pointFamily_of_fixMax [Finite K] (β : MulAut (D4P K)) (hodd : Odd (orderOf β))
    (y u : D4P K) (hβ : β y = y) (Z : Submodule K (Fin 4 ⊕ Fin 4 → K))
    (hZX : Z = flag 4 K 4 ∨ Z = Xstar 4 K (by norm_num))
    (hZ : statedProjectiveSubspaceAction (StatedQuadPlus 4 K) y
      (statedProjectiveSubspaceAction (StatedQuadPlus 4 K) u Z) =
        statedProjectiveSubspaceAction (StatedQuadPlus 4 K) u Z)
    (hno : ∀ L : Points (quadPlus 4 K), statedPointAction (coe_quadPlus 4 K) y L ≠ L) :
    β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  have hβ2 : (β * β) y = y := by rw [MulAut.mul_apply, hβ, hβ]
  have hO := fun γ : MulAut (D4P K) =>
    stated_pointFamily_orbit_subset (K := K) (n := 4) rfl (MulAction.mem_orbit _ γ)
  rcases hZX with rfl | rfl
  · refine smul_eq_of_orbit_three β hodd _ _
      (conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
        (Xstar 4 K (by norm_num)))) hO
      (smul_pointFamily_ne β y u _ hβ hZ hno) (smul_pointFamily_ne (β * β) y u _ hβ2 hZ hno)
  · refine smul_eq_of_orbit_three β hodd _ _
      (conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
        (flag 4 K 4))) (fun γ => ?_)
      (smul_pointFamily_ne β y u _ hβ hZ hno) (smul_pointFamily_ne (β * β) y u _ hβ2 hZ hno)
    rcases hO γ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

end CFSG.ClassicalInvolution.Q3.TL4
