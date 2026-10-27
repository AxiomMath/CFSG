module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCentralizers
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverCentralizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Matrix LinearAlgebra.Projectivization Pointwise

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)
local notation "G" => SuzukiMatrixGroup m

theorem suzuki_root_involution_coordinates (hm : 0 < m)
    (t : suzukiCoverRoot m) (ht : orderOf t = 2) :
    ∃ b : K, b ≠ 0 ∧ t = suzukiCoverRootElement m 0 b ∧
      t ∈ Subgroup.center (suzukiCoverRoot m) := by
  obtain ⟨a, b, hab⟩ := suzukiCoverRootElement_surjective m t
  have htt : t * t = 1 := by simpa only [ht, pow_two] using pow_orderOf_eq_one t
  rw [← hab, suzukiCoverRootElement_mul m hm,
    CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add,
    ← suzukiCoverRootElement_zero_zero m] at htt
  have ha0 : a = 0 := by
    have hzero := (suzukiCoverRootElement_injective m 0
      (a * suzukiCoverTits m a) 0 0 htt).2
    rcases mul_eq_zero.mp hzero with ha | ha
    · exact ha
    · exact (suzukiCoverTits m).injective (ha.trans (map_zero _).symm)
  rw [ha0] at hab
  have hb0 : b ≠ 0 := by
    intro hb
    rw [hb, suzukiCoverRootElement_zero_zero] at hab
    rw [← hab, orderOf_one] at ht
    omega
  refine ⟨b, hb0, hab.symm, ?_⟩
  rw [← (suzukiCoverRoot_structure m hm).2.2.1]
  exact ((suzukiCoverRoot_structure m hm).2.2.2 t).mpr ⟨b, hab.symm⟩

theorem suzuki_root_unique_ovoid_fixed (hm : 0 < m)
    (t : suzukiCoverRoot m) (ht : t ≠ 1) :
    let pinf : ℙ K (Fin 4 → K) := Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + suzukiCoverTits m x * x ^ 2 + suzukiCoverTits m y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    (Matrix.GeneralLinearGroup.toLin ((t : G) : GL (Fin 4) K)).toLinearEquiv • pinf = pinf ∧
      ∀ z ∈ O,
        (Matrix.GeneralLinearGroup.toLin ((t : G) : GL (Fin 4) K)).toLinearEquiv • z = z →
        z = pinf := by
  let pinf : ℙ K (Fin 4 → K) := Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + suzukiCoverTits m x * x ^ 2 + suzukiCoverTits m y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  rcases huppert_blackburn_XI_3_3 m hm (suzukiCoverTits m) (suzukiCoverTits_apply m) with
    ⟨_, _, _, _, _, _, _, hstab⟩
  change _ = pinf ∧ ∀ z ∈ O, _ = z → z = pinf
  refine ⟨(hstab t.val).mpr ((le_sup_left : suzukiCoverRootGL m ≤
    suzukiCoverRootGL m ⊔ suzukiCoverTorusGL m) t.property), ?_⟩
  intro z hz htz
  by_contra hzinf
  obtain ⟨r, _, huniq⟩ := suzukiRootClosure_regular_on_ovoid_complement
    m (suzukiCoverTits m) (suzukiCoverTits_apply m) z z hz hz hzinf hzinf
  have heq : (suzukiCoverRootBridge m) t = 1 :=
    (huniq ((suzukiCoverRootBridge m) t) htz).trans
      (huniq 1 (by
        change (Matrix.GeneralLinearGroup.toLin (1 : GL (Fin 4) K)).toLinearEquiv • z = z
        rw [map_one]
        change (1 : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) • z = z
        exact one_smul _ z)).symm
  apply ht
  exact (suzukiCoverRootBridge m).injective (heq.trans (map_one _).symm)

theorem suzuki_root_involution_centralizer_le_normalizer (hm : 0 < m)
    (t : suzukiCoverRoot m) (ht : orderOf t = 2) :
    Subgroup.centralizer ({(t : G)} : Set G) ≤
      Subgroup.normalizer (suzukiCoverRoot m : Set G) := by
  let pinf : ℙ K (Fin 4 → K) := Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + suzukiCoverTits m x * x ^ 2 + suzukiCoverTits m y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let linRep : G →* LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (SuzukiMatrixGroup m).subtype
  let : MulAction G (ℙ K (Fin 4 → K)) := MulAction.compHom _ linRep
  rcases huppert_blackburn_XI_3_3 m hm (suzukiCoverTits m) (suzukiCoverTits_apply m) with
    ⟨hpres, _, _, _, _, _, _, hstab⟩
  have htne : t ≠ 1 := by intro ht1; rw [ht1, orderOf_one] at ht; omega
  obtain ⟨htfix, huniq⟩ := suzuki_root_unique_ovoid_fixed m hm t htne
  intro c hc
  have hct : Commute c (t : G) := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcO : c • pinf ∈ O := hpres c pinf (Or.inl rfl)
  have hcfix : (t : G) • (c • pinf) = c • pinf := by
    rw [← mul_smul, ← hct.eq, mul_smul]
    exact congrArg (fun z : ℙ K (Fin 4 → K) => c • z) htfix
  have hcinf : (Matrix.GeneralLinearGroup.toLin (c : GL (Fin 4) K)).toLinearEquiv • pinf = pinf :=
    huniq (c • pinf) hcO hcfix
  rw [suzukiCoverRoot_normalizer m hm]
  have hmem : (c : GL (Fin 4) K) ∈ suzukiCoverRootGL m ⊔ suzukiCoverTorusGL m :=
    (hstab c).mp hcinf
  change c ∈ (suzukiCoverRootGL m).subgroupOf (SuzukiMatrixGroup m) ⊔
    (suzukiCoverTorusGL m).subgroupOf (SuzukiMatrixGroup m)
  rw [← Subgroup.subgroupOf_sup (suzukiCoverRootGL_le m) (suzukiCoverTorusGL_le m)]
  exact hmem

theorem suzuki_root_involution_full_centralizer (hm : 0 < m)
    (t : suzukiCoverRoot m) (ht : orderOf t = 2) :
    Subgroup.centralizer ({(t : G)} : Set G) = suzukiCoverRoot m := by
  obtain ⟨b, hb, htb, htcenter⟩ := suzuki_root_involution_coordinates m hm t ht
  apply le_antisymm
  · intro c hc
    obtain ⟨r, x, hfactor⟩ := suzukiCoverRoot_normalizer_decomposition m hm c
      (suzuki_root_involution_centralizer_le_normalizer m hm t ht hc)
    let s := suzukiCoverTorusHom m x
    let az := coverNormalizerAction (suzukiCoverRoot m) (suzukiCoverTorus m)
      (suzukiCoverTorus_le_normalizer m) s t
    have hconj : r * az * r⁻¹ = t := by
      apply Subtype.ext
      change r.val * az.val * r.val⁻¹ = t.val
      dsimp only [az]
      rw [coverNormalizerAction_coe]
      have hct := Subgroup.mem_centralizer_singleton_iff.mp hc
      have heq : c * t.val * c⁻¹ = t.val := by rw [hct, mul_inv_cancel_right]
      rw [hfactor, mul_inv_rev] at heq
      simpa only [mul_assoc] using heq
    have haz : az = t := by
      have h := congrArg (fun z : suzukiCoverRoot m => r⁻¹ * z * r) hconj
      have hcentral : r⁻¹ * t * r = t :=
        (show Commute r t from (Subgroup.mem_center_iff.mp htcenter r)).inv_mul_cancel
      simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel_right, inv_mul_cancel, mul_one, hcentral] using h
    have hnorm : suzukiCoverNorm m x = 1 := by
      apply Units.ext
      have h := congrArg (fun z : suzukiCoverRoot m =>
        (((z : G) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 2) haz
      dsimp only [az, s] at h
      rw [htb, suzukiCoverTorus_action_root] at h
      change (x : K) * suzukiCoverTits m (x : K) * b = b at h
      exact mul_right_cancel₀ hb (h.trans (one_mul b).symm)
    have hx : x = 1 := (suzukiCoverNorm_bijective m).1 (hnorm.trans (map_one _).symm)
    rw [hfactor, hx, map_one, OneMemClass.coe_one, mul_one]
    exact r.property
  · intro r hr
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp htcenter (⟨r, hr⟩ : suzukiCoverRoot m))

theorem suzuki_involution_centralizer_isPGroup (hm : 0 < m)
    (t : G) (ht : orderOf t = 2) :
    IsPGroup 2 (Subgroup.centralizer ({t} : Set G)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card
    simpa only [Nat.card_zpowers, ht] using (show Nat.card (Subgroup.zpowers t) = 2 ^ 1 by
      simp only [Nat.card_zpowers, ht, pow_one])
  obtain ⟨P, hTP⟩ := hTp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P (suzukiCoverSylow m hm)
  have htP : t ∈ (P : Subgroup G) := hTP (Subgroup.mem_zpowers t)
  have hctR : (MulAut.conj c) t ∈ suzukiCoverRoot m := by
    change (MulAut.conj c) t ∈ (suzukiCoverSylow m hm : Subgroup G)
    rw [← hc, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul t (MulAut.conj c) (P : Subgroup G) htP
  let s : suzukiCoverRoot m := ⟨(MulAut.conj c) t, hctR⟩
  have hs : orderOf s = 2 := (Subgroup.orderOf_coe s).symm.trans
    ((orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective t).trans ht)
  have hCtwo : IsPGroup 2 (Subgroup.centralizer ({(s : G)} : Set G)) := by
    rw [suzuki_root_involution_full_centralizer m hm s hs]
    exact (suzukiCoverRoot_structure m hm).1
  exact hCtwo.of_equiv (elementCentralizerEquiv (MulAut.conj c) t).symm

theorem suzuki_model_involution_centralizers_two {F : Type*} [Group F]
    {k : Type} [Field k] [Finite k] (a : ℕ) (ha : 1 ≤ a)
    (hcard : Nat.card k = 2 ^ (2 * a + 1)) (e : F ≃* GLASzGroup a k) :
    ∀ t : F, orderOf t = 2 → IsPGroup 2 (Subgroup.centralizer ({t} : Set F)) := by
  let E := (e.trans (glaSzEquivNative a ha hcard)).trans (suzukiCoverNativeEquiv a)
  intro t ht
  have hEt : orderOf (E t) = 2 := (orderOf_injective E.toMonoidHom E.injective t).trans ht
  exact (suzuki_involution_centralizer_isPGroup a (by omega) (E t) hEt).of_equiv
    (elementCentralizerEquiv E t).symm

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
