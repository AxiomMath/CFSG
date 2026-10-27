module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeCommonField
public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley.RootOps

namespace LargeReeCatalog

@[expose] def largeReeAlpha44 : Fin F4.tag.rank → ℤ := ![1, 2, 3, 2]

@[expose] def largeReeAlpha47 : Fin F4.tag.rank → ℤ := ![2, 3, 4, 2]

@[expose] def largeReeAlpha44' : Fin Tag.F4.rank → ℤ := ![1, 2, 3, 2]

@[expose] def largeReeAlpha47' : Fin Tag.F4.rank → ℤ := ![2, 3, 4, 2]

@[expose] def largeReeE1' : Fin Tag.F4.rank → ℤ := Pi.single ⟨0, by decide⟩ 1

@[expose] def largeReeE4' : Fin Tag.F4.rank → ℤ := Pi.single ⟨3, by decide⟩ 1

theorem orbitCertRoot_largeRee :
    orbitCertRoot .F4 33 = largeReeE1' ∧ orbitCertRoot .F4 24 = largeReeE4' ∧
    orbitCertRoot .F4 25 = largeReeRoot 0 ∧ orbitCertRoot .F4 27 = largeReeRoot 1 ∧
    orbitCertRoot .F4 30 = largeReeRoot 3 ∧ orbitCertRoot .F4 44 = largeReeAlpha44' ∧
    orbitCertRoot .F4 47 = largeReeAlpha47' := by
  decide

theorem largeReeAlpha_duality :
    F4.dualRoot largeReeAlpha44 = largeReeAlpha47 ∧ F4.dualRoot largeReeAlpha47 = largeReeAlpha44 ∧
    F4.quadForm largeReeAlpha44 = 2 ∧ F4.quadForm largeReeAlpha47 = 2 * F4.prime := by
  decide

variable {K : Type} [Field K]

theorem f4x_44 (c : K) : f4x K 44 c = pinnedX F4.tag K largeReeAlpha44 c := by
  rw [f4x, orbitCertRoot_largeRee.2.2.2.2.2.1]
  rfl

theorem f4x_47 (c : K) : f4x K 47 c = pinnedX F4.tag K largeReeAlpha47 c := by
  rw [f4x, orbitCertRoot_largeRee.2.2.2.2.2.2]
  rfl

theorem isRoot_largeReeAlpha44 : IsRoot F4.tag largeReeAlpha44 ∧ 0 < height largeReeAlpha44 := by
  have h := f4_isRoot_pos (i := 44) ⟨by norm_num, by norm_num⟩
  rw [orbitCertRoot_largeRee.2.2.2.2.2.1] at h
  exact h

theorem isRoot_largeReeAlpha47 : IsRoot F4.tag largeReeAlpha47 ∧ 0 < height largeReeAlpha47 := by
  have h := f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩
  rw [orbitCertRoot_largeRee.2.2.2.2.2.2] at h
  exact h

theorem largeReeTestA_eq_largeReeA1X (a : ℕ) (t : K) :
    largeReeTestA K (2 ^ a) t = largeReeA1X a t := by
  rw [largeReeTestA, f4x, f4x, orbitCertRoot_largeRee.1, orbitCertRoot_largeRee.2.1,
    largeReeE1', largeReeE4', pinnedX_single, pinnedX_single]
  rfl

theorem largeReeTestB_eq_largeReeCoord (a : ℕ) (t : K) :
    largeReeTestB K (2 ^ a) t = largeReeCoord a K t 0 := by
  rw [largeReeTestB, f4x, f4x, f4x, orbitCertRoot_largeRee.2.2.1, orbitCertRoot_largeRee.2.2.2.1,
    orbitCertRoot_largeRee.2.2.2.2.1, largeReeCoord, largeReeP, largeReeSigma, largeReeSigma,
    zero_pow (by positivity), zero_add, ← pow_add, show largeReeX K 2 0 = 1 from pinnedX_zero _ _ _,
    mul_one, add_comm 2]
  rfl

end LargeReeCatalog

open LargeReeCatalog

theorem large_Ree_Sylow_center (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∃ S : Sylow 2 (F4.reeGamma K a), (S : Subgroup (F4.reeGamma K a)) =
      (F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) ∧
    ((Subgroup.center (F4.reeFixedPosUnipotent K a)).map (F4.reeFixedPosUnipotent K a).subtype :
        Set (ModGL F4.tag K)) =
      Set.range (fun c : K => pinnedX F4.tag K ![1, 2, 3, 2] c *
        pinnedX F4.tag K ![2, 3, 4, 2] (c ^ (2 * 2 ^ a))) ∧
    CFSG.IsElementaryAbelian 2 (Subgroup.center (F4.reeFixedPosUnipotent K a)) ∧
    Nat.card (Subgroup.center (F4.reeFixedPosUnipotent K a)) = 2 ^ (2 * a + 1) := by
  classical
  have h2 : (2 : K) = 0 := F4_two_eq_zero
  obtain ⟨ρ, σ, -, hσ, -, hσρ, -, hlong, hshort, -, -⟩ :=
    large_Ree_root_parameter_involution a K hK
  have hρσ : ∀ c, ρ (σ c) = c := fun c => congrArg (fun e : K ≃+* K => e c) hσρ
  obtain ⟨d44, d47, q44, q47⟩ := largeReeAlpha_duality
  have hs44 : largeReeAlpha44 ∈ F4.shortRoots :=
    ⟨isRoot_largeReeAlpha44.1, lengthParam_eq_one_iff.2 q44⟩
  have hl47 : largeReeAlpha47 ∈ F4.longRoots :=
    ⟨isRoot_largeReeAlpha47.1, lengthParam_eq_prime_iff.2 q47⟩
  have hne : largeReeAlpha44 ≠ largeReeAlpha47 := by decide
  obtain ⟨hCZ, hZJ, hJ⟩ := large_Ree_ambient_positive_centralizer a ha K hK
  have hcentral : ∀ (c d : K), ∀ g ∈ posUnipotent F4.tag K,
      g * (pinnedX F4.tag K largeReeAlpha44 c * pinnedX F4.tag K largeReeAlpha47 d) =
        (pinnedX F4.tag K largeReeAlpha44 c * pinnedX F4.tag K largeReeAlpha47 d) * g := by
    intro c d g hg
    have hmem : f4x K 44 c * f4x K 47 d ∈
        (Subgroup.center (posUnipotent .F4 K)).map (posUnipotent .F4 K).subtype := by
      rw [hZJ, ← SetLike.mem_coe, hJ]
      exact ⟨c, d, rfl⟩
    obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.1 hmem
    have hzg' : (z : ModGL .F4 K) = f4x K 44 c * f4x K 47 d := hzg
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hzg', f4x_44, f4x_47] at h
    exact h
  have hcomm : ∀ c d : K, pinnedX F4.tag K largeReeAlpha47 d * pinnedX F4.tag K largeReeAlpha44 c =
      pinnedX F4.tag K largeReeAlpha44 c * pinnedX F4.tag K largeReeAlpha47 d := fun c d => by
    have h := hcentral c 0 _ (pinnedX_mem_rootSpan (S := {α | IsRoot F4.tag α ∧ 0 < height α})
      isRoot_largeReeAlpha47 d)
    rwa [pinnedX_zero, mul_one] at h
  have hF : ∀ c d : K, ((F4.finiteReeAut K a ⟨pinnedX F4.tag K largeReeAlpha44 c *
      pinnedX F4.tag K largeReeAlpha47 d, mul_mem (pinnedX_mem_adjointGroup _ _)
        (pinnedX_mem_adjointGroup _ _)⟩ : adjointGroup F4.tag K) : ModGL F4.tag K) =
      pinnedX F4.tag K largeReeAlpha44 (ρ d) * pinnedX F4.tag K largeReeAlpha47 (σ c) := by
    intro c d
    have e : (⟨pinnedX F4.tag K largeReeAlpha44 c * pinnedX F4.tag K largeReeAlpha47 d,
        mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩ :
          adjointGroup F4.tag K) =
        ⟨pinnedX F4.tag K largeReeAlpha44 c, pinnedX_mem_adjointGroup _ _⟩ *
          ⟨pinnedX F4.tag K largeReeAlpha47 d, pinnedX_mem_adjointGroup _ _⟩ := rfl
    rw [e, map_mul, hshort _ hs44, hlong _ hl47, Subgroup.coe_mul, d44, d47]
    exact hcomm _ _
  have hP : ∀ c : K, pinnedX F4.tag K largeReeAlpha44 c *
      pinnedX F4.tag K largeReeAlpha47 (σ c) ∈ F4.reeFixedPosUnipotent K a := fun c =>
    Subgroup.mem_inf.2 ⟨mul_mem
      (pinnedX_mem_rootSpan (S := {α | IsRoot F4.tag α ∧ 0 < height α}) isRoot_largeReeAlpha44 c)
      (pinnedX_mem_rootSpan (S := {α | IsRoot F4.tag α ∧ 0 < height α}) isRoot_largeReeAlpha47 _),
      mem_reeGamma_of_fixed _ (by rw [hF, hρσ])⟩
  have hZ : ∀ c : K, (⟨_, hP c⟩ : F4.reeFixedPosUnipotent K a) ∈
      Subgroup.center (F4.reeFixedPosUnipotent K a) := fun c =>
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcentral _ _ _ (Subgroup.mem_inf.1 g.2).1)
  have hdesc : ∀ z : Subgroup.center (F4.reeFixedPosUnipotent K a), ∃ c : K,
      ((z : F4.reeFixedPosUnipotent K a) : ModGL F4.tag K) =
        pinnedX F4.tag K largeReeAlpha44 c * pinnedX F4.tag K largeReeAlpha47 (σ c) := by
    intro z
    obtain ⟨hzU, hzΓ⟩ := Subgroup.mem_inf.1 (z : F4.reeFixedPosUnipotent K a).2
    obtain ⟨g', hg'⟩ : ∃ g' : ModGL .F4 K,
        g' = ((z : F4.reeFixedPosUnipotent K a) : ModGL F4.tag K) := ⟨_, rfl⟩
    have hmem : g' ∈ posUnipotent .F4 K ⊓ Subgroup.centralizer (Subgroup.closure
        (Set.range (largeReeTestA K (2 ^ a)) ∪ Set.range (largeReeTestB K (2 ^ a))) :
          Set (ModGL .F4 K)) := by
      rw [hg']
      refine Subgroup.mem_inf.2 ⟨hzU, ?_⟩
      rw [Subgroup.centralizer_closure]
      refine Subgroup.mem_centralizer_iff.2 ?_
      have hcz : ∀ g ∈ F4.reeFixedPosUnipotent K a,
          g * ((z : F4.reeFixedPosUnipotent K a) : ModGL F4.tag K) =
            ((z : F4.reeFixedPosUnipotent K a) : ModGL F4.tag K) * g := fun g hg =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨g, hg⟩)
      rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · rw [largeReeTestA_eq_largeReeA1X]
        exact hcz _ (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent _ (largeReeA1X_mem_U1 hK t))
      · rw [largeReeTestB_eq_largeReeCoord]
        exact hcz _ (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent _ (largeReeCoord_mem hK t 0))
    rw [hCZ, hZJ, ← SetLike.mem_coe, hJ] at hmem
    obtain ⟨c, d, hcd⟩ := hmem
    have hcd' : pinnedX F4.tag K largeReeAlpha44 c * pinnedX F4.tag K largeReeAlpha47 d =
        ((z : F4.reeFixedPosUnipotent K a) : ModGL F4.tag K) := by
      rw [← f4x_44, ← f4x_47]
      exact hcd.trans hg'
    have hzΓ' : pinnedX F4.tag K largeReeAlpha44 c * pinnedX F4.tag K largeReeAlpha47 d ∈
        F4.reeGamma K a := by
      rw [hcd']
      exact hzΓ
    have hfix := finiteReeAut_eq_of_mem_reeGamma hzΓ'
      (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _))
    rw [hF] at hfix
    obtain ⟨-, hd⟩ := pinnedX_mul_pinnedX_inj (Or.inl ⟨isRoot_largeReeAlpha44,
      isRoot_largeReeAlpha47⟩) hne hfix
    exact ⟨c, hcd'.symm.trans (by rw [hd])⟩
  let f : K → Subgroup.center (F4.reeFixedPosUnipotent K a) := fun c => ⟨⟨_, hP c⟩, hZ c⟩
  have hf : Function.Bijective f := by
    refine ⟨fun c c' h => ?_, fun z => ?_⟩
    · have h' := congrArg (fun z : Subgroup.center (F4.reeFixedPosUnipotent K a) =>
        ((z : F4.reeFixedPosUnipotent K a) : ModGL F4.tag K)) h
      exact (pinnedX_mul_pinnedX_inj (Or.inl ⟨isRoot_largeReeAlpha44, isRoot_largeReeAlpha47⟩)
        hne h').1
    · obtain ⟨c, hc⟩ := hdesc z
      exact ⟨c, Subtype.ext (Subtype.ext hc.symm)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
    obtain ⟨S, hS⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
    exact ⟨S, hS⟩
  · ext g
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨c, hc⟩ := hdesc ⟨z, hz⟩
      refine ⟨c, ?_⟩
      change pinnedX F4.tag K largeReeAlpha44 c *
        pinnedX F4.tag K largeReeAlpha47 (c ^ (2 * 2 ^ a)) = _
      rw [← hσ]
      exact hc.symm
    · rintro ⟨c, rfl⟩
      refine ⟨⟨_, hP c⟩, hZ c, ?_⟩
      change pinnedX F4.tag K largeReeAlpha44 c * pinnedX F4.tag K largeReeAlpha47 (σ c) = _
      rw [hσ]
      rfl
  · refine { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun z => ?_ }
    obtain ⟨c, rfl⟩ := hf.2 z
    refine Subtype.ext (Subtype.ext ?_)
    change (pinnedX F4.tag K largeReeAlpha44 c * pinnedX F4.tag K largeReeAlpha47 (σ c)) ^ 2 = 1
    rw [sq, mul_assoc, ← mul_assoc (pinnedX F4.tag K largeReeAlpha47 (σ c)), hcomm, mul_assoc,
      ← mul_assoc, ← pinnedX_add, ← pinnedX_add, CharTwo.add_self_eq_zero,
      CharTwo.add_self_eq_zero, pinnedX_zero, pinnedX_zero, mul_one]
  · rw [← Nat.card_congr (Equiv.ofBijective f hf), hK]

end CFSG.ComponentClassification.UnbalancedCatalog
