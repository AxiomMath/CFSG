module

public import CFSG.LieType.Chevalley.BorelSelfNormalizer
public import CFSG.LieType.Chevalley.OppositeBorel

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem xUnit_mem_posUnipotent
    (i : Fin τ.rank) (c : K) : xUnit τ K i c ∈ posUnipotent τ K := by
  rw [← pinnedX_single]
  exact Subgroup.mem_iSup_of_mem (Pi.single i 1) (Subgroup.mem_iSup_of_mem
    ⟨isRoot_single τ i, by rw [height_single]; exact one_pos⟩ (Subgroup.subset_closure ⟨c, rfl⟩))

theorem yUnit_mem_negUnipotent
    (i : Fin τ.rank) (c : K) : yUnit τ K i c ∈ negUnipotent τ K := by
  rw [← pinnedX_neg_single]
  exact Subgroup.mem_iSup_of_mem (-Pi.single i 1) (Subgroup.mem_iSup_of_mem
    ⟨isRoot_neg_single τ i, by rw [height_neg, height_single]; omega⟩
    (Subgroup.subset_closure ⟨c, rfl⟩))

theorem mem_torusGroup_of_mem_normalCore
    {x : adjointGroup τ K}
    (hx : x ∈ ((borelGroup τ K).subgroupOf (adjointGroup τ K)).normalCore) :
    (x : ModGL τ K) ∈ torusGroup τ K := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
  obtain ⟨-, hmap, hinf, -⟩ := opposite_Borel_intersection τ K w₀ hw₀
  set n := canonicalRep (coxeterSystem τ) K w₀
  have hnC : n ∈ adjointGroup τ K := canonicalRep_mem_adjointGroup _ K w₀
  have h1 : (x : ModGL τ K) ∈ borelGroup τ K := by
    have := hx 1
    rw [one_mul, inv_one, mul_one] at this
    exact this
  have h2 : (x : ModGL τ K) ∈ torusGroup τ K ⊔ negUnipotent τ K := by
    have := hx ⟨n⁻¹, inv_mem hnC⟩
    rw [Subgroup.mem_subgroupOf] at this
    rw [← hmap]
    refine ⟨n⁻¹ * x * n, ?_, ?_⟩
    · simpa using this
    · simp [MulAut.conj_apply, mul_assoc]
  rw [← hinf]
  exact Subgroup.mem_inf.2 ⟨h1, h2⟩

theorem commute_of_mem_normalCore
    {x : adjointGroup τ K}
    (hx : x ∈ ((borelGroup τ K).subgroupOf (adjointGroup τ K)).normalCore)
    {S : Subgroup (ModGL τ K)} (hS : torusGroup τ K ⊓ S = ⊥)
    (hSn : torusGroup τ K ≤ Subgroup.normalizer (S : Set (ModGL τ K)))
    {g : adjointGroup τ K} (hg : (g : ModGL τ K) ∈ S) : g * x = x * g := by
  set Core := ((borelGroup τ K).subgroupOf (adjointGroup τ K)).normalCore
  have hk : x * g * x⁻¹ * g⁻¹ ∈ Core := by
    have h' : g * x⁻¹ * g⁻¹ ∈ Core := (Subgroup.normalCore_normal _).conj_mem _ (inv_mem hx) g
    have := mul_mem hx h'
    simpa [mul_assoc] using this
  have hH := mem_torusGroup_of_mem_normalCore hk
  have hxH := mem_torusGroup_of_mem_normalCore hx
  have hconj : (x : ModGL τ K) * g * (x : ModGL τ K)⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.1 (hSn hxH) g).1 hg
  have hkS : ((x * g * x⁻¹ * g⁻¹ : adjointGroup τ K) : ModGL τ K) ∈ S := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem hconj (inv_mem hg)
  have hk1 := Subgroup.mem_inf.2 ⟨hH, hkS⟩
  rw [hS, Subgroup.mem_bot] at hk1
  have hk1' : x * g * x⁻¹ * g⁻¹ = 1 := Subtype.ext hk1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hk1'
  exact hk1'.symm

theorem borel_core_center
    (τ : Tag) (K : Type) [Field K] :
    ((borelGroup τ K).subgroupOf (adjointGroup τ K)).normalCore =
      Subgroup.center (adjointGroup τ K) ∧
    (MulAction.toPermHom (adjointGroup τ K)
        (adjointGroup τ K ⧸ (borelGroup τ K).subgroupOf (adjointGroup τ K))).ker =
      Subgroup.center (adjointGroup τ K) := by
  have hcore : ((borelGroup τ K).subgroupOf (adjointGroup τ K)).normalCore =
      Subgroup.center (adjointGroup τ K) := by
    have hHB : torusGroup τ K ≤ borelGroup τ K := le_sup_left
    have hHU : torusGroup τ K ⊓ posUnipotent τ K = ⊥ :=
      (triangular_borel_structure.{0, 0} τ K).2.2.2.1
    have hHU' : torusGroup τ K ⊓ negUnipotent τ K = ⊥ := by
      obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
      refine eq_bot_iff.2 fun g hg => ?_
      have hB := (opposite_Borel_intersection τ K w₀ hw₀).2.2.2
      rw [← hB]
      exact Subgroup.mem_inf.2 ⟨hHB (Subgroup.mem_inf.1 hg).1, (Subgroup.mem_inf.1 hg).2⟩
    have hNU : torusGroup τ K ≤ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
      (triangular_borel_structure.{0, 0} τ K).2.2.1
    refine le_antisymm (fun x hx => ?_) ?_
    · refine Subgroup.mem_center_iff.2 fun g => ?_
      let Z : Subgroup (ModGL τ K) := Subgroup.centralizer {(x : ModGL τ K)}
      have hle : adjointGroup τ K ≤ Z := by
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨i, c, hgen | hgen⟩
        · have h := commute_of_mem_normalCore hx hHU hNU (g := ⟨xUnit τ K i c,
            xUnit_mem_adjointGroup i c⟩) (xUnit_mem_posUnipotent i c)
          rw [show _ = xUnit τ K i c from Units.ext hgen]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (congrArg Subtype.val h).symm
        · have h := commute_of_mem_normalCore hx hHU' torusGroup_le_normalizer_negUnipotent
            (g := ⟨yUnit τ K i c, yUnit_mem_adjointGroup i c⟩) (yUnit_mem_negUnipotent i c)
          rw [show _ = yUnit τ K i c from Units.ext hgen]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (congrArg Subtype.val h).symm
      have hg := hle g.2 (x : ModGL τ K) rfl
      exact Subtype.ext hg.symm
    · refine Subgroup.normal_le_normalCore.2 fun z hz => ?_
      rw [Subgroup.mem_subgroupOf]
      have hzN : (z : ModGL τ K) ∈
          adjointGroup τ K ⊓ Subgroup.normalizer (borelGroup τ K : Set (ModGL τ K)) := by
        refine Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_normalizer_iff.2 fun b => ?_⟩
        have hBC : borelGroup τ K ≤ adjointGroup τ K :=
          ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1
        constructor
        · intro hb
          have hc := Subgroup.mem_center_iff.1 hz ⟨b, hBC hb⟩
          have hc' : (z : ModGL τ K) * b = b * z := (congrArg Subtype.val hc).symm
          rw [hc', mul_inv_cancel_right]
          exact hb
        · intro hb
          have hb' : b ∈ adjointGroup τ K := by
            have := hBC hb
            have h2 := mul_mem (mul_mem (inv_mem z.2) this) z.2
            simpa [mul_assoc] using h2
          have hc := Subgroup.mem_center_iff.1 hz ⟨b, hb'⟩
          have hc' : (z : ModGL τ K) * b = b * z := (congrArg Subtype.val hc).symm
          rw [hc', mul_inv_cancel_right] at hb
          exact hb
      rw [(borel_self_normalizers τ K).2] at hzN
      exact hzN
  exact ⟨hcore, by rw [← Subgroup.normalCore_eq_ker, hcore]⟩

end CFSG.LieType.Chevalley
