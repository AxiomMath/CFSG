module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinFinalA3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinFinalMain

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule
  CFSG.EvenSmallLie
open CFSG.LieType.Universal.Spin (quadPlus)
open CFSG.LieType.Steinberg.TwistedE6 (sigma)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

local instance f4PilotGraphSpinFinalAgreeNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Inputs

@[expose] def E6RowSp4ModelInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] [CharP K CFSG.LieType.Ree.ReeTag.F4.prime]
    (f : ℕ) (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f),
    (∃ ε : K ≃+* K, ∀ (x : e6Data_valid.minGroup K) (sA sD : StatedSp 3 K),
      x ∈ e6ScLevi K e6A3Nodes → sigma K (RingHom.id K) x = x →
      graphParamHom K (RingEquiv.refl K) (sp6ToSL6 sA) = x → spinToE6Sc K (spinIota hK hf sD) = x →
      ((c3LeviEquiv K sA : C3Levi K) : adjointGroup .F4 K) =
        graphAutF4 K (c3LeviEquiv K (statedSpCongr ε 3 sD) : C3Levi K)) ∧
    (∃ ε : K ≃+* K, ∀ (x : e6Data_valid.minGroup K) (sA sD : StatedSp 3 K),
      x ∈ e6ScLevi K e6A3Nodes → sigma K (RingHom.id K) x = x →
      graphParamHom K (RingEquiv.refl K) (sp6ToSL6 sA) = x → spinToE6Sc K (spinIota hK hf sD) = x →
      graphAutF4 K (c3LeviEquiv K sA : C3Levi K) =
        ((c3LeviEquiv K (statedSpCongr ε 3 sD) : C3Levi K) : adjointGroup .F4 K))

@[expose] def E6RowA3RigidityInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ θ : MulAut (e6ScLevi K e6A3Nodes),
      (∀ x : e6ScLevi K e6A3Nodes,
        sigma K (RingHom.id K) (x : e6Data_valid.minGroup K) = x → θ x = x) →
      (∀ x y : e6ScLevi K e6A3Nodes,
        (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x →
          (θ y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) (θ x)) →
      (∀ x, θ x = x) ∨
        (∀ x y : e6ScLevi K e6A3Nodes,
          (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → θ x = y)

end Inputs

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_sp6_of_sigma_fixed_A5 {x : e6Data_valid.minGroup K} (hx : x ∈ e6ScLevi K e6A5Nodes)
    (hσ : sigma K (RingHom.id K) x = x) :
    ∃ s : StatedSp 3 K, graphParamHom K (RingEquiv.refl K) (sp6ToSL6 s) = x := by
  rw [← range_graphParamHom (RingEquiv.refl K)] at hx
  obtain ⟨g, rfl⟩ := hx
  have hβ : (slConjugation 6 K (graphGram6 K) * slGraphAut 6 K) g = g := by
    apply graphParamHom_injective (RingEquiv.refl K)
    rw [← sigma_graphParamHom, hσ]
  have hg : g ∈ fixedSubgroup (slConjugation 6 K (graphGram6 K) * slGraphAut 6 K) := hβ
  rw [fixedSubgroup_graphGram6] at hg
  obtain ⟨s, rfl⟩ := hg
  exact ⟨s, rfl⟩

variable {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)

theorem exists_sp6_of_sigma_fixed_D4 {x : e6Data_valid.minGroup K}
    (hx : x ∈ e6ScLevi K e6D4Nodes) (hσ : sigma K (RingHom.id K) x = x) :
    ∃ s : StatedSp 3 K, spinToE6Sc K (spinIota hK hf s) = x := by
  set y := (spinEquivD4 K).symm ⟨x, hx⟩ with hy
  have hxy : spinToE6Sc K y = x := by
    rw [← coe_spinEquivD4, hy, MulEquiv.apply_symm_apply]
  have hγ : spinD4Graph K y = y := by
    apply (spinEquivD4 K).injective
    rw [spinEquivD4_spinD4Graph]
    apply Subtype.ext
    rw [hy, MulEquiv.apply_symm_apply]
    exact hσ
  obtain ⟨s, hs⟩ := (mem_range_spinIota_iff hK hf y).2 hγ
  exact ⟨s, by rw [hs, hxy]⟩

end Fixed

section Twist

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit
  [Finite K] [CharP K 2] in
theorem sigma_mem_e6ScLevi_A3 {x : e6Data_valid.minGroup K} (hx : x ∈ e6ScLevi K e6A3Nodes) :
    sigma K (RingHom.id K) x ∈ e6ScLevi K e6A3Nodes :=
  sigma_mem_e6ScLevi (by decide) hx

theorem agree_of_sp4Agree (hR : E6RowA3RigidityInput) {t : G} {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {e : L ≃* adjointGroup .F4 K} {N₁ N₂ : AmalgamNeighbour}
    {e₁ e₂ : L ≃* adjointGroup .F4 K} (he₁ : IsNeighbourFrame e e₁ N₁)
    (he₂ : IsNeighbourFrame e e₂ N₂) {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hrA : ΦA.range = neighbourCore e N₁) (hkA : ΦA.ker ≤ center (e6ScLevi K e6A5Nodes))
    (hcA : ∀ x y : e6ScLevi K e6A5Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y)
    (hnA : IsLeviNormalizedA e₁ ΦA) {ε : K ≃+* K} {ΦY : spinGroup (quadPlus 4 K) →* G}
    (hrY : ΦY.range = neighbourCore e N₂) (hiY : Function.Injective ΦY)
    (hc : ∀ g, t * ΦY g * t⁻¹ = ΦY (spinD4Graph K g))
    (hn : ∀ s, ΦY (spinIota hK hf s) = levi6Hom e₂ ε s)
    (hP : ∀ (x : e6Data_valid.minGroup K) (sA sD : StatedSp 3 K),
      x ∈ e6ScLevi K e6A3Nodes → sigma K (RingHom.id K) x = x →
      graphParamHom K (RingEquiv.refl K) (sp6ToSL6 sA) = x → spinToE6Sc K (spinIota hK hf sD) = x →
      levi6Hom e₁ (RingEquiv.refl K) sA = levi6Hom e₂ ε sD) :
    (∀ x : e6ScLevi K e6A3Nodes, scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
        scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) e6A3Nodes_subset_e6D4Nodes x) ∨
      (∀ x y : e6ScLevi K e6A3Nodes,
        (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x →
          scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes x =
            scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom)
              e6A3Nodes_subset_e6D4Nodes y) := by
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set a := scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes with ha
  set d := scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) e6A3Nodes_subset_e6D4Nodes
    with hd
  have hrange : d.range = a.range :=
    range_scLeviRestrict_A3_D_eq_A hK hf he₁ he₂ hrA hkA hnA hrY hiY hn
  have hai : Function.Injective a := scLeviRestrict_A3_injective hkA
  have hdi : Function.Injective d := by
    have h1 : Function.Injective (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) := by
      rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
      exact hiY.comp (spinEquivD4 K).symm.injective
    exact scLeviRestrict_injective_of_injective h1 _
  set θ : MulAut (e6ScLevi K e6A3Nodes) := ((MonoidHom.ofInjective hai).trans
    (MulEquiv.subgroupCongr hrange.symm)).trans (MonoidHom.ofInjective hdi).symm with hθ
  have hdθ : ∀ x, d (θ x) = a x := by
    intro x
    have h1 := (MonoidHom.ofInjective hdi).apply_symm_apply
      (MulEquiv.subgroupCongr hrange.symm (MonoidHom.ofInjective hai x))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hta : ∀ x y : e6ScLevi K e6A3Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * a x * t⁻¹ = a y := by
    intro x y hxy
    rw [ha, scLeviRestrict_apply, scLeviRestrict_apply]
    exact hcA _ _ hxy
  have htd : ∀ x y : e6ScLevi K e6A3Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * d x * t⁻¹ = d y := by
    intro x y hxy
    rw [hd, scLeviRestrict_apply, scLeviRestrict_apply, MonoidHom.comp_apply,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hc]
    congr 1
    apply (spinEquivD4 K).injective
    rw [spinEquivD4_spinD4Graph, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    exact hxy.symm
  have hfix : ∀ x : e6ScLevi K e6A3Nodes,
      sigma K (RingHom.id K) (x : e6Data_valid.minGroup K) = x → θ x = x := by
    intro x hσ
    have hx5 := CFSG.LieType.CurtisTits.levi_mono _ e6A3Nodes_subset_e6A5Nodes x.2
    have hx4 := CFSG.LieType.CurtisTits.levi_mono _ e6A3Nodes_subset_e6D4Nodes x.2
    obtain ⟨sA, hsA⟩ := exists_sp6_of_sigma_fixed_A5 hx5 hσ
    obtain ⟨sD, hsD⟩ := exists_sp6_of_sigma_fixed_D4 hK hf hx4 hσ
    apply hdi
    rw [hdθ]
    have hA : a x = levi6Hom e₁ (RingEquiv.refl K) sA := by
      rw [ha, scLeviRestrict_apply, ← hnA sA]
      congr 1
      exact Subtype.ext hsA.symm
    have hD : d x = levi6Hom e₂ ε sD := by
      rw [hd, scLeviRestrict_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hn sD]
      congr 1
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext hsD.symm
    rw [hA, hD]
    exact hP _ sA sD x.2 hσ hsA hsD
  have hcomm : ∀ x y : e6ScLevi K e6A3Nodes,
      (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x →
        (θ y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) (θ x) := by
    intro x y hxy
    set w : e6ScLevi K e6A3Nodes := ⟨sigma K (RingHom.id K) (θ x), sigma_mem_e6ScLevi_A3 (θ x).2⟩
      with hw
    have hdw : d w = d (θ y) := by
      rw [← htd (θ x) w rfl, hdθ, hdθ, hta x y hxy]
    rw [← hdi hdw]
  rcases hR K hq θ hfix hcomm with h1 | h2
  · refine .inl fun x => ?_
    rw [← hdθ, h1]
  · refine .inr fun x y hxy => ?_
    rw [← hdθ, h2 x y hxy]

end Twist

section Reduction

theorem statedSpCongr_refl_apply {K : Type} [Field K] {n : ℕ} (s : StatedSp n K) :
    statedSpCongr (RingEquiv.refl K) n s = s := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_statedSpCongr, coe_statedSpMap]
  ext i j
  rfl

theorem e6GraphRowSpinAgreeInput_of_inputs (hM : E6RowSp4ModelInput)
    (hR : E6RowA3RigidityInput) : E6GraphRowSpinAgreeInput := by
  intro G _ _ L K _ _ _ e t f hw hf N₁ N₂ hN h6 h8 e₁ he₁ e₂ he₂ ΦA hrA hkA hcA hnA
  have hc2 : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨⟨εX, hX⟩, ⟨εY, hY⟩⟩ := hM K f hw.card_eq hf
  have key : ∃ ε : K ≃+* K, ∀ (x : e6Data_valid.minGroup K) (sA sD : StatedSp 3 K),
      x ∈ e6ScLevi K e6A3Nodes → sigma K (RingHom.id K) x = x →
      graphParamHom K (RingEquiv.refl K) (sp6ToSL6 sA) = x →
      spinToE6Sc K (spinIota hw.card_eq hf sD) = x →
      levi6Hom e₁ (RingEquiv.refl K) sA = levi6Hom e₂ ε sD := by
    rcases hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h1 : e₁ = e := he₁
      obtain ⟨hc', rfl⟩ := he₂
      subst h1
      refine ⟨εX, fun x sA sD hx hσ hA hD => ?_⟩
      simp only [levi6Hom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
        MulEquiv.symm_trans_apply, MulEquiv.symm_symm, statedSpCongr_refl_apply]
      rw [hX x sA sD hx hσ hA hD]
    · obtain ⟨hc', rfl⟩ := he₁
      have h2 : e₂ = e := he₂
      subst h2
      refine ⟨εY, fun x sA sD hx hσ hA hD => ?_⟩
      simp only [levi6Hom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
        MulEquiv.symm_trans_apply, MulEquiv.symm_symm, statedSpCongr_refl_apply]
      rw [hY x sA sD hx hσ hA hD]
  obtain ⟨ε, hε⟩ := key
  exact ⟨ε, fun ΦY hrY hiY hc hn =>
    agree_of_sp4Agree hR hw.card_eq hf he₁ he₂ hrA hkA hcA hnA hrY hiY hc hn hε⟩

end Reduction

section Corollaries

theorem e6GraphRowSpinNormInput_of_models (hM : E6RowSp4ModelInput)
    (hR : E6RowA3RigidityInput) : E6GraphRowSpinNormInput :=
  e6GraphRowSpinNormInput_of_agree (e6GraphRowSpinAgreeInput_of_inputs hM hR)

end Corollaries

end CFSG.SeitzReduction.F4Pilot
