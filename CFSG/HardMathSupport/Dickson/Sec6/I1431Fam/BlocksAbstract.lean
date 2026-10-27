module

public import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

section Quotient

variable {Q : Type*} [Group Q] [Finite Q]

theorem component_le_or_commute {K N : Subgroup Q} (hK : Open.IsComponentOf K ⊤) (hN : N.Normal) :
    K ≤ N ∨ ⁅K, N⁆ = ⊥ :=
  CFSG.LocalCores.component_normal_subgroup ((CFSG.isComponent_iff_open K).2 hK) hN

theorem not_le_centralizer_of_isQuasisimple {K : Subgroup Q} (hK : Open.IsQuasisimple K) :
    ¬ K ≤ Subgroup.centralizer (K : Set Q) := by
  intro h
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK
  apply hab
  have hz : ∀ z : K ⧸ Subgroup.center K, z = 1 := by
    intro z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (h z.2)) g g.2)
  rw [hz a, hz b]

theorem ne_bot_of_isComponentOf {K : Subgroup Q} (hK : Open.IsComponentOf K ⊤) : K ≠ ⊥ := by
  intro hbot
  have hs : Subsingleton K := by
    subst hbot
    infer_instance
  have hs2 : Subsingleton (K ⧸ Subgroup.center K) :=
    (QuotientGroup.mk'_surjective (Subgroup.center K)).subsingleton
  exact (not_nontrivial_iff_subsingleton.2 hs2) hK.2.2.2.toNontrivial

theorem component_eq_of_le_sup_normal {ι : Type*} (M : ι → Subgroup Q) (hMn : ∀ i, (M i).Normal)
    (hMq : ∀ i, M i = ⊥ ∨ Open.IsQuasisimple (M i)) {K : Subgroup Q}
    (hK : Open.IsComponentOf K ⊤) (hKM : K ≤ ⨆ i, M i) : ∃ i, K = M i := by
  by_contra hne
  push Not at hne
  have hcomm : ∀ i, M i ≤ Subgroup.centralizer (K : Set Q) := by
    intro i
    rcases component_le_or_commute hK (hMn i) with h | h
    · exfalso
      rcases hMq i with hbot | hq
      · exact ne_bot_of_isComponentOf hK (le_bot_iff.1 (hbot ▸ h))
      · have h1 : CFSG.Assembly.IsComponentOf K ⊤ := CFSG.Assembly.isComponentOf_iff_open.2 hK
        have h2 := CFSG.Assembly.IsComponentOf.of_le_of_le h1 h le_top
        have h3 : Open.IsComponentOf K (M i) := CFSG.Assembly.isComponentOf_iff_open.1 h2
        exact hne i
          (CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple h3 hq)
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact h))
  have hKc : K ≤ Subgroup.centralizer (K : Set Q) := hKM.trans (iSup_le hcomm)
  exact not_le_centralizer_of_isQuasisimple hK.2.2 hKc

end Quotient

theorem subgroupOf_iSup_eq {G : Type*} [Group G] {X : Subgroup G} {ι : Type*}
    (N : ι → Subgroup G) (hNX : ∀ i, N i ≤ X) :
    (⨆ i, N i).subgroupOf X = ⨆ i, (N i).subgroupOf X := by
  have hinj : Function.Injective X.subtype := X.subtype_injective
  apply Subgroup.map_injective hinj
  rw [Subgroup.map_iSup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (iSup_le hNX)]
  exact (iSup_congr fun i => by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hNX i)]).symm


section Blocks

variable {G : Type} [Group G] [Finite G]

theorem exists_barX_eq_of_blocks {X J : Subgroup G} (hJ : GLAPComponent 3 X J) {ι : Type*}
    (N : ι → Subgroup G) (hNX : ∀ i, N i ≤ X)
    (hNn : ∀ i, ∀ c ∈ X, ∀ n ∈ N i, c * n * c⁻¹ ∈ N i)
    (hNq : ∀ i, CFSG.IsQuasisimple (N i))
    (hk : ∃ k : ℕ, ∀ x ∈ derivedSeries ↥X k, (x : G) ∈ ⨆ i, N i) :
    ∃ i, barX 3 X J = barX 3 X (N i) := by
  classical
  set O : Subgroup ↥X := GLAPPrimeCore 3 ↥X with hO
  set π : ↥X →* ↥X ⧸ O := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hLcomp : Open.IsComponentOf (barX 3 X J) ⊤ := hJ.2.2.1
  have hMn : ∀ i, (barX 3 X (N i)).Normal := by
    intro i
    have h1 : ((N i).subgroupOf X).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (hNX i)]
      exact fun x c hx hc => hNn i c hc x hx
    exact h1.map π hπs
  have hMq : ∀ i, barX 3 X (N i) = ⊥ ∨ Open.IsQuasisimple (barX 3 X (N i)) := by
    intro i
    by_cases hle : (N i).subgroupOf X ≤ π.ker
    · left
      exact (Subgroup.map_eq_bot_iff _).2 hle
    · right
      have hq : CFSG.IsQuasisimple ((N i).subgroupOf X) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hNX i)).symm
          (hNq i)
      obtain ⟨hp, hs, -⟩ := CFSG.LocalCores.isQuasisimple_map hq π hle
      exact ⟨hp.commutator_eq_top, hs⟩
  have hperf : ⁅barX 3 X J, barX 3 X J⁆ = barX 3 X J :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hLcomp.2.2.1)
  have hder : ∀ m : ℕ, barX 3 X J ≤ derivedSeries (↥X ⧸ O) m := by
    intro m
    induction m with
    | zero => exact le_top
    | succ m ih =>
      rw [derivedSeries_succ]
      calc barX 3 X J = ⁅barX 3 X J, barX 3 X J⁆ := hperf.symm
        _ ≤ _ := Subgroup.commutator_mono ih ih
  obtain ⟨k, hk⟩ := hk
  have hk' : derivedSeries ↥X k ≤ ⨆ i, (N i).subgroupOf X := by
    rw [← subgroupOf_iSup_eq N hNX]
    exact fun x hx => hk x hx
  have hLM : barX 3 X J ≤ ⨆ i, barX 3 X (N i) := by
    refine (hder k).trans ?_
    rw [← map_derivedSeries_eq hπs k]
    refine (Subgroup.map_mono hk').trans ?_
    rw [Subgroup.map_iSup]
    exact le_rfl
  exact component_eq_of_le_sup_normal (fun i => barX 3 X (N i)) hMn hMq hLcomp hLM

theorem exists_inner_of_blocks {X J : Subgroup G} (hJ : GLAPComponent 3 X J) {ι : Type*}
    (N : ι → Subgroup G) (hNX : ∀ i, N i ≤ X)
    (hNn : ∀ i, ∀ c ∈ X, ∀ n ∈ N i, c * n * c⁻¹ ∈ N i)
    (hNq : ∀ i, CFSG.IsQuasisimple (N i))
    (hk : ∃ k : ℕ, ∀ x ∈ derivedSeries ↥X k, (x : G) ∈ ⨆ i, N i)
    {b : G} (hbX : b ∈ X)
    (hb : ∀ i, barX 3 X (N i) = barX 3 X J →
      ∃ n ∈ N i, ∃ c ∈ X, (∀ m ∈ N i, c * m = m * c) ∧ b = n * c) :
    ∃ j₀ ∈ J, ∀ j ∈ J, ∀ (h1 : b * j * b⁻¹ ∈ X) (h2 : j₀ * j * j₀⁻¹ ∈ X),
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨b * j * b⁻¹, h1⟩ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨j₀ * j * j₀⁻¹, h2⟩ := by
  classical
  obtain ⟨i, hi⟩ := exists_barX_eq_of_blocks hJ N hNX hNn hNq hk
  obtain ⟨n, hn, c, hcX, hcN, hbnc⟩ := hb i hi.symm
  set π : ↥X →* ↥X ⧸ GLAPPrimeCore 3 ↥X := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hπ
  have hnbar : π ⟨n, hNX i hn⟩ ∈ barX 3 X J := by
    rw [hi]
    exact ⟨⟨n, hNX i hn⟩, Subgroup.mem_subgroupOf.2 hn, rfl⟩
  obtain ⟨j₀', hj₀', hj₀π⟩ := hnbar
  refine ⟨(j₀' : G), Subgroup.mem_subgroupOf.1 hj₀', fun j hj h1 h2 => ?_⟩
  set c' : ↥X := ⟨c, hcX⟩ with hc'
  set n' : ↥X := ⟨n, hNX i hn⟩ with hn'
  set j' : ↥X := ⟨j, hJ.1 hj⟩ with hj'
  have hb' : (⟨b, hbX⟩ : ↥X) = n' * c' := Subtype.ext hbnc
  have hjbar : π j' ∈ barX 3 X (N i) := by
    rw [← hi]
    exact ⟨j', Subgroup.mem_subgroupOf.2 hj, rfl⟩
  obtain ⟨m', hm', hmπ⟩ := hjbar
  have hcm : c' * m' = m' * c' := Subtype.ext (hcN m' (Subgroup.mem_subgroupOf.1 hm'))
  have hcomm : π c' * π j' = π j' * π c' := by
    rw [← hmπ, ← map_mul, ← map_mul, hcm]
  have e1 : (⟨b * j * b⁻¹, h1⟩ : ↥X) = (⟨b, hbX⟩ : ↥X) * j' * (⟨b, hbX⟩ : ↥X)⁻¹ := rfl
  have e2 : (⟨(j₀' : G) * j * (j₀' : G)⁻¹, h2⟩ : ↥X) = j₀' * j' * j₀'⁻¹ := rfl
  have hj₀π' : π j₀' = π n' := hj₀π
  have h3 : π c' * π j' * (π c')⁻¹ = π j' := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [e1, e2, hb']
  simp only [map_mul, map_inv, hj₀π', mul_inv_rev]
  rw [show π n' * π c' * π j' * ((π c')⁻¹ * (π n')⁻¹) =
      π n' * (π c' * π j' * (π c')⁻¹) * (π n')⁻¹ by group, h3]

end Blocks

end CFSG.HardMathSupport.Dickson.Sec6.I1431
