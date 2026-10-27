module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLOut
public import CFSG.ClassicalInvolution.Q3.TL3T25

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
  CFSG.ClassicalInvolution.Q3.TC.Thin

section Trans

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)}

theorem exists_third_member' (hΦ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 ↥J) {K K' : Subgroup G}
    (hK : K ∈ Φ) (hK'tw : K' ∈ twinSet Φ K) (hne : K' ≠ K) {a : G} (ha : ¬ IsPGroup 2 ↥(Ea Φ a)) :
    ∃ J ∈ Φ, J ≠ K ∧ J ≠ K' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hK'Φ, z, hzK, hzK'⟩ := hK'tw
  have hcomm := OddQuot.commutes_of_twin_pgroup hΦ h2 hK hK'Φ hne.symm hzK hzK'
  have hKK' : IsPGroup 2 ↥(K ⊔ K') := by
    have hnorm : K ≤ Subgroup.normalizer (K' : Set G) := fun x hx =>
      mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hx hcomm)
    exact (h2 K hK).to_sup_of_normal_right' (h2 K' hK'Φ) hnorm
  have hEa : IsPGroup 2 ↥(Ea Φ a) := by
    refine hKK'.to_le (Ea_le (fun L hL _ => ?_))
    by_cases hLK : L = K
    · exact hLK ▸ le_sup_left
    · exact (hcon L hL hLK) ▸ le_sup_right
  exact ha hEa

theorem trans_of_twin' {n : ℕ} (h4 : Thm4RTwinBelow 3 n) (hlt : Nat.card G < n)
    (hΦ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 ↥J)
    (hq : ∀ J ∈ Φ, Nonempty (↥J ≃* QuaternionGroup 2)) (hA : ∀ J ∈ Φ, AEmpty Φ J)
    (hO : classicalInvolutionOddCore G = ⊥) {K K' : Subgroup G} (hK : K ∈ Φ)
    (hK'tw : K' ∈ twinSet Φ K) (hne : K' ≠ K)
    (hperp : ∀ J ∈ Φ, J ≠ K → J ≤ Subgroup.normalizer (K : Set G) → J = K')
    (hperp' : ∀ J ∈ Φ, J ≠ K' → J ≤ Subgroup.normalizer (K' : Set G) → J = K) {a : G}
    (ha : ¬ IsPGroup 2 ↥(Ea Φ a)) : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : G, conjSub g L = L' := by
  have hK'Φ : K' ∈ Φ := hK'tw.1
  have hq' : ∀ J ∈ Φ, ∀ P : Subgroup G, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (3 - 2))) := by
    intro J hJ P hP
    have hJP : J = P := hP.2.2 J le_rfl (h2 J hJ) hP.1
    subst hJP
    exact hq J hJ
  have h4' := h4 G hlt Φ hΦ (fun J hJ => IsPGroup.of_surjective (h2 J hJ)
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥J)) (QuotientGroup.mk'_surjective _)) hq' hA hO
  have hnorm : ∀ J K₀ : Subgroup G, Commutes K₀ J → J ≤ Subgroup.normalizer (K₀ : Set G) :=
    fun J K₀ hc y hy => mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hy hc.symm)
  have hA_ : ∀ L ∈ Φ, L ≠ K → (¬ ∃ g : G, conjSub g K = L) → L = K' := fun L hL hLK hno =>
    hperp L hL hLK (hnorm L K (h4' K hK L hL hno))
  have hA' : ∀ L ∈ Φ, L ≠ K' → (¬ ∃ g : G, conjSub g K' = L) → L = K := fun L hL hLK hno =>
    hperp' L hL hLK (hnorm L K' (h4' K' hK'Φ L hL hno))
  obtain ⟨J₁, hJ₁, hJ₁K, hJ₁K'⟩ := exists_third_member' hΦ h2 hK hK'tw hne ha
  have hJ₁orb : ∃ g : G, conjSub g K = J₁ := by
    by_contra hno
    exact hJ₁K' (hA_ J₁ hJ₁ hJ₁K hno)
  have hJ₁orb' : ∃ g : G, conjSub g K' = J₁ := by
    by_contra hno
    exact hJ₁K (hA' J₁ hJ₁ hJ₁K' hno)
  obtain ⟨g₁, hg₁⟩ := hJ₁orb
  obtain ⟨g₂, hg₂⟩ := hJ₁orb'
  have hK'orb : ∃ g : G, conjSub g K = K' :=
    ⟨g₂⁻¹ * g₁, by rw [conjSub_mul, hg₁, ← hg₂, conjSub_inv_conjSub]⟩
  have horb : ∀ L ∈ Φ, ∃ g : G, conjSub g K = L := by
    intro L hL
    by_cases hLK : L = K
    · exact ⟨1, by rw [conjSub_one, hLK]⟩
    · by_contra hno
      have := hA_ L hL hLK hno
      subst this
      exact hno hK'orb
  intro L hL L' hL'
  obtain ⟨g, rfl⟩ := horb L hL
  obtain ⟨g', rfl⟩ := horb L' hL'
  exact ⟨g' * g⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩

theorem not_isPGroup_of_not_isSolvable {H : Type} [Group H] [Finite H]
    (h : ¬ Group.IsSolvable H) : ¬ IsPGroup 2 H := fun h2 => h (by
  haveI := h2.isNilpotent
  infer_instance)

end Trans

section Ident

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)}

theorem eq_seven_of_aeIdent (F : TwinDisc.ExitO2.Q8Fam G Φ) {m : ℕ} (hm : 5 ≤ m) (I : AEIdent Φ m)
    {K K' : Subgroup G} (hK : K ∈ Φ) (hK' : K' ∈ Φ) (hne : K' ≠ K)
    (hperp : ∀ J ∈ Φ, J ≠ K → J ≤ Subgroup.normalizer (K : Set G) → J = K') {a : G}
    (ha2 : a * a = 1) (hanc : a ∉ Subgroup.center G) (haE : a ∈ Ea Φ a)
    (hns : ¬ Group.IsSolvable ↥(Ea Φ a))
    (mf5 : ModelNoLayer 5 Set.univ ((AE.aeSub 5).map (AE.mkQ 5)))
    (mf6 : ModelNoLayer 6 Set.univ ((AE.aeSub 6).map (AE.mkQ 6))) : Nonempty (AEIdent Φ 7) := by
  have hlabel : ∀ L ∈ Φ, ∃ α ∈ (Set.univ : Set (Finset (Fin m))), ∃ (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Φ)).map I.φ = AE.memBar α h b := fun L hL => by
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    exact ⟨α, Set.mem_univ _, h, b, hlab⟩
  have hsurj : ∀ α ∈ (Set.univ : Set (Finset (Fin m))), ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Φ,
      (L.subgroupOf (pSpan Φ)).map I.φ = AE.memBar α h b := fun α _ h b => I.label_surj α h b
  have hrange : (I.φ.comp (toPSpan F.gen)) a ∈ (AE.aeSub m).map (AE.mkQ m) := by
    rw [← I.range_eq]
    exact ⟨_, rfl⟩
  by_cases hm8 : 8 ≤ m
  · exfalso
    refine false_of_far F hm I.φ I.ker_le hlabel hsurj ?_ hK hne hperp hK'
    intro α _ hα
    have hc : 4 ≤ (αᶜ).card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨β, hβ, hβ4⟩ := Finset.exists_subset_card_eq hc
    exact ⟨β, Set.mem_univ _, hβ4, Finset.disjoint_of_subset_right hβ disjoint_compl_right⟩
  · have hML := modelLayer_of_layer F hm I.φ I.ker_le hlabel hsurj ha2 hanc haE hns
    have hm' : m = 5 ∨ m = 6 ∨ m = 7 := by omega
    rcases hm' with rfl | rfl | rfl
    · exact (mf5 _ hrange hML).elim
    · exact (mf6 _ hrange hML).elim
    · exact ⟨I⟩

theorem aeIdent7_of_concl (F : TwinDisc.ExitO2.Q8Fam G Φ) (hconcl : ThmDConcl Φ)
    {K K' : Subgroup G} (hK : K ∈ Φ) (hK'tw : K' ∈ twinSet Φ K) (hne : K' ≠ K)
    (hperp : ∀ J ∈ Φ, J ≠ K → J ≤ Subgroup.normalizer (K : Set G) → J = K') {a : G}
    (ha2 : a * a = 1) (hanc : a ∉ Subgroup.center G) (haE : a ∈ Ea Φ a)
    (hns : ¬ Group.IsSolvable ↥(Ea Φ a)) (hW : ¬ ∃ W : Subgroup G, WSet Φ = {W})
    (mf5 : ModelNoLayer 5 Set.univ ((AE.aeSub 5).map (AE.mkQ 5)))
    (mf6 : ModelNoLayer 6 Set.univ ((AE.aeSub 6).map (AE.mkQ 6)))
    (mf64 : ModelNoLayer 7 AE.e64Sets AE.e64Sub) : Nonempty (AEIdent Φ 7) := by
  obtain ⟨hK'Φ, z, hzK, hzK'⟩ := hK'tw
  rcases hconcl with h1 | h2 | ⟨E, hE⟩ | h4 | ⟨m, hm, hI⟩ | hI29
  · exact absurd (h1 K' hK'Φ K hK) hne
  · exact absurd h2 hW
  · exact absurd (TC.Thin.eq_of_inv_e8 (Q8Fam.thmDHyp F) hE hK hK'Φ hzK hzK').symm hne
  · obtain ⟨I⟩ := h4
    exfalso
    have hML := modelLayer_of_layer F (by norm_num : 5 ≤ 7) I.φ I.ker_le I.label I.label_surj ha2
      hanc haE hns
    have hrange : (I.φ.comp (toPSpan F.gen)) a ∈ AE.e64Sub := by
      have h1 : (I.φ.comp (toPSpan F.gen)) a ∈ I.φ.range := ⟨_, rfl⟩
      rwa [I.range_eq] at h1
    exact mf64 _ hrange hML
  · obtain ⟨I⟩ := hI
    exact eq_seven_of_aeIdent F hm I hK hK'Φ hne hperp ha2 hanc haE hns mf5 mf6
  · obtain ⟨I⟩ := hI29
    exact (false_of_e29 F I hK hK'Φ hne hperp).elim

end Ident

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
