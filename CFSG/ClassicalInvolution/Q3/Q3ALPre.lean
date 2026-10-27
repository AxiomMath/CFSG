module

public import CFSG.ClassicalInvolution.Q3.Q3ALCent
public import CFSG.ClassicalInvolution.Q3.Q3AEdges
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AL

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD

@[expose] def OddThreeFreePre3 (P : ∀ {G : Type} [Group G], Subgroup G → G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K → P K z →
      ExactMembers3 (conjClass3 K) → Q3W.LocalOddThreeFree3 (conjClass3 K) z

theorem OddThreeFreePre3.mono {P Q : ∀ {G : Type} [Group G], Subgroup G → G → Prop}
    (hQP : ∀ (G : Type) [Group G] (K : Subgroup G) (z : G), Q K z → P K z)
    (h : OddThreeFreePre3 P) : OddThreeFreePre3 Q := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hQ hex
  exact h G hnab K z hz hBelow h3 h4 hΔ (hQP G K z hQ) hex


section Exact

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem exactMembers3_of_alphaEdges (hE : AlphaEdges3) (hnab : ∃ a b : G, a * b ≠ b * a)
    {K : Subgroup G} {z : G} (hz : IsClassicalMember3 K z) (hBelow : CIT3Below (Nat.card G))
    (h3 : 3 ≤ twoRank G) (h4 : ¬ TwoSubgroupsFourGenerated G) (hΔ : DeltaConnected K)
    (hB : ¬ BootData3 (conjClass3 K)) : ExactMembers3 (conjClass3 K) := by
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hBelow
  obtain ⟨K₁, K₂, z₁, z₂, he⟩ := exists_edge3 hnab hz hΔ
  have hα₁ : alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥ :=
    hE G hnab K z hz hBelow h3 h4 hΔ hB K₁ K₂ z₁ z₂ he
  have hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G := fun b hb1 hbc =>
    not_subset_center_of_ne_one hnab hb1 (Set.singleton_subset_iff.mpr hbc)
  have hex1 : classicalInvolutionOddCore ↥K₁ = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_deltaCore_eq_bot₃ hΩ.conjInvariant hIH he.mem₁ he.cls₁
      he.le_centralizer_pair (fun f _ hf1 => hnc f hf1)
      (le_bot_iff.mp (by simpa [hα₁] using (deltaCore_le_alphaCore
        (F := Subgroup.closure ({z₁, z₂} : Set G)))))
  obtain ⟨b, hb⟩ := he.mem₁
  refine exactMembers3_of_conjugates hex1 fun L hL => ?_
  obtain ⟨a, rfl⟩ := hL
  refine ⟨a * b⁻¹, ?_⟩
  show conjSub a K = conjSub (a * b⁻¹) K₁
  rw [← hb, ← conjSub_mul]
  simp

end Exact

theorem locCommute3_of_oddThreeFreePre3 (hE : AlphaEdges3)
    (h : OddThreeFreePre3 fun K _ => ¬ BootData3 (conjClass3 K)) : LocCommute3 := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB L M l m hL hM hl hm hne _ hMl
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hBelow
  have hex : ExactMembers3 (conjClass3 K) :=
    exactMembers3_of_alphaEdges hE hnab hz hBelow h3 h4 hΔ hB
  obtain ⟨a, -, haz⟩ := conjClass3_involution hz hL hl
  have h3z : Q3W.LocalOddThreeFree3 (conjClass3 K) z := h G hnab K z hz hBelow h3 h4 hΔ hB hex
  have h3l : Q3W.LocalOddThreeFree3 (conjClass3 K) l := by
    rw [haz]
    exact Q3W.localOddThreeFree3_conj hΩ.conjInvariant a z h3z
  exact commutes_of_exact_threeFree (RouteD.Gaps.fundNoncentral 3) hnab hIH hL hM hl hm hne hMl
    (hex L hL) h3l

theorem cit3LargeWeak_of_edges_pre (hd : SmallDisconnected3) (hb3 : BootTriple3)
    (hb : BootNoTriple3) (hE : AlphaEdges3)
    (h : OddThreeFreePre3 fun K _ => ¬ BootData3 (conjClass3 K)) (hrec : SetupRecognition3) :
    CIT3LargeWeak :=
  cit3LargeWeak_of_edges hd hb3 hb (locCommute3_of_oddThreeFreePre3 hE h) hE hrec

end CFSG.ClassicalInvolution.Q3.Q3AL
