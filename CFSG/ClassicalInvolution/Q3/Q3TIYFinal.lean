module

public import CFSG.ClassicalInvolution.Q3.Q3TIYNC
public import CFSG.ClassicalInvolution.Q3.Q3TIYRank2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TIV
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt TwinElt.u IsTwinAt TwinRow TwinDatumOn
  TwinMFCommutantOn twinYModel)


theorem twinYType3On_of_inputs {P : StatedLieTag → ℕ → Prop} (h3 : OddThreeFreeInput)
    (hNC : TwinYNoCentral3On P) (hKind : TwinYKind3On P) (hRank : TwinYRank3On P) :
    Q3TY.TwinYType3On P := by
  intro G _ _ _ hnab K z hR t n hrow hP hshape T hT clsT e hP1u hO3u
  classical
  have hex : ExactMembers3 (conjClass3 K) := hR.setup.1
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hnc : ¬ ({e.u} : Set G) ⊆ Subgroup.center G := by
    intro h
    have h1 : e.u ∈ Subgroup.center G := h (Set.mem_singleton _)
    rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at h1
    have h2 := Q3TY.twinElt_orderOf_u3 e hR.cls (hex K hKΩ) hKT'
    rw [h1, orderOf_one] at h2
    omega
  obtain ⟨ι, hι, ⟨D⟩⟩ := hR.ih {e.u} hnc
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨hKΩ, isSubnormal_le hR.cls.subnormal⟩
  have hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  obtain ⟨hft, hG2, hD4, hE6, -⟩ := twinRow_tag_facts3 hrow
  have hCF := ModelFacts.commutingFundamentalGeneration3_nonTwisted hG2 hD4 hE6 hft
    (twinRow_admissible3 hrow)
  obtain ⟨i₀, hi₀, -⟩ := c.oneComponent hCF e hKz hT.mem hT.ne.symm hKiso hTiso hP1u hO3u
    (hNC h3 G hnab K z hR t n hrow hP hshape T hT clsT e) D
  have hcard : Nat.card ι = 1 := Nat.card_eq_one_iff_exists.mpr ⟨i₀, hi₀⟩
  obtain ⟨t', n', hk, hrow'⟩ :=
    hKind h3 G hnab K z hR t n hrow hP hshape T hT clsT e hP1u hO3u ι D hcard i₀
  obtain ⟨ht', hn'⟩ :=
    hRank h3 G hnab K z hR t n hrow hP hshape T hT clsT e hP1u hO3u ι D hcard i₀ t' n' hk hrow'
  refine ⟨ι, hι, D, by rw [hcard], i₀, ?_, fun i hi => absurd (hi₀ i) hi⟩
  rw [hk, ht', hn']

theorem twinCentralizingNe3_of_mfNC {tY : StatedLieTag} {nY : ℕ} (hrow : TwinRow tY nY)
    (h : TwinMFCommutantOn tY (modelUniv tY nY 3 1 Nat.prime_three)) :
    TwinCentralizingNe3 tY nY := by
  intro R R' x x' ã ã' hd hãR hã'R _ _
  by_contra hno
  push Not at hno
  obtain ⟨S₀, hS₀, hne, hnc⟩ := (twinRowFacts3_of_row hrow).nc R hd.mem
  rcases h R R' x x' hd S₀ hS₀ (fun S hS hSR hSR' => by
      exfalso
      refine hno S hS (fun s hs => ?_)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : s * ã = ã * s := hSR s hs ã hãR
      have h2 : s * ã' = ã' * s := hSR' s hs ã' hã'R
      calc s * (ã * ã') = (s * ã) * ã' := by group
        _ = (ã * s) * ã' := by rw [h1]
        _ = ã * (s * ã') := by group
        _ = ã * (ã' * s) := by rw [h2]
        _ = (ã * ã') * s := by group) with h' | h'
  · exact hne h'
  · exact hnc (h' ▸ hd.comm.symm)

theorem twinYType3On_of_model {P : StatedLieTag → ℕ → Prop} (h3 : OddThreeFreeInput)
    (hMF : ∀ t n, TwinRow t n → P t n →
      TwinMFCommutantOn t (modelUniv t n 3 1 Nat.prime_three))
    (hcount : ∀ t n, TwinRow t n → P t n → TwinRank3Model t n) (hsmall : SmallNoThree3) :
    Q3TY.TwinYType3On P := by
  have hne : ∀ t n, TwinRow t n → P t n → TwinCentralizingNe3 t n :=
    fun t n hrow hP => twinCentralizingNe3_of_mfNC hrow (hMF t n hrow hP)
  exact twinYType3On_of_inputs h3 (twinYNoCentral3_of_model hMF) (twinYKind3_of_model hne)
    (twinYRank3_of_model hcount hne hsmall)

theorem twinYType3_large_of_model (h3 : OddThreeFreeInput)
    (hMF : ∀ t n, TwinRowLarge3 t n →
      TwinMFCommutantOn t (modelUniv t n 3 1 Nat.prime_three))
    (hcount : ∀ t n, TwinRowLarge3 t n → TwinRank3Model t n) (hsmall : SmallNoThree3) :
    Q3TY.TwinYType3On TwinRowLarge3 :=
  twinYType3On_of_model h3 (fun t n _ hP => hMF t n hP) (fun t n _ hP => hcount t n hP) hsmall

end CFSG.ClassicalInvolution.Q3.Q3TIY
