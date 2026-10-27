module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.BottomCentralInvolutionInverts

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.BottomBinaryCenterOrderTwo

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem Y_ne_bot (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1)) :
    CentralBinaryBlocks.Y hc ≠ ⊥ := by
  have he : Odd e := BottomCentralInvolutionInverts.odd_of_isPrimePow hc.oddPrimeClassTwoAction.two_lt hr
  set Ts : Subgroup (MulAut ↥P) := T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal) with hTs
  have hT2 : IsPGroup 2 Ts := hc.oddPrimeClassTwoAction.setting.twoGroup.map _
  have hTne : Ts ≠ ⊥ := by
    intro h
    have hS := (CoprimeStarSubgroupStructure.structure hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction).2.1
    apply hS
    rw [OddExponentCommutatorImage.commutator_image hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction.normal he, ← hTs, h]
    simp
  haveI : Nontrivial Ts := (Subgroup.nontrivial_iff_ne_bot Ts).mpr hTne
  haveI : Nontrivial (Subgroup.center Ts) := hT2.center_nontrivial
  have hZ : IsPGroup 2 (Subgroup.center Ts) := hT2.to_subgroup _ |>.to_le le_rfl
  obtain ⟨n, hn⟩ := hZ.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 := Finite.one_lt_card (α := Subgroup.center Ts)
    rw [hn] at h1
    simp at h1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Ts) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hmem : (z : Ts).1 ∈ CentralBinaryBlocks.Y hc := by
    unfold CentralBinaryBlocks.Y
    rw [JeTransport.mem_omegaOneZ_gen 2 _]
    refine Subgroup.subset_closure ⟨(z : Ts).2, ?_, ?_⟩
    · intro w hw
      have := Subgroup.mem_center_iff.mp z.2 ⟨w, hw⟩
      have := congrArg Subtype.val this
      exact this
    · have := congrArg (fun a : Subgroup.center Ts => ((a : Ts) : MulAut ↥P)) hz2
      simpa using this
  intro hY
  rw [hY] at hmem
  apply hz1
  apply Subtype.ext; apply Subtype.ext
  simpa using hmem

end CFSG.LocalAnalysis.RankThreeUC.Section5.BottomBinaryCenterOrderTwo
