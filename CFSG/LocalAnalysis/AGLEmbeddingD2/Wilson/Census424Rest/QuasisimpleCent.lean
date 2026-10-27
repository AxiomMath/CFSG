module

public import CFSG.RankThree.PartTwo.Sec11.FieldCentRigid82
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofBasic
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

theorem commutatorElement_mul_central {C : Type*} [Group C] {k₁ k₂ w₁ w₂ : C}
    (h₁ : w₁ ∈ Subgroup.center C) (h₂ : w₂ ∈ Subgroup.center C) :
    ⁅k₁ * w₁, k₂ * w₂⁆ = ⁅k₁, k₂⁆ := by
  have c1 : ∀ g : C, g * w₁ = w₁ * g := fun g => (Subgroup.mem_center_iff.mp h₁ g)
  have c2 : ∀ g : C, g * w₂ = w₂ * g := fun g => (Subgroup.mem_center_iff.mp h₂ g)
  simp only [commutatorElement_def, mul_inv_rev]
  calc k₁ * w₁ * (k₂ * w₂) * (w₁⁻¹ * k₁⁻¹) * (w₂⁻¹ * k₂⁻¹)
      = k₁ * (w₁ * (k₂ * w₂) * w₁⁻¹) * k₁⁻¹ * (w₂⁻¹ * k₂⁻¹) := by group
    _ = k₁ * (k₂ * w₂) * k₁⁻¹ * (w₂⁻¹ * k₂⁻¹) := by
        rw [← c1 (k₂ * w₂)]; group
    _ = k₁ * k₂ * (w₂ * k₁⁻¹ * w₂⁻¹) * k₂⁻¹ := by group
    _ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by
        rw [← c2 k₁⁻¹]; group

theorem false_of_mem_thetaComponents_of_quasisimple {C : Type} [Group C] [Finite C]
    (hC : CFSG.IsQuasisimple C) {z : C} (hz : z ∈ Subgroup.center C) (hz3 : orderOf z = 3)
    {K : Subgroup C} (hK : K ∈ thetaComponents 3 C)
    (hT : Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K)) : False := by
  obtain ⟨-, hsub, hq⟩ := hK
  obtain ⟨hCperf, hCsimple, -⟩ := hC
  set π : C →* C ⧸ Subgroup.center C := QuotientGroup.mk' (Subgroup.center C) with hπ
  have hmap : (K.map π).IsSubnormal := hsub.map (QuotientGroup.mk'_surjective _)
  rcases hmap.eq_bot_or_top_of_isSimpleGroup hCsimple with h0 | h1
  ·
    obtain ⟨-, -, a, b, hab⟩ := hq
    have hKc : ∀ x ∈ K, x ∈ Subgroup.center C := by
      intro x hx
      have : π x ∈ K.map π := ⟨x, hx, rfl⟩
      rw [h0, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨a'', rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨b'', rfl⟩ := QuotientGroup.mk_surjective b'
    apply hab
    have hcomm : (a'' : C) * b'' = b'' * a'' := by
      have := Subgroup.mem_center_iff.mp (hKc _ b''.2) a''
      exact this
    have hcomm' : a'' * b'' = b'' * a'' := Subtype.ext hcomm
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, hcomm']
  ·
    have hsurj : ∀ c : C, ∃ k ∈ K, ∃ w ∈ Subgroup.center C, c = k * w := by
      intro c
      have : π c ∈ K.map π := by rw [h1]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkc⟩ := this
      refine ⟨k, hk, k⁻¹ * c, ?_, by group⟩
      have : π k = π c := hkc
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
      exact this
    have hcomm_le : _root_.commutator C ≤ K := by
      rw [_root_.commutator, Subgroup.commutator_def]
      refine (Subgroup.closure_le K).mpr ?_
      rintro g ⟨g₁, -, g₂, -, rfl⟩
      obtain ⟨k₁, hk₁, w₁, hw₁, rfl⟩ := hsurj g₁
      obtain ⟨k₂, hk₂, w₂, hw₂, rfl⟩ := hsurj g₂
      rw [commutatorElement_mul_central hw₁ hw₂, commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)
    have hKtop : K = ⊤ := by
      rw [eq_top_iff]
      intro c _
      exact hcomm_le (by rw [hCperf.commutator_eq_top]; exact Subgroup.mem_top c)
    have hzK : z ∈ K := by rw [hKtop]; exact Subgroup.mem_top z
    have hz3' : z ^ 3 = 1 := by rw [← hz3]; exact pow_orderOf_eq_one z
    have := Item424Proof.eq_one_of_mem_of_commute (K := K)
      (Sec11.FieldCentRigid82.center_eq_bot_of_isType424 hT) hzK
      (fun k _ => (Subgroup.mem_center_iff.mp hz k).symm) hz3'
    rw [this, orderOf_one] at hz3
    omega

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
