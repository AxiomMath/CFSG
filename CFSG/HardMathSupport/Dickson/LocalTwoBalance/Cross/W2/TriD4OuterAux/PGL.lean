module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open (StatedScalars)

section PGL

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem eq_one_of_commute_slPi_image (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (z : ↥(projImage (glPi π 3 (p ^ f) K)))
    (hz : ∀ x : ↥(projImage (glPi π 3 (p ^ f) K)),
      (x : Matrix.ProjGenLinGroup (Fin 3) K) ∈ projImage (slPi π 3 (p ^ f) K) →
        z * x = x * z) : z = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hperf : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
    Sec13.isPerfect_projImage_slPi hK hq2
  obtain ⟨w, hwG, hw⟩ := z.2
  have hsc : w ∈ StatedScalars (Fin 3) K := by
    refine Sec4.mem_statedScalars_of_comm_mod hK hq (w := w) fun s hs => ?_
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars]
    have hsG : s ∈ glPi π 3 (p ^ f) K := Sec4.slPi_le_glPi hπ hs
    have h1 := hz ⟨Matrix.ProjGenLinGroup.mk s, Subgroup.mem_map_of_mem _ hsG⟩
      (Subgroup.mem_map_of_mem _ hs)
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    rw [← hw] at h2
    simp only [map_mul, map_inv]
    rw [h2]
    group
  refine Subtype.ext ?_
  rw [← hw, Subgroup.coe_one]
  exact (Sec4.mk_eq_one_iff_mem_statedScalars).2 hsc

theorem pgl_center_trivial (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (z : ↥(projImage (glPi π 3 (p ^ f) K))) (hz : ∀ x, z * x = x * z) : z = 1 :=
  eq_one_of_commute_slPi_image hK hq hq2 z fun x _ => hz x

theorem pgl_normal_coprime_eq_bot (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (N : Subgroup ↥(projImage (glPi π 3 (p ^ f) K))) [hNn : N.Normal]
    (hN : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have := hK.finite
  have hSP : projImage (slPi π 3 (p ^ f) K) ≤ projImage (glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup ↥(projImage (glPi π 3 (p ^ f) K)),
      Q = (projImage (slPi π 3 (p ^ f) K)).subgroupOf (projImage (glPi π 3 (p ^ f) K)) :=
    ⟨_, rfl⟩
  have hQn : Q.Normal := by
    have h : (commutator ↥(projImage (glPi π 3 (p ^ f) K))).Normal := inferInstance
    rwa [Sec13.commutator_projImage_glPi hK hq2, ← hQdef] at h
  have hQe : ↥Q ≃* ↥(projImage (slPi π 3 (p ^ f) K)) := by
    rw [hQdef]
    exact Subgroup.subgroupOfEquivOfLe hSP
  have hsimple : IsSimpleGroup ↥Q := by
    haveI := Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
    exact hQe.isSimpleGroup
  have h3Q : 3 ∣ Nat.card ↥Q :=
    KFacts.three_dvd_card_of_mulEquiv_projImage hQe (Sec4.cycThree_mem_slPi hπ)
  have hNQ : (N.subgroupOf Q).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf Q) with hbot | htop
  ·
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    refine eq_one_of_commute_slPi_image hK hq hq2 n fun x hx => ?_
    have hxQ : x ∈ Q := by rw [hQdef]; exact hx
    have hc1 : n * x * n⁻¹ * x⁻¹ ∈ N := by
      have : x * n⁻¹ * x⁻¹ ∈ N := hNn.conj_mem _ (inv_mem hn) x
      have h2 := mul_mem hn this
      simpa [mul_assoc] using h2
    have hc2 : n * x * n⁻¹ * x⁻¹ ∈ Q := by
      have : n * x * n⁻¹ ∈ Q := hQn.conj_mem _ hxQ n
      exact mul_mem this (inv_mem hxQ)
    have h3 : (⟨n * x * n⁻¹ * x⁻¹, hc2⟩ : ↥Q) ∈ N.subgroupOf Q := hc1
    rw [hbot, Subgroup.mem_bot] at h3
    have h4 : n * x * n⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h3
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
    exact h4
  ·
    exfalso
    have hQN : Q ≤ N := Subgroup.subgroupOf_eq_top.1 htop
    have h3N : 3 ∣ Nat.card N := h3Q.trans (Subgroup.card_dvd_of_le hQN)
    have := Nat.Coprime.eq_one_of_dvd hN h3N
    omega

end PGL

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
