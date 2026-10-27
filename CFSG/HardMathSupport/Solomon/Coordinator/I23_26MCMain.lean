module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26MCX

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem mc_generation {X : Type} [Group X] [Finite X] {K E : Subgroup X}
    (hK : IsComponentOf K ⊤) (h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K))
    (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hmove : ¬ E ≤ Subgroup.normalizer (K : Set X))
    (hfaith : ∀ e ∈ E, (∀ k ∈ K, e * k = k * e) → e = 1) :
    K ≤ ⨆ (e : X) (_ : e ∈ E) (_ : e ≠ 1),
      GLAPLayer 3 ((⨆ g ∈ E, GLBConj g K) ⊓ Subgroup.centralizer ({e} : Set X)) := by
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
  have hE3 : ∀ a ∈ E, a ^ 3 = 1 := hE.2
  have hE1 : (1 : X) ∈ E := E.one_mem
  obtain ⟨g₀, hg₀E, hg₀K⟩ : ∃ g₀ ∈ E, GLBConj g₀ K ≠ K := by
    obtain ⟨g, hgE, hg⟩ := IsConcreteLE.not_le_iff_exists.1 hmove
    refine ⟨g, hgE, fun hc => hg ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : y ∈ GLBConj g K ↔ y ∈ K := by rw [hc]
    rw [← h1, mem_gLBConj]
  let A : ↥E → Subgroup ↥(mcPi K E) := fun i => mcA K E (i : X)
  have hAn : ∀ i : ↥E, (A i).Normal := fun i => mcA_normal hK (i : X)
  have hmax : ∀ (i : ↥E) (N : Subgroup ↥(mcPi K E)), N.Normal → A i ≤ N → N = A i ∨ N = ⊤ :=
    fun i N hN hAN => by
      have := hN
      exact mc_hmax hK i.2 N hAN
  have hnab : ∀ i : ↥E, ¬ ⁅(⊤ : Subgroup ↥(mcPi K E)), (⊤ : Subgroup ↥(mcPi K E))⁆ ≤ A i :=
    fun i => mc_hnab hK i.2
  let T : Subgroup ↥(mcPi K E) := (mcT K E).subgroupOf (mcPi K E)
  have hT : ∀ i : ↥E, T ⊔ A i = ⊤ := fun i => mc_hT hK hEc hg₀E (hE3 g₀ hg₀E) hg₀K i.2
  have hne : ∃ t ∈ T, ∃ i : ↥E, t ∉ A i := by
    obtain ⟨t, ht, ht'⟩ := mc_exists_not_mem hK hE1 hg₀E (hE3 g₀ hg₀E) hg₀K
    exact ⟨t, ht, ⟨1, hE1⟩, ht'⟩
  obtain ⟨t, htT, ⟨i₀, hi₀⟩, hstar⟩ := mc_min_support A hmax hnab T hT hne
  have hall : ∀ j : ↥E, GLBConj (j : X) K ≠ GLBConj (i₀ : X) K → t ∈ A j := by
    intro j hjne
    by_contra htj
    have hle := hstar i₀ j hi₀ htj
    obtain ⟨y, z, hy, hz, hyz0, w, hw, hwne⟩ :=
      mc_cross hK hEc hE3 hE27 hfaith i₀.2 j.2 hjne
    have hyP : y ∈ mcPi K E := mc_T_le_pi hy
    have hzP : z ∈ mcPi K E := mc_T_le_pi hz
    have hmem : (⟨y, hyP⟩ : ↥(mcPi K E))⁻¹ * ⟨z, hzP⟩ ∈ T ⊓ A i₀ := by
      refine ⟨T.mul_mem (T.inv_mem hy) hz, ?_⟩
      show (⟨y, hyP⟩ : ↥(mcPi K E))⁻¹ * ⟨z, hzP⟩ ∈ mcA K E (i₀ : X)
      rw [mem_mcA]
      exact hyz0
    have h2 : (⟨y, hyP⟩ : ↥(mcPi K E))⁻¹ * ⟨z, hzP⟩ ∈ mcA K E (j : X) := hle hmem
    rw [mem_mcA] at h2
    exact hwne (h2 w hw)
  have hB : ⁅(GLBConj (i₀ : X) K).subgroupOf (mcPi K E), (GLBConj (i₀ : X) K).subgroupOf (mcPi K E)⁆ =
      (GLBConj (i₀ : X) K).subgroupOf (mcPi K E) := by
    have hperf := mc_commutator_eq_of_qs (mc_isComponentOf_gLBConj hK (i₀ : X)).2.2
    apply Subgroup.map_injective (mcPi K E).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (mc_le_pi i₀.2), hperf]
  have hfin : (GLBConj (i₀ : X) K).subgroupOf (mcPi K E) ≤ T := by
    refine mc_final A hmax T hT _ hB htT hi₀ (fun j => ?_) (fun z hz => ?_)
    · by_cases hjeq : GLBConj (j : X) K = GLBConj (i₀ : X) K
      · left
        show mcA K E (j : X) = mcA K E (i₀ : X)
        unfold mcA
        rw [hjeq]
      · right
        refine ⟨hall j hjeq, fun b hb => ?_⟩
        show b ∈ mcA K E (j : X)
        rw [mem_mcA]
        intro y hy
        have hb' : (b : X) ∈ GLBConj (i₀ : X) K := hb
        exact mc_comm_of_ne (mc_isComponentOf_gLBConj hK (j : X))
          (mc_isComponentOf_gLBConj hK (i₀ : X)) hjeq hy hb'
    · rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact mc_pi_central z.2 (fun e he y hy => mem_mcA.1 (hz ⟨e, he⟩) y hy) g.2
  have hK0T : GLBConj (i₀ : X) K ≤ mcT K E := by
    intro x hx
    have hxP : x ∈ mcPi K E := mc_le_pi i₀.2 hx
    exact hfin (show (⟨x, hxP⟩ : ↥(mcPi K E)) ∈ (GLBConj (i₀ : X) K).subgroupOf (mcPi K E) from hx)
  have hKT : K ≤ mcT K E := mc_le_T_of_conj hEc i₀.2 hK0T
  exact hKT.trans (mc_T_le_M hK hEc h3)

end CFSG.HardMathSupport.Solomon.Coordinator
