module

public import CFSG.CGT.PushingUpLit.T2K.CoverInvolution
public import CFSG.CGT.PushingUpLit.T2K.Setup

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.ShultStronglyClosedTI
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}

namespace NatBlock

theorem cover_facts (h : NatBlock L n) :
    (∀ o ∈ oTwoIn L, o ^ 2 ∈ blockU L) ∧
    (∀ r ∈ L, r ∉ oTwoIn L → r ^ 2 ∈ blockU L → oTwoIn L = blockU L) ∧
    (3 ≤ n → oTwoIn L = blockU L) := by
  classical
  let D := h.natData
  let N : Subgroup ↥L := (blockU L).subgroupOf L
  have hN : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_blockU L)
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 h.perfect
  have hNker : N ≤ D.φ.ker := by
    intro x hx
    exact (D.φ_ker x).2 (blockU_le_oTwoIn L hx)
  let η : (↥L ⧸ N) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    QuotientGroup.lift N D.φ hNker
  have hη : ∀ l : ↥L, η (QuotientGroup.mk l) = D.φ l := fun l => rfl
  have hsurj : Function.Surjective η := by
    intro g
    obtain ⟨l, hl⟩ := D.φ_surj g
    exact ⟨QuotientGroup.mk l, by rw [hη, hl]⟩
  have hker : ∀ z : ↥L ⧸ N, η z = 1 → ∃ l : ↥L, (l : G) ∈ oTwoIn L ∧ QuotientGroup.mk l = z := by
    intro z hz
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [hη] at hz
    exact ⟨l, (D.φ_ker l).1 hz, rfl⟩
  have hcentral : η.ker ≤ Subgroup.center (↥L ⧸ N) := by
    intro z hz
    obtain ⟨l, hlO, rfl⟩ := hker z hz
    refine Subgroup.mem_center_iff.2 fun g => ?_
    obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    show ((l' * l)⁻¹ * (l * l') : ↥L) ∈ N
    rw [Subgroup.mem_subgroupOf]
    have h1 : ⁅(l : G)⁻¹, (l' : G)⁻¹⁆ ∈ ⁅oTwoIn L, L⁆ :=
      Subgroup.commutator_mem_commutator (inv_mem hlO) (inv_mem l'.2)
    have e : (((l' * l)⁻¹ * (l * l') : ↥L) : G) = ⁅(l : G)⁻¹, (l' : G)⁻¹⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      group
    rw [e]
    exact h1
  have hp : IsPGroup 2 η.ker := by
    intro g
    obtain ⟨l, hlO, hl⟩ := hker g.1 g.2
    obtain ⟨k, hk⟩ := isPGroup_oTwoIn L ⟨(l : G), hlO⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : ((l : G)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hk'' : l ^ 2 ^ k = 1 := Subtype.ext hk'
    show (g.1) ^ 2 ^ k = 1
    rw [← hl, ← QuotientGroup.mk_pow, hk'']
    rfl
  have hq : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by have := h.two_le; omega)
  have hbot : η.ker = ⊥ → oTwoIn L = blockU L := by
    intro hb
    refine le_antisymm (fun o ho => ?_) (blockU_le_oTwoIn L)
    have hz : η (QuotientGroup.mk ⟨o, oTwoIn_le L ho⟩) = 1 := by
      rw [hη]
      exact (D.φ_ker _).2 ho
    have hz' : QuotientGroup.mk (⟨o, oTwoIn_le L ho⟩ : ↥L) ∈ η.ker := hz
    rw [hb, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hz'
    exact (Subgroup.mem_subgroupOf.1 hz')
  refine ⟨fun o ho => ?_, fun r hr hrO hr2 => ?_, fun hn3 => ?_⟩
  · have hz : η (QuotientGroup.mk ⟨o, oTwoIn_le L ho⟩) = 1 := by
      rw [hη]
      exact (D.φ_ker _).2 ho
    have hsq := cover_ker_sq_eq_one hq hsurj hcentral hp _ hz
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hsq
    exact Subgroup.mem_subgroupOf.1 hsq
  · refine hbot (cover_ker_eq_bot_of_sq_eq_one hq hsurj hcentral hp
      (x := QuotientGroup.mk ⟨r, hr⟩) ?_ ?_)
    · rw [hη]
      intro h1
      exact hrO ((D.φ_ker _).1 h1)
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hr2
  · exact hbot (large_even_linear_central_two_cover_kernel_eq_bot n hn3 hq η hsurj hcentral hp)

theorem sq_mem_blockU_of_mem_oTwoIn (h : NatBlock L n) {o : G} (ho : o ∈ oTwoIn L) :
    o ^ 2 ∈ blockU L :=
  h.cover_facts.1 o ho

theorem oTwoIn_eq_blockU_of_sq_mem (h : NatBlock L n) {r : G} (hr : r ∈ L) (hrO : r ∉ oTwoIn L)
    (hr2 : r ^ 2 ∈ blockU L) : oTwoIn L = blockU L :=
  h.cover_facts.2.1 r hr hrO hr2

theorem oTwoIn_eq_blockU_of_three_le (h : NatBlock L n) (hn : 3 ≤ n) : oTwoIn L = blockU L :=
  h.cover_facts.2.2 hn

end NatBlock

end CFSG.CGT.PushingUpLit.T2K
