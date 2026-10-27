module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatA.SFM6

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_or_inf_eq_bot_of_isSubnormal {D : Subgroup G} [hDn : D.Normal] [hDs : IsSimpleGroup D]
    {H : Subgroup G} (hH : H.IsSubnormal) : D ≤ H ∨ H ⊓ D = ⊥ := by
  induction hH with
  | top => exact Or.inl le_top
  | step H K hHK hK hN ih =>
    rcases ih with hDK | hKD
    · have hnorm : (H.subgroupOf D).Normal := by
        refine ⟨fun n hn g => ?_⟩
        have hn' : (n : G) ∈ H := Subgroup.mem_subgroupOf.1 hn
        have hc := hN.conj_mem ⟨(n : G), hDK n.2⟩ (Subgroup.mem_subgroupOf.2 hn')
          ⟨(g : G), hDK g.2⟩
        exact Subgroup.mem_subgroupOf.2 hc
      rcases hDs.eq_bot_or_eq_top_of_normal (H.subgroupOf D) with h | h
      · exact Or.inr (disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h))
      · exact Or.inl (Subgroup.subgroupOf_eq_top.1 h)
    · exact Or.inr (le_bot_iff.1 ((inf_le_inf_right D hHK).trans hKD.le))

theorem exists_ne_one_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    ∃ x : Q, x ≠ 1 := by
  obtain ⟨-, hs⟩ := hQ
  obtain ⟨z, hz⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  induction z using QuotientGroup.induction_on with
  | H a =>
    refine ⟨a, fun ha => hz ?_⟩
    rw [ha]
    rfl

theorem nonempty_mulEquiv_of_isSubnormal {D : Subgroup G} [hDn : D.Normal] [hDs : IsSimpleGroup D]
    (hcomm : commutator G ≤ D) {S : Subgroup G} (hS : S.IsSubnormal) {Q : Type} [Group Q]
    (φ : S →* Q) (hφ : Function.Surjective φ) (hQ : CFSG.Open.IsQuasisimple Q) :
    Nonempty (Q ≃* D) := by
  have hcomm' : ∀ g h : G, ⁅g, h⁆ ∈ D := fun g h =>
    hcomm (by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))
  have hQc : commutator Q = ⊤ := hQ.1
  rcases le_or_inf_eq_bot_of_isSubnormal (D := D) hS with hDS | hSD
  ·
    let ψ : D →* Q := φ.comp (Subgroup.inclusion hDS)
    have hψ : Function.Surjective ψ := by
      have hle : commutator Q ≤ ψ.range := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        obtain ⟨s, rfl⟩ := hφ a
        obtain ⟨t, rfl⟩ := hφ b
        refine ⟨⟨⁅(s : G), (t : G)⁆, hcomm' _ _⟩, ?_⟩
        have hst : (Subgroup.inclusion hDS ⟨⁅(s : G), (t : G)⁆, hcomm' _ _⟩ : S) = ⁅s, t⁆ := by
          apply Subtype.ext
          simp [commutatorElement_def]
        simp only [ψ, MonoidHom.comp_apply, hst, map_commutatorElement]
      intro q
      have hq : q ∈ commutator Q := by
        rw [hQc]
        exact Subgroup.mem_top q
      obtain ⟨d, hd⟩ := MonoidHom.mem_range.1 (hle hq)
      exact ⟨d, hd⟩
    have hker : ψ.ker = ⊥ := by
      rcases hDs.eq_bot_or_eq_top_of_normal ψ.ker with h | h
      · exact h
      · exfalso
        obtain ⟨x, hx⟩ := exists_ne_one_of_isQuasisimple hQ
        obtain ⟨d, rfl⟩ := hψ x
        have hd : d ∈ ψ.ker := by
          rw [h]
          exact Subgroup.mem_top d
        exact hx (MonoidHom.mem_ker.1 hd)
    exact ⟨(MulEquiv.ofBijective ψ ⟨(MonoidHom.ker_eq_bot_iff ψ).1 hker, hψ⟩).symm⟩
  ·
    exfalso
    have hcommS : ∀ s t : S, ⁅s, t⁆ = 1 := by
      intro s t
      have hval : ((⁅s, t⁆ : S) : G) = ⁅(s : G), (t : G)⁆ := by
        simp [commutatorElement_def]
      have hmem : ((⁅s, t⁆ : S) : G) ∈ S ⊓ D :=
        ⟨(⁅s, t⁆ : S).2, by rw [hval]; exact hcomm' _ _⟩
      rw [hSD] at hmem
      exact Subtype.ext (by simpa using Subgroup.mem_bot.1 hmem)
    have hbot : commutator Q ≤ ⊥ := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨s, rfl⟩ := hφ a
      obtain ⟨t, rfl⟩ := hφ b
      rw [← map_commutatorElement, hcommS, map_one]
      exact Subgroup.mem_bot.2 rfl
    obtain ⟨x, hx⟩ := exists_ne_one_of_isQuasisimple hQ
    apply hx
    have hxc : x ∈ commutator Q := by
      rw [hQc]
      exact Subgroup.mem_top x
    exact Subgroup.mem_bot.1 (hbot hxc)

end CFSG.LocalAnalysis.GLTheoremA.CatA.SFM6

end
