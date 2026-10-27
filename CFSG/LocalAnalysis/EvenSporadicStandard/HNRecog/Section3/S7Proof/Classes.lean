module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.ClassesCycle

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem s7_exists_conj_of_cycleType {a x : G} (φ : ↥(Gxy a x) ≃* Sym 7)
    {u u' : ↥(Gxy a x)} (h : (φ u).cycleType = (φ u').cycleType) :
    ∃ k ∈ Gxy a x, k * (u : G) * k⁻¹ = (u' : G) := by
  have hconj : IsConj (φ u) (φ u') := by
    rwa [Equiv.Perm.isConj_iff_cycleType_eq]
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  refine ⟨((φ.symm g : ↥(Gxy a x)) : G), (φ.symm g).2, ?_⟩
  have h2 := congrArg (fun y : ↥(Gxy a x) => (y : G)) (congrArg φ.symm hg)
  simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] using h2

theorem s7_cycleType {a z : G} (H : S7Hyps a z) :
    ∀ x ∈ orb3A a a, ∀ φ : ↥(Gxy a x) ≃* Sym 7, ∀ t : ↥(Gxy a x),
      ((t : G) ∈ orb2A a a ∩ orb2A a x → (φ t).cycleType = {2}) ∧
      ((t : G) ∈ orb2B a z a ∩ orb2B a z x → (φ t).cycleType = {2, 2}) ∧
      ((t : G) ∈ orb2BB a z a ∩ orb2BB a z x → (φ t).cycleType = {2, 2, 2}) := by
  intro x hx φ t
  refine ⟨?_, ?_, ?_⟩
  · intro htD
    exact (s7_phi_D H hx φ t).mp htD
  · intro htE2
    have ht2 : orderOf (t : G) = 2 := (s7_E2_subset H hx.1 htE2).2
    rcases s7_classes_cycle H hx φ t ht2 with ⟨hD, _⟩ | ⟨hE2, hcyc⟩ | ⟨hE3, _⟩
    · exact (s7_not_both H hD.2.2 htE2.2.2).elim
    · exact hcyc
    · exact (s7_not_both H htE2.1.1 hE3.1.1).elim
  · intro htE3
    have ht2 : orderOf (t : G) = 2 := (s7_E3_subset H hx.1 htE3).2
    rcases s7_classes_cycle H hx φ t ht2 with ⟨hD, _⟩ | ⟨hE2, _⟩ | ⟨hE3, hcyc⟩
    · exact (s7_not_both H hD.1.1 htE3.1.1).elim
    · exact (s7_not_both H hE2.1.1 htE3.1.1).elim
    · exact hcyc

theorem s7_classes [Finite G] {a z x : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a) :
    IsOrbitPartition (Gxy a x) {t | t ∈ Gxy a x ∧ orderOf t = 2} (s7Set a z x) := by
  obtain ⟨φ⟩ := s7_shape H hx
  refine ⟨?_, ?_, s7_disjoint H x, ?_⟩
  · intro i
    fin_cases i
    · exact s7_D_subset H hx.1
    · exact s7_E2_subset H hx.1
    · exact s7_E3_subset H hx.1
  · intro c hc
    rcases s7_classes_cycle H hx φ ⟨c, hc.1⟩ hc.2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · intro i
    fin_cases i
    · refine ⟨fun k hk c hc => s7_conj_D hk hc, hx.2.2, ?_⟩
      intro c hc c' hc'
      let u : ↥(Gxy a x) := ⟨c, (s7_D_subset H hx.1 hc).1⟩
      let u' : ↥(Gxy a x) := ⟨c', (s7_D_subset H hx.1 hc').1⟩
      have hcyc : (φ u).cycleType = (φ u').cycleType := by
        rw [(s7_cycleType H x hx φ u).1 hc, (s7_cycleType H x hx φ u').1 hc']
      have h := s7_exists_conj_of_cycleType φ hcyc
      change ∃ k ∈ Gxy a x, k * (u : G) * k⁻¹ = (u' : G) at h
      exact h
    · refine ⟨fun k hk c hc => s7_conj_E2 hk hc, s7_E2_nonempty H hx, ?_⟩
      intro c hc c' hc'
      let u : ↥(Gxy a x) := ⟨c, (s7_E2_subset H hx.1 hc).1⟩
      let u' : ↥(Gxy a x) := ⟨c', (s7_E2_subset H hx.1 hc').1⟩
      have hcyc : (φ u).cycleType = (φ u').cycleType := by
        rw [(s7_cycleType H x hx φ u).2.1 hc, (s7_cycleType H x hx φ u').2.1 hc']
      have h := s7_exists_conj_of_cycleType φ hcyc
      change ∃ k ∈ Gxy a x, k * (u : G) * k⁻¹ = (u' : G) at h
      exact h
    · refine ⟨fun k hk c hc => s7_conj_E3 hk hc, s7_E3_nonempty H hx, ?_⟩
      intro c hc c' hc'
      let u : ↥(Gxy a x) := ⟨c, (s7_E3_subset H hx.1 hc).1⟩
      let u' : ↥(Gxy a x) := ⟨c', (s7_E3_subset H hx.1 hc').1⟩
      have hcyc : (φ u).cycleType = (φ u').cycleType := by
        rw [(s7_cycleType H x hx φ u).2.2 hc, (s7_cycleType H x hx φ u').2.2 hc']
      have h := s7_exists_conj_of_cycleType φ hcyc
      change ∃ k ∈ Gxy a x, k * (u : G) * k⁻¹ = (u' : G) at h
      exact h

end CFSG.EvenSporadicStandard.HNRecog.Section3
