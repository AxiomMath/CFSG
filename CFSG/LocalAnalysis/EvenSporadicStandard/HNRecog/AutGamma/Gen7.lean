module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem closure_orb2A_inter_eq (hF : IsF5Type a z) (hL : F5Local G a z) {x : G}
    (hx : x ∈ orb3A a a) : Subgroup.closure (orb2A a a ∩ orb2A a x) = Gxy a x := by
  classical
  obtain ⟨φ⟩ := hL.s7.self.shape x hx
  set P : Set G := orb2A a a ∩ orb2A a x with hP
  have hle : Subgroup.closure P ≤ Gxy a x := by
    rw [Subgroup.closure_le]
    rintro t ⟨⟨hta, htaa⟩, -, hxt⟩
    exact mem_Gxy.mpr ⟨mem_Gx.mpr (comm_of_adj hF (IsConj.refl a) hta htaa),
      mem_Gx.mpr (comm_of_adj hF hx.1 hta hxt)⟩
  have hswapP : ∀ t : ↥(Gxy a x), (φ t).IsSwap → (t : G) ∈ P := by
    intro t ht
    have ht2 : orderOf t = 2 := by
      rw [← MulEquiv.orderOf_eq φ t, Equiv.Perm.IsSwap.orderOf ht]
    have hmem : (t : G) ∈ {u : G | u ∈ Gxy a x ∧ orderOf u = 2} :=
      ⟨t.2, by rw [Subgroup.orderOf_coe]; exact ht2⟩
    obtain ⟨i, hi⟩ := (hL.s7.self.classes x hx).cover (t : G) hmem
    have hcyc : (φ t).cycleType = {2} := Equiv.Perm.isSwap_iff_cycleType.mp ht
    fin_cases i
    · rw [hP]
      exact hi
    · exfalso
      have h22 : (φ t).cycleType = {2, 2} := (hL.s7.self.cycleType x hx φ t).2.1 hi
      have hcard := congrArg Multiset.card (hcyc.symm.trans h22)
      simp at hcard
    · exfalso
      have h222 : (φ t).cycleType = {2, 2, 2} := (hL.s7.self.cycleType x hx φ t).2.2 hi
      have hcard := congrArg Multiset.card (hcyc.symm.trans h222)
      simp at hcard
  let Q : Subgroup ↥(Gxy a x) :=
    Subgroup.comap (Gxy a x).subtype (Subgroup.closure P)
  have hmap : Subgroup.map (φ : ↥(Gxy a x) →* Sym 7) Q = ⊤ := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    intro σ hσ
    refine Subgroup.mem_map.mpr ⟨φ.symm σ, ?_, φ.apply_symm_apply σ⟩
    exact Subgroup.subset_closure (hswapP (φ.symm σ) (by rwa [φ.apply_symm_apply]))
  have hQ : Q = ⊤ := by
    rw [eq_top_iff]
    intro t _
    have ht : φ t ∈ Subgroup.map (φ : ↥(Gxy a x) →* Sym 7) Q := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨q, hq, hqt⟩ := Subgroup.mem_map.mp ht
    rwa [φ.injective hqt] at hq
  refine le_antisymm hle ?_
  intro g hg
  have hgQ : (⟨g, hg⟩ : ↥(Gxy a x)) ∈ Q := by
    rw [hQ]
    exact Subgroup.mem_top _
  exact hgQ

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
