module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpSym7Gen

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

structure IsInvReps (a x : G) (R : Set G) : Prop where
  subset : R ⊆ InvIn (Gxy a x)
  cover : ∀ t ∈ InvIn (Gxy a x), ∃ r ∈ R, ConjIn (Gxy a x) r t
  generate : Subgroup.closure (⋃ r ∈ R, (Gxyz a r x : Set G)) = Gxy a x

theorem isInvReps_config (h : F5Std a z) {t t' x : G} (ht : t ∈ orb2A a a) (ht' : t' ∈ orb2B a z a)
    (htt : t * t' ∈ orb2BB a z a) (hx : x ∈ orb3A a a) (hxt : x ∈ Gxy t t') :
    IsInvReps a x {t, t', t * t'} := by
  have htGa : t ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) ht
  have ht'Ga : t' ∈ Gx a := h.mem_Gx_of_orb2B (IsConj.refl a) ht'
  have hxGt : x ∈ Gx t := (mem_Gxy.mp hxt).1
  have hxGt' : x ∈ Gx t' := (mem_Gxy.mp hxt).2
  have htGx : t ∈ Gx x := mem_Gx.mpr (mem_Gx.mp hxGt).symm
  have ht'Gx : t' ∈ Gx x := mem_Gx.mpr (mem_Gx.mp hxGt').symm
  have htK : t ∈ Gxy a x := mem_Gxy.mpr ⟨htGa, htGx⟩
  have ht'K : t' ∈ Gxy a x := mem_Gxy.mpr ⟨ht'Ga, ht'Gx⟩
  have httK : t * t' ∈ Gxy a x := (Gxy a x).mul_mem htK ht'K
  have hord_t : orderOf t = 2 := h.orderOf_eq_two (Or.inl ht.1)
  have hord_t' : orderOf t' = 2 := h.orderOf_eq_two (Or.inl ht'.1)
  have hord_tt' : orderOf (t * t') = 2 := h.orderOf_eq_two (Or.inr htt.1)
  have hcomm : t * t' = t' * t := h.mul_comm (Or.inl ht.1) (Or.inl ht'.1) (Or.inr htt.1)
  have htInv : t ∈ InvIn (Gxy a x) := ⟨htK, hord_t⟩
  have ht'Inv : t' ∈ InvIn (Gxy a x) := ⟨ht'K, hord_t'⟩
  have httInv : t * t' ∈ InvIn (Gxy a x) := ⟨httK, hord_tt'⟩
  have hcl := h.loc.s7.self.classes x hx
  have ht0 : t ∈ s7Set a z x 0 := by
    obtain ⟨i, hi⟩ := hcl.cover t htInv
    fin_cases i
    · exact hi
    · exfalso
      simp [s7Set] at hi
      exact h.not_isConj (ht.2.trans (IsConj.symm hi.1.2))
    · exfalso
      simp [s7Set] at hi
      exact h.not_isConj (ht.1.trans (IsConj.symm hi.1.1))
  have ht'1 : t' ∈ s7Set a z x 1 := by
    obtain ⟨i, hi⟩ := hcl.cover t' ht'Inv
    fin_cases i
    · exfalso
      simp [s7Set] at hi
      exact h.not_isConj (hi.1.2.trans (IsConj.symm ht'.2))
    · exact hi
    · exfalso
      simp [s7Set] at hi
      exact h.not_isConj (ht'.1.trans (IsConj.symm hi.1.1))
  have htt2 : t * t' ∈ s7Set a z x 2 := by
    obtain ⟨i, hi⟩ := hcl.cover (t * t') httInv
    fin_cases i
    · exfalso
      simp [s7Set] at hi
      exact h.not_isConj (hi.1.1.trans (IsConj.symm htt.1))
    · exfalso
      simp [s7Set] at hi
      exact h.not_isConj (hi.1.1.trans (IsConj.symm htt.1))
    · exact hi
  have ht0' : t ∈ orb2A a a ∩ orb2A a x := by simpa [s7Set] using ht0
  have ht'1' : t' ∈ orb2B a z a ∩ orb2B a z x := by simpa [s7Set] using ht'1
  have htt2' : t * t' ∈ orb2BB a z a ∩ orb2BB a z x := by simpa [s7Set] using htt2
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · exact htInv
    · exact ht'Inv
    · exact httInv
  · intro s hs
    obtain ⟨i, hi⟩ := hcl.cover s hs
    fin_cases i
    · exact ⟨t, by simp, (hcl.orbit 0).transitive t ht0 s hi⟩
    · exact ⟨t', by simp, (hcl.orbit 1).transitive t' ht'1 s hi⟩
    · exact ⟨t * t', by simp, (hcl.orbit 2).transitive (t * t') htt2 s hi⟩
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      obtain ⟨r, -, hgr⟩ := Set.mem_iUnion₂.mp hg
      exact mem_Gxy.mpr ⟨(mem_Gxyz.mp hgr).1, (mem_Gxyz.mp hgr).2.2⟩
    · obtain ⟨φ⟩ := h.loc.s7.self.shape x hx
      have hcycle := h.loc.s7.self.cycleType x hx φ
      have h1 : (φ ⟨t, htK⟩).cycleType = {2} := (hcycle ⟨t, htK⟩).1 ht0'
      have h2 : (φ ⟨t', ht'K⟩).cycleType = {2, 2} := (hcycle ⟨t', ht'K⟩).2.1 ht'1'
      have h3 : (φ ⟨t * t', httK⟩).cycleType = {2, 2, 2} :=
        (hcycle ⟨t * t', httK⟩).2.2 htt2'
      have hgen := cp_s7_cent_gen φ htK ht'K hcomm h1 h2 h3
      have hcent_t : (Gxy a x ⊓ Subgroup.centralizer {t} : Subgroup G) = Gxyz a t x := by
        ext g
        simp only [Subgroup.mem_inf, mem_Gxyz, mem_Gxy, mem_Gx,
          Subgroup.mem_centralizer_singleton_iff]
        tauto
      have hcent_t' : (Gxy a x ⊓ Subgroup.centralizer {t'} : Subgroup G) = Gxyz a t' x := by
        ext g
        simp only [Subgroup.mem_inf, mem_Gxyz, mem_Gxy, mem_Gx,
          Subgroup.mem_centralizer_singleton_iff]
        tauto
      have hsub : (((Gxy a x ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) ∪
          ((Gxy a x ⊓ Subgroup.centralizer {t'} : Subgroup G) : Set G)) ⊆
          (⋃ r ∈ ({t, t', t * t'} : Set G), (Gxyz a r x : Set G)) := by
        intro g hg
        rcases hg with hg | hg
        · rw [hcent_t] at hg
          exact Set.mem_iUnion₂_of_mem (by simp : t ∈ ({t, t', t * t'} : Set G)) hg
        · rw [hcent_t'] at hg
          exact Set.mem_iUnion₂_of_mem (by simp : t' ∈ ({t, t', t * t'} : Set G)) hg
      exact hgen.trans (Subgroup.closure_mono hsub)

end CFSG.EvenSporadicStandard.HNRecog.Section4
