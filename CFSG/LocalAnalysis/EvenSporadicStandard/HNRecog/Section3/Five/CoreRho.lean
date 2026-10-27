module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FiveLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Vertex
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Klein
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem exists_core_of_orb5E (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hCore : Vert FiveCoreFacts a z) (hPar : ParityFacts a z)
    (hCls : GzClassFacts a z) (hT4 : TableIVFacts a z) (hT6 : TableVIFacts a z) {x : G}
    (hx : x ∈ orb5E a a) :
    ∃ s z' : G, IsConj a s ∧ IsConj z z' ∧ IsConj z (s * z') ∧ s ∈ Gxy a x ∧ z' ∈ Gx (a * x) ∧
      s * z' = z' * s ∧ Nat.card ↥(Subgroup.closure ({s, z'} : Set G)) = 4 ∧
      Nonempty (↥(Subgroup.closure ({s, z'} : Set G)) ≃* Elem2 2) ∧
      ∃ N : Subgroup G, N ≤ Gx (a * x) ∧ (N.subgroupOf (Gx (a * x))).Normal ∧ IsPGroup 5 ↥N ∧
        Nat.card ↥N ≤ 5 ^ 4 ∧ N ⊔ Subgroup.closure ({s, z'} : Set G) = Gx (a * x) ∧
        N ⊓ Subgroup.closure ({s, z'} : Set G) = ⊥ := by
  classical
  have hx' := hx
  simp only [orb5E, oddSet, Set.mem_setOf_eq] at hx'
  obtain ⟨hxodd, hρord, -⟩ := hx'
  obtain ⟨hconj_x, hx_ne_a, hodd, s, hs, hsx⟩ := hxodd
  have hsa : a * s = s * a := mem_Gx.mp (mem_Gxy.mp hsx).1
  have hsx' : x * s = s * x := mem_Gx.mp (mem_Gxy.mp hsx).2
  have hρGs : a * x ∈ Gx s := by
    rw [mem_Gx]
    calc s * (a * x) = (s * a) * x := by rw [mul_assoc]
      _ = (a * s) * x := by rw [← hsa]
      _ = a * (s * x) := by rw [mul_assoc]
      _ = a * (x * s) := by rw [← hsx']
      _ = (a * x) * s := by rw [← mul_assoc]
  have hshape : IsShapeCentralizerFiveB ↥(Gxy s (a * x)) :=
    isShapeCentralizerFiveB_of_orb5E h hPar hCls hT4 hT6 hx hs hsx
  have hC : FiveCoreFacts s z := hCore s z hs (IsConj.refl z)
  let T : Sylow 2 ↥(Gxy s (a * x)) := default
  obtain ⟨z', hz, hsz, -, hTmap, -⟩ := hC.sylow (a * x) hρGs hρord hshape T
  obtain ⟨N, hNle, hNn, hN5, hNcard, hNsup, hNinf⟩ :=
    hC.odd_core (a * x) hρGs hρord hshape T
  have hz'clos : z' ∈ Subgroup.closure ({s, z'} : Set G) := Subgroup.subset_closure (by simp)
  have hz'Gxy : z' ∈ Gxy s (a * x) :=
    Subgroup.map_subtype_le (T : Subgroup ↥(Gxy s (a * x))) (hTmap.symm ▸ hz'clos)
  have hz'Gx : z' ∈ Gx (a * x) := (mem_Gxy.mp hz'Gxy).2
  have hscomm : s * z' = z' * s := mem_Gx.mp (mem_Gxy.mp hz'Gxy).1
  have hs2ord : orderOf s = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hs
    rw [← hc]
    simpa [MulAut.conj_apply] using
      (MulEquiv.orderOf_eq (MulAut.conj c) a).trans h.orderOf_a
  have hz'2ord : orderOf z' = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hz
    rw [← hc]
    simpa [MulAut.conj_apply] using
      (MulEquiv.orderOf_eq (MulAut.conj c) z).trans h.orderOf_z
  have hs2 : s * s = 1 := by
    have : s ^ 2 = 1 := by rw [← hs2ord]; exact pow_orderOf_eq_one s
    simpa [pow_two] using this
  have hz'2 : z' * z' = 1 := by
    have : z' ^ 2 = 1 := by rw [← hz'2ord]; exact pow_orderOf_eq_one z'
    simpa [pow_two] using this
  have hs1 : s ≠ 1 := by
    intro h1
    have : orderOf s = 1 := orderOf_eq_one_iff.mpr h1
    rw [hs2ord] at this
    exact (by norm_num : (2 : ℕ) ≠ 1) this
  have hz'1 : z' ≠ 1 := by
    intro h1
    have : orderOf z' = 1 := orderOf_eq_one_iff.mpr h1
    rw [hz'2ord] at this
    exact (by norm_num : (2 : ℕ) ≠ 1) this
  have hsne : s ≠ z' := by
    intro h1
    have hzs : IsConj z s := by
      have hzcopy := hz
      rw [← h1] at hzcopy
      exact hzcopy
    exact not_isConj_of_isF5Type hI h (hs.trans hzs.symm)
  have hcard : Nat.card ↥(Subgroup.closure ({s, z'} : Set G)) = 4 :=
    card_closure_pair_of_involutions hs2 hz'2 hscomm hs1 hz'1 hsne
  have hKlein : Nonempty (↥(Subgroup.closure ({s, z'} : Set G)) ≃* Elem2 2) :=
    nonempty_mulEquiv_elem_two_of_involutions hs2 hz'2 hscomm hs1 hz'1 hsne
  refine ⟨s, z', hs, hz, hsz, hsx, hz'Gx, hscomm, hcard, hKlein, N, hNle, hNn, hN5, hNcard,
    ?_, ?_⟩
  · rw [← hTmap]; exact hNsup
  · rw [← hTmap]; exact hNinf

end CFSG.EvenSporadicStandard.HNRecog.Section3
