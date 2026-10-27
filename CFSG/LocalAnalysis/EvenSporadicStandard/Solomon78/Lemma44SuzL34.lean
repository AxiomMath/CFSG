module

public import CFSG.Monster.B.Co2.PermArr
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
public import CFSG.LieType.Steinberg.CentralExt.PSLSmall
public import Certificates.Certificate10741

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

private theorem suzL34PtsOK_spec :
    suzL34Pts.size = 42 ∧ (∀ i : Fin 42, suzL34Pts[i.val]! < 1782) ∧
      suzL34Pts.toList.Nodup := by
  have h := Certificates.certificate10741
  simp only [suzL34Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hpts, _⟩, _⟩, _⟩ := h
  simp only [suzL34PtsOK, Bool.and_eq_true, decide_eq_true_eq] at hpts
  obtain ⟨⟨hsize, hall⟩, hnd⟩ := hpts
  refine ⟨?_, ?_, hnd⟩
  · exact beq_iff_eq.mp hsize
  · intro i
    exact of_decide_eq_true ((List.all_eq_true.mp hall) i.val (List.mem_range.mpr i.isLt))

private theorem suzL34RestrOK_spec {t g : Array Nat}
    (h : suzL34RestrOK t g = true) :
    ∀ i : Fin 42, t[i.val]! < 42 ∧
      suzL34Pts[t[i.val]!]! = g[suzL34Pts[i.val]!]! := by
  intro i
  have h' := (List.all_eq_true.mp h) i.val (List.mem_range.mpr i.isLt)
  simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using h'

private theorem suzL34RestrA :
    ∀ i : Fin 42, suzL34TA[i.val]! < 42 ∧
      suzL34Pts[suzL34TA[i.val]!]! = suzArrA[suzL34Pts[i.val]!]! := by
  have h := Certificates.certificate10741
  simp only [suzL34Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, hA⟩, _⟩, _⟩ := h
  exact suzL34RestrOK_spec hA

private theorem suzL34RestrB :
    ∀ i : Fin 42, suzL34TB[i.val]! < 42 ∧
      suzL34Pts[suzL34TB[i.val]!]! = suzArrB[suzL34Pts[i.val]!]! := by
  have h := Certificates.certificate10741
  simp only [suzL34Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, _⟩, hB⟩, _⟩ := h
  exact suzL34RestrOK_spec hB

private theorem suzL34Words_spec :
    suzL34WordTab suzL34G1 = g₁T ∧ suzL34WordTab suzL34G2 = g₂T ∧
      suzL34WordTab suzL34G3 = g₃T := by
  have h := Certificates.certificate10741
  simp only [suzL34Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, _⟩, _⟩, hwords⟩ := h
  simp only [suzL34WordsOK, Bool.and_eq_true, beq_iff_eq] at hwords
  exact ⟨hwords.1.1, hwords.1.2, hwords.2⟩

private noncomputable def suzPhi (i : Fin 42) : Fin 1782 :=
  ⟨suzL34Pts[i.val]!, suzL34PtsOK_spec.2.1 i⟩

private theorem suzPhi_injective : Function.Injective suzPhi := by
  intro i j hij
  have hval : suzL34Pts[i.val]! = suzL34Pts[j.val]! := by
    simpa [suzPhi] using congrArg Fin.val hij
  have hsize : suzL34Pts.size = 42 := suzL34PtsOK_spec.1
  have hi : i.val < suzL34Pts.size := by rw [hsize]; exact i.isLt
  have hj : j.val < suzL34Pts.size := by rw [hsize]; exact j.isLt
  have hval' : suzL34Pts[i.val] = suzL34Pts[j.val] := by
    rwa [getElem!_pos suzL34Pts i.val hi, getElem!_pos suzL34Pts j.val hj] at hval
  have he : suzL34Pts.toList[i.val] = suzL34Pts.toList[j.val] := by
    simpa only [Array.getElem_toList] using hval'
  have hlen : suzL34Pts.toList.length = 42 := by
    rw [Array.length_toList, hsize]
  have hi' : i.val < suzL34Pts.toList.length := by rw [hlen]; exact i.isLt
  have hj' : j.val < suzL34Pts.toList.length := by rw [hlen]; exact j.isLt
  have hinj : Function.Injective (fun k : Fin suzL34Pts.toList.length =>
      suzL34Pts.toList[k.val]) :=
    List.nodup_iff_injective_getElem.mp (suzL34PtsOK_spec.2.2)
  exact Fin.ext (congrArg Fin.val (hinj he))

private noncomputable def suzPhiEquiv :
    Fin 42 ≃ Set.range suzPhi :=
  Equiv.ofInjective suzPhi suzPhi_injective

private noncomputable def suzTabAFun (i : Fin 42) : Fin 42 :=
  ⟨suzL34TA[i.val]!, (suzL34RestrA i).1⟩

private noncomputable def suzTabBFun (i : Fin 42) : Fin 42 :=
  ⟨suzL34TB[i.val]!, (suzL34RestrB i).1⟩

private theorem suzTabAFun_injective
    {a : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a) : Function.Injective suzTabAFun := by
  intro i j hij
  have htab : suzL34TA[i.val]! = suzL34TA[j.val]! := by
    simpa [suzTabAFun] using congrArg Fin.val hij
  have hpt : suzL34Pts[suzL34TA[i.val]!]! = suzL34Pts[suzL34TA[j.val]!]! := by rw [htab]
  have hAi := (suzL34RestrA i).2
  have hAj := (suzL34RestrA j).2
  have hAeq : suzArrA[suzL34Pts[i.val]!]! = suzArrA[suzL34Pts[j.val]!]! := by
    rw [← hAi, hpt, hAj]
  have hi : suzArrA[suzL34Pts[i.val]!]! = (a (suzPhi i) : Fin 1782) := by
    simpa [suzPhi] using ha (suzPhi i)
  have hj : suzArrA[suzL34Pts[j.val]!]! = (a (suzPhi j) : Fin 1782) := by
    simpa [suzPhi] using ha (suzPhi j)
  have hfin : a (suzPhi i) = a (suzPhi j) := by
    apply Fin.ext
    exact hi.symm.trans (hAeq.trans hj)
  exact suzPhi_injective (a.injective hfin)

private theorem suzTabBFun_injective
    {b : Equiv.Perm (Fin 1782)}
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b) : Function.Injective suzTabBFun := by
  intro i j hij
  have htab : suzL34TB[i.val]! = suzL34TB[j.val]! := by
    simpa [suzTabBFun] using congrArg Fin.val hij
  have hpt : suzL34Pts[suzL34TB[i.val]!]! = suzL34Pts[suzL34TB[j.val]!]! := by rw [htab]
  have hBi := (suzL34RestrB i).2
  have hBj := (suzL34RestrB j).2
  have hBeq : suzArrB[suzL34Pts[i.val]!]! = suzArrB[suzL34Pts[j.val]!]! := by
    rw [← hBi, hpt, hBj]
  have hi : suzArrB[suzL34Pts[i.val]!]! = (b (suzPhi i) : Fin 1782) := by
    simpa [suzPhi] using hb (suzPhi i)
  have hj : suzArrB[suzL34Pts[j.val]!]! = (b (suzPhi j) : Fin 1782) := by
    simpa [suzPhi] using hb (suzPhi j)
  have hfin : b (suzPhi i) = b (suzPhi j) := by
    apply Fin.ext
    exact hi.symm.trans (hBeq.trans hj)
  exact suzPhi_injective (b.injective hfin)

private noncomputable def suzSigmaA
    {a : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a) : Equiv.Perm (Fin 42) :=
  Equiv.ofBijective suzTabAFun (Finite.injective_iff_bijective.mp (suzTabAFun_injective ha))

private noncomputable def suzSigmaB
    {b : Equiv.Perm (Fin 1782)}
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b) : Equiv.Perm (Fin 42) :=
  Equiv.ofBijective suzTabBFun (Finite.injective_iff_bijective.mp (suzTabBFun_injective hb))

private theorem suzSigmaA_tabRep
    {a : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a) :
    TabRep suzL34TA (suzSigmaA ha) := by
  refine ⟨?_, fun i => ?_⟩
  · simp [suzL34TA]
  · simp [suzSigmaA, suzTabAFun, Equiv.ofBijective_apply]

private theorem suzSigmaB_tabRep
    {b : Equiv.Perm (Fin 1782)}
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b) :
    TabRep suzL34TB (suzSigmaB hb) := by
  refine ⟨?_, fun i => ?_⟩
  · simp [suzL34TB]
  · simp [suzSigmaB, suzTabBFun, Equiv.ofBijective_apply]

private theorem suzPhi_a
    {a : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a) (i : Fin 42) :
    a (suzPhi i) = suzPhi (suzSigmaA ha i) := by
  apply Fin.ext
  have hrep : suzArrA[suzL34Pts[i.val]!]! = a (suzPhi i) := by
    simpa [suzPhi] using ha (suzPhi i)
  have hrestr := (suzL34RestrA i).2
  have hval : (suzSigmaA ha i).val = suzL34TA[i.val]! := by
    simp [suzSigmaA, suzTabAFun, Equiv.ofBijective_apply]
  change (a (suzPhi i)).val = (suzPhi (suzSigmaA ha i)).val
  rw [show (suzPhi (suzSigmaA ha i)).val = suzL34Pts[suzL34TA[i.val]!]! by
    simp [suzPhi, hval]]
  exact hrep.symm.trans hrestr.symm

private theorem suzPhi_b
    {b : Equiv.Perm (Fin 1782)}
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b) (i : Fin 42) :
    b (suzPhi i) = suzPhi (suzSigmaB hb i) := by
  apply Fin.ext
  have hrep : suzArrB[suzL34Pts[i.val]!]! = b (suzPhi i) := by
    simpa [suzPhi] using hb (suzPhi i)
  have hrestr := (suzL34RestrB i).2
  have hval : (suzSigmaB hb i).val = suzL34TB[i.val]! := by
    simp [suzSigmaB, suzTabBFun, Equiv.ofBijective_apply]
  change (b (suzPhi i)).val = (suzPhi (suzSigmaB hb i)).val
  rw [show (suzPhi (suzSigmaB hb i)).val = suzL34Pts[suzL34TB[i.val]!]! by
    simp [suzPhi, hval]]
  exact hrep.symm.trans hrestr.symm

private theorem suzMapsTo_closure
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b) :
    ∀ k : Equiv.Perm (Fin 1782), k ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 1782))) →
      Set.MapsTo k (Set.range suzPhi) (Set.range suzPhi) ∧
        Set.MapsTo (k⁻¹ : Equiv.Perm (Fin 1782)) (Set.range suzPhi) (Set.range suzPhi) := by
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · subst x
        refine ⟨?_, ?_⟩
        · rintro _ ⟨i, rfl⟩
          exact ⟨suzSigmaA ha i, (suzPhi_a ha i).symm⟩
        · rintro _ ⟨i, rfl⟩
          refine ⟨(suzSigmaA ha).symm i, ?_⟩
          have h := suzPhi_a ha ((suzSigmaA ha).symm i)
          have h' : a (suzPhi ((suzSigmaA ha).symm i)) = suzPhi i := by
            simpa using h
          have hsymm : suzPhi ((suzSigmaA ha).symm i) = a.symm (suzPhi i) := by
            simpa using congrArg a.symm h'
          exact hsymm
      · subst x
        refine ⟨?_, ?_⟩
        · rintro _ ⟨i, rfl⟩
          exact ⟨suzSigmaB hb i, (suzPhi_b hb i).symm⟩
        · rintro _ ⟨i, rfl⟩
          refine ⟨(suzSigmaB hb).symm i, ?_⟩
          have h := suzPhi_b hb ((suzSigmaB hb).symm i)
          have h' : b (suzPhi ((suzSigmaB hb).symm i)) = suzPhi i := by
            simpa using h
          have hsymm : suzPhi ((suzSigmaB hb).symm i) = b.symm (suzPhi i) := by
            simpa using congrArg b.symm h'
          exact hsymm
  | one =>
      refine ⟨?_, ?_⟩ <;> intro x hx <;> simpa using hx
  | mul x y _ _ hx hy =>
      refine ⟨?_, ?_⟩
      · intro z hz
        exact hx.1 (hy.1 hz)
      · intro z hz
        exact hy.2 (hx.2 hz)
  | inv x _ hx =>
      refine ⟨hx.2, ?_⟩
      simpa using hx.1

private theorem suzSubtypeMapTo
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b)
    (k : ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 1782))))) :
    ∀ x : Fin 1782, k.val x ∈ Set.range suzPhi ↔ x ∈ Set.range suzPhi := by
  intro x
  constructor
  · intro hx
    have := (suzMapsTo_closure ha hb k.val k.2).2 hx
    simpa using this
  · intro hx
    exact (suzMapsTo_closure ha hb k.val k.2).1 hx

private noncomputable def suzRPerm
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b)
    (k : ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 1782))))) :
    Equiv.Perm (Set.range suzPhi) :=
  k.val.subtypePerm (suzSubtypeMapTo ha hb k)

private noncomputable def suzR
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b) :
    ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 1782)))) →* Equiv.Perm (Fin 42) where
  toFun k := (suzPhiEquiv.trans (suzRPerm ha hb k)).trans suzPhiEquiv.symm
  map_one' := by
    ext i
    simp [suzRPerm]
  map_mul' k l := by
    ext i
    simp [suzRPerm]

private theorem suzR_a
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b) :
    suzR ha hb ⟨a, Subgroup.subset_closure (by simp)⟩ = suzSigmaA ha := by
  ext i
  apply congrArg Fin.val
  apply suzPhiEquiv.injective
  apply Subtype.ext
  simp [suzR, suzRPerm, suzPhiEquiv, Equiv.Perm.subtypePerm_apply]
  exact suzPhi_a ha i

private theorem suzR_b
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b) :
    suzR ha hb ⟨b, Subgroup.subset_closure (by simp)⟩ = suzSigmaB hb := by
  ext i
  apply congrArg Fin.val
  apply suzPhiEquiv.injective
  apply Subtype.ext
  simp [suzR, suzRPerm, suzPhiEquiv, Equiv.Perm.subtypePerm_apply]
  exact suzPhi_b hb i

private noncomputable def suzSigmaGen
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b)
    (l : Nat) : Equiv.Perm (Fin 42) :=
  if l = 1 then suzSigmaA ha else suzSigmaB hb

private noncomputable def suzSigmaWord
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b) :
    List Nat → Equiv.Perm (Fin 42)
  | [] => 1
  | l :: w => suzSigmaGen ha hb l * suzSigmaWord ha hb w

private theorem suzL34GenTab_tabRep
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b)
    (l : Nat) : TabRep (suzL34GenTab l) (suzSigmaGen ha hb l) := by
  by_cases hl : l = 1
  · simp only [suzL34GenTab, suzSigmaGen, hl, if_true]
    exact suzSigmaA_tabRep ha
  · simp only [suzL34GenTab, suzSigmaGen, hl, if_false]
    exact suzSigmaB_tabRep hb

private theorem suzL34WordTab_tabRep
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b)
    (w : List Nat) (acc : Array Nat) (g : Equiv.Perm (Fin 42)) (hacc : TabRep acc g) :
    TabRep (w.foldl (fun acc l => comp 42 acc (suzL34GenTab l)) acc)
      (g * suzSigmaWord ha hb w) := by
  induction w generalizing acc g with
  | nil => simpa [suzSigmaWord] using hacc
  | cons l w ih =>
      simp only [List.foldl_cons, suzSigmaWord]
      have h := ih (comp 42 acc (suzL34GenTab l)) (g * suzSigmaGen ha hb l)
        (hacc.comp (suzL34GenTab_tabRep ha hb l))
      simpa only [mul_assoc] using h

private theorem suzL34WordTab_tabRep'
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b)
    (w : List Nat) : TabRep (suzL34WordTab w) (suzSigmaWord ha hb w) := by
  have h := suzL34WordTab_tabRep ha hb w (idTab 42) 1 TabRep.idTab
  simpa only [suzL34WordTab, one_mul] using h

private theorem suzSigmaWord_mem
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b)
    (w : List Nat) :
    suzSigmaWord ha hb w ∈
      Subgroup.closure ({suzSigmaA ha, suzSigmaB hb} : Set (Equiv.Perm (Fin 42))) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons l w ih =>
      simp only [suzSigmaWord]
      refine Subgroup.mul_mem _ ?_ ih
      by_cases hl : l = 1
      · simp only [suzSigmaGen, hl, if_true]
        exact Subgroup.subset_closure (by simp)
      · simp only [suzSigmaGen, hl, if_false]
        exact Subgroup.subset_closure (by simp)

private theorem suzG_mem_closure
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b) :
    g₁ ∈ Subgroup.closure ({suzSigmaA ha, suzSigmaB hb} : Set (Equiv.Perm (Fin 42))) ∧
      g₂ ∈ Subgroup.closure ({suzSigmaA ha, suzSigmaB hb} : Set (Equiv.Perm (Fin 42))) ∧
      g₃ ∈ Subgroup.closure ({suzSigmaA ha, suzSigmaB hb} : Set (Equiv.Perm (Fin 42))) := by
  obtain ⟨h1, h2, h3⟩ := suzL34Words_spec
  have hrep1 : TabRep g₁T (suzSigmaWord ha hb suzL34G1) := by
    rw [← h1]
    exact suzL34WordTab_tabRep' ha hb _
  have hrep2 : TabRep g₂T (suzSigmaWord ha hb suzL34G2) := by
    rw [← h2]
    exact suzL34WordTab_tabRep' ha hb _
  have hrep3 : TabRep g₃T (suzSigmaWord ha hb suzL34G3) := by
    rw [← h3]
    exact suzL34WordTab_tabRep' ha hb _
  refine ⟨?_, ?_, ?_⟩
  · rw [tabRep_g₁.perm_eq hrep1]
    exact suzSigmaWord_mem ha hb _
  · rw [tabRep_g₂.perm_eq hrep2]
    exact suzSigmaWord_mem ha hb _
  · rw [tabRep_g₃.perm_eq hrep3]
    exact suzSigmaWord_mem ha hb _

private theorem suzS_le_suzR_range
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b) :
    S ≤ (suzR ha hb).range := by
  have hclos : Subgroup.closure ({suzSigmaA ha, suzSigmaB hb} :
      Set (Equiv.Perm (Fin 42))) ≤ (suzR ha hb).range := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨⟨a, Subgroup.subset_closure (by simp)⟩, suzR_a ha hb⟩
    · exact ⟨⟨b, Subgroup.subset_closure (by simp)⟩, suzR_b ha hb⟩
  rw [S, Subgroup.closure_le]
  intro x hx
  have hmem := suzG_mem_closure ha hb
  rcases hx with rfl | rfl | rfl
  · exact hclos hmem.1
  · exact hclos hmem.2.1
  · exact hclos hmem.2.2

private theorem suzR_card_range
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b)
    (hcard : Nat.card ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 1782)))) = 20160) :
    Nat.card ↥(suzR ha hb).range = 20160 := by
  have hSle := suzS_le_suzR_range ha hb
  have hS : Nat.card ↥S = 20160 := card_S
  have hdvd := Subgroup.card_range_dvd (suzR ha hb)
  rw [hcard] at hdvd
  refine le_antisymm ?_ ?_
  · exact Nat.le_of_dvd (by norm_num) hdvd
  · calc 20160 = Nat.card ↥S := hS.symm
      _ ≤ Nat.card ↥(suzR ha hb).range := Subgroup.card_le_of_le hSle

private theorem suzR_injective
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b)
    (hcard : Nat.card ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 1782)))) = 20160) :
    Function.Injective (suzR ha hb) := by
  have hrange := suzR_card_range ha hb hcard
  have hker : Nat.card ↥(suzR ha hb).ker = 1 := by
    have hmul := Subgroup.card_ker_mul_card_range (suzR ha hb)
    rw [hrange, hcard] at hmul
    omega
  exact (MonoidHom.ker_eq_bot_iff (suzR ha hb)).mp (Subgroup.card_eq_one.mp hker)

theorem nonempty_mulEquiv_S_of_rep
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b)
    (hcard : Nat.card ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 1782)))) = 20160) :
    Nonempty (↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 1782)))) ≃*
      ↥CFSG.ComponentClassification.PSL3Four.S) := by
  have hinj := suzR_injective ha hb hcard
  have hrange : S = (suzR ha hb).range := by
    apply Subgroup.eq_of_le_of_card_ge (suzS_le_suzR_range ha hb)
    rw [suzR_card_range ha hb hcard, card_S]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange).symm⟩

theorem lieModel_closure_of_rep
    {a b : Equiv.Perm (Fin 1782)}
    (ha : CFSG.Monster.B.Co2.Rep 1782 suzArrA a)
    (hb : CFSG.Monster.B.Co2.Rep 1782 suzArrB b)
    (hcard : Nat.card ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 1782)))) = 20160) :
    CFSG.Blueprint.LieModel ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin 1782))))
      .PSL 3 2 2 := by
  obtain ⟨eKS⟩ := nonempty_mulEquiv_S_of_rep ha hb hcard
  have hst : CFSG.Open.StatedClassicalModel
      (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 2)) .PSL 3 2 2 :=
    ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, GaloisField 2 2,
      inferInstance, inferInstance, GaloisField.card 2 2 (by norm_num),
      ⟨CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3
        (GaloisField 2 2)⟩⟩
  obtain ⟨ePSL⟩ := CFSG.ComponentClassification.PSL3Four.nonempty_equiv_of_stated
    (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 2)) hst
  exact CFSG.Blueprint.LieModel.of_mulEquiv (eKS.trans ePSL.symm).symm
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_three_four_lieModel

end CFSG.EvenSporadicStandard.Solomon78
