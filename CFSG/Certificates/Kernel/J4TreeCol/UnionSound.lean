module

public import CFSG.Certificates.Kernel.J4TreeCol.NodeSound
public import Certificates.Data.Kernel.J4TreeColUnion

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.J4TreeCol

open CFSG.KC.J4TreeN CFSG.KC.J4Tree CFSG.KC.J4Q CFSG.KC.Loop CFSG.J4Tree.Native
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.ASVolI

section Sound


theorem colUnion_sound {G : Mats} {T : Tabs} {D : CRec} (hG : MatsOK G) (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false)
    (h : colUnionOK T D = true)
    (hpair : D.mode = 1 → ∀ a b, a ≤ b → b < 2 ^ (treeWv D.k).length →
      fld D.qp 7 (pIdx (2 ^ (treeWv D.k).length) a b) +
        gRank G (pairP G (packMs (matsOf G (treeWv D.k))) a b) = 112) :
    Subgroup.normalizer (burnsideJ4NP_Wv D.k : Set J) ≤
      Subgroup.normalizer ((Subgroup.closure
        ((fun o => eta (burnsideJ4NP_colBasis D.k) (treeWv D.k).length o) ''
          {o | o ∈ bitsOf D.om (2 ^ (treeWv D.k).length)}) : Subgroup J) : Set J) := by
  classical
  unfold colUnionOK at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, hco⟩, hBc⟩, hmode⟩, hlabs⟩, hun⟩ := h
  have hbv : burnsideJ4NP_colBasis D.k = bvOf (treeWv D.k) := rfl
  rw [burnsideJ4NP_col_Wv_eq_Eg, hbv]
  generalize hwv : treeWv D.k = wv at hco hBc hlabs hun hpair
  set r := wv.length with hr
  set bv := bvOf wv with hbvdef
  have hE : Elem bv r := elem_of_codes hT hco hBc
  obtain ⟨hClen, hC⟩ := codes_spec hT hco
  have hlab' : ∀ m < 2 ^ r, labJ (eta bv r m) = labC D m ∧ (labC D m = 0 ↔ m = 0) := by
    intro m hm
    unfold labsOK at hlabs
    have hm' : m < ((codesOf (wv.map (ccT T))).zipIdx).length := by
      rw [List.length_zipIdx, hClen]
      exact hm
    have h1 := List.all_eq_true.1 hlabs _ (List.getElem_mem hm')
    rw [List.getElem_zipIdx, Nat.zero_add, ← List.getD_eq_getElem _ oneK] at h1
    exact labOK_spec h1 (hC m hm) (eta_sq hE m) hsx
  have hlab : ∀ m < 2 ^ r, labJ (eta bv r m) = labC D m := fun m hm => (hlab' m hm).1
  have hlab1 : labJ 1 = 0 := by
    unfold labJ
    rw [if_pos rfl]
  have hinj : ∀ i < 2 ^ r, ∀ j < 2 ^ r, eta bv r i = eta bv r j → i = j := by
    intro i hi j hj e
    have hx : i ^^^ j < 2 ^ r := Nat.xor_lt_two_pow hi hj
    have h1 : eta bv r (i ^^^ j) = 1 := by rw [eta_xor hE le_rfl, e, eta_sq hE]
    have h2 := hlab' _ hx
    rw [h1, hlab1] at h2
    exact burnsideJ4NP_col_eq_of_xor_eq_zero (h2.2.1 h2.1.symm)
  obtain ⟨q, hqc, hqn⟩ : ∃ q : J → J → ℕ, (∀ g x w : J, q (g * x * g⁻¹) (g * w * g⁻¹) = q x w) ∧
      ∀ i < 2 ^ r, ∀ j < 2 ^ r, q (eta bv r i) (eta bv r j) = qC D (2 ^ r) i j := by
    by_cases hm0 : D.mode = 0
    · refine ⟨qProd, qProd_conj, fun i hi j hj => ?_⟩
      unfold qC qProd
      rw [if_pos hm0, ← eta_xor hE le_rfl]
      exact hlab _ (Nat.xor_lt_two_pow hi hj)
    · have hm1 : D.mode = 1 := by
        have := Nat.le_of_ble_eq_true hmode
        omega
      refine ⟨burnsideJ4NP_colPair, burnsideJ4NP_colPair_conj, fun i hi j hj => ?_⟩
      unfold qC
      rw [if_neg hm0]
      split_ifs with hij
      · exact (pairP_label hG hE hi hj (hpair hm1 i j hij hj)).symm
      · rw [colPair_symm (eta_comm hE i j)]
        exact (pairP_label hG hE hj hi (hpair hm1 j i (by omega) hi)).symm
  have hsig : ∀ {i y : ℕ}, i < 2 ^ r → y < 2 ^ r →
      (∀ a b, burnsideJ4NP_colCount (Eg bv r) labJ q (eta bv r i) a b =
        burnsideJ4NP_colCount (Eg bv r) labJ q (eta bv r y) a b) →
      sigC D (2 ^ r) i = sigC D (2 ^ r) y :=
    fun hi hy hc => sig_eq_of_counts hinj hE q hlab hqn hi hy hc
  unfold unionOK at hun
  dsimp only at hun
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne,
    ne_eq, Bool.not_eq_true'] at hun
  obtain ⟨-, hall⟩ := hun
  set oL := bitsOf D.om (2 ^ r) with hoLdef
  have hoL : ∀ o, o ∈ oL ↔ o < 2 ^ r ∧ D.om.testBit o = true := by
    intro o
    rw [hoLdef, bitsOf, List.mem_filter, List.mem_range]
  have hOW : (fun o => eta bv r o) '' {o | o ∈ oL} ⊆ Eg bv r := by
    rintro _ ⟨o, -, rfl⟩
    exact eta_mem_Eg r le_rfl o
  refine burnsideJ4NP_normalizer_le_of_colUnion (Eg bv r) labJ q labJ_conj hqc hOW ?_
  intro x hx o' ho' hl hc
  obtain ⟨i, hi, rfl⟩ := (mem_Eg_iff hE).1 hx
  obtain ⟨o, ho, rfl⟩ := ho'
  have hon := ((hoL o).1 ho).1
  rcases hall i hi with hb | hall'
  · exact ⟨i, (hoL i).2 ⟨hi, hb⟩, rfl⟩
  · exfalso
    rcases hall' _ (List.mem_map.2 ⟨o, ho, rfl⟩) with h1 | h1
    · exact h1 (by rw [← hlab o hon, ← hl, hlab i hi])
    · exact h1 (hsig hon hi fun a b => (hc a b).symm)

end Sound

end CFSG.KC.J4TreeCol

end
