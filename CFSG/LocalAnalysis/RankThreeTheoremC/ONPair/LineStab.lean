module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.Model
public import CFSG.Sporadic.ONOddCore.Prim
public import CFSG.Sporadic.ONOddCore.FaithfulProj
public import CFSG.Sporadic.HNSchreier.StrongSpec
public import Certificates.Certificate753503
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.Sporadic.ONOddCore.PrimBase
public import CFSG.Sporadic.ONOddCore.TreeOrbit
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON CFSG.Sporadic.ONOddCore
  CFSG.Sporadic.ON.Native CFSG.RankThree.Native
open CFSG.Sporadic.HNSchreier (gStrong gStrong_of_lt gStrong_of_ge map_gStrong)
open scoped commutatorElement

theorem wordStrong_eq_gStrong {n : ℕ} (orig : List (Equiv.Perm (Fin n))) (W : Array (List ℤ)) :
    ∀ j, wordStrong orig W j = gStrong orig W j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < orig.length
    · rw [wordStrong_of_lt _ _ hj, gStrong_of_lt _ _ hj]
    · rw [wordStrong_of_ge _ _ (by omega), gStrong_of_ge _ _ (by omega)]
      congr 1
      funext h
      exact ih h.val h.isLt

theorem ptoLetters_h1Word :
    ptoLetters 7 h1Word = [((1 : Fin 7), false), ((0 : Fin 7), true), ((1 : Fin 7), true)] := by
  decide

theorem ptoLetters_h2Word :
    ptoLetters 7 h2Word = [((1 : Fin 7), false), ((1 : Fin 7), false), ((0 : Fin 7), false),
      ((1 : Fin 7), false), ((1 : Fin 7), false), ((0 : Fin 7), false), ((1 : Fin 7), true),
      ((0 : Fin 7), true), ((1 : Fin 7), true), ((1 : Fin 7), true), ((0 : Fin 7), true),
      ((1 : Fin 7), true), ((1 : Fin 7), true)] := by
  decide

section Strong

@[expose] noncomputable def pvS (h : ℕ) : Pv := ⟨sgen h, sgen_mem h⟩

@[expose] noncomputable def pvEval (w : List ℤ) : Pv := ⟨evalS w, evalS_mem w⟩

theorem pvEval_eq (w : List ℤ) :
    pvEval w = Quiver.SchreierGraph.evalWord (fun h : Fin 7 => pvS h) (ptoLetters 7 w) := by
  apply Subtype.ext
  show evalS w = Pv.subtype (Quiver.SchreierGraph.evalWord (fun h : Fin 7 => pvS h) _)
  rw [map_evalWord]
  rfl

theorem pvS_zero : pvS 0 = ⟨a0, a0_mem⟩ :=
  Subtype.ext cert_on_schreier_action_data.2.2.2.2.2.1

theorem pvS_one : pvS 1 = ⟨a1, a1_mem⟩ :=
  Subtype.ext cert_on_schreier_action_data.2.2.2.2.2.2.1

theorem pvS_eq_gStrong (j : ℕ) :
    pvS j = gStrong [(⟨a0, a0_mem⟩ : Pv), ⟨a1, a1_mem⟩] Data.strongWords j := by
  apply Subtype.ext
  show sgen j = Pv.subtype (gStrong _ _ j)
  rw [map_gStrong, sgen, wordStrong_eq_gStrong]
  rfl

theorem map_pvS {G : Type*} [Group G] (φ : Pv →* G) (j : ℕ) :
    φ (pvS j) = gStrong [φ ⟨a0, a0_mem⟩, φ ⟨a1, a1_mem⟩] Data.strongWords j := by
  rw [pvS_eq_gStrong, map_gStrong]
  rfl

theorem map_pvEval {G : Type*} [Group G] (φ : Pv →* G) (w : List ℤ) :
    φ (pvEval w) = Quiver.SchreierGraph.evalWord
      (fun h : Fin 7 => gStrong [φ ⟨a0, a0_mem⟩, φ ⟨a1, a1_mem⟩] Data.strongWords h)
      (ptoLetters 7 w) := by
  rw [pvEval_eq, map_evalWord]
  congr 1
  funext h
  exact map_pvS φ h

@[expose] noncomputable def hgenP (h : ℕ) : Pv := ⟨hgen h, hgen_mem h⟩

theorem hP_eq (w : List ℤ) : (⟨hval w, hval_mem w⟩ : Pv) =
    Quiver.SchreierGraph.evalWord (fun h : Fin 2 => hgenP h) (ptoLetters 2 w) := by
  apply Subtype.ext
  show hval w = Pv.subtype (Quiver.SchreierGraph.evalWord (fun h : Fin 2 => hgenP h) _)
  rw [map_evalWord]
  rfl

theorem gStrong_d_zero : gStrong [d0, d1] Data.strongWords 0 = d0 :=
  gStrong_of_lt _ _ (by simp)

theorem gStrong_d_one : gStrong [d0, d1] Data.strongWords 1 = d1 :=
  gStrong_of_lt _ _ (by simp)

end Strong

section Line

@[expose] noncomputable def pvEquivPl : Pv ≃* Pl := jEquivPv.symm.trans jEquivPl

@[expose] noncomputable def lineAct : Pv →* Equiv.Perm (Fin nL) :=
  Pl.subtype.comp (pvEquivPl : Pv →* Pl)

theorem lineAct_apply (g : Pv) : lineAct g = (pvEquivPl g : Equiv.Perm (Fin nL)) := rfl

theorem lineAct_jEquivPv (g : J) : lineAct (jEquivPv g) = phiL g := by
  rw [lineAct_apply, pvEquivPl, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, jEquivPl_apply]

theorem lineAct_a0 : lineAct ⟨a0, a0_mem⟩ = d0 := by
  rw [show (⟨a0, a0_mem⟩ : Pv) = jEquivPv ga from Subtype.ext phiV_ga.symm, lineAct_jEquivPv,
    phiL_ga]

theorem lineAct_a1 : lineAct ⟨a1, a1_mem⟩ = d1 := by
  rw [show (⟨a1, a1_mem⟩ : Pv) = jEquivPv gb from Subtype.ext phiV_gb.symm, lineAct_jEquivPv,
    phiL_gb]

theorem lineAct_pvEval (w : List ℤ) :
    lineAct (pvEval w) = Quiver.SchreierGraph.evalWord
      (fun h : Fin 7 => gStrong [d0, d1] Data.strongWords h) (ptoLetters 7 w) := by
  rw [map_pvEval, lineAct_a0, lineAct_a1]

@[expose] noncomputable def lineStab (ℓ : Fin nL) : Subgroup Pv :=
  (MulAction.stabilizer Pl ℓ).comap (pvEquivPl : Pv →* Pl)

theorem mem_lineStab {ℓ : Fin nL} {g : Pv} : g ∈ lineStab ℓ ↔ lineAct g ℓ = ℓ :=
  Iff.rfl

@[expose] noncomputable def M1 : Subgroup Pv := lineStab 0

theorem mem_M1 {g : Pv} : g ∈ M1 ↔ lineAct g 0 = 0 := Iff.rfl

theorem lineStab_smul (g : Pv) (ℓ : Fin nL) :
    lineStab (lineAct g ℓ) = (lineStab ℓ).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_lineStab, Subgroup.mem_map_equiv, mem_lineStab, MulAut.conj_symm_apply, map_mul,
    map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]

theorem lineAct_hgenP_zero : lineAct (hgenP 0) = lineRegs 1 := by
  have e : hgenP 0 = pvEval h1Word := Subtype.ext hgen_zero
  rw [e, lineAct_pvEval, ptoLetters_h1Word, lineRegs_one]
  simp only [Quiver.SchreierGraph.evalWord_cons_true, Quiver.SchreierGraph.evalWord_cons_false,
    Quiver.SchreierGraph.evalWord_nil, Fin.val_zero, Fin.val_one, gStrong_d_zero, gStrong_d_one]
  group

theorem lineAct_hgenP_one : lineAct (hgenP 1) = lineRegs 2 := by
  have e : hgenP 1 = pvEval h2Word := Subtype.ext hgen_one
  rw [e, lineAct_pvEval, ptoLetters_h2Word, lineRegs_two]
  simp only [Quiver.SchreierGraph.evalWord_cons_true, Quiver.SchreierGraph.evalWord_cons_false,
    Quiver.SchreierGraph.evalWord_nil, Fin.val_zero, Fin.val_one, gStrong_d_zero, gStrong_d_one]
  group

section Order

theorem card_stabilizer_Pl_eq (ℓ : Fin nL) :
    Nat.card (MulAction.stabilizer Pl ℓ) = 3753792 := by
  have h := (MulAction.stabilizer Pl ℓ).card_mul_index
  have hi : (MulAction.stabilizer Pl ℓ).index = 122760 := by
    rw [MulAction.index_stabilizer_of_transitive, Nat.card_fin]
  rw [hi, card_Pl] at h
  omega

theorem card_lineStab (ℓ : Fin nL) : Nat.card (lineStab ℓ) = 3753792 := by
  rw [lineStab, Subgroup.comap_equiv_eq_map_symm,
    Subgroup.card_map_of_injective pvEquivPl.symm.injective, card_stabilizer_Pl_eq]

theorem card_M1 : Nat.card M1 = 3753792 := card_lineStab 0

end Order

section Fix

theorem isCoatom_lineStab (ℓ : Fin nL) : IsCoatom (lineStab ℓ) := by
  haveI := pl_preprimitive
  haveI : Nontrivial (Fin nL) := Fin.nontrivial_iff_two_le.2 (by norm_num)
  rw [lineStab, Subgroup.isCoatom_comap]
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive Pl ℓ

theorem hgenP_mem_M1 (h : Fin 2) : hgenP h ∈ M1 := by
  rw [mem_M1]
  fin_cases h
  · show lineAct (hgenP 0) 0 = 0
    rw [lineAct_hgenP_zero]
    exact lineSubgroup_fix_zero _ (Subgroup.subset_closure (Set.mem_insert _ _))
  · show lineAct (hgenP 1) 0 = 0
    rw [lineAct_hgenP_one]
    exact lineSubgroup_fix_zero _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem hP_mem_M1 (w : List ℤ) : (⟨hval w, hval_mem w⟩ : Pv) ∈ M1 := by
  rw [hP_eq]
  exact evalWord_mem (fun h => hgenP_mem_M1 h) _

theorem qP_mem_M1 (i : Fin 4) : qP i ∈ M1 := hP_mem_M1 _

theorem tOut_mem_M1 : tOut ∈ M1 := hP_mem_M1 _

theorem Q0_le_M1 : Q0 ≤ M1 := by
  rw [Q0_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact qP_mem_M1 i

theorem card_M1_eq_two_mul : Nat.card M1 = 2 * Nat.card Q0 := by
  rw [card_M1, card_Q0]

theorem index_Q0_M1 : (Q0.subgroupOf M1).index = 2 := by
  have h := (Q0.subgroupOf M1).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q0_le_M1).toEquiv, card_M1, card_Q0] at h
  omega

instance normal_Q0_M1 : (Q0.subgroupOf M1).Normal :=
  Subgroup.normal_of_index_eq_two index_Q0_M1

end Fix

end Line

section Mflat

@[expose] noncomputable def Mflat : Subgroup Pv := Subgroup.closure {qP 0, qP 1, qP 2, tOut}

theorem qtGen_mem_Mflat (h : Fin 4) : qtGen h ∈ Mflat := by
  fin_cases h
  · exact Subgroup.subset_closure (by simp [qtGen])
  · exact Subgroup.subset_closure (by simp [qtGen])
  · exact Subgroup.subset_closure (by simp [qtGen])
  · exact Subgroup.subset_closure (by simp [qtGen])

theorem tOut_mem_Mflat : tOut ∈ Mflat := Subgroup.subset_closure (by simp)

theorem qP_three_eq : qP 3 = Quiver.SchreierGraph.evalWord (fun h : Fin 4 => qtGen h)
    (ptoLetters 4 q4Word) :=
  Certificates.certificate753503.1

theorem qP_mem_Mflat (i : Fin 4) : qP i ∈ Mflat := by
  fin_cases i
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · show qP 3 ∈ Mflat
    rw [qP_three_eq]
    exact evalWord_mem (fun h => qtGen_mem_Mflat h) _

theorem tOut_apply_ne : (tOut : Equiv.Perm (Fin N)) 0 ≠ 0 :=
  Certificates.certificate753503.2.1

theorem tOut_conj_b1 : tOut * b1P * tOut⁻¹ = b1P ^ 4 :=
  Certificates.certificate753503.2.2

theorem Q0_le_Mflat : Q0 ≤ Mflat := by
  rw [Q0_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact qP_mem_Mflat i

theorem tOut_not_mem_Q0 : tOut ∉ Q0 := fun h => tOut_apply_ne (Q0_le_stab tOut h)

theorem Mflat_le_M1 : Mflat ≤ M1 := by
  rw [Mflat, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl)
  · exact qP_mem_M1 0
  · exact qP_mem_M1 1
  · exact qP_mem_M1 2
  · exact tOut_mem_M1

theorem Mflat_eq_M1 : Mflat = M1 := by
  have h1 : Nat.card Q0 ∣ Nat.card Mflat := Subgroup.card_dvd_of_le Q0_le_Mflat
  have h2 : Nat.card Mflat ∣ Nat.card M1 := Subgroup.card_dvd_of_le Mflat_le_M1
  obtain ⟨k, hk⟩ := h1
  rw [card_M1_eq_two_mul, hk] at h2
  have hQ : 0 < Nat.card Q0 := by rw [card_Q0]; norm_num
  have hk2 : k ∣ 2 := (Nat.mul_dvd_mul_iff_left hQ).1 (by simpa [mul_comm] using h2)
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    have : Q0 = Mflat := Subgroup.eq_of_le_of_card_ge Q0_le_Mflat hk.le
    exact tOut_not_mem_Q0 (this ▸ tOut_mem_Mflat)
  have hk2' : k = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with h | h
    · exact absurd h hk1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge Mflat_le_M1 ?_
  rw [card_M1_eq_two_mul, hk, hk2', mul_comm]

end Mflat

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
