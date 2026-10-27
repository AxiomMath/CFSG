
module

public import CFSG.HardMathSupport.Foote.E27.SporFi22Base

public import CFSG.HardMathSupport.Foote.E27.TableSylow
public import CFSG.HardMathSupport.Foote.E27.TableMat
public import CFSG.HardMathSupport.Foote.E27.SporSylowBound
public import CFSG.HardMathSupport.Foote.E27.SporKill
public import Certificates.Certificate131101

public section

namespace CFSG.HardMathSupport.Foote.E27.Fi22S0

open CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.S0 CFSG.Sporadic.Fi22.Native CFSG.F3.Native
  CFSG.HardMathSupport.Foote.E27 Subgroup

section Certificates

theorem fi22S0Check_parts :
    shapeOK = true ∧ killOK = true ∧ canonOK = true ∧ leftOK = true ∧ distinctOK = true := by
  have h := Certificates.certificate131101
  unfold fi22S0Check at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem shape_parts :
    (∀ t < ops.size, (ops[t]!).1 < t + 3 ∧ (ops[t]!).2 < t + 3) ∧
    (∀ j < gens.size, gens[j]! < ops.size + 3) ∧ ops.size = 567 ∧ gens.size = 3 ∧ par.size = nS ∧
    (∀ i < nS, i = 0 ∨ ((par[i]!).1 < i ∧ (par[i]!).2 < 3)) := by
  have h := fi22S0Check_parts.1
  unfold shapeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨fun t ht => h5 t ht, fun j hj => h6 j hj, h1, h2, h3, fun i hi => h7 i hi⟩

theorem regs_spec :
    regsM.size = 3 + ops.size ∧ ∀ k < 3 + ops.size, (regsM[k]!).size = 77 ∧ RowsWF (regsM[k]!) ∧
      toMat 77 (regsM[k]!) = matJ (regJ k) := by
  obtain ⟨hops, -, -, -, -, -⟩ := shape_parts
  have h := buildN_inv (#[matA, matB, matBi] : Array (Array V))
    (fun acc k => mul 77 (acc[(ops[k - 3]!).1]!) (acc[(ops[k - 3]!).2]!))
    (fun k x => x.size = 77 ∧ RowsWF x ∧ toMat 77 x = matJ (regJ k)) ops.size ?_ ?_
  · exact h
  · intro k hk
    have hk3 : k < 3 := hk
    interval_cases k
    · refine ⟨matA_size, rowsWF_matA, ?_⟩
      show toMat 77 matA = matJ (regJ 0)
      rw [regJ_zero, toMat_matA]; rfl
    · refine ⟨matB_size, rowsWF_matB, ?_⟩
      show toMat 77 matB = matJ (regJ 1)
      rw [regJ_one, toMat_matB]; rfl
    · refine ⟨matBi_size, rowsWF_matBi, ?_⟩
      show toMat 77 matBi = matJ (regJ 2)
      rw [regJ_two]; exact b_inv_val.symm
  · intro n hn r hr hP
    have hrs : r.size = 3 + n := hr
    obtain ⟨hp1, hp2⟩ := hops n hn
    have e : r.size - 3 = n := by omega
    obtain ⟨hs1, hw1, ht1⟩ := hP _ (by omega : (ops[n]!).1 < r.size)
    obtain ⟨hs2, hw2, ht2⟩ := hP _ (by omega : (ops[n]!).2 < r.size)
    show (mul 77 (r[(ops[r.size - 3]!).1]!) (r[(ops[r.size - 3]!).2]!)).size = 77 ∧
      RowsWF (mul 77 (r[(ops[r.size - 3]!).1]!) (r[(ops[r.size - 3]!).2]!)) ∧
      toMat 77 (mul 77 (r[(ops[r.size - 3]!).1]!) (r[(ops[r.size - 3]!).2]!)) =
        matJ (regJ r.size)
    rw [e]
    refine ⟨by rw [mul_size, hs1], RowsWF.mul _ 77 hw1 hw2, ?_⟩
    rw [regJ_succ (k := r.size) ⟨by omega, by rw [e]; omega, by rw [e]; omega⟩, e,
      toMat_mul hs1 hw1 hw2, matJ_mul, ht1, ht2]

theorem genM_spec {j : ℕ} (hj : j < 3) :
    (genM j).size = 77 ∧ RowsWF (genM j) ∧ toMat 77 (genM j) = matJ (gJ j) := by
  obtain ⟨-, hg, -, hgs, -, -⟩ := shape_parts
  have hj' : j < gens.size := by omega
  exact regs_spec.2 (gens[j]!) (by have := hg j hj'; omega)

theorem elts_spec :
    eltsM.size = nS ∧ ∀ i < nS, (eltsM[i]!).size = 77 ∧ RowsWF (eltsM[i]!) ∧
      toMat 77 (eltsM[i]!) = matJ (tabElt gJ par i) := by
  obtain ⟨-, -, -, -, -, hpar⟩ := shape_parts
  have h := buildN_inv (#[idM 77] : Array (Array V))
    (fun acc i => mul 77 (genM (par[i]!).2) (acc[(par[i]!).1]!))
    (fun k x => x.size = 77 ∧ RowsWF x ∧ toMat 77 x = matJ (tabElt gJ par k)) (nS - 1) ?_ ?_
  · have hs : 1 + (nS - 1) = nS := by unfold nS; omega
    have hsz : (#[idM 77] : Array (Array V)).size = 1 := rfl
    rw [hsz, hs] at h
    exact h
  · intro k hk
    have hk1 : k = 0 := by
      have : k < 1 := hk
      omega
    subst hk1
    refine ⟨idM_size 77, RowsWF.idM 77, ?_⟩
    show toMat 77 (idM 77) = matJ (tabElt gJ par 0)
    rw [toMat_idM, tabElt_zero, matJ_one]
  · intro n hn r hr hP
    have hrs : r.size = 1 + n := hr
    have hnS : 1 + n < nS := by unfold nS at hn ⊢; omega
    rcases hpar (1 + n) hnS with h0 | ⟨hp, hj⟩
    · omega
    have hp' : (par[r.size]!).1 < r.size := by rw [hrs]; exact hp
    have hj' : (par[r.size]!).2 < 3 := by rw [hrs]; exact hj
    obtain ⟨hs1, hw1, ht1⟩ := genM_spec hj'
    obtain ⟨hs2, hw2, ht2⟩ := hP _ hp'
    show (mul 77 (genM (par[r.size]!).2) (r[(par[r.size]!).1]!)).size = 77 ∧
      RowsWF (mul 77 (genM (par[r.size]!).2) (r[(par[r.size]!).1]!)) ∧
      toMat 77 (mul 77 (genM (par[r.size]!).2) (r[(par[r.size]!).1]!)) =
        matJ (tabElt gJ par r.size)
    refine ⟨by rw [mul_size, hs1], RowsWF.mul _ 77 hw1 hw2, ?_⟩
    rw [tabElt_succ gJ par hp', toMat_mul hs1 hw1 hw2, matJ_mul, ht1, ht2]

theorem tabData : TabData gJ par L nS 3 := by
  obtain ⟨-, -, -, -, -, hpar⟩ := shape_parts
  obtain ⟨-, -, hcanon, hleft, hdist⟩ := fi22S0Check_parts
  obtain ⟨hesz, hE⟩ := elts_spec
  refine ⟨fun i hi hin => ?_, fun j hj i hi => ?_, fun i hi k hk hik => ?_⟩
  · rcases hpar i hin with h0 | h0
    · omega
    · exact h0
  · unfold leftOK at hleft
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hleft
    obtain ⟨hlt, hmat⟩ := hleft j hj i hi
    refine ⟨hlt, matJ_injective ?_⟩
    obtain ⟨hs1, hw1, ht1⟩ := genM_spec hj
    obtain ⟨hs2, hw2, ht2⟩ := hE i hi
    obtain ⟨-, -, ht3⟩ := hE _ hlt
    have := toMat_eq_of_eqM hmat
    rw [toMat_mul hs1 hw1 hw2, ht1, ht2, ht3] at this
    rw [matJ_mul]
    exact this
  · unfold canonOK at hcanon
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hcanon
    unfold distinctOK at hdist
    simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hdist
    have key : ∀ i < nS, ∀ k < i, tabElt gJ par i ≠ tabElt gJ par k := by
      intro i hi k hk heq
      have h1 := not_eqM_of_ne (hE i hi).1 (hE k (by omega)).1 (hdist i hi k hk)
        (hcanon.2 i hi) (hcanon.2 k (by omega))
      apply h1
      rw [(hE i hi).2.2, (hE k (by omega)).2.2, heq]
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key k hk i hlt hik.symm
    · exact key i hi k hlt hik

theorem killOK_parts :
    ∀ a < nS, a ≠ 0 → tabMul par L a (tabMul par L a a) = 0 → 81 ≤ tabComm par L nS a := by
  have h := fi22S0Check_parts.2.1
  unfold killOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  intro a ha ha0 hcube
  rcases h a ha with (h0 | h1) | h2
  · exact absurd h0 ha0
  · exact absurd hcube h1
  · exact h2

theorem e27_fi22S0_table :
    ∃ T : Subgroup J, Nat.card T = 3 ^ (Nat.card J).factorization 3 ∧
      ∀ s ∈ T, orderOf s = 3 → 81 ∣ Nat.card ↥(T ⊓ centralizer ({s} : Set J)) := by
  haveI := finite_J
  obtain ⟨T, hT, -⟩ := tabData.exists_subgroup (by unfold nS; norm_num : 0 < nS)
  refine ⟨T, tabData.sylow_kill hT ?_ killOK_parts⟩
  rw [factorization_J]
  rfl

theorem fi22_dvd81_card_sylow_inf_centralizer {G : Type*}
    [Group G] (e : G ≃* J) (S₀ : Sylow 3 G) {z : G} (hz : z ∈ (S₀ : Subgroup G))
    (hz3 : orderOf z = 3) :
    81 ∣ Nat.card ↥((S₀ : Subgroup G) ⊓ centralizer ({z} : Set G)) := by
  obtain ⟨Tsub, hTcard, hTprop⟩ := e27_fi22S0_table
  refine @dvd81_card_sylow_inf_centralizer_of_equiv G J _ (Subgroup.toGroup J) finite_J e Tsub
    ?_ ?_ S₀ z hz hz3
  · exact hTcard
  · exact hTprop

end Certificates

end CFSG.HardMathSupport.Foote.E27.Fi22S0

namespace CFSG.HardMathSupport.Foote.E27

theorem E27Config.false_of_fi22
    {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X} (h : E27Config X K R T z)
    (hz : z ∈ K) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Fi22) : False := by
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  exact h.false_of_sylow_kill hz S₀ fun s hs hs3 =>
    Or.inl (Fi22S0.fi22_dvd81_card_sylow_inf_centralizer
      (e.trans CFSG.Sporadic.Fi22.fi22EquivJ) S₀ hs hs3)

theorem E27Config.false_of_sporadic_fi22
    {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic .Fi22).Group))
    (e : ↥K ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) : False :=
  h.false_of_fi22 hz (e.trans hbr.some.symm)

end CFSG.HardMathSupport.Foote.E27
