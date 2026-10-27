module

public import CFSG.HardMathSupport.Foote.E27.TableSylow
public import CFSG.HardMathSupport.Foote.E27.TableMat
public import CFSG.HardMathSupport.Foote.E27.SporSylowBound
public import CFSG.HardMathSupport.Foote.E27.SporKill
public import Certificates.Certificate131301
public import CFSG.Sporadic.Co1Block.PermBase

public section

namespace CFSG.HardMathSupport.Foote.E27.Co1S0

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1.S0 CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.SmallF2 CFSG.HardMathSupport.Foote.E27 Subgroup

noncomputable def regG (k : ℕ) : GL24 :=
  if _h : 3 ≤ k ∧ (ops[k - 3]!).1 < k ∧ (ops[k - 3]!).2 < k then
    regG (ops[k - 3]!).1 * regG (ops[k - 3]!).2
  else if k = 0 then A₁ else if k = 1 then A₂ else if k = 2 then A₂⁻¹ else 1
termination_by k
decreasing_by
  all_goals first | exact _h.2.1 | exact _h.2.2

theorem regG_succ {k : ℕ} (h : 3 ≤ k ∧ (ops[k - 3]!).1 < k ∧ (ops[k - 3]!).2 < k) :
    regG k = regG (ops[k - 3]!).1 * regG (ops[k - 3]!).2 := by
  rw [regG]; simp [h]

theorem regG_zero : regG 0 = A₁ := by rw [regG]; simp

theorem regG_one : regG 1 = A₂ := by rw [regG]; simp

theorem regG_two : regG 2 = A₂⁻¹ := by rw [regG]; simp

theorem regG_mem (k : ℕ) : regG k ∈ GA := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h : 3 ≤ k ∧ (ops[k - 3]!).1 < k ∧ (ops[k - 3]!).2 < k
    · rw [regG_succ h]
      exact mul_mem (ih _ h.2.1) (ih _ h.2.2)
    · rw [regG]
      simp only [h, dite_false]
      split_ifs
      · exact A₁_mem
      · exact A₂_mem
      · exact inv_mem A₂_mem
      · exact one_mem _

@[expose] noncomputable def regJ (k : ℕ) : GA := ⟨regG k, regG_mem k⟩

@[expose] noncomputable def gJ (j : ℕ) : GA := regJ (gens[j]!)

theorem coe_gJ (j : ℕ) : (gJ j : GL24) = regG (gens[j]!) := rfl

theorem rows_eq_of_mRep {X Y : Rows} {g : GL24} (hX : wf X = true) (hY : wf Y = true)
    (hgX : MRep X g) (hgY : MRep Y g) : X = Y := by
  have hm : rowsMatrix 24 X = rowsMatrix 24 Y := hgX.trans hgY.symm
  unfold wf at hX hY
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at hX hY
  obtain ⟨hXs, hXb⟩ := hX
  obtain ⟨hYs, hYb⟩ := hY
  refine Array.ext (hXs.trans hYs.symm) fun i hi hi' => ?_
  have hi24 : i < 24 := hXs ▸ hi
  apply toVecD_injective (d := 24) (hXb i hi) (hYb i hi')
  funext j
  have := congrFun (congrFun hm ⟨i, hi24⟩) j
  rw [rowsMatrix_apply, rowsMatrix_apply] at this
  simpa [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi'] using this

theorem co1S0Check_parts :
    invOK = true ∧ shapeOK = true ∧ killOK = true ∧ canonOK = true ∧ leftOK = true ∧
      distinctOK = true := by
  have h := Certificates.certificate131301
  unfold co1S0Check at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem shape_parts :
    (∀ t < ops.size, (ops[t]!).1 < t + 3 ∧ (ops[t]!).2 < t + 3) ∧
    (∀ j < gens.size, gens[j]! < ops.size + 3) ∧ ops.size = 1153 ∧ gens.size = 3 ∧
    par.size = nS ∧ (∀ i < nS, i = 0 ∨ ((par[i]!).1 < i ∧ (par[i]!).2 < 3)) := by
  have h := co1S0Check_parts.2.1
  unfold shapeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨fun t ht => h5 t ht, fun j hj => h6 j hj, h1, h2, h3, fun i hi => h7 i hi⟩

theorem regs_spec :
    regsM.size = 3 + ops.size ∧ ∀ k < 3 + ops.size, MRep (regsM[k]!) (regG k) := by
  obtain ⟨hops, -, -, -, -, -⟩ := shape_parts
  have hinv := co1S0Check_parts.1
  unfold invOK at hinv
  rw [beq_iff_eq] at hinv
  have hbi : MRep biRows (A₂⁻¹ : GL24) := rep_A₂.inv hinv
  have h := buildN_inv (#[aRows, bRows, biRows] : Array Rows)
    (fun acc k => mul (acc[(ops[k - 3]!).1]!) (acc[(ops[k - 3]!).2]!))
    (fun k x => MRep x (regG k)) ops.size ?_ ?_
  · exact h
  · intro k hk
    have hk3 : k < 3 := hk
    interval_cases k
    · show MRep aRows (regG 0)
      rw [regG_zero]
      exact rep_A₁
    · show MRep bRows (regG 1)
      rw [regG_one]
      exact rep_A₂
    · show MRep biRows (regG 2)
      rw [regG_two]
      exact hbi
  · intro n hn r hr hP
    have hrs : r.size = 3 + n := hr
    obtain ⟨hp1, hp2⟩ := hops n hn
    have e : r.size - 3 = n := by omega
    have ht1 := hP _ (by omega : (ops[n]!).1 < r.size)
    have ht2 := hP _ (by omega : (ops[n]!).2 < r.size)
    show MRep (mul (r[(ops[r.size - 3]!).1]!) (r[(ops[r.size - 3]!).2]!)) (regG r.size)
    rw [regG_succ (k := r.size) ⟨by omega, by rw [e]; omega, by rw [e]; omega⟩, e]
    exact ht1.mul ht2

theorem genM_spec {j : ℕ}
    (hj : j < 3) : MRep (genM j) (gJ j : GL24) := by
  obtain ⟨-, hg, -, hgs, -, -⟩ := shape_parts
  have hj' : j < gens.size := by omega
  rw [coe_gJ]
  exact regs_spec.2 (gens[j]!) (by have := hg j hj'; omega)

theorem elts_spec :
    eltsM.size = nS ∧ ∀ i < nS, MRep (eltsM[i]!) ((tabElt gJ par i : GA) : GL24) := by
  obtain ⟨-, -, -, -, -, hpar⟩ := shape_parts
  have h := buildN_inv (#[one] : Array Rows)
    (fun acc i => mul (genM (par[i]!).2) (acc[(par[i]!).1]!))
    (fun k x => MRep x ((tabElt gJ par k : GA) : GL24)) (nS - 1) ?_ ?_
  · have hs : 1 + (nS - 1) = nS := by unfold nS; omega
    have hsz : (#[one] : Array Rows).size = 1 := rfl
    rw [hsz, hs] at h
    exact h
  · intro k hk
    have hk1 : k = 0 := by
      have : k < 1 := hk
      omega
    subst hk1
    show MRep one ((tabElt gJ par 0 : GA) : GL24)
    rw [tabElt_zero]
    exact MRep.one
  · intro n hn r hr hP
    have hrs : r.size = 1 + n := hr
    have hnS : 1 + n < nS := by unfold nS at hn ⊢; omega
    rcases hpar (1 + n) hnS with h0 | ⟨hp, hj⟩
    · omega
    have hp' : (par[r.size]!).1 < r.size := by rw [hrs]; exact hp
    have hj' : (par[r.size]!).2 < 3 := by rw [hrs]; exact hj
    show MRep (mul (genM (par[r.size]!).2) (r[(par[r.size]!).1]!))
      ((tabElt gJ par r.size : GA) : GL24)
    rw [tabElt_succ gJ par hp']
    exact (genM_spec hj').mul (hP _ hp')

theorem tabData :
    TabData gJ par L nS 3 := by
  obtain ⟨-, -, -, -, -, hpar⟩ := shape_parts
  obtain ⟨-, -, -, hcanon, hleft, hdist⟩ := co1S0Check_parts
  obtain ⟨hesz, hE⟩ := elts_spec
  refine ⟨fun i hi hin => ?_, fun j hj i hi => ?_, fun i hi k hk hik => ?_⟩
  · rcases hpar i hin with h0 | h0
    · omega
    · exact h0
  · unfold leftOK at hleft
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hleft
    obtain ⟨hlt, hmat⟩ := hleft j hj i hi
    refine ⟨hlt, Subtype.ext (MRep.eq ?_ (hE _ hlt))⟩
    rw [← hmat]
    exact (genM_spec hj).mul (hE i hi)
  · unfold canonOK at hcanon
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hcanon
    unfold distinctOK at hdist
    simp only [List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hdist
    have key : ∀ i < nS, ∀ k < i, tabElt gJ par i ≠ tabElt gJ par k := by
      intro i hi k hk heq
      have h1 := hE i hi
      rw [heq] at h1
      exact hdist i hi k hk (rows_eq_of_mRep (hcanon.2 i hi) (hcanon.2 k (by omega)) h1
        (hE k (by omega)))
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key k hk i hlt hik.symm
    · exact key i hi k hlt hik

theorem killOK_parts :
    ∀ a < nS, a ≠ 0 → tabMul par L a (tabMul par L a a) = 0 → 81 ≤ tabComm par L nS a := by
  have h := co1S0Check_parts.2.2.1
  unfold killOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  intro a ha ha0 hcube
  rcases h a ha with (h0 | h1) | h2
  · exact absurd h0 ha0
  · exact absurd hcube h1
  · exact h2

theorem finite_GA : Finite GA :=
  Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)

theorem factorization_GA :
    (Nat.card GA).factorization 3 = 9 := by
  rw [card_GA_eq]
  have h : (4157776806543360000 : ℕ) = 3 ^ 9 * 211236945920000 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem e27_co1S0_table :
    ∃ T : Subgroup GA, Nat.card T = 3 ^ (Nat.card GA).factorization 3 ∧
      ∀ s ∈ T, orderOf s = 3 → 81 ∣ Nat.card ↥(T ⊓ centralizer ({s} : Set GA)) := by
  have := finite_GA
  obtain ⟨T, hT, -⟩ := tabData.exists_subgroup (by unfold nS; norm_num : 0 < nS)
  refine ⟨T, tabData.sylow_kill hT ?_ killOK_parts⟩
  rw [factorization_GA]
  rfl

theorem co1_dvd81_card_sylow_inf_centralizer
    {G : Type*} [Group G] (e : G ≃* GA) (S₀ : Sylow 3 G) {z : G}
    (hz : z ∈ (S₀ : Subgroup G)) (hz3 : orderOf z = 3) :
    81 ∣ Nat.card ↥((S₀ : Subgroup G) ⊓ centralizer ({z} : Set G)) := by
  obtain ⟨Tsub, hTcard, hTprop⟩ := e27_co1S0_table
  exact @dvd81_card_sylow_inf_centralizer_of_equiv G GA _ (Subgroup.toGroup GA) finite_GA e Tsub
    hTcard hTprop S₀ z hz hz3

end CFSG.HardMathSupport.Foote.E27.Co1S0

namespace CFSG.HardMathSupport.Foote.E27

theorem E27Config.false_of_co1
    {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X} (h : E27Config X K R T z)
    (hz : z ∈ K) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Co1) : False := by
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  exact h.false_of_sylow_kill hz S₀ fun s hs hs3 =>
    Or.inl (Co1S0.co1_dvd81_card_sylow_inf_centralizer
      (e.trans CFSG.Sporadic.Co1Block.co1MatEquiv) S₀ hs hs3)

theorem E27Config.false_of_sporadic_co1
    {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .Co1 ≃*
      (TauCeti.CFSGIndex.sporadic .Co1).Group))
    (e : ↥K ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group) : False :=
  h.false_of_co1 hz (e.trans hbr.some.symm)

end CFSG.HardMathSupport.Foote.E27
