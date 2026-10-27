module

public import CFSG.HardMathSupport.Foote.E27.TableSylow
public import CFSG.HardMathSupport.Foote.E27.TableMat
public import CFSG.HardMathSupport.Foote.E27.SporSylowBound
public import CFSG.HardMathSupport.Foote.E27.SporKill
public import CFSG.Sporadic.Ly
public import Certificates.Certificate131100

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.S0 CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native Subgroup

section Certificates


noncomputable def regJ (k : ℕ) : J :=
  if h : 2 ≤ k ∧ (ops[k - 2]!).1 < k ∧ (ops[k - 2]!).2 < k then
    regJ (ops[k - 2]!).1 * regJ (ops[k - 2]!).2
  else if k = 0 then a else if k = 1 then b else 1
termination_by k
decreasing_by
  all_goals first | exact h.2.1 | exact h.2.2

noncomputable def gJ (j : ℕ) : J := regJ (gens[j]!)

theorem regJ_succ {k : ℕ} (h : 2 ≤ k ∧ (ops[k - 2]!).1 < k ∧ (ops[k - 2]!).2 < k) :
    regJ k = regJ (ops[k - 2]!).1 * regJ (ops[k - 2]!).2 := by
  rw [regJ]; simp [h]

theorem regJ_zero : regJ 0 = a := by rw [regJ]; simp

theorem regJ_one : regJ 1 = b := by rw [regJ]; simp

theorem lyS0Check_parts :
    shapeOK = true ∧ killOK = true ∧ leftOK = true ∧ distinctOK = true := by
  have h := Certificates.certificate131100
  unfold lyS0Check at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem shape_parts :
    (∀ t < ops.size, (ops[t]!).1 < t + 2 ∧ (ops[t]!).2 < t + 2) ∧
    (∀ j < gens.size, gens[j]! < ops.size + 2) ∧ ops.size = 745 ∧ gens.size = 5 ∧ par.size = nS ∧
    (∀ i < nS, i = 0 ∨ ((par[i]!).1 < i ∧ (par[i]!).2 < 5)) := by
  have h := lyS0Check_parts.1
  unfold shapeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨fun t ht => h5 t ht, fun j hj => h6 j hj, h1, h2, h3, fun i hi => h7 i hi⟩

theorem regs_spec :
    regsM.size = 2 + ops.size ∧ ∀ k < 2 + ops.size, toMat 5 111 (regsM[k]!) = mat (regJ k) := by
  obtain ⟨hops, -, -, -, -, -⟩ := shape_parts
  have h := buildN_inv (#[matA, matB] : Array (Array (Array ℕ)))
    (fun acc k => mulM 5 111 (acc[(ops[k - 2]!).1]!) (acc[(ops[k - 2]!).2]!))
    (fun k x => toMat 5 111 x = mat (regJ k)) ops.size ?_ ?_
  · exact h
  · intro k hk
    have hk2 : k < 2 := hk
    interval_cases k
    · show toMat 5 111 matA = mat (regJ 0)
      rw [regJ_zero, toMat_matA]; rfl
    · show toMat 5 111 matB = mat (regJ 1)
      rw [regJ_one, toMat_matB]; rfl
  · intro n hn r hr hP
    have hrs : r.size = 2 + n := hr
    obtain ⟨hp1, hp2⟩ := hops n hn
    have e : r.size - 2 = n := by omega
    show toMat 5 111 (mulM 5 111 (r[(ops[r.size - 2]!).1]!) (r[(ops[r.size - 2]!).2]!)) =
      mat (regJ r.size)
    rw [e, regJ_succ (k := r.size) ⟨by omega, by rw [e]; omega, by rw [e]; omega⟩, e, toMat_mulM,
      mat_mul, hP _ (by omega), hP _ (by omega)]

theorem genM_spec {j : ℕ} (hj : j < 5) :
    toMat 5 111 (genM j) = mat (gJ j) := by
  obtain ⟨-, hg, -, hgs, -, -⟩ := shape_parts
  have hj' : j < gens.size := by omega
  have := (regs_spec.2 (gens[j]!) (by have := hg j hj'; omega))
  exact this

theorem elts_spec :
    eltsM.size = nS ∧ ∀ i < nS, toMat 5 111 (eltsM[i]!) = mat (tabElt gJ par i) := by
  obtain ⟨-, -, -, -, -, hpar⟩ := shape_parts
  have h := buildN_inv (#[idM 111] : Array (Array (Array ℕ)))
    (fun acc i => mulM 5 111 (genM (par[i]!).2) (acc[(par[i]!).1]!))
    (fun k x => toMat 5 111 x = mat (tabElt gJ par k)) (nS - 1) ?_ ?_
  · have hs : 1 + (nS - 1) = nS := by unfold nS; omega
    have hsz : (#[idM 111] : Array (Array (Array ℕ))).size = 1 := rfl
    rw [hsz, hs] at h
    exact h
  · intro k hk
    have hk1 : k = 0 := by
      have : k < 1 := hk
      omega
    subst hk1
    show toMat 5 111 (idM 111) = mat (tabElt gJ par 0)
    rw [toMat_idM, tabElt_zero, mat_one]
  · intro n hn r hr hP
    have hrs : r.size = 1 + n := hr
    have hnS : 1 + n < nS := by unfold nS at hn ⊢; omega
    rcases hpar (1 + n) hnS with h0 | ⟨hp, hj⟩
    · omega
    show toMat 5 111 (mulM 5 111 (genM (par[r.size]!).2) (r[(par[r.size]!).1]!)) =
      mat (tabElt gJ par r.size)
    have hp' : (par[r.size]!).1 < r.size := by rw [hrs]; exact hp
    rw [tabElt_succ gJ par hp', toMat_mulM, mat_mul, genM_spec (by rw [hrs]; exact hj),
      hP _ hp']

theorem tabData : TabData gJ par L nS 5 := by
  obtain ⟨-, -, -, -, -, hpar⟩ := shape_parts
  obtain ⟨-, -, hleft, hdist⟩ := lyS0Check_parts
  obtain ⟨hesz, hE⟩ := elts_spec
  refine ⟨fun i hi hin => ?_, fun j hj i hi => ?_, fun i hi k hk hik => ?_⟩
  · rcases hpar i hin with h0 | h0
    · omega
    · exact h0
  · unfold leftOK at hleft
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hleft
    obtain ⟨hlt, hmat⟩ := hleft j hj i hi
    refine ⟨hlt, mat_injective ?_⟩
    have := matEqB_true hmat
    rw [toMat_mulM, genM_spec hj, hE i hi, hE _ hlt, ← mat_mul] at this
    exact this
  · unfold distinctOK at hdist
    simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hdist
    have key : ∀ i < nS, ∀ k < i, tabElt gJ par i ≠ tabElt gJ par k := by
      intro i hi k hk heq
      have h1 := matEqB_false (hdist i hi k hk)
      apply h1
      rw [hE i hi, hE k (by omega), heq]
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key k hk i hlt hik.symm
    · exact key i hi k hlt hik

theorem killOK_parts :
    ∀ a < nS, a ≠ 0 → tabMul par L a (tabMul par L a a) = 0 → 81 ≤ tabComm par L nS a := by
  have h := lyS0Check_parts.2.1
  unfold killOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  intro a ha ha0 hcube
  rcases h a ha with (h0 | h1) | h2
  · exact absurd h0 ha0
  · exact absurd hcube h1
  · exact h2

theorem card_J_eq : Nat.card J = 51765179004000000 := by
  rw [← Nat.card_congr lyEquivJ.toEquiv]; exact card_Ly

theorem finite_J : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J_eq]; norm_num)

theorem factorization_J : (Nat.card J).factorization 3 = 7 := by
  rw [card_J_eq]
  have h : (51765179004000000 : ℕ) = 3 ^ 7 * (2 ^ 8 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67) := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem e27_lyS0_table :
    ∃ T : Subgroup J, Nat.card T = 3 ^ (Nat.card J).factorization 3 ∧
      ∀ s ∈ T, orderOf s = 3 → 81 ∣ Nat.card ↥(T ⊓ centralizer ({s} : Set J)) := by
  haveI := finite_J
  obtain ⟨T, hT, -⟩ := tabData.exists_subgroup (by unfold nS; norm_num : 0 < nS)
  refine ⟨T, tabData.sylow_kill hT ?_ killOK_parts⟩
  rw [factorization_J]
  rfl

theorem ly_dvd81_card_sylow_inf_centralizer {G : Type*} [Group G]
    (e : G ≃* J) (S₀ : Sylow 3 G) {z : G} (hz : z ∈ (S₀ : Subgroup G)) (hz3 : orderOf z = 3) :
    81 ∣ Nat.card ↥((S₀ : Subgroup G) ⊓ centralizer ({z} : Set G)) := by
  obtain ⟨Tsub, hTcard, hTprop⟩ := e27_lyS0_table
  refine @dvd81_card_sylow_inf_centralizer_of_equiv G J _ (Subgroup.toGroup J) finite_J e Tsub ?_ ?_ S₀ z hz hz3
  · exact hTcard
  · exact hTprop

theorem E27Config.false_of_ly {X : Type} [Group X] [Finite X]
    {K R T : Subgroup X} {z : X} (h : E27Config X K R T z) (hz : z ∈ K)
    (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Ly) : False := by
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  exact h.false_of_sylow_kill hz S₀ fun s hs hs3 =>
    Or.inl (ly_dvd81_card_sylow_inf_centralizer (e.trans lyEquivJ) S₀ hs hs3)

theorem E27Config.false_of_sporadic_ly {X : Type} [Group X]
    [Finite X] {K R T : Subgroup X} {z : X} (h : E27Config X K R T z) (hz : z ∈ K)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .Ly ≃*
      (TauCeti.CFSGIndex.sporadic .Ly).Group))
    (e : ↥K ≃* (TauCeti.CFSGIndex.sporadic .Ly).Group) : False :=
  h.false_of_ly hz (e.trans hbr.some.symm)

end Certificates

end CFSG.HardMathSupport.Foote.E27
