module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporRuGen
public import Certificates.Certificate4096
public import CFSG.Sporadic.Schreier.RuPair

public noncomputable section

namespace CFSG.QuasithinUnique.Vol2Native.L239.RuPairs

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native Equiv
open scoped commutatorElement

theorem ne_one_of_eqA_false {n : ℕ} {t : Array ℕ} {g : Perm (Fin n)} (ht : Rep n t g)
    (h : eqA n t (idA n) = false) : g ≠ 1 := fun hg => by
  have := (eqA_iff ht rep_idA).2 hg
  rw [h] at this
  exact Bool.false_ne_true this

theorem ne_of_eqA_false {n : ℕ} {t u : Array ℕ} {g h : Perm (Fin n)} (ht : Rep n t g)
    (hu : Rep n u h) (he : eqA n t u = false) : g ≠ h := fun hgh => by
  have := (eqA_iff ht hu).2 hgh
  rw [he] at this
  exact Bool.false_ne_true this

theorem rep_ruCInv : ∀ h < 2, Rep 4060 #[ruInv ruC0A, ruInv ruC1A][h]! ([ruC0, ruC1].getD h 1)⁻¹ :=
  rep_pair_getD_inv (rep_ruInv rep_ruC0 ruBasic_check.2.2.2.2.2.2.1)
    (rep_ruInv rep_ruC1 ruBasic_check.2.2.2.2.2.2.2.1)

theorem rep_ruWC {w : List ℤ} (hw : lettersOK 2 w = true) :
    Rep 4060 (ruWC w) (evalSigned [ruC0, ruC1] w) :=
  rep_wordA_evalSigned (k := 2) (rep_pair_getD rep_ruC0 rep_ruC1) rep_ruCInv w hw

theorem rep_ruWN {w : List ℤ} (hw : lettersOK 2 w = true) :
    Rep 4060 (ruWN w) (evalSigned [ruNs0, ruNs1] w) :=
  rep_wordA_evalSigned (k := 2) rep_ruNsPair rep_ruNsInvPair w hw

@[expose] def ruBC : Perm (Fin 4060) := evalSigned [ruC0, ruC1] [1, 1, 2] ^ 2

@[expose] def ruCC : Perm (Fin 4060) := ruC0 ^ 4

theorem ruC_witness_check :
    isInvA 4060 ruBCA (ruInv ruBCA) = true ∧
    isInvA 4060 ruJGensA[0]! (ruInv ruJGensA[0]!) = true ∧
    eqA 4060 (powA 4060 ruBCA 3) (idA 4060) = true ∧ eqA 4060 ruBCA (idA 4060) = false ∧
    eqA 4060 (powA 4060 ruCCA 5) (idA 4060) = true ∧ eqA 4060 ruCCA (idA 4060) = false ∧
    eqA 4060 (compA 4060 ruXCA ruXCA) (idA 4060) = false ∧
    eqA 4060 (compA 4060 ruJGensA[0]! ruCCA) (compA 4060 ruCCA ruJGensA[0]!) = false :=
  Certificates.certificate4096.1

theorem rep_ruBC : Rep 4060 ruBCA ruBC := rep_powA (rep_ruWC (by decide)) 2

theorem rep_ruCC : Rep 4060 ruCCA ruCC := rep_powA rep_ruC0 4

theorem rep_ruUJ : Rep 4060 ruJGensA[0]! (ruJGens.getD 0 1) := rep_ruJGens 0 (by norm_num)

theorem ruBC_order : orderOf ruBC = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (eq_of_eqA (rep_powA rep_ruBC 3) rep_idA ruC_witness_check.2.2.1)
    (ne_one_of_eqA_false rep_ruBC ruC_witness_check.2.2.2.1)

theorem ruCC_order : orderOf ruCC = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (eq_of_eqA (rep_powA rep_ruCC 5) rep_idA ruC_witness_check.2.2.2.2.1)
    (ne_one_of_eqA_false rep_ruCC ruC_witness_check.2.2.2.2.2.1)

theorem ruC_comm_sq : ⁅ruJGens.getD 0 1, ruBC⁆ * ⁅ruJGens.getD 0 1, ruBC⁆ ≠ 1 := by
  have hX : Rep 4060 ruXCA ⁅ruJGens.getD 0 1, ruBC⁆ := by
    rw [commutatorElement_def]
    exact rep_compA (rep_compA (rep_compA rep_ruUJ rep_ruBC)
      (rep_inv_of_isInvA rep_ruUJ ruC_witness_check.2.1))
      (rep_inv_of_isInvA rep_ruBC ruC_witness_check.1)
  exact ne_one_of_eqA_false (rep_compA hX hX) ruC_witness_check.2.2.2.2.2.2.1

theorem ruC_noncomm : ruJGens.getD 0 1 * ruCC ≠ ruCC * ruJGens.getD 0 1 :=
  ne_of_eqA_false (rep_compA rep_ruUJ rep_ruCC) (rep_compA rep_ruCC rep_ruUJ)
    ruC_witness_check.2.2.2.2.2.2.2

@[expose] def ruCN : Perm (Fin 4060) := evalSigned [ruNs0, ruNs1] [1, 2] ^ 2

theorem ruN_witness_check :
    isInvA 4060 ruKGensA[0]! (ruInv ruKGensA[0]!) = true ∧
    eqA 4060 (powA 4060 ruNs1A 3) (idA 4060) = true ∧ eqA 4060 ruNs1A (idA 4060) = false ∧
    isInvA 4060 ruCNA (ruInv ruCNA) = true ∧
    eqA 4060 (powA 4060 ruCNA 7) (idA 4060) = true ∧ eqA 4060 ruCNA (idA 4060) = false ∧
    eqA 4060 (compA 4060 ruXNA ruXNA) (idA 4060) = false ∧
    eqA 4060 (compA 4060 ruKGensA[0]! ruCNA) (compA 4060 ruCNA ruKGensA[0]!) = false :=
  Certificates.certificate4096.2

theorem rep_ruCN : Rep 4060 ruCNA ruCN := rep_powA (rep_ruWN (by decide)) 2

theorem rep_ruUK : Rep 4060 ruKGensA[0]! (ruKGens.getD 0 1) := rep_ruKGens 0 (by norm_num)

theorem ruNs1_order : orderOf ruNs1 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (eq_of_eqA (rep_powA rep_ruNs1 3) rep_idA ruN_witness_check.2.1)
    (ne_one_of_eqA_false rep_ruNs1 ruN_witness_check.2.2.1)

theorem ruCN_order : orderOf ruCN = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (eq_of_eqA (rep_powA rep_ruCN 7) rep_idA ruN_witness_check.2.2.2.2.1)
    (ne_one_of_eqA_false rep_ruCN ruN_witness_check.2.2.2.2.2.1)

theorem ruN_comm_sq : ⁅ruKGens.getD 0 1, ruNs1⁆ * ⁅ruKGens.getD 0 1, ruNs1⁆ ≠ 1 := by
  have hX : Rep 4060 ruXNA ⁅ruKGens.getD 0 1, ruNs1⁆ := by
    rw [commutatorElement_def]
    exact rep_compA (rep_compA (rep_compA rep_ruUK rep_ruNs1)
      (rep_inv_of_isInvA rep_ruUK ruN_witness_check.1))
      (rep_inv_of_isInvA rep_ruNs1 ruBasic_check.2.2.2.2.2.2.2.2.2.2.2.1)
  exact ne_one_of_eqA_false (rep_compA hX hX) ruN_witness_check.2.2.2.2.2.2.1

theorem ruN_noncomm : ruKGens.getD 0 1 * ruCN ≠ ruCN * ruKGens.getD 0 1 :=
  ne_of_eqA_false (rep_compA rep_ruUK rep_ruCN) (rep_compA rep_ruCN rep_ruUK)
    ruN_witness_check.2.2.2.2.2.2.2

theorem getD_mem_ruJGens {j : ℕ} (hj : j < 6) : ruJGens.getD j 1 ∈ ruJ := by
  refine Subgroup.subset_closure ?_
  rw [Set.mem_ofPred_eq, List.getD_eq_getElem ruJGens 1 (by simpa [ruJGens, ruJWords] using hj)]
  exact List.getElem_mem _

theorem getD_mem_ruKGens {j : ℕ} (hj : j < 8) : ruKGens.getD j 1 ∈ ruK := by
  refine Subgroup.subset_closure ?_
  rw [Set.mem_ofPred_eq, List.getD_eq_getElem ruKGens 1 (by simpa [ruKGens, ruKWords] using hj)]
  exact List.getElem_mem _

theorem ruC_goodLocal : GoodLocal (ruC.subgroupOf ruP) := by
  refine goodLocal_subgroupOf (Q := ruJ) ruC_le ruJ_leC ruJ_normal isPGroup_ruJ (a := 14)
    (p := 5) (by norm_num) le_rfl (by norm_num [card_ruC])
    (b := ruBC) (c := ruCC) (u := ruJGens.getD 0 1) (w := ruJGens.getD 0 1)
    (ruC.pow_mem (evalSigned_mem (pair_mem ruC0_memC ruC1_memC) _) 2) ruBC_order
    (ruC.pow_mem ruC0_memC 4) ruCC_order (getD_mem_ruJGens (by norm_num))
    (getD_mem_ruJGens (by norm_num)) ruC_comm_sq ruC_noncomm

theorem ruN_goodLocal : GoodLocal (ruN.subgroupOf ruP) := by
  refine goodLocal_subgroupOf (Q := ruK) ruN_le ruK_leN ruK_normal isPGroup_ruK (a := 14)
    (p := 7) (by norm_num) (by norm_num) (by norm_num [card_ruN])
    (b := ruNs1) (c := ruCN) (u := ruKGens.getD 0 1) (w := ruKGens.getD 0 1)
    ruNs1_memN ruNs1_order
    (ruN.pow_mem (evalSigned_mem (pair_mem ruNs0_memN ruNs1_memN) _) 2) ruCN_order
    (getD_mem_ruKGens (by norm_num)) (getD_mem_ruKGens (by norm_num)) ruN_comm_sq ruN_noncomm

end CFSG.QuasithinUnique.Vol2Native.L239.RuPairs
