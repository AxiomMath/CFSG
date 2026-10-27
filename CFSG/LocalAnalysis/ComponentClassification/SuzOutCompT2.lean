module

public import CFSG.LocalAnalysis.ComponentClassification.SuzOutCompTools
public import CFSG.LocalAnalysis.ComponentClassification.SuzOutCompBlock
public import CFSG.Sporadic.SuzOddCore.CTIBase
public import Certificates.Certificate22617
public import CFSG.LocalAnalysis.ComponentClassification.SuzOutCompSimple

public noncomputable section

namespace CFSG.ComponentClassification.SuzOutComp

open CFSG CFSG.LocalCores Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Quasithin CFSG.Sporadic.SuzOddCore Native

theorem t2_check :
    blocksOK 1782 396 t2Lab t2Rep = true ∧
    blockOK 1782 396 t2Lab t2Rep (invInnerGenArrs 2)[0]! = true ∧
    blockOK 1782 396 t2Lab t2Rep (invInnerGenArrs 2)[1]! = true ∧
    t2Gens.size = 2 ∧ t2Gens.size ≤ t2XStrong.size ∧
    (∀ i < t2Gens.size, t2XStrong[i]! = t2Gens[i]!) ∧
    rawChainOK 396 (t2XStrong.extract 0 t2Gens.size) t2XStrong (t2XBase.map Fin.val).toArray
      t2XRaw 4 = true ∧
    rawOrbitSizes 396 t2XStrong (t2XBase.map Fin.val).toArray = [396, 120, 2, 2] ∧
    lettersOK t2Gens.size t2Ab[0]! = true ∧ lettersOK t2Gens.size t2Ab[1]! = true ∧
    isInvA 396 t2A (invCand 396 t2A) = true ∧ isInvA 396 t2B (invCand 396 t2B) = true ∧
    t2O.size ≤ t2DStrong.size ∧ (∀ i < t2O.size, t2DStrong[i]! = t2O[i]!) ∧
    rawChainOK 396 (t2DStrong.extract 0 t2O.size) t2DStrong (t2DBase.map Fin.val).toArray
      t2DRaw 4 = true ∧
    rawOrbitSizes 396 t2DStrong (t2DBase.map Fin.val).toArray = [396, 60, 4] ∧
    primCheck 396 t2DStrong 0 t2Labels t2Roots 10 t2Tw t2Hw = true ∧
    reachCheck 396 t2DStrong 0 t2Labels t2Roots 10 t2Tw t2Reach = true ∧
    eqA 396 (Quasithin.powA 396 t2A 3) (idA 396) = true ∧ eqA 396 t2A (idA 396) = false ∧
    eqA 396 (Quasithin.powA 396 t2B 11) (idA 396) = true ∧ eqA 396 t2B (idA 396) = false ∧
    eqA 396 (Quasithin.powA 396 (compA 396 t2A t2B) 11) (idA 396) = true ∧
    eqA 396 (compA 396 t2A t2B) (idA 396) = false ∧
    eqA 396 (compA 396 t2A t2B) (compA 396 t2B t2A) = false :=
  Certificates.certificate22617

@[expose] def t2lab (x : Fin 1782) : ℕ := t2Lab[(x : ℕ)]!

@[expose] def t2rep (j : Fin 396) : Fin 1782 := ⟨t2Rep[(j : ℕ)]! % 1782, Nat.mod_lt _ (by norm_num)⟩

theorem t2rep_spec (j : Fin 396) :
    (t2rep j : ℕ) = t2Rep[(j : ℕ)]! ∧ t2lab (t2rep j) = j := by
  have h := allLt_spec t2_check.1 j.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hv : (t2rep j : ℕ) = t2Rep[(j : ℕ)]! := Nat.mod_eq_of_lt h.1
  refine ⟨hv, ?_⟩
  rw [t2lab, hv]
  exact h.2

theorem t2rep_lab (j : Fin 396) : t2lab (t2rep j) = j :=
  (t2rep_spec j).2

theorem invInnerGenArrs_size2 : (invInnerGenArrs 2).size = 2 := by
  simp [invInnerGenArrs, invInnerGenCounts]

theorem invE2_le_blockStab :
    invE 2 ≤ blockStab 1782 396 t2lab := by
  rw [invE_eq_closure (i := 2) (by norm_num), closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk2 : k < 2 := invInnerGenArrs_size2 ▸ hk
  obtain ⟨-, h0, h1, -⟩ := t2_check
  interval_cases k
  · exact mem_blockStab_of_blockOK (rep_invInnerGen (i := 2) (by norm_num) hk) h0
  · exact mem_blockStab_of_blockOK (rep_invInnerGen (i := 2) (by norm_num) hk) h1

@[expose] def rho2 :
    invE 2 →* Equiv.Perm (Fin 396) :=
  (blockHom t2rep_lab).comp (Subgroup.inclusion invE2_le_blockStab)

theorem t2Gens_isInvA {k : ℕ} (hk : k < t2Gens.size) :
    isInvA 396 t2Gens[k]! (invCand 396 t2Gens[k]!) = true := by
  obtain ⟨-, -, -, -, hOS, hSO, hchain, -⟩ := t2_check
  have hF := chainCheckFacts hchain
  have := hF.strong_inv k (by omega)
  rw [rawInvs_getElem! (by omega), hSO k hk] at this
  exact this

theorem rho2_gen {k : ℕ}
    (hk : k < 2) :
    rho2 ⟨invInnerGen 2 k, invInnerGen_mem (by norm_num) (invInnerGenArrs_size2 ▸ hk)⟩ =
      permOfArr 396 t2Gens[k]! := by
  have hk' : k < (invInnerGenArrs 2).size := invInnerGenArrs_size2 ▸ hk
  have hkG : k < t2Gens.size := by rw [t2_check.2.2.2.1]; exact hk
  have h1 : t2Gens[k]! = blockArr t2Lab t2Rep 396 (invInnerGenArrs 2)[k]! := by
    rw [t2Gens, getElem!_pos _ k (by simpa using hk'), Array.getElem_map,
      ← getElem!_pos _ k hk']
  have hrep : Rep 396 t2Gens[k]! (rho2 ⟨invInnerGen 2 k, invInnerGen_mem (by norm_num) hk'⟩) := by
    rw [h1]
    exact rep_blockArr t2rep_lab (fun x => rfl) (fun j => (t2rep_spec j).1) _
      (rep_invInnerGen (i := 2) (by norm_num) hk')
  exact hrep.unique (rep_permOfArr (t2Gens_isInvA hkG)).1

theorem range_rho2 :
    rho2.range = closure {g | ∃ k < t2Gens.size, permOfArr 396 t2Gens[k]! = g} := by
  have hs : t2Gens.size = 2 := t2_check.2.2.2.1
  have hE := invE_eq_closure (i := 2) (by norm_num)
  rw [invInnerGenArrs_size2] at hE
  rw [hs]
  exact range_eq_closure_of_gens hE (fun k hk => invInnerGen_mem (by norm_num)
    (invInnerGenArrs_size2 ▸ hk)) rho2 (fun k hk => rho2_gen hk)

theorem card_range_rho2 :
    Nat.card rho2.range = 190080 := by
  obtain ⟨-, -, -, -, hOS, hSO, hchain, horb, -⟩ := t2_check
  rw [range_rho2, card_closure_permOfArr_of_rawChainOK (by norm_num) (by decide) (by norm_num)
    hOS hSO hchain, horb]
  norm_num

theorem rho2_injective :
    Function.Injective rho2 := by
  have hE : Nat.card (invE 2) = 190080 := card_invE (i := 2) (by norm_num)
  have hR := card_range_rho2
  have : Finite (invE 2) := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup rho2.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange rho2).toEquiv, hR, hE] at h
  have hk : Nat.card rho2.ker = 1 := by omega
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.eq_bot_of_card_eq _ hk

abbrev D2 : Subgroup (Equiv.Perm (Fin 396)) :=
  closure {g | ∃ k < t2O.size, permOfArr 396 t2O[k]! = g}

theorem getElem!_pair_zero {α : Type*} [Inhabited α] (a b : α) : #[a, b][0]! = a := rfl

theorem getElem!_pair_one {α : Type*} [Inhabited α] (a b : α) : #[a, b][1]! = b := rfl

theorem t2O_size : t2O.size = 2 := by rw [t2O]; rfl

theorem t2O_zero : t2O[0]! = t2A := by rw [t2O]; exact getElem!_pair_zero t2A t2B

theorem t2O_one : t2O[1]! = t2B := by rw [t2O]; exact getElem!_pair_one t2A t2B

theorem D2_simple : IsSimpleGroup D2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hA, hB, hOS, hSO, hchain, horb, hprim, hreach, hA3, hA1,
    hB11, hB1, hAB11, hAB1, -⟩ := t2_check
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hrA := (rep_permOfArr hA).1
  have hrB := (rep_permOfArr hB).1
  refine isSimpleGroup_of_chain_reach (k := 10) (m := 240) (by norm_num) (by decide)
    (by norm_num) t2O_size hOS hSO hchain hprim hreach (by rw [horb]; norm_num) ?_ ?_ ?_
    (by norm_num : Nat.Coprime 3 11) (by norm_num : Nat.Coprime 11 240)
  · rw [t2O_zero]
    exact orderOf_eq_prime_of_rep hrA hA3 hA1
  · rw [t2O_one]
    exact orderOf_eq_prime_of_rep hrB hB11 hB1
  · rw [t2O_zero, t2O_one]
    exact orderOf_eq_prime_of_rep (rep_compA hrA hrB) hAB11 hAB1

theorem card_D2 : Nat.card D2 = 95040 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hOS, hSO, hchain, horb, -⟩ := t2_check
  rw [card_closure_permOfArr_of_rawChainOK (by norm_num) (by decide) (by norm_num) hOS hSO
    hchain, horb]
  norm_num

theorem D2_le_range :
    D2 ≤ rho2.range := by
  obtain ⟨-, -, -, -, -, -, -, -, hla, hlb, hA, hB, -⟩ := t2_check
  rw [range_rho2, closure_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [t2O_size] at hk
  interval_cases k
  · rw [t2O_zero]
    exact permOfArr_wordA_mem (fun k hk => t2Gens_isInvA hk) hla hA
  · rw [t2O_one]
    exact permOfArr_wordA_mem (fun k hk => t2Gens_isInvA hk) hlb hB

theorem D2_noncomm : ∃ a b : D2, a * b ≠ b * a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hA, hB, -, -, -, -, -, -, -, -, -, -, -, -, hc⟩ := t2_check
  have hrA := (rep_permOfArr hA).1
  have hrB := (rep_permOfArr hB).1
  refine ⟨⟨permOfArr 396 t2A, subset_closure ⟨0, by rw [t2O_size]; norm_num, by rw [t2O_zero]⟩⟩,
    ⟨permOfArr 396 t2B, subset_closure ⟨1, by rw [t2O_size]; norm_num, by rw [t2O_one]⟩⟩,
    fun h => ?_⟩
  have h' : permOfArr 396 t2A * permOfArr 396 t2B = permOfArr 396 t2B * permOfArr 396 t2A :=
    congrArg Subtype.val h
  have := (eqA_iff (rep_compA hrA hrB) (rep_compA hrB hrA)).2 h'
  rw [hc] at this
  exact Bool.false_ne_true this

theorem invE2_components
    {B : Subgroup (invE 2)} (hB : IsComponent B) :
    Nat.card (B ⧸ center B) = 95040 := by
  have hE : Nat.card (invE 2) = 190080 := card_invE (i := 2) (by norm_num)
  have : Finite (invE 2) := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  rw [← card_D2]
  exact card_quotient_center_of_injective rho2 rho2_injective D2 D2_simple D2_le_range
    (by rw [card_D2, hE]) D2_noncomm hB

end CFSG.ComponentClassification.SuzOutComp
