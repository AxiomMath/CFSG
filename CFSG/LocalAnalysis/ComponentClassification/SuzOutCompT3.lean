module

public import CFSG.LocalAnalysis.ComponentClassification.SuzOutCompT2
public import Certificates.Certificate22618

public noncomputable section

namespace CFSG.ComponentClassification.SuzOutComp

open CFSG CFSG.LocalCores Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Quasithin CFSG.Sporadic.SuzOddCore Native

theorem t3_check :
    (fixList 3).length = 100 ∧ (kGens 3).size = 5 ∧ (kGens 3).size ≤ t3XStrong.size ∧
    (∀ i < (kGens 3).size, t3XStrong[i]! = (kGens 3)[i]!) ∧
    rawChainOK 100 (t3XStrong.extract 0 (kGens 3).size) t3XStrong (t3XBase.map Fin.val).toArray
      t3XRaw 4 = true ∧
    rawOrbitSizes 100 t3XStrong (t3XBase.map Fin.val).toArray = [100, 63, 24, 8] ∧
    lettersOK (kGens 3).size t3Ab[0]! = true ∧ lettersOK (kGens 3).size t3Ab[1]! = true ∧
    isInvA 100 t3A (invCand 100 t3A) = true ∧ isInvA 100 t3B (invCand 100 t3B) = true ∧
    t3O.size ≤ t3DStrong.size ∧ (∀ i < t3O.size, t3DStrong[i]! = t3O[i]!) ∧
    rawChainOK 100 (t3DStrong.extract 0 t3O.size) t3DStrong (t3DBase.map Fin.val).toArray
      t3DRaw 4 = true ∧
    rawOrbitSizes 100 t3DStrong (t3DBase.map Fin.val).toArray = [100, 63, 24, 4] ∧
    primCheck 100 t3DStrong 0 t3Labels t3Roots 3 t3Tw t3Hw = true ∧
    reachCheck 100 t3DStrong 0 t3Labels t3Roots 3 t3Tw t3Reach = true ∧
    eqA 100 (Quasithin.powA 100 t3A 3) (idA 100) = true ∧ eqA 100 t3A (idA 100) = false ∧
    eqA 100 (Quasithin.powA 100 t3B 7) (idA 100) = true ∧ eqA 100 t3B (idA 100) = false ∧
    eqA 100 (Quasithin.powA 100 (compA 100 t3A t3B) 5) (idA 100) = true ∧
    eqA 100 (compA 100 t3A t3B) (idA 100) = false ∧
    eqA 100 (compA 100 t3A t3B) (compA 100 t3B t3A) = false :=
  Certificates.certificate22618

@[expose] def rho3 :
    invE 3 →* Equiv.Perm (Fin 100) :=
  cRho (i := 3) (by norm_num) t3_check.1

theorem invInnerGenArrs_size3' : (invInnerGenArrs 3).size = 5 := by
  simp [invInnerGenArrs, invInnerGenCounts]

theorem kGens3_isInvA {k : ℕ} (hk : k < (kGens 3).size) :
    isInvA 100 (kGens 3)[k]! (invCand 100 (kGens 3)[k]!) = true := by
  obtain ⟨-, -, hOS, hSO, hchain, -⟩ := t3_check
  have hF := chainCheckFacts hchain
  have := hF.strong_inv k (by omega)
  rw [rawInvs_getElem! (by omega), hSO k hk] at this
  exact this

theorem rho3_gen
    {k : ℕ} (hk : k < 5) :
    rho3 ⟨invInnerGen 3 k, invInnerGen_mem (by norm_num) (invInnerGenArrs_size3' ▸ hk)⟩ =
      permOfArr 100 (kGens 3)[k]! := by
  have hk' : k < (invInnerGenArrs 3).size := invInnerGenArrs_size3' ▸ hk
  have hkG : k < (kGens 3).size := by rw [t3_check.2.1]; exact hk
  have he : (⟨invInnerGen 3 k, invInnerGen_mem (by norm_num) hk'⟩ : invE 3) =
      innerGenE (i := 3) (by norm_num) k := by
    rw [innerGenE, dite_eq_left hk']
  have htab := tabRep_kGens (i := 3) (by norm_num) t3_check.1 hk'
  have hrep : Rep 100 (kGens 3)[k]! (rho3 ⟨invInnerGen 3 k, invInnerGen_mem (by norm_num) hk'⟩) :=
    by
    rw [he]
    exact htab.2
  exact hrep.unique (rep_permOfArr (kGens3_isInvA hkG)).1

theorem range_rho3 :
    rho3.range = closure {g | ∃ k < (kGens 3).size, permOfArr 100 (kGens 3)[k]! = g} := by
  have hs : (kGens 3).size = 5 := t3_check.2.1
  have hE := invE_eq_closure (i := 3) (by norm_num)
  rw [invInnerGenArrs_size3'] at hE
  rw [hs]
  exact range_eq_closure_of_gens hE (fun k hk => invInnerGen_mem (by norm_num)
    (invInnerGenArrs_size3' ▸ hk)) rho3 (fun k hk => rho3_gen hk)

theorem card_range_rho3 :
    Nat.card rho3.range = 1209600 := by
  obtain ⟨-, -, hOS, hSO, hchain, horb, -⟩ := t3_check
  rw [range_rho3, card_closure_permOfArr_of_rawChainOK (by norm_num) (by decide) (by norm_num)
    hOS hSO hchain, horb]
  norm_num

theorem rho3_injective :
    Function.Injective rho3 := by
  have hE : Nat.card (invE 3) = 1209600 := card_invE (i := 3) (by norm_num)
  have hR := card_range_rho3
  have : Finite (invE 3) := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup rho3.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange rho3).toEquiv, hR, hE] at h
  have hk : Nat.card rho3.ker = 1 := by omega
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.eq_bot_of_card_eq _ hk

abbrev D3 : Subgroup (Equiv.Perm (Fin 100)) :=
  closure {g | ∃ k < t3O.size, permOfArr 100 t3O[k]! = g}

theorem t3O_size : t3O.size = 2 := by rw [t3O]; rfl

theorem t3O_zero : t3O[0]! = t3A := by rw [t3O]; exact getElem!_pair_zero t3A t3B

theorem t3O_one : t3O[1]! = t3B := by rw [t3O]; exact getElem!_pair_one t3A t3B

theorem D3_simple : IsSimpleGroup D3 := by
  obtain ⟨-, -, -, -, -, -, -, -, hA, hB, hOS, hSO, hchain, horb, hprim, hreach, hA3, hA1,
    hB7, hB1, hAB5, hAB1, -⟩ := t3_check
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hrA := (rep_permOfArr hA).1
  have hrB := (rep_permOfArr hB).1
  refine isSimpleGroup_of_chain_reach (k := 3) (m := 6048) (by norm_num) (by decide)
    (by norm_num) t3O_size hOS hSO hchain hprim hreach (by rw [horb]; norm_num) ?_ ?_ ?_
    (by norm_num : Nat.Coprime 3 7) (by norm_num : Nat.Coprime 5 6048)
  · rw [t3O_zero]
    exact orderOf_eq_prime_of_rep hrA hA3 hA1
  · rw [t3O_one]
    exact orderOf_eq_prime_of_rep hrB hB7 hB1
  · rw [t3O_zero, t3O_one]
    exact orderOf_eq_prime_of_rep (rep_compA hrA hrB) hAB5 hAB1

theorem card_D3 : Nat.card D3 = 604800 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hOS, hSO, hchain, horb, -⟩ := t3_check
  rw [card_closure_permOfArr_of_rawChainOK (by norm_num) (by decide) (by norm_num) hOS hSO
    hchain, horb]
  norm_num

theorem D3_le_range :
    D3 ≤ rho3.range := by
  obtain ⟨-, -, -, -, -, -, hla, hlb, hA, hB, -⟩ := t3_check
  rw [range_rho3, closure_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [t3O_size] at hk
  interval_cases k
  · rw [t3O_zero]
    exact permOfArr_wordA_mem (fun k hk => kGens3_isInvA hk) hla hA
  · rw [t3O_one]
    exact permOfArr_wordA_mem (fun k hk => kGens3_isInvA hk) hlb hB

theorem D3_noncomm : ∃ a b : D3, a * b ≠ b * a := by
  obtain ⟨-, -, -, -, -, -, -, -, hA, hB, -, -, -, -, -, -, -, -, -, -, -, -, hc⟩ := t3_check
  have hrA := (rep_permOfArr hA).1
  have hrB := (rep_permOfArr hB).1
  refine ⟨⟨permOfArr 100 t3A, subset_closure ⟨0, by rw [t3O_size]; norm_num, by rw [t3O_zero]⟩⟩,
    ⟨permOfArr 100 t3B, subset_closure ⟨1, by rw [t3O_size]; norm_num, by rw [t3O_one]⟩⟩,
    fun h => ?_⟩
  have h' : permOfArr 100 t3A * permOfArr 100 t3B = permOfArr 100 t3B * permOfArr 100 t3A :=
    congrArg Subtype.val h
  have := (eqA_iff (rep_compA hrA hrB) (rep_compA hrB hrA)).2 h'
  rw [hc] at this
  exact Bool.false_ne_true this

theorem invE3_components
    {B : Subgroup (invE 3)} (hB : IsComponent B) : Nat.card (B ⧸ center B) = 604800 := by
  have hE : Nat.card (invE 3) = 1209600 := card_invE (i := 3) (by norm_num)
  have : Finite (invE 3) := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  rw [← card_D3]
  exact card_quotient_center_of_injective rho3 rho3_injective D3 D3_simple D3_le_range
    (by rw [card_D3, hE]) D3_noncomm hB

end CFSG.ComponentClassification.SuzOutComp
