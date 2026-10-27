module

public import CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Seven
public import Certificates.Certificate17707

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows.Co2Eleven

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Co2Cert
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenNative CFSG.Sporadic.Fi23.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Seven
  CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenNative


local notation "LL" => slpLetters 2300 (co2Gens (co2T 0) (co2T 1)) co2ElevenData.words

local notation "YY" => LL[2 * co2ElevenData.is]!

local notation "ωω" => ap LL[2 * co2ElevenData.ih]! 0

set_option quotPrecheck false in
local notation "BB" => (Array.range 7).map fun i => iterAp YY i ωω

local notation "LCC" => subLetters LL co2ElevenData.chain

local notation "TT" => chainTrees 2300 LCC BB

theorem co2Eleven_parts :
    invOK 2300 (co2T 0) (invT 2300 (co2T 0)) = true ∧
      invOK 2300 (co2T 1) (invT 2300 (co2T 1)) = true ∧
      slpOK co2ElevenData.words = true ∧ co2ElevenData.is < co2ElevenData.words.size ∧
      (∀ j < co2ElevenData.words.size, invOK 2300 LL[2 * j]! LL[2 * j + 1]! = true) ∧
      (∀ t < co2ElevenData.chain.size, co2ElevenData.chain[t]! < co2ElevenData.words.size) ∧
      eqTab2 (powT 2300 11 YY) (idT 2300) = true ∧ eqTab2 YY (idT 2300) = false ∧
      (∀ i < 7, treeOK 2300 (BB)[i]! (TT)[i]! LCC (levelLetters LCC BB i) = true) ∧
      (List.range 7).foldl (fun acc i => acc * (TT)[i]!.pts.size) 1 = cardCo2 () ∧
      Nat.count (fun p => sift TT LCC (Array.range 7) BB 0 (tupleOf YY 7 p) = true) 2300 ≤
        11 := by
  have h := Certificates.certificate17707
  unfold co2ElevenCheck co2ElevenOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩, -⟩, -⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩ := h
  refine ⟨h1, h2, h3, h4, fun j hj => ?_, fun t ht => ?_, h10, h11, fun i hi => ?_, h13, h14⟩
  · rw [List.all_eq_true] at h6
    exact h6 j (List.mem_range.2 hj)
  · rw [Array.all_eq_true] at h7
    rw [getElem!_pos _ t ht]
    exact of_decide_eq_true (h7 t ht)
  · rw [List.all_eq_true] at h12
    exact h12 i (List.mem_range.2 hi)

@[expose] noncomputable def gE (j : ℕ) : co2P :=
  CFSG.Sporadic.Fi23.slpG genG co2ElevenData.words j

theorem rep_genE : ∀ z, Rep 2300 (co2Gens (co2T 0) (co2T 1) z) (genG z) := by
  have h0 : Rep 2300 (co2T 0) gen0 := rep_co2T (by norm_num) rfl
  have h1 : Rep 2300 (co2T 1) gen1 := rep_co2T (by norm_num) rfl
  obtain ⟨hi0, hi1, -⟩ := co2Eleven_parts
  intro z
  unfold co2Gens genG
  split_ifs
  · exact h0
  · exact h0.inv_of_invOK hi0
  · exact h1
  · exact h1.inv_of_invOK hi1

theorem rep_gE : ∀ j < co2ElevenData.words.size, Rep 2300 LL[2 * j]! (gE j) :=
  CFSG.Sporadic.Fi23.rep_slpLetters (by norm_num) rep_genE co2Eleven_parts.2.2.1
    co2Eleven_parts.2.2.2.2.1

@[expose] noncomputable def sE : co2P := gE co2ElevenData.is

theorem rep_YY : Rep 2300 YY sE := rep_gE _ co2Eleven_parts.2.2.2.1

theorem orderOf_sE : orderOf sE = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime
    (eq_of_eqTab2 (rep_YY.powT (by norm_num) 11) (Rep.idT (by norm_num))
      co2Eleven_parts.2.2.2.2.2.2.1)
    (ne_of_eqTab2_false rep_YY co2Eleven_parts.2.2.2.2.2.2.2.1)

theorem card_centralizer_sE_le :
    Nat.card (Subgroup.centralizer ({sE} : Set co2P)) ≤ 11 := by
  obtain ⟨-, -, -, -, hinv, hch, -, -, htree, hprod, hcount⟩ := co2Eleven_parts
  have hrepC : ∀ t < (LCC).size / 2, Rep 2300 (LCC)[2 * t]! (gE co2ElevenData.chain[t]!) := by
    intro t ht
    rw [subLetters_size'] at ht
    have ht' : t < co2ElevenData.chain.size := by omega
    rw [subLetters_even' _ _ ht']
    exact rep_gE _ (hch t ht')
  have h2C : (LCC).size % 2 = 0 := by rw [subLetters_size']; omega
  have hinvC : ∀ t < (LCC).size / 2, invOK 2300 (LCC)[2 * t]! (LCC)[2 * t + 1]! = true := by
    intro t ht
    rw [subLetters_size'] at ht
    have ht' : t < co2ElevenData.chain.size := by omega
    rw [subLetters_even' _ _ ht', subLetters_odd' _ _ ht']
    exact hinv _ (hch t ht')
  have hbsz : (BB).size = 7 := by simp
  have htree' : ∀ i < (BB).size, Perm.Native.treeOK 2300 (BB)[i]! (TT)[i]! LCC
      (levelLetters LCC BB i) = true := by
    intro i hi
    rw [hbsz] at hi
    exact htree i hi
  have hfold : (List.range 7).foldl (fun acc i => acc * (TT)[i]!.pts.size) 1 =
      ∏ i ∈ Finset.range 7, (TT)[i]!.pts.size := by
    simp [Finset.prod_range_succ, List.range_succ]
  have hcard : ∏ l ∈ Finset.range (BB).size, (TT)[l]!.pts.size = Nat.card co2P := by
    rw [hbsz, ← hfold, hprod, card_co2P]
    rfl
  have hbase : ∀ i < (BB).size, (BB)[i]! = iterAp YY i (BB)[0]! := by
    intro i hi
    have h0 : (BB)[0]! = ωω := by
      rw [getElem!_pos _ 0 (by simp), Array.getElem_map, Array.getElem_range]
      rfl
    rw [h0, getElem!_pos _ i (by simpa using hi), Array.getElem_map, Array.getElem_range]
  have hcardC := card_centralizer_le_of_tupleSift (G := co2P)
    (gs := fun t => gE co2ElevenData.chain[t]!) hrepC h2C hinvC (by simp [chainTrees]) htree'
    hcard rep_YY (by rw [hbsz]; norm_num) hbase
  rw [hbsz] at hcardC
  exact hcardC.trans hcount

theorem card_centralizer_sE :
    Nat.card (Subgroup.centralizer ({sE} : Set co2P)) = 11 := by
  have : Finite co2P := Nat.finite_of_card_ne_zero (by rw [card_co2P]; norm_num)
  have hle : Subgroup.zpowers sE ≤ Subgroup.centralizer ({sE} : Set co2P) :=
    (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have h11 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, orderOf_sE] at h11
  exact le_antisymm card_centralizer_sE_le h11

theorem co2_eleven_card_centralizer
    (x : CFSG.Blueprint.NativeSporadic.Co2) (hx : orderOf x = 11) :
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co2)) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hcard : Nat.card CFSG.Blueprint.NativeSporadic.Co2 = 42305421312000 := by
    rw [Nat.card_congr co2PermEquiv.toEquiv, card_co2P]
  have : Finite CFSG.Blueprint.NativeSporadic.Co2 :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hy : orderOf (co2PermEquiv.symm sE) = 11 := by
    rw [MulEquiv.orderOf_eq]; exact orderOf_sE
  have hfac : (Nat.card CFSG.Blueprint.NativeSporadic.Co2).factorization 11 = 1 := by
    rw [hcard, show (42305421312000 : ℕ) = 11 * 3845947392000 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  exact @card_centralizer_of_conj_pow co2P CFSG.Blueprint.NativeSporadic.Co2 _ Units.instGroup _
    co2PermEquiv.symm sE 11 _ hy hfac 11 card_centralizer_sE x hx

end CFSG.HardMathSupport.Dickson.BMRows.Co2Eleven
